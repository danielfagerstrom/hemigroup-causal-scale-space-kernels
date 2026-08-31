#!/usr/bin/env python3
"""Numerical experiment for the hemigroup Gamma cascade (planned Example, section 12).

Runs the section-11 machine -- the ZOH pole--zero cascade over a fine geometric knot
ladder, gamma = 2 -- on a synthetic grey-level signal, renders the classical
scale-space evolution images (t horizontal, log x vertical, signal entering at the
bottom edge, the orientation of fig-signaling), and executes four checks, each tied
to a numbered result of the paper:

  C1  knot exactness (Prop. knot-exactness): refining the knot ladder does not move
      the final tap (differences at the time-discretization floor), and the ladder
      agrees with the direct single-increment filter; an Euler march of the scale
      ODE, run for contrast, shows O(Delta x) error.
  C2  non-creation (Prop. gamma-regularity): N(u(., x)) <= N(f) at every scale.
      Scale-to-scale monotonicity is NOT asserted by the theorem -- the increments
      carry transform zeros and are not variation-diminishing -- and the run indeed
      exhibits a few scale-to-scale increases, on the exact kernels as well: the
      per-increment caveat observed.
  C3  non-enhancement along the delay path (Cor. past-dominating): tracked maxima
      are nonincreasing in scale while past-dominating; a small event in the wake of
      a large one is transiently ENHANCED by the arriving delayed mass -- the
      predicted echo, the corollary's sharp failure mode -- before annihilating.
  C4  jets by subtraction (Prop. gamma-jets): x^n d_t^n u_gamma = (-grad)^n u_gamma
      along the shape column -- exact in continuous (FFT) semantics, and satisfied
      by the recursive architecture up to time-discretization error.

Outputs (written to ../figures):
  fig-experiment.png   -- signal strip + grey-level maps of u, x d_t u, x^2 d_t^2 u,
                          with mean-delay lines, tracked extremum paths, and the
                          tracked-value inset overlaid
  fig-fingerprint.png  -- zero-crossing fingerprints of d_t u and d_t^2 u
and prints the four checks' numbers.

The checks run on the M-knot ladder (the actual section-11 machine); the display
maps use a finer scale grid of per-scale shape columns for visual continuity only.
Deterministic (fixed seed). Time unit = one sample (Delta = 1).
"""
import os
import numpy as np
import matplotlib.pyplot as plt
from scipy.signal import lfilter

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "..", "figures")
plt.rcParams.update({"font.size": 9.5, "axes.linewidth": 0.8})
TEAL, BLUE, RED = "#2a9d8f", "#1b6ca8", "#d1495b"

# ----------------------------------------------------------------------------- setup
GAMMA = 2                       # shape: two sections per increment, jets to order 2
NT = 4096                       # samples; Delta = 1
XMIN, XMAX, M = 2.0, 400.0, 64  # geometric knot ladder (the machine under test)
MDISP = 160                     # display-only scale grid
SEED = 20260831

t = np.arange(NT, dtype=float)


def knots(m):
    """0 = x_0 < x_1 < ... < x_m, geometric above x_1 = XMIN."""
    return np.concatenate([[0.0], np.geomspace(XMIN, XMAX, m)])


def make_signal():
    """A grey-level image row: values in [0,1], every feature earning a check."""
    rng = np.random.default_rng(SEED)
    f = np.zeros(NT)
    bump = lambda t0, sig, amp: amp * np.exp(-0.5 * ((t - t0) / sig) ** 2)
    f += bump(350, 3, 0.85)          # fine event: dies low in the map
    f += bump(1150, 30, 0.70)        # coarse event: survives high
    f += bump(2000, 10, 0.90)        # the heavy event ...
    f += bump(2200, 35, 0.06)        # ... and the small one in its wake: echo specimen
    f += 0.25 * (1 + np.tanh((t - 2900) / 4.0))  # step: persists to the top of the map
    burst = (t >= 3350) & (t < 3550)
    f[burst] += 0.35 * (rng.random(burst.sum()) - 0.5)  # broadband burst on the step
    return np.clip(f, 0.0, 1.0)


# ------------------------------------------------------------------- the section-11 machine
def zoh_leaky(y, tau):
    """Exact exponential-integrator update of x w' = y - w for ZOH input; w(0)=0.

    w[n] uses input strictly before sample n:  w = (1-q) z^{-1} y / (1 - q z^{-1})."""
    if tau <= 0:
        return y.copy()
    q = np.exp(-1.0 / tau)
    return lfilter([0.0, 1.0 - q], [1.0, -q], y)


def section(y, xk, xk1):
    """One pole--zero section (1 + xk s)/(1 + xk1 s): v = a y + (1-a) w."""
    a = xk / xk1
    return a * y + (1 - a) * zoh_leaky(y, xk1)


def ladder(f, xs):
    """The cascade over the knot ladder; returns taps u(., x_k) for k >= 1."""
    u = f.copy()
    taps = []
    for k in range(len(xs) - 1):
        for _ in range(GAMMA):
            u = section(u, xs[k], xs[k + 1])
        taps.append(u.copy())
    return np.array(taps)


def shape_column(f, x):
    """u_0 = f, u_m = (1 + x d_t)^{-1} u_{m-1}: the gamma memory at scale x."""
    col = [f]
    for _ in range(GAMMA):
        col.append(zoh_leaky(col[-1], x))
    return col  # [u_0, u_1, u_2]


def euler_march(f, xs):
    """Forward-Euler march of  d_x u = -gamma (u - w)/x,  w = (1+x d_t)^{-1} u."""
    u = f.copy()
    for k in range(1, len(xs) - 1):
        x, dx = xs[k], xs[k + 1] - xs[k]
        w = zoh_leaky(u, x)
        u = u - dx * GAMMA * (u - w) / x
    return u


# ------------------------------------------------------------------------------ checks
def count_extrema(row, eps):
    d = np.diff(row)
    d = np.where(np.abs(d) < eps, 0.0, d)
    s = np.sign(d)
    s = s[s != 0]
    return int(np.sum(s[1:] != s[:-1]))


def local_maxima(row, eps=1e-7):
    d = np.diff(row)
    d = np.where(np.abs(d) < eps, 0.0, d)
    s = np.sign(d)
    idx = np.nonzero(s)[0]
    si = s[idx]
    out = [idx[b] for a, b in zip(range(len(si) - 1), range(1, len(si)))
           if si[a] > 0 and si[b] < 0]
    return np.array(out, dtype=int)


def track_max(taps, xs_mid, t0, drift=GAMMA):
    """Follow one local maximum upward through scale; stop when it annihilates."""
    ts, vals, dom = [], [], []
    tc = float(t0)
    for i, row in enumerate(taps):
        cand = local_maxima(row)
        if len(cand) == 0:
            break
        step = drift * (xs_mid[i] - (xs_mid[i - 1] if i else 0.0))
        win = 3.0 * step + 25.0
        j = cand[np.argmin(np.abs(cand - (tc + step)))]
        if abs(j - (tc + step)) > win:
            break
        tc = float(j)
        ts.append(j)
        vals.append(row[j])
        dom.append(row[j] >= row[: j + 1].max() - 1e-9)
    return np.array(ts, dtype=int), np.array(vals), np.array(dom)


def truncate_at_merge(tsA, tsB):
    """Cut track A where it lands on track B (the pair has merged)."""
    n = min(len(tsA), len(tsB))
    for i in range(n):
        if abs(int(tsA[i]) - int(tsB[i])) <= 2:
            return i
    return len(tsA)


def main():
    f = make_signal()
    xs = knots(M)
    xm = xs[1:]                       # the tap scales
    taps = ladder(f, xs)

    # --- C1: knot exactness -------------------------------------------------------
    taps2 = ladder(f, knots(2 * M))
    direct = f.copy()
    for _ in range(GAMMA):
        direct = section(direct, 0.0, XMAX)
    e_refine = np.max(np.abs(taps[-1] - taps2[-1]))
    e_direct = np.max(np.abs(taps[-1] - direct))
    e_euler = np.max(np.abs(euler_march(f, xs) - direct))
    e_euler2 = np.max(np.abs(euler_march(f, knots(2 * M)) - direct))
    print("C1 knot exactness   |ladder(M) - ladder(2M)|_inf = %.2e" % e_refine)
    print("                    |ladder(M) - direct|_inf     = %.2e" % e_direct)
    print("                    |euler(M)  - direct|_inf     = %.2e   (2M: %.2e)"
          % (e_euler, e_euler2))

    # --- C2: non-creation ---------------------------------------------------------
    eps = 1e-7
    counts = [count_extrema(f, eps)] + [count_extrema(r, eps) for r in taps]
    pad = 4 * NT
    om = 2j * np.pi * np.fft.rfftfreq(pad)
    F = np.fft.rfft(f, pad)
    exact = [np.fft.irfft(F / (1 + x * om) ** GAMMA, pad)[:NT] for x in xm]
    counts_x = [counts[0]] + [count_extrema(r, eps) for r in exact]
    inc = sum(1 for a, b in zip(counts, counts[1:]) if b > a)
    inc_x = sum(1 for a, b in zip(counts_x, counts_x[1:]) if b > a)
    print("C2 non-creation     N(x) <= N(f) at every scale: %s  (N(f)=%d, max N(x)=%d)"
          % ("yes" if max(counts[1:]) <= counts[0] else "NO",
             counts[0], max(counts[1:])))
    print("                    scale-to-scale increases (per-increment caveat):"
          " ladder %d, exact kernels %d, of %d steps" % (inc, inc_x, len(counts) - 1))

    # --- C3: delay-path non-enhancement + the echo --------------------------------
    tsC, valC, domC = track_max(taps, xm, 2000)
    tsB, valB, domB = track_max(taps, xm, 1150)
    tsD, valD, _ = track_max(taps, xm, 2200)
    cut = truncate_at_merge(tsC, tsB)
    tsC, valC, domC = tsC[:cut], valC[:cut], domC[:cut]
    viol = 0
    for vals, dom in ((valC, domC), (valB, domB)):
        viol += int(np.sum((np.diff(vals) > 1e-9) & dom[:-1]))
    print("C3 delay path       tracked maxima: value increases while past-dominating:"
          " %d (heavy event dominates %d, coarse event %d, of %d scales)"
          % (viol, domC.sum(), domB.sum(), len(xm)))
    kmin = int(np.argmin(valD))
    kup = kmin + int(np.argmax(valD[kmin:]))
    print("                    wake event: decays to %.4f (x=%.0f), echo lifts it to"
          " %.4f (x=%.0f, +%.0f%%), annihilates at x~%.0f"
          % (valD[kmin], xm[kmin], valD[kup], xm[kup],
             100 * (valD[kup] / valD[kmin] - 1), xm[len(valD) - 1]))

    # --- C4: jets by subtraction --------------------------------------------------
    x0 = 60.0
    e_fft = np.max(np.abs(np.fft.irfft(
        x0 * om * F / (1 + x0 * om) ** 2 - (F / (1 + x0 * om) - F / (1 + x0 * om) ** 2),
        pad)))
    col = shape_column(f, x0)
    sub1 = col[1] - col[2]                       # x d_t u_2 by subtraction
    num1 = x0 * np.gradient(col[2], 1.0)         # by temporal differencing
    e_arch = np.max(np.abs(sub1 - num1))
    print("C4 jets             identity in transform semantics: %.2e (machine floor)" % e_fft)
    print("                    recursive column vs differencing: %.2e (time-disc.)" % e_arch)

    # --------------------------------------------------- display fields (finer grid)
    xd = np.geomspace(XMIN, XMAX, MDISP)
    umap = np.empty((MDISP, NT))
    j1 = np.empty((MDISP, NT))
    j2 = np.empty((MDISP, NT))
    for i, x in enumerate(xd):
        c = shape_column(f, x)
        umap[i] = c[2]
        j1[i] = c[1] - c[2]                      # x d_t u
        j2[i] = c[0] - 2 * c[1] + c[2]           # x^2 d_t^2 u

    lx = np.log10
    ext = [0, NT, lx(XMIN), lx(XMAX)]
    ytv = [2, 10, 50, 200]

    # ------------------------------------------------------------------ figure 1: maps
    fig, axes = plt.subplots(4, 1, figsize=(9.2, 7.6), sharex=True,
                             gridspec_kw={"height_ratios": [1, 3.2, 3.2, 3.2]})
    ax0, ax1, ax2, ax3 = axes
    ax0.plot(t, f, color="k", lw=0.7)
    ax0.set_ylabel("$f$"); ax0.set_ylim(-0.05, 1.1); ax0.set_yticks([0, 1])
    ax1.imshow(umap, aspect="auto", origin="lower", cmap="gray",
               extent=ext, vmin=0, vmax=1, interpolation="nearest")
    for t0 in (350, 1150, 2000):
        ax1.plot(t0 + GAMMA * xd, lx(xd), color=RED, lw=0.9, ls="--")
    ax1.plot(tsC, lx(xm[:len(tsC)]), color=TEAL, lw=1.2)
    ax1.plot(tsB, lx(xm[:len(tsB)]), color=BLUE, lw=1.2)
    ax1.plot(tsD, lx(xm[:len(tsD)]), color=RED, lw=1.2, ls=":")
    # inset: tracked-maximum values against scale -- monotone while dominating,
    # the wake curve showing the echo uptick before annihilation
    ins = ax1.inset_axes([0.02, 0.10, 0.195, 0.42])
    ins.semilogx(xm[:len(valC)], valC, color=TEAL, lw=1.0)
    ins.semilogx(xm[:len(valB)], valB, color=BLUE, lw=1.0)
    ins.semilogx(xm[:len(valD)], 6 * valD, color=RED, lw=1.0)
    ins.plot(xm[len(valD) - 1], 6 * valD[-1], "x", color=RED, ms=4)
    ins.set_xticks([10, 100]); ins.set_xticklabels(["10", "100"], fontsize=6)
    ins.set_yticks([])
    ins.tick_params(length=2)
    ins.set_facecolor((1, 1, 1, 0.9))
    ins.text(0.05, 0.80, "tracked max values\n($6\\times$ the wake)", fontsize=5.6,
             transform=ins.transAxes)
    for a, lab in ((ax2, r"$x\,\partial_t u$"), (ax3, r"$x^2\,\partial_t^2 u$")):
        a.text(0.006, 0.86, lab, transform=a.transAxes, fontsize=10,
               bbox=dict(fc="white", ec="none", alpha=0.7, pad=1.2))
    v1 = np.percentile(np.abs(j1), 99.5)
    v2 = np.percentile(np.abs(j2), 99.5)
    ax2.imshow(j1, aspect="auto", origin="lower", cmap="gray", extent=ext,
               vmin=-v1, vmax=v1, interpolation="nearest")
    ax3.imshow(j2, aspect="auto", origin="lower", cmap="gray", extent=ext,
               vmin=-v2, vmax=v2, interpolation="nearest")
    for a in (ax1, ax2, ax3):
        a.set_ylabel(r"$x$ (log)")
        a.set_yticks([lx(v) for v in ytv])
        a.set_yticklabels(["$%d$" % v for v in ytv])
        a.set_ylim(lx(XMIN), lx(XMAX))
    ax3.set_xlabel("$t$ (samples)")
    fig.align_ylabels(axes)
    fig.tight_layout(h_pad=0.4)
    fig.savefig(os.path.join(OUT, "fig-experiment.png"), dpi=200,
                bbox_inches="tight")

    # ------------------------------------------------------------- figure 2: fingerprints
    fig2, (b1, b2) = plt.subplots(1, 2, figsize=(9.2, 3.4), sharey=True)
    for ax, jm, ttl in ((b1, j1, r"zero-crossings of $\partial_t u$ (extrema of $u$)"),
                        (b2, j2, r"zero-crossings of $\partial_t^2 u$")):
        z = np.where(np.abs(jm) < 1e-6, 0.0, jm)
        sgn = np.sign(z)
        for i in range(MDISP):
            s = sgn[i]
            nz = s != 0
            si = s[nz]; ti = t[nz]
            cross = ti[1:][si[1:] != si[:-1]]
            ax.plot(cross, np.full(len(cross), lx(xd[i])), ".k", ms=0.7)
        ax.set_title(ttl, fontsize=9.5)
        ax.set_xlabel("$t$ (samples)")
        ax.set_yticks([lx(v) for v in ytv])
        ax.set_yticklabels(["$%d$" % v for v in ytv])
    b1.set_ylabel(r"$x$ (log)")
    fig2.tight_layout()
    fig2.savefig(os.path.join(OUT, "fig-fingerprint.png"), dpi=200,
                 bbox_inches="tight")
    print("wrote fig-experiment.png, fig-fingerprint.png")


if __name__ == "__main__":
    main()
