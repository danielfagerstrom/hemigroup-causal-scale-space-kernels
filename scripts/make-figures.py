#!/usr/bin/env python3
"""Kernel comparison figures for the hemigroup causal scale-space draft (Example 13.5).

Generates:
  fig-kernels.png       -- kernels at matched MEAN delay 1 (stable: median 1)
  fig-kernels-mode.png  -- kernels at matched MODE delay 1 (gamma=1 omitted: mode at onset)
and prints the window-length tables T_p with  int_0^{T_p} phi = p.

Kernel families (canonical / parabolic gauge as in the draft):
  Gamma(gamma, x):        phi(t) = t^{gamma-1} e^{-t/x} / (Gamma(gamma) x^gamma)
                          mean = gamma x, mode = (gamma-1) x
  inverse-gamma(a, th):   phi(t) = th^a t^{-a-1} e^{-th/t} / Gamma(a),  th = x^2/2
                          mean = th/(a-1) (a>1), mode = th/(a+1), tail t^{-1-a}
  1/2-stable = inverse-gamma(1/2, th): mean infinite, mode = 2 th / 3, tail t^{-3/2}
"""
import os
import numpy as np
import matplotlib.pyplot as plt
from scipy.stats import gamma as gamma_d, invgamma

HERE = os.path.dirname(os.path.abspath(__file__))
FIGDIR = os.path.normpath(os.path.join(HERE, "..", "figures"))
plt.rcParams.update({"font.size": 9.5, "axes.linewidth": 0.8})
COLS = {1: "#1b6ca8", 2: "#2a9d8f", 4: "#6a4c93"}
RED, GREY = "#d1495b", "#555555"


def window_table(title, rows):
    print(f"\n{title}")
    for name, rv in rows:
        mean = rv.mean()
        mean_s = f"{mean:6.3f}" if np.isfinite(mean) else "  inf "
        print(f"  {name:26s} mean = {mean_s}   "
              f"T99 = {rv.ppf(0.99):12.3f}   T999 = {rv.ppf(0.999):14.3f}")


def make_figure(fname, gam_list, gam_scale, ig_shape, ig_scale, st_scale,
                title_a, xmax):
    """gam_scale, ig_scale, st_scale: scale parameters per family."""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.2, 3.5))

    gams = {g: gamma_d(a=g, scale=gam_scale(g)) for g in gam_list}
    ig = invgamma(a=ig_shape, scale=ig_scale)
    st = invgamma(a=0.5, scale=st_scale)

    t_lin = np.linspace(1e-4, xmax, 1400)
    for g in gam_list:
        ax1.plot(t_lin, gams[g].pdf(t_lin), color=COLS[g], lw=1.8,
                 label=rf"$\Gamma(\gamma={g})$")
    ax1.plot(t_lin, ig.pdf(t_lin), color=RED, lw=1.8, ls="--",
             label=rf"inv-$\Gamma$, $a={ig_shape:g}$ (Bessel)")
    ax1.plot(t_lin, st.pdf(t_lin), color=GREY, lw=1.8, ls=":",
             label="1/2-stable (2005)")
    ax1.set_xlabel(r"$t$"); ax1.set_ylabel(r"kernel $\phi(t)$")
    ax1.set_xlim(0, xmax); ax1.set_ylim(bottom=0)
    ax1.set_title(title_a, fontsize=9.5)
    ax1.legend(frameon=False, fontsize=8.2)

    t_log = np.logspace(-1, 3, 800)
    for g in gam_list:
        ax2.loglog(t_log, gams[g].pdf(t_log), color=COLS[g], lw=1.8)
    ax2.loglog(t_log, ig.pdf(t_log), color=RED, lw=1.8, ls="--")
    ax2.loglog(t_log, st.pdf(t_log), color=GREY, lw=1.8, ls=":")

    # exact power-law asymptotes:  inv-gamma ~ th^a/Gamma(a) t^{-1-a};
    # 1/2-stable ~ sqrt(th/pi) t^{-3/2}
    from scipy.special import gamma as G
    tg = np.logspace(0.8, 3, 50)
    c_ig = ig_scale**ig_shape / G(ig_shape)
    c_st = np.sqrt(st_scale / np.pi)
    ax2.loglog(tg, c_ig * tg**(-(1 + ig_shape)), color=RED, lw=0.8, alpha=0.55)
    ax2.loglog(tg, c_st * tg**(-1.5), color=GREY, lw=0.8, alpha=0.55)
    ax2.text(tg[-1]*0.9, c_ig*tg[-1]**(-(1+ig_shape))*3.0,
             rf"$t^{{-{1+ig_shape:g}}}$", color=RED, fontsize=8.5, ha="right")
    ax2.text(tg[-1]*0.9, c_st*tg[-1]**(-1.5)*3.0,
             r"$t^{-3/2}$", color=GREY, fontsize=8.5, ha="right")
    ax2.set_xlabel(r"$t$"); ax2.set_ylim(1e-12, 3)
    ax2.set_title("(b) tails, log--log", fontsize=9.5)

    fig.tight_layout()
    fig.savefig(os.path.join(FIGDIR, fname), dpi=200, bbox_inches="tight")
    plt.close(fig)
    print(f"wrote {fname}")
    return gams, ig, st


# ---------------- Figure 1: matched MEAN delay = 1 ----------------
# Gamma: mean gamma*x = 1  -> x = 1/gamma
# inv-gamma a=2: mean th/(a-1) = 1 -> th = 1
# 1/2-stable: mean infinite -> match MEDIAN = 1 (th solves median(th) = 1)
th_med1 = 0.5 / invgamma(a=0.5, scale=0.5).median()
gams, ig, st = make_figure(
    "fig-kernels.png", [1, 2, 4], lambda g: 1.0/g, 2.0, 1.0, th_med1,
    "(a) matched mean delay $= 1$ (stable: median $= 1$)", xmax=5)
window_table("matched mean (Figure 1):",
             [(f"Gamma(gamma={g}, x=1/{g})", gams[g]) for g in [1, 2, 4]]
             + [("inv-gamma a=2, th=1", ig), ("1/2-stable, median 1", st)])

# ---------------- Figure 2: matched MODE delay = 1 ----------------
# Gamma: mode (gamma-1)x = 1 -> x = 1/(gamma-1); gamma=1 omitted (mode at 0)
# inv-gamma a=2: mode th/(a+1) = 1 -> th = 3
# 1/2-stable: mode 2 th/3 = 1 -> th = 3/2
gams, ig, st = make_figure(
    "fig-kernels-mode.png", [2, 4], lambda g: 1.0/(g-1), 2.0, 3.0, 1.5,
    "(a) matched mode delay $= 1$", xmax=6)
window_table("matched mode (Figure 2):",
             [(f"Gamma(gamma={g}, x=1/{g-1})", gams[g]) for g in [2, 4]]
             + [("inv-gamma a=2, th=3", ig), ("1/2-stable, th=3/2", st)])
