#!/usr/bin/env python3
"""fig-families.png -- the moment threshold as a dial (paper §8, after the Bessel family).

Left: log-log densities of the Bessel/inverse-gamma family T_1 = 1/(2 Y_a) for a = 1/2, 1, 2, 4
(Y_a Gamma(a,1)); the tails are straight lines of slope -(a+1), so E T^n < inf iff n < a, and
a = 1/2 is the extremal stable member (heaviest). The Gamma kernel (shape 2) is drawn for
contrast: an exponential tail, every moment finite. Right: the same densities on a linear
scale, unit canonical scale. Design after the hub's scripts/covariant_memory_figure.py.

Run:  python scripts/make-fig-families.py      Out:  figures/fig-families.png
"""
import os
import numpy as np
import matplotlib.pyplot as plt
from scipy.stats import invgamma, gamma as gamma_d

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "..", "figures", "fig-families.png")
plt.rcParams.update({"font.size": 9.5, "axes.linewidth": 0.8})

# inverse-gamma(a, scale=1/2): density of 1/(2 Y_a)
fams = [(0.5, "#d1495b", r"$a=\frac{1}{2}$ (stable $\alpha=\frac{1}{2}$)"),
        (1.0, "#6a4c93", r"$a=1$"), (2.0, "#2a9d8f", r"$a=2$"), (4.0, "#1b6ca8", r"$a=4$")]
fig, (axl, axr) = plt.subplots(1, 2, figsize=(8.6, 3.3))

t = np.logspace(-2, 3, 600)
for a, col, lab in fams:
    axl.loglog(t, invgamma(a, scale=0.5).pdf(t), color=col, lw=1.6, label=lab)
axl.loglog(t, gamma_d(2.0).pdf(t), color="#555555", lw=1.6, ls="--", label=r"Gamma, $\gamma=2$")
axl.set_xlim(1e-2, 1e3); axl.set_ylim(1e-8, 10)
axl.set_xlabel(r"$t$"); axl.set_ylabel(r"$\phi_1(t)$")
axl.set_title("log–log: tails of slope $-(a+1)$", fontsize=9.5)
# slope guides
for a, col, _ in fams:
    t0 = 40.0; y0 = invgamma(a, scale=0.5).pdf(t0)
    axl.annotate(rf"$t^{{-{a+1:g}}}$", (t0, y0), xytext=(6, 3), textcoords="offset points", color=col, fontsize=8)
axl.legend(fontsize=7.5, loc="lower left", frameon=False)

tt = np.linspace(0, 4, 500)
for a, col, lab in fams[:3]:
    axr.plot(tt, invgamma(a, scale=0.5).pdf(tt), color=col, lw=1.6)
axr.plot(tt, gamma_d(2.0).pdf(tt), color="#555555", lw=1.6, ls="--")
axr.set_xlim(0, 4); axr.set_ylim(0, 2.0)
axr.set_xlabel(r"$t$"); axr.set_title(r"linear scale ($a \leq 2$), unit canonical scale", fontsize=9.5)
for ax in (axl, axr):
    for s in ("top", "right"): ax.spines[s].set_visible(False)
fig.tight_layout()
fig.savefig(OUT, dpi=200)
print("wrote", OUT)
