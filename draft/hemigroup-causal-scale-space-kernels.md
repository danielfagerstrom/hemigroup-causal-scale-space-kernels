# Time-Causal Scale Space from Hemigroup Axioms: Characterization of the Kernels

*Working draft — kernel-level (time line) characterization, with the scale-Cauchy formulation (Theorem 3′) in §10, the signaling form (Theorem 4′) in §11, the locality theorem (Theorem 5′) in §12, implementation notes in §13, and the embodied temporal N-jet in §14.*

## 1. Introduction

A measurement of a temporal signal is subject to two asymmetries that have no spatial counterpart. The observer cannot access the future: measurement must be causal. And the observer cannot return to the past: whatever of the signal's history is to influence the present output must be carried in the observer's own state — in the formulation of [Fagerström 2005, §5], the observer must *embody* its past. A theory of uncommitted multi-scale temporal measurement — a temporal scale space — must therefore supply a family of smoothing operators, indexed by temporal scale, that is linear, positive and mass-preserving (creating no spurious structure), causal, implementable by a state evolving recursively in present time, and covariant under rescalings of the time axis, since an uncommitted front end has no preferred unit of time.

The Gaussian scale space that answers the corresponding spatial question [Iijima; Lindeberg 2011] is unavailable here — the Gaussian is non-causal, and its causal truncations destroy the cascade structure — and the known time-causal constructions each concede one of the desiderata. The scale-time of [Koenderink 1988] applies Gaussian smoothing to a logarithmically remapped past, achieving causality but not time-recursivity: the representation must be recomputed at every present moment. The Poisson scale space of [Lindeberg–Fagerström 1996] is causal and time-recursive but, as Remark 15.1 below proves, carries no dilation covariance of any span: its fixed elementary delay is a preferred time unit. The axiomatization of [Fagerström 2005] imposes full continuous covariance together with a one-parameter *semigroup* cascade and obtains a complete answer — the kernels are exactly the extremal (one-sided) stable densities, $\mathcal{L}^{-1}[e^{-\tau s^\alpha}]$, $0 < \alpha < 1$ — but every member has infinite mean delay, the heavy power tails limiting the family's use as a bank of measurement operators. The time-causal limit kernel of [Lindeberg 2016] restores finite moments through a recursive cascade of first-order integrators with geometrically distributed time constants, with covariance established there under the discrete subgroup of rescalings $\sigma \in q^{\mathbb{Z}}$; Remark 15.1 below shows that its exponent is in fact self-decomposable, so that the limit kernel is, in retrospect, the first-discovered member of the class characterized in this paper — a construction that preceded the classification explaining it.

This paper locates the obstruction in a single axiom, and removes it. The semigroup form of the cascade property, $\Phi_\tau \Phi_{\tau'} = \Phi_{\tau + \tau'}$, formalizes "a measurement of a measurement is a measurement" together with a second, tacit assumption: that the composite depends only on the total *amount* of scale — that measurement stages are interchangeable. We keep the first assumption and drop the second, stating the cascade as a two-parameter **hemigroup**,

$$\Phi_{y,z}\,\Phi_{x,y} \;=\; \Phi_{x,z}, \qquad 0 \le x \le y \le z,$$

so that scale is an ordered interval structure rather than an additive quantity, and the elementary smoothing applied between fine scales need not equal the one applied between coarse scales. All other axioms — causality, linearity, positivity, unit area, continuity, translation covariance, and *full continuous* scale covariance — are retained verbatim.

Rerunning the 2005 derivation in the same order and with the same tools (Laplace transforms, two functional equations, complete monotonicity), the characterization theorem (Theorem 7.3) reads: the admissible kernel families are exactly

$$\phi_x(t) \;=\; \mathcal{L}^{-1}\big[\,e^{-F(xs)}\,\big](t), \qquad F(s) = b_0\,s + \int_0^\infty\big(1 - e^{-st}\big)\,\frac{k(t)}{t}\,dt, \quad k \ \text{nonincreasing},$$

the Laplace exponents of the *self-decomposable* laws — equivalently, the kernels are the marginal densities of self-similar additive (Sato) subordinators. The extremal stable family is precisely the sub-case recovered when stage-interchangeability is reimposed, and the heavy tails are thereby exposed as the price of that tacit assumption, not of causality and covariance: the new class contains members with all moments finite, the flagship being the Gamma family $\phi_x(t) = t^{\gamma-1}e^{-t/x}/(\Gamma(\gamma)x^\gamma)$ — mean delay $\gamma x$, exponential tails, exact continuous scale covariance, and a recursive implementation by first-order filter sections.

The remainder develops the memory-line theory in parallel with Theorems 3–5 of [Fagerström 2005], and the embodiment principle, invoked there as motivation, recurs here three times as theorem content. First, the evolution across scale is a general fractional relaxation equation in the sense of Kochubei and Luchko whose memory kernel is the self-decomposability function $k$ itself, dilated to the current scale, and the unit-area axiom becomes an exact Sonine conservation identity, $\kappa * \ell = \mathrm{Leb}$: the infinitesimal smoothing applied at each scale is exactly invertible, destroying no information (§9, Theorem 10.4). Second, the inversion into a signaling problem $\partial_t u = A u$ over the memory half-line is accomplished by a covariant *Mellin* operator — multiplicative harmonic analysis mirroring the Wendel step on the additive group that opens the derivation — and comes with the identity $\mathcal{M}_x[u(t, \cdot)](z) = \tilde H(z)\,(I^z f)(t)$: at each instant, the memory line stores precisely the analytic family of Riemann–Liouville integrals of the past signal (Theorem 11.6, Lemma 11.5). Third, the temporal $N$-jet — the causal analogue of the derivative-of-Gaussian receptive fields — is an instantaneous functional of that same state, $\partial_t^n u = A^n u$: differentiation is re-indexing of the embodied record, and for the Gamma family a binomial subtraction of coexisting filter states, so that no second memory of the scale space is needed to differentiate (§14).

The locality analogue of Theorem 5 becomes a genuine classification (Theorem 12.5). Locality of the memory-line operator alone admits a ladder of every differential order, with reciprocal gamma-product kernels whose depth-homogeneous slice recovers, through Gauss's multiplication formula, the local stable cases $\alpha = 1/n$; the positive maximum principle then closes the ladder at order two, unfolding the isolated heat case $\alpha = \tfrac12$ of [Fagerström 2005, Thm. 5] into the one-parameter Bessel family $\tfrac12\partial_x^2 + \tfrac{\beta}{x}\partial_x$ with inverse-gamma kernels, whose drift weight $\beta$ buys any prescribed finite number of kernel moments. On the implementation side (§13), the hemigroup itself is the algorithm: the discrete cascade over any set of scale knots reproduces the continuum family *exactly* at the knots, the Gamma increments are rational — identical pole–zero first-order sections — and, through the Thorin structure of generalized gamma convolutions, finite gamma cascades approximate the entire completely-monotone-kernel subclass from *inside* the axiom class, making the Gamma family the implementation substrate for the whole theory; Example 13.7 quantifies the tail contrast, the $\tfrac12$-stable kernel requiring a window five to six orders of magnitude beyond its typical delay to capture $99.9\%$ of its mass, against a small constant multiple for the Gamma members.

Finally, the earlier time-causal constructions are situated *inside* the axiom system rather than beside it (Remark 15.1): the axioms without any covariance give the Bernstein hemigroups, containing the Poisson scale space; covariance under the discrete subgroup $q^{\mathbb{Z}}$ gives the semi-selfdecomposable (semi-Sato) stratum, containing the time-causal limit kernel — one $q$-step of scale per pole section of its cascade; and full covariance gives the present class. The comparison with the previous literature is thus one of containment rather than difference. Four problems are left open in §15, chief among them the memory-line inverse problem — which admissible exponents are realized by genuine Markov media, a correspondence of Krein type [Kotani–Watanabe 1982; Dym–McKean 1976] admitting jumps — which is the subject of a separate article, and the structure theorem of the discrete-covariance stratum with its canonical-selection question for the limit kernel, deferred to a companion note.

The paper is purely temporal; composition with a spatial scale space is orthogonal to everything done here. The organization follows the derivation: §2 fixes notation and the Bernstein-function toolbox; §3 states the axioms with domains; §§4–6 derive the convolution representation, the additivity and infinite divisibility of the exponents, and the similarity form forced by covariance; §7 proves the characterization theorem; §8 gives examples and moment formulas; §9 the memory-kernel and Sonine structure with a Volterra derivation of the kernels; §10 the scale-Cauchy problem; §11 the Mellin signaling form; §12 the locality theorem; §13 implementation; §14 the embodied temporal jet; §15 concludes.

## 2. Preliminaries and notation

Time runs over $\mathbb{R}$. We write:

- $X = L^1(\mathbb{R}, dt)$, real, with positive cone $X_+$ and $\int f := \int_{\mathbb{R}} f(t)\,dt$;
- $M_+(\mathbb{R})$ for the finite positive Borel measures on $\mathbb{R}$, with total mass $\|\mu\| = \mu(\mathbb{R})$;
- translations $(\tau_a f)(t) = f(t-a)$, $a \in \mathbb{R}$;
- dilations on functions $(D_\sigma f)(t) = \sigma^{-1} f(t/\sigma)$, $\sigma > 0$ (mass-preserving), and on measures $D_\sigma \mu :=$ the pushforward of $\mu$ under $t \mapsto \sigma t$;
- convolution $(\mu * f)(t) = \int f(t - r)\,\mu(dr)$ for $\mu \in M_+(\mathbb{R})$, $f \in X$; then $\|\mu * f\|_1 \le \|\mu\|\,\|f\|_1$, and

$$D_\sigma(\mu * f) = (D_\sigma \mu) * (D_\sigma f).$$

For $\mu \in M_+$ supported on $[0,\infty)$ the Laplace transform is

$$\hat\mu(s) = \int_{[0,\infty)} e^{-st}\,\mu(dt), \qquad s \ge 0 .$$

If $\mu \ne 0$ then $\hat\mu(s) > 0$ for all $s \ge 0$.

**Definition 2.1 (completely monotone).** $f : (0,\infty) \to \mathbb{R}$ is *completely monotone* (CM) if $f \in C^\infty$ and $(-1)^n f^{(n)} \ge 0$ for all $n \ge 0$.

**Definition 2.2 (Bernstein function).** $g : (0,\infty) \to [0,\infty)$ is a *Bernstein function* if $g \in C^\infty$ and $g'$ is completely monotone. We write $g \in \mathrm{BF}$, and $g \in \mathrm{BF}_0$ if moreover $g(0{+}) = 0$.

**Proposition 2.3 (toolbox; see [Feller, Ch. XIII], [SSV, Ch. 1, 3]).**

1. *(Bernstein–Widder / Feller criterion.)* $f$ is the Laplace transform of a probability measure on $[0,\infty)$ iff $f$ is CM and $f(0{+}) = 1$.
2. $g \in \mathrm{BF}$ iff $e^{-\tau g}$ is CM for every $\tau > 0$.
3. Every $g \in \mathrm{BF}$ is nonnegative, nondecreasing, concave, and has the unique Lévy–Khintchine representation

$$g(s) = a + b s + \int_0^\infty \big(1 - e^{-st}\big)\,\nu(dt), \qquad a, b \ge 0, \ \int_0^\infty (1 \wedge t)\,\nu(dt) < \infty,$$

with $g(0{+}) = a$.
4. $\mathrm{BF}$ is a convex cone, closed under pointwise limits: if $g_n \in \mathrm{BF}$ and $g_n(s) \to g(s) < \infty$ for every $s > 0$, then $g \in \mathrm{BF}$. Consequently $\mathrm{BF}$ is closed under mixtures $s \mapsto \int g_u(s)\,m(du)$ with $m \ge 0$, whenever the integral is finite.

**Lemma 2.4 (vanishing lemma).** If $g \in \mathrm{BF}_0$ and $g(s_0) = 0$ for some $s_0 > 0$, then $g \equiv 0$.

*Proof.* $g$ is nonnegative and concave with $g(0{+}) = g(s_0) = 0$, hence $g \equiv 0$ on $(0, s_0]$. Then $g' \equiv 0$ on $(0, s_0)$; since $g'$ is nonincreasing (concavity) and nonnegative ($g' \in \mathrm{CM}$), $g' \equiv 0$ on $(0,\infty)$, so $g \equiv 0$. ∎

## 3. Axioms

The primitive object is a two-parameter family of operators indexed by ordered pairs of scales.

**Definition 3.1 (causal cascade measurement family).** A family of linear operators

$$\Phi_{x,y} : X \to X, \qquad 0 \le x \le y < \infty,$$

is a *causal cascade measurement family* if it satisfies:

- **(A1) Boundedness.** Each $\Phi_{x,y}$ is a bounded operator on $X$.
- **(A2) Time-translation covariance.** $\Phi_{x,y}\,\tau_a = \tau_a\,\Phi_{x,y}$ for all $a \in \mathbb{R}$.
- **(A3) Causality.** If $f \in X$ vanishes a.e. on $(-\infty, t_0)$, then so does $\Phi_{x,y} f$.
- **(A4) Positivity.** $\Phi_{x,y} X_+ \subseteq X_+$.
- **(A5) Unit area.** $\int \Phi_{x,y} f = \int f$ for all $f \in X_+$.
- **(A6) Cascade (hemigroup).** $\Phi_{x,x} = \mathrm{Id}$, and $\Phi_{y,z}\,\Phi_{x,y} = \Phi_{x,z}$ for all $x \le y \le z$.
- **(A7) Continuity.** For every $f \in X$, the map $(x,y) \mapsto \Phi_{x,y} f$ is continuous from $\{0 \le x \le y\}$ to $X$.
- **(A8) Scale covariance.** There is a family $(S_\sigma)_{\sigma > 0}$ of increasing bijections of $[0,\infty)$ such that

$$D_\sigma\,\Phi_{x,y} = \Phi_{S_\sigma x,\,S_\sigma y}\,D_\sigma \qquad \text{for all } 0 \le x \le y,\ \sigma > 0.$$

- **(ND) Nondegeneracy.** $\Phi_{x,y} \ne \mathrm{Id}$ whenever $x < y$.

**Remark 3.2.** (A1)–(A5), (A7) are as in [Fagerström 2005]; the diagonal condition in (A6) together with (A7) is the two-parameter form of the *extended point* axiom $\lim_{\tau\to 0}\phi_\tau = \delta$. The single change is (A6): in [Fagerström 2005] the cascade reads $\Phi_\tau \Phi_{\tau'} = \Phi_{\tau + \tau'}$, which additionally assumes that the composite measurement depends only on the total amount of scale — that measurement stages are interchangeable. (A6) drops exactly that assumption. (A8) is the two-parameter form of scaling covariance; note that an increasing bijection of $[0,\infty)$ automatically fixes $0$. (ND) excludes idle stretches of the scale axis. A *passive* variant replaces (A5) by $\int \Phi_{x,y} f \le \int f$ on $X_+$; all results below hold with sub-probability kernels and an extra killing term, and we do not pursue it.

## 4. Convolution representation

**Lemma 4.1 (representation).** Under (A1)–(A5), for each pair $x \le y$ there is a unique probability measure $\mu_{x,y}$ on $[0,\infty)$ with

$$\Phi_{x,y} f = \mu_{x,y} * f, \qquad f \in X,$$

and conversely every such measure defines an operator satisfying (A1)–(A5).

*Proof.* Fix $(x,y)$ and write $\Phi = \Phi_{x,y}$. Choose an approximate identity $\rho_\varepsilon \in X_+$, $\int \rho_\varepsilon = 1$, $\operatorname{supp}\rho_\varepsilon \subseteq [0,\varepsilon]$. By (A4), (A5), $h_\varepsilon := \Phi \rho_\varepsilon \in X_+$ with $\int h_\varepsilon = 1$; by (A3), $h_\varepsilon$ vanishes a.e. on $(-\infty, 0)$. Regarding $h_\varepsilon\,dt$ as elements of the unit ball of $M(\mathbb{R}) = C_0(\mathbb{R})^*$, extract a subnet converging weak-* to some $\mu \ge 0$ with $\|\mu\| \le 1$ and $\operatorname{supp}\mu \subseteq [0,\infty)$.

For $f, g \in X$ we have $f * g = \int \tau_r g\, f(r)\,dr$ as a Bochner integral, so (A1)–(A2) give $\Phi(f * g) = f * \Phi g$. Hence for $f \in C_c(\mathbb{R})$,

$$\Phi(f * \rho_\varepsilon) = f * h_\varepsilon \xrightarrow{\ \varepsilon \to 0\ } f * \mu \quad \text{pointwise},$$

using $f(t - \cdot) \in C_0(\mathbb{R})$ and weak-* convergence, while $\Phi(f * \rho_\varepsilon) \to \Phi f$ in $X$ by (A1). Therefore $\Phi f = \mu * f$ for $f \in C_c$, and by density for all $f \in X$. Finally, for $f \in X_+$, Tonelli gives $\int \mu * f = \|\mu\| \int f$, so (A5) forces $\|\mu\| = 1$. Uniqueness and the converse are routine. ∎

**Lemma 4.2 (continuity of transforms).** Under (A1)–(A5) and (A7), the function

$$g_{x,y}(s) := -\log \hat\mu_{x,y}(s) \in [0,\infty), \qquad s \ge 0,$$

is well defined, and $(x,y) \mapsto g_{x,y}(s)$ is continuous for each $s \ge 0$; moreover $g_{x,y}(0{+}) = 0$ and $s \mapsto g_{x,y}(s)$ is continuous.

*Proof.* $\hat\mu(s) \in (0, 1]$ for a probability measure on $[0,\infty)$, so $g$ is well defined and nonnegative; $\hat\mu(s) \to 1$ as $s \downarrow 0$ by dominated convergence, and $s \mapsto \hat\mu(s)$ is continuous. For continuity in $(x,y)$: fix a probability density $\rho \in X_+$ supported in $[0,\infty)$, so $\hat\rho(s) > 0$. If $(x_n, y_n) \to (x,y)$, then by (A7) $\mu_{x_n,y_n} * \rho \to \mu_{x,y} * \rho$ in $X$; since all functions involved are supported in $[0,\infty)$ and $|e^{-st}| \le 1$ there,

$$\big|\hat\mu_{x_n,y_n}(s)\,\hat\rho(s) - \hat\mu_{x,y}(s)\,\hat\rho(s)\big| \le \|\mu_{x_n,y_n} * \rho - \mu_{x,y} * \rho\|_1 \to 0,$$

and dividing by $\hat\rho(s) > 0$ gives the claim. ∎

## 5. The cascade: additivity and infinite divisibility

**Lemma 5.1 (additivity).** Under (A1)–(A7), $\mu_{x,z} = \mu_{y,z} * \mu_{x,y}$ for $x \le y \le z$, hence

$$g_{x,z}(s) = g_{x,y}(s) + g_{y,z}(s), \qquad g_{x,x} = 0.$$

Consequently, with $G(x, s) := g_{0,x}(s)$,

$$g_{x,y}(s) = G(y, s) - G(x, s),$$

where $G(0, \cdot) = 0$, $G(\cdot, s)$ is nondecreasing and continuous for each $s$, and $G(x, 0{+}) = 0$.

*Proof.* Immediate from (A6), Lemma 4.1 (convolution corresponds to operator composition), and Lemma 4.2. ∎

The next step upgrades the increments from "exponents of probability measures" to Bernstein functions. In the semigroup case this is trivial ($\mu_\tau = \mu_{\tau/n}^{*n}$); in the hemigroup case it is a null-array argument, which on the half-line can be made elementary.

**Theorem 5.2 (increments are Bernstein).** Under (A1)–(A7), $g_{x,y} \in \mathrm{BF}_0$ for every $x \le y$.

*Proof.* Fix $x < y$ and the uniform partition $t_i = x + \tfrac{i}{n}(y - x)$, $i = 0, \dots, n$. Write $\mu_i := \mu_{t_i, t_{i+1}}$, $g_i := g_{t_i, t_{i+1}}$, so that by Lemma 5.1

$$g_{x,y}(s) = \sum_{i=0}^{n-1} g_i(s) \qquad \text{for every } n.$$

Fix $s > 0$. Since $G(\cdot, s)$ is continuous on the compact $[x, y]$, it is uniformly continuous, so $m_n := \max_i g_i(s) \to 0$ as $n \to \infty$. Using $0 \le u - (1 - e^{-u}) \le u^2/2$ for $u \ge 0$,

$$\Big|\, g_{x,y}(s) - \sum_{i}\big(1 - e^{-g_i(s)}\big) \Big| \;\le\; \tfrac12 \sum_i g_i(s)^2 \;\le\; \tfrac{m_n}{2}\, g_{x,y}(s) \;\longrightarrow\; 0 .$$

On the other hand, with $\Pi_n := \sum_i \mu_i \in M_+([0,\infty))$ (a finite measure),

$$\sum_i \big(1 - e^{-g_i(s)}\big) = \sum_i \big(1 - \hat\mu_i(s)\big) = \int_0^\infty \big(1 - e^{-st}\big)\,\Pi_n(dt),$$

which is a Bernstein function of $s$ vanishing at $0{+}$ (Lévy–Khintchine form with finite Lévy measure $\Pi_n$). Hence $g_{x,y}$ is a finite pointwise limit of elements of $\mathrm{BF}_0$, so $g_{x,y} \in \mathrm{BF}$ by Proposition 2.3(4), and $g_{x,y}(0{+}) = 0$ by Lemma 4.2. ∎

**Corollary 5.3 (strict monotonicity).** Assume in addition (ND). Then for every $s > 0$ and $x < y$,

$$G(y, s) - G(x, s) = g_{x,y}(s) > 0,$$

i.e. $G(\cdot, s)$ is strictly increasing for every $s > 0$.

*Proof.* By (ND), $\mu_{x,y} \ne \delta_0$, so $g_{x,y} \not\equiv 0$; by Theorem 5.2 and Lemma 2.4, $g_{x,y}(s) > 0$ for all $s > 0$. ∎

## 6. Scale covariance: the similarity form

**Lemma 6.1 (Laplace form of covariance).** Under (A1)–(A5), axiom (A8) is equivalent to

$$D_\sigma\,\mu_{x,y} = \mu_{S_\sigma x,\, S_\sigma y} \qquad \Longleftrightarrow \qquad g_{S_\sigma x,\, S_\sigma y}(s) = g_{x,y}(\sigma s),$$

and in particular

$$G(S_\sigma x,\, s) = G(x,\, \sigma s) \qquad \text{for all } x \ge 0,\ \sigma, s > 0. \tag{6.1}$$

*Proof.* $D_\sigma(\mu * f) = (D_\sigma\mu) * (D_\sigma f)$ and uniqueness in Lemma 4.1 give the first equivalence; $\widehat{D_\sigma\mu}(s) = \hat\mu(\sigma s)$ gives the second. The case $x = 0$ uses $S_\sigma 0 = 0$. ∎

**Lemma 6.2 (rigidity of the action).** Assume (A1)–(A8) and (ND). Then:

1. For each $\sigma$, $S_\sigma$ is uniquely determined by (6.1).
2. $S_\sigma S_\tau = S_{\sigma\tau}$ for all $\sigma, \tau > 0$, and $S_1 = \mathrm{Id}$.
3. $\sigma \mapsto S_\sigma x$ is continuous and strictly increasing for each $x > 0$.
4. The action has no fixed point in $(0,\infty)$: if $S_\sigma x^* = x^*$ for all $\sigma$, then $x^* = 0$.

*Proof.* (1) If $S, S'$ both satisfy (6.1) then $G(S_\sigma x, s) = G(S'_\sigma x, s)$ for all $s > 0$; Corollary 5.3 gives $S_\sigma x = S'_\sigma x$. (2) Apply (6.1) twice: $G(S_\sigma S_\tau x, s) = G(S_\tau x, \sigma s) = G(x, \sigma\tau s) = G(S_{\sigma\tau} x, s)$, and use (1); similarly $S_1 = \mathrm{Id}$. (3) $G(S_\sigma x, s_0) = G(x, \sigma s_0)$ is continuous and, by Corollary 5.3 applied in the second argument via monotonicity of $g_{0,x}$ — indeed $\sigma \mapsto G(x, \sigma s_0)$ is nondecreasing since Bernstein functions are nondecreasing, and strictly increasing because $g_{0,x}$, being a nonzero element of $\mathrm{BF}_0$, is strictly increasing (its derivative is CM and not identically zero, hence positive) — strictly increasing in $\sigma$; composing with the continuous strictly increasing inverse of $G(\cdot, s_0)$ gives (3). (4) If $S_\sigma x^* = x^*$ for all $\sigma$ then $G(x^*, s) = G(x^*, \sigma s)$ for all $\sigma, s$, so $G(x^*, \cdot)$ is constant $= G(x^*, 0{+}) = 0$, i.e. $\Phi_{0,x^*} = \mathrm{Id}$; (ND) forces $x^* = 0$. ∎

**Proposition 6.3 (orbit coordinate; the gauge).** Assume (A1)–(A8), (ND). Then the map $c(\sigma) := S_\sigma 1$ is a continuous strictly increasing bijection of $(0,\infty)$ onto $(0,\infty)$ with $c(1) = 1$. Consequently

$$\chi := c^{-1} : (0,\infty) \to (0,\infty), \qquad \chi(0) := 0,$$

is an increasing bijection ("the canonical gauge") satisfying $\chi(S_\sigma x) = \sigma\,\chi(x)$, and

$$G(x, s) = F\big(\chi(x)\, s\big), \qquad F := G(1, \cdot) \in \mathrm{BF}_0,\ F \not\equiv 0. \tag{6.2}$$

*Proof.* By Lemma 6.2(3), $c$ is continuous. It is injective: if $c(\sigma) = c(\tau)$ with $\rho := \sigma/\tau \ne 1$ then $S_\rho 1 = 1$ by the group law, hence $F(s) = G(1,s) = G(S_\rho 1, s) = G(1, \rho s) = F(\rho s)$ for all $s$; iterating along $\rho^{\pm n}$ and using $F(0{+}) = 0$ gives $F \equiv 0$, contradicting (ND) via Corollary 5.3. Being continuous and injective on a connected set, $c$ is strictly monotone; since $\sigma > 1$ gives $F(\sigma s) \ge F(s)$ with strict inequality somewhere (same iteration argument), Corollary 5.3 forces $S_\sigma 1 > 1$, so $c$ is increasing. Its limits as $\sigma \to 0{+}, \infty$ are fixed points of the action or boundary points of $[0, \infty]$; by Lemma 6.2(4) they must be $0$ and $\infty$. Hence $c$ is a bijection onto $(0,\infty)$. The relation $\chi(S_\sigma x) = \sigma\chi(x)$ follows from the group law: $S_\sigma x = S_\sigma S_{\chi(x)} 1 = S_{\sigma\chi(x)}1$. Finally, for $x > 0$,

$$G(x, s) = G\big(S_{\chi(x)} 1,\, s\big) = G\big(1,\, \chi(x)\, s\big) = F\big(\chi(x)\,s\big),$$

and $F = g_{0,1} \in \mathrm{BF}_0$ by Theorem 5.2, $F \not\equiv 0$ by (ND). ∎

**Remark 6.4 (gauge freedom).** In the hemigroup setting the scale coordinate carries no intrinsic parametrization: replacing $x$ by any increasing bijection of $[0,\infty)$ yields an equivalent family. Proposition 6.3 fixes the *canonical gauge* $\tilde x := \chi(x)$, in which $S_\sigma$ acts by multiplication, scale carries the dimension of time, and $G(x,s) = F(\tilde x\, s)$. The powers $\tilde x \mapsto \tilde x^{\,\alpha}$ parametrize the other homogeneous gauges; the *parabolic gauge* $\alpha = 1/2$ is the natural one for the diffusive memory-line realization and will be used in the sequel.

## 7. Self-decomposability and the main theorem

By Proposition 6.3 the exponent of every kernel is an increment $F(bs) - F(as)$, $0 \le a \le b$, and by Theorem 5.2 every such increment must lie in $\mathrm{BF}_0$. This pins down $F$:

**Lemma 7.1 (self-decomposable exponents).** For $F \in \mathrm{BF}_0$ the following are equivalent:

1. $F(b\,\cdot) - F(a\,\cdot) \in \mathrm{BF}_0$ for all $0 < a \le b$;
2. $B(s) := s\,F'(s)$ is a Bernstein function;
3. $F$ has the representation

$$F(s) = b_0\, s + \int_0^\infty \big(1 - e^{-st}\big)\, \frac{k(t)}{t}\,dt, \qquad b_0 \ge 0, \tag{7.1}$$

with $k : (0,\infty) \to [0,\infty)$ nonincreasing (and $\int_0^1 k < \infty$, $\int_1^\infty k(t)/t\,dt < \infty$).

*Proof.* (1) ⇒ (2): For $h > 0$, $s \mapsto \big(F(e^h s) - F(s)\big)/h \in \mathrm{BF}$; as $h \downarrow 0$ it converges pointwise to $sF'(s)$ ($F$ is smooth on $(0,\infty)$), which is therefore Bernstein by Proposition 2.3(4).

(2) ⇒ (1): $F(bs) - F(as) = \int_{\log a}^{\log b} B(e^u s)\,du$; each integrand is Bernstein in $s$, hence so is the (finite) mixture, by Proposition 2.3(4); vanishing at $0{+}$ follows from monotone convergence.

(2) ⇔ (3): Write $F(s) = b_0 s + \int (1 - e^{-st})\,\nu(dt)$ (no killing term since $F(0{+}) = 0$), so that

$$B(s) = s F'(s) = b_0 s + \int_0^\infty s\,t\, e^{-st}\, \nu(dt).$$

Note $B(0{+}) = 0$ since $0 \le sF'(s) \le F(s)$ by concavity. Suppose $\nu(dt) = k(t)\,t^{-1}dt$ with $k$ nonincreasing; writing $k(t) = \rho\big((t,\infty)\big)$ for the positive measure $\rho = -dk$ (right-continuity may be assumed; $k(\infty) = 0$ is forced by $\int^\infty k(t)t^{-1}dt < \infty$), Tonelli gives

$$\int_0^\infty s\, e^{-st}\, k(t)\, dt = \int_0^\infty \rho(du) \int_0^u s\,e^{-st}\,dt = \int_0^\infty \big(1 - e^{-su}\big)\,\rho(du),$$

so $B(s) = b_0 s + \int (1 - e^{-su})\rho(du) \in \mathrm{BF}_0$. Conversely, if $B \in \mathrm{BF}$ then $B \in \mathrm{BF}_0$ (shown above), so $B(s) = \beta s + \int (1 - e^{-su})\rho(du)$; running the same computation backwards and invoking uniqueness of the Lévy–Khintchine triple (Proposition 2.3(3)) identifies $\beta = b_0$ and $\nu(dt) = k(t)t^{-1}dt$ with $k(t) = \rho((t,\infty))$ nonincreasing. ∎

**Remark 7.2.** Condition (3) is the classical characterization of the Laplace exponents of *self-decomposable* laws on $[0,\infty)$ (laws of $L$-class); see [Sato, Ch. 3]. Probabilistically, (7.1) together with the similarity structure below says that the kernels are the marginal laws of a *self-similar additive process* ("Sato subordinator"): an increasing process $(T_{\tilde x})_{\tilde x \ge 0}$ with independent (not stationary) increments and $T_{\sigma \tilde x} \stackrel{d}{=} \sigma\, T_{\tilde x}$.

**Theorem 7.3 (Main theorem; the variant of [Fagerström 2005, Thm. 2]).** A family $(\Phi_{x,y})_{0 \le x \le y}$ satisfies (A1)–(A8) and (ND) **iff** there exist an increasing bijection $\chi$ of $[0,\infty)$ (the gauge) and a function $F$ of the form (7.1) with $F \not\equiv 0$ such that

$$\Phi_{x,y} f = \mu_{x,y} * f, \qquad \hat\mu_{x,y}(s) = \exp\Big[-\big(F(\chi(y)\,s) - F(\chi(x)\,s)\big)\Big].$$

In particular, in the canonical gauge the scale-space kernels are

$$\phi_{x}(t) \;=\; \mathcal{L}^{-1}\Big[\, e^{-F(x\,s)} \,\Big](t), \qquad F \text{ as in } (7.1),$$

and the pair $(\chi, F)$ is unique up to the normalization $\chi(1) = 1$.

*Proof.* (⇒) Lemmas 4.1–4.2, 5.1, Theorem 5.2, Corollary 5.3, Lemma 6.1–6.2, Proposition 6.3 give the representation with $F = G(1,\cdot) \in \mathrm{BF}_0$, $F \not\equiv 0$; since every increment $F(\chi(y)s) - F(\chi(x)s)$ lies in $\mathrm{BF}_0$ and $\chi$ is onto $(0,\infty)$, Lemma 7.1 applies and yields (7.1).

(⇐) Let $F$ be of the form (7.1), $F \not\equiv 0$; work in the canonical gauge. For $0 \le a \le b$, $g_{a,b}(s) := F(bs) - F(as) \in \mathrm{BF}_0$ by Lemma 7.1, so $e^{-g_{a,b}}$ is CM with value $1$ at $0{+}$ (Proposition 2.3(2)), hence by the Bernstein–Widder criterion (Proposition 2.3(1)) it is the Laplace transform of a unique probability measure $\mu_{a,b}$ on $[0,\infty)$. Define $\Phi_{a,b} f := \mu_{a,b} * f$. Then (A1)–(A5) hold by Lemma 4.1 (converse direction); (A6) holds since exponents add: $g_{a,b} + g_{b,c} = g_{a,c}$ and Laplace transforms determine measures; (A8) holds with $S_\sigma x = \sigma x$ by Lemma 6.1, since $\hat\mu_{\sigma a, \sigma b}(s) = \hat\mu_{a,b}(\sigma s)$; (ND) holds since $F$ is strictly increasing (Lemma 2.4 applied to $F$). For (A7): if $(a_n, b_n) \to (a,b)$ then $\hat\mu_{a_n,b_n} \to \hat\mu_{a,b}$ pointwise (continuity of $F$), hence $\mu_{a_n,b_n} \to \mu_{a,b}$ weakly by the continuity theorem for Laplace transforms [Feller, XIII.1]; weak convergence of probability measures implies $\mu_{a_n,b_n} * f \to \mu_{a,b} * f$ in $L^1$ for every $f \in X$: writing $\mu * f = \int \tau_r f\, \mu(dr)$ as an $X$-valued Bochner integral, the map $r \mapsto \tau_r f$ is bounded and continuous, weak convergence supplies tightness, and a standard $\varepsilon/3$ argument on a compact carrying mass $1 - \varepsilon$ concludes.

Uniqueness of $(\chi, F)$ with $\chi(1) = 1$: $F$ is recovered as $g_{0,1}$ and $\chi(x)$ as the unique $c$ with $g_{0,x} = F(c\,\cdot)$, using strict monotonicity of $F$. ∎

**Corollary 7.4 (recovering the semigroup case).** Assume in addition that the family is one-parameter: $\Phi_{x,y}$ depends only on $y - x$. Then, after normalization $g_{0,1}(1) = 1$,

$$F(s) = s^{\alpha} \quad \text{for some } 0 < \alpha \le 1,$$

i.e. the kernels are exactly the extremal stable densities of [Fagerström 2005, Thm. 2], together with the boundary case $\alpha = 1$ (pure delay: $\mu_{0,x} = \delta_x$).

*Proof.* Homogeneity gives $g_{x,y} = (y - x)\,g$ with $g := g_{0,1}$, and (6.1) becomes $(S_\sigma y - S_\sigma x)\, g(s) = (y - x)\, g(\sigma s)$; hence $S_\sigma$ is affine and, fixing $0$, linear: $S_\sigma x = c(\sigma) x$, with $c(\sigma) g(s) = g(\sigma s)$. Then $c$ is a continuous multiplicative homomorphism, $c(\sigma) = \sigma^\alpha$ (Cauchy's equation, as in [Fagerström 2005, Lemma 2]), and $g(\sigma s) = \sigma^\alpha g(s)$ forces $g(s) = g(1) s^\alpha$. Bernstein-ness restricts $\alpha \in (0, 1]$; the value $\alpha = 1$ gives $sF' = s \in \mathrm{BF}$, so it is admitted by the present axioms. ∎

**Remark 7.5 (the boundary case $\alpha = 1$ and the drift term).** [Fagerström 2005] excluded $\alpha = 1$ through the pointwise-continuity requirement on the kernel functions, which the deterministic delay $\delta(t - x)$ violates. Under Definition 3.1 the delay family — and more generally the drift term $b_0 s$ in (7.1), which shifts every kernel by $b_0 x$ — is admissible. If undesired, it is removed by one additional axiom, e.g. absolute continuity of the kernels for $x > 0$, or the requirement $\lim_{s\to\infty} F(s)/s = 0$ (no deterministic front).

**Remark 7.6 (geometry of the class; extreme rays).** The admissible set of Theorem 7.3 is a convex cone, and it carries an exact Choquet structure. Writing $\rho := -dk$ for the Lebesgue–Stieltjes measure of the nonincreasing $k$ (so $k(t) = \rho((t,\infty))$), Tonelli turns (7.1) into the *unique* linear representation

$$F(s) \;=\; b_0\,s \;+\; \int_{(0,\infty)} \mathrm{Ein}(\tau s)\,\rho(d\tau), \qquad \mathrm{Ein}(z) := \int_0^z \frac{1 - e^{-u}}{u}\,du,$$

the pairs that occur being exactly those with $b_0 \ge 0$ and $\int_{(0,\infty)} \big[\tau \wedge (1 + \log_+ \tau)\big]\,\rho(d\tau) < \infty$ — since $\mathrm{Ein}(z) \le z$ and $\mathrm{Ein}(z) = \log z + \gamma_E + o(1)$ as $z \to \infty$, that condition is precisely the finiteness of $F$. So $(b_0, \rho)$ are simplex coordinates and the extreme rays of the cone are the pure delay together with the one-parameter family $\mathrm{Ein}(\tau\,\cdot)$ — the Laplace exponents, with Lévy density $t^{-1}\mathbf{1}_{(0,\tau)}(t)$, of the *dilated Dickman subordinators* [Caravenna–Sun–Zygouras 2019]. Every admissible family is a unique superposition of Dickman rays and drift. None of the distinguished families of this paper is extreme; each is a slice cut by a different principle — the stable family by dilation symmetry (Corollary 7.4), the Gamma family as the atoms of the Thorin representation (Example 8.2, Proposition 13.6), the Bessel family by locality (Theorem 12.5). Since all three have completely monotone $k$, the closed convex cone that the three corners generate together is exactly the Thorin subclass of Proposition 13.6 — strictly smaller than the whole class, the difference being the non-CM monotone memory kernels (plateaus, kinks, hard cutoffs). The Dickman rays are the paradigm of the difference: their kernels solve the delay equation obtained from (9.2) with the step kernel $k = \mathbf{1}_{[0,\tau)}$ and carry derivative singularities at the delays $\tau, 2\tau, \dots$ — echo signatures unattainable within the Thorin subclass. Two universal bounds nevertheless hold across the entire cone: every kernel is absolutely continuous [Sato, Thm. 27.13] and, by Yamazato's theorem on class-$L$ laws, *unimodal* [Yamazato 1978] — the axioms never produce multimodal kernels. Finally, every extreme ray has $F(s) \sim \log s$ and hence $z_* = 1$: the extreme boundary of the cone lies exactly on the boundary of hypothesis (H) of §11, so the third open problem of §15 is, in retrospect, the theory of the cone's extreme points.

## 8. Examples and moments

Throughout, canonical gauge; $\phi_x = \mathcal{L}^{-1}[e^{-F(x s)}]$, and $T_x$ denotes a random variable with density $\phi_x$.

**Example 8.1 (extremal stable; the 2005 family).** $F(s) = s^\alpha$, $0 < \alpha < 1$: $k(t) = \tfrac{\alpha}{\Gamma(1-\alpha)}\, t^{-\alpha}$, nonincreasing. All moments are infinite; the delay must be measured by the mode, which scales as $x^{1/\alpha}$.

**Example 8.2 (Gamma family).** $F(s) = \gamma\,\log(1 + s)$, $\gamma > 0$: here $k(t) = \gamma\, e^{-t}$, nonincreasing, and

$$e^{-F(xs)} = (1 + x s)^{-\gamma}, \qquad \phi_x(t) = \frac{t^{\gamma - 1} e^{-t/x}}{\Gamma(\gamma)\, x^{\gamma}},$$

the Gamma density with fixed shape $\gamma$ and scale $x$. All moments are finite; $\mathbb{E}\,T_x = \gamma x$, $\operatorname{Var} T_x = \gamma x^2$. The increment measures $\mu_{a,b}$ have Laplace transform $\big(\tfrac{1 + as}{1 + bs}\big)^{\gamma}$ and are the increments of the Gamma-type Sato subordinator.

**Example 8.3 (Bessel-K family; preview of the memory line).** For $a > 0$ let $F$ be the exponent of the scaled inverse-gamma law $T_1 \stackrel{d}{=} 1/(2\gamma_a)$,

$$e^{-F(s)} = \frac{2^{1-a}}{\Gamma(a)}\,\big(\sqrt{2s}\big)^{a} K_a\big(\sqrt{2s}\big),$$

which is self-decomposable (as a limiting generalized-inverse-Gaussian law, [Halgreen 1979]). In the parabolic gauge $\tilde x = x^2/2$ these are the boundary-hitting kernels of the Bessel-type media $\tfrac12\partial_x^2 + \tfrac{\beta}{x}\partial_x$, $a = \tfrac12 - \beta$; moments satisfy $\mathbb{E}\,T_x^n < \infty$ iff $a > n$. This family is the subject of the memory-line development (Theorems 10.4, 11.6 and 12.5).

**Proposition 8.4 (moments and the influence curve).** $\mathbb{E}\,T_x = x\,F'(0{+}) = x\Big(b_0 + \int_0^\infty k(t)\,dt\Big)$, finite iff $k$ is integrable at infinity; more generally $\mathbb{E}\,T_x^n < \infty$ iff $\int_1^\infty t^{\,n-1} k(t)\,dt < \infty$. When the mean is finite, the influence curve of [Fagerström 2005, §7] can be defined by the mean delay and is exactly linear in the canonical gauge:

$$t_0 - t_m = F'(0{+})\; x .$$

*Proof.* $\mathbb{E}\,T_x = -\partial_s\, e^{-F(xs)}\big|_{s=0{+}} = x F'(0{+})$, and $F'(0{+}) = b_0 + \int k(t)\,dt$ by monotone convergence in (7.1); the higher-moment criterion follows from $\int t^n\,\nu(dt) = \int t^{\,n-1}k(t)\,dt$ and the standard equivalence between moments of an infinitely divisible law and of its Lévy measure at infinity [Sato, Thm. 25.3]. ∎

**Remark 8.5.** The heavy tails of the 2005 kernels are thus an artifact of the semigroup axiom, not of causality plus covariance: within Theorem 7.3 the semigroup sub-case (Corollary 7.4) is precisely the subset with $k$ a pure power — the only $k$ compatible with homogeneity — and every non-power nonincreasing $k$, e.g. $k(t) = \gamma e^{-t}$, yields a causal, continuously scale-covariant family with finite moments of all orders.

## 9. Memory kernels, Sonine conservation, and a Volterra derivation

The representation (7.1) attaches to every admissible family a nonincreasing function $k$. This section shows that $k$ is the *memory kernel* of the evolution across scale, that it forms a Sonine pair with the associated potential kernel — the conservation identity $\kappa * \ell \equiv 1$ — and that the kernels of Theorem 7.3 can be obtained from $k$ by solving a linear Volterra integral equation, without Laplace inversion. The section is self-contained: the scale-evolution result needed here is stated and proved as Proposition 9.2.

Throughout: canonical gauge; a function $f \in X$ is *causal* if it vanishes a.e. on $(-\infty, 0)$, in which case $\hat f(s) = \int_0^\infty e^{-st} f(t)\,dt$ is defined for $s > 0$ with $|\hat f(s)| \le \|f\|_1$.

**Lemma 9.1 (the kernel behind $F'$).** Let $F$ be as in (7.1). Then

$$F'(s) \;=\; b_0 \;+\; \int_0^\infty e^{-st}\, k(t)\,dt, \qquad s > 0.$$

Consequently, defining for $x > 0$ the locally finite measure

$$\kappa^{(x)}(dt) \;:=\; b_0\,\delta_0(dt) \;+\; \tfrac{1}{x}\,k\big(\tfrac{t}{x}\big)\,dt,$$

we have $\partial_x F(xs) = s\,F'(xs) = s\,\widehat{\kappa^{(x)}}(s)$.

*Proof.* Differentiating the integrand of (7.1) in $s$ gives $e^{-st}k(t)$, which for $s \ge s_0 > 0$ is dominated by $e^{-s_0 t} k(t)$; this is integrable near $0$ by $\int_0^1 k < \infty$ and at infinity because $k$ is bounded there ($k$ nonincreasing), so differentiation under the integral is justified. The second statement is the substitution $\tau = t/x$ in $F'(xs) = b_0 + \int_0^\infty e^{-xs\tau} k(\tau)\,d\tau$. ∎

Thus the memory kernel of the scale flow is the self-decomposability function $k$ itself, in $L^1$-normalized dilation to the current scale; the monotonicity of $k$, which entered abstractly as condition (3) of Lemma 7.1, is precisely the admissibility of $\kappa^{(x)}$ as a Lévy tail. In the extremal stable case $k(t) = \alpha t^{-\alpha}/\Gamma(1-\alpha)$ and the operator $\partial_t(\kappa^{(x)} * \cdot)$ below is the Riemann–Liouville derivative $D^{\alpha}_{t,+}$ of [Fagerström 2005]; in the Gamma family $k(t) = \gamma e^{-t}$, a bounded kernel.

**Proposition 9.2 (scale evolution in memory-kernel form).** Let $(\Phi_{x,y})$ be as in Theorem 7.3, in the canonical gauge, let $f \in X$ be causal, and set $u(\cdot, x) := \Phi_{0,x} f = \mu_{0,x} * f$. Then:

1. For each $s > 0$, $\hat u(s, x) = e^{-F(xs)} \hat f(s)$ is continuously differentiable in $x$ with

$$\partial_x \hat u(s, x) \;=\; -\,s\,F'(xs)\,\hat u(s, x).$$

2. For each $x > 0$ the causal function $w(\cdot, x) := \kappa^{(x)} * u(\cdot, x)$ is in $L^1_{\mathrm{loc}}$, and for all $0 \le a \le b$,

$$u(\cdot, b) - u(\cdot, a) \;=\; -\,\partial_t \int_a^b \big(\kappa^{(x)} * u(\cdot, x)\big)\,dx \qquad \text{in } \mathcal{D}'(\mathbb{R}).$$

Differentiating in $x$: $u$ satisfies, in the distributional sense on $\mathbb{R}_t \times (0,\infty)_x$ and with boundary value $u(\cdot, 0) = f$,

$$\partial_x u \;=\; -\,\partial_t\big(\kappa^{(x)} * u\big) \;=\; -\,b_0\,\partial_t u \;-\; \partial_t \int_0^t \tfrac{1}{x}\,k\big(\tfrac{t-r}{x}\big)\,u(r, x)\,dr .$$

Since $u(\cdot, x)$ is causal, the outer $\partial_t$ may equivalently be moved onto $u$ inside the convolution: the Riemann–Liouville and Caputo forms of the operator coincide on this family.

*Proof.* (1) is the chain rule; $F$ is smooth on $(0,\infty)$ (Proposition 2.3(3)).

(2) Local integrability: for $T > 0$, $\int_0^T |w(t,x)|\,dt \le \kappa^{(x)}([0,T])\,\|u(\cdot,x)\|_1 \le \big(b_0 + \int_0^{T/x} k\big)\|f\|_1 < \infty$, locally uniformly in $x > 0$; joint measurability follows from (A7). By Tonelli, for $s > 0$,

$$\hat w(s, x) = \widehat{\kappa^{(x)}}(s)\,\hat u(s, x) = F'(xs)\,\hat u(s, x) .$$

Integrate (1) over $x \in [a, b]$; the exchange of $\int_a^b dx$ with the Laplace integral is justified by Tonelli since $\int_a^b s\,F'(xs)\,\hat{|u|}\ldots dx \le \|f\|_1 \int_a^b s F'(xs)\,dx = \|f\|_1\big(F(bs) - F(as)\big) < \infty$ (finite also for $a = 0$). This gives

$$\hat u(s, b) - \hat u(s, a) \;=\; -\,s \int_a^b \hat w(s, x)\,dx \;=\; -\,s\,\widehat{W}(s), \qquad W := \int_a^b w(\cdot, x)\,dx \in L^1_{\mathrm{loc}},\ \text{causal}.$$

Hence the causal, locally integrable function $V(t) := \int_0^t \big(u(r, b) - u(r, a)\big)\,dr + W(t)$ has Laplace transform $\big(\hat u(s,b) - \hat u(s,a)\big)/s + \widehat W(s) = 0$ for every $s > 0$, so $V = 0$ a.e. by uniqueness of the Laplace transform [Feller, XIII.1]. This is the displayed identity. The last statement holds because $u(\cdot, x)$ vanishes on $(-\infty, 0)$, so no boundary term arises when moving $\partial_t$ through the convolution. ∎

**Remark 9.3.** Proposition 9.2 is the memory-kernel form of the per-scale generator; Theorem 10.4 below upgrades it to a classical scale-Cauchy problem $\partial_x u = -\varphi_x(\partial_t)u$, $\varphi_x(s) = sF'(xs)$, on an explicit operator core. It identifies the scale evolution as a *general fractional* relaxation equation in the sense of Kochubei and Luchko, with scale-dilated kernel; the case $k(t) = \alpha t^{-\alpha}/\Gamma(1-\alpha)$ recovers the fractional scale-Cauchy problem of [Fagerström 2005, Thm. 3].

**Lemma 9.4 (potential kernel).** For $x > 0$ set $\varphi_x(s) := s F'(xs)$. Then $\varphi_x$ is a nonzero Bernstein function, positive on $(0,\infty)$, and there is a unique positive, locally finite measure $\ell^{(x)}$ on $[0,\infty)$ — the *potential kernel* — with

$$\widehat{\ell^{(x)}}(s) \;=\; \frac{1}{\varphi_x(s)} \;=\; \frac{1}{s\,F'(xs)}, \qquad s > 0.$$

Moreover $\ell^{(x)} = x \cdot \big(\text{pushforward of } \ell^{(1)} \text{ under } t \mapsto xt\big)$; in density form, $\ell^{(x)}(t) = \ell^{(1)}(t/x)$.

*Proof.* With $B(s) := sF'(s) \in \mathrm{BF} \setminus \{0\}$ (Lemma 7.1(2)), $\varphi_x(s) = B(xs)/x \in \mathrm{BF} \setminus \{0\}$, and $\varphi_x > 0$ on $(0,\infty)$ by Lemma 2.4. The function $u \mapsto 1/u$ is completely monotone on $(0,\infty)$, and the composition of a CM function with a positive Bernstein function is CM [SSV, Thm. 3.7]; hence $1/\varphi_x$ is CM, and by the Bernstein–Widder theorem in its general form [Feller, XIII.4; SSV, Thm. 1.4] it is the Laplace transform of a unique positive measure on $[0,\infty)$, locally finite since the transform is finite for $s > 0$. The scaling law follows by comparing transforms: $\widehat{\ell^{(x)}}(s) = x/B(xs) = x\,\widehat{\ell^{(1)}}(xs)$. ∎

**Theorem 9.5 (Sonine conservation).** For every $x > 0$,

$$\kappa^{(x)} * \ell^{(x)} \;=\; \mathrm{Leb}_{[0,\infty)}, \qquad \text{i.e.} \qquad \int_{[0,t]} \ell^{(x)}\big([0,\, t - r]\big)\,\kappa^{(x)}(dr) \;=\; t \quad \text{for all } t \ge 0.$$

*Proof.* Both sides are locally finite measures on $[0,\infty)$ with finite Laplace transforms, and these transforms agree: $\widehat{\kappa^{(x)}}(s)\,\widehat{\ell^{(x)}}(s) = \tfrac{\varphi_x(s)}{s}\cdot\tfrac{1}{\varphi_x(s)} = \tfrac{1}{s} = \widehat{\mathrm{Leb}}(s)$. Uniqueness of the Laplace transform concludes. ∎

Note the scaling structure: $\kappa^{(x)}$ dilates with $L^1$ normalization, $\ell^{(x)}$ with sup normalization (Lemma 9.4), and it is exactly this mismatch that renders the identity scale-invariant — the pair $(\kappa^{(x)}, \ell^{(x)})$ is itself scale-covariant.

**Corollary 9.6 (exact invertibility; conservation of information).** Define, on causal $v \in X$, the generalized derivative and integral

$$D^{(x)} v := \partial_t\big(\kappa^{(x)} * v\big), \qquad I^{(x)} v := \ell^{(x)} * v .$$

Then $D^{(x)} I^{(x)} v = v$ (in $\mathcal{D}'$, hence a.e.).

*Proof.* By Theorem 9.5 and associativity of convolution (Tonelli on causal supports), $\kappa^{(x)} * \ell^{(x)} * v = \mathrm{Leb} * v = \int_0^{\,\cdot} v(r)\,dr$, and $\partial_t \int_0^t v = v$. ∎

Corollary 9.6 is the conservation content of the axioms in Volterra form: the infinitesimal smoothing applied at each scale is exactly invertible, so no single step of the cascade destroys information — it only redistributes it, consistently with (A5), which fixes the mass. Probabilistically, $\ell^{(x)}$ is the potential (renewal) measure of the subordinator with exponent $\varphi_x$, $\kappa^{(x)}$ its drift-plus-Lévy-tail, and Theorem 9.5 is the renewal identity balancing expected occupation against tail decay.

**Proposition 9.7 (regularity of the pair).** Modulo the drift atoms $b_0\delta_0$:

1. For every admissible $F$, the pair $(\kappa^{(x)}, \ell^{(x)})$ exists at the level of positive measures (Lemmas 9.1, 9.4) and satisfies Theorem 9.5.
2. $\ell^{(x)}$ has the form $c\,\delta_0 + (\text{nonincreasing density})$, $c \ge 0$, if and only if $1/F'$ is a Bernstein function (equivalently, $\varphi_x$ is a *special* Bernstein function; by dilation invariance the condition does not depend on $x$) [SSV, Thm. 11.3].
3. $\kappa^{(x)}$ has a completely monotone density iff $k$ is completely monotone, which holds iff $F'$ belongs to the Stieltjes class $\mathcal{S} := \{\,h(s) = \tfrac{a}{s} + b + \int_{(0,\infty)} \tfrac{\sigma(d\tau)}{s + \tau}\,\}$ [SSV, Ch. 2]. In that case $\ell^{(x)}$ also has a (drift-atom plus) completely monotone density, i.e. $(\kappa^{(x)}, \ell^{(x)})$ is a classical Sonine pair of CM kernels; moreover $k$ CM implies $F$ is a complete Bernstein function.

*Proof.* (2) is the characterization of potential measures of special subordinators. (3) Dilation preserves complete monotonicity, so the first equivalence reduces to $k$. If $k$ is CM, $k = \int e^{-\tau t}\sigma(d\tau)$ for a positive measure $\sigma$, and Lemma 9.1 gives $F'(s) = b_0 + \int \sigma(d\tau)/(s+\tau) \in \mathcal{S}$; conversely, an $\mathcal{S}$-representation of $F'$ must have $a = 0$ (an $a/s$ term corresponds to an additive constant in $k$, contradicting $\int_1^\infty k(t)t^{-1}dt < \infty$), and then $k(t) = \int e^{-\tau t}\sigma(d\tau)$ is CM. Next, for $h \in \mathcal{S}\setminus\{0\}$ one has $1/h \in \mathrm{CBF}$ [SSV, Thm. 7.3], so $g := 1/F'(x\,\cdot) \in \mathrm{CBF}$, and $\widehat{\ell^{(x)}}(s) = g(s)/s$; writing the Lévy–Khintchine triple of $g$ as $(a_g, b_g, \nu_g)$ with CM Lévy density [SSV, Thm. 6.2], $g(s)/s = \tfrac{a_g}{s} + b_g + \widehat{\bar\nu_g}(s)$, i.e. $\ell^{(x)} = b_g\,\delta_0 + \big(a_g + \bar\nu_g(t)\big)\,dt$, and $a_g + \bar\nu_g(t) = a_g + \int_t^\infty (\text{CM})$ is CM. Finally $k$ CM implies the Lévy density $k(t)/t$ of $F$ is CM (product of CM functions), hence $F \in \mathrm{CBF}$ [SSV, Thm. 6.2]. ∎

Part (3) delineates exactly where the classical Sonine calculus with completely monotone kernel pairs — the standing hypothesis of most of the general-fractional-calculus literature — applies: on the complete-Bernstein subfamily, which the outlook (§12) identifies with the locality corner of the memory-line realization. For general admissible $F$ the pair, and Theorem 9.5, live at measure level.

**Proposition 9.8 (Volterra equation for the kernels).** Let $F$ be as in (7.1), $x > 0$, and $\mu_x := \mu_{0,x}$. Then, as measures on $[0,\infty)$,

$$t\,\mu_x(dt) \;=\; \big(\theta_x * \mu_x\big)(dt), \qquad \theta_x(dt) := b_0\,x\,\delta_0(dt) + k\big(\tfrac{t}{x}\big)\,dt, \tag{9.1}$$

and $\mu_x$ is the *unique* probability measure on $[0,\infty)$ satisfying (9.1). If $k \not\equiv 0$, then $\mu_x$ is absolutely continuous [Sato, Thm. 27.13], with density $\phi_x$ solving the linear Volterra equation of the second kind

$$\big(t - b_0 x\big)\,\phi_x(t) \;=\; \int_0^t k\big(\tfrac{u}{x}\big)\,\phi_x(t - u)\,du \qquad \text{for a.e. } t > 0. \tag{9.2}$$

*Proof.* Laplace transforms: $\mathcal{L}[t\,\mu_x](s) = -\tfrac{d}{ds} e^{-F(xs)} = x F'(xs)\, e^{-F(xs)}$, while by Lemma 9.1 (substitution $\tau = t/x$), $\widehat{\theta_x}(s) = b_0 x + \int_0^\infty e^{-st} k(t/x)\,dt = x F'(xs)$; so both sides of (9.1) have the finite transform $x F'(xs)e^{-F(xs)}$ and coincide. Uniqueness: if $\nu$ is a probability measure on $[0,\infty)$ with $t\,\nu(dt) = \theta_x * \nu$, then $\hat\nu$ is differentiable on $(0,\infty)$ with $-\hat\nu'(s) = \mathcal{L}[t\nu](s) = xF'(xs)\,\hat\nu(s)$; solving this linear ODE with $\hat\nu(0{+}) = 1$ gives $\hat\nu(s) = e^{-F(xs)}$, hence $\nu = \mu_x$. Absolute continuity: $\mu_x$ is a nondegenerate self-decomposable law when $k \not\equiv 0$ (Remark 7.2), and nondegenerate self-decomposable distributions are absolutely continuous. Restricting (9.1) to densities yields (9.2). ∎

Equation (9.2) is the constructive counterpart of the inverse Laplace transform in Theorem 7.3: the kernels are *derived* from the memory kernel $k$ by Volterra integration. Note the role of the axioms in closing the derivation: (9.2) is linear and homogeneous, so it determines $\phi_x$ only up to a multiplicative constant — it is the unit-area axiom (A5) that selects the solution. Positivity of the solution is manifest from Picard iteration, all of whose terms are nonnegative.

**Example 9.9 (verification: the Gamma family).** For $F(s) = \gamma\log(1+s)$ we have $b_0 = 0$, $k(u) = \gamma e^{-u}$, and $\phi_x(t) = t^{\gamma-1}e^{-t/x}/(\Gamma(\gamma)x^\gamma)$ (Example 8.2). Indeed, since $e^{-u/x}e^{-(t-u)/x} = e^{-t/x}$,

$$\int_0^t \gamma e^{-u/x}\,\frac{(t-u)^{\gamma-1} e^{-(t-u)/x}}{\Gamma(\gamma)\,x^{\gamma}}\,du \;=\; \frac{\gamma\, e^{-t/x}}{\Gamma(\gamma)\,x^{\gamma}} \cdot \frac{t^{\gamma}}{\gamma} \;=\; t\,\phi_x(t). \qquad \checkmark$$

**Remark 9.10 (computation; relation to the 2005 series).** For $F(s) = s^\alpha$, i.e. $k(u) = \alpha u^{-\alpha}/\Gamma(1-\alpha)$, Picard iteration of (9.2) regenerates, term by term, the series expansion following Theorem 2 of [Fagerström 2005]; the Volterra route thus contains the original series as its homogeneous special case. Numerically, (9.2) is a weakly singular Volterra equation of the second kind, amenable to standard product-integration quadrature, and provides an inversion-free forward scheme for the kernels for arbitrary admissible $k$.

**Remark 9.11 (literature).** Kernel pairs satisfying $\kappa * \ell \equiv 1$ go back to Sonine (1884); the operator calculus built on them is the general fractional calculus of Kochubei (2011) and Luchko (2021), usually developed under CM or Sonine-class kernel hypotheses, which by Proposition 9.7(3) delineate the complete-Bernstein subfamily. In Volterra-equation theory the kernels $\kappa^{(x)}$ are the *completely positive* kernels of Clément–Nohel; Prüss's resolvent theory then yields well-posedness and positivity of the evolution in Proposition 9.2 by purely deterministic arguments. The integral equation (9.1) is the classical characterization of infinitely divisible laws on the half-line of Steutel–van Harn.

## 10. The scale-Cauchy problem: Theorem 3′

This section upgrades Proposition 9.2 from a distributional identity to a classical Cauchy problem in the scale variable, on an explicit operator core. Throughout: canonical gauge, and

$$X_0 := L^1(\mathbb{R}_+),$$

identified with the causal elements of $X$; by (A3) every $\Phi_{x,y}$ restricts to $X_0$. On $X_0$ let $(T_r)_{r \ge 0}$ denote the *delay semigroup*, $(T_r f)(t) = f(t - r)\mathbf{1}_{t \ge r}$, a strongly continuous semigroup of positive isometries, and define the core

$$\mathcal{D} \;:=\; \big\{\, f \in X_0 :\ f \text{ absolutely continuous},\ f' \in X_0,\ f(0) = 0 \,\big\}.$$

**Lemma 10.1 (delay derivative).** $\mathcal{D}$ is dense in $X_0$ and invariant under every $T_r$ and every $\Phi_{x,y}$, and for $f \in \mathcal{D}$,

$$\lim_{h \downarrow 0} \tfrac{1}{h}\big(T_h f - f\big) = -\,f' \quad \text{in } X_0, \qquad \big\|T_r f - f\big\|_1 \le \min\big(2\|f\|_1,\ r\,\|f'\|_1\big).$$

*Proof.* Density is standard. Invariance under $T_r$: $T_r f$ is absolutely continuous, vanishes on $[0, r]$, and $(T_r f)' = T_r f'$. Invariance under $\Phi_{x,y} = \mu_{x,y} * \cdot$: from $f = \mathbf{1}_{[0,\infty)} * f'$ we get $\mu * f = \mathbf{1}_{[0,\infty)} * (\mu * f')$, so $\mu * f$ is absolutely continuous with derivative $\mu * f' \in X_0$ and value $0$ at $0$. For the limit: on $[h, \infty)$, $\tfrac{1}{h}(f(t-h) - f(t)) + f'(t) = -\tfrac{1}{h}\int_{t-h}^{t}\big(f'(\rho) - f'(t)\big)d\rho$, whose $L^1$-norm tends to $0$ by continuity of translation in $L^1$; on $[0, h)$ the contribution is $\tfrac{1}{h}\int_0^h |f| + \int_0^h |f'| \le \sup_{[0,h]}|f| + o(1) \to |f(0)| = 0$. The estimate follows from $T_r f - f = -\int_0^r T_\rho f'\,d\rho$ (Bochner), which is the integrated form of the limit, together with $\|T_\rho f'\|_1 = \|f'\|_1$ and the trivial bound. ∎

**Definition 10.2 (per-scale generator; Phillips form).** Let $\nu_1$ be the Lebesgue–Stieltjes measure $-dk$ on $(0,\infty)$ (with $k$ taken right-continuous, $k(\infty) = 0$), so that $\nu_1\big((r,\infty)\big) = k(r)$, and for $x > 0$ put $\nu_x := x^{-1}\cdot\big(\text{pushforward of } \nu_1 \text{ under } r \mapsto xr\big)$, i.e. $\nu_x\big((r,\infty)\big) = k(r/x)/x$. For $f \in \mathcal{D}$ define

$$\varphi_x(\partial_t)\, f \;:=\; b_0\, f' \;+\; \int_0^\infty \big(f - T_r f\big)\,\nu_x(dr) \;=\; b_0\, f' \;+\; \frac{1}{x}\int_0^\infty \big(f - T_{xr} f\big)\,\nu_1(dr).$$

**Lemma 10.3 (properties of the generator).** For $f \in \mathcal{D}$ and $x > 0$:

1. The integral converges absolutely in $X_0$, with $\|\varphi_x(\partial_t) f\|_1 \le b_0 \|f'\|_1 + \int_0^\infty \min\big(2\|f\|_1,\, xr\,\|f'\|_1\big)\,x^{-1}\nu_1(dr) < \infty$.
2. $\mathcal{L}\big[\varphi_x(\partial_t) f\big](s) = \varphi_x(s)\,\hat f(s)$ for $s > 0$, where $\varphi_x(s) = s F'(xs)$.
3. $\varphi_x(\partial_t)$ commutes with every $\Phi_{y,z}$ on $\mathcal{D}$: $\varphi_x(\partial_t)\,\Phi_{y,z} f = \Phi_{y,z}\,\varphi_x(\partial_t) f$.
4. $x \mapsto \varphi_x(\partial_t) f$ is continuous from $(0,\infty)$ to $X_0$.
5. $\kappa^{(x)} * f$ is (a.e. equal to) an absolutely continuous function with $\big(\kappa^{(x)} * f\big)' = \varphi_x(\partial_t) f$ a.e.; i.e. the Phillips form coincides with the memory-kernel operator of §9 on $\mathcal{D}$.

*Proof.* (1) Combine Lemma 10.1 with $\int (1 \wedge r)\,\nu_x(dr) < \infty$, which follows from $\int_0^1 k < \infty$ and $k(1) < \infty$ by integration by parts. (2) Termwise: $\mathcal{L}[f'] = s\hat f$ (using $f(0) = 0$), and $\mathcal{L}[f - T_rf] = (1 - e^{-sr})\hat f$; Fubini is justified by (1), and $b_0 s + \int(1 - e^{-sr})\nu_x(dr) = \varphi_x(s)$ by Lemma 9.1 (equality of the two Bernstein representations of $\varphi_x$). (3) Convolutions commute; pull $\Phi_{y,z}$ through the Bochner integral. (4) In the dilated form of Definition 10.2, the integrand $\tfrac1x(f - T_{xr}f)$ is, for $x$ in a compact subset of $(0,\infty)$, continuous in $x$ for each $r$ (strong continuity of $T$) and dominated by $C\min(\|f\|_1,\, r\|f'\|_1)$, which is $\nu_1$-integrable; apply dominated convergence, and treat the drift term trivially. (5) Both $\varphi_x(\partial_t)f \in L^1$ and $\kappa^{(x)} * f \in L^1_{\mathrm{loc}}$ are causal with finite Laplace transforms, and by (2) and Lemma 9.1 the causal function $V(t) := \int_0^t \varphi_x(\partial_t)f\,(\rho)\,d\rho - (\kappa^{(x)} * f)(t)$ has transform $\varphi_x(s)\hat f(s)/s - F'(xs)\hat f(s) = 0$ for all $s > 0$; hence $V = 0$ a.e. by uniqueness of the Laplace transform, which is the claim (the value $(\kappa^{(x)}*f)(0{+}) = 0$ follows from $\kappa^{(x)}([0,t]) \to b_0$ and $\sup_{[0,t]}|f| \to 0$). ∎

**Theorem 10.4 (Theorem 3′: the scale-Cauchy problem).** Let $(\Phi_{x,y})$ be as in Theorem 7.3, in the canonical gauge, and let $f \in \mathcal{D}$. Set $u(\cdot, x) := \Phi_{0,x} f$. Then:

1. $u(\cdot, x) \in \mathcal{D}$ for every $x \ge 0$;
2. $x \mapsto u(\cdot, x)$ belongs to $C\big([0,\infty); X_0\big) \cap C^1\big((0,\infty); X_0\big)$ and satisfies

$$\partial_x u(\cdot, x) \;=\; -\,\varphi_x(\partial_t)\,u(\cdot, x) \quad (x > 0), \qquad u(\cdot, 0) = f,$$

with $\partial_x$ a norm-derivative in $X_0$;

3. $u$ is the *unique* solution in the class of $v \in C([0,\infty); X_0) \cap C^1((0,\infty); X_0)$ with $v(\cdot, x) \in \mathcal{D}$ for $x > 0$, satisfying the equation for $x > 0$ and $v(\cdot, 0) = f$.

*Proof.* (1) is the $\Phi$-invariance of $\mathcal{D}$ (Lemma 10.1), and continuity at every $x \ge 0$ is (A7).

(2) Write $v(\cdot, x) := \varphi_x(\partial_t)\, u(\cdot, x)$. By Lemma 10.3(3), $v(\cdot, x) = \Phi_{0,x}\,\varphi_x(\partial_t) f$, so by Lemma 10.3(4), contractivity of $\Phi_{0,x}$, and (A7),

$$\|v(\cdot,x) - v(\cdot,x')\|_1 \;\le\; \big\|\varphi_x(\partial_t)f - \varphi_{x'}(\partial_t)f\big\|_1 + \big\|(\Phi_{0,x} - \Phi_{0,x'})\,\varphi_{x'}(\partial_t)f\big\|_1 \;\longrightarrow\; 0,$$

i.e. $x \mapsto v(\cdot, x)$ is continuous from $(0,\infty)$ to $X_0$. By Lemma 10.3(5) applied to $u(\cdot,x) \in \mathcal{D}$, each $\kappa^{(x)} * u(\cdot, x)$ is absolutely continuous with derivative $v(\cdot, x)$, vanishing at $0$; hence, for $0 < a \le b$, Fubini gives

$$\int_a^b \big(\kappa^{(x)} * u(\cdot, x)\big)(t)\,dx \;=\; \int_0^t \int_a^b v(\rho, x)\,dx\,d\rho ,$$

so the distributional $\partial_t$ in Proposition 9.2(2) evaluates to the Bochner integral $\int_a^b v(\cdot, x)\,dx$:

$$u(\cdot, b) - u(\cdot, a) \;=\; -\int_a^b v(\cdot, x)\,dx .$$

Since the integrand is continuous in $x$, the fundamental theorem of calculus for Bochner integrals yields $u \in C^1((0,\infty); X_0)$ with $\partial_x u = -v$, which is the equation.

(3) Let $v$ be any solution in the stated class and fix $s > 0$. Then $\eta(x) := \hat v(s, x)$ is continuous on $[0,\infty)$, and $C^1$ on $(0,\infty)$ with $\eta'(x) = \mathcal{L}[\partial_x v](s) = -\mathcal{L}[\varphi_x(\partial_t) v](s) = -\varphi_x(s)\,\eta(x)$ by Lemma 10.3(2) (differentiation and $\mathcal{L}$ exchange since $|\hat g(s)| \le \|g\|_1$). Solving the scalar linear ODE on $[\varepsilon, x]$ and letting $\varepsilon \downarrow 0$ using continuity at $0$:

$$\eta(x) = \hat f(s)\, e^{-F(xs)} .$$

Thus $\hat v(s, x) = \hat u(s, x)$ for all $s > 0$, and $v = u$ by uniqueness of the Laplace transform on $X_0$. ∎

**Proposition 10.5 (fixed-scale semigroups; core property).** For fixed $x > 0$, the operator $-\varphi_x(\partial_t)$ with domain $\mathcal{D}$ is closable, and its closure generates the strongly continuous contraction semigroup on $X_0$ of convolutions by the probability measures with Laplace transforms $e^{-\tau \varphi_x(s)}$, $\tau \ge 0$ — the semigroup subordinate to the delay semigroup via $\varphi_x$; $\mathcal{D}$ is a core. 

*Proof.* $\varphi_x$ is a Bernstein function without killing term (Lemma 9.4), so Phillips' subordination theorem [Phillips 1952; SSV, Ch. 13] applies to the delay semigroup, whose generator extends $f \mapsto -f'$ on $\mathcal{D}$ (Lemma 10.1): the subordinate generator is the closure of the Phillips form on the generator's domain. That $\mathcal{D}$ is a core follows since it is dense and invariant under the subordinate semigroup (which consists of convolutions, Lemma 10.1) [Engel–Nagel, Prop. II.1.7]. ∎

**Example 10.6 (Gamma family: time-recursive form).** For $F(s) = \gamma\log(1+s)$: $\nu_x(d\rho) = \gamma x^{-2} e^{-\rho/x}\,d\rho$, an exponential memory, and $\varphi_x(s) = \gamma s/(1 + xs)$, so

$$\varphi_x(\partial_t)\,u \;=\; \gamma\,\partial_t\big(1 + x\,\partial_t\big)^{-1} u \;=\; \gamma\, w', \qquad \text{where } w \text{ solves } w + x\,w' = u,\ \ w(0) = 0 .$$

The auxiliary variable $w$ is computed by one causal first-order ODE, so the scale step is realized by a single recursive low-pass filter — the strongest possible form of the time-recursivity requirement of [Fagerström 2005, §5]: the observer embodies its past in one first-order state per scale.

**Remark 10.7 (recovering Theorem 3 of 2005).** For $F(s) = s^\alpha$, $0 < \alpha < 1$: $\nu_x\big((\rho,\infty)\big) = \alpha x^{\alpha-1}\rho^{-\alpha}/\Gamma(1-\alpha)$ and $b_0 = 0$, so $\varphi_x(\partial_t) = \alpha x^{\alpha - 1} D^{\alpha}_{t,+}$ with $D^{\alpha}_{t,+}$ the Riemann–Liouville/Marchaud derivative, and Theorem 10.4 reads $\partial_x u = -\alpha x^{\alpha-1} D^{\alpha}_{t,+} u$. Under the reparametrization $\tau := x^{\alpha}$ this is exactly

$$\partial_\tau u \;=\; -\,D^{\alpha}_{t,+}\, u,$$

Theorem 3 of [Fagerström 2005] verbatim — identifying the scale parameter $\tau$ of that paper as the $\alpha$-gauge of Remark 6.4 applied to the canonical scale coordinate.

## 11. The signaling form: Theorem 4′

Theorem 4 of [Fagerström 2005] inverts the scale-Cauchy problem into an evolution *in time* over the memory line: $\partial_t u = D^{1/\alpha}_{x,-} u$ with boundary data $u(t, 0) = f(t)$ and $u(0, x) = 0$ — the signaling problem. The operator there is translation-invariant in $x$, which is available only in the homogeneous (semigroup) case. This section constructs the general inversion. The structural observation that replaces homogeneity is this: writing $H := e^{-F}$, the Laplace-domain profiles of the field,

$$\hat u(s, x) = \hat f(s)\, H(sx),$$

are *dilates of a single profile* $H$, with the eigenvalue $s$ appearing as the dilation parameter. Operators diagonal on dilation families are the subject of multiplicative harmonic analysis, so the inversion operator lives in the **Mellin calculus** — the multiplicative-group counterpart of the Wendel step of §4 on the additive group. Throughout: canonical gauge, so that $\mu_{0,x}$ is the law of $x\,T_1$ with $\mathbb{E}[e^{-sT_1}] = H(s)$; Mellin transform $\tilde g(z) := \int_0^\infty x^{z-1} g(x)\,dx$; Euler operator $\theta := x\,\partial_x$; and $(I^z f)(t) := \tfrac{1}{\Gamma(z)}\int_0^t (t-r)^{z-1} f(r)\,dr$ denotes the Riemann–Liouville integral of complex order $z$, $\operatorname{Re} z > 0$ [Samko–Kilbas–Marichev].

**Definition 11.1 (the standing hypothesis (H)).** An admissible exponent $F$ satisfies the *standing hypothesis* (H) if $F(\infty) = \infty$ (equivalently: $b_0 > 0$ or $\int_0^\infty k(t)\,t^{-1}dt = \infty$; no atom of the kernels at zero delay), and

$$z_* \;:=\; \sup\big\{\, \zeta > 0 :\ \mathbb{E}\big[T_1^{-\zeta}\big] < \infty \,\big\} \;>\; 1 .$$

The second condition is equivalent to $\int_0^\infty e^{-F(s)}\,ds < \infty$. It holds with $z_* = \infty$ whenever $b_0 > 0$, for the stable family, and for the Bessel-K family of Example 8.3; for the Gamma family $z_* = \gamma$, so (H) requires $\gamma > 1$ there. (The construction extends below $z_* = 1$ by meromorphic continuation; we do not pursue this.)

**Lemma 11.2 (Mellin data of the profile).** Under (H), for $0 < \operatorname{Re} z < z_*$,

$$\tilde H(z) \;=\; \Gamma(z)\;\mathbb{E}\big[T_1^{-z}\big],$$

analytic on the strip, with $|\tilde H(c + i\tau)| \le \mathbb{E}[T_1^{-c}]\,|\Gamma(c+i\tau)|$, hence absolutely integrable on every vertical line of the strip. Define the *inversion symbol*

$$B(-z) \;:=\; \frac{\tilde H(z+1)}{\tilde H(z)} \;=\; z\,\frac{\mathbb{E}\big[T_1^{-z-1}\big]}{\mathbb{E}\big[T_1^{-z}\big]}, \qquad 0 < \operatorname{Re} z < z_* - 1,$$

meromorphic on the strip, with poles only at the (isolated) zeros of $\tilde H$.

*Proof.* $\tilde H(z) = \int_0^\infty s^{z-1}\,\mathbb{E}[e^{-sT_1}]\,ds = \mathbb{E}\big[\int_0^\infty s^{z-1}e^{-sT_1}ds\big] = \mathbb{E}[T_1^{-z}]\,\Gamma(z)$ by Tonelli. The exchange is licensed by the strip condition and by nothing else: run on absolute values it reads $\int\!\!\int s^{c-1}e^{-ts}\,ds\,d\mu(t) = \Gamma(c)\,\mathbb{E}[T_1^{-c}]$ with $c = \operatorname{Re}z$, whose left side is the total mass of $|\cdot|$ for the product measure, so joint integrability holds *iff* the right side is finite, which is $c < z_*$. The same computation gives the bound, since $|T_1^{-z}| = T_1^{-c}$. (The first clause of (H) is used here, and only here: it gives $T_1 > 0$ a.s., without which the identity is false rather than merely unproved — at an atom $t = 0$ the inner integral $\int_0^\infty s^{c-1}ds$ diverges while $\mathbb{E}[T_1^{-c}]$, an integral over $(0,\infty)$, does not see the atom.)

For integrability along a vertical line, note that *quadratic* decay of $|\Gamma|$ suffices, and quadratic decay is the functional equation twice: $|\Gamma(\sigma + i\tau)| \le \Gamma(\sigma)$ for $\sigma > 0$, the imaginary part only rotating Euler's integrand; and $\Gamma(z+2) = (z+1)z\Gamma(z)$ with $|z|, |z+1| \ge |\tau|$ — both have imaginary part $\tau$ — so $|\Gamma(c+i\tau)|\,\tau^2 \le \Gamma(c+2)$. Adding, $|\Gamma(c+i\tau)|(1+\tau^2) \le \Gamma(c) + \Gamma(c+2)$, and $(1+\tau^2)^{-1}$ is integrable. (The classical asymptotic $|\Gamma(c+i\tau)| \sim \sqrt{2\pi}|\tau|^{c-1/2}e^{-\pi|\tau|/2}$ is of course stronger, but it needs Stirling in the complex plane and nothing below uses it.)

Analyticity is the identity read backwards rather than a separate argument: $m(z) := \mathbb{E}[T_1^{-z}] = \mathbb{E}[e^{-z\log T_1}]$ is the moment-generating function of $-\log T_1$, analytic on the interior of the set where the corresponding real exponential is integrable — which is $(0, z_*)$, the strip condition verbatim. So the strip of analyticity and the strip of the identity are the same strip for the same reason, and $\Gamma$ contributes the rest. Finally $\tilde H \not\equiv 0$, both factors being strictly positive at real points of the strip, so its zeros are isolated. ∎

**Definition 11.3 (the inversion operator).** Fix $c \in (0, z_* - 1)$. For $g$ with $\tilde g$ defined on the line $\operatorname{Re} z = c$ and $B(-z)\tilde g(z)$ absolutely integrable there, set

$$\big(A g\big)(x) \;:=\; \frac{1}{x}\cdot \frac{1}{2\pi i}\int_{(c)} x^{-z}\, B(-z)\,\tilde g(z)\,dz \;=\; \Big(\frac{1}{x}\,B(\theta)\,g\Big)(x),$$

the second expression being the functional-calculus reading (the Euler operator has Mellin symbol $-z$). The second equality is an assertion and not a rewriting, and it is worth being explicit about what it asserts: $B(\theta)$ is a functional calculus for a symbol with poles, so what the display says is that there *exists* a function $h$ on $(0,\infty)$ whose Mellin transform is $B(-z)\tilde g(z)$ on the line, and that the contour integral computes $h(x)/x$. Absolute integrability on the line is exactly the hypothesis under which the inversion integral recovers such an $h$ [Widder, Ch. VI, §9, Thm. 9a]. Given $h$, the rest is elementary: $Ag = h/x$ at every point of continuity of $h$, and hence, the weight $x^{-1}$ being a Mellin shift, $\widetilde{Ag}(z) = \tilde h(z-1)$ at every $z$ — which is the transform-level form $\widetilde{A g}(z) = B(1 - z)\,\tilde g(z - 1)$ wherever the identity defining $h$ holds pointwise. Every application below *exhibits* its $h$ rather than inferring it (for the profiles $g = H(s\,\cdot)$ it is $h(x) = s\,x\,H(sx)$, Theorem 11.6(1)), so the cited inversion theorem is available but never spent. Note finally the covariant scaling: $A$ commutes with dilations up to the weight $x^{-1}$, i.e. it scales like $\partial_t$ under $(t, x) \mapsto (\sigma t, \sigma x)$, as (A8) requires of any inversion.

**Lemma 11.4 (uniqueness of the symbol).** If two operators of the form $x^{-1}B_1(\theta)$, $x^{-1}B_2(\theta)$ both satisfy $A[H(s\,\cdot)] = s\,H(s\,\cdot)$ — for a single $s > 0$; see the proof — then $B_1 = B_2$ on the strip *as meromorphic functions*: they agree on a punctured neighbourhood of every point of it, hence pointwise at every point where both are continuous, in particular at any point that is a pole of neither. Hence $A$ is the unique inversion within the covariant Mellin class.

*Proof.* "Of the form $x^{-1}B_i(\theta)$" is the hypothesis that each operator has a realising function in the sense of Definition 11.3, so let $h_i$ realise $B_i(\theta)H(s\,\cdot)$. Both operators send $H(s\,\cdot)$ to the same function, and $x^{-1}h_1 = x^{-1}h_2$ on $(0,\infty)$ is $h_1 = h_2$; so there is a single $\tilde h$, and

$$B_1(-z)\,\tilde g(z) \;=\; \tilde h(z) \;=\; B_2(-z)\,\tilde g(z), \qquad \tilde g(z) = \widetilde{H(s\cdot)}(z) = s^{-z}\tilde H(z),$$

at every point of the line where the realising identity holds. Cancelling the nonvanishing factor $s^{-z}$ leaves $B_1(-z)\tilde H(z) = B_2(-z)\tilde H(z)$ there; at a zero of $\tilde H$ both sides vanish, so this holds on the strip outright. The zeros of $\tilde H$ are isolated (Lemma 11.2), so $\tilde H$ may be cancelled on a punctured neighbourhood of *every* point of the strip, the zeros included, which is the conclusion. Two economies are worth recording, since both tools are natural to reach for and neither is needed: no injectivity of the inverse Mellin transform, the shared realising function carrying the information that injectivity would otherwise have to recover; and a single dilation, the dilate contributing only the factor $s^{-z}$, which never vanishes. ∎

**Lemma 11.5 (the memory line stores fractional integrals).** Under (H), let $f \in X_0$ be causal and $u(\cdot, x) := \Phi_{0,x} f$. Then for every $t > 0$ and $1 < \operatorname{Re} z < z_*$,

$$\widetilde{u(t, \cdot)}(z) \;=\; \int_0^\infty x^{z-1}\, u(t, x)\,dx \;=\; \tilde H(z)\,\big(I^{z} f\big)(t),$$

absolutely convergent. If moreover $f \in \mathcal{D}$, the same holds for $\partial_t u$ with $I^z f$ replaced by $I^z f' = I^{z-1} f$.

*Proof.* $u(t, x) = \mathbb{E}\big[f(t - x T_1)\big]$, so by Tonelli (justified since, for $c = \operatorname{Re} z > 1$, $\mathbb{E}[T_1^{-c}]\int_0^t y^{c-1}|f(t-y)|\,dy \le \mathbb{E}[T_1^{-c}]\, t^{c-1}\|f\|_1 < \infty$),

$$\int_0^\infty x^{z-1}\,\mathbb{E}\big[f(t - xT_1)\big]\,dx \;=\; \mathbb{E}\big[T_1^{-z}\big]\int_0^t y^{z-1} f(t - y)\,dy \;=\; \mathbb{E}\big[T_1^{-z}\big]\,\Gamma(z)\,(I^z f)(t),$$

which is the claim by Lemma 11.2. For $f \in \mathcal{D}$: $\partial_t u(t, x) = \mathbb{E}[f'(t - xT_1)]$, and $I^z f' = I^{z-1} I^1 f' = I^{z-1} f$ using $f(0) = 0$. ∎

**Theorem 11.6 (Theorem 4′: the signaling form).** Assume (H), canonical gauge. Then:

1. *(Eigenfunctions.)* For every $s > 0$, the profile $H(s\,\cdot)$ is in the domain of Definition 11.3 for every $c \in (0, z_*-1)$, and

$$A\big[H(s\,\cdot)\big](x) \;=\; s\, H(sx), \qquad x > 0 .$$

2. *(The field solves the signaling problem.)* Let $f \in \mathcal{D}$ and $u(\cdot, x) := \Phi_{0,x} f$. Then $u$ is causal in $t$ with $u(\cdot, x) \to f$ in $X_0$ as $x \downarrow 0$, and:
   - Laplace form: for every $s > 0$, $\ A\big[\hat u(s, \cdot)\big] = s\,\hat u(s, \cdot)$, with $\hat u(s, 0{+}) = \hat f(s)$;
   - time-domain (Mellin) form: for every $t > 0$ and $1 < \operatorname{Re} z < z_*$,

$$\widetilde{\partial_t u(t, \cdot)}(z) \;=\; B(1 - z)\;\widetilde{u(t, \cdot)}(z - 1), \qquad \text{i.e.} \qquad \partial_t u \;=\; A\,u \ \text{ read through the Mellin transform in } x .$$

3. *(Uniqueness.)* $A$ is the unique operator in the covariant Mellin class with property (1), hence with property (2).

*Proof.* (1) The realising function is exhibited: put

$$h(x) \;:=\; s\,x\,H(sx), \qquad \text{so that} \qquad \tilde h(z) \;=\; s^{-z}\,\tilde H(z+1),$$

the weight $x$ shifting the Mellin argument by one and the two powers of $s$ combining as $s\cdot s^{-(z+1)}$. On the other side, $\tilde g(z) := \widetilde{H(s\,\cdot)}(z) = s^{-z}\tilde H(z)$, so

$$B(-z)\,\tilde g(z) \;=\; \frac{\tilde H(z+1)}{\tilde H(z)}\cdot s^{-z}\tilde H(z) \;=\; s^{-z}\tilde H(z+1) \;=\; \tilde h(z)$$

at every point of the line where $\tilde H(z) \ne 0$ — which is all but an isolated, hence null, set of it. (The cancellation is the whole content: it is Lemma 11.2's recursion with the denominator cleared. It should not be described as a product "containing no division"; the division is there, and clearing it is what costs the exceptional set. That set is null, which is all the inversion integral needs.) Both convergence hypotheses of Definition 11.3 hold for $h$ at height $c$, being Lemma 11.2 at height $c + 1 \in (1, z_*)$, and $h$ is continuous since $H$ is. So $h$ realises $B(\theta)H(s\,\cdot)$, and

$$A\big[H(s\cdot)\big](x) \;=\; \frac{h(x)}{x} \;=\; s\,H(sx).$$

Equivalently, and this is the same computation read as a contour integral: the weight $x^{-1}$ of Definition 11.3 is exactly what cancels the weight $x$ that shifted the transform, so the eigenfunction relation and the exhibition of $h$ are one statement rather than two.

(2) Causality and the boundary attainment are (A3) and (A7). The Laplace form is (1) applied to $\hat u(s, \cdot) = \hat f(s) H(s\,\cdot)$. The Mellin form is Lemma 11.5 combined with Lemma 11.2:

$$B(1-z)\,\widetilde{u(t,\cdot)}(z-1) = \frac{\tilde H(z)}{\tilde H(z-1)}\cdot\tilde H(z-1)\,(I^{z-1}f)(t) = \tilde H(z)\,(I^{z-1}f)(t) = \widetilde{\partial_t u(t,\cdot)}(z).$$

(3) is Lemma 11.4. ∎

**Remark 11.7 (reading of Lemma 11.5; embodiment).** Lemma 11.5 gives the motivation of [Fagerström 2005, §5] an exact form: at each instant $t$, the Mellin analysis of the memory line holds precisely the analytic family of Riemann–Liouville integrals $\{(I^z f)(t)\}$ of the *past* signal, weighted by the negative delay-moments $\mathbb{E}[T_1^{-z}]$. The observer's embodiment of its past is fractional integration, with the admissible weightings classified by Theorem 7.3.

**Remark 11.8 (classical interpretation; poles).** The time-domain equation in Theorem 11.6(2) is stated at the level of Mellin transforms; this is the honest general formulation, since $B$ may have poles (at zeros of $\tilde H$) and polynomial growth along vertical lines, so that $A u(t, \cdot)$ need not be given by an absolutely convergent integral for rough $f$ — note that on the field the identity is nevertheless regular, the factor $\tilde H(z-1)$ cancelling every denominator. When the symbol $B$ is a *polynomial*, $A$ is a local differential operator and the equation is a classical PDE; that is precisely the situation of Theorem 5′ (§12) and of Example 11.11 below.

**Example 11.9 (extremal stable; recovering Theorem 4 of 2005).** $F(s) = s^\alpha$: $\tilde H(z) = \Gamma(z/\alpha)/\alpha$ and

$$B(-z) \;=\; \frac{\Gamma\big(\tfrac{z+1}{\alpha}\big)}{\Gamma\big(\tfrac{z}{\alpha}\big)} \;\sim\; \Big(\tfrac{z}{\alpha}\Big)^{1/\alpha} \quad (z \to \infty),$$

a symbol of order $1/\alpha$. On the profiles $e^{-(sx)^\alpha}$ the right-sided Liouville derivative acts by $D^{1/\alpha}_{x,-} e^{-cx} = c^{1/\alpha} e^{-cx}$ with $c = s^\alpha$, i.e. also produces the eigenvalue $s$; thus the Mellin representative and the operator of [Fagerström 2005, Thm. 4] agree on the span of the field profiles — the translation-invariant representative is a coincidence of homogeneity, the Mellin representative is the one that survives in general.

**Example 11.10 (Gamma family; scale-recursive form).** $F(s) = \gamma \log(1+s)$, $\gamma > 1$: $\tilde H(z) = \Gamma(z)\Gamma(\gamma - z)/\Gamma(\gamma)$ and $B(-z) = z/(\gamma - 1 - z)$, i.e.

$$B(\theta) = -\,\theta\,\big(\theta + \gamma - 1\big)^{-1}, \qquad A = -\,\frac{1}{x}\,\theta\,\big(\theta + \gamma - 1\big)^{-1},$$

a *rational* Mellin symbol — the memory-line mirror of the time-side resolvent $\gamma\,\partial_t(1 + x\partial_t)^{-1}$ of Example 10.6. Explicitly, $w := (\theta + \gamma - 1)^{-1} u$ solves $x\,w_x + (\gamma-1)w = u$ with the regular-at-$0$ solution

$$w(t, x) = x^{-(\gamma-1)}\int_0^x y^{\gamma - 2}\, u(t, y)\,dy, \qquad \partial_t u = -\tfrac{1}{x}\,\theta\, w = -\,\partial_x w \cdot 1 \big/ 1 \;\; \text{(one scale-Volterra step)},$$

so the time evolution at scale $x$ is computed from the field at *finer* scales by a single weighted average — scale-recursive, one-sided from the boundary, matching the causal architecture of the time side.

**Example 11.11 (parabolic gauge; the Bessel family is the quadratic case).** In the $\alpha$-gauge (similarity variable $x^{1/\alpha} s$; Remark 6.4) the profiles are $H(x^{1/\alpha}s)$, the Euler operator acts on the profile through $\alpha^{-1}\theta$, and the inversion becomes $A = x^{-1/\alpha}\,B(\alpha\,\theta)$. Take the parabolic gauge $\alpha = \tfrac12$ and the Bessel-K family of Example 8.3, $T_1 = 1/(2\gamma_a)$: then $\mathbb{E}[T_1^{-z}] = 2^z\,\Gamma(a + z)/\Gamma(a)$, so

$$B(-z) = 2z(z + a), \qquad B(\tfrac12\theta)\cdot 2 \big/ 2 = \tfrac{\theta^2}{2} - a\,\theta, \qquad A = x^{-2}\Big(\tfrac{\theta^2}{2} - a\theta\Big) = \tfrac12\,\partial_x^2 + \frac{\beta}{x}\,\partial_x, \quad \beta = \tfrac12 - a .$$

The symbol is a *quadratic polynomial*, so $A$ is local: the signaling form of the Bessel-K scale space is exactly the Bessel diffusion-with-drift medium, and Theorem 11.6(2) becomes the classical signaling problem $\partial_t u = \tfrac12 u_{xx} + \tfrac{\beta}{x}u_x$, $u(t,0) = f(t)$, $u(0,x) = 0$.

**Remark 11.12 (Markov media).** Within the class of Theorem 11.6, the operators $A$ that additionally satisfy the positive maximum principle — i.e. generate a sub-Markov process on the memory half-line, so that the medium is a physical transport medium — are, after the logarithmic substitution $x = e^\xi$, exactly those whose symbol $B$ is the Laplace exponent of a Lévy process; by the Lamperti correspondence [Lamperti 1972] these media are positive self-similar Markov processes absorbed at the boundary, and the kernels are the boundary-arrival times $T_x \stackrel{d}{=}$ absorption time from depth $x$. The spectral orientation of the jumps is *not* constrained: for spectrally positive media the process creeps downward through every level and the hemigroup (A6) holds *pathwise*, the kernels being genuine level-passage times; but media with downward jumps are also admissible — the factorization then holds in law though not pathwise, being inherited from the exponent $F$ rather than from the paths. The Gamma family is the standard example: unfolding Example 11.10, its medium is the multiplicative jump process that waits at scale $x$ an $\mathrm{Exp}(\text{mean } x)$ time and jumps to $\sigma x$ with $\sigma \sim \mathrm{Beta}(\gamma-1, 1)$, reaching the boundary by accumulation of jumps; a first-jump computation confirms $\mathbb{E}_x[e^{-s\tau_0}] = (1+sx)^{-\gamma}$. A necessary condition in all cases is quadratic symbol growth, $B(\theta) = O(\theta^2)$; by Example 11.9 the homogeneous members with $\alpha < \tfrac12$ (symbol order $1/\alpha > 2$) admit *no* Markov medium, although Theorem 11.6 always supplies the analytic signaling form — the operator exists, the process does not. The classification of which admissible $F$ are Markov-realizable is the memory-line inverse problem and is taken up with Theorem 5′.

## 12. The locality theorem: Theorem 5′

Theorem 5 of [Fagerström 2005] singles out $\alpha = \tfrac12$ — the heat signaling equation — as the unique member of the stable family whose memory-line evolution is a local, positivity-respecting differential equation. This section proves the hemigroup analogue. The structure is genuinely two-layered: locality *alone* opens a countable ladder of admissible local media of every order, and it is the positive maximum principle — the requirement that the medium be a physical transport medium — that closes the ladder at order two, where it leaves exactly the Bessel family. Throughout: hypothesis (H), canonical gauge, $m(z) := \mathbb{E}[T_1^{-z}]$, and $A$, $B$ as in §11.

**Definition 12.1 (locality; positive maximum principle).** The inversion operator $A$ is *local (of order $n$)* if it agrees on $C_c^\infty((0,\infty))$ with a differential expression $\sum_{j=0}^{n} c_j(x)\,\partial_x^j$, $c_j \in C((0,\infty))$, $c_n \not\equiv 0$. It satisfies the *positive maximum principle* (PMP) if $(Ag)(x_0) \le 0$ whenever $g \in C_c^\infty((0,\infty))$ attains a nonnegative maximum at $x_0$.

**Lemma 12.2 (covariant local = polynomial symbol).** $A$ is local of order $n$ iff $B$ is a polynomial of degree $n$; in that case the covariance built into the Mellin class forces the coefficients

$$c_j(x) \;=\; \gamma_j\, x^{\,j-1}, \qquad A \;=\; \frac{1}{x}\sum_{j=0}^n \gamma_j\,\theta(\theta-1)\cdots(\theta-j+1) \;=\; \frac{1}{x}\,B(\theta).$$

*Proof.* ($\Leftarrow$) $x^{j}\partial_x^{j} = \theta(\theta-1)\cdots(\theta - j + 1)$, so a polynomial $B$, expanded in falling factorials, gives $x^{-1}B(\theta) = \sum \gamma_j x^{j-1}\partial_x^j$, a differential expression of order $\deg B$. ($\Rightarrow$) Every operator of Definition 11.3 satisfies the covariance $A\Delta_\sigma = \sigma^{-1}\Delta_\sigma A$, $(\Delta_\sigma g)(x) = g(x/\sigma)$. Imposing this on $\sum c_j(x)\partial_x^j$ and comparing coefficients of $g^{(j)}(x/\sigma)$ gives $c_j(x)\sigma^{-j} = \sigma^{-1}c_j(x/\sigma)$, i.e. $c_j(x) = c_j(1)x^{j-1}$. Rewriting via falling factorials, $A$ agrees on $C_c^\infty$ with $x^{-1}P(\theta)$ for a polynomial $P$; Mellin-transforming on a line and using injectivity, $B = P$. ∎

**Lemma 12.3 (the moment recursion).** Suppose $A$ is local of order $n$, i.e. $B$ is a polynomial of degree $n$. Then:

1. $B(0) = 0$; write $B(-z) = z\,Q(z)$ with $Q$ a polynomial of degree $n - 1$;
2. $z_* = \infty$: all negative moments of $T_1$ are finite;
3. $m(z+1) = Q(z)\,m(z)$ for all $z > 0$, and $Q > 0$ on $(0,\infty)$.

*Proof.* (1) By Lemma 11.2, $B(-z) = z\,m(z+1)/m(z)$ on the strip; as $z \downarrow 0$, $m(z) \to 1$ (dominated convergence) and $m(z+1) \to m(1) < \infty$ (hypothesis (H)), so $B(0) = 0$; since $B$ is a polynomial, $Q(z) := B(-z)/z$ is one of degree $n-1$.

(2) On $0 < z < z_* - 1$ we have the identity $\tilde H(z+1) = B(-z)\tilde H(z)$ of functions analytic on the strip $0 < \operatorname{Re} z < z_*$. If $z_* < \infty$, the right side is analytic at $z = z_* - 1 + \varepsilon$ for small $\varepsilon$, extending $\tilde H$ analytically through the real point $z_*$. But $\tilde H$ is the Mellin transform of the nonnegative function $H$, and by the Pringsheim–Landau theorem [Widder, Ch. II] the real endpoint of its convergence strip is a singularity if finite. Hence $z_* = \infty$.

(3) The recursion is now Lemma 11.2 on all of $(0,\infty)$; positivity of $Q$ follows from $m > 0$. ∎

**Lemma 12.4 (log-convexity).** $z \mapsto m(z)$ is log-convex on $(0, \infty)$.

*Proof.* Cauchy–Schwarz: $m\big(\tfrac{z_1+z_2}{2}\big) = \mathbb{E}\big[T^{-z_1/2}\,T^{-z_2/2}\big] \le m(z_1)^{1/2} m(z_2)^{1/2}$; midpoint log-convexity plus continuity. ∎

**Theorem 12.5 (Theorem 5′: the locality theorem).** Assume (H). The inversion operator $A$ of Theorem 11.6 is local *and* satisfies the positive maximum principle **iff** one of the following holds:

1. *(order 1; pure transport, degenerate.)* $B(\theta) = -c'\theta$ with $c' > 0$: $A = -c'\,\partial_x$, the kernels are the deterministic delays $\mu_{0,x} = \delta_{x/c'}$, and the signaling problem is the transport equation. This member has no smoothing and is excluded by requiring absolutely continuous kernels (Remark 7.5).

2. *(order 2; the Bessel family.)* After normalizing the unit of time ($c_2 = 2$): $B(\theta) = 2\,\theta(\theta - a)$ for some $a > 0$; the kernels are the inverse-gamma family $T_1 \stackrel{d}{=} 1/(2\gamma_a)$ of Example 8.3; and in the parabolic gauge the signaling problem is the classical degenerate-parabolic PDE

$$\partial_t u \;=\; \tfrac12\,\partial_x^2 u + \frac{\beta}{x}\,\partial_x u, \qquad \beta = \tfrac12 - a, \qquad u(t,0) = f(t),\quad u(0,x) = 0 .$$

Within case (2), the depth-homogeneous (semigroup) members are exactly $a = \tfrac12$, i.e. $\beta = 0$ — the heat signaling equation — recovering [Fagerström 2005, Thm. 5] as the zero-drift point of the family. The kernel moments in case (2) satisfy $\mathbb{E}\,T_x^{\,n} < \infty$ iff $n < a$.

*Proof.* ($\Rightarrow$) A local operator satisfying the positive maximum principle has order at most $2$: this is the local case of Courrège's classification [Courrège] (the jump measure vanishes by locality, leaving $c_2(x)\partial^2 + c_1(x)\partial + c_0(x)$ with $c_2 \ge 0$, $c_0 \le 0$). By Lemma 12.2, $\deg B \le 2$, and $B(0) = 0$ by Lemma 12.3(1) (equivalently: no killing, which is (A5)).

*Order 1.* $Q \equiv c'$ constant, so $m(z+1) = c'm(z)$, $m(0)=1$; the unique log-convex solution is $m(z) = c'^{\,z}$ (Lemma 12.4 and [Webster]; here directly: $\log m$ is convex with constant unit-increments, hence affine). Thus $T_1 = 1/c'$ a.s., $B(-z) = c'z$, i.e. $B(\theta) = -c'\theta$ and $A = -c'x^{-1}\theta = -c'\partial_x$; positivity of $Q$ gives $c' > 0$.

*Order 2.* $Q(z) = c_2 z + q_0$ with, by Lemma 12.3(3), $c_2 > 0$ (positivity at $z \to \infty$) and $q_0 = Q(0) = m(1) > 0$; write $Q(z) = c_2(z + a)$, $a := q_0/c_2 > 0$. The recursion $m(z+1) = c_2(z+a)\,m(z)$, $m(0)=1$, with $\log Q$ concave, has a *unique* log-convex solution by the Krull–Webster extension of the Bohr–Mollerup theorem [Webster], namely

$$m(z) \;=\; c_2^{\,z}\,\frac{\Gamma(a + z)}{\Gamma(a)} \;=\; \mathbb{E}\Big[\big(c_2\,\gamma_a\big)^{z}\Big],$$

and $m$ is log-convex by Lemma 12.4, hence equals it. Thus $T_1 \stackrel{d}{=} 1/(c_2\gamma_a)$; the time normalization $c_2 = 2$ gives Example 8.3, the profile is the Bessel-K function, and the operator is computed in Example 11.11: $B(\theta) = 2\theta(\theta - a)$, parabolic-gauge form as displayed.

($\Leftarrow$) Case (1): admissibility is the pure-drift member $F(s) = s/c'$ of (7.1), and a first-order operator satisfies the PMP trivially ($g'(x_0) = 0$ at an interior maximum). Case (2): admissibility of the inverse-gamma family is Example 8.3 (self-decomposability by [Halgreen]); locality is Example 11.11; and a second-order operator $\tfrac12\partial_x^2 + \tfrac{\beta}{x}\partial_x$ with nonnegative leading coefficient satisfies the PMP: at an interior nonnegative maximum, $g' (x_0)= 0$ and $g''(x_0) \le 0$, so $(Ag)(x_0) = \tfrac12 g''(x_0) \le 0$.

The homogeneity claim: by Corollary 7.4, depth-homogeneous members have $F(s) = c\,s^{\alpha}$; within the inverse-gamma family the exponent is a pure power only for $a = \tfrac12$ (where $K_{1/2}$ is elementary and $H(y) = e^{-\sqrt{2y}}$), the $\tfrac12$-stable/heat case. The moment statement is Example 8.3. ∎

**Proposition 12.6 (the ladder: locality without the maximum principle).** Fix $n \ge 2$, $c' > 0$ and $a_1, \dots, a_{n-1} > 0$, and let

$$T_1 \;\stackrel{d}{=}\; \frac{1}{c'\,\gamma_{a_1}\gamma_{a_2}\cdots\gamma_{a_{n-1}}} \qquad (\text{independent factors}), \qquad m(z) = c'^{\,z}\prod_{i=1}^{n-1}\frac{\Gamma(a_i + z)}{\Gamma(a_i)} .$$

Then the family is admissible (Theorem 7.3) and satisfies (H), and its inversion operator is *local of order $n$*, with polynomial symbol

$$B(-z) \;=\; c'\,z\prod_{i=1}^{n-1}(z + a_i);$$

the kernels are Meijer $G$-function densities: the product $\gamma_{a_1}\cdots\gamma_{a_{n-1}}$ has a $G^{\,n-1,0}_{\,0,n-1}$ density with arbitrary distinct shapes [Springer–Thompson 1970, Thm. 1], and the reciprocal together with the scale factor $c'$ is absorbed by the $G$-function transformation rules [Samko–Kilbas–Marichev, eqs. (1.96)–(1.97)]. Conversely, every local admissible family of order $n$ has $m$ equal to the unique log-convex (Krull–Webster) solution of $m(z+1) = Q(z)m(z)$ for its polynomial $Q$; when the roots of $Q$ are real — necessarily $\le 0$, giving $Q(z) = c'\prod(z+a_i)$ with $a_i > 0$ — this is the family above. Whether complex-conjugate root pairs can support an admissible family is left open; we conjecture not.

*Proof.* Admissibility: gamma densities are hyperbolically completely monotone (HCM), and the HCM class is closed under products of independent variables and under reciprocals; HCM laws are generalized gamma convolutions, hence self-decomposable [Bondesson 1992]. So $-\log \mathbb{E}e^{-sT_1}$ is of the form (7.1), and (H) holds since all negative moments are finite and $\mathbb{P}(T_1 = 0) = 0$. The symbol is $B(-z) = z\,m(z+1)/m(z) = c'z\prod(z+a_i)$, polynomial, so $A$ is local of order $n$ by Lemma 12.2. The converse is Lemmas 12.3–12.4 with [Webster], as in the proof of Theorem 12.5; a real root $-a_i \ge 0$ of $Q$ would contradict $Q > 0$ on $(0,\infty)$ together with $Q(0) = m(1) > 0$, so real roots give $a_i > 0$ and the Webster solution is the displayed gamma product. ∎

**Remark 12.7 (the stable slice; Gauss multiplication).** Depth-homogeneity intersects the ladder at the equally spaced parameters $a_j = j/n$, $c' = n^n$: by the Gauss multiplication formula,

$$m(z) \;=\; n^{nz}\prod_{j=1}^{n-1}\frac{\Gamma(j/n + z)}{\Gamma(j/n)} \;=\; n\,\frac{\Gamma(nz)}{\Gamma(z)}, \qquad \text{i.e.} \qquad \tilde H(z) = n\,\Gamma(nz), \qquad H(y) = e^{-y^{1/n}} :$$

the $\tfrac1n$-stable laws, recovering the classical identity representing the $\tfrac1n$-stable subordinator as a scaled reciprocal product of $n-1$ gamma variables. Thus the local cases $\alpha = 1/n$ of [Fagerström 2005] are precisely the homogeneous slice of the ladder, and each unfolds under the hemigroup axioms into an $(n-1)$-parameter inhomogeneous family of local media. The maximum principle eliminates $n \ge 3$ in both settings; what remains at $n = 2$ is the single point $\alpha = \tfrac12$ there, the Bessel line here.

**Remark 12.8 (what the theorem settles).** Theorem 12.5 completes the resolution of the practicality problem of Remark 8.5 *within the local class*: the drift weight $\beta = \tfrac12 - a$ is a design parameter, and any prescribed number of finite kernel moments is achievable by a local, positivity-respecting, continuously scale-covariant, time-causal medium ($n < a$). The residual trade-off is the tail: inverse-gamma kernels have polynomial tails $t^{-1-a}$ for every finite $a$, so *all* moments — exponential localization — still require leaving the local class for the Gamma-type corner of Example 8.2. Homogeneity, locality, and moment control thus interact as follows: homogeneity + covariance forces stable kernels (no mean); locality + covariance + PMP allows any finite number of moments but polynomial tails; full moment control requires nonlocal delay accrual.

## 13. Implementation

This section records how the scale spaces of Theorem 7.3 are computed, and compares the three practically distinguished corners — Gamma, Bessel, stable — from the implementer's point of view. The structural fact that organizes everything is that the *scale direction never needs to be discretized approximately*:

**Proposition 13.1 (exactness at the knots).** Let $0 = x_0 < x_1 < \cdots < x_M$ be any finite set of scale knots and define the discrete cascade

$$u_0 := f, \qquad u_{k+1} := \mu_{x_k,\,x_{k+1}} * u_k .$$

Then $u_k = \Phi_{0, x_k} f$ *exactly*, for every knot set. Consequently the only discretization error in a digital implementation is the time discretization of the increment filters; moreover, refining the knot set changes nothing at the old knots, so intermediate scales can be added at any time without recomputation error.

*Proof.* Immediate induction from the hemigroup (A6): $\mu_{0,x_{k+1}} = \mu_{x_k, x_{k+1}} * \mu_{0,x_k}$. ∎

This is a genuine advantage over discretizing the memory-line evolution of §11, where the scale direction carries truncation error; the cascade is not an approximation scheme for the family but the family itself, sampled.

**Proposition 13.2 (the Gamma cascade).** For the Gamma family with integer $\gamma$, the increment filter is rational:

$$\widehat{\mu}_{x_k, x_{k+1}}(s) \;=\; \left(\frac{1 + x_k\, s}{1 + x_{k+1}\, s}\right)^{\gamma},$$

a cascade of $\gamma$ *identical* first-order pole–zero sections (pole $1/x_{k+1}$, zero $1/x_k$). Each section admits the one-state realization, free of input differentiation,

$$\dot w = \frac{y - w}{x_{k+1}}, \qquad v \;=\; \frac{x_k}{x_{k+1}}\, y \;+\; \Big(1 - \frac{x_k}{x_{k+1}}\Big)\, w,$$

($y$ input, $v$ output), whose transfer is $(1 + x_k s)/(1 + x_{k+1} s)$; the output is a *convex combination* of input and state, so positivity and unit mass are manifest at the realization level. With sampled-and-held input the exact (exponential-integrator) update is

$$w_{n+1} = e^{-\Delta/x_{k+1}}\, w_n + \big(1 - e^{-\Delta/x_{k+1}}\big)\, y_n ,$$

so the discrete filter is exact for zero-order-held signals, unconditionally stable (real pole in $(0,1)$), and free of overshoot and ringing. A full scale space over knots $x_1 < \cdots < x_M$ costs $\gamma M$ first-order states and $O(\gamma M)$ multiply-adds per sample.

*Proof.* The transfer identity: $v = \tfrac{x_k}{x_{k+1}} y + \big(1 - \tfrac{x_k}{x_{k+1}}\big)\tfrac{y}{1 + x_{k+1}s} = y\,\tfrac{1 + x_k s}{1 + x_{k+1} s}$; the rest is standard first-order filter theory. ∎

**Remark 13.3 (covariance in practice).** With geometric knots $x_k = q^k x_0$ the discrete system is exactly covariant under rescalings $\sigma \in q^{\mathbb{Z}}$ by a shift of the ladder; and because the underlying continuum family exists at *every* scale, arbitrary $\sigma$ are handled by re-evaluating the same family at shifted knots — kernels between knots belong to the family, so resampling the ladder is principled. This is the operational content of continuous covariance, and the point of the pole–zero structure: a pure-pole cascade (truncated exponentials with distinct time constants) also marches a hemigroup, but its kernels are hypoexponential laws whose family is *not* dilation-closed, so only the discrete covariance of the ladder itself survives. The zeros are what the hemigroup increments of the Sato–Gamma process add, and they are exactly what buys the continuum.

**Remark 13.4 (implementing the local corner).** The Bessel/inverse-gamma increments have transcendental transforms (ratios of Bessel-K profiles), hence *no* finite-dimensional time-recursive realization; the same holds for the stable family ($e^{-(x_{k+1}^{\,\alpha} - x_k^{\,\alpha})\,s^\alpha}$ in the homogeneous gauge). The implementation options are: (i) direct convolution against tabulated increment kernels per knot — burdened by the polynomial tails $t^{-1-a}$, so truncation error decays only polynomially in the window length; (ii) marching the memory-line PDE $\partial_t u = \tfrac12 u_{xx} + \tfrac{\beta}{x}u_x$ in time (implicit in $x$, with care at the degenerate boundary), which reintroduces scale-direction discretization error; or (iii) rational approximation of the irrational symbol, as for fractional-order elements in filter and control design, with state count growing logarithmically in the required bandwidth — made systematic within the axioms in Proposition 13.6 below. All three are workable; none matches the cascade of Proposition 13.2 in simplicity or exactness. This is the practical face of Theorem 12.5: locality of the medium is bought at the price of heavy-tailed, non-rational kernels.

**Remark 13.5 (finite differences on the memory line).** The explicit finite-difference scheme of [Fagerström 2005, §§6–7] for the heat signaling equation extends verbatim to the Bessel family. On the logarithmic grid $\xi = \log x$ the operator is constant-coefficient up to a rate factor,

$$\tfrac12\,\partial_x^2 + \frac{\beta}{x}\,\partial_x \;=\; e^{-2\xi}\Big[\tfrac12\,\partial_\xi^2 + \big(\beta - \tfrac12\big)\,\partial_\xi\Big],$$

so the stencil is uniform along the scale ladder and only the update rate varies with position — the discrete form of the Lamperti time change [Lamperti 1972]. With the first-order term upwinded, the explicit update matrix is sub-stochastic, so positivity and non-amplification are automatic, and the discrete scheme is itself a hemigroup of sub-probability kernels: a random-walk medium whose absorption-time laws are discrete analogues of the inverse-gamma kernels. We record this for continuity with the 2005 paper but do not recommend it: the explicit step is constrained by the finest cell, $\Delta t \lesssim x_{\min}^2\,\Delta\xi^2$, while the coarse-scale dynamics live on horizons $\sim x_{\max}^2$, so the cost of covering the ladder grows like $(x_{\max}/x_{\min})^2$ (an implicit march trades this for per-sample band solves plus additional discretization error); the finite-moment regime $a > 1$, i.e. $\beta < -\tfrac12$ — the very reason to prefer the Bessel family — is advection-dominated near the singular boundary and numerically the least pleasant; and, decisively, any marching of the signaling equation approximates the scale direction, which Proposition 13.1 shows can be sampled exactly. The principled numerics for the local corner is instead the following.

**Proposition 13.6 (the Thorin subclass; gamma cascades approximate the local corner).** For an admissible $F$ (Theorem 7.3) the following are equivalent:

1. the memory kernel $k$ is completely monotone — the classical Sonine case of Proposition 9.7(3);
2. $F$ has a *Thorin representation*

$$F(s) \;=\; b_0\,s \;+\; \int_{(0,\infty)} \log\Big(1 + \frac{s}{\tau}\Big)\,U(d\tau), \qquad U \ge 0,\ \ \int_{(0,1]} \log\tfrac{1}{\tau}\,U(d\tau) + \int_{(1,\infty)} \frac{U(d\tau)}{\tau} < \infty;$$

3. the kernels are generalized gamma convolutions (GGC).

In that case, for any atomic approximation $U_N = \sum_{i=1}^N w_i\,\delta_{\tau_i}$ converging to $U$, the exponents $F_N(s) = b_0 s + \sum_i w_i \log(1 + s/\tau_i)$ are *themselves admissible* — finite multi-Gamma members of Theorem 7.3 — with $F_N \to F$ pointwise, hence weak convergence of the kernel families at every scale; positivity and unit mass hold *exactly at every truncation level*, the approximation staying inside the axiom class rather than merely near it. For integer weights the increments over any knot ladder are rational of order $\sum_i w_i$, realized by the cascade of Proposition 13.2 applied per Thorin node, with time constants $x/\tau_i$.

*Proof.* (1) $\Leftrightarrow$ (2): $k$ CM means $k(t) = \int e^{-\tau t}\,U(d\tau)$ for a positive measure $U$; by Lemma 9.1, $F'(s) = b_0 + \int U(d\tau)/(s + \tau)$, and integrating in $s$ from $0$ gives the Thorin form, the integrability condition being finiteness of $F(1)$; conversely differentiate. (2) $\Leftrightarrow$ (3) is Thorin's characterization of the GGC class [Thorin 1977a, 1977b; Bondesson 1992, Thm. 3.1.1; SSV, Thm. 8.2]. Admissibility of $F_N$: $sF_N'(s) = b_0 s + \sum_i w_i\, s/(s + \tau_i)$ is a Bernstein function, so Lemma 7.1 applies; $F_N(0{+}) = 0$. Pointwise convergence of $F_N$ gives convergence of the transforms $e^{-F_N(xs)}$, hence weak convergence of the kernels by the continuity theorem [Feller, XIII.1]. ∎

Every family named in this paper lies in the Thorin subclass. The Gamma family is its *single-atom* member, $U = \gamma\,\delta_1$ — the cascade of Proposition 13.2 is literally the atomic case of Proposition 13.6. The stable family has the explicit Thorin density $U(d\tau) = \tfrac{\alpha \sin(\pi\alpha)}{\pi}\,\tau^{\alpha - 1}\,d\tau$. The inverse-gamma/Bessel family is GGC by [Halgreen 1979; Bondesson 1992], with Thorin measure supported on the spectral cut of the Bessel operator and density expressible through the Bessel functions of the first and second kind, $u(\tau) \propto \big[\tau\,\big(J_a^2 + Y_a^2\big)\big(\sqrt{2\tau}\big)\big]^{-1}$ [Ismail–Kelker], decaying like $\tau^{-1/2}$ at infinity in accordance with $F(s) \sim \sqrt{2s}$. And the gamma-product ladder of Proposition 12.6 is GGC since HCM $\subset$ GGC [Bondesson 1992]. The conclusion deserves stating plainly: **the Gamma family is the implementation substrate for the entire theory** — even when Bessel semantics are wanted, the machine one builds is a bank of first-order Gamma sections; and since the Bessel Thorin density decays like $\tau^{-1/2}$, logarithmically spaced nodes, a fixed number per decade of covered bandwidth, suffice — substantiating the state-count claim of Remark 13.4(iii). In practice the node data $(\tau_i, w_i)$ come either from quadrature of $U$ or from direct rational fitting of the increment transfer functions; the Thorin structure guarantees that a fit with *positive* weights exists.

**Comparison of the three corners.**

| | Gamma (Ex. 8.2) | Bessel (Ex. 8.3) | stable ([Fagerström 2005]) |
|---|---|---|---|
| axiomatic role | nonlocal medium, order-$0$ symbol | local medium + PMP (Thm 12.5) | homogeneous (Cor. 7.4) |
| kernels | $\Gamma(\gamma,\,x)$ | inverse-gamma, shape $a$ | one-sided $\alpha$-stable |
| moments | all finite; $\mathbb{E}\,T_x = \gamma x$ | $n$-th iff $n < a$ | none |
| tails | exponential | $t^{-1-a}$ | $t^{-1-\alpha}$ |
| increment transfer | rational, order $\gamma$ | transcendental (Bessel-K) | transcendental |
| time-recursive states per knot | $\gamma$ | — (approximation only) | — (approximation only) |
| scale covariance | continuous | continuous | continuous |
| medium (Rmk 11.12) | multiplicative jump process | diffusion + drift | $\alpha \ge \tfrac12$: Lévy; $\alpha < \tfrac12$: none |

The recommendation implicit in the table: the Gamma family as the default measurement front-end; the Bessel family when a local PDE medium or a diffusion interpretation is required; the stable family when strict depth-homogeneity is required and heavy tails are acceptable.

**Example 13.7 (numerical illustration).** Figure 1 compares the kernels of the three corners at matched delay: Gamma kernels with $\gamma \in \{1, 2, 4\}$ and scale $x = 1/\gamma$ (mean delay $1$); the Bessel/inverse-gamma kernel with $a = 2$ and scale $x^2/2 = a - 1$ (mean delay $1$); and the $\tfrac12$-stable kernel of [Fagerström 2005] normalized to median delay $1$, its mean being infinite.

![Figure 1: time-causal scale-space kernels at matched delay. (a) linear scale; (b) log–log, with the power-law guides $t^{-3}$ (inverse-gamma, $a=2$) and $t^{-3/2}$ ($\tfrac12$-stable).](fig-kernels.png)

Panel (a) shows the bodies: at matched mean the Gamma kernels are the most concentrated, sharpening with $\gamma$ (mode $(\gamma - 1)/\gamma \to$ mean), while the inverse-gamma kernel buys its early sharp peak by exporting mass into the tail, and the stable kernel does so to the point of losing the mean altogether; beyond $t \approx 2$–$3$ the ordering reverses and the heavy-tailed members dominate. Panel (b) shows the mechanism: the Gamma tails fall exponentially, the inverse-gamma and stable tails follow the powers $t^{-1-a}$ and $t^{-3/2}$ of Remark 12.8. The practical consequence is quantified by the window length $T_p$ capturing a fraction $p$ of the kernel mass ($\int_0^{T_p}\phi = p$), the quantity governing the truncation error of route (i) in Remark 13.4:

| kernel (delay $1$) | $T_{0.99}$ | $T_{0.999}$ |
|---|---|---|
| $\Gamma(\gamma{=}1)$ | $4.61$ | $6.91$ |
| $\Gamma(\gamma{=}2)$ | $3.32$ | $4.62$ |
| $\Gamma(\gamma{=}4)$ | $2.51$ | $3.27$ |
| inverse-gamma, $a = 2$ | $6.73$ | $22.0$ |
| $\tfrac12$-stable | $2.90 \times 10^{3}$ | $2.90 \times 10^{5}$ |

For the Gamma family each extra decade of captured mass costs a fixed additive window increment (exponential tails); for the inverse-gamma with $a = 2$ it costs a factor $10^{1/a} \approx 3.2$; for the $\tfrac12$-stable a factor $10^{1/a} = 100$ — capturing $99.9\%$ of its mass requires a window five orders of magnitude longer than its median delay. This is the quantitative content of the statement that the 2005 kernels are too heavy-tailed for practical measurement, and of its resolution within the hemigroup class.

Since the stable mean is infinite, the delay proxy used in the influence-curve discussion of [Fagerström 2005, §7] is the *mode*, and Figure 2 repeats the experiment in that normalization: matched mode delay $1$, i.e. $x = 1/(\gamma - 1)$ for the Gamma kernels ($\gamma = 1$ is omitted, its mode sitting at the onset), $x^2/2 = a + 1 = 3$ for the inverse-gamma, and $x^2/2 = 3/2$ for the $\tfrac12$-stable.

![Figure 2: the same comparison at matched mode delay $= 1$, the normalization of the 2005 influence-curve discussion. (a) linear scale; (b) log–log, with the exact power-law asymptotes.](fig-kernels-mode.png)

Matching at the peak is the normalization most favorable to the heavy-tailed kernels in the body — panel (a) shows the $\Gamma(\gamma{=}2)$ and inverse-gamma bodies nearly coinciding through the peak, so the families are barely distinguishable by their peak response — and it makes the separation in the delay statistics all the starker:

| kernel (mode $1$) | mean | $T_{0.99}$ | $T_{0.999}$ |
|---|---|---|---|
| $\Gamma(\gamma{=}2)$ | $2$ | $6.64$ | $9.23$ |
| $\Gamma(\gamma{=}4)$ | $4/3$ | $3.35$ | $4.35$ |
| inverse-gamma, $a = 2$ | $3$ | $20.2$ | $66.1$ |
| $\tfrac12$-stable | $\infty$ | $1.91 \times 10^{4}$ | $1.91 \times 10^{6}$ |

At matched mode, capturing $99.9\%$ of the $\tfrac12$-stable kernel requires a window six orders of magnitude beyond the peak. Both figures and both tables are generated by the accompanying script `make-figures.py`; the power-law guides in the tail panels are the exact asymptotes $\theta^a t^{-1-a}/\Gamma(a)$ and $\sqrt{\theta/\pi}\, t^{-3/2}$.

## 14. The temporal N-jet: the memory embodies its derivatives

The output of a scale space is not the smoothed field alone but its jet — the temporal derivatives $\partial_t^n u(t, x)$ across scales, the causal analogue of the derivative-of-Gaussian receptive fields. Computed naively, $\partial_t^n u$ requires differencing the field in time, i.e. a *second* memory recording the recent history of the scale space on top of the memory line itself. This section shows that the axioms exclude the need for it: the inversion structure of §11 turns temporal differentiation into an instantaneous spatial readout of the present memory state — the memory line embodies its own jet.

**Definition 14.1.** For $n \ge 1$ let $\mathcal{D}^n := \{f \in X_0 : f, f', \dots, f^{(n)} \in X_0,\ f^{(j)}(0) = 0 \text{ for } j \le n-1\}$ (so $\mathcal{D}^1 = \mathcal{D}$). The *temporal $N$-jet* of the scale space at $(t, x)$ is $\{\partial_t^n u(t, x)\}_{0 \le n \le N}$, and the *scale-normalized jet* is $\{x^n \partial_t^n u(t, x)\}_{n \le N}$, which transforms under the joint dilation $(t, x) \mapsto (\sigma t, \sigma x)$ like the field itself.

**Theorem 14.2 (the embodied jet).** Assume (H), canonical gauge, $f \in \mathcal{D}^n$, and let $u(\cdot, x) = \Phi_{0,x}f$. Then:

1. For every $t > 0$ and $1 < \operatorname{Re} z < z_*$,

$$\widetilde{\partial_t^n u(t, \cdot)}(z) \;=\; \tilde H(z)\,\big(I^{z} f^{(n)}\big)(t) \;=\; \tilde H(z)\,\big(I^{\,z - n} f\big)(t),$$

the second equality holding as a Riemann–Liouville integral for $\operatorname{Re} z > n$ and by analytic continuation (a fractional derivative of $f$) below.

2. Consequently, whenever $z_* > n + 1$, the $n$-th temporal derivative is the $n$-th power of the inversion operator applied to the *present* memory state: in the Mellin sense on $n + 1 < \operatorname{Re} z < z_*$,

$$\partial_t^n u(t, \cdot) \;=\; A^n\, u(t, \cdot), \qquad A^n = \frac{1}{x^n}\,B^{(n)}(\theta), \qquad B^{(n)}(-z) := \frac{\tilde H(z + n)}{\tilde H(z)} = \prod_{j=0}^{n-1} B(-z - j).$$

In particular the entire temporal jet at time $t$ is an instantaneous linear functional of the single profile $x \mapsto u(t, x)$; no record of past states is required.

*Proof.* (1) $\partial_t^n u(t, x) = \mathbb{E}\big[f^{(n)}(t - x T_1)\big]$, and Lemma 11.5 applied to the causal $f^{(n)} \in X_0$ gives the first equality; the second is $I^{z} f^{(n)} = I^{\,z-n} I^{\,n} f^{(n)} = I^{\,z-n} f$, using the vanishing boundary values in $\mathcal{D}^n$. (2) Telescoping the shift relation of Definition 11.3 $n$ times, $\mathcal{M}[A^n g](z) = \prod_{j=1}^{n} B(j - z)\,\tilde g(z - n) = \tfrac{\tilde H(z)}{\tilde H(z - n)}\,\tilde g(z - n)$; insert $\tilde g = \widetilde{u(t,\cdot)}$ from Lemma 11.5 and compare with (1). ∎

**Remark 14.3 (differentiation is re-indexing).** Combined with Remark 11.7, Theorem 14.2(1) says that the memory line stores, once and simultaneously, the analytic family $\{(I^{z} f)(t)\}$ of fractional integrals of the past — and the jet of every order is a *re-reading* of that same stored family at shifted index, order $n$ living at Mellin depth $\operatorname{Re} z > n$ of the strip. Nothing new is stored when one differentiates; the embodiment of the signal already contains its jet, at all orders up to the strip width $z_*$.

**Proposition 14.4 (the Gamma family: jets by subtraction along the shape column).** For the Gamma family write $u_m(\cdot, x)$ for the field of shape $m$ ($u_0 := f$). From $s(1 + xs)^{-m} = x^{-1}\big[(1 + xs)^{-(m-1)} - (1 + xs)^{-m}\big]$,

$$x\,\partial_t\, u_m \;=\; u_{m-1} - u_m \;=\; -\,(\nabla u)_m, \qquad (\nabla u)_m := u_m - u_{m-1},$$

and hence, iterating at fixed $x$,

$$x^n\,\partial_t^n\, u_\gamma \;=\; (-\nabla)^n u_\gamma \;=\; \sum_{j=0}^{n} (-1)^{n-j}\binom{n}{j}\, u_{\gamma - j}(t, x), \qquad 0 \le n \le \gamma .$$

The column $\{u_m(\cdot, x)\}_{m=0}^{\gamma}$ is realized by $\gamma$ identical leaky integrators in series with time constant $x$, $u_m = (1 + x\,\partial_t)^{-1} u_{m-1}$ — the gamma memory of [de Vries–Principe] — so the scale-normalized jet at scale $x$ is a binomial-weighted *subtraction of coexisting filter states*, with no temporal differencing anywhere in the architecture, $\gamma$ states per scale, and jets available up to order $\gamma$. The identity is exact for all $n \le \gamma$, extending beyond the strip condition of Theorem 14.2 (the transforms are rational and continue meromorphically) — consistently with $z_* = \gamma$ marking the strip reading and with the third open problem of §15.

*Proof.* The transform identity is $(1+xs)^{-m}\big[(1+xs) - 1\big] = xs(1+xs)^{-m}$; induction in $n$ at fixed $x$; the realization is Proposition 13.2 with $x_k = x_{k+1}$ degenerate to the pure-pole section. ∎

**Remark 14.5 (receptive fields; Laguerre structure).** By Proposition 14.4 the jet kernels $x^n \partial_t^n k_{\gamma, x}$ are Gamma densities times polynomials in $t/x$ — associated Laguerre functions — and the shape column spans the order-$\gamma$ rational function space with the single pole $1/x$, i.e. the classical Laguerre filter space at time constant $x$. The temporal receptive-field family thus stands to the causal scale space exactly as the Hermite/derivative-of-Gaussian family stands to the Gaussian one: a graded, orthogonalizable basis, read off the embodied state by subtraction.

**Remark 14.6 (the local corner: derivatives as curvatures of the memory trace).** For the Bessel family, Theorem 14.2(2) is local:

$$\partial_t^n u \;=\; \Big(\tfrac12\,\partial_x^2 + \frac{\beta}{x}\,\partial_x\Big)^{\!n} u,$$

the jet read from spatial stencils of order $2n$ on the instantaneous memory profile. In the heat case $\beta = 0$ this is the statement that the observer reads temporal derivatives as curvatures, and iterated curvatures, of its memory trace — the embodiment reading already implicit in [Fagerström 2005, Thm. 4], here extended from the local corner to the whole class by the Mellin form.

## 15. Concluding remarks

One axiom of [Fagerström 2005] was weakened — the one-parameter semigroup cascade to the two-parameter hemigroup, i.e. the assumption that measurement stages are interchangeable — and the entire derivation was rerun in the same order with the same tools. The kernel characterization (Theorem 7.3) enlarges the extremal stable class to the self-decomposable (Sato) class; the memory-kernel and Sonine structure (§9) identifies the self-decomposability function $k$ as the physical memory kernel and losslessness as an exact conservation identity; the scale-Cauchy problem (Theorem 10.4), the Mellin signaling form (Theorem 11.6), and the locality theorem (Theorem 12.5) are the analogues of Theorems 3–5, with the isolated heat case unfolding into the Bessel family and with the heavy tails of the stable kernels exposed as the price of the semigroup axiom rather than of causality or covariance.

Four problems remain open. First, the memory-line inverse problem: which admissible exponents $F$ are realized by genuine Markov media (Remark 11.12), i.e. a correspondence of Krein type [Kotani–Watanabe 1982; Dym–McKean 1976] admitting jumps, together with the question of what surface data determine the medium. Second, the complex-root cases of Proposition 12.6 — largely resolved in the companion note (spectrally leading pairs excluded; order three settled), with the subordinate-pair configuration remaining. Third, the relaxation of hypothesis (H) by meromorphic continuation, which would admit the slowly growing exponents (e.g. the Gamma family with $\gamma \le 1$) into §§11–12. Fourth, the discrete-covariance branch, whose place in the axiom system is identified in Remark 15.1 below; its structure theorem — the classification of the admissible log-periodic modulations, together with the canonical-selection question for the time-causal limit kernel — is deferred to a companion note.

**Remark 15.1 (the discrete-covariance stratum and the previous literature).** Weaken (A8) to the subgroup $\sigma \in q^{\mathbb{Z}}$, $q > 1$. Most of §6 survives verbatim: uniqueness of $S_q$, the group law along the subgroup, and the absence of interior fixed points (the orbit argument needs only the powers $q^{\pm n}$). The similarity solution generalizes as follows: in the variables $(\log(xs),\, \log(x/s))$ the covariance relation $G(qx, s) = G(x, qs)$ says precisely that

$$G(x, s) \;=\; \mathfrak{F}\big(x s;\ \log(x/s)\big), \qquad \mathfrak{F}(\,\cdot\,;\ v + 2\log q) = \mathfrak{F}(\,\cdot\,;\ v),$$

a log-periodic modulation of the continuous case's $F(xs)$ in the chirp variable $\log(x/s)$. The probabilistic identification is exact: applying covariance once, the marginal exponents satisfy

$$\Psi_x(qs) - \Psi_x(s) \;=\; g_{x,\,qx}(s) \;\in\; \mathrm{BF}_0,$$

which is the definition of a *semi-selfdecomposable* law of span $q$ [Maejima–Naito], and the two-parameter families are the *semi-selfsimilar additive* subordinators of [Maejima–Sato] — the discrete analogue of Theorem 7.3, with the classification of the admissible modulations $\mathfrak{F}$ (all increments Bernstein, not only the $q$-steps) as the open structure theorem. The axiom system thus carries a three-level stratification, and the earlier time-causal constructions occupy its strata rather than lying outside it:

1. *(A1)–(A7) alone: Bernstein hemigroups.* This stratum contains the Poisson scale space of [Lindeberg–Fagerström 1996], which belongs to no higher stratum: with exponent $\lambda(1 - e^{-\delta s})$ the $q$-step increment $\lambda(e^{-\delta s} - e^{-q\delta s})$ has a sign-changing derivative for every $q > 1$, so the fixed jump size $\delta$ is incompatible with covariance under any dilation subgroup.

2. *(A8) for $q^{\mathbb{Z}}$: semi-Sato families.* This stratum contains the time-causal limit kernel of [Lindeberg 2016]: its exponent $F(s) = \sum_{i \ge 1} \log(1 + c\,q^{-i}s)$ telescopes under one covariance step,

$$F(qs) - F(s) \;=\; \log(1 + c\,s) \;\in\; \mathrm{BF}_0,$$

one $q$-step of scale per pole section. But more is true, and deserves stating precisely: the Lévy tail of $F$ is $k(t) = \sum_{i \ge 1} e^{-t q^{i}/c}$, a sum of decreasing exponentials — nonincreasing, indeed completely monotone — so $F$ is itself *self-decomposable*, and the similarity family $\{F(x s)\}_{x > 0}$ is a fully covariant member of Theorem 7.3: the Thorin member of Proposition 13.6 whose measure is the geometric atom train $\sum_i \delta_{q^i/c}$ in place of the Gamma family's single atom. The limit kernel is thus, in retrospect, the first-discovered member of the class characterized in this paper, and the Sonine-pair structure of §9, the cascade implementation of §13, and the jets of §14 apply to it verbatim. What is intrinsically discrete about it is the cascade construction — the finite truncations are hypoexponential and not dilation-closed (Remark 13.3) — and the role of $q$ as the log-spacing of its Thorin atoms. Strict members of the middle stratum, semi-selfdecomposable but not self-decomposable, exist and are natural: replace the Poisson scale space's fixed jump $\delta$ by a geometric jump ladder, $F(s) = \sum_{i \in \mathbb{Z}} w_i\big(1 - e^{-\delta q^i s}\big)$ with weights $w_i$ nonincreasing in $i$ and suitably summable. The Lévy measure $\sum_i w_i\,\delta_{\delta q^i}$ satisfies the semi-selfdecomposability domination $\nu \le T_q\nu$, but, being atomic, is self-decomposable for no parameter values — a *$q$-Poisson scale space*, the minimal covariant repair of [Lindeberg–Fagerström 1996].

3. *(A8) in full: the Sato class of the present paper.*

Interpolation between the strata is cheap but not canonical: any ladder family extends to a continuous hemigroup in the first stratum by partial stages $\theta\log(1 + \mu s)$, $\theta \in [0,1]$, and the non-uniqueness of the extension is exactly the modulation freedom of $\mathfrak{F}$. For the limit kernel the extension question has a clean answer: among all $q^{\mathbb{Z}}$-covariant families with its $q$-step increments $g_{x,qx}(s) = \log(1 + c x s)$, *exactly one* extends to full continuous covariance — full covariance forces the similarity form $\Psi_x = F(x\,\cdot)$, the $q$-difference equation $F(qs) - F(s) = \log(1+cs)$ determines $F$ up to a log-periodic summand, and a continuous log-periodic function with limit $0$ at the origin vanishes — namely the limit-kernel family itself. The selection question deferred to the companion note is the intrinsic version: whether the limit kernel is distinguished within its modulation orbit by an extremality principle that does not invoke the continuum extension. The comparison with the previous literature is thereby one of containment rather than difference: the Poisson scale space lies strictly in the first stratum, the limit kernel in the third, and the strict middle stratum is populated by their common refinement, the modulated ($q$-Poisson-type) families.

## References

- L. Bondesson, *Generalized Gamma Convolutions and Related Classes of Distributions and Densities*, Lecture Notes in Statistics **76**, Springer (1992). [HCM densities; closure under products and reciprocals; HCM ⊂ GGC ⊂ SD.]
- F. Caravenna, R. Sun, N. Zygouras, The Dickman subordinator, renewal theorems, and disordered systems, *Electron. J. Probab.* **24** (2019), paper no. 101. [The Dickman subordinator: Laplace exponent $\mathrm{Ein}(\tau s)$, Lévy density $t^{-1}\mathbf{1}_{(0,\tau)}(t)$ — the extreme rays of the admissible cone, Remark 7.6.]
- P. Clément, J. A. Nohel, Asymptotic behavior of solutions of nonlinear Volterra equations with completely positive kernels, *SIAM J. Math. Anal.* **12** (1981) 514–535.
- Ph. Courrège, Sur la forme intégro-différentielle des opérateurs de $C_k^\infty$ dans $C$ satisfaisant au principe du maximum, *Séminaire Brelot–Choquet–Deny (Théorie du Potentiel)* **10** (1965/66), exp. 2, pp. 2-01–2-38. [Corollaire 2, p. 2-10: the *local* positive maximum principle forces a second-order diffusion operator, with no jump part.]
- B. de Vries, J. C. Principe, The gamma model — a new neural model for temporal processing, *Neural Networks* **5** (1992) 565–576. [Gamma memories.]
- H. Dym, H. P. McKean, *Gaussian Processes, Function Theory and the Inverse Spectral Problem*, Academic Press (1976). [The Krein string correspondence, book-length.]
- K.-J. Engel, R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Springer (2000). [Prop. II.1.7, p. 53: the core criterion.]
- D. Fagerström, Temporal scale spaces, *Int. J. Computer Vision* **64**(2–3) (2005) 97–106.
- W. Feller, *An Introduction to Probability Theory and Its Applications*, Vol. 2, 2nd ed., Wiley (1971). [§XIII.1: uniqueness (Thms. 1, 1a) and continuity (Thms. 2, 2a) for Laplace transforms, stated separately for probability distributions and for general measures; §XIII.4, Thms. 1 and 1a: complete monotonicity.]
- C. Halgreen, Self-decomposability of the generalized inverse Gaussian and hyperbolic distributions, *Z. Wahrsch. verw. Gebiete* **47** (1979) 13–17.
- T. Iijima, Basic theory on normalization of pattern (in case of typical one-dimensional pattern), *Bull. Electrotechnical Laboratory* **26** (1962) 368–388. [In Japanese.]
- M. E. H. Ismail, D. H. Kelker, Special functions, Stieltjes transforms and infinite divisibility, *SIAM J. Math. Anal.* **10** (1979) 884–901. [Bessel-function ratios as Stieltjes transforms; the spectral-cut densities.]
- A. N. Kochubei, General fractional calculus, evolution equations, and renewal processes, *Integral Equations Operator Theory* **71** (2011) 583–600.
- J. J. Koenderink, Scale-time, *Biol. Cybern.* **58** (1988) 159–162.
- S. Kotani, S. Watanabe, Krein's spectral theory of strings and generalized diffusion processes, in *Functional Analysis in Markov Processes*, Lecture Notes in Mathematics **923**, Springer (1982) 235–259. [The Krein correspondence as a bijection; the reference SSV Ch. 15 relies on.]
- J. Lamperti, Semi-stable Markov processes I, *Z. Wahrsch. verw. Gebiete* **22** (1972) 205–225. [The Lamperti correspondence and time change.]
- T. Lindeberg, D. Fagerström, Scale-space with causal time direction, in *Proc. ECCV'96*, Lecture Notes in Computer Science **1064**, Springer (1996) 229–240. [The Poisson scale space.]
- T. Lindeberg, Generalized Gaussian scale-space axiomatics comprising linear scale-space, affine scale-space and spatio-temporal scale-space, *J. Math. Imaging Vision* **40** (2011) 36–81.
- T. Lindeberg, Time-causal and time-recursive spatio-temporal receptive fields, *J. Math. Imaging Vision* **55** (2016) 50–88. [The time-causal limit kernel.]
- Y. Luchko, General fractional integrals and derivatives with the Sonine kernels, *Mathematics* **9** (2021) 594.
- M. Maejima, Y. Naito, Semi-selfdecomposable distributions and a new class of limit theorems, *Probab. Theory Related Fields* **112** (1998) 13–31.
- M. Maejima, K. Sato, Semi-selfsimilar processes, *J. Theoret. Probab.* **12** (1999) 347–373.
- R. S. Phillips, On the generation of semigroups of linear operators, *Pacific J. Math.* **2** (1952) 343–369. [Subordination of semigroups; the Phillips form of the subordinate generator.]
- J. Prüss, *Evolutionary Integral Equations and Applications*, Birkhäuser (1993). [Completely positive kernels; resolvent positivity.]
- S. G. Samko, A. A. Kilbas, O. I. Marichev, *Fractional Integrals and Derivatives: Theory and Applications*, Gordon & Breach (1993).
- K. Sato, *Lévy Processes and Infinitely Divisible Distributions*, Cambridge UP (1999). [Ch. 3: self-similar additive processes; Thm. 25.3: moments; Thm. 27.13: absolute continuity of self-decomposable laws.]
- R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*, 2nd ed., de Gruyter (2012). [Cited as SSV; Ch. 1–3, 6–8, 11. Numbering is 2nd-edition throughout: a chapter was inserted at position 10, so Thm. 11.3 here is Thm. 10.3 in the 1st edition.]
- N. Sonine, Sur la généralisation d'une formule d'Abel, *Acta Math.* **4** (1884) 171–176.
- M. D. Springer, W. E. Thompson, The distribution of products of beta, gamma and Gaussian random variables, *SIAM J. Appl. Math.* **18**(4) (1970) 721–737. [Thm. 1, p. 722: a product of independent gamma variables of arbitrary distinct shapes has a Meijer $G^{N,0}_{0,N}$ density. Density convention $M\{f\}(s) = \mathbb{E}[x^{s-1}]$, so the $G$-parameters are the shapes minus one.]
- F. W. Steutel, K. van Harn, *Infinite Divisibility of Probability Distributions on the Real Line*, Dekker (2004).
- O. Thorin, On the infinite divisibility of the Pareto distribution, *Scand. Actuarial J.* **1977** (1977) 31–40. [Cited as Thorin 1977a; the Thorin representation and the GGC class.]
- O. Thorin, On the infinite divisibility of the lognormal distribution, *Scand. Actuarial J.* **1977** (1977) 121–148. [Cited as Thorin 1977b.]
- R. Webster, Log-convex solutions to the functional equation $f(x+1) = g(x)f(x)$: $\Gamma$-type functions, *J. Math. Anal. Appl.* **209** (1997) 605–623. [Krull–Webster extension of Bohr–Mollerup; Thm. 3.1, p. 609, is the uniqueness theorem, Thm. 5.1, p. 615, the closure of the class under products and quotients. See also J.-L. Marichal, N. Zenaïdi, *A Generalization of Bohr–Mollerup's Theorem for Higher Order Convex Functions*, Springer (2022), for a modern book-length treatment.]
- J. G. Wendel, Left centralizers and isomorphisms of group algebras, *Pacific J. Math.* **2** (1952) 251–261. [Convolution representation of translation-invariant operators on $L^1$.]
- D. V. Widder, *The Laplace Transform*, Princeton UP (1941). [Ch. II, §5, Thm. 5b, pp. 58–59: the singularity at the abscissa of convergence for transforms with monotonic integrand — usually called the Pringsheim–Landau theorem, though Widder himself credits Hamburger (1921). Ch. VI, §9, Thm. 9a, pp. 246–247: Mellin inversion on a line of absolute convergence.]
- M. Yamazato, Unimodality of infinitely divisible distribution functions of class $L$, *Ann. Probab.* **6** (1978) 523–531. [Every self-decomposable law on the line is unimodal; applied in Remark 7.6 to the kernels of the whole admissible cone.]
