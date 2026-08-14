/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup

/-!
# The trust-boundary guard

Not part of the development: this file is elaborated by CI alone (`lean.yml`, guard 3), which
reads the `#print axioms` output below and fails if any axiom appears that
`blueprint/trust-boundary.txt` does not declare — and `linkage axioms --check` independently
refuses a declared name that no `AXIOMS.md` entry grounds. So the trust base cannot widen
without a reviewed ledger entry behind it, and a `sorry` reaching a headline result is caught
by the same step.

**What belongs here.** Every declaration a blueprint node points a `\lean{}` tag at with
`\leanok`, and the artifacts those tags stand on. Adding a node to the blueprint without adding
its declaration here silently exempts it from the guard, so the two are kept in step by hand.

Expected output today: Lean core (`propext`, `Classical.choice`, `Quot.sound`) everywhere, plus
`Hemigroup.exists_isFiniteMeasure_laplace_eq_exp_neg_levyExponent` — ledger A17 — on the
constructive direction and on the uniqueness clause, which quantifies over the kernels A17
builds and so inherits it through `kernel`.

The blueprint's `thm:main-characterization` is a collation and carries no tag of its own; its
halves `thm:main-construction` and `prop:main-uniqueness` do, and are listed below.
-/

-- Deliberately no `open Hemigroup`: the guard compares the printed axiom names against
-- `blueprint/trust-boundary.txt` by exact string match, and opening the namespace would
-- abbreviate them, so every interface axiom would read as undeclared.

/-! ### `def:levy-exponent` -/

#print axioms Hemigroup.levyExponent

/-! ### `lem:vanishing` -/

#print axioms Hemigroup.levyExponent_eq_zero_of_eq_zero

/-! ### `prop:laplace-uniqueness-causal`

The `[T]` refinement of `prop:laplace-uniqueness` (ledger A6). It reduces to Lean core, which is
why A6 is absent from `trust-boundary.txt`.
-/

#print axioms Hemigroup.laplace_injective

/-! ### `prop:laplace-uniqueness-sigma-finite` and `lem:laplace-local-finiteness`

The unbounded-measure refinement, which chapter 9 needs and which keeps A6 off the trust
boundary in its general form as well as its restricted one.
-/

#print axioms Hemigroup.laplaceL_injective_of_ne_top
#print axioms Hemigroup.measure_Icc_ne_top_of_laplaceL_ne_top

/-! ### `prop:laplace-continuity-causal`

Likewise for `prop:laplace-continuity` (ledger A5).
-/

#print axioms Hemigroup.tendsto_integral_of_tendsto_laplace

/-! ### `lem:transform-tightness`

The Markov bound. It lives in `Continuity.lean`, which imports the interface file, but the
statement does not mention `kernel`, so it does not inherit A17 — and this line is what checks
that rather than assuming it.
-/

#print axioms Hemigroup.measureReal_Ioi_mul_le

/-! ### `lem:selfdecomposable-increment`

(3) ⇒ (1) of Lemma 7.1, the cheap half — a change of variables and a sign. It is what
`thm:main-construction` cites instead of the derivative route, and this line is what checks the
claim that doing so costs no ledger entry.
-/

#print axioms Hemigroup.levyExponentD_increment

/-! ### `def:cascade-family`

The structure carries no proof obligations of its own; what has to hold is that the constructed
kernels satisfy it, which is the next entry.
-/

/-! ### `thm:main-construction`

Theorem 7.3 (⇐), and the instance that checks `def:cascade-family` against a model. A17 enters
here.
-/

#print axioms Hemigroup.SelfDecomposableExponent.cascadeFamily

/-! ### `prop:main-uniqueness`

Theorem 7.3's uniqueness clause. A17 reaches it through `kernel`, which the statement quantifies
over; nothing in the argument itself leaves Lean core.
-/

#print axioms Hemigroup.SelfDecomposableExponent.gauge_and_exponent_unique

/-! ### `lem:convolution-representation` -/

#print axioms Hemigroup.CascadeCore.existsUnique_repr
#print axioms Hemigroup.mconvL1_satisfies_axioms

/-! ### `lem:transform-continuity` -/

#print axioms Hemigroup.CascadeCore.transform_continuity

/-! ### `lem:additivity` -/

#print axioms Hemigroup.CascadeCore.additivity

/-! ### `thm:increments-bernstein`

The `LE` reading of Theorem 5.2. Prokhorov and dominated convergence are Mathlib's, so this
reduces to Lean core: no ledger entry is spent on the null-array limit, which is the point of
running it elementarily.
-/

#print axioms Hemigroup.CascadeCore.exponent_hasLevyRep

/-! ### `cor:strict-monotonicity` -/

#print axioms Hemigroup.CascadeCore.strict_monotonicity

/-! ### `lem:covariance-laplace`

(A8) turned into the scalar identity `(6.1)`. The route runs through the uniqueness clause of
`lem:convolution-representation`, so this checks that nothing on the way in picked up an
interface.
-/

#print axioms Hemigroup.CascadeCore.covariance_laplace

/-! ### `lem:action-rigidity` -/

#print axioms Hemigroup.CascadeCore.action_rigidity

/-! ### `prop:canonical-gauge`

The gauge is built from `Function.invFunOn`, so `Classical.choice` is expected and nothing else.
-/

#print axioms Hemigroup.CascadeCore.canonical_gauge

/-! ### `thm:main-analysis`

Two lines, and the pair is the point. `similarity_form` is chapters 4 to 6 collated — the whole
hypothesis of the one appeal to `lem:selfdecomposable-derivative` — and reduces to **Lean core**,
so everything up to that appeal is interface-free. `main_analysis` adds the appeal and picks up
**A18 and nothing else**.

Read together with `thm:main-construction` and `prop:main-uniqueness` above, which carry A17 and
not A18, this is what makes the article's asymmetry checkable rather than asserted: the analysis
direction crosses the boundary where the constructive one does not, and the two entries do not
mix.
-/

#print axioms Hemigroup.CascadeCore.similarity_form
#print axioms Hemigroup.CascadeCore.main_analysis

/-! ### `prop:admissibility-criterion`, and the two instances built from it

The criterion itself, and the two concrete exponents. `#print axioms` on a *definition* is worth
running for the same reason it is worth running on a theorem: these two carry proof obligations
in their fields, and an interface leaking into one of them would mean the witness is not a
witness. Both reduce to Lean core.
-/

#print axioms Hemigroup.levyExponentD_ne_top_of_integrableOn
#print axioms Hemigroup.gammaExponent
#print axioms Hemigroup.dickmanExponent

#print axioms Hemigroup.SelfDecomposableExponent.integrableOn_of_ne_top

#print axioms Hemigroup.SelfDecomposableExponent.hasDerivAt_toRealExponent

#print axioms Hemigroup.SelfDecomposableExponent.tendsto_toRealExponent_nhdsGT_zero
#print axioms Hemigroup.SelfDecomposableExponent.gammaExponent_toRealExponent

#print axioms Hemigroup.SelfDecomposableExponent.stableExponent
#print axioms Hemigroup.SelfDecomposableExponent.stableExponent_toRealExponent

#print axioms Hemigroup.SelfDecomposableExponent.laplace_memoryKernel

#print axioms Hemigroup.SelfDecomposableExponent.laplaceL_memoryKernel

#print axioms Hemigroup.SelfDecomposableExponent.symbol_pos

#print axioms Hemigroup.SelfDecomposableExponent.sonine_conservation

/-! ### `lem:mellin-data`, chapter 11's entry point

The identity and the bound, plus the `ℝ≥0∞` hinge both come out of and the Fubini side condition
that hinge *is*. All four carry **A17 and nothing else**, which is the expected reading and worth
saying why: `lawT₁` is `F.kernel 0 1`, so every statement about the profile quantifies over the
measure A17 builds and inherits it through `kernel`, exactly as `prop:main-uniqueness` does. No
chapter-11 interface enters — in particular **not A12**, which grounds `def:inversion-operator`
and not this node.
-/

#print axioms Hemigroup.lintegral_ofReal_rpow_mul_exp
#print axioms Hemigroup.SelfDecomposableExponent.lawT₁_singleton_zero
#print axioms Hemigroup.SelfDecomposableExponent.negMoment_ne_top_of_lt_zStar
#print axioms Hemigroup.SelfDecomposableExponent.zStar
#print axioms Hemigroup.SelfDecomposableExponent.le_zStar_of_negMoment_ne_top
#print axioms Hemigroup.SelfDecomposableExponent.zStar_eq_top_of_forall_negMoment_ne_top
#print axioms Hemigroup.SelfDecomposableExponent.one_lt_zStar_of_forall_negMoment_ne_top
#print axioms Hemigroup.SelfDecomposableExponent.lintegral_lintegral_gamma
#print axioms Hemigroup.SelfDecomposableExponent.integrable_mellin_laplace
#print axioms Hemigroup.SelfDecomposableExponent.mellin_profile
#print axioms Hemigroup.SelfDecomposableExponent.norm_mellin_profile_le

/-! ### `lem:inversion-symbol` (11.14), the complex-analytic half of chapter 11

Analyticity of `H̃` on the strip, its non-vanishing at real points, the isolation of its zeros,
and the symbol `B` with its closed form and meromorphy. A17 again and nothing else: the analysis
is Mathlib's — `analyticAt_complexMGF` for `E[T₁^{-z}]`, `differentiableAt_Gamma` for the other
factor — and the article's own interfaces do not enter. `lem:mellin-vertical` is what would carry
A12, and it is not here.
-/

#print axioms Hemigroup.analyticAt_Gamma
#print axioms Hemigroup.SelfDecomposableExponent.negMomentC_eq_complexMGF
#print axioms Hemigroup.SelfDecomposableExponent.momentInterval_subset_integrableExpSet
#print axioms Hemigroup.SelfDecomposableExponent.analyticAt_negMomentC
#print axioms Hemigroup.SelfDecomposableExponent.analyticAt_mellin_profile
#print axioms Hemigroup.SelfDecomposableExponent.mellin_profile_ofReal_ne_zero
#print axioms Hemigroup.SelfDecomposableExponent.eventually_mellin_profile_ne_zero
#print axioms Hemigroup.SelfDecomposableExponent.inversionSymbol_eq
#print axioms Hemigroup.SelfDecomposableExponent.analyticAt_inversionSymbol
#print axioms Hemigroup.SelfDecomposableExponent.meromorphicOn_inversionSymbol

/-! ### `lem:symbol-rigidity` (11.15), the core of `lem:symbol-uniqueness`

The step that makes the eigenfunction relation *pin* the symbol rather than merely constrain it.
A17 and nothing else — and note which entry is absent: the reduction *to* the transform relation
is `def:inversion-operator`, hence A12, and it is deliberately not in this file. What is here is
everything downstream of that reduction.
-/

#print axioms Hemigroup.SelfDecomposableExponent.SameSymbolAction.eqOn_of_ne_zero
#print axioms Hemigroup.SelfDecomposableExponent.SameSymbolAction.eventuallyEq
#print axioms Hemigroup.SelfDecomposableExponent.SameSymbolAction.eq_of_continuousAt
#print axioms Hemigroup.SelfDecomposableExponent.SameSymbolAction.eqOn

/-! ### Route B's measurability machinery

Not blueprint nodes: the three general lemmas `lem:potential-kernel` needs to form
`U = ∫₀^∞ μ_t dt` at all. They are listed because the sorry guard cannot see them — they live in
`Hemigroup/` and are consumed by a `Skeleton/` statement that still carries a `sorry` upstream, so
this is the only check that they themselves are interface-free. All three reduce to Lean core.
-/

#print axioms Hemigroup.levyExponent_smul
#print axioms Hemigroup.conv_Iic_le
#print axioms Hemigroup.measurable_of_antitone_measure_Iic
#print axioms Hemigroup.sigmaFinite_of_isCausal_of_measure_Icc_ne_top
#print axioms Hemigroup.lintegral_one_sub_exp_eq_tail
#print axioms Hemigroup.SelfDecomposableExponent.tendsto_k_atTop_nhds_zero

/-! ### `lem:potential-kernel` and `prop:sonine-pair-exists` — Route B complete

The lines that matter most in chapter 9, because they are what the route was *chosen* for. The
blueprint's own proof of `lem:potential-kernel` goes through Bernstein–Widder for general measures
— ledger **A1**, the entry the representation-first design exists to keep off the critical path.
Route B constructs the measure instead, and these lines are the check that it worked: **A17 and
nothing else**, with A1 and A2 absent. The article's claim about its own trust base is therefore
machine-checked rather than asserted, in the one place it was most at risk.
-/

#print axioms Hemigroup.tailInv
#print axioms Hemigroup.exists_tailMeasure
#print axioms Hemigroup.SelfDecomposableExponent.exists_levyTriple_symbol
#print axioms Hemigroup.SelfDecomposableExponent.exists_subordinatorFamily
#print axioms Hemigroup.SelfDecomposableExponent.existsUnique_potentialKernel
#print axioms Hemigroup.SelfDecomposableExponent.exists_sonine_pair

/-! ### `lem:mellin-vertical` (11.13), and the Γ estimate under it

The clause A12's retirement turns on. It was recorded twice as blocked on a missing Mathlib
estimate — the vertical decay of `|Γ(c+iτ)|` — and is not: integrability needs only quadratic
decay, which is the functional equation twice. The three `Gamma` lemmas are general and reduce to
Lean core; the profile's vertical integrability inherits A17 through `kernel`, as everything about
`T₁` does.
-/

#print axioms Hemigroup.norm_Gamma_le_of_re_pos
#print axioms Hemigroup.norm_Gamma_mul_sq_le
#print axioms Hemigroup.integrable_norm_Gamma_vertical
#print axioms Hemigroup.SelfDecomposableExponent.verticalIntegrable_mellin_profile

/-! ### The same estimate against an arbitrary polynomial

Chapter 12 inverts `P(z)·H̃(z)` with `P` of degree `n`, and needs `∫ |τ|ⁿ‖Γ(c+iτ)‖ dτ < ∞`. It is
the lemma above with the functional equation peeled `n` times instead of twice — each factor of
`Γ(z+k)/Γ(z)` has imaginary part `τ`, so it contributes a `|τ|` — and the binomial theorem to turn
`(M+|τ|)ⁿ` into a finite sum of those. No asymptotics, and Lean core alone: nothing here mentions
a kernel.

This is what was standing between the two directions of `lem:local-polynomial-symbol`. Recording
it separately is the point: the missing piece was never the Fubini-and-Gamma computation, which is
below, but one estimate, and naming it is what let it be done.
-/

#print axioms Hemigroup.Gamma_add_natCast
#print axioms Hemigroup.norm_Gamma_mul_pow_le
#print axioms Hemigroup.integrable_norm_Gamma_mul_pow_vertical
#print axioms Hemigroup.integrable_norm_Gamma_mul_add_abs_pow_vertical

/-! ### `def:inversion-operator` (11.3), ledger **A12**

The operator, and the two theorems that compute it. What these lines check is narrower than the
node and worth being exact about: the machine-checked statements take the realising function `h`
as a **hypothesis** — `RealisesSymbolAction` — where the blueprint's definition asserts, on A12's
authority, that absolute integrability of `B(-z)g̃(z)` produces it. So A12 is not retired by these
lines. What they establish is that everything *after* the existence of `h` is interface-free: the
functional-calculus reading, the transform-level identity, and the shift.

Whether A12 retires is now a concrete question about this article rather than about Mathlib — does
every use of `A` exhibit its `h`? — and the profile case is the one to settle it.
-/

#print axioms Hemigroup.SelfDecomposableExponent.inversionOperator
#print axioms Hemigroup.SelfDecomposableExponent.inversionOperator_eq
#print axioms Hemigroup.SelfDecomposableExponent.mellin_inversionOperator
#print axioms Hemigroup.SelfDecomposableExponent.mellin_inversionOperator_eq

/-! ### The profile instance, and what it does to **A12**

`def:inversion-operator`'s remaining interface is the production of the function `B(θ)g` names.
These lines are the check that the article never calls on it: for the only shape in which `A` is
ever applied — the profile dilate `g = H(s·)` — the referent `h(x) = s x H(sx)` is *exhibited*,
and `#print axioms` on the instance gives A17 and nothing else.

`inversionOperator_profile` is then the eigenfunction relation `A[H(s·)] = s H(s·)`, i.e.
`thm:signaling-form`(1). Note that the instance and the eigenfunction relation are the same
statement: `A g = x⁻¹h` and `h(x) = s x H(sx)` give `s H(sx)` with the weights cancelling.

The two `mellin_profile_ne_zero` lines are what the a.e. reading of the realising identity costs.
The blueprint's proof of clause (1) says the product `B(-z)g̃(z)` "contain[s] no division"; that is
true of the simplified product and false of `B` as a function, so the division has to be cancelled
on the line, which needs its zeros to be null.
-/

#print axioms Hemigroup.SelfDecomposableExponent.countable_zeros_mellin_profile
#print axioms Hemigroup.SelfDecomposableExponent.ae_mellin_profile_ne_zero
#print axioms Hemigroup.SelfDecomposableExponent.mellinConvergent_profile
#print axioms Hemigroup.SelfDecomposableExponent.mellin_profile_comp_mul_weight
#print axioms Hemigroup.SelfDecomposableExponent.realisesSymbolAction_profile
#print axioms Hemigroup.SelfDecomposableExponent.inversionOperator_profile

/-! ### `lem:symbol-uniqueness` (11.4), both halves

Recorded as waiting on ledger A12 and not waiting on it. Step 1 was read as needing
`def:inversion-operator`'s transform identity, hence the *production* of `B(θ)g`; but an operator
"of the form `x⁻¹B(θ)`" is one whose `B(θ)g` is **given**, and the class the statement quantifies
over is exactly the class where the referent exists. So the citation was never in the way.

Note what the route avoids: no injectivity of the inverse Mellin transform, which is the obvious
tool and a second Widder citation (Thm. 6a, listed in the ledger against just this possibility).
Two operators agreeing on `H(s·)` share a realising function there, so their transforms agree at
every point and the symbols come off directly.
-/

#print axioms Hemigroup.SelfDecomposableExponent.sameSymbolAction_of_realisesAction
#print axioms Hemigroup.SelfDecomposableExponent.eventuallyEq_inversionSymbol_of_realisesAction

/-! ### `lem:memory-fractional-integrals` (11.5), analytic core

The Mellin transform in `x` of the delayed average is `H̃(z)` times the Riemann–Liouville integral
of the past signal. `riemannLiouville` is *defined* here rather than cited: Mathlib carries no
fractional integral of any order, and the article's Samko–Kilbas–Marichev citation is for the
notation and theory of `Iᶻ`, of which chapter 11 uses only the definition. So these lines add no
interface, and `#print axioms` gives A17 alone.

What they do not cover is the identification of the integrand with `Φ_{0,x}f`, which is an
`L¹`-level statement and carries the modelling decision recorded in `PLAN-chapters-8-12.md`.
-/

#print axioms Hemigroup.riemannLiouville
#print axioms Hemigroup.integrableOn_pastIntegrand
#print axioms Hemigroup.mul_riemannLiouville
#print axioms Hemigroup.integral_pastNorm_comp_mul
#print axioms Hemigroup.integrable_rpow_neg
#print axioms Hemigroup.integrable_delayed
#print axioms Hemigroup.mellin_delayed_average

/-! ### `lem:memory-fractional-integrals` (11.5), first clause complete

The bridge from the analytic core to the field. `kernel_zero_eq_map_lawT₁` is the canonical gauge
at the level of measures — the article reads `μ_{0,x}` as the law of `x·T₁` off the notation,
which in Lean is a lemma, both sides being causal with transform `e^{-F(xs)}` and `kernel_unique`
being Laplace injectivity. `coeFn_Phi_zero` then identifies the chosen representative with
`Φ_{0,x}f` at each scale, and `mellin_delayedField` is the clause itself. A17 alone throughout.
-/

#print axioms Hemigroup.laplace_map_mul
#print axioms Hemigroup.isCausal_map_mul
#print axioms Hemigroup.SelfDecomposableExponent.kernel_zero_eq_map_lawT₁
#print axioms Hemigroup.SelfDecomposableExponent.coeFn_Phi_zero
#print axioms Hemigroup.SelfDecomposableExponent.mellin_delayedField

/-! ### `thm:signaling-form`(2), the Mellin form — transform side

The displayed computation of Theorem 4′(2), entire. What stands between it and the node's
conclusion is the derivative clause of `lem:memory-fractional-integrals`, which needs `∂_t u` and
hence `lem:delay-core`.

`integrableOn_pastIntegrand_of_bounded` is the range repair: 11.5 is stated for `1 < Re z < z_*`
and 11.6(2) applies it at `z-1` while stating the same range, so the chain does not close as
written. It closes because 11.6(2) hypothesises `f ∈ 𝒟`, which is bounded, and boundedness moves
the lower end of the strip from `1` to `0`. Nothing about the result changes; what changes is what
the lemma says.
-/

#print axioms Hemigroup.integrableOn_pastIntegrand_of_bounded
#print axioms Hemigroup.SelfDecomposableExponent.inversionSymbol_mul_mellin_delayedField

/-! ### `lem:fractional-integral-derivative` (11.20) — `Iᶻf' = I^{z-1}f`

The transform half of 11.5's derivative clause. Note what these lines show: the statement is about
the Riemann–Liouville family and mentions no hemigroup object, so it reduces to **Lean core
alone** — not even A17 enters. It is the first result in the development of which that is true and
which is not a general-purpose lemma about `Γ`.

The draft derives it from the semigroup property `I^{z-1}I¹ = Iᶻ`, a Beta-integral identity that
would have to be proved in its own right. Fubini over the triangle avoids it entirely.
-/

#print axioms Hemigroup.integral_cpow_sub_left
#print axioms Hemigroup.riemannLiouville_integral

/-! ### `thm:signaling-form`(2)'s Mellin form, entire

The derivative clause and with it Theorem 4′(2)'s Mellin form. Note the reading:
`delayedField_eq_setIntegral` says the field of `f` is the **primitive** of the field of `f'`,
which is what `∂_t u` means in `X₀`. The pointwise reading — a derivative at every `t` — is false:
`f ∈ 𝒟` is absolutely continuous so `f'` exists only a.e., and the field is a convolution of two
`L¹` functions, hence `L¹` and not continuous. Buying continuity would cost Sato Thm. 27.13, an
interface, for nothing.

`abs_primitive_le` is the part of `f ∈ 𝒟` that is actually load-bearing: the primitive of an `L¹`
function is bounded, which is what widens 11.5's strip from `Re z > 1` to `Re z > 0` and lets
`thm:signaling-form`(2) apply it at `z-1`.
-/

#print axioms Hemigroup.SelfDecomposableExponent.delayedField_eq_setIntegral
#print axioms Hemigroup.SelfDecomposableExponent.abs_primitive_le
#print axioms Hemigroup.SelfDecomposableExponent.mellin_delayedField_deriv
#print axioms Hemigroup.SelfDecomposableExponent.mellin_signaling_form

/-! ### `thm:signaling-form` — Theorem 4′, assembled

The theorem the article exists for, as one declaration. Its six conjuncts are proved in the files
that develop them; this line is the check that the assembly costs nothing new — A17 and nothing
else, for a statement that runs from the construction through the Mellin calculus to uniqueness.

Assembling it is also what showed the chapter was not finished when every *lemma* was `\leanok`:
clause (2) asserts four things and only the Mellin form had been proved. A theorem node exists
precisely because it asserts more than its lemmas do.
-/

#print axioms Hemigroup.SelfDecomposableExponent.delayedField_eq_zero
#print axioms Hemigroup.SelfDecomposableExponent.tendsto_Phi_zero
#print axioms Hemigroup.SelfDecomposableExponent.laplaceFun_delayedField
#print axioms Hemigroup.SelfDecomposableExponent.inversionOperator_const_mul_profile
#print axioms Hemigroup.SelfDecomposableExponent.signaling_form

/-! ### `thm:main-characterization` — the main theorem, assembled

The bundle, so that the graph stops reporting the article's main theorem as unproved when all of
it is proved. **The per-half lines above remain the load-bearing ones**: the three halves cross the
trust boundary in different places — `(⇐)` and uniqueness on A17, `(⇒)` on A18, neither borrowing
the other's — and a bundle cannot show that, since it necessarily depends on both. This line will
therefore print both names, and that is correct rather than a regression.
-/

#print axioms Hemigroup.SelfDecomposableExponent.main_characterization

/-! ## Chapter 12 — locality

### `lem:log-convexity` — the first node of chapter 12

Log-convexity of the negative moments, in two readings. The `[0,∞]` form is unconditional and the
real form is the blueprint's, on `Ioo 0 z_*` rather than the blueprint's `(0,∞)` because the
latter presupposes `z_* = ∞`, which is the clause of `lem:moment-recursion` that ledger **A13**
carries.

All three lines print **A17 and nothing else** — A17 because `lawT₁` is a kernel of the construction
and so every statement about `T₁` inherits it, not because anything here uses it. What matters for
chapter 12 is what is *absent*: none of the chapter's own cited interfaces (A13 Widder, A14
Courrège, A15 Krull--Webster) is touched by this node.
-/

#print axioms Hemigroup.SelfDecomposableExponent.negMoment_le_rpow_mul_rpow
#print axioms Hemigroup.SelfDecomposableExponent.negMoment_pos
#print axioms Hemigroup.SelfDecomposableExponent.convexOn_log_negMoment

/-! ### `lem:symbol-vanishes-at-origin` — clause (1) of `lem:moment-recursion`, split off

`B(-z) → 0` as `z ↓ 0`, with `m(z) → 1` as its first half. The node it was split from spends
ledger **A13** on its clause (2); these lines show that clause (1) does not, printing A17 and
nothing else. The polynomial hypothesis under which the blueprint states clause (1) is inert in
the argument, which is why the split-off node does not carry it.
-/

#print axioms Hemigroup.SelfDecomposableExponent.tendsto_negMoment_nhdsGT_zero
#print axioms Hemigroup.SelfDecomposableExponent.tendsto_inversionSymbol_nhdsGT_zero

/-! ### `lem:moment-recursion-quotient` — clauses (1) and (3) of `lem:moment-recursion`

Split off for the same reason `lem:symbol-vanishes-at-origin` was: the node they come from spends
ledger **A13** on its clause (2), and these lines are the check that they do not spend it too.
A17 and nothing else.

Clause (1) is two statements and both are now here. `B(0) = 0` was already
`tendsto_inversionSymbol_nhdsGT_zero`, which needs no polynomial hypothesis;
`coeff_zero_eq_zero_of_symbol_eq` is where the polynomial hypothesis enters, and only to turn that
limit into a value. The factorisation `B(-z) = z·Q(z)` is then exact and analysis-free — the Euler
factors' own recursion `E_{j+1}(z) = -z·E_j(z+1)`, so `Q` comes out in the same basis one degree
lower.

Clause (3) is `lem:mellin-data` at a *real* point of the strip, where `H̃` is known not to vanish,
so the symbol identity holds pointwise and `z` cancels. **Its range is `0 < z < z_* - 1`**, not the
blueprint's `(0,∞)`: widening it is `z_* = ∞`, which is clause (2) and which is what A13 carries.
-/

#print axioms Hemigroup.mellinEulerFactor_zero_eq_zero
#print axioms Hemigroup.symbolQuotient
#print axioms Hemigroup.sum_mellinEulerFactor_eq_mul_symbolQuotient
#print axioms Hemigroup.symbolQuotient_two
#print axioms Hemigroup.SelfDecomposableExponent.coeff_zero_eq_zero_of_symbol_eq
#print axioms Hemigroup.SelfDecomposableExponent.exists_pos_symbolQuotient_of_symbol_eq
#print axioms Hemigroup.SelfDecomposableExponent.exists_symbolQuotient_of_isLocalOfOrder

/-! ### `lem:pmp-verification` — the (⇐) half of `thm:locality`'s maximum principle

`thm:locality` uses the PMP twice and at opposite costs. Its (⇒) direction spends ledger **A14**
(Courrège) on the order bound — that a local operator satisfying the PMP is a pure second-order
diffusion — and that is cited, not proved. Its (⇐) direction has to check that the operators the
theorem exhibits *do* satisfy the PMP, and that is elementary. These lines are what keeps the two
apart: they print A17 through `inversionOperator` and **not A14**.

`deriv_deriv_nonpos_of_isLocalMax` is the second-derivative half of Fermat's rule, which Mathlib
does not carry — it has `IsLocalMax.deriv_eq_zero` and stops there — so it is written from
scratch. It mentions nothing of this development and prints **Lean core alone**.
-/

#print axioms Hemigroup.deriv_deriv_nonpos_of_isLocalMax
#print axioms Hemigroup.contDiff_of_isTestFunction_ofReal
#print axioms Hemigroup.SelfDecomposableExponent.satisfiesPMP_of_isLocalOfOrderCore
#print axioms Hemigroup.SelfDecomposableExponent.satisfiesPMP_of_symbol_eq

/-! ### `thm:locality`(⇒), the order-two branch

The step that turns the recursion into the Gamma form, and so `T₁` into the inverse-gamma family.
Both citations of that direction enter as **hypotheses** rather than as axioms, phrased so either
can be demoted the day it is proved: `AllNegMomentsFinite` is `lem:moment-recursion`(2), ledger
**A13**, and the order bound is Courrège, **A14**, which here is just the order `2`. So these lines
print A17 and neither A13 nor A14 — the interfaces are in the statement, where a reader can see
them, and not in the trust base.

`tendsto_negMoment_succ_nhdsGT_zero` is where the work is: `a₀ > 0` is `Q(0) = m(1)`, a limit, and
positivity of `Q` on the open half-line gives only `a₀ ≥ 0`. The dominating function is `t^{-2}+1`,
integrable exactly because `2 < z_*` — which is what A13 supplies and what the `ℝ≥0∞` abscissa
finally lets one say.
-/

#print axioms Hemigroup.SelfDecomposableExponent.tendsto_negMoment_succ_nhdsGT_zero
#print axioms Hemigroup.SelfDecomposableExponent.exists_gamma_form_of_isLocalOfOrder_two

/-! ### `thm:locality`(⇒), the order-one branch

The degenerate member, where the kernels are deterministic delays. Same shape as order two --- A13
and A14 as hypotheses, A17 alone in the trust base --- but it uses neither Krull--Webster nor
Bohr--Mollerup, and the node always said so: at order one the recursion has a constant multiplier
and `log m` is convex with constant unit increments, hence affine.

`eq_of_convexOn_of_periodic` is that fact, and Mathlib does not carry it. The usual proof goes
through continuity of a convex function on an open interval, to get boundedness, to get
antitonicity; none of that is needed. Convexity on `x < y < y+1`, with `y` written as a
combination of `x` and `y+1`, gives `g(y) ≤ g(x)` from periodicity alone. Three points and one
inequality, and it prints Lean core.
-/

#print axioms Hemigroup.convexOn_const_mul_id
#print axioms Hemigroup.antitone_of_convexOn_of_periodic
#print axioms Hemigroup.eq_of_convexOn_of_periodic
#print axioms Hemigroup.SelfDecomposableExponent.exists_pow_form_of_isLocalOfOrder_one

/-! ### `thm:locality`(⇒), collated

The two branches are exhaustive, and the collation is what says so. Order `0` is impossible ---
`def:locality-pmp` asks `c_0` not to vanish identically while `lem:moment-recursion`(1) forces
`γ_0 = 0` and
covariance makes `c_0` identically `0` --- and orders above `2` are excluded by the hypothesis
that is A14's conclusion. So the theorem's case list is a dichotomy for a reason, not by
inspection.

The positive maximum principle does not appear in either line, and that is the point: (⇒) uses it
*only* through **A14**, whose conclusion is the order bound. A statement carrying `SatisfiesPMP`
as an unused hypothesis would misreport where the principle is spent.

A17 and neither A13 nor A14, both being hypotheses.
-/

#print axioms Hemigroup.SelfDecomposableExponent.not_isLocalOfOrder_zero
#print axioms Hemigroup.SelfDecomposableExponent.exists_moment_form_of_isLocalOfOrder

/-! ### `lem:gamma-recursion-uniqueness` — ledger A15, order-two case, discharged

Krull--Webster restricted to a linear `Q`, which is the only case `thm:locality` applies it to,
proved from Mathlib's Bohr--Mollerup. The statement mentions nothing of this development, so this
line should print **Lean core alone** — no A17, since no kernel appears in it. That is the check
that the entry really is discharged rather than relocated.
-/

#print axioms Hemigroup.eq_gamma_form_of_logConvex_of_recursion

/-! ### The engine of `lem:local-polynomial-symbol`

The Mellin symbol of the Euler operator, `M[xʲg⁽ʲ⁾](z) = (∏_{i<j}(-z-i))·M[g](z)`. Mathlib has no
Mellin/derivative interface, so this is written from scratch; it mentions nothing of this
development, so like `eq_gamma_form_of_logConvex_of_recursion` it should print **Lean core alone**.
-/

#print axioms Hemigroup.mellin_pow_mul_iteratedDeriv
#print axioms Hemigroup.integral_cpow_mul_deriv

/-! ### Inversion for test functions

Everything `mellinInv_mellin_eq` asks for. The vertical-integrability clause is the only one with
content, and it comes out of the engine above rather than from an estimate: at `j = 2` the identity
reads `E2(z)*M[g](z) = M[x^2 g'']( z)`, whose right side is bounded on the line while
`||E2(c+iy)|| >= y^2`. Quadratic decay, one power more than integrability needs, and no asymptotic
analysis anywhere. Lean core alone.
-/

#print axioms Hemigroup.verticalIntegrable_mellin
#print axioms Hemigroup.mellinInv_mellin_of_isTestFunction

/-! ### `def:locality-pmp` and the (⇐) direction of `lem:local-polynomial-symbol`

The polynomial symbol turned into a differential expression. A17 through `inversionOperator`,
which quantifies over the construction's kernels; nothing else, and in particular none of chapter
12's own cited interfaces.

This direction was stated without the standing hypothesis (H), and that was recorded here as a
finding: nothing in its argument used (H), only the statement's non-vacuity did. It now takes (H),
and the reason is worth keeping visible because it is not a defect in the proof. Its symbol
hypothesis is asked for **off the zeros of `H̃`**, which is what the (⇒) direction delivers and all
it can deliver — `inversionSymbol` is a quotient by `H̃` — and "the zeros on the line are null" is
`ae_mellin_profile_ne_zero`, which needs (H). So (H) is the price of the two halves composing,
paid in the direction where it is cheap. What it buys costs nothing analytically:
`mellinInv_congr_line_ae` discards the null set, `mellinInv` integrating over the line rather than
evaluating on it.
-/

#print axioms Hemigroup.mellinInv_congr_line_ae
#print axioms Hemigroup.SelfDecomposableExponent.IsLocalOfOrderCore
#print axioms Hemigroup.SelfDecomposableExponent.IsLocalOfOrder
#print axioms Hemigroup.SelfDecomposableExponent.isLocalOfOrderCoreOfSymbolEq
#print axioms Hemigroup.SelfDecomposableExponent.isLocalOfOrderCore_of_symbol_eq

/-! ### Covariance of the inversion operator

`A Δ_σ = σ⁻¹ Δ_σ A`, which the blueprint asserts in passing inside 12.2's proof and which is the
load-bearing step of that lemma's (⇒) direction. A17 through `inversionOperator`; the two
supporting identities about positive reals raised to a complex power are Lean core.
-/

#print axioms Hemigroup.inversionOperator_lineDilate
#print axioms Hemigroup.mellinInv_cpow_mul

/-! ### Prescribed jets

At every point of `(0,∞)` and every order `m`, a test function whose jet there is the `m`-th basis
vector. This is what licenses comparing coefficients of a differential expression, and so what the
(⇒) direction of `lem:local-polynomial-symbol` rests on. Lean core alone: nothing here mentions a
kernel.
-/

#print axioms Hemigroup.exists_isTestFunction_jet
#print axioms Hemigroup.iteratedDeriv_ofReal_sub_pow

/-! ### Covariance forces the coefficients homogeneous

`c_m(σ) = c_m(1) σ^{m-1}` — the first half of the (⇒) direction of `lem:local-polynomial-symbol`,
and the step the blueprint takes by "comparing coefficients of g^(j)(x/σ)". A17 through
`inversionOperator`.
-/

#print axioms Hemigroup.SelfDecomposableExponent.coeff_eq_of_isLocalOfOrder
#print axioms Hemigroup.iteratedDeriv_lineDilate

/-! ### Derivatives of the profile

`H^(j)(u) = (-1)^j E[T_1^j e^{-u T_1}]`, which the profile clause of `def:locality-pmp` needs and
which chapter 11 never had occasion to establish. It is free: `H` is Mathlib's `mgf` at a negative
argument, and `ProbabilityTheory.iteratedDeriv_mgf` does the differentiation under the integral.
A17 through `lawT₁`.
-/

#print axioms Hemigroup.SelfDecomposableExponent.profile_eq_mgf
#print axioms Hemigroup.SelfDecomposableExponent.iteratedDeriv_profile_comp_mul

#print axioms Hemigroup.iteratedDeriv_ofReal_comp
#print axioms Hemigroup.SelfDecomposableExponent.iteratedDeriv_profileC_comp_mul

/-! ### `lem:mellin-data`, restated for a measure

The three steps of chapter 11's Gamma-integral hinge, freed of `T₁`. They are what chapter 12
spends on the weighted law `tʲ μ(dt)`, and they should print **Lean core alone** — no A17, since
no kernel appears in them. That is the check that the generalisation really did detach the
computation from the construction rather than carrying it along.
-/

#print axioms Hemigroup.lintegral_lintegral_gamma_of_ae_mem_Ioi
#print axioms Hemigroup.integrable_mellin_laplace_of_ae_mem_Ioi
#print axioms Hemigroup.mellin_laplace_of_ae_mem_Ioi
#print axioms Hemigroup.mellinConvergent_laplace_of_ae_mem_Ioi

/-! ### The engine of `lem:local-polynomial-symbol` on the profile class

`M[x ↦ xʲ ∂ₓʲ H(sx)](w) = E_j(w)·M[H(s·)](w)`, with no integration by parts: the derivative is
already an integral (`ProfileDeriv.lean`), the weight `xʲ` is a Mellin shift, the dilation is a
factor, and what is left is `lem:mellin-data` on the weighted law. A17 through `lawT₁`; the two
`Γ`/Euler-factor identities and `mellin_finset_sum` mention nothing of this development and print
Lean core alone.
-/

#print axioms Hemigroup.mellinEulerFactor_eq_neg_one_pow_mul_prod
#print axioms Hemigroup.norm_mellinEulerFactor_le
#print axioms Hemigroup.mellin_finset_sum
#print axioms Hemigroup.SelfDecomposableExponent.mellin_weightedProfile
#print axioms Hemigroup.SelfDecomposableExponent.mellinConvergent_weightedProfile
#print axioms Hemigroup.SelfDecomposableExponent.mellin_pow_mul_iteratedDeriv_profile

/-! ### `lem:local-polynomial-symbol`, the (⇒) direction — the node closed

The clause the skeleton carried, and the two forms it takes. A17 through `inversionOperator` and
`lawT₁`; none of chapter 12's own cited interfaces (A13 Widder, A14 Courrège, A15 Krull--Webster)
is touched, and neither is A12 — the route runs through `lem:symbol-uniqueness`, whose realising
function is exhibited rather than produced.

**Three statements rather than one, because they are not the same statement.** The recursion
`H̃(z+1) = P(z)H̃(z)` holds at every point of the strip with no side condition, and is what
`lem:moment-recursion` consumes. `B = P` as an equality of meromorphic functions is the
`EventuallyEq`, also unconditional. `B(z) = P(z)` as an equality of *values* holds exactly off
the zeros of `H̃`, because at a zero `inversionSymbol z` is `H̃(z+1)/0`, whose value is Lean's `0`.
-/

#print axioms Hemigroup.SelfDecomposableExponent.mul_profile_eq_sum_of_isLocalOfOrder
#print axioms Hemigroup.SelfDecomposableExponent.mellin_profile_weight_eq_of_isLocalOfOrder
#print axioms Hemigroup.SelfDecomposableExponent.mellin_profile_shift_eq_of_isLocalOfOrder
#print axioms Hemigroup.SelfDecomposableExponent.realisesAction_sum_mellinEulerFactor
#print axioms Hemigroup.SelfDecomposableExponent.eventuallyEq_inversionSymbol_of_isLocalOfOrder
#print axioms Hemigroup.SelfDecomposableExponent.exists_symbol_eq_of_isLocalOfOrder

/-! ### `lem:local-polynomial-symbol` — the equivalence

The (⇐) direction on the profiles, and the bundle. `def:locality-pmp` tests locality on two
classes, so this direction had to be run twice; on the test functions it is
`isLocalOfOrderCore_of_symbol_eq`, and on the profiles it needed the engine (no integration by
parts) together with vertical integrability of `P·g̃`, which is the polynomial `Γ` decay above.

`nonempty_isLocalOfOrder_iff_symbol_eq` is a **bundle**, in the sense `thm:main-characterization`
and `thm:signaling-form` are: it necessarily depends on everything both halves do, so the per-half
lines remain the load-bearing ones. It also asserts *less* than the halves — the coefficient form
`c_j(x) = γ_j x^{j-1}` cannot be stated in an equivalence of this shape, and lives in
`exists_symbol_eq_of_isLocalOfOrder`. A17 throughout, through `inversionOperator` and `lawT₁`.
-/

#print axioms Hemigroup.SelfDecomposableExponent.eulerExpression
#print axioms Hemigroup.SelfDecomposableExponent.mellin_eulerExpression
#print axioms Hemigroup.SelfDecomposableExponent.verticalIntegrable_mellin_eulerExpression
#print axioms Hemigroup.SelfDecomposableExponent.inversionOperator_profile_eq_eulerExpression
#print axioms Hemigroup.SelfDecomposableExponent.isLocalOfOrder_of_symbol_eq
#print axioms Hemigroup.SelfDecomposableExponent.nonempty_isLocalOfOrder_iff_symbol_eq

/-! ### Chapter 10's setting: `X₀`, `T_r` and the core `𝒟`

Definitions and their elementary theory (`Hemigroup/DelayCore.lean`), listed here for the reason
`Hemigroup/Subordinator.lean`'s lemmas are: they are proved and in the library while their
consumer — `lem:delay-core`, still in `Skeleton/Chapter10.lean` — is not, so CI's sorry guard
cannot see them and this list is the only check that they are interface-free.

`memCore_iff_signaling_hypotheses` is the one worth reading. It is an `iff` between `f ∈ 𝒟` and
the six hypotheses `thm:signaling-form` takes about its signal, and it is what says the model of
`𝒟` chosen here supplies chapter 11's hypotheses rather than drifting from them — chapter 11 was
written taking those six directly, `𝒟` having no definition at the time.

Lean core throughout: nothing here mentions a hemigroup object. `abs_le` is the exception in
appearance only — it reuses `abs_primitive_le`, which sits in the `SelfDecomposableExponent`
namespace without taking an `F`.
-/

#print axioms Hemigroup.delay_eq_translate
#print axioms Hemigroup.HasCoreDeriv.causal
#print axioms Hemigroup.HasCoreDeriv.apply_zero
#print axioms Hemigroup.HasCoreDeriv.eq_intervalIntegral
#print axioms Hemigroup.HasCoreDeriv.continuous
#print axioms Hemigroup.HasCoreDeriv.measurable
#print axioms Hemigroup.HasCoreDeriv.abs_le
#print axioms Hemigroup.HasCoreDeriv.absolutelyContinuousOnInterval
#print axioms Hemigroup.memCore_iff_signaling_hypotheses
#print axioms Hemigroup.coreL1_subset_causalL1
#print axioms Hemigroup.causalL1_transL1

/-! ### `lem:delay-core`, the two invariance clauses

`𝒟` is invariant under `T_r` and under `Φ_{x,y}`, with the derivative tracked in each case —
`(T_r f)' = T_r f'` and `(μ ∗ f)' = μ ∗ f'`, which is what the blueprint's proof establishes and
what `def:phillips-generator` will consume. Stated for a causal probability measure, the level
`lem:convolution-representation` supplies `Φ` at.

`mconv_eq_setIntegral_mconv` is the analytic content and is worth its own line: it is
`delayedField_eq_setIntegral` for a general causal measure rather than for the law of `xT₁`, which
is the direction the chapter-11 lemma should have been stated in. Lean core throughout.
-/

#print axioms Hemigroup.setIntegral_Ioc_of_causal
#print axioms Hemigroup.measurable_mconv
#print axioms Hemigroup.mconv_eq_setIntegral_mconv
#print axioms Hemigroup.HasCoreDeriv.translate
#print axioms Hemigroup.HasCoreDeriv.conv
#print axioms Hemigroup.hasCoreDerivL1_transL1
#print axioms Hemigroup.hasCoreDerivL1_mconvL1
#print axioms Hemigroup.tendsto_norm_transL1_sub

/-! ### `lem:delay-core`, the two quantitative clauses

The difference quotient `h⁻¹(T_hf - f) → -f'` in `X₀`, and the estimate
`‖T_rf - f‖₁ ≤ min(2‖f‖₁, r‖f'‖₁)`. Both run on one pointwise identity,
`f(t) - f(t-r) = ∫₀^r f'(t-u)du`, and one exchange of integrals in `ℝ≥0∞`.

Two departures from the blueprint's route, neither changing the result. The estimate is reached
without an `X`-valued Bochner integral — `T_rf - f = -∫₀^r T_ρf' dρ` — because going through
`ℝ≥0∞` needs no integrability side condition. And the limit needs no separate treatment of the
interval `[0,h)`: `norm_differenceQuotient_le` says the quotient is an *average* of the
translation defects over `(0,h]`, so it cannot exceed their supremum, and `f(0) = 0` is used
once, inside `HasCoreDeriv`, to make the identity hold at all. Lean core throughout.
-/

#print axioms Hemigroup.norm_eq_lintegral_of_ae
#print axioms Hemigroup.HasCoreDeriv.sub_translate
#print axioms Hemigroup.HasCoreDeriv.enorm_sub_translate_le
#print axioms Hemigroup.HasCoreDeriv.enorm_differenceQuotient_le
#print axioms Hemigroup.lintegral_lintegral_enorm_translate
#print axioms Hemigroup.lintegral_lintegral_enorm_translate_sub
#print axioms Hemigroup.norm_transL1_sub_eq_lintegral
#print axioms Hemigroup.norm_transL1_sub_le
#print axioms Hemigroup.norm_differenceQuotient_le
#print axioms Hemigroup.tendsto_differenceQuotient

/-! ### `lem:delay-core` (10.1) — density, and the node

`𝒟` is dense in `X₀`. The blueprint says "standard", and the standard route is the wrong one:
step functions are dense in `X₀` and lie in `𝒟` nowhere, while Mathlib's smooth compactly
supported approximants are not causal. The mollification `ρ_ε * f` lands *in* `𝒟`, because
`approxId ε = ε⁻¹·1_{(0,ε)}` is carried by `[0,ε]` — chapter 4 built it that way for Prokhorov,
and causality is exactly what makes `ρ_ε * f` start at the origin.

`delay_core` is the node: a **bundle**, in the sense `thm:signaling-form` is, so the per-clause
lines above it are the load-bearing ones. It also states the invariance clauses in the
blueprint's weaker form (`T_r f ∈ 𝒟`) where the lemmas prove the tracked form
`(T_r f)' = T_r f'`. Lean core throughout — the whole of chapter 10's Lemma 10.1 is
interface-free.
-/

#print axioms Hemigroup.exists_causal_representative
#print axioms Hemigroup.setIntegral_Ioc_eq_zero_of_causal
#print axioms Hemigroup.setIntegral_Ioc_eq_intervalIntegral_of_causal
#print axioms Hemigroup.setIntegral_Ioc_differenceQuotient
#print axioms Hemigroup.hasCoreDerivL1_bconv_approxId
#print axioms Hemigroup.dense_coreL1
#print axioms Hemigroup.delay_core

/-! ### `Ein`, the entire exponential integral

Mathlib has no exponential integral of any kind — no `Ein`, no `Ei`, no `E₁` — so `ein` is
defined here, on the pattern `riemannLiouville` set in chapter 11. That adds a definition and no
interface: the article cites Caravenna–Sun–Zygouras for the Dickman subordinator's Lévy density
and transform, not for a theorem about `Ein`.

Note that `intervalIntegrable_einIntegrand` is stated on `z ≥ 0` and not on `ℝ`. The bound
`(1 - e^{-u})/u ≤ 1` is false to the left of the origin, where the integrand grows like
`e^{|u|}/|u|`; every use is at `z ≥ 0`, and the layer cake asks for exactly `∀ t > 0`.
-/

#print axioms Hemigroup.ein
#print axioms Hemigroup.einIntegrand_nonneg
#print axioms Hemigroup.einIntegrand_le_one
#print axioms Hemigroup.intervalIntegrable_einIntegrand

/-! ### `lem:admissible-cone` (7.13) and `lem:dickman-superposition` (7.14)

The two clauses of `prop:extreme-rays` that need neither uniqueness of the Lévy–Khintchine triple
nor a Choquet argument, split off and proved. Lean core throughout.

`ℝ≥0∞` is what makes the cone cheap, and it is worth a line: additivity of `levyJump` in `k` is a
statement about `lintegral`, so `lintegral_add_left'` needs only `AEMeasurable` of one summand and
no integrability side condition. The classical argument has to know both integrals are finite
first; here finiteness is the *conclusion*, which is exactly what `ne_top` asks for.

The superposition is Mathlib's layer cake for the third time in this development — the same
`lintegral_comp_eq_lintegral_meas_lt_mul` chapter 9's Route B ran on twice, with only the
antiderivative changed, from `1 - e^{-su}` to `Ein(su)`. It needs no σ-finiteness on `ρ`, which
matters: the tail measure of a bounded `k` puts infinite mass at the origin, and only its
restriction to `(0,∞)` is σ-finite.

`add` and `smul` are listed alongside the theorems for the reason `gammaExponent` and
`dickmanExponent` are: they carry proof obligations in their fields, and an interface leaking into
one would mean the witness is not a witness.
-/

#print axioms Hemigroup.levyJump_add
#print axioms Hemigroup.levyJump_smul
#print axioms Hemigroup.SelfDecomposableExponent.add
#print axioms Hemigroup.SelfDecomposableExponent.smul
#print axioms Hemigroup.SelfDecomposableExponent.exponent_add
#print axioms Hemigroup.SelfDecomposableExponent.exponent_smul
#print axioms Hemigroup.SelfDecomposableExponent.admissible_cone
#print axioms Hemigroup.dickmanExponent_exponent
#print axioms Hemigroup.SelfDecomposableExponent.exists_tailMeasure_k
#print axioms Hemigroup.SelfDecomposableExponent.exponent_eq_lintegral_ein
#print axioms Hemigroup.dickman_superposition
