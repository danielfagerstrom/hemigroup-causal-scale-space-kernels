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
#print axioms Hemigroup.SelfDecomposableExponent.Ioo_subset_integrableExpSet
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
-/

#print axioms Hemigroup.SelfDecomposableExponent.IsLocalOfOrderCore
#print axioms Hemigroup.SelfDecomposableExponent.IsLocalOfOrder
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
