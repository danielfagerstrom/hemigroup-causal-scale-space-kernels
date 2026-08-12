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
