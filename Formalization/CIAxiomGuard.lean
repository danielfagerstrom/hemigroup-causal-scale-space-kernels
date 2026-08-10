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
