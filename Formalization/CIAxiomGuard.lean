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
constructive direction only.
-/

-- Deliberately no `open Hemigroup`: the guard compares the printed axiom names against
-- `blueprint/trust-boundary.txt` by exact string match, and opening the namespace would
-- abbreviate them, so every interface axiom would read as undeclared.

/-! ### `lem:vanishing` -/

#print axioms Hemigroup.levyExponent_eq_zero_of_eq_zero

/-! ### `def:cascade-family`

The structure carries no proof obligations of its own; what has to hold is that the constructed
kernels satisfy it. A17 enters here, and only here.
-/

#print axioms Hemigroup.SelfDecomposableExponent.cascadeFamily

/-! ### `lem:convolution-representation` -/

#print axioms Hemigroup.CascadeFamily.existsUnique_repr
#print axioms Hemigroup.mconvL1_satisfies_axioms
