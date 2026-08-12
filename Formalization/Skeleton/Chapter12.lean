/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.LocalOperator

/-!
# The target types of chapter 12

**This file carries a `sorry` and is not part of the `Hemigroup` library.**

## What is proved, and lives under `Hemigroup/`

| node | declaration | file |
|---|---|---|
| `lem:log-convexity` (12.4) | `convexOn_log_negMoment` | `Locality.lean` |
| `lem:symbol-vanishes-at-origin` (12.9) | `tendsto_inversionSymbol_nhdsGT_zero` | `Locality.lean` |
| `lem:gamma-recursion-uniqueness` (12.10) | `eq_gamma_form_of_logConvex_of_recursion` | `GammaRecursion.lean` |
| `def:locality-pmp` (12.1) | `IsLocalOfOrder`, `SatisfiesPMP` | `LocalOperator.lean` |
| `lem:local-polynomial-symbol` (⇐) | `isLocalOfOrder_of_symbol_eq` | `LocalOperator.lean` |
| — (its engine) | `mellin_pow_mul_iteratedDeriv` and inversion | `MellinEuler.lean` |

Everything that was stated here has moved except one thing.

## What is left: the (⇒) direction

`exists_symbol_eq_of_isLocalOfOrder` is the half that needs covariance. The blueprint gets the
homogeneous form of the coefficients by imposing `A Δ_σ = σ^{-1} Δ_σ A` on `∑ c_j(x) ∂_x^j` and
**comparing coefficients of `g^{(j)}(x/σ)`**. That comparison is the obligation: it says a
differential expression is determined by its coefficients, which in Lean means exhibiting, at each
point of `(0,∞)` and each order `j ≤ n`, a test function whose jet there is a prescribed vector.
Mathlib's bump functions give the ingredients; the construction is the work.

Nothing analytic remains beyond that. Once the coefficients are known to be `γ_j x^{j-1}`, the
symbol identity follows by running `isLocalOfOrder_of_symbol_eq`'s computation backwards through
`mellin_inversionOperator_eq` and injectivity of the Mellin transform on the line.
-/

namespace Hemigroup

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent)

/-- **`lem:local-polynomial-symbol`, the (⇒) direction.** Locality forces the symbol to be a
polynomial, and covariance forces the coefficients to be `γ_j x^{j-1}`.

Unlike the (⇐) direction this one is stated under (H), because the covariance argument runs
through `lem:mellin-data`, which needs it. -/
theorem exists_symbol_eq_of_isLocalOfOrder (hH : F.StandingHypothesis) {c : ℝ} (hc : 0 < c)
    (hc' : c < F.zStar - 1) {n : ℕ} (hL : F.IsLocalOfOrder c n) :
    ∃ γ : ℕ → ℂ, γ n ≠ 0 ∧
      (∀ j ∈ Finset.range (n + 1), ∀ x : ℝ, 0 < x →
        hL.coeff j x = γ j * (x : ℂ) ^ ((j : ℤ) - 1)) ∧
      (∀ z : ℂ, 0 < z.re → z.re < F.zStar - 1 →
        F.inversionSymbol z = ∑ j ∈ Finset.range (n + 1), γ j * mellinEulerFactor j z) := by
  sorry

end SelfDecomposableExponent

end Hemigroup
