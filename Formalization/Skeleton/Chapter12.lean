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

## What is left: one clause of the (⇒) direction

`exists_symbol_eq_of_isLocalOfOrder` has three conclusions and **two of them are proved**. That
`γ n ≠ 0` and that `c_j(x) = γ_j x^{j-1}` both come from `coeff_eq_of_isLocalOfOrder`, which is the
blueprint's covariance argument: apply locality to `Δ_σ g` at the point `σ`, apply
`inversionOperator_lineDilate` to the same thing, and feed both a test function whose jet at `1`
is a basis vector. The sums collapse and `c_m(σ) σ^{-m} = σ^{-1} c_m(1)` falls out. Evaluating at
`x = σ` is what makes one jet, at the single point `1`, settle every `σ` at once.

The `sorry` is the third clause alone: that the symbol is then the corresponding polynomial,
`B(z) = ∑ γ_j E_j(z)`. **The blueprint disposes of it in half a sentence — "Mellin-transforming on
a line and using injectivity gives `B = P`" — and that sentence hides a real step.**

What the argument gives is that `B·ĝ` and `P·ĝ` have the same inverse transform on `(0,∞)`, for
every *test function* `g`. Two obstacles stand between that and `B = P`, and only the first is a
Lean matter.

1. Concluding `B·ĝ = P·ĝ` on the line needs the forward-after-inverse direction of Mellin
   inversion, and **Mathlib has only the inverse-after-forward direction**
   (`mellinInv_mellin_eq`). It does have the missing direction for *Fourier*
   (`Continuous.fourier_fourierInv_eq`), and `mellin_eq_fourier` / `mellinInv_eq_fourierInv` are
   the bridge, so this is plumbing rather than mathematics — but it is plumbing Mathlib does not
   carry.

2. The deeper one. `P·ĝ` is vertically integrable, because `E_j(z)·ĝ(z)` is itself the transform
   of a test function (`x^j g^{(j)}`) and so `verticalIntegrable_mellin` already covers it --- no
   sharpening needed. But **`B·ĝ` need not be**: `B = H̃(z+1)/H̃(z)` carries no a priori growth
   bound, which is exactly why chapter 11 carries integrability as a *field* of `RealisesAction`
   rather than deriving it. So the two inverse transforms are not automatically comparable, and
   the identity has to be routed through the class where `B`'s behaviour is known --- the profiles
   `H(s·)`, which are **not test functions**, being neither compactly supported nor supported away
   from the origin.

So `lem:symbol-uniqueness` does not apply off the shelf: it asks for a symbol realising the action
on profiles, and locality gives information only on test functions. Getting from one class to the
other is an approximation argument that the paper does not make. That is a finding about the
article rather than about the formalisation, and it is recorded in the node.
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
  refine ⟨fun j => hL.coeff j 1, ?_, ?_, ?_⟩
  · -- the leading coefficient is nonzero at `1` because it is nonzero somewhere
    obtain ⟨x₀, hx₀, hne⟩ := hL.leading_ne_zero
    intro h
    refine hne ?_
    rw [F.coeff_eq_of_isLocalOfOrder hL le_rfl hx₀, show hL.coeff n 1 = 0 from h, zero_mul]
  · -- covariance, which is `coeff_eq_of_isLocalOfOrder`
    intro j hj x hx
    exact F.coeff_eq_of_isLocalOfOrder hL (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hx
  · -- the symbol identity: all that is left
    sorry

end SelfDecomposableExponent

end Hemigroup
