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
| `def:locality-pmp` (12.1) | `IsLocalOfOrderCore`, `IsLocalOfOrder`, `SatisfiesPMP` | `LocalOperator.lean` |
| `lem:local-polynomial-symbol` (⇐) | `isLocalOfOrderCore_of_symbol_eq` | `LocalOperator.lean` |
| — (its engine) | `mellin_pow_mul_iteratedDeriv` and inversion | `MellinEuler.lean` |

Everything that was stated here has moved except one thing.

## Why the definition was widened

Formalising the (⇒) direction showed that the blueprint's "Mellin-transforming on a line and using
injectivity gives `B = P`" hides a real step. What that argument delivers is that `B·ĝ` and `P·ĝ`
have the same inverse transform, for every *test function* `g`. `P·ĝ` is vertically integrable ---
`E_j(z)·ĝ(z)` is itself the transform of a test function, `x^j g^{(j)}`, so
`verticalIntegrable_mellin` already covers it. But **`B·ĝ` need not be**: `B = H̃(z+1)/H̃(z)`
carries no growth bound, which is exactly why chapter 11 carries integrability as a *field* of
`RealisesAction` rather than deriving it. So the comparison has to be routed through the one class
where `B`'s behaviour is known --- `lem:symbol-uniqueness`'s profiles `H(s·)` --- and those are
not test functions, being neither compactly supported nor supported away from the origin.

The definition therefore now tests locality on the profiles too, so that 12.2 and
`lem:symbol-uniqueness` speak about the same objects. The two clauses are separate structures
because they cost differently: `IsLocalOfOrderCore` is the `C_c^∞` clause, which a polynomial
symbol supplies cheaply and which `isLocalOfOrderCore_of_symbol_eq` proves; `IsLocalOfOrder`
extends it with the profile clause, true for the same reason but by a different computation
(`∂ₓ^j H(sx) = ∫ (-st)^j e^{-sxt} dμ(t)`, then `lem:mellin-data`'s Gamma-integral hinge), which
needs differentiation under the integral sign `j` times and is not yet formalised.

## What is left: one clause of the (⇒) direction

`exists_symbol_eq_of_isLocalOfOrder` has three conclusions and **two of them are proved**. That
`γ n ≠ 0` and that `c_j(x) = γ_j x^{j-1}` both come from `coeff_eq_of_isLocalOfOrder`, which is the
blueprint's covariance argument and needs only the core clause: apply locality to `Δ_σ g` at the
point `σ`, apply `inversionOperator_lineDilate` to the same thing, and feed both a test function
whose jet at `1` is a basis vector. The sums collapse and `c_m(σ) σ^{-m} = σ^{-1} c_m(1)` falls
out. Evaluating at `x = σ` is what makes one jet, at the single point `1`, settle every `σ`.

The `sorry` is the third clause, and it is now unblocked rather than merely deferred: with the
profile clause in hand, `A(H(s·))` has two readings --- `lem:symbol-uniqueness`'s eigenfunction
relation and the differential expression --- and equating them puts `P` in the position
`eventuallyEq_inversionSymbol_of_realisesAction` requires.

### The one remaining obligation, and its route

`MellinEuler.lean`'s engine on the profile class:
`M[x ↦ xʲ ∂ₓʲ H(sx)](w) = E_j(w) · M[H(s·)](w)`. It does **not** need the integration by parts
that the test-function case used --- the profiles are not compactly supported and the boundary
terms would have to be argued --- because `ProfileDeriv.lean` has already turned the derivative
into an integral. What is left is a computation in three moves.

1. **The weight is a Mellin shift.** `mellin_cpow_smul` gives
   `M[x ↦ xʲ f(x)](w) = M[f](w + j)`, so the `xʲ` disappears into the argument and never has to
   be carried through a Fubini.
2. **The dilation is a factor.** `mellin_comp_mul_left`, already used in chapter 11 as
   `mellin_profile_comp_mul`.
3. **What is left is chapter 11's own hinge with one extra factor.** After 1 and 2 the target is
   `M[x ↦ ∫ tʲ e^{-xt} dμ(t)](z) = Γ(z) ∫ t^{j-z} dμ(t)`, which is `mellin_profile` with `μ`
   replaced by `tʲ μ(dt)`. The pointwise inner computation is `lintegral_ofReal_rpow_mul_exp`,
   which is *already stated for arbitrary `t > 0`* and needs no change; only the outer step of
   `lintegral_lintegral_gamma`, and the Bochner-side integrability of `mellin_profile`, are
   specific to `lawT₁` and have to be generalised to a weighted measure.

Then `E_j(w) = (-1)^j Γ(w+j)/Γ(w)` matches `mellinEulerFactor` by `Gamma_add_one` `j` times.
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
    rw [F.coeff_eq_of_isLocalOfOrder hL.toIsLocalOfOrderCore le_rfl hx₀, show hL.coeff n 1 = 0 from h, zero_mul]
  · -- covariance, which is `coeff_eq_of_isLocalOfOrder`
    intro j hj x hx
    exact F.coeff_eq_of_isLocalOfOrder hL.toIsLocalOfOrderCore (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hx
  · -- the symbol identity: all that is left
    sorry

end SelfDecomposableExponent

end Hemigroup
