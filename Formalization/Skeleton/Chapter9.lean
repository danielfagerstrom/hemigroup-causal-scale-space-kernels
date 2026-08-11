/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.MemoryKernel

/-!
# The target types of chapter 9

**This file carries `sorry`s and is not part of the `Hemigroup` library.** Phase 2 of
`blueprint/PLAN-chapters-8-12.md`: state the chapter before proving it, so that the design
decisions are taken once, visibly, and the remaining work becomes countable rather than
estimated.

Writing these down has already earned its keep — three findings that a proof-first order would
have hit one at a time, halfway through:

**1. The vocabulary question is settled, and the design does not bend.** `HasCMRep` and
`HasStieltjesRep` in `Hemigroup/MemoryKernel.lean` state complete monotonicity and the Stieltjes
class as *representations*. `prop:pair-regularity`(2) is expressible with no new predicate. See
that file's docstring.

**2. Two statements here needed something the development did not have** — Laplace injectivity
for measures that are not finite, since `κ^{(x)}`, `ℓ^{(x)}` and Lebesgue measure are none of
them finite and `sonine_conservation` compares them. **Discharged 2026-08-11** as
`Hemigroup.laplaceL_injective_of_ne_top`, so ledger A6 stays off the trust boundary in its
general form too. Writing these statements is what showed it was a prerequisite rather than a
detail; the sharpening it produced — that the real hypothesis is convergence of the transform at
one point, not local finiteness — came out of trying to prove it.

**3. `lem:potential-kernel` is where a third trust-boundary entry would enter.** It asserts a
measure with a prescribed Laplace transform, which is Bernstein–Widder in its general
(locally finite) form — ledger A1. Unlike A17 and A18 this one is *not* forced yet: the function
whose transform is prescribed is `1/φ_x`, and the development might reach it through the
subordinator correspondence it already trusts. Deciding that is Phase 5 work, and the statement
below is deliberately written so either route can discharge it.
-/

namespace Skeleton

open MeasureTheory Set
open scoped ENNReal

open Hemigroup Hemigroup.SelfDecomposableExponent

variable (F : Hemigroup.SelfDecomposableExponent)

/-! ## `lem:memory-kernel`

The one statement in the chapter that needs no new machinery: differentiation under the integral
sign, which Mathlib has. The dominating function is `e^{-s₀t} k(t)`, integrable near `0` because
`∫₀¹ k < ∞` and at infinity because `k` is bounded there, being nonincreasing.
-/

/-- **`lem:memory-kernel`.** `F'(s) = b₀ + ∫₀^∞ e^{-st} k(t) dt`. -/
theorem hasDerivAt_toRealExponent {s : ℝ} (hs : 0 < s) :
    HasDerivAt F.toRealExponent
      (F.b₀ + ∫ t in Ioi (0 : ℝ), Real.exp (-(s * t)) * F.k t) s := by
  sorry

/-- The memory kernel's Laplace transform is the symbol divided by `s` — the first factor of the
Sonine identity. -/
theorem laplace_memoryKernel {x s : ℝ} (hx : 0 < x) (hs : 0 < s) :
    laplace (F.memoryKernel x) s = F.symbol x s / s := by
  sorry

/-! ## `lem:potential-kernel`

Existence *and* uniqueness of `ℓ^{(x)}`. Uniqueness is Laplace injectivity for locally finite
measures (see the module docstring); existence is the open question of the chapter.
-/

/-- **`lem:potential-kernel`.** The potential kernel exists, is unique, and scales. -/
theorem existsUnique_potentialKernel {x : ℝ} (hx : 0 < x) :
    ∃! ℓ : Measure ℝ, IsCausal ℓ ∧ (∀ T : ℝ, ℓ (Icc 0 T) ≠ ⊤) ∧
      ∀ s : ℝ, 0 < s → laplace ℓ s = (F.symbol x s)⁻¹ := by
  sorry

/-! ## `thm:sonine-conservation` and its corollary -/

/-- **`thm:sonine-conservation`.** `κ^{(x)} ∗ ℓ^{(x)} = Leb` on `[0,∞)`.

Stated against an arbitrary `ℓ` satisfying the potential-kernel specification rather than
against a chosen one, so that it does not depend on how `existsUnique_potentialKernel` is
discharged. -/
theorem sonine_conservation {x : ℝ} (hx : 0 < x) (ℓ : Measure ℝ) [SFinite ℓ]
    (hℓ : ∀ s : ℝ, 0 < s → laplace ℓ s = (F.symbol x s)⁻¹) :
    (F.memoryKernel x ∗ ℓ).restrict (Ici 0) = volume.restrict (Ici 0) := by
  sorry

/-- **`prop:sonine-pair-exists`**, the node split out in Phase 0: at the level of measures the
pair is unconditional. A collation of the three results above, and the reason it is worth
stating separately is that it needs no ledger entry, where the regularity clauses do. -/
theorem exists_sonine_pair {x : ℝ} (hx : 0 < x) :
    ∃ ℓ : Measure ℝ, IsCausal ℓ ∧ (∀ T : ℝ, ℓ (Icc 0 T) ≠ ⊤) ∧
      ∃ _ : SFinite ℓ, (F.memoryKernel x ∗ ℓ).restrict (Ici 0) = volume.restrict (Ici 0) := by
  sorry

/-! ## `prop:pair-regularity`(2), the Phase 1 decision made concrete

The statement that forced the vocabulary question. Note that no predicate `CompletelyMonotone`
appears: `HasCMRep` and `HasStieltjesRep` are representations, and the equivalence below is
therefore statable in the development's existing idiom.

Crossing to the blueprint's derivative-sign reading of the same classes costs ledger **A1**,
once, in the statement — never inside a proof. That is the discipline `prop:bernstein-toolbox`(3)
already documents for `BF₀` against `LE`.
-/

/-- **`prop:pair-regularity`(2).** `κ^{(x)}` has a completely monotone density iff `k` does,
iff `F'` is Stieltjes. -/
theorem hasCMDensity_iff {x : ℝ} (hx : 0 < x) :
    (HasCMDensity (F.memoryKernel x) ↔ HasCMRep F.k) ∧
      (HasCMRep F.k ↔ HasStieltjesRep (deriv F.toRealExponent)) := by
  sorry

end Skeleton
