/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.Covariance

/-!
# The target types of `lem:action-rigidity` and `prop:canonical-gauge`

**This file carries `sorry`s and is not part of the `Hemigroup` library.** It states what the two
remaining nodes of Chapter 6 *are*, so that they can be `\notready` rather than untagged. When a
proof lands, its declaration moves into `Hemigroup/`.

## What is already proved, in `Hemigroup/Covariance.lean`

Three of `lem:action-rigidity`'s four clauses, and the identity they all run on:

* `CascadeCore.G_scale` — `(6.1)`, `G(S_σ x, s) = G(x, σ s)`, together with its measure and
  exponent forms (`repr_map_const_mul`, `exponent_scale`), i.e. all of
  `lem:covariance-laplace`.
* `CascadeCore.eq_of_G_eq` — clause (1): `G(\cdot, s)` is injective, so `(6.1)` *determines*
  `S_σ`.
* `CascadeCore.S_comp`, `CascadeCore.S_one` — clause (2), the group law.
* `CascadeCore.eq_zero_of_fixed` — clause (4), no fixed point in `(0,∞)`.
* `CascadeCore.exponent_strictMonoOn_right` — strict monotonicity in `s`, which the blueprint
  takes from the sign of a Bernstein function's derivative and which is proved here instead
  from the support of `e^{-st} - e^{-s't}`. Clause (3) needs it and nothing else did.

## What the `sorry`s stand for

**Clause (3)**, continuity of `σ ↦ S_σ x`. Strict monotonicity is immediate from the two
monotonicity results above; continuity is the blueprint's inverse-function step, and the shape
it will take in Lean is `Set.invFunOn (G(\cdot, s₀)) (Ici 0)` composed with `σ ↦ G(x, σ s₀)`,
continuous at each interior point by `StrictMonoOn.continuousAt_of_image_mem_nhds`. The
hypothesis that lemma asks for — that the range of `G(\cdot, s₀)` is a neighbourhood of
`G(x, σ₀ s₀)` — is where `(6.1)` is spent a second time: the range contains `G(x, r)` for every
`r > 0`, hence points on both sides, and it is an interval because `Ici 0` is connected.

**`prop:canonical-gauge`**, stated as the existence of the gauge together with everything
downstream needs of it. Bundling the conjugation `χ(S_σ x) = σ χ(x)` and the similarity form
into the same statement is deliberate: `prop:main-uniqueness` declined to guess at that
interface, and this is where it gets fixed.
-/

namespace Skeleton

open MeasureTheory Set

open Hemigroup

/-- **`lem:action-rigidity`**, all four clauses. Clauses (1), (2) and (4) are already proved in
`Hemigroup/Covariance.lean`; what this statement adds is (3). -/
theorem action_rigidity (Fam : CascadeCore) {S : ℝ → ℝ → ℝ}
    (hcov : IsScaleCovariant Fam (Ioi 0) S) :
    (∀ (a b s : ℝ), 0 ≤ a → 0 ≤ b → 0 < s → Fam.G a s = Fam.G b s → a = b) ∧
      (∀ σ τ x : ℝ, 0 < σ → 0 < τ → 0 ≤ x → S σ (S τ x) = S (σ * τ) x) ∧
      (∀ x : ℝ, 0 ≤ x → S 1 x = x) ∧
      (∀ x : ℝ, 0 < x → ContinuousOn (fun σ => S σ x) (Ioi 0) ∧
        StrictMonoOn (fun σ => S σ x) (Ioi 0)) ∧
      (∀ x : ℝ, 0 ≤ x → (∀ σ : ℝ, 0 < σ → S σ x = x) → x = 0) := by
  sorry

/-- **`prop:canonical-gauge`**: the orbit coordinate, bundled with the two things every
consumer needs — the conjugation, and the similarity form `G(x, s) = F(χ(x) s)` with
`F = G(1, \cdot)`.

`F`'s membership in `LE` is not asserted here because it is not new: `F = g_{0,1}` and
`thm:increments-bernstein` already gives it. -/
theorem exists_canonical_gauge (Fam : CascadeCore) {S : ℝ → ℝ → ℝ}
    (hcov : IsScaleCovariant Fam (Ioi 0) S) :
    ∃ χ : ℝ → ℝ, χ 0 = 0 ∧ StrictMonoOn χ (Ici 0) ∧ SurjOn χ (Ici 0) (Ici 0) ∧
      (∀ σ x : ℝ, 0 < σ → 0 ≤ x → χ (S σ x) = σ * χ x) ∧
      (∀ x s : ℝ, 0 ≤ x → 0 ≤ s → Fam.G x s = Fam.G 1 (χ x * s)) := by
  sorry

end Skeleton
