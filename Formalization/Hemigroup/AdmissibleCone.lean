/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.Ein

/-!
# `lem:admissible-cone`: the admissible exponents form a convex cone

Blueprint: `lem:admissible-cone` (7.13), the clause of `prop:extreme-rays` that needs neither
uniqueness of the Lévy–Khintchine triple nor a Choquet argument.

The content is that all six fields of `SelfDecomposableExponent` are stable under addition and
under multiplication by a nonnegative scalar, and that the exponent transports: `F + G` has
exponent `F(s) + G(s)`, and `cF` has exponent `c·F(s)`. Five of the six fields are immediate;
`ne_top` is the one with content, and it is exactly the transport statement, since a sum of two
finite things is finite.

## `ℝ≥0∞` is what makes this cheap, and it is worth saying why

The exponent is `[0,∞]`-valued, so the additivity of `levyJump` in `k` is a statement about
`lintegral` with **no integrability side condition** — `lintegral_add_left'` needs only
`AEMeasurable` of one summand, which `aemeasurable_of_antitoneOn` supplies from `k_antitone`.
The classical argument would first have to know both integrals are finite; here finiteness is
the *conclusion*. Same economy as `Operator.lean`'s Tonelli identity, one chapter earlier.
-/

namespace Hemigroup

open MeasureTheory Set

open scoped ENNReal

variable {k₁ k₂ : ℝ → ℝ} {s c : ℝ}

/-- The jump part is additive in the density. -/
theorem levyJump_add (h₁ : AEMeasurable k₁ (volume.restrict (Ioi (0 : ℝ))))
    (h₁₀ : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ k₁ t) (h₂₀ : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ k₂ t) (hs : 0 ≤ s) :
    levyJump (k₁ + k₂) s = levyJump k₁ s + levyJump k₂ s := by
  rw [levyJump, levyJump, levyJump, ← lintegral_add_left' (aemeasurable_levyJump_integrand h₁ s)]
  refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu' : 0 < u := hu
  have hw : 0 ≤ 1 - Real.exp (-(s * u)) := by
    have h := Real.exp_le_one_iff.mpr (show -(s * u) ≤ 0 by nlinarith)
    linarith
  have hA : 0 ≤ (1 - Real.exp (-(s * u))) * k₁ u / u :=
    div_nonneg (mul_nonneg hw (h₁₀ u hu)) hu'.le
  have hB : 0 ≤ (1 - Real.exp (-(s * u))) * k₂ u / u :=
    div_nonneg (mul_nonneg hw (h₂₀ u hu)) hu'.le
  rw [← ENNReal.ofReal_add hA hB]
  congr 1
  simp only [Pi.add_apply]
  ring

/-- The jump part is homogeneous in the density, for a nonnegative scalar. -/
theorem levyJump_smul (hc : 0 ≤ c) (h₁₀ : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ k₁ t) (hs : 0 ≤ s) :
    levyJump (c • k₁) s = ENNReal.ofReal c * levyJump k₁ s := by
  rw [levyJump, levyJump, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu' : 0 < u := hu
  have hw : 0 ≤ 1 - Real.exp (-(s * u)) := by
    have h := Real.exp_le_one_iff.mpr (show -(s * u) ≤ 0 by nlinarith)
    linarith
  have hA : 0 ≤ (1 - Real.exp (-(s * u))) * k₁ u / u :=
    div_nonneg (mul_nonneg hw (h₁₀ u hu)) hu'.le
  rw [← ENNReal.ofReal_mul hc]
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

namespace SelfDecomposableExponent

variable (F G : SelfDecomposableExponent)

/-- **The sum of two admissible exponents**, with data `(b₀¹ + b₀², k₁ + k₂)`. -/
noncomputable def add : SelfDecomposableExponent where
  b₀ := F.b₀ + G.b₀
  k := F.k + G.k
  b₀_nonneg := add_nonneg F.b₀_nonneg G.b₀_nonneg
  k_nonneg := fun t ht => add_nonneg (F.k_nonneg t ht) (G.k_nonneg t ht)
  k_antitone := F.k_antitone.add G.k_antitone
  k_zero := by simp [F.k_zero, G.k_zero]
  ne_top := fun s hs => by
    rw [levyExponentD, levyJump_add (aemeasurable_of_antitoneOn F.k_antitone) F.k_nonneg
      G.k_nonneg hs, add_mul,
      ENNReal.ofReal_add (mul_nonneg F.b₀_nonneg hs) (mul_nonneg G.b₀_nonneg hs)]
    have h₁ := F.ne_top s hs
    have h₂ := G.ne_top s hs
    rw [levyExponentD] at h₁ h₂
    obtain ⟨ha₁, hb₁⟩ := ENNReal.add_ne_top.mp h₁
    obtain ⟨ha₂, hb₂⟩ := ENNReal.add_ne_top.mp h₂
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ha₁, ha₂⟩,
      ENNReal.add_ne_top.mpr ⟨hb₁, hb₂⟩⟩

/-- **A nonnegative multiple of an admissible exponent**, with data `(c b₀, c k)`. -/
noncomputable def smul (hc : 0 ≤ c) : SelfDecomposableExponent where
  b₀ := c * F.b₀
  k := c • F.k
  b₀_nonneg := mul_nonneg hc F.b₀_nonneg
  k_nonneg := fun t ht => by
    simpa using mul_nonneg hc (F.k_nonneg t ht)
  k_antitone := fun x hx y hy hxy => by
    simpa using mul_le_mul_of_nonneg_left (F.k_antitone hx hy hxy) hc
  k_zero := by simp [F.k_zero]
  ne_top := fun s hs => by
    rw [levyExponentD, levyJump_smul hc F.k_nonneg hs, mul_assoc,
      ENNReal.ofReal_mul hc]
    have h := F.ne_top s hs
    rw [levyExponentD] at h
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.mp h).1, ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.mp h).2⟩

@[simp] theorem add_b₀ : (F.add G).b₀ = F.b₀ + G.b₀ := rfl

@[simp] theorem add_k : (F.add G).k = F.k + G.k := rfl

@[simp] theorem smul_b₀ (hc : 0 ≤ c) : (F.smul hc).b₀ = c * F.b₀ := rfl

@[simp] theorem smul_k (hc : 0 ≤ c) : (F.smul hc).k = c • F.k := rfl

/-- **The exponent is additive**: `(F + G)(s) = F(s) + G(s)`. -/
theorem exponent_add (hs : 0 ≤ s) : (F.add G).exponent s = F.exponent s + G.exponent s := by
  simp only [exponent, add_b₀, add_k, levyExponentD]
  rw [levyJump_add (aemeasurable_of_antitoneOn F.k_antitone) F.k_nonneg G.k_nonneg hs, add_mul,
    ENNReal.ofReal_add (mul_nonneg F.b₀_nonneg hs) (mul_nonneg G.b₀_nonneg hs)]
  ring

/-- **The exponent is homogeneous**: `(cF)(s) = c·F(s)` for `c ≥ 0`. -/
theorem exponent_smul (hc : 0 ≤ c) (hs : 0 ≤ s) :
    (F.smul hc).exponent s = ENNReal.ofReal c * F.exponent s := by
  simp only [exponent, smul_b₀, smul_k, levyExponentD]
  rw [levyJump_smul hc F.k_nonneg hs, mul_assoc, ENNReal.ofReal_mul hc, mul_add]

/-- **`lem:admissible-cone` (7.13).** The admissible exponents are closed under addition and
under multiplication by a nonnegative scalar, and the correspondence with the data `(b₀, k)` is
linear — so they form a convex cone.

Stated existentially, as the skeleton stated it: what has to hold is that a sum *exists* with the
right data and the right exponent, not that it is built by any particular definition. -/
theorem admissible_cone (hc : 0 ≤ c) :
    (∃ H : SelfDecomposableExponent, H.b₀ = F.b₀ + G.b₀ ∧ H.k = F.k + G.k ∧
        ∀ s : ℝ, 0 ≤ s → H.exponent s = F.exponent s + G.exponent s) ∧
      (∃ H : SelfDecomposableExponent, H.b₀ = c * F.b₀ ∧ H.k = c • F.k ∧
        ∀ s : ℝ, 0 ≤ s → H.exponent s = ENNReal.ofReal c * F.exponent s) :=
  ⟨⟨F.add G, rfl, rfl, fun _ hs => F.exponent_add G hs⟩,
   ⟨F.smul hc, rfl, rfl, fun _ hs => F.exponent_smul hc hs⟩⟩

end SelfDecomposableExponent

end Hemigroup
