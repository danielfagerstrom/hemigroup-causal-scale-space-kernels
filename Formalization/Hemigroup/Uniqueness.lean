/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Hemigroup.Continuity

/-!
# Uniqueness of the pair `(χ, F)`

The last clause of `thm:main-characterization`: the gauge and the exponent are determined by the
family, once `χ` is normalised by `χ(1) = 1`.

## Why `χ` is a hypothesis and not a structure

The blueprint's `χ` is produced by `prop:canonical-gauge` out of the scaling action, and in that
role it has to be an increasing bijection of `[0,∞)` with an inverse, conjugating the action into
multiplication. None of that is needed *here*. The uniqueness clause only ever **quantifies
over** gauges, so `χ` can enter as a bare function `ℝ → ℝ` carrying exactly the three properties
the argument consumes —

* `hmono`  it is nondecreasing on `(0,∞)`;
* `hpos`   it is positive there, so that `χ x` is a legal kernel index;
* `hzero`  `χ(0+) = 0`, in the elementary form "it gets below every `ε`";

plus the normalisation `χ(1) = 1`. It leaves the argument as the identity. Bundling `χ` with an
inverse and a conjugated action is what the *analysis* direction will need, and that interface is
better designed against its consumer than guessed at now.

## The argument

Everything rests on the two facts already proved, and adds no analysis:

1. Equal kernels have equal increments — `laplace_kernel` plus injectivity of `exp`.
2. `increment_toReal` turns increments into differences of exponents, so the hypothesis reads
   `F'(χ(y)s) - F'(χ(x)s) = F(ys) - F(xs)`.
3. Letting `x ↓ 0` kills both subtrahends, because `F(0+) = 0` — `exists_exponent_lt`, the same
   fact tightness ran on. That gives `F'(χ(y)s) = F(ys)`, and at `y = 1` with `χ(1) = 1`,
   `F' = F`.
4. Feeding that back, `F(χ(y)s) = F(ys)`; at `s = 1`, strict monotonicity of `F`
   (`exponent_strictMono`) forces `χ(y) = y`.

Step 3 is run as an `ε` argument rather than a limit: `exists_exponent_lt` is already the
non-sequential form, so no filter machinery is needed and the two subtrahends are bounded
simultaneously by choosing one small `u` below three thresholds.

Everything here is Lean core.
-/

namespace Hemigroup

open MeasureTheory Set
open scoped ENNReal

namespace SelfDecomposableExponent

variable {F F' : SelfDecomposableExponent} {χ : ℝ → ℝ} {x y s : ℝ}

/-- **Equal kernels have equal increments.** The transform determines the exponent, since `exp`
is injective and both increments are finite. -/
theorem increment_toReal_eq_of_kernel_eq
    (hpos : ∀ u : ℝ, 0 < u → 0 < χ u)
    (hmono : ∀ ⦃u v : ℝ⦄, 0 < u → u ≤ v → χ u ≤ χ v)
    (heq : F'.kernel (χ x) (χ y) = F.kernel x y)
    (hx : 0 < x) (hxy : x ≤ y) (hs : 0 ≤ s) :
    (F'.increment (χ x) (χ y) s).toReal = (F.increment x y s).toReal := by
  have h1 := laplace_kernel (F := F') (hpos x hx).le (hmono hx hxy) hs
  rw [heq, laplace_kernel (F := F) hx.le hxy hs] at h1
  exact (neg_inj.mp (Real.exp_eq_exp.mp h1)).symm

/-- **The exponents agree along the gauge.** If the gauged family `μ'_{χ(x),χ(y)}` is the family
`μ_{x,y}`, then `F'(χ(y)s) = F(ys)`.

This is where `F(0+) = 0` is spent: the hypothesis only ever gives *differences* of exponents,
and the constant is pinned by pushing the lower index to the origin. -/
theorem exponent_eq_of_kernel_eq
    (hpos : ∀ u : ℝ, 0 < u → 0 < χ u)
    (hmono : ∀ ⦃u v : ℝ⦄, 0 < u → u ≤ v → χ u ≤ χ v)
    (hzero : ∀ ε : ℝ, 0 < ε → ∃ u : ℝ, 0 < u ∧ χ u < ε)
    (heq : ∀ u v : ℝ, 0 < u → u ≤ v → F'.kernel (χ u) (χ v) = F.kernel u v)
    (hy : 0 < y) (hs : 0 ≤ s) :
    F'.exponent (χ y * s) = F.exponent (y * s) := by
  rcases hs.eq_or_lt with rfl | hs'
  · simp [exponent, levyExponentD, levyJump]
  have hsne : s ≠ 0 := hs'.ne'
  have hfin1 : F'.exponent (χ y * s) ≠ ⊤ := F'.ne_top _ (mul_nonneg (hpos y hy).le hs)
  have hfin2 : F.exponent (y * s) ≠ ⊤ := F.ne_top _ (mul_nonneg hy.le hs)
  refine (ENNReal.toReal_eq_toReal_iff' hfin1 hfin2).mp ?_
  -- The difference at `y` equals the difference at any smaller `u`: the increments cancel.
  have key : ∀ u : ℝ, 0 < u → u ≤ y →
      (F'.exponent (χ y * s)).toReal - (F.exponent (y * s)).toReal
        = (F'.exponent (χ u * s)).toReal - (F.exponent (u * s)).toReal := by
    intro u hu huy
    have hA := increment_toReal_eq_of_kernel_eq (F := F) (F' := F') hpos hmono
      (heq u y hu huy) hu huy hs
    rw [increment_toReal (hpos u hu).le (hmono hu huy) hs, increment_toReal hu.le huy hs] at hA
    linarith
  -- Both subtrahends can be made arbitrarily small, so the difference is `0`.
  have hsmall : ∀ ε : ℝ, 0 < ε →
      |(F'.exponent (χ y * s)).toReal - (F.exponent (y * s)).toReal| < ε := by
    intro ε hε
    obtain ⟨r, hr0, hrlt⟩ := exists_exponent_lt F (ε := ENNReal.ofReal (ε / 2))
      (by simp only [ENNReal.ofReal_pos]; linarith)
    obtain ⟨r', hr'0, hr'lt⟩ := exists_exponent_lt F' (ε := ENNReal.ofReal (ε / 2))
      (by simp only [ENNReal.ofReal_pos]; linarith)
    have hrR : (F.exponent r).toReal < ε / 2 := by
      have h := (ENNReal.toReal_lt_toReal (F.ne_top r hr0.le) ENNReal.ofReal_ne_top).mpr hrlt
      rwa [ENNReal.toReal_ofReal (by linarith)] at h
    have hr'R : (F'.exponent r').toReal < ε / 2 := by
      have h := (ENNReal.toReal_lt_toReal (F'.ne_top r' hr'0.le) ENNReal.ofReal_ne_top).mpr hr'lt
      rwa [ENNReal.toReal_ofReal (by linarith)] at h
    obtain ⟨x₀, hx₀0, hx₀⟩ := hzero (r' / s) (div_pos hr'0 hs')
    -- One `u` below all three thresholds: `y`, `r/s`, and `x₀`.
    obtain ⟨u, hu0, huy, hur', hux⟩ :
        ∃ u : ℝ, 0 < u ∧ u ≤ y ∧ u ≤ r / s ∧ u ≤ x₀ :=
      ⟨min y (min (r / s) x₀), lt_min hy (lt_min (div_pos hr0 hs') hx₀0), min_le_left _ _,
        (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
    have hur : u * s ≤ r := by
      have h := mul_le_mul_of_nonneg_right hur' hs'.le
      rwa [div_mul_cancel₀ _ hsne] at h
    have hχu : χ u * s < r' := by
      have hlt : χ u < r' / s := lt_of_le_of_lt (hmono hu0 hux) hx₀
      have h := mul_lt_mul_of_pos_right hlt hs'
      rwa [div_mul_cancel₀ _ hsne] at h
    have hb1 : (F.exponent (u * s)).toReal < ε / 2 :=
      lt_of_le_of_lt (ENNReal.toReal_mono (F.ne_top r hr0.le)
        (exponent_mono F (mul_pos hu0 hs') hur)) hrR
    have hb2 : (F'.exponent (χ u * s)).toReal < ε / 2 :=
      lt_of_le_of_lt (ENNReal.toReal_mono (F'.ne_top r' hr'0.le)
        (exponent_mono F' (mul_pos (hpos u hu0) hs') hχu.le)) hr'R
    have h1 : 0 ≤ (F'.exponent (χ u * s)).toReal := ENNReal.toReal_nonneg
    have h2 : 0 ≤ (F.exponent (u * s)).toReal := ENNReal.toReal_nonneg
    rw [key u hu0 huy, abs_lt]
    constructor <;> linarith
  by_contra hne
  exact absurd (hsmall _ (abs_pos.mpr (sub_ne_zero_of_ne hne))) (lt_irrefl _)

/-- **The exponent is determined**: with `χ(1) = 1`, the gauge drops out at `y = 1` and `F' = F`
as functions on `[0,∞)`.

`SelfDecomposableExponent` is data — a drift and a density — and two different records can carry
the same exponent, differing on a null set. So the conclusion is stated at the level of
`exponent`, which is the object the theorem is about. -/
theorem exponent_eq_of_kernel_eq_of_map_one
    (hpos : ∀ u : ℝ, 0 < u → 0 < χ u)
    (hmono : ∀ ⦃u v : ℝ⦄, 0 < u → u ≤ v → χ u ≤ χ v)
    (hzero : ∀ ε : ℝ, 0 < ε → ∃ u : ℝ, 0 < u ∧ χ u < ε)
    (heq : ∀ u v : ℝ, 0 < u → u ≤ v → F'.kernel (χ u) (χ v) = F.kernel u v)
    (hχ1 : χ 1 = 1) {t : ℝ} (ht : 0 ≤ t) :
    F'.exponent t = F.exponent t := by
  have h := exponent_eq_of_kernel_eq (F := F) (F' := F') (y := (1 : ℝ)) (s := t)
    hpos hmono hzero heq one_pos ht
  rwa [hχ1, one_mul] at h

/-- **The gauge is determined**: it is the identity.

Having `F' = F`, the hypothesis reads `F(χ(y)s) = F(ys)`; at `s = 1` strict monotonicity of `F`
— which is exactly `F ≢ 0`, the theorem's nondegeneracy — leaves no room between `χ(y)` and
`y`. -/
theorem gauge_eq_self
    (hpos : ∀ u : ℝ, 0 < u → 0 < χ u)
    (hmono : ∀ ⦃u v : ℝ⦄, 0 < u → u ≤ v → χ u ≤ χ v)
    (hzero : ∀ ε : ℝ, 0 < ε → ∃ u : ℝ, 0 < u ∧ χ u < ε)
    (heq : ∀ u v : ℝ, 0 < u → u ≤ v → F'.kernel (χ u) (χ v) = F.kernel u v)
    (hχ1 : χ 1 = 1) (hne : ∃ s₀, 0 < s₀ ∧ F.exponent s₀ ≠ 0)
    (hy : 0 < y) : χ y = y := by
  have hkey : F.exponent (χ y) = F.exponent y := by
    have h := exponent_eq_of_kernel_eq (F := F) (F' := F') (s := (1 : ℝ))
      hpos hmono hzero heq hy zero_le_one
    rw [mul_one, mul_one] at h
    rwa [exponent_eq_of_kernel_eq_of_map_one hpos hmono hzero heq hχ1
      (hpos y hy).le] at h
  rcases lt_trichotomy (χ y) y with hlt | h | hgt
  · exact absurd hkey (ne_of_lt (exponent_strictMono F hne (hpos y hy) hlt))
  · exact h
  · exact absurd hkey.symm (ne_of_lt (exponent_strictMono F hne hy hgt))

/-- **The uniqueness clause of `thm:main-characterization`.**

If a gauge `χ`, normalised by `χ(1) = 1`, and an exponent `F'` reproduce the kernel family of a
nondegenerate `F`, then `χ` is the identity and `F'` has the same exponent as `F`.

The theorem's clause reads "the pair `(χ, F)` is unique up to the normalization `χ(1) = 1`";
this is that statement for the constructed family, with `χ` quantified over rather than
modelled. -/
theorem gauge_and_exponent_unique
    (hpos : ∀ u : ℝ, 0 < u → 0 < χ u)
    (hmono : ∀ ⦃u v : ℝ⦄, 0 < u → u ≤ v → χ u ≤ χ v)
    (hzero : ∀ ε : ℝ, 0 < ε → ∃ u : ℝ, 0 < u ∧ χ u < ε)
    (heq : ∀ u v : ℝ, 0 < u → u ≤ v → F'.kernel (χ u) (χ v) = F.kernel u v)
    (hχ1 : χ 1 = 1) (hne : ∃ s₀, 0 < s₀ ∧ F.exponent s₀ ≠ 0) :
    (∀ u : ℝ, 0 < u → χ u = u) ∧ (∀ t : ℝ, 0 ≤ t → F'.exponent t = F.exponent t) :=
  ⟨fun _ hu => gauge_eq_self hpos hmono hzero heq hχ1 hne hu,
    fun _ ht => exponent_eq_of_kernel_eq_of_map_one hpos hmono hzero heq hχ1 ht⟩

end SelfDecomposableExponent

end Hemigroup
