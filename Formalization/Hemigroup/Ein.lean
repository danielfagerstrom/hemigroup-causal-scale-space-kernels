/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.Examples

/-!
# `Ein`, the entire exponential integral

Blueprint: the function named in `prop:extreme-rays` and `lem:dickman-superposition`,
`Ein(z) = ∫₀^z (1 - e^{-u})/u du`.

**Mathlib has no exponential integral of any kind** — no `Ein`, no `Ei`, no `E₁`; `Analysis/`
carries `Gamma`, `Beta`, `Zeta`, `Polylog` and nothing of this family. So `ein` is *defined* here,
on the pattern `riemannLiouville` set in chapter 11: the article cites Caravenna–Sun–Zygouras for
the Dickman subordinator's Lévy density and transform, not for any theorem about `Ein`, so this
adds a definition and no interface.

## Why the integrand needs no guard at the origin

`(1 - e^{-u})/u` extends continuously by `1` at `u = 0`, and Lean's `x / 0 = 0` gives it the value
`0` there instead. That is a discontinuity on a null set and no integral sees it, so no `if 0 < u`
guard is carried — unlike `SelfDecomposableExponent.k`, where the guard is load-bearing because
`k 0` is a *field* the structure constrains. The bound `0 ≤ (1 - e^{-u})/u ≤ 1` on `(0,∞)` is what
every estimate below reduces to, and it is `one_sub_exp_neg_le` divided by `u`.
-/

namespace Hemigroup

open MeasureTheory Set

open scoped ENNReal

/-- The integrand of `Ein`: `(1 - e^{-u})/u`, extended by Lean's `x / 0 = 0` at the origin. -/
noncomputable def einIntegrand (u : ℝ) : ℝ := (1 - Real.exp (-u)) / u

/-- **`Ein(z) = ∫₀^z (1 - e^{-u})/u du`.**

Total in `z`: for `z ≤ 0` the interval integral is `≤ 0`-oriented and the value is what the
orientation gives, which the article never asks about — every use is at `z ≥ 0`. -/
noncomputable def ein (z : ℝ) : ℝ := ∫ u in (0 : ℝ)..z, einIntegrand u

theorem einIntegrand_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ einIntegrand u := by
  have h : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  exact div_nonneg (by linarith) hu

/-- `(1 - e^{-u})/u ≤ 1`: the estimate every bound below reduces to, and `one_sub_exp_neg_le`
divided by `u`. -/
theorem einIntegrand_le_one {u : ℝ} (hu : 0 ≤ u) : einIntegrand u ≤ 1 := by
  rcases hu.eq_or_lt with rfl | hu'
  · simp [einIntegrand]
  · rw [einIntegrand, div_le_one hu']
    exact one_sub_exp_neg_le u

theorem measurable_einIntegrand : Measurable einIntegrand := by
  unfold einIntegrand
  fun_prop

/-- The integrand is interval-integrable on `[0,z]` for `z ≥ 0`: measurable, and bounded by `1`.

Stated on the right half-line and not on all of `ℝ`, because the bound is false to the left of the
origin — `(1 - e^{-u})/u` grows like `e^{|u|}/|u|` there. Every use is at `z ≥ 0`, and the layer
cake below asks for exactly `∀ t > 0`. -/
theorem intervalIntegrable_einIntegrand {z : ℝ} (hz : 0 ≤ z) :
    IntervalIntegrable einIntegrand volume 0 z := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hz]
  have hfin : volume (Ioc (0 : ℝ) z) ≠ ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  refine Integrable.mono' (g := fun _ : ℝ => (1 : ℝ)) (integrableOn_const (hs := hfin))
    measurable_einIntegrand.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (.of_forall fun u hu => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (einIntegrand_nonneg hu.1.le)]
  exact einIntegrand_le_one hu.1.le

/-! ## The dilated integrand

`(1 - e^{-su})/u` is the Lévy integrand of the Dickman ray at rate `s`, and it is `s` times
`einIntegrand (su)`. That single line is the whole of `lem:dickman-superposition`(1): the
substitution `u ↦ su` turns `∫₀^τ (1 - e^{-st})\,dt/t` into `Ein(sτ)`.
-/

/-- `(1 - e^{-su})/u = s · einIntegrand(su)`, at every real `s` and `u`.

No hypothesis, and the two degenerate cases are why: at `u = 0` both sides are `0/0 = 0` in
Lean's convention, and at `s = 0` both are `0`. -/
theorem dilate_einIntegrand (s u : ℝ) :
    (1 - Real.exp (-(s * u))) / u = s * einIntegrand (s * u) := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp [einIntegrand]
  rcases eq_or_ne u 0 with rfl | hu
  · simp [einIntegrand]
  · rw [einIntegrand]
    field_simp

/-- **The substitution**: `∫₀^z (1 - e^{-st})\,dt/t = Ein(sz)`. -/
theorem intervalIntegral_dilate_einIntegrand (s z : ℝ) :
    (∫ t in (0 : ℝ)..z, (1 - Real.exp (-(s * t))) / t) = ein (s * z) := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp [ein, einIntegrand]
  · simp only [dilate_einIntegrand]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left _ hs,
      mul_zero, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hs, one_mul, ein]

/-- The dilated integrand is nonnegative on the half-line. -/
theorem dilate_einIntegrand_nonneg {s : ℝ} (hs : 0 ≤ s) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ (1 - Real.exp (-(s * u))) / u := by
  rw [dilate_einIntegrand]
  exact mul_nonneg hs (einIntegrand_nonneg (mul_nonneg hs hu))

/-- The dilated integrand is interval-integrable on `[0,z]` for `s, z ≥ 0`: bounded by `s`. -/
theorem intervalIntegrable_dilate_einIntegrand {s : ℝ} (hs : 0 ≤ s) {z : ℝ} (hz : 0 ≤ z) :
    IntervalIntegrable (fun t => (1 - Real.exp (-(s * t))) / t) volume 0 z := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hz]
  have hfin : volume (Ioc (0 : ℝ) z) ≠ ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hmeas : Measurable fun t : ℝ => (1 - Real.exp (-(s * t))) / t :=
    (measurable_const.sub (Real.measurable_exp.comp (by fun_prop))).div measurable_id
  refine Integrable.mono' (g := fun _ : ℝ => s) (integrableOn_const (hs := hfin))
    hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (.of_forall fun u hu => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (dilate_einIntegrand_nonneg hs hu.1.le),
    dilate_einIntegrand]
  calc s * einIntegrand (s * u) ≤ s * 1 :=
        mul_le_mul_of_nonneg_left (einIntegrand_le_one (mul_nonneg hs hu.1.le)) hs
    _ = s := mul_one s

end Hemigroup
