/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the MIT license as described in the file LICENSES/MIT.txt.
Authors: Daniel Fagerström
-/
import Hemigroup.Examples
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

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

/-- **`(1 - e^{-u})/u = ∫₀¹ e^{-uv} dv`.**

Not true at `u = 0`, where Lean's `0/0 = 0` disagrees with the integral's `1`; that is the one
place the junk value is visible, and it is why the antitonicity below is stated on `(0,∞)`. -/
theorem einIntegrand_eq_integral {u : ℝ} (hu : u ≠ 0) :
    einIntegrand u = ∫ v in (0 : ℝ)..1, Real.exp (-(u * v)) := by
  have hinner : (∫ w in (0 : ℝ)..u, Real.exp (-w)) = 1 - Real.exp (-u) := by
    rw [intervalIntegral.integral_comp_neg (fun w => Real.exp w), integral_exp, neg_zero,
      Real.exp_zero]
  rw [intervalIntegral.integral_comp_mul_left (fun w => Real.exp (-w)) hu, mul_zero, mul_one,
    hinner, smul_eq_mul, einIntegrand]
  field_simp

/-- **`(1 - e^{-u})/u` is nonincreasing on `(0,∞)`.**

Through the integral representation, where it is monotonicity of `e^{-uv}` in `u` and nothing
else. The direct route is the sign of the derivative, whose numerator is `e^{-u}(1+u) - 1`; that
is `1 + u ≤ e^u` and would do, but it needs the mean value theorem to get from the derivative to
the function, where the integral needs nothing.

This is what makes the difference quotient `(1 - e^{-st})/s` monotone in `s`, and hence what lets
the mean delay be reached by monotone convergence rather than by a Tauberian theorem. -/
theorem antitoneOn_einIntegrand : AntitoneOn einIntegrand (Ioi 0) := by
  intro a ha b hb hab
  rw [einIntegrand_eq_integral (mem_Ioi.mp ha).ne', einIntegrand_eq_integral (mem_Ioi.mp hb).ne']
  refine intervalIntegral.integral_mono_on zero_le_one
    ((Continuous.intervalIntegrable (by fun_prop) _ _))
    ((Continuous.intervalIntegrable (by fun_prop) _ _)) fun v hv => ?_
  exact Real.exp_le_exp.mpr (by nlinarith [hv.1])

/-- **`(1 - e^{-u})/u → 1` at the origin** — the difference quotient of `1 - e^{-x}` at `0`, which
is what `einIntegrand` *is*. -/
theorem tendsto_einIntegrand_nhdsNE_zero :
    Filter.Tendsto einIntegrand (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 1) := by
  have hd : HasDerivAt (fun x : ℝ => 1 - Real.exp (-x)) 1 0 := by
    have h1 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-1) 0 := by
      simpa using (hasDerivAt_neg (0 : ℝ)).exp
    simpa using h1.const_sub (1 : ℝ)
  have h := hasDerivAt_iff_tendsto_slope.mp hd
  refine h.congr fun u => ?_
  rw [slope_def_field, einIntegrand]
  simp

/-! ## The difference quotient at the origin

`s \mapsto (1 - e^{-st})/s` is the difference quotient whose limit at `s = 0` is the mean delay,
and written through `einIntegrand` it is `t·einIntegrand(st)`: nondecreasing as `s` decreases by
`antitoneOn_einIntegrand`, with limit `t` by `tendsto_einIntegrand_nhdsNE_zero`. Both are stated
below along a *sequence* of scales, which is the form monotone convergence consumes — and stating
them here rather than at the point of use is what keeps `prop:moments` free of any analysis of its
own.
-/

/-- **The difference quotient, through `Ein`'s integrand**: `(1 - e^{-st})/s = t·einIntegrand(st)`.

No hypothesis, and the degenerate cases are why: at `t = 0` both sides are `0`, and at `s = 0`
Lean's `x / 0 = 0` makes both sides `0` again. -/
theorem quotient_eq_mul_einIntegrand (s t : ℝ) :
    (1 - Real.exp (-(s * t))) / s = t * einIntegrand (s * t) := by
  rw [mul_comm s t]
  exact dilate_einIntegrand t s

/-- **The quotient grows as the scale shrinks** — `antitoneOn_einIntegrand` with the factor `t`
carried along. The `t = 0` case is separated because the antitonicity is stated on `(0,∞)`, and
there the quotient is `0` at every scale. -/
theorem mul_einIntegrand_le_of_le {t : ℝ} (ht : 0 ≤ t) {s s' : ℝ} (hs' : 0 < s') (hss : s' ≤ s) :
    t * einIntegrand (s * t) ≤ t * einIntegrand (s' * t) := by
  rcases ht.eq_or_lt with rfl | ht'
  · simp
  · refine mul_le_mul_of_nonneg_left ?_ ht
    exact antitoneOn_einIntegrand (mem_Ioi.mpr (mul_pos hs' ht'))
      (mem_Ioi.mpr (mul_pos (hs'.trans_le hss) ht')) (by nlinarith)

/-- `einIntegrand(s_n t) → 1` along any sequence of positive scales tending to `0`.

The sequence stays in `{0}ᶜ` because `t > 0`, which is what lets
`tendsto_einIntegrand_nhdsNE_zero` — a punctured limit, since the junk value at the origin is `0`
and not `1` — be composed with it. -/
theorem tendsto_einIntegrand_mul {t : ℝ} (ht : 0 < t) {s : ℕ → ℝ} (hpos : ∀ n, 0 < s n)
    (hlim : Filter.Tendsto s Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => einIntegrand (s n * t)) Filter.atTop (nhds 1) := by
  have hzero : Filter.Tendsto (fun n => s n * t) Filter.atTop (nhds 0) := by
    simpa using hlim.mul_const t
  have hmul : Filter.Tendsto (fun n => s n * t) Filter.atTop (nhdsWithin 0 {(0 : ℝ)}ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hzero
      (Filter.Eventually.of_forall fun n => ?_)
    simpa using (mul_pos (hpos n) ht).ne'
  simpa [Function.comp_def] using tendsto_einIntegrand_nhdsNE_zero.comp hmul

/-- And the quotient itself converges to `t` — the limit the mean delay is read off from. -/
theorem tendsto_mul_einIntegrand {t : ℝ} (ht : 0 ≤ t) {s : ℕ → ℝ} (hpos : ∀ n, 0 < s n)
    (hlim : Filter.Tendsto s Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => t * einIntegrand (s n * t)) Filter.atTop (nhds t) := by
  rcases ht.eq_or_lt with rfl | ht'
  · simp
  · simpa using (tendsto_einIntegrand_mul ht' hpos hlim).const_mul t

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
