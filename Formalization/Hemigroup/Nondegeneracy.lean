/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.Family
import Hemigroup.Injectivity

/-!
# (ND): only `δ₀` acts as the identity

`def:cascade-family`'s nondegeneracy clause is `Φ_{x,y} ≠ Id` for `x < y`, and the kernels are
distinguished by their transforms, so what has to be supplied is the converse direction: a
measure whose convolution operator is the identity *is* `δ₀`.

## The argument

Pair the identity `μ * f = f` against a bounded `g` (`integral_mul_mconv`). Choosing

* `f = 1_{(0,1)}`, a box carried by the half line, and
* `g = g_s : t ↦ e^{-s max(t,0)}`, which is bounded on all of `ℝ` — unlike `e^{-st}` — and
  agrees with `e^{-st}` exactly where causal mass lives,

makes the inner integral factor: translating by `r ≥ 0` multiplies it by `e^{-sr}`, because on
the box `max(u+r,0) = u+r`. So the pairing collapses to

  `Λ_s = Λ_s · μ̂(s)`,

and `Λ_s > 0` forces `μ̂ ≡ 1`, which is `δ₀`'s transform. `laplace_injective` finishes.

The clamp is the same device `Injectivity.lean` and `WeakConvergence.lean` needed, for the same
reason: `e^{-st}` is unbounded on `ℝ`, and every argument that wants it as a test function has to
be told that the measure does not live there.
-/

namespace Hemigroup

open MeasureTheory Set
open scoped ENNReal

variable {μ : Measure ℝ}

/-! ## The test pair -/

/-- `g_s(t) = e^{-s max(t,0)}`: bounded on `ℝ`, and equal to `e^{-st}` for `t ≥ 0`. -/
noncomputable def clampExp (s t : ℝ) : ℝ := Real.exp (-(s * max t 0))

/-- The box `1_{(0,1)}`, a probability density carried by the half line. -/
noncomputable def box : ℝ → ℝ := (Ioo (0 : ℝ) 1).indicator (fun _ => 1)

lemma measurable_clampExp (s : ℝ) : Measurable (clampExp s) :=
  (Real.continuous_exp.comp
    (continuous_const.mul (continuous_id.max continuous_const)).neg).measurable

lemma abs_clampExp_le_one {s : ℝ} (hs : 0 ≤ s) (t : ℝ) : |clampExp s t| ≤ 1 := by
  rw [clampExp, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (by have : 0 ≤ max t 0 := le_max_right _ _; nlinarith)

lemma measurable_box : Measurable box := measurable_const.indicator measurableSet_Ioo

lemma box_nonneg (t : ℝ) : 0 ≤ box t := Set.indicator_nonneg (fun _ _ => zero_le_one) t

lemma integrable_box : Integrable box :=
  IntegrableOn.integrable_indicator
    (integrableOn_const (hs := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top))
    measurableSet_Ioo

@[simp] lemma integral_box : ∫ t, box t = 1 := by
  rw [box, integral_indicator_const _ measurableSet_Ioo, smul_eq_mul, mul_one, measureReal_def,
    Real.volume_Ioo]
  simp

/-! ## The factorisation -/

/-- Translating the box multiplies the pairing by `e^{-sr}`. This is where the clamp earns its
keep: on the box `max(u+r,0) = u+r`, so `g_s(u+r) = e^{-sr} g_s(u)`. -/
theorem integral_clampExp_box_translate {s r : ℝ} (hr : 0 ≤ r) :
    ∫ t, clampExp s t * box (t - r) = Real.exp (-(s * r)) * ∫ t, clampExp s t * box t := by
  rw [← integral_add_right_eq_self (fun t => clampExp s t * box (t - r)) r,
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [add_sub_cancel_right]
  by_cases hu : u ∈ Ioo (0 : ℝ) 1
  · have h1 : max (u + r) 0 = u + r := max_eq_left (by have := hu.1; linarith)
    have h2 : max u 0 = u := max_eq_left hu.1.le
    simp only [clampExp, h1, h2, box, Set.indicator_of_mem hu, mul_one, ← Real.exp_add]
    ring_nf
  · simp only [box, Set.indicator_of_notMem hu, mul_zero]

/-- The pairing is strictly positive: on the box, `g_s ≥ e^{-s}`. -/
theorem integral_clampExp_box_pos {s : ℝ} (hs : 0 ≤ s) : 0 < ∫ t, clampExp s t * box t := by
  have hint : Integrable (fun t => clampExp s t * box t) :=
    integrable_box.bdd_mul (c := 1) (measurable_clampExp s).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs]; exact abs_clampExp_le_one hs t)
  have hle : ∀ t, Real.exp (-s) * box t ≤ clampExp s t * box t := by
    intro t
    by_cases hu : t ∈ Ioo (0 : ℝ) 1
    · rw [box, Set.indicator_of_mem hu, mul_one, mul_one, clampExp,
        max_eq_left hu.1.le]
      exact Real.exp_le_exp.mpr (by nlinarith [hu.2.le, hu.1.le])
    · rw [box, Set.indicator_of_notMem hu, mul_zero, mul_zero]
  have hstep : Real.exp (-s) * ∫ t, box t ≤ ∫ t, clampExp s t * box t := by
    rw [← integral_const_mul]
    exact integral_mono (integrable_box.const_mul _) hint hle
  rw [integral_box, mul_one] at hstep
  exact lt_of_lt_of_le (Real.exp_pos _) hstep

/-! ## (ND) -/

@[simp] lemma laplace_dirac_zero (s : ℝ) : laplace (Measure.dirac (0 : ℝ)) s = 1 := by
  rw [laplace, integral_dirac]
  simp

/-- **Only `δ₀` convolves as the identity.**

Every step is a consequence of the pairing identity; the only inequality used is that the
pairing of the box with `g_s` is nonzero. -/
theorem eq_dirac_of_mconv_box [IsProbabilityMeasure μ] (hμ : IsCausal μ)
    (h : mconv μ box =ᵐ[volume] box) : μ = Measure.dirac 0 := by
  refine laplace_injective hμ (isCausal_dirac le_rfl) fun s hs => ?_
  rw [laplace_dirac_zero]
  have hpair := integral_mul_mconv μ measurable_box.aestronglyMeasurable integrable_box
    (measurable_clampExp s) (abs_clampExp_le_one hs)
  have hlhs : ∫ t, clampExp s t * mconv μ box t = ∫ t, clampExp s t * box t := by
    refine integral_congr_ae ?_
    filter_upwards [h] with t ht
    rw [ht]
  have hinner : ∫ r, (∫ t, clampExp s t * box (t - r)) ∂μ
      = (∫ t, clampExp s t * box t) * laplace μ s := by
    rw [laplace, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hμ.ae_nonneg] with r hr
    rw [integral_clampExp_box_translate hr]
    ring
  rw [hlhs, hinner] at hpair
  have hpos := integral_clampExp_box_pos hs
  have h1 : (∫ t, clampExp s t * box t) * 1 = (∫ t, clampExp s t * box t) * laplace μ s := by
    rw [mul_one]; exact hpair
  exact (mul_left_cancel₀ hpos.ne' h1).symm

end Hemigroup
