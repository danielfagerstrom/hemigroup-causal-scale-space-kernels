/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
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

/-! ## The transform, read off the box

The pairing of `g_s` against `μ * 1_{(0,1)}` collapses to `Λ_s · μ̂(s)`. That one identity does
two jobs: fed `μ * box = box` it gives (ND), and fed `μ * box = ρ * box` it says the transforms
agree — so the box alone determines a causal measure, which is the uniqueness clause of
`lem:convolution-representation`.
-/

/-- **The pairing factorises**: `⟨g_s, μ * box⟩ = ⟨g_s, box⟩ · μ̂(s)`. -/
theorem integral_clampExp_mconv_box [IsFiniteMeasure μ] (hμ : IsCausal μ) {s : ℝ} (hs : 0 ≤ s) :
    ∫ t, clampExp s t * mconv μ box t = (∫ t, clampExp s t * box t) * laplace μ s := by
  refine (integral_mul_mconv μ measurable_box.aestronglyMeasurable integrable_box
    (measurable_clampExp s) (abs_clampExp_le_one hs)).trans ?_
  rw [laplace, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hμ.ae_nonneg] with r hr
  rw [integral_clampExp_box_translate hr]
  ring

/-- **The box determines a causal measure.** Two finite causal measures that convolve the box
the same way have the same transform, and `laplace_injective` does the rest. -/
theorem eq_of_mconv_box_ae {μ ρ : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ρ]
    (hμ : IsCausal μ) (hρ : IsCausal ρ) (h : mconv μ box =ᵐ[volume] mconv ρ box) : μ = ρ := by
  refine laplace_injective hμ hρ fun s hs => ?_
  have hlhs : ∫ t, clampExp s t * mconv μ box t = ∫ t, clampExp s t * mconv ρ box t := by
    refine integral_congr_ae ?_
    filter_upwards [h] with t ht
    rw [ht]
  rw [integral_clampExp_mconv_box hμ hs, integral_clampExp_mconv_box hρ hs] at hlhs
  exact mul_left_cancel₀ (integral_clampExp_box_pos hs).ne' hlhs

/-! ## (ND) -/

@[simp] lemma laplace_dirac_zero (s : ℝ) : laplace (Measure.dirac (0 : ℝ)) s = 1 := by
  rw [laplace, integral_dirac]
  simp

/-- **Only `δ₀` convolves as the identity.** -/
theorem eq_dirac_of_mconv_box [IsProbabilityMeasure μ] (hμ : IsCausal μ)
    (h : mconv μ box =ᵐ[volume] box) : μ = Measure.dirac 0 :=
  eq_of_mconv_box_ae hμ (isCausal_dirac le_rfl) (by rwa [mconv_dirac_zero])

/-! ## The operator determines the measure

The same statement one level up, on `L¹`. Testing the operator on the single element
`1_{(0,1)}` of `X` is enough; no density argument, no separating family.
-/

/-- The box as an element of `X`. -/
noncomputable def boxL1 : X := integrable_box.toL1 box

lemma coeFn_boxL1 : ((boxL1 : X) : ℝ → ℝ) =ᵐ[volume] box := Integrable.coeFn_toL1 _

lemma coeFn_mconvL1_boxL1 (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ((mconvL1 μ boxL1 : X) : ℝ → ℝ) =ᵐ[volume] mconv μ box :=
  (coeFn_mconvL1 μ boxL1).trans (mconv_congr_ae μ coeFn_boxL1)

/-- **A causal measure is determined by its convolution operator** — the uniqueness clause of
`lem:convolution-representation`. -/
theorem mconvL1_injective {μ ρ : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ρ]
    (hμ : IsCausal μ) (hρ : IsCausal ρ) (h : mconvL1 μ = mconvL1 ρ) : μ = ρ := by
  refine eq_of_mconv_box_ae hμ hρ ?_
  have hμb := (coeFn_mconvL1_boxL1 μ).symm
  rw [h] at hμb
  exact hμb.trans (coeFn_mconvL1_boxL1 ρ)

end Hemigroup
