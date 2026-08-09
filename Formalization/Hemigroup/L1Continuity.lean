/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.Nondegeneracy
import Hemigroup.Continuity

/-!
# (A7): the tail estimate

(A7) asks for continuity of `(x,y) ↦ Φ_{x,y} f` **into `L¹`**, which is strictly more than the
weak convergence of the kernels that `Continuity.tendsto_integral_kernel` supplies. The blueprint
bridges the two with an `ε/3` argument on a compact carrying most of the mass; this file proves
the estimate that makes the compact work.

## The estimate

If `f` vanishes above `M`, then for `t > T + M` the integrand `f(t - r)` can only be nonzero when
`r > T`. Integrating that observation in `t` gives

  `∫_{t > T+M} ‖(μ * f)(t)‖ ≤ ‖f‖₁ · μ((T,∞))`,

so the right tail of `μ * f` is controlled by the right tail of `μ`, uniformly over the family —
which is exactly what `exists_kernel_tail_le` makes small. The left tail needs no estimate at all:
causality kills it outright.

The point of doing it this way is that the bound is *integrated*, not pointwise. Pointwise one only
gets `‖f‖_∞ · μ((T,∞))`, which is uniform in `t` but constant over an infinite range and therefore
useless in `L¹`. Moving the `t`-integral inside first is what converts it to `‖f‖₁`.
-/

namespace Hemigroup

open MeasureTheory Set
open scoped ENNReal

variable {μ : Measure ℝ}

/-- Translating a restricted lower integral. `∫⁻_{t > c} ‖f(t-r)‖ = ∫⁻_{u > c-r} ‖f(u)‖`: the
indicator travels with the integrand, so this is `lintegral_sub_right_eq_self` applied to the
product of the two. -/
theorem setLIntegral_enorm_sub_right (f : ℝ → ℝ) (c r : ℝ) :
    ∫⁻ t in Ioi c, ‖f (t - r)‖ₑ = ∫⁻ u in Ioi (c - r), ‖f u‖ₑ := by
  have hind : ∀ t : ℝ, (Ioi c).indicator (fun t => ‖f (t - r)‖ₑ) t
      = ((Ioi (c - r)).indicator (fun u => ‖f u‖ₑ)) (t - r) := by
    intro t
    by_cases ht : t ∈ Ioi c
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem (by simp only [mem_Ioi] at ht ⊢; linarith)]
    · rw [Set.indicator_of_notMem ht,
        Set.indicator_of_notMem (by simp only [mem_Ioi, not_lt] at ht ⊢; linarith)]
  rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi]
  simp only [hind]
  exact lintegral_sub_right_eq_self _ r

/-- **The tail estimate.** If `f` vanishes above `M`, the mass of `μ * f` beyond `T + M` is at
most `‖f‖₁` times the mass of `μ` beyond `T`. -/
theorem setLIntegral_enorm_mconv_tail_le (μ : Measure ℝ) [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f) {M T : ℝ} (hsupp : ∀ u, M < u → f u = 0) :
    ∫⁻ t in Ioi (T + M), ‖mconv μ f t‖ₑ ≤ (∫⁻ u, ‖f u‖ₑ) * μ (Ioi T) := by
  have huncurry : AEMeasurable (Function.uncurry fun t r : ℝ => ‖f (t - r)‖ₑ)
      ((volume.restrict (Ioi (T + M))).prod μ) := by
    refine AEMeasurable.mono_ac ?_ (Measure.AbsolutelyContinuous.prod
      (Measure.restrict_le_self.absolutelyContinuous) (Measure.AbsolutelyContinuous.rfl))
    exact hf.enorm.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub volume μ)
  calc ∫⁻ t in Ioi (T + M), ‖mconv μ f t‖ₑ
      ≤ ∫⁻ t in Ioi (T + M), ∫⁻ r, ‖f (t - r)‖ₑ ∂μ :=
        lintegral_mono fun t => enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ r, (∫⁻ t in Ioi (T + M), ‖f (t - r)‖ₑ) ∂μ := lintegral_lintegral_swap huncurry
    _ ≤ ∫⁻ _ in Ioi T, (∫⁻ u, ‖f u‖ₑ) ∂μ := by
        rw [← lintegral_indicator measurableSet_Ioi]
        refine lintegral_mono fun r => ?_
        rw [setLIntegral_enorm_sub_right]
        by_cases hr : r ∈ Ioi T
        · rw [Set.indicator_of_mem hr]
          exact setLIntegral_le_lintegral _ _
        · -- `r ≤ T` puts the whole region above `M`, where `f` vanishes.
          rw [Set.indicator_of_notMem hr]
          simp only [mem_Ioi, not_lt] at hr
          refine le_of_eq (setLIntegral_eq_zero measurableSet_Ioi fun u hu => ?_)
          simp [hsupp u (by simp only [mem_Ioi] at hu; linarith)]
    _ = (∫⁻ u, ‖f u‖ₑ) * μ (Ioi T) := by
        rw [setLIntegral_const, mul_comm]

/-- A compactly supported function vanishes outside a bounded window. This is the form the tail
estimate and the causality argument both consume — the latter needing only the left half. -/
theorem exists_window_of_hasCompactSupport {f : ℝ → ℝ} (hcs : HasCompactSupport f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, M < |x| → f x = 0 := by
  obtain ⟨R, hR⟩ := hcs.isCompact.isBounded.subset_closedBall (0 : ℝ)
  refine ⟨max R 0, le_max_right _ _, fun x hx => ?_⟩
  refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
  have hle := hR hmem
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hle
  exact absurd hx (by simp only [not_lt]; exact hle.trans (le_max_left _ _))

theorem vanish_left_of_window {f : ℝ → ℝ} {M : ℝ} (hM0 : 0 ≤ M)
    (hw : ∀ x, M < |x| → f x = 0) (x : ℝ) (hx : x < -M) : f x = 0 :=
  hw x (by rw [abs_of_neg (by linarith)]; linarith)

theorem vanish_right_of_window {f : ℝ → ℝ} {M : ℝ} (hM0 : 0 ≤ M)
    (hw : ∀ x, M < |x| → f x = 0) (x : ℝ) (hx : M < x) : f x = 0 :=
  hw x (by rw [abs_of_pos (by linarith)]; exact hx)

/-- **The left tail costs nothing.** Causality plus a compactly supported `f` make `μ * f` vanish
identically below `-M` — no estimate, no `ε`. This is the same asymmetry that made `[0,T]` the
right compact for tightness in `Continuity.lean`. -/
theorem mconv_eq_zero_of_window {μ : Measure ℝ} (hμ : IsCausal μ) {f : ℝ → ℝ} {M : ℝ}
    (hM0 : 0 ≤ M) (hw : ∀ x, M < |x| → f x = 0) {t : ℝ} (ht : t < -M) :
    mconv μ f t = 0 :=
  mconv_eq_zero_of_lt hμ (vanish_left_of_window hM0 hw) ht

/-- **The tail estimate for a difference.** Both terms are controlled separately, so the tails of
the two measures add. -/
theorem setLIntegral_enorm_mconv_sub_tail_le (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {f : ℝ → ℝ} (hf : AEStronglyMeasurable f) (hfi : Integrable f)
    {M T : ℝ} (hsupp : ∀ u, M < u → f u = 0) :
    ∫⁻ t in Ioi (T + M), ‖mconv μ f t - mconv ν f t‖ₑ
      ≤ (∫⁻ u, ‖f u‖ₑ) * μ (Ioi T) + (∫⁻ u, ‖f u‖ₑ) * ν (Ioi T) := by
  have hmμ : AEMeasurable (fun t => ‖mconv μ f t‖ₑ) (volume.restrict (Ioi (T + M))) :=
    ((integrable_mconv μ hf hfi).aestronglyMeasurable.enorm).restrict
  calc ∫⁻ t in Ioi (T + M), ‖mconv μ f t - mconv ν f t‖ₑ
      ≤ ∫⁻ t in Ioi (T + M), (‖mconv μ f t‖ₑ + ‖mconv ν f t‖ₑ) :=
        lintegral_mono fun t => enorm_sub_le
    _ = (∫⁻ t in Ioi (T + M), ‖mconv μ f t‖ₑ) + ∫⁻ t in Ioi (T + M), ‖mconv ν f t‖ₑ :=
        lintegral_add_left' hmμ _
    _ ≤ _ := add_le_add (setLIntegral_enorm_mconv_tail_le μ hf hsupp)
        (setLIntegral_enorm_mconv_tail_le ν hf hsupp)

/-! ## Pointwise convergence -/

namespace SelfDecomposableExponent

open Filter

/-- **Pointwise convergence of `μ_n * f`.** For bounded continuous `f`, the integrand
`r ↦ f (t - r)` is itself bounded continuous, which is exactly what weak convergence of the
kernels tests against — so `tendsto_integral_kernel` applies directly, with no partition of the
parameter interval and no continuity-set condition on `μ`.

Note the index range: `0 ≤ u n`, not `0 < u n`. The lower endpoint of `def:cascade-family` is
inside the range (A7) quantifies over, and since `increment_zero_left` made `x = 0` an ordinary
point of the construction, the whole tightness-and-transforms chain now covers it. -/
theorem tendsto_mconv_kernel_apply (F : SelfDecomposableExponent) {u v : ℕ → ℝ} {α β B : ℝ}
    (hB : 0 < B) (hu0 : ∀ n, 0 ≤ u n) (huv : ∀ n, u n ≤ v n) (hvB : ∀ n, v n ≤ B)
    (hα : Tendsto u atTop (nhds α)) (hβ : Tendsto v atTop (nhds β))
    (hα0 : 0 ≤ α) (hαβ : α ≤ β) (hβB : β ≤ B)
    {f : ℝ → ℝ} (hcont : Continuous f) {C : ℝ} (hbdd : ∀ x, ‖f x‖ ≤ C) (t : ℝ) :
    Tendsto (fun n => mconv (F.kernel (u n) (v n)) f t) atTop
      (nhds (mconv (F.kernel α β) f t)) := by
  have h := tendsto_integral_kernel F hB hu0 huv hvB hα hβ hα0 hαβ hβB
    (BoundedContinuousFunction.ofNormedAddCommGroup (fun r => f (t - r))
      (hcont.comp (continuous_const.sub continuous_id)) C (fun r => hbdd (t - r)))
  simpa [mconv_apply] using h

end SelfDecomposableExponent

end Hemigroup
