/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.MemoryKernelTransform
import Hemigroup.MeanDelay
import Hemigroup.TransformContinuity

/-!
# `prop:volterra`: the Volterra equation for the kernels

Blueprint: `prop:volterra` (Proposition 9.8), the identity clause. As measures on `[0,∞)`,

  `t μ_x(dt) = (θ_x ∗ μ_x)(dt)`,   `θ_x(dt) = b₀ x δ₀(dt) + k(t/x) dt`.

## `θ_x` is `x` times the memory kernel, so the chapter already has its transform

`κ^{(x)} = b₀δ₀ + (1/x)k(t/x)dt` is `lem:memory-kernel`'s object, and `θ_x = x·κ^{(x)}` on the
nose — the atom scales from `b₀` to `b₀x` and the density from `k(t/x)/x` to `k(t/x)`. So the
blueprint's `θ̂_x(s) = b₀x + ∫e^{-st}k(t/x)dt = xF'(xs)` is `laplace_memoryKernel` times `x`, and
no new computation is needed on that side.

## What is new is differentiating the transform, and it is dominated convergence

`Lap[tμ](s) = -\frac{d}{ds}Lap[μ](s)` is the one analytic step. Mathlib has
`hasDerivAt_mgf`, but it asks for membership of the interior of the integrability set; the direct
route is `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with a **constant** dominating
function, because on a causal measure `t e^{-xt} ≤ 1/(ex)` uniformly in `t` — the maximum of
`u e^{-u}`. A finite measure then integrates a constant, so there is no integrability side
condition to discharge at all. Same tool `hasDerivAt_toRealExponent` uses in chapter 9, and the
easier instance of it.
-/

namespace Hemigroup

open MeasureTheory Set Filter

open scoped ENNReal Topology

/-- `u e^{-u} ≤ e^{-1}`: the maximum of the profile, from `1 + v ≤ e^v` at `v = u - 1`.

No hypothesis on `u`, which is worth noting because the estimate is normally quoted on the
half-line: to the left of the origin the left-hand side is negative and the bound is free. -/
theorem mul_exp_neg_le (u : ℝ) : u * Real.exp (-u) ≤ Real.exp (-1) := by
  have h : u ≤ Real.exp (u - 1) := by
    have := Real.add_one_le_exp (u - 1)
    linarith
  calc u * Real.exp (-u) ≤ Real.exp (u - 1) * Real.exp (-u) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = Real.exp (-1) := by rw [← Real.exp_add]; congr 1; ring

/-- The bound the differentiation runs on: `t e^{-xt} ≤ e^{-1}/x`, at every real `t`. -/
theorem mul_exp_neg_mul_le {x : ℝ} (hx : 0 < x) (t : ℝ) :
    t * Real.exp (-(x * t)) ≤ Real.exp (-1) / x := by
  have h := mul_exp_neg_le (x * t)
  rw [le_div_iff₀ hx]
  calc t * Real.exp (-(x * t)) * x = x * t * Real.exp (-(x * t)) := by ring
    _ ≤ Real.exp (-1) := h

/-- **The Laplace transform differentiates under the integral**, on a causal finite measure:
`Lap[μ]'(s) = -∫ t e^{-st} dμ`.

Dominated convergence with a *constant* bound — `t e^{-xt} ≤ e^{-1}/(s/2)` for `x > s/2` and
`t ≥ 0` — which a finite measure integrates for free. -/
theorem hasDerivAt_laplace {μ : Measure ℝ} [IsFiniteMeasure μ] (hμ : IsCausal μ) {s : ℝ}
    (hs : 0 < s) :
    HasDerivAt (laplace μ) (-∫ t, t * Real.exp (-(s * t)) ∂μ) s := by
  have hhalf : (0 : ℝ) < s / 2 := by linarith
  have hFint : Integrable (fun t : ℝ => Real.exp (-(s * t))) μ := by
    refine ⟨(by fun_prop : Measurable fun t : ℝ => Real.exp (-(s * t))).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have hb : ∀ᵐ t ∂μ, ‖Real.exp (-(s * t))‖ₑ ≤ (1 : ℝ≥0∞) := by
      filter_upwards [hμ.ae_nonneg] with t ht
      rw [Real.enorm_eq_ofReal (Real.exp_pos _).le, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr (by nlinarith))
    calc (∫⁻ t, ‖Real.exp (-(s * t))‖ₑ ∂μ) ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂μ := lintegral_mono_ae hb
      _ < ⊤ := by simp
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun x t => Real.exp (-(x * t)))
    (F' := fun x t => -(t * Real.exp (-(x * t))))
    (bound := fun _ => Real.exp (-1) / (s / 2))
    (x₀ := s) (s := Ioi (s / 2))
    (Ioi_mem_nhds (by linarith))
    (.of_forall fun x => (by fun_prop : Measurable fun t : ℝ =>
      Real.exp (-(x * t))).aestronglyMeasurable)
    hFint (by fun_prop) ?bound (integrable_const _) ?diff
  · exact key.2.congr_deriv (by rw [integral_neg])
  case bound =>
    filter_upwards [hμ.ae_nonneg] with t ht x hx
    rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg (mul_nonneg ht (Real.exp_pos _).le)]
    refine le_trans (mul_le_mul_of_nonneg_left ?_ ht) (mul_exp_neg_mul_le hhalf t)
    exact Real.exp_le_exp.mpr (by nlinarith [mem_Ioi.mp hx])
  case diff =>
    filter_upwards with t x _
    have h0 : HasDerivAt (fun y : ℝ => y * t) t x := by
      simpa using (hasDerivAt_id x).mul_const t
    have h1 : HasDerivAt (fun y : ℝ => -(y * t)) (-t) x := h0.neg
    have h2 := h1.exp
    rwa [show Real.exp (-(x * t)) * -t = -(t * Real.exp (-(x * t))) from by ring] at h2

/-- `t e^{-st}` is integrable against a causal finite measure, being bounded by `e^{-1}/s`. -/
theorem integrable_mul_exp_neg {μ : Measure ℝ} [IsFiniteMeasure μ] (hμ : IsCausal μ) {s : ℝ}
    (hs : 0 < s) : Integrable (fun t : ℝ => t * Real.exp (-(s * t))) μ := by
  refine Integrable.mono' (integrable_const (Real.exp (-1) / s)) (by fun_prop) ?_
  filter_upwards [hμ.ae_nonneg] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht (Real.exp_pos _).le)]
  exact mul_exp_neg_mul_le hs t

/-- **The size-biased measure's transform**: `Lap[tμ](s) = ∫ t e^{-st} dμ`. -/
theorem laplaceL_withDensity_id {μ : Measure ℝ} [IsFiniteMeasure μ] (hμ : IsCausal μ) {s : ℝ}
    (hs : 0 < s) :
    laplaceL (μ.withDensity fun t => ENNReal.ofReal t) s
      = ENNReal.ofReal (∫ t, t * Real.exp (-(s * t)) ∂μ) := by
  rw [laplaceL, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop),
    ofReal_integral_eq_lintegral_ofReal (integrable_mul_exp_neg hμ hs)
      ((hμ.ae_nonneg).mono fun t ht => mul_nonneg ht (Real.exp_pos _).le)]
  refine lintegral_congr_ae ?_
  filter_upwards [hμ.ae_nonneg] with t ht
  rw [Pi.mul_apply, ← ENNReal.ofReal_mul ht]

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent)

/-- **`θ_x = b₀ x δ₀(dt) + k(t/x)dt`**, the Volterra kernel — which is `x` times chapter 9's
memory kernel, so the chapter already has its transform. -/
noncomputable def volterraKernel (x : ℝ) : Measure ℝ := ENNReal.ofReal x • F.memoryKernel x

theorem isCausal_volterraKernel (x : ℝ) : IsCausal (F.volterraKernel x) := by
  rw [IsCausal, volterraKernel, Measure.smul_apply, F.isCausal_memoryKernel, smul_zero]

instance sFinite_volterraKernel (x : ℝ) : SFinite (F.volterraKernel x) := by
  rw [volterraKernel]; infer_instance

/-- `θ̂_x(s) = x F'(xs)`: `laplace_memoryKernel` scaled. -/
theorem laplaceL_volterraKernel {x s : ℝ} (hx : 0 < x) (hs : 0 < s) :
    laplaceL (F.volterraKernel x) s
      = ENNReal.ofReal (x * deriv F.toRealExponent (x * s)) := by
  rw [volterraKernel, laplaceL, lintegral_smul_measure, ← laplaceL,
    F.laplaceL_memoryKernel hx hs, symbol, mul_div_cancel_left₀ _ hs.ne', smul_eq_mul,
    ← ENNReal.ofReal_mul hx.le]

/-- **`prop:volterra`, the identity (9.1)**: `t μ_x(dt) = (θ_x ∗ μ_x)(dt)`.

Both sides have transform `xF'(xs)e^{-F(xs)}`, and `prop:laplace-uniqueness` separates them. The
left side's transform is where the work is — it is `-\frac{d}{ds}e^{-F(xs)}`, and
`hasDerivAt_laplace` is what turns the derivative into the size-biased integral. -/
theorem volterra {x : ℝ} (hx : 0 < x) :
    (F.kernel 0 x).withDensity (fun t => ENNReal.ofReal t)
      = F.volterraKernel x ∗ F.kernel 0 x := by
  haveI := isProbabilityMeasure_kernel (F := F) le_rfl hx.le
  have hcaus : IsCausal (F.kernel 0 x) := isCausal_kernel le_rfl hx.le
  -- the transform of the kernel, and its derivative
  have hlap : ∀ s : ℝ, 0 < s →
      laplace (F.kernel 0 x) s = Real.exp (-F.toRealExponent (x * s)) := by
    intro s hs
    rw [laplace_kernel le_rfl hx.le hs.le, increment_zero_left hx.le]
    rfl
  have hsize : ∀ s : ℝ, 0 < s → (∫ t, t * Real.exp (-(s * t)) ∂(F.kernel 0 x))
      = x * deriv F.toRealExponent (x * s) * Real.exp (-F.toRealExponent (x * s)) := by
    intro s hs
    have hF := (F.hasDerivAt_toRealExponent (by positivity : (0 : ℝ) < x * s))
    have hchain : HasDerivAt (fun y : ℝ => Real.exp (-F.toRealExponent (x * y)))
        (-(x * deriv F.toRealExponent (x * s)) * Real.exp (-F.toRealExponent (x * s))) s := by
      have hxy : HasDerivAt (fun y : ℝ => x * y) x s := by
        simpa using (hasDerivAt_id s).const_mul x
      have hcomp := (hF.comp s hxy).neg
      rw [hF.deriv] at *
      simpa [mul_comm] using hcomp.exp
    have heq := (hasDerivAt_laplace hcaus hs).congr_of_eventuallyEq
      (by filter_upwards [Ioi_mem_nhds hs] with y hy using (hlap y (mem_Ioi.mp hy)).symm)
    have := hchain.unique heq
    linarith [this]
  -- both sides, transformed
  refine laplaceL_injective_of_ne_top ?_ ((F.isCausal_volterraKernel x).conv hcaus)
    (?_ : laplaceL _ (1 : ℝ) ≠ ⊤) fun s hs => ?_
  · exact (withDensity_absolutelyContinuous _ _) hcaus
  · rw [laplaceL_withDensity_id hcaus zero_lt_one]
    exact ENNReal.ofReal_ne_top
  · have hspos : (0 : ℝ) < s := lt_of_lt_of_le zero_lt_one hs
    have hderiv_nn : 0 ≤ deriv F.toRealExponent (x * s) := by
      rw [(F.hasDerivAt_toRealExponent (by positivity : (0 : ℝ) < x * s)).deriv]
      have hI : 0 ≤ ∫ t in Ioi (0 : ℝ), Real.exp (-(x * s * t)) * F.k t :=
        integral_nonneg_of_ae ((ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun t ht =>
          mul_nonneg (Real.exp_pos _).le (F.k_nonneg t ht)))
      linarith [F.b₀_nonneg]
    have hk : laplaceL (F.kernel 0 x) s
        = ENNReal.ofReal (Real.exp (-F.toRealExponent (x * s))) := by
      rw [← hlap s hspos, laplace_eq_toReal_laplaceL,
        ENNReal.ofReal_toReal (laplaceL_ne_top_of_causal hcaus hspos.le)]
    rw [laplaceL_withDensity_id hcaus hspos, laplaceL_conv,
      F.laplaceL_volterraKernel hx hspos, hsize s hspos, hk,
      ← ENNReal.ofReal_mul (mul_nonneg hx.le hderiv_nn)]

/-- **`prop:volterra-uniqueness`**: `μ_{0,x}` is the *only* probability measure on `[0,∞)`
satisfying (9.1).

The scalar linear ODE the blueprint names, and it needs no new analysis: `hasDerivAt_laplace` was
stated for an arbitrary causal finite measure precisely so a competitor `ν` could use it, and what
is left is `(\log\hat\nu)' = -xF'(x\cdot)` against `F(x\cdot)' = xF'(x\cdot)` with both sides
vanishing at `0+` — `eq_of_hasDerivAt_of_tendsto_zero_pair`, the antiderivative-uniqueness lemma
chapter 8's closed forms already run on, generalised to two arbitrary functions when this became
its second consumer. The one extra ingredient is `\hat\nu > 0`, which is `laplace_pos_of_prob`. -/
theorem volterra_unique {x : ℝ} (hx : 0 < x) {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hνc : IsCausal ν)
    (h : ν.withDensity (fun t => ENNReal.ofReal t) = F.volterraKernel x ∗ ν) :
    ν = F.kernel 0 x := by
  haveI := isProbabilityMeasure_kernel (F := F) le_rfl hx.le
  have hcaus : IsCausal (F.kernel 0 x) := isCausal_kernel le_rfl hx.le
  have hpos : ∀ s : ℝ, 0 < s → 0 < laplace ν s := fun s hs => laplace_pos_of_prob hνc hs.le
  -- (9.1) read through the transform: the ODE `-\hat\nu'(s) = xF'(xs)\hat\nu(s)`
  have hode : ∀ s : ℝ, 0 < s → (∫ t, t * Real.exp (-(s * t)) ∂ν)
      = x * deriv F.toRealExponent (x * s) * laplace ν s := by
    intro s hs
    have hL := congrArg (fun μ => laplaceL μ s) h
    have hk : laplaceL ν s = ENNReal.ofReal (laplace ν s) := by
      rw [laplace_eq_toReal_laplaceL,
        ENNReal.ofReal_toReal (laplaceL_ne_top_of_causal hνc hs.le)]
    rw [laplaceL_withDensity_id hνc hs, laplaceL_conv, F.laplaceL_volterraKernel hx hs,
      hk] at hL
    have hderiv_nn : 0 ≤ deriv F.toRealExponent (x * s) := by
      rw [(F.hasDerivAt_toRealExponent (by positivity : (0 : ℝ) < x * s)).deriv]
      have hI : 0 ≤ ∫ t in Ioi (0 : ℝ), Real.exp (-(x * s * t)) * F.k t :=
        integral_nonneg_of_ae ((ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun t ht =>
          mul_nonneg (Real.exp_pos _).le (F.k_nonneg t ht)))
      linarith [F.b₀_nonneg]
    rw [← ENNReal.ofReal_mul (mul_nonneg hx.le hderiv_nn)] at hL
    have hnn : 0 ≤ ∫ t, t * Real.exp (-(s * t)) ∂ν :=
      integral_nonneg_of_ae (hνc.ae_nonneg.mono fun t ht => mul_nonneg ht (Real.exp_pos _).le)
    exact (ENNReal.ofReal_eq_ofReal_iff hnn
      (mul_nonneg (mul_nonneg hx.le hderiv_nn) (hpos s hs).le)).mp hL
  -- `-\log\hat\nu` and `F(x\cdot)` have the same derivative and both vanish at the origin
  have hlog : ∀ y : ℝ, 0 < y → HasDerivAt (fun z => -Real.log (laplace ν z))
      (x * deriv F.toRealExponent (x * y)) y := by
    intro y hy
    have hd := hasDerivAt_laplace hνc hy
    rw [hode y hy] at hd
    have hL0 : laplace ν y ≠ 0 := (hpos y hy).ne'
    have hlogd := (hd.log hL0).neg
    rwa [show -(-(x * deriv F.toRealExponent (x * y) * laplace ν y) / laplace ν y)
      = x * deriv F.toRealExponent (x * y) from by field_simp] at hlogd
  have hFx : ∀ y : ℝ, 0 < y → HasDerivAt (fun z => F.toRealExponent (x * z))
      (x * deriv F.toRealExponent (x * y)) y := by
    intro y hy
    have hxy : HasDerivAt (fun z : ℝ => x * z) x y := by
      simpa using (hasDerivAt_id y).const_mul x
    have hFd := F.hasDerivAt_toRealExponent (by positivity : (0 : ℝ) < x * y)
    have hc := hFd.comp y hxy
    rw [hFd.deriv]
    simpa [Function.comp_def, mul_comm] using hc
  have hlog0 : Tendsto (fun z => -Real.log (laplace ν z)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Tendsto (laplace ν) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      have h0 := ((continuousOn_laplace hνc) 0 Set.self_mem_Ici).tendsto
      rw [laplace_zero_prob] at h0
      exact h0.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    simpa using ((Real.continuousAt_log one_ne_zero).tendsto.comp hc).neg
  have hFx0 : Tendsto (fun z => F.toRealExponent (x * z)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine F.tendsto_toRealExponent_nhdsGT_zero.comp ?_
    have hzero : Tendsto (fun z : ℝ => x * z) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hm : Tendsto (fun z : ℝ => x * z) (𝓝 (0 : ℝ)) (𝓝 (x * 0)) :=
        tendsto_const_nhds.mul tendsto_id
      simpa using hm.mono_left nhdsWithin_le_nhds
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hzero ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact mem_Ioi.mpr (mul_pos hx (mem_Ioi.mp hz))
  -- the transforms agree, so the measures do
  refine laplace_injective hνc hcaus fun s hs => ?_
  rcases hs.eq_or_lt with rfl | hspos
  · rw [laplace_zero_prob, laplace_zero_prob]
  · have heq := eq_of_hasDerivAt_of_tendsto_zero_pair hlog hFx hlog0 hFx0 hspos
    rw [laplace_kernel le_rfl hx.le hspos.le, increment_zero_left hx.le,
      show ((F.exponent (x * s)).toReal) = F.toRealExponent (x * s) from rfl, ← heq, neg_neg,
      Real.exp_log (hpos s hspos)]

end SelfDecomposableExponent

end Hemigroup
