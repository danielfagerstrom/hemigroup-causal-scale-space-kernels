/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Hemigroup.Instance
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Towards `lem:convolution-representation`: convolution as a Bochner integral

M6b. The step every route to Lemma 4.1 needs first is

  `Φ (f * g) = f * (Φ g)`,

which is (A1) and (A2) and nothing else. The proof writes `f * g` as the `X`-valued Bochner
integral `∫ f(r) · τ_r g dr` and moves `Φ` inside, which a bounded operator may do.

Defining that integral is the work. It needs `r ↦ τ_r g` to be strongly measurable as a map into
`X`, and the clean sufficient condition is continuity — the statement that translation acts
continuously on `L¹`. Mathlib has no lemma under that name, but it has
`Lp.compMeasurePreserving_continuous`, joint continuity of `(g, φ) ↦ g ∘ φ` over
measure-preserving `φ` varying in `C(ℝ,ℝ)`, which is the same fact wearing a different hat. The
bridge is `transL1_eq`: the translation operator built in `Symmetries.lean` by hand agrees with
Mathlib's composition operator.

This file is deliberately stated for an arbitrary translation-commuting bounded operator rather
than for a `CascadeFamily`, since that is all the argument uses.
-/

namespace Hemigroup

open MeasureTheory Set Filter
open scoped ENNReal

/-! ## Translation acts continuously on `L¹` -/

/-- `a ↦ (t ↦ t - a)`, as a continuous map into `C(ℝ,ℝ)`. Currying is what makes the
compact-open continuity automatic. -/
noncomputable def subCM : C(ℝ, C(ℝ, ℝ)) :=
  ContinuousMap.curry ⟨fun p : ℝ × ℝ => p.2 - p.1, by fun_prop⟩

@[simp] lemma subCM_apply (a t : ℝ) : subCM a t = t - a := rfl

lemma measurePreserving_subCM (a : ℝ) :
    MeasurePreserving (subCM a) volume volume := measurePreserving_sub_const a

/-- The hand-built `transL1` is Mathlib's composition operator. -/
theorem transL1_eq (a : ℝ) (g : X) :
    transL1 a g = Lp.compMeasurePreserving (subCM a) (measurePreserving_subCM a) g := by
  refine Lp.ext ((coeFn_transL1 a g).trans ?_)
  exact (Lp.coeFn_compMeasurePreserving g (measurePreserving_subCM a)).symm

/-- **Translation acts continuously on `L¹`.** -/
theorem continuous_transL1 (g : X) : Continuous fun a : ℝ => transL1 a g := by
  rw [continuous_iff_continuousAt]
  intro a₀
  have h := Filter.Tendsto.compMeasurePreservingLp (l := nhds a₀) (f := fun _ : ℝ => g)
    (f₀ := g) (g := fun a : ℝ => subCM a) (g₀ := subCM a₀) tendsto_const_nhds
    (subCM.continuous.tendsto a₀) (fun a => measurePreserving_subCM a)
    (measurePreserving_subCM a₀) ENNReal.one_ne_top
  simp only [← transL1_eq] at h
  exact h

lemma norm_transL1_le (a : ℝ) (g : X) : ‖transL1 a g‖ ≤ ‖g‖ := by
  have hop : ‖transL1 a‖ ≤ 1 := by
    rw [transL1]
    exact LinearMap.mkContinuous_norm_le _ zero_le_one _
  calc ‖transL1 a g‖ ≤ ‖transL1 a‖ * ‖g‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖g‖ := by nlinarith [norm_nonneg g]
    _ = ‖g‖ := one_mul _

/-! ## Convolution as a Bochner integral -/

/-- `f * g = ∫ f(r) · τ_r g dr`, as an `X`-valued Bochner integral. -/
noncomputable def bconv (f : ℝ → ℝ) (g : X) : X := ∫ r, f r • transL1 r g

theorem integrable_smul_transL1 {f : ℝ → ℝ} (hf : Integrable f) (g : X) :
    Integrable (fun r => f r • transL1 r g) := by
  have hm : AEStronglyMeasurable (fun r => f r • transL1 r g) volume :=
    hf.aestronglyMeasurable.smul (continuous_transL1 g).aestronglyMeasurable
  refine ⟨hm, ?_⟩
  have hdom : ∀ r, ‖f r • transL1 r g‖ ≤ ‖f r‖ * ‖g‖ := by
    intro r
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (norm_transL1_le r g) (norm_nonneg _)
  exact ((hf.norm.mul_const ‖g‖).mono' hm
    (Filter.Eventually.of_forall hdom)).2

/-- **`Φ (f * g) = f * (Φ g)`.** The whole content of the step, for any bounded operator that
commutes with translation — which is (A1) and (A2) and nothing else. -/
theorem map_bconv (L : X →L[ℝ] X) (hL : ∀ a g, L (transL1 a g) = transL1 a (L g))
    {f : ℝ → ℝ} (hf : Integrable f) (g : X) :
    L (bconv f g) = bconv f (L g) := by
  rw [bconv, ← L.integral_comp_comm (integrable_smul_transL1 hf g), bconv]
  refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  change L (f r • transL1 r g) = f r • transL1 r (L g)
  rw [ContinuousLinearMap.map_smul, hL]

/-! ## `bconv` is the classical convolution

The Bochner integral defining `bconv` has no pointwise meaning on the nose — `L¹` has no
evaluation map — so identifying it with `t ↦ ∫ f(r) g(t-r) dr` goes through set integrals:
the two agree on every set of finite measure, and `ae_eq_of_forall_setIntegral_eq_of_sigmaFinite`
concludes. Pairing against a set is a bounded functional, so it passes through the Bochner
integral, which is what makes the left-hand side computable at all.
-/

/-- Integration over a fixed set of finite measure, as a bounded functional on `L¹`. -/
noncomputable def setIntegralCLM (A : Set ℝ) : X →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun h => ∫ t in A, (h : ℝ → ℝ) t
      map_add' := fun h₁ h₂ => by
        rw [← integral_add ((L1.integrable_coeFn h₁).integrableOn)
          ((L1.integrable_coeFn h₂).integrableOn)]
        refine integral_congr_ae ?_
        filter_upwards [(Lp.coeFn_add h₁ h₂).restrict] with t ht
        rw [ht]
        rfl
      map_smul' := fun c h => by
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [(Lp.coeFn_smul c h).restrict] with t ht
        rw [ht]
        rfl }
    1 fun h => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      calc ‖∫ t in A, (h : ℝ → ℝ) t‖ ≤ ∫ t in A, ‖(h : ℝ → ℝ) t‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ t, ‖(h : ℝ → ℝ) t‖ :=
            setIntegral_le_integral (L1.integrable_coeFn h).norm
              (Filter.Eventually.of_forall fun t => norm_nonneg _)
        _ = ‖h‖ := by
            rw [Lp.norm_def, eLpNorm_one_eq_lintegral_enorm,
              ← integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable h)]

@[simp] lemma setIntegralCLM_apply (A : Set ℝ) (h : X) :
    setIntegralCLM A h = ∫ t in A, (h : ℝ → ℝ) t := rfl

/-- The two-variable integrand of the classical convolution is integrable on the product —
the Tonelli bound `‖f‖₁ ‖g‖₁`, by translation invariance in `t`. -/
theorem integrable_uncurry_pconv {f : ℝ → ℝ} (hf : Integrable f) (g : X) :
    Integrable (fun p : ℝ × ℝ => f p.2 * (g : ℝ → ℝ) (p.1 - p.2)) (volume.prod volume) := by
  have hgm : AEStronglyMeasurable (fun p : ℝ × ℝ => (g : ℝ → ℝ) (p.1 - p.2))
      (volume.prod volume) :=
    (Lp.aestronglyMeasurable g).comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub volume volume)
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => f p.2 * (g : ℝ → ℝ) (p.1 - p.2))
      (volume.prod volume) :=
    ((hf.aestronglyMeasurable.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_snd)).mul hgm)
  refine ⟨hm, ?_⟩
  have hme : AEMeasurable
      (Function.uncurry fun t r : ℝ => ‖f r‖ₑ * ‖(g : ℝ → ℝ) (t - r)‖ₑ)
      (volume.prod volume) := by
    have hu : (Function.uncurry fun t r : ℝ => ‖f r‖ₑ * ‖(g : ℝ → ℝ) (t - r)‖ₑ)
        = fun p : ℝ × ℝ => ‖f p.2‖ₑ * ‖(g : ℝ → ℝ) (p.1 - p.2)‖ₑ := rfl
    rw [hu]
    simpa [enorm_mul] using hm.enorm
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hm.enorm]
  calc ∫⁻ t, ∫⁻ r, ‖f r * (g : ℝ → ℝ) (t - r)‖ₑ
      = ∫⁻ r, ∫⁻ t, ‖f r‖ₑ * ‖(g : ℝ → ℝ) (t - r)‖ₑ := by
        simp only [enorm_mul]
        exact lintegral_lintegral_swap hme
    _ = ∫⁻ r, ‖f r‖ₑ * ∫⁻ t, ‖(g : ℝ → ℝ) t‖ₑ := by
        refine lintegral_congr fun r => ?_
        rw [lintegral_const_mul' _ _ (enorm_ne_top),
          lintegral_sub_right_eq_self (fun t => ‖(g : ℝ → ℝ) t‖ₑ) r]
    _ < ⊤ := by
        rw [lintegral_mul_const' _ _ (L1.integrable_coeFn g).2.ne]
        exact ENNReal.mul_lt_top hf.2 (L1.integrable_coeFn g).2

/-- The classical convolution is integrable. -/
theorem integrable_pconv {f : ℝ → ℝ} (hf : Integrable f) (g : X) :
    Integrable (fun t => ∫ r, f r * (g : ℝ → ℝ) (t - r)) :=
  (integrable_uncurry_pconv hf g).integral_prod_left

/-- **`bconv` is the classical convolution.** -/
theorem coeFn_bconv {f : ℝ → ℝ} (hf : Integrable f) (g : X) :
    (bconv f g : ℝ → ℝ) =ᵐ[volume] fun t => ∫ r, f r * (g : ℝ → ℝ) (t - r) := by
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun A _ _ => (L1.integrable_coeFn (bconv f g)).integrableOn)
    (fun A _ _ => (integrable_pconv hf g).integrableOn) fun A hA hAfin => ?_
  -- Left: pass the bounded functional through the Bochner integral.
  have hleft : ∫ t in A, (bconv f g : ℝ → ℝ) t
      = ∫ r, f r * ∫ t in A, (g : ℝ → ℝ) (t - r) := by
    rw [← setIntegralCLM_apply A (bconv f g), bconv,
      ← ContinuousLinearMap.integral_comp_comm _ (integrable_smul_transL1 hf g)]
    refine integral_congr_ae ?_
    filter_upwards with r
    rw [ContinuousLinearMap.map_smul, setIntegralCLM_apply, smul_eq_mul]
    congr 1
    exact integral_congr_ae ((coeFn_transL1 r g).restrict)
  -- Right: Fubini.
  have hprodint : Integrable
      (Function.uncurry fun t r : ℝ => A.indicator (fun t' => f r * (g : ℝ → ℝ) (t' - r)) t)
      (volume.prod volume) := by
    have hset : (Function.uncurry fun t r : ℝ =>
          A.indicator (fun t' => f r * (g : ℝ → ℝ) (t' - r)) t)
        = (A ×ˢ (univ : Set ℝ)).indicator
          (fun p : ℝ × ℝ => f p.2 * (g : ℝ → ℝ) (p.1 - p.2)) := by
      funext p
      change A.indicator (fun t' => f p.2 * (g : ℝ → ℝ) (t' - p.2)) p.1
        = (A ×ˢ (univ : Set ℝ)).indicator
          (fun q : ℝ × ℝ => f q.2 * (g : ℝ → ℝ) (q.1 - q.2)) p
      by_cases hp : p.1 ∈ A
      · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (by simp [hp])]
      · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (by simp [hp])]
    rw [hset]
    exact (integrable_uncurry_pconv hf g).indicator (hA.prod MeasurableSet.univ)
  have hright : ∫ t in A, (∫ r, f r * (g : ℝ → ℝ) (t - r))
      = ∫ r, f r * ∫ t in A, (g : ℝ → ℝ) (t - r) := by
    rw [← integral_indicator hA]
    have hswap : ∫ t, A.indicator (fun t => ∫ r, f r * (g : ℝ → ℝ) (t - r)) t
        = ∫ t, ∫ r, A.indicator (fun t' => f r * (g : ℝ → ℝ) (t' - r)) t := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      by_cases ht : t ∈ A
      · simp only [Set.indicator_of_mem ht]
      · simp only [Set.indicator_of_notMem ht, integral_zero]
    rw [hswap, integral_integral_swap hprodint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
    change ∫ t, A.indicator (fun t' => f r * (g : ℝ → ℝ) (t' - r)) t
      = f r * ∫ t in A, (g : ℝ → ℝ) (t - r)
    rw [integral_indicator hA, integral_const_mul]
  rw [hleft, hright]

/-- `bconv` respects a.e. equality of the scalar factor. -/
theorem bconv_congr_ae {f₁ f₂ : ℝ → ℝ} (h : f₁ =ᵐ[volume] f₂) (g : X) :
    bconv f₁ g = bconv f₂ g := by
  refine integral_congr_ae ?_
  filter_upwards [h] with r hr
  rw [hr]

/-- `r ↦ t - r` preserves Lebesgue measure. -/
theorem measurePreserving_const_sub (t : ℝ) :
    MeasurePreserving (fun r : ℝ => t - r) volume volume :=
  (volume : Measure ℝ).measurePreserving_sub_left t

/-- Convolution is commutative — now that `bconv` has a pointwise description, this is the
change of variables `r ↦ t - r`. -/
theorem bconv_comm {f : ℝ → ℝ} (hf : Integrable f) (g : X) :
    bconv f g = bconv (g : ℝ → ℝ) (hf.toL1 f) := by
  refine Lp.ext ((coeFn_bconv hf g).trans ?_)
  refine Filter.EventuallyEq.symm
    ((coeFn_bconv (L1.integrable_coeFn g) (hf.toL1 f)).trans ?_)
  filter_upwards with t
  have hswap : ∫ r, (g : ℝ → ℝ) r * ((hf.toL1 f : X) : ℝ → ℝ) (t - r)
      = ∫ r, (g : ℝ → ℝ) r * f (t - r) := by
    refine integral_congr_ae ?_
    filter_upwards [(measurePreserving_const_sub t).quasiMeasurePreserving.ae
      (Integrable.coeFn_toL1 hf)] with r hr
    rw [hr]
  have hkey : ∫ r, (g : ℝ → ℝ) r * f (t - r) = ∫ r, f r * (g : ℝ → ℝ) (t - r) := by
    rw [← integral_sub_left_eq_self (fun r => f r * (g : ℝ → ℝ) (t - r)) volume t]
    refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
    change (g : ℝ → ℝ) r * f (t - r) = f (t - r) * (g : ℝ → ℝ) (t - (t - r))
    rw [sub_sub_cancel, mul_comm]
  rw [hswap, hkey]

/-! ## `μ * f` as a Bochner integral

`bconv` writes convolution by a density as `∫ f(r) · τ_r g dr`. The same formula with the
density replaced by a measure is `μ * f = ∫ τ_r f dμ(r)`, and *that* is the form a bounded
functional can be moved inside of. Identifying it with `mconvL1` is the argument of
`coeFn_bconv` again, with `volume` replaced by `μ` in the second factor.
-/

/-- `r ↦ τ_r f` is `μ`-integrable for every finite `μ`: continuous, hence strongly measurable,
and bounded by `‖f‖`. -/
theorem integrable_transL1 (μ : Measure ℝ) [IsFiniteMeasure μ] (f : X) :
    Integrable (fun r => transL1 r f) μ :=
  Integrable.mono' (integrable_const ‖f‖) (continuous_transL1 f).aestronglyMeasurable
    (Filter.Eventually.of_forall fun r => norm_transL1_le r f)

/-- `μ * f = ∫ τ_r f dμ(r)`, as an `X`-valued Bochner integral. -/
noncomputable def bconvM (μ : Measure ℝ) (f : X) : X := ∫ r, transL1 r f ∂μ

/-- **The Bochner form of `mconvL1`.** Both sides have the same integral over every set of
finite measure — on the left because `setIntegralCLM` passes through the Bochner integral, on
the right by Fubini on `volume ⊗ μ`. -/
theorem bconvM_eq_mconvL1 (μ : Measure ℝ) [IsFiniteMeasure μ] (f : X) :
    bconvM μ f = mconvL1 μ f := by
  refine Lp.ext ?_
  refine Filter.EventuallyEq.trans ?_ (coeFn_mconvL1 μ f).symm
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun A _ _ => (L1.integrable_coeFn (bconvM μ f)).integrableOn)
    (fun A _ _ => (integrable_mconv μ (Lp.aestronglyMeasurable f)
      (L1.integrable_coeFn f)).integrableOn) fun A hA _ => ?_
  -- Left: pass the bounded functional through the Bochner integral.
  have hleft : ∫ t in A, (bconvM μ f : ℝ → ℝ) t
      = ∫ r, (∫ t in A, (f : ℝ → ℝ) (t - r)) ∂μ := by
    rw [← setIntegralCLM_apply A (bconvM μ f), bconvM,
      ← ContinuousLinearMap.integral_comp_comm _ (integrable_transL1 μ f)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
    change ∫ t in A, ((transL1 r f : X) : ℝ → ℝ) t = ∫ t in A, (f : ℝ → ℝ) (t - r)
    exact integral_congr_ae ((coeFn_transL1 r f).restrict)
  -- Right: Fubini.
  have hprodint : Integrable
      (Function.uncurry fun t r : ℝ => A.indicator (fun t' => (f : ℝ → ℝ) (t' - r)) t)
      (volume.prod μ) := by
    have hset : (Function.uncurry fun t r : ℝ =>
          A.indicator (fun t' => (f : ℝ → ℝ) (t' - r)) t)
        = (A ×ˢ (univ : Set ℝ)).indicator
          (Function.uncurry fun t r : ℝ => (f : ℝ → ℝ) (t - r)) := by
      funext p
      change A.indicator (fun t' => (f : ℝ → ℝ) (t' - p.2)) p.1
        = (A ×ˢ (univ : Set ℝ)).indicator
          (fun q : ℝ × ℝ => (f : ℝ → ℝ) (q.1 - q.2)) p
      by_cases hp : p.1 ∈ A
      · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (by simp [hp])]
      · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (by simp [hp])]
    rw [hset]
    exact (integrable_uncurry_sub μ (Lp.aestronglyMeasurable f)
      (L1.integrable_coeFn f)).indicator (hA.prod MeasurableSet.univ)
  have hright : ∫ t in A, mconv μ (f : ℝ → ℝ) t
      = ∫ r, (∫ t in A, (f : ℝ → ℝ) (t - r)) ∂μ := by
    rw [← integral_indicator hA]
    have hswap : ∫ t, A.indicator (mconv μ (f : ℝ → ℝ)) t
        = ∫ t, ∫ r, A.indicator (fun t' => (f : ℝ → ℝ) (t' - r)) t ∂μ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      by_cases ht : t ∈ A
      · simp only [Set.indicator_of_mem ht, mconv_apply]
      · simp only [Set.indicator_of_notMem ht, integral_zero]
    rw [hswap, integral_integral_swap hprodint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
    change ∫ t, A.indicator (fun t' => (f : ℝ → ℝ) (t' - r)) t
      = ∫ t in A, (f : ℝ → ℝ) (t - r)
    rw [integral_indicator hA]
  rw [hleft, hright]

/-! ## Pairing with a bounded functional

For `Ψ : X →L[ℝ] ℝ` the map `r ↦ Ψ (τ_r f)` is continuous — translation acts continuously on
`L¹` — and bounded by `‖Ψ‖ ‖f‖`. It is therefore a legitimate test function for weak
convergence, and that single observation is the whole bridge from `ν_ε → μ` to `f * h_ε → μ * f`.
-/

/-- `r ↦ Ψ (τ_r f)`, as a bounded continuous function. -/
noncomputable def pairTrans (Ψ : X →L[ℝ] ℝ) (f : X) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun r => Ψ (transL1 r f))
    (Ψ.continuous.comp (continuous_transL1 f)) (‖Ψ‖ * ‖f‖) fun r =>
    (Ψ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_transL1_le r f) (norm_nonneg _))

@[simp] lemma pairTrans_apply (Ψ : X →L[ℝ] ℝ) (f : X) (r : ℝ) :
    pairTrans Ψ f r = Ψ (transL1 r f) := rfl

/-- **`Ψ (μ * f) = ∫ Ψ (τ_r f) dμ(r)`.** -/
theorem apply_mconvL1 (Ψ : X →L[ℝ] ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ] (f : X) :
    Ψ (mconvL1 μ f) = ∫ r, pairTrans Ψ f r ∂μ := by
  rw [← bconvM_eq_mconvL1, bconvM,
    ← ContinuousLinearMap.integral_comp_comm _ (integrable_transL1 μ f)]
  rfl

/-- **`Ψ (g * f) = ∫ g(r) Ψ (τ_r f) dr`**, the density counterpart. -/
theorem apply_bconv (Ψ : X →L[ℝ] ℝ) {g : ℝ → ℝ} (hg : Integrable g) (f : X) :
    Ψ (bconv g f) = ∫ r, g r * pairTrans Ψ f r := by
  rw [bconv, ← ContinuousLinearMap.integral_comp_comm _ (integrable_smul_transL1 hg f)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  change Ψ (g r • transL1 r f) = g r * Ψ (transL1 r f)
  rw [ContinuousLinearMap.map_smul, smul_eq_mul]

/-! ## The approximate identity -/

/-- `ρ_ε = ε^{-1} 1_{(0,ε)}`: a probability density carried by `[0,ε]`. Total in `ε` — for
`ε ≤ 0` the interval is empty and `ρ_ε = 0` — so no positivity hypothesis is needed to state
integrability. -/
noncomputable def approxId (ε : ℝ) : ℝ → ℝ :=
  fun t => ε⁻¹ * (Ioo (0 : ℝ) ε).indicator (fun _ => (1 : ℝ)) t

lemma approxId_nonneg (ε : ℝ) (t : ℝ) : 0 ≤ approxId ε t := by
  rcases le_or_gt ε 0 with h | h
  · have hempty : (Ioo (0 : ℝ) ε) = ∅ := Ioo_eq_empty (by simp; linarith)
    simp [approxId, hempty]
  · exact mul_nonneg (inv_nonneg.mpr h.le) (Set.indicator_nonneg (fun _ _ => zero_le_one) t)

lemma measurable_approxId (ε : ℝ) : Measurable (approxId ε) :=
  measurable_const.mul (measurable_const.indicator measurableSet_Ioo)

lemma integrable_approxId (ε : ℝ) : Integrable (approxId ε) :=
  (IntegrableOn.integrable_indicator
    (integrableOn_const (hs := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top))
    measurableSet_Ioo).const_mul _

lemma approxId_eq_zero {ε t : ℝ} (ht : t ∉ Ioo (0 : ℝ) ε) : approxId ε t = 0 := by
  simp [approxId, Set.indicator_of_notMem ht]

lemma integral_approxId {ε : ℝ} (hε : 0 < ε) : ∫ t, approxId ε t = 1 := by
  simp only [approxId]
  rw [integral_const_mul, integral_indicator_const _ measurableSet_Ioo, smul_eq_mul, mul_one,
    measureReal_def, Real.volume_Ioo, sub_zero, ENNReal.toReal_ofReal hε.le,
    inv_mul_cancel₀ hε.ne']

/-- `ρ_ε` as an element of `X`. -/
noncomputable def approxIdL1 (ε : ℝ) : X := (integrable_approxId ε).toL1 _

@[simp] lemma transL1_zero (g : X) : transL1 0 g = g := by
  refine Lp.ext ((coeFn_transL1 0 g).trans ?_)
  filter_upwards with t
  rw [sub_zero]

/-- **`ρ_ε * g → g` in `L¹`.** The mass sits in `(0,ε)`, where `τ_r g` is within `δ` of `g` by
continuity of translation — so the average of the translates is too. -/
theorem tendsto_bconv_approxId (g : X) :
    Tendsto (fun ε => bconv (approxId ε) g) (nhdsWithin 0 (Ioi 0)) (nhds g) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro δ hδ
  have hcont : ContinuousAt (fun r => transL1 r g) 0 := (continuous_transL1 g).continuousAt
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨η, hη, hηb⟩ := hcont (δ / 2) (by linarith)
  refine ⟨η, hη, fun {ε} hε hd => ?_⟩
  have hε0 : 0 < ε := hε
  have hεη : ε < η := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hε0] at hd
    exact hd
  have hint0 : Integrable (fun r => approxId ε r • (transL1 r g - g)) := by
    simp only [smul_sub]
    exact (integrable_smul_transL1 (integrable_approxId ε) g).sub
      ((integrable_approxId ε).smul_const g)
  have hsub : bconv (approxId ε) g - g = ∫ r, approxId ε r • (transL1 r g - g) := by
    have hsplit : ∫ r, approxId ε r • (transL1 r g - g)
        = (∫ r, approxId ε r • transL1 r g) - ∫ r, approxId ε r • g := by
      simp only [smul_sub]
      exact integral_sub (integrable_smul_transL1 (integrable_approxId ε) g)
        ((integrable_approxId ε).smul_const g)
    rw [hsplit, bconv, integral_smul_const, integral_approxId hε0, one_smul]
  have hbound : ∀ r, ‖approxId ε r • (transL1 r g - g)‖ ≤ approxId ε r * (δ / 2) := by
    intro r
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (approxId_nonneg ε r)]
    by_cases hr : r ∈ Ioo (0 : ℝ) ε
    · refine mul_le_mul_of_nonneg_left ?_ (approxId_nonneg ε r)
      have hdr : dist r 0 < η := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hr.1]
        linarith [hr.2]
      have := hηb hdr
      rw [transL1_zero, dist_eq_norm] at this
      exact this.le
    · rw [approxId_eq_zero hr]
      simp
  calc dist (bconv (approxId ε) g) g = ‖bconv (approxId ε) g - g‖ := dist_eq_norm _ _
    _ = ‖∫ r, approxId ε r • (transL1 r g - g)‖ := by rw [hsub]
    _ ≤ ∫ r, ‖approxId ε r • (transL1 r g - g)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ r, approxId ε r * (δ / 2) :=
        integral_mono hint0.norm ((integrable_approxId ε).mul_const _) hbound
    _ = δ / 2 := by rw [integral_mul_const, integral_approxId hε0, one_mul]
    _ < δ := by linarith

/-- **`f * ρ_ε → f`**, the form the representation argument consumes: the approximate identity
sits in the second slot, so that `Φ (f * ρ_ε) = f * (Φ ρ_ε)` puts `Φ` on the varying factor. -/
theorem tendsto_bconv_approxIdL1 {f : ℝ → ℝ} (hf : Integrable f) :
    Tendsto (fun ε => bconv f (approxIdL1 ε)) (nhdsWithin 0 (Ioi 0)) (nhds (hf.toL1 f)) := by
  have hcongr : ∀ ε : ℝ, bconv f (approxIdL1 ε) = bconv (approxId ε) (hf.toL1 f) := fun ε => by
    rw [bconv_comm hf (approxIdL1 ε)]
    exact bconv_congr_ae (Integrable.coeFn_toL1 (integrable_approxId ε)) _
  simp only [hcongr]
  exact tendsto_bconv_approxId _

/-! ## The approximants `h_ε = Φ ρ_ε`

(A3), (A4) and (A5) say exactly that `h_ε` is a probability density carried by `[0,∞)` — which
is what makes `ν_ε := h_ε · dt` a causal probability measure, the object Prokhorov will act on.
-/

lemma coeFn_approxIdL1 (ε : ℝ) : ((approxIdL1 ε : X) : ℝ → ℝ) =ᵐ[volume] approxId ε :=
  Integrable.coeFn_toL1 _

lemma isNonneg_approxIdL1 (ε : ℝ) : IsNonneg (approxIdL1 ε) := by
  filter_upwards [coeFn_approxIdL1 ε] with t ht
  simp only [Pi.zero_apply, ht]
  exact approxId_nonneg ε t

lemma vanishesBefore_approxIdL1 (ε : ℝ) : VanishesBefore 0 (approxIdL1 ε) := by
  filter_upwards [coeFn_approxIdL1 ε] with t ht hlt
  rw [ht]
  exact approxId_eq_zero fun hmem => absurd hmem.1 (not_lt.mpr hlt.le)

lemma integral_approxIdL1 {ε : ℝ} (hε : 0 < ε) :
    ∫ t, ((approxIdL1 ε : X) : ℝ → ℝ) t = 1 := by
  rw [integral_congr_ae (coeFn_approxIdL1 ε)]
  exact integral_approxId hε

namespace CascadeCore

/-- `h_ε = Φ_{x,y} ρ_ε`, the image of the approximate identity. -/
noncomputable def approx (Fam : CascadeCore) (x y ε : ℝ) : X := Fam.Φ x y (approxIdL1 ε)

variable {Fam : CascadeCore} {x y : ℝ}

lemma isNonneg_approx (hx : 0 ≤ x) (hxy : x ≤ y) (ε : ℝ) : IsNonneg (Fam.approx x y ε) :=
  Fam.positive x y hx hxy _ (isNonneg_approxIdL1 ε)

lemma vanishesBefore_approx (hx : 0 ≤ x) (hxy : x ≤ y) (ε : ℝ) :
    VanishesBefore 0 (Fam.approx x y ε) :=
  Fam.causal x y hx hxy 0 _ (vanishesBefore_approxIdL1 ε)

lemma integral_approx (hx : 0 ≤ x) (hxy : x ≤ y) {ε : ℝ} (hε : 0 < ε) :
    ∫ t, ((Fam.approx x y ε : X) : ℝ → ℝ) t = 1 := by
  rw [approx, Fam.unit_area x y hx hxy _ (isNonneg_approxIdL1 ε)]
  exact integral_approxIdL1 hε

/-- **`f * h_ε = Φ (f * ρ_ε)`**, the identity the whole argument turns on. `map_bconv` with
(A2) supplying the commutation. -/
theorem bconv_approx (hx : 0 ≤ x) (hxy : x ≤ y) {f : ℝ → ℝ} (hf : Integrable f) (ε : ℝ) :
    bconv f (Fam.approx x y ε) = Fam.Φ x y (bconv f (approxIdL1 ε)) :=
  (map_bconv (Fam.Φ x y) (fun a g => Fam.translation x y hx hxy a g) hf (approxIdL1 ε)).symm

/-- **`f * h_ε → Φ f`.** The left side is `Φ (f * ρ_ε)` and `f * ρ_ε → f`, so this is
continuity of a bounded operator. -/
theorem tendsto_bconv_approx (hx : 0 ≤ x) (hxy : x ≤ y) {f : ℝ → ℝ} (hf : Integrable f) :
    Tendsto (fun ε => bconv f (Fam.approx x y ε)) (nhdsWithin 0 (Ioi 0))
      (nhds (Fam.Φ x y (hf.toL1 f))) := by
  simp only [bconv_approx hx hxy hf]
  exact ((Fam.Φ x y).continuous.tendsto _).comp (tendsto_bconv_approxIdL1 hf)

/-! ## `ν_ε`, the approximants as measures -/

/-- `ν_ε = h_ε · dt`. -/
noncomputable def approxMeasure (Fam : CascadeCore) (x y ε : ℝ) : Measure ℝ :=
  volume.withDensity fun t => ENNReal.ofReal ((Fam.approx x y ε : X) t)

lemma isProbabilityMeasure_approxMeasure (hx : 0 ≤ x) (hxy : x ≤ y) {ε : ℝ} (hε : 0 < ε) :
    IsProbabilityMeasure (Fam.approxMeasure x y ε) := by
  constructor
  rw [approxMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (L1.integrable_coeFn _) (isNonneg_approx hx hxy ε),
    integral_approx hx hxy hε, ENNReal.ofReal_one]

lemma isCausal_approxMeasure (hx : 0 ≤ x) (hxy : x ≤ y) (ε : ℝ) :
    IsCausal (Fam.approxMeasure x y ε) := by
  rw [IsCausal, approxMeasure, withDensity_apply _ measurableSet_Iio]
  have hae : (fun t => ENNReal.ofReal ((Fam.approx x y ε : X) t))
      =ᵐ[volume.restrict (Iio 0)] 0 := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Iio]
    filter_upwards [vanishesBefore_approx (Fam := Fam) hx hxy ε] with t ht hmem
    rw [ht hmem, ENNReal.ofReal_zero]
    rfl
  rw [lintegral_congr_ae hae]
  simp

/-! ## Tightness

The tail of `ν_ε` is dominated by the tail of `ρ₁ * h_ε`, because convolving with a density
carried by `(0,1)` can only push mass to the right. And `ρ₁ * h_ε` converges in `L¹`, so its
tails are small uniformly — which is tightness.

No Fubini is needed: `setIntegralCLM` is a bounded functional, so it passes through the Bochner
integral defining `bconv`, exactly as it did in `coeFn_bconv`.
-/

/-- Translating a restricted Bochner integral. -/
theorem setIntegral_sub_right (φ : ℝ → ℝ) (T r : ℝ) :
    ∫ t in Ioi T, φ (t - r) = ∫ u in Ioi (T - r), φ u := by
  have hind : ∀ t : ℝ, (Ioi T).indicator (fun t => φ (t - r)) t
      = ((Ioi (T - r)).indicator φ) (t - r) := by
    intro t
    by_cases ht : t ∈ Ioi T
    · rw [Set.indicator_of_mem ht,
        Set.indicator_of_mem (by simp only [mem_Ioi] at ht ⊢; linarith)]
    · rw [Set.indicator_of_notMem ht,
        Set.indicator_of_notMem (by simp only [mem_Ioi, not_lt] at ht ⊢; linarith)]
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  simp only [hind]
  exact integral_sub_right_eq_self _ r

/-- **The tail of `ν_ε` is dominated by the tail of `ρ₁ * h_ε`.** -/
theorem tail_le_tail_bconv (hx : 0 ≤ x) (hxy : x ≤ y) (ε T : ℝ) :
    ∫ u in Ioi T, ((Fam.approx x y ε : X) : ℝ → ℝ) u
      ≤ ∫ t in Ioi T, ((bconv (approxId 1) (Fam.approx x y ε) : X) : ℝ → ℝ) t := by
  set h : X := Fam.approx x y ε with hh
  have hnn : IsNonneg h := isNonneg_approx hx hxy ε
  -- The value of the bounded functional on each integrand.
  have hpt : ∀ r : ℝ, setIntegralCLM (Ioi T) (approxId 1 r • transL1 r h)
      = approxId 1 r * ∫ u in Ioi (T - r), (h : ℝ → ℝ) u := by
    intro r
    rw [ContinuousLinearMap.map_smul, setIntegralCLM_apply, smul_eq_mul]
    congr 1
    rw [← setIntegral_sub_right (h : ℝ → ℝ) T r]
    exact integral_congr_ae ((coeFn_transL1 r h).restrict)
  -- Pass the bounded functional through the Bochner integral.
  have hpass : ∫ t in Ioi T, ((bconv (approxId 1) h : X) : ℝ → ℝ) t
      = ∫ r, approxId 1 r * ∫ u in Ioi (T - r), (h : ℝ → ℝ) u := by
    rw [← setIntegralCLM_apply (Ioi T) (bconv (approxId 1) h), bconv,
      ← ContinuousLinearMap.integral_comp_comm _
        (integrable_smul_transL1 (integrable_approxId 1) h)]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  -- Integrability of the right-hand integrand, by composing with the same functional.
  have hintg : Integrable (fun r => approxId 1 r * ∫ u in Ioi (T - r), (h : ℝ → ℝ) u) :=
    (((setIntegralCLM (Ioi T)).integrable_comp
      (integrable_smul_transL1 (integrable_approxId 1) h))).congr
      (Filter.Eventually.of_forall hpt)
  -- On the support of `ρ₁` the shifted tail is larger, `h` being nonnegative.
  have hmono : ∀ r, approxId 1 r * (∫ u in Ioi T, (h : ℝ → ℝ) u)
      ≤ approxId 1 r * ∫ u in Ioi (T - r), (h : ℝ → ℝ) u := by
    intro r
    by_cases hr : r ∈ Ioo (0 : ℝ) 1
    · refine mul_le_mul_of_nonneg_left ?_ (approxId_nonneg 1 r)
      refine setIntegral_mono_set (L1.integrable_coeFn h).integrableOn
        (ae_restrict_of_ae hnn) (HasSubset.Subset.eventuallyLE fun u hu => ?_)
      simp only [mem_Ioi] at hu ⊢
      linarith [hr.1]
    · rw [approxId_eq_zero hr, zero_mul, zero_mul]
  rw [hpass]
  calc ∫ u in Ioi T, (h : ℝ → ℝ) u
      = ∫ r, approxId 1 r * ∫ u in Ioi T, (h : ℝ → ℝ) u := by
        rw [integral_mul_const, integral_approxId one_pos, one_mul]
    _ ≤ ∫ r, approxId 1 r * ∫ u in Ioi (T - r), (h : ℝ → ℝ) u :=
        integral_mono ((integrable_approxId 1).mul_const _) hintg hmono

/-! ### Tails vanish -/

/-- The right tail of a finite measure can be made as small as wanted. -/
theorem exists_measure_Ioi_le (ν : Measure ℝ) [IsFiniteMeasure ν] {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ T : ℝ, ν (Ioi T) ≤ η := by
  have hmono : Antitone fun n : ℕ => Ioi (n : ℝ) := fun m n hmn =>
    Ioi_subset_Ioi (by exact_mod_cast hmn)
  have hinter : (⋂ n : ℕ, Ioi (n : ℝ)) = ∅ := by
    ext t
    simp only [Set.mem_iInter, mem_Ioi, Set.mem_empty_iff_false, iff_false, not_forall, not_lt]
    obtain ⟨n, hn⟩ := exists_nat_gt t
    exact ⟨n, hn.le⟩
  have h := tendsto_measure_iInter_atTop
    (fun n : ℕ => (measurableSet_Ioi (a := (n : ℝ))).nullMeasurableSet) hmono
    ⟨0, measure_ne_top ν _⟩
  rw [hinter, measure_empty] at h
  obtain ⟨n, hn⟩ := (h.eventually (gt_mem_nhds hη)).exists
  exact ⟨n, hn.le⟩

/-- The right tail of an integrable function's absolute value can be made as small as wanted. -/
theorem exists_setIntegral_abs_tail_le {k : ℝ → ℝ} (hk : Integrable k) {η : ℝ} (hη : 0 < η) :
    ∃ T : ℝ, ∫ u in Ioi T, |k u| ≤ η := by
  set ν : Measure ℝ := volume.withDensity fun t => ‖k t‖ₑ with hν
  haveI : IsFiniteMeasure ν := by
    constructor
    rw [hν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hk.2
  obtain ⟨T, hT⟩ := exists_measure_Ioi_le ν (η := ENNReal.ofReal η)
    (by simp only [ENNReal.ofReal_pos]; linarith)
  refine ⟨T, ?_⟩
  have hval : ν (Ioi T) = ∫⁻ u in Ioi T, ‖k u‖ₑ := withDensity_apply _ measurableSet_Ioi
  have heq : ∫ u in Ioi T, |k u| = (∫⁻ u in Ioi T, ‖k u‖ₑ).toReal := by
    simpa [Real.norm_eq_abs] using
      integral_norm_eq_lintegral_enorm (hk.aestronglyMeasurable.restrict)
  rw [heq, ← hval]
  calc (ν (Ioi T)).toReal ≤ (ENNReal.ofReal η).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hT
    _ = η := ENNReal.toReal_ofReal hη.le

/-! ### The tightness statement -/

/-- The sequence `ε n = 1/(n+1)` along which the approximants are taken. -/
noncomputable def epsSeq (n : ℕ) : ℝ := 1 / (n + 1)

lemma epsSeq_pos (n : ℕ) : 0 < epsSeq n := by
  rw [epsSeq]; positivity

lemma tendsto_epsSeq : Tendsto epsSeq atTop (nhdsWithin 0 (Ioi 0)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    tendsto_one_div_add_atTop_nhds_zero_nat
    (Filter.Eventually.of_forall fun n => epsSeq_pos n)

/-- **The tails of `ν_{ε n}` are small uniformly in `n`.**

For large `n` the bound comes from `ρ₁ * h_{ε n} → Φ ρ₁` in `L¹` together with
`tail_le_tail_bconv`; for the finitely many small `n` each measure is finite and supplies its
own cutoff, and the maximum serves for all. -/
theorem exists_uniform_tail (hx : 0 ≤ x) (hxy : x ≤ y) {η : ℝ} (hη : 0 < η) :
    ∃ T : ℝ, ∀ n : ℕ, ∫ u in Ioi T, ((Fam.approx x y (epsSeq n) : X) : ℝ → ℝ) u ≤ η := by
  -- The `L¹` limit of `ρ₁ * h_ε`.
  set k : X := Fam.Φ x y ((integrable_approxId 1).toL1 (approxId 1)) with hk
  obtain ⟨T₁, hT₁⟩ := exists_setIntegral_abs_tail_le (L1.integrable_coeFn k) (η := η / 2)
    (by linarith)
  -- Large `n`.
  have hconv : Tendsto (fun n => bconv (approxId 1) (Fam.approx x y (epsSeq n))) atTop
      (nhds k) :=
    (tendsto_bconv_approx hx hxy (integrable_approxId 1)).comp tendsto_epsSeq
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hconv (η / 2) (by linarith)
  -- Small `n`: finitely many, each with its own cutoff.
  have hfin : ∀ m : ℕ, ∃ T : ℝ, ∫ u in Ioi T,
      ((Fam.approx x y (epsSeq m) : X) : ℝ → ℝ) u ≤ η := by
    intro m
    obtain ⟨T, hT⟩ := exists_setIntegral_abs_tail_le
      (L1.integrable_coeFn (Fam.approx x y (epsSeq m))) hη
    refine ⟨T, le_trans ?_ hT⟩
    exact setIntegral_mono_on (L1.integrable_coeFn _).integrableOn
      (L1.integrable_coeFn (Fam.approx x y (epsSeq m))).abs.integrableOn measurableSet_Ioi
      fun u _ => le_abs_self _
  choose Tsmall hTsmall using hfin
  obtain ⟨M, hM⟩ := Finset.exists_le ((Finset.range N).image Tsmall)
  refine ⟨max T₁ M, fun n => ?_⟩
  by_cases hn : N ≤ n
  · -- The `L¹` estimate.
    have hd := hN n hn
    rw [dist_eq_norm] at hd
    have hstep : ∫ t in Ioi (max T₁ M),
        ((bconv (approxId 1) (Fam.approx x y (epsSeq n)) : X) : ℝ → ℝ) t ≤ η := by
      set F : X := bconv (approxId 1) (Fam.approx x y (epsSeq n)) with hF
      have hdiff : Integrable (fun t => (F : ℝ → ℝ) t - (k : ℝ → ℝ) t) :=
        (L1.integrable_coeFn F).sub (L1.integrable_coeFn k)
      have habsk : Integrable (fun t => |(k : ℝ → ℝ) t|) := (L1.integrable_coeFn k).abs
      calc ∫ t in Ioi (max T₁ M), (F : ℝ → ℝ) t
          ≤ ∫ t in Ioi (max T₁ M), (|(k : ℝ → ℝ) t| + |(F : ℝ → ℝ) t - (k : ℝ → ℝ) t|) := by
            refine setIntegral_mono_on (L1.integrable_coeFn F).integrableOn
              (habsk.add hdiff.abs).integrableOn measurableSet_Ioi fun u _ => ?_
            calc (F : ℝ → ℝ) u = (k : ℝ → ℝ) u + ((F : ℝ → ℝ) u - (k : ℝ → ℝ) u) := by ring
              _ ≤ |(k : ℝ → ℝ) u| + |(F : ℝ → ℝ) u - (k : ℝ → ℝ) u| :=
                  add_le_add (le_abs_self _) (le_abs_self _)
        _ = (∫ t in Ioi (max T₁ M), |(k : ℝ → ℝ) t|)
              + ∫ t in Ioi (max T₁ M), |(F : ℝ → ℝ) t - (k : ℝ → ℝ) t| :=
            integral_add habsk.integrableOn hdiff.abs.integrableOn
        _ ≤ η / 2 + η / 2 := by
            refine add_le_add (le_trans ?_ hT₁) ?_
            · exact setIntegral_mono_set habsk.integrableOn
                (ae_restrict_of_ae (Filter.Eventually.of_forall fun u => abs_nonneg _))
                (HasSubset.Subset.eventuallyLE (Ioi_subset_Ioi (le_max_left _ _)))
            · calc ∫ t in Ioi (max T₁ M), |(F : ℝ → ℝ) t - (k : ℝ → ℝ) t|
                  ≤ ∫ t, |(F : ℝ → ℝ) t - (k : ℝ → ℝ) t| :=
                    setIntegral_le_integral hdiff.abs
                      (Filter.Eventually.of_forall fun u => abs_nonneg _)
                _ = ‖F - k‖ := by
                    rw [norm_sub_eq_lintegral, ← integral_norm_eq_lintegral_enorm
                      (f := fun t => (F : ℝ → ℝ) t - (k : ℝ → ℝ) t) hdiff.aestronglyMeasurable]
                    simp [Real.norm_eq_abs]
                _ ≤ η / 2 := hd.le
        _ = η := by ring
    exact le_trans (tail_le_tail_bconv hx hxy _ _) hstep
  · -- One of the finitely many exceptions.
    push_neg at hn
    refine le_trans ?_ (hTsmall n)
    exact setIntegral_mono_set (L1.integrable_coeFn _).integrableOn
      (ae_restrict_of_ae (isNonneg_approx hx hxy _))
      (HasSubset.Subset.eventuallyLE
        (Ioi_subset_Ioi (le_trans (hM _ (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hn)))
          (le_max_right _ _))))

/-- The right tail of `ν_ε`, in terms of the density. -/
lemma approxMeasure_Ioi (hx : 0 ≤ x) (hxy : x ≤ y) (ε T : ℝ) :
    Fam.approxMeasure x y ε (Ioi T)
      = ENNReal.ofReal (∫ u in Ioi T, ((Fam.approx x y ε : X) : ℝ → ℝ) u) := by
  rw [approxMeasure, withDensity_apply _ measurableSet_Ioi,
    ← ofReal_integral_eq_lintegral_ofReal (L1.integrable_coeFn _).integrableOn
      (ae_restrict_of_ae (isNonneg_approx hx hxy ε))]

/-- **The approximants are tight.** The compact is `[0,T]`: causality kills the left tail
outright, so the whole content is `exists_uniform_tail`. -/
theorem isTightMeasureSet_approxMeasure (hx : 0 ≤ x) (hxy : x ≤ y) :
    IsTightMeasureSet {ν : Measure ℝ | ∃ n : ℕ, ν = Fam.approxMeasure x y (epsSeq n)} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro η hη
  rcases eq_or_ne η ⊤ with rfl | hηtop
  · exact ⟨∅, isCompact_empty, fun ν _ => le_top⟩
  have hη0 : 0 < η.toReal := ENNReal.toReal_pos hη.ne' hηtop
  obtain ⟨T, hT⟩ := exists_uniform_tail hx hxy hη0
  refine ⟨Icc 0 T, isCompact_Icc, ?_⟩
  rintro ν ⟨n, rfl⟩
  have hsub : (Icc (0 : ℝ) T)ᶜ ⊆ Iio 0 ∪ Ioi T := by
    intro u hu
    simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at hu
    exact hu.imp id id
  calc Fam.approxMeasure x y (epsSeq n) ((Icc (0 : ℝ) T)ᶜ)
      ≤ Fam.approxMeasure x y (epsSeq n) (Iio 0 ∪ Ioi T) := measure_mono hsub
    _ ≤ Fam.approxMeasure x y (epsSeq n) (Iio 0)
        + Fam.approxMeasure x y (epsSeq n) (Ioi T) := measure_union_le _ _
    _ = Fam.approxMeasure x y (epsSeq n) (Ioi T) := by
        rw [isCausal_approxMeasure hx hxy (epsSeq n), zero_add]
    _ ≤ η := by
        rw [approxMeasure_Ioi hx hxy]
        calc ENNReal.ofReal (∫ u in Ioi T, ((Fam.approx x y (epsSeq n) : X) : ℝ → ℝ) u)
            ≤ ENNReal.ofReal η.toReal := ENNReal.ofReal_le_ofReal (hT n)
          _ = η := ENNReal.ofReal_toReal hηtop

/-! ## The limit measure

Prokhorov turns tightness into a convergent subsequence. `ProbabilityMeasure ℝ` is metrizable
because `ℝ` is Polish, so compactness of the closure gives sequential compactness.
-/

/-- **A weak limit exists.** Some subsequence of the approximants converges weakly to a causal
probability measure. -/
theorem exists_weak_limit (hx : 0 ≤ x) (hxy : x ≤ y) :
    ∃ (μ : Measure ℝ) (_ : IsProbabilityMeasure μ), IsCausal μ ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ φ : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun k => ∫ t, φ t ∂(Fam.approxMeasure x y (epsSeq (σ k)))) atTop
          (nhds (∫ t, φ t ∂μ)) := by
  haveI hprob : ∀ n : ℕ, IsProbabilityMeasure (Fam.approxMeasure x y (epsSeq n)) := fun n =>
    isProbabilityMeasure_approxMeasure hx hxy (epsSeq_pos n)
  -- The approximants as `ProbabilityMeasure ℝ`.
  set P : ℕ → ProbabilityMeasure ℝ := fun n => ⟨Fam.approxMeasure x y (epsSeq n), hprob n⟩ with hP
  have hsetEq : {ν : Measure ℝ | ∃ Q ∈ Set.range P, (Q : Measure ℝ) = ν}
      = {ν : Measure ℝ | ∃ n : ℕ, ν = Fam.approxMeasure x y (epsSeq n)} := by
    ext ν
    constructor
    · rintro ⟨-, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨P n, ⟨n, rfl⟩, rfl⟩
  have hset : IsTightMeasureSet {ν : Measure ℝ | ∃ Q ∈ Set.range P, (Q : Measure ℝ) = ν} := by
    rw [hsetEq]
    exact isTightMeasureSet_approxMeasure hx hxy
  have hcompact : IsCompact (closure (Set.range P)) :=
    isCompact_closure_of_isTightMeasureSet hset
  obtain ⟨Q, -, σ, hσ, hQ⟩ :=
    hcompact.tendsto_subseq (fun n => subset_closure (Set.mem_range_self n))
  refine ⟨(Q : Measure ℝ), Q.2, ?_, σ, hσ, fun φ => ?_⟩
  · -- Causality passes to the limit: `Iio 0` is open, so portmanteau bounds it.
    rw [IsCausal, ← le_zero_iff]
    have hport := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hQ
      (isOpen_Iio (a := (0 : ℝ)))
    refine hport.trans (le_of_eq ?_)
    have hzero : ∀ k : ℕ, ((P ∘ σ) k : Measure ℝ) (Iio 0) = 0 := fun k =>
      isCausal_approxMeasure hx hxy _
    simp only [hzero]
    exact Filter.liminf_const 0
  · exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hQ) φ

/-! ## The identification

`exists_weak_limit` produces a measure; this section shows it is *the* measure, i.e. that
`Φ_{x,y} f = μ_{x,y} * f`. The proof pairs both sides against an arbitrary bounded functional
`Ψ` and reads the three ingredients off:

* `Ψ (f * h_ε) = ∫ Ψ (τ_r f) dν_ε(r)` — `apply_bconv`, after `bconv_comm` puts `h_ε` in the
  density slot;
* `∫ Ψ (τ_r f) dν_ε → ∫ Ψ (τ_r f) dμ` — weak convergence, legitimate because `pairTrans` is
  bounded continuous;
* `∫ Ψ (τ_r f) dμ = Ψ (μ * f)` — `apply_mconvL1`.

Since `f * h_ε → Φ f` in `X` and `Ψ` is continuous, the two limits agree, and taking
`Ψ = setIntegralCLM A` for every `A` separates points of `X`.

Note what is *not* needed: the blueprint restricts to `f ∈ C_c` and extends by density, because
its pointwise argument needs `f(t - ·) ∈ C_0`. Nothing here is pointwise — the Bochner
formulation applies verbatim to every `f ∈ X`, since `Integrable.toL1_coeFn` says every element
of `X` already *is* `hf.toL1 f`. The density step disappears.
-/

/-- Integration against `ν_ε` is integration against the density `h_ε`. -/
theorem integral_approxMeasure (hx : 0 ≤ x) (hxy : x ≤ y) (ε : ℝ)
    (G : BoundedContinuousFunction ℝ ℝ) :
    ∫ r, G r ∂(Fam.approxMeasure x y ε)
      = ∫ r, ((Fam.approx x y ε : X) : ℝ → ℝ) r * G r := by
  rw [approxMeasure, integral_withDensity_eq_integral_toReal_smul₀
    ((Lp.aestronglyMeasurable (Fam.approx x y ε)).aemeasurable.ennreal_ofReal)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards [isNonneg_approx (Fam := Fam) hx hxy ε] with r hr
  rw [smul_eq_mul, ENNReal.toReal_ofReal hr]

/-- **The pairing identity in the limit.** For every bounded functional, `Ψ (Φ f)` is the
integral of the bounded continuous function `r ↦ Ψ (τ_r f)` against the weak limit. -/
theorem apply_eq_integral_pairTrans (hx : 0 ≤ x) (hxy : x ≤ y) {μ : Measure ℝ}
    {σ : ℕ → ℕ} (hσ : StrictMono σ)
    (hweak : ∀ φ : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun k => ∫ t, φ t ∂(Fam.approxMeasure x y (epsSeq (σ k)))) atTop
        (nhds (∫ t, φ t ∂μ)))
    (Ψ : X →L[ℝ] ℝ) (f : X) :
    Ψ (Fam.Φ x y f) = ∫ r, pairTrans Ψ f r ∂μ := by
  have hfL : (L1.integrable_coeFn f).toL1 (f : ℝ → ℝ) = f :=
    Integrable.toL1_coeFn f (L1.integrable_coeFn f)
  -- `f * h_{ε_k} → Φ f`, hence `Ψ (f * h_{ε_k}) → Ψ (Φ f)`.
  have h1 : Tendsto (fun k => Ψ (bconv (f : ℝ → ℝ) (Fam.approx x y (epsSeq (σ k))))) atTop
      (nhds (Ψ (Fam.Φ x y f))) := by
    have hlim := (tendsto_bconv_approx hx hxy (Fam := Fam) (L1.integrable_coeFn f)).comp
      (tendsto_epsSeq.comp hσ.tendsto_atTop)
    rw [hfL] at hlim
    exact (Ψ.continuous.tendsto _).comp hlim
  -- The same quantity, as an integral against `ν_{ε_k}`.
  have h2 : ∀ k : ℕ, Ψ (bconv (f : ℝ → ℝ) (Fam.approx x y (epsSeq (σ k))))
      = ∫ r, pairTrans Ψ f r ∂(Fam.approxMeasure x y (epsSeq (σ k))) := by
    intro k
    rw [bconv_comm (L1.integrable_coeFn f) (Fam.approx x y (epsSeq (σ k))), hfL,
      apply_bconv Ψ (L1.integrable_coeFn _) f, integral_approxMeasure hx hxy]
  refine tendsto_nhds_unique h1 ?_
  simpa only [h2] using hweak (pairTrans Ψ f)

/-- **`lem:convolution-representation`, existence.** Every cascade family is convolution by a
causal probability measure. -/
theorem exists_isProbabilityMeasure_eq_mconvL1 (hx : 0 ≤ x) (hxy : x ≤ y) :
    ∃ (μ : Measure ℝ) (_ : IsProbabilityMeasure μ), IsCausal μ ∧ Fam.Φ x y = mconvL1 μ := by
  obtain ⟨μ, hprob, hcausal, σ, hσ, hweak⟩ := exists_weak_limit (Fam := Fam) hx hxy
  refine ⟨μ, hprob, hcausal, ContinuousLinearMap.ext fun f => Lp.ext ?_⟩
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun A _ _ => (L1.integrable_coeFn (Fam.Φ x y f)).integrableOn)
    (fun A _ _ => (L1.integrable_coeFn (mconvL1 μ f)).integrableOn) fun A _ _ => ?_
  rw [← setIntegralCLM_apply A (Fam.Φ x y f), ← setIntegralCLM_apply A (mconvL1 μ f),
    apply_eq_integral_pairTrans hx hxy hσ hweak, apply_mconvL1]

/-! ## `μ_{x,y}`, the representing measure

Existence and uniqueness are in hand; naming the measure is a further, and separate, act of
choice. It is taken once here so that every later chapter can write `μ_{x,y}` instead of
re-extracting it from an existential.

Off the index set `0 ≤ x ≤ y` the definition falls back to `δ₀`, which is itself a causal
probability measure. That is what lets the two structural facts below be stated with no
hypotheses at all — only the identification `Φ_{x,y} = μ_{x,y} * ·` needs the restriction.
-/

open Classical in
/-- **`μ_{x,y}`**: the causal probability measure representing `Φ_{x,y}`. -/
noncomputable def repr (Fam : CascadeCore) (x y : ℝ) : Measure ℝ :=
  if h : 0 ≤ x ∧ x ≤ y then
    (exists_isProbabilityMeasure_eq_mconvL1 (Fam := Fam) h.1 h.2).choose
  else Measure.dirac 0

theorem repr_eq_choose (hx : 0 ≤ x) (hxy : x ≤ y) :
    Fam.repr x y = (exists_isProbabilityMeasure_eq_mconvL1 (Fam := Fam) hx hxy).choose := by
  unfold repr
  exact dif_pos ⟨hx, hxy⟩

instance instIsProbabilityMeasureRepr (Fam : CascadeCore) (x y : ℝ) :
    IsProbabilityMeasure (Fam.repr x y) := by
  unfold repr
  split_ifs with h
  · exact (exists_isProbabilityMeasure_eq_mconvL1 (Fam := Fam) h.1 h.2).choose_spec.choose
  · infer_instance

theorem isCausal_repr (Fam : CascadeCore) (x y : ℝ) : IsCausal (Fam.repr x y) := by
  unfold repr
  split_ifs with h
  · exact
      (exists_isProbabilityMeasure_eq_mconvL1 (Fam := Fam) h.1 h.2).choose_spec.choose_spec.1
  · exact isCausal_dirac le_rfl

/-- **`Φ_{x,y} f = μ_{x,y} * f`.** -/
theorem Phi_eq_mconvL1_repr (hx : 0 ≤ x) (hxy : x ≤ y) :
    Fam.Φ x y = mconvL1 (Fam.repr x y) := by
  haveI := (exists_isProbabilityMeasure_eq_mconvL1 (Fam := Fam) hx hxy).choose_spec.choose
  have hspec :=
    (exists_isProbabilityMeasure_eq_mconvL1 (Fam := Fam) hx hxy).choose_spec.choose_spec.2
  rw [mconvL1_congr (repr_eq_choose (Fam := Fam) hx hxy)]
  exact hspec

/-- **`lem:convolution-representation`.** For `0 ≤ x ≤ y` the operator `Φ_{x,y}` is convolution
by a causal probability measure, and by exactly one. -/
theorem existsUnique_repr (hx : 0 ≤ x) (hxy : x ≤ y) :
    ∃ (μ : Measure ℝ) (_ : IsProbabilityMeasure μ), IsCausal μ ∧ Fam.Φ x y = mconvL1 μ ∧
      ∀ (ρ : Measure ℝ) (_ : IsProbabilityMeasure ρ), IsCausal ρ →
        Fam.Φ x y = mconvL1 ρ → ρ = μ :=
  ⟨Fam.repr x y, instIsProbabilityMeasureRepr Fam x y, isCausal_repr Fam x y,
    Phi_eq_mconvL1_repr hx hxy,
    fun _ _ hρ hρeq =>
      mconvL1_injective hρ (isCausal_repr Fam x y)
        (hρeq.symm.trans (Phi_eq_mconvL1_repr hx hxy))⟩

end CascadeCore

end Hemigroup
