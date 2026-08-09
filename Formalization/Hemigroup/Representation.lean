/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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

end Hemigroup
