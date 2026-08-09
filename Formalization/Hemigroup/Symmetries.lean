/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.OperatorL1
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The two symmetries of `L¹`: translation `τ_a` and dilation `D_σ`

`def:cascade-family` states (A2) as `Φ τ_a = τ_a Φ` and (A8) as
`D_σ Φ_{x,y} = Φ_{S_σ x, S_σ y} D_σ`, so both operators have to exist on `X = L¹(ℝ)` before
either axiom can be *stated*. Mathlib has neither:

* `Lp.compMeasurePreserving` is an `AddMonoidHom`, not a continuous linear map, and it is anyway
  the wrong shape for `D_σ`;
* `t ↦ t/σ` is not measure preserving — it scales Lebesgue measure — so the dilation that
  preserves mass carries the Jacobian, `(D_σ f)(t) = σ^{-1} f(σ^{-1} t)`. That normalisation is
  what makes `D_σ` an isometry of `L¹` and what matches the measure-side `\dil_σ` of
  `kernel_map_const_mul`, which is pushforward along `t ↦ σ t`.

Both are built on the pattern `OperatorL1.lean` established: work with an integrable
representative, descend along a quasi-measure-preserving change of variables, package with
`LinearMap.mkContinuous`. Both are isometries, so the constant is `1`.
-/

namespace Hemigroup

open MeasureTheory Set
open scoped ENNReal

/-! ## Translation -/

/-- `t ↦ t - a` preserves Lebesgue measure. -/
theorem measurePreserving_sub_const (a : ℝ) :
    MeasurePreserving (fun t : ℝ => t - a) volume volume := by
  simpa [sub_eq_add_neg] using measurePreserving_add_right (volume : Measure ℝ) (-a)

theorem translate_congr_ae (a : ℝ) {f g : ℝ → ℝ} (h : f =ᵐ[volume] g) :
    (fun t => f (t - a)) =ᵐ[volume] fun t => g (t - a) :=
  (measurePreserving_sub_const a).quasiMeasurePreserving.ae h

theorem integrable_translate {f : ℝ → ℝ} (hf : Integrable f) (a : ℝ) :
    Integrable (fun t => f (t - a)) :=
  ((measurePreserving_sub_const a).integrable_comp hf.aestronglyMeasurable).mpr hf

/-- `τ_a f = f(· - a)` as a linear map on `L¹`. -/
noncomputable def transₗ (a : ℝ) : (ℝ →₁[volume] ℝ) →ₗ[ℝ] (ℝ →₁[volume] ℝ) where
  toFun f := (integrable_translate (L1.integrable_coeFn f) a).toL1 _
  map_add' f g := by
    rw [← Integrable.toL1_add]
    exact (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr (translate_congr_ae a (Lp.coeFn_add f g))
  map_smul' c f := by
    simp only [RingHom.id_apply]
    rw [← Integrable.toL1_smul']
    exact (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr (translate_congr_ae a (Lp.coeFn_smul c f))

/-- **Translation is an isometry of `L¹`** — Lebesgue measure is translation invariant. -/
noncomputable def transL1 (a : ℝ) : (ℝ →₁[volume] ℝ) →L[ℝ] (ℝ →₁[volume] ℝ) :=
  (transₗ a).mkContinuous 1 fun f => by
    rw [transₗ, LinearMap.coe_mk, AddHom.coe_mk, Integrable.norm_toL1_eq_lintegral_enorm,
      one_mul, Lp.norm_def, eLpNorm_one_eq_lintegral_enorm]
    exact le_of_eq (congrArg ENNReal.toReal
      (lintegral_sub_right_eq_self (fun x => ‖(f : ℝ → ℝ) x‖ₑ) a))

lemma coeFn_transL1 (a : ℝ) (f : ℝ →₁[volume] ℝ) :
    transL1 a f =ᵐ[volume] fun t => (f : ℝ → ℝ) (t - a) :=
  Integrable.coeFn_toL1 (integrable_translate (L1.integrable_coeFn f) a)

/-! ## Dilation

`D_σ f = σ^{-1} f(σ^{-1} ·)`, the normalisation that preserves `∫ f`.
-/

/-- Multiplication by a nonzero constant is quasi-measure-preserving: it scales Lebesgue
measure by a finite nonzero factor, which is absolute continuity in both directions. -/
theorem quasiMeasurePreserving_const_mul {c : ℝ} (hc : c ≠ 0) :
    Measure.QuasiMeasurePreserving (fun t : ℝ => c * t) volume volume := by
  refine ⟨measurable_const_mul c, ?_⟩
  rw [Real.map_volume_mul_left hc]
  exact Measure.smul_absolutelyContinuous

/-- `D_σ f = σ^{-1} f(σ^{-1} ·)`. -/
noncomputable def dilate (σ : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := fun t => σ⁻¹ * f (σ⁻¹ * t)

theorem dilate_congr_ae {σ : ℝ} (hσ : σ ≠ 0) {f g : ℝ → ℝ} (h : f =ᵐ[volume] g) :
    dilate σ f =ᵐ[volume] dilate σ g := by
  filter_upwards [(quasiMeasurePreserving_const_mul (inv_ne_zero hσ)).ae h] with t ht
  simp only [dilate, ht]

theorem integrable_dilate {f : ℝ → ℝ} (hf : Integrable f) {σ : ℝ} (hσ : σ ≠ 0) :
    Integrable (dilate σ f) :=
  (Integrable.comp_mul_left' hf (inv_ne_zero hσ)).const_mul σ⁻¹

/-- The change of variables the isometry rests on: `∫⁻ g(c t) dt = |c|^{-1} ∫⁻ g`. -/
theorem lintegral_comp_const_mul {c : ℝ} (hc : c ≠ 0) {g : ℝ → ℝ≥0∞} (hg : AEMeasurable g) :
    ∫⁻ t, g (c * t) = ENNReal.ofReal |c⁻¹| * ∫⁻ t, g t := by
  have hmap := Real.map_volume_mul_left hc
  calc ∫⁻ t, g (c * t)
      = ∫⁻ y, g y ∂(Measure.map (fun t : ℝ => c * t) volume) := by
        rw [lintegral_map' (hg.mono_ac (by rw [hmap]; exact Measure.smul_absolutelyContinuous))
          (measurable_const_mul c).aemeasurable]
    _ = ENNReal.ofReal |c⁻¹| * ∫⁻ t, g t := by
        rw [hmap, lintegral_smul_measure, smul_eq_mul]

/-- `D_σ` as a linear map on `L¹`. -/
noncomputable def dilₗ {σ : ℝ} (hσ : σ ≠ 0) : (ℝ →₁[volume] ℝ) →ₗ[ℝ] (ℝ →₁[volume] ℝ) where
  toFun f := (integrable_dilate (L1.integrable_coeFn f) hσ).toL1 _
  map_add' f g := by
    rw [← Integrable.toL1_add]
    refine (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr ?_
    refine (dilate_congr_ae hσ (Lp.coeFn_add f g)).trans ?_
    filter_upwards with t
    simp only [dilate, Pi.add_apply, mul_add]
  map_smul' c f := by
    simp only [RingHom.id_apply]
    rw [← Integrable.toL1_smul']
    refine (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr ?_
    refine (dilate_congr_ae hσ (Lp.coeFn_smul c f)).trans ?_
    filter_upwards with t
    simp only [dilate, Pi.smul_apply, smul_eq_mul]
    ring

/-- **Dilation is an isometry of `L¹`** for `σ > 0` — the `σ^{-1}` normalisation exactly
cancels the Jacobian. -/
noncomputable def dilL1 {σ : ℝ} (hσ : 0 < σ) : (ℝ →₁[volume] ℝ) →L[ℝ] (ℝ →₁[volume] ℝ) :=
  (dilₗ hσ.ne').mkContinuous 1 fun f => by
    rw [dilₗ, LinearMap.coe_mk, AddHom.coe_mk, Integrable.norm_toL1_eq_lintegral_enorm,
      one_mul, Lp.norm_def, eLpNorm_one_eq_lintegral_enorm]
    refine le_of_eq (congrArg ENNReal.toReal ?_)
    have henorm : ∀ t : ℝ, ‖dilate σ (f : ℝ → ℝ) t‖ₑ
        = ENNReal.ofReal σ⁻¹ * ‖(f : ℝ → ℝ) (σ⁻¹ * t)‖ₑ := by
      intro t
      simp only [dilate, enorm_mul, Real.enorm_eq_ofReal (inv_nonneg.mpr hσ.le)]
    simp only [henorm]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_comp_const_mul (inv_ne_zero hσ.ne') (Lp.aestronglyMeasurable f).enorm,
      ← mul_assoc, inv_inv, abs_of_pos hσ, ← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hσ)),
      inv_mul_cancel₀ hσ.ne', ENNReal.ofReal_one, one_mul]

lemma coeFn_dilL1 {σ : ℝ} (hσ : 0 < σ) (f : ℝ →₁[volume] ℝ) :
    dilL1 hσ f =ᵐ[volume] dilate σ (f : ℝ → ℝ) :=
  Integrable.coeFn_toL1 (integrable_dilate (L1.integrable_coeFn f) hσ.ne')

/-! ## (A8) at the level of functions -/

/-- **(A8) at the level of functions**: `D_σ (μ * f) = (D_σ μ) * (D_σ f)`, where the dilation
of the measure is pushforward along `t ↦ σ t`.

Unlike (A6) this is *pointwise*, at every `t`: the change of variables happens inside a single
integral and no Fubini is involved. `f` is asked to be genuinely measurable because `mconv`
against an arbitrary `μ` is not blind to null sets of `volume`; the `L¹` statement below moves
to a measurable representative first. -/
theorem dilate_mconv {σ : ℝ} (hσ : 0 < σ) (μ : Measure ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    dilate σ (mconv μ f) = mconv (μ.map (fun t => σ * t)) (dilate σ f) := by
  have hmeas : Measurable (dilate σ f) := (hf.comp (measurable_const_mul σ⁻¹)).const_mul σ⁻¹
  funext t
  have hcomp : AEStronglyMeasurable (fun u : ℝ => dilate σ f (t - u))
      (μ.map (fun t => σ * t)) :=
    (hmeas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  rw [mconv_apply, integral_map (measurable_const_mul σ).aemeasurable hcomp]
  have harg : ∀ r : ℝ, σ⁻¹ * (t - σ * r) = σ⁻¹ * t - r := fun r => by
    field_simp
  simp only [dilate, harg]
  rw [integral_const_mul]
  rfl

end Hemigroup
