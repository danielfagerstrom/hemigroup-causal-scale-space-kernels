/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.Operator

/-!
# `Φ f = μ * f` as a bounded operator on `L¹`

`Operator.lean` proves (A1)–(A5) for `mconv` as an operation on *functions*. The blueprint's
`X` is `L¹(ℝ)`, and `def:cascade-family` speaks of bounded linear operators on it, so stating
the axioms at all requires the operation to descend to a.e.-equivalence classes and to be
packaged as a continuous linear map. That is what this file does.

## The one fact that makes it work

`mconv μ f t = ∫ f(t - r) μ(dr)` sees `f` only through integrals, so it ought to descend. The
proof is a null-set transfer: a `volume`-null set pulls back to a `volume ⊗ μ`-null set along
`(t,r) ↦ t - r`, because that map is quasi-measure-preserving
(`quasiMeasurePreserving_sub`, Mathlib) — Lebesgue measure being translation invariant. Then
`ae_ae_of_ae_prod` turns "null on the product" into "for a.e. `t`, null in `r`", which is
exactly the hypothesis `integral_congr_ae` wants.

That same quasi-measure-preserving map is what let the hypotheses in `Operator.lean` be loosened
from `Measurable` to `AEStronglyMeasurable`, which is all an `Lp` coercion supplies. So this file
adds no analysis: the boundedness constant is `lintegral_enorm_mconv_le`, unchanged, and the rest
is bookkeeping about representatives.
-/

namespace Hemigroup

open MeasureTheory Set
open scoped ENNReal

/-! ## Descent to a.e.-equivalence classes -/

/-- **The null-set transfer.** A property holding `volume`-a.e. holds at `t - r` for a.e. `t`
and `μ`-a.e. `r`. This is the one fact every descent argument below uses: `(t,r) ↦ t - r` is
quasi-measure-preserving from `volume ⊗ μ` to `volume`, so a null set pulls back to a null set
on the product, and `ae_ae_of_ae_prod` turns that into an iterated statement. -/
theorem ae_ae_sub_of_ae (μ : Measure ℝ) [SFinite μ] {p : ℝ → Prop} (h : ∀ᵐ u ∂volume, p u) :
    ∀ᵐ t ∂volume, ∀ᵐ r ∂μ, p (t - r) :=
  Measure.ae_ae_of_ae_prod ((quasiMeasurePreserving_sub volume μ).ae h)

/-- **`mconv` respects a.e. equality**, so it descends to `L¹`. -/
theorem mconv_congr_ae (μ : Measure ℝ) [SFinite μ] {f g : ℝ → ℝ} (h : f =ᵐ[volume] g) :
    mconv μ f =ᵐ[volume] mconv μ g := by
  filter_upwards [ae_ae_sub_of_ae μ h] with t ht
  exact integral_congr_ae ht

/-- Additivity, for a.e. `t`. Not pointwise: splitting the integral needs `r ↦ f(t - r)` and
`r ↦ g(t - r)` to be `μ`-integrable, which `integrable_uncurry_sub` supplies for a.e. `t` only. -/
theorem mconv_add_ae (μ : Measure ℝ) [IsFiniteMeasure μ] {f g : ℝ → ℝ}
    (hf : AEStronglyMeasurable f) (hfi : Integrable f)
    (hg : AEStronglyMeasurable g) (hgi : Integrable g) :
    mconv μ (f + g) =ᵐ[volume] mconv μ f + mconv μ g := by
  filter_upwards [(integrable_uncurry_sub μ hf hfi).prod_right_ae,
    (integrable_uncurry_sub μ hg hgi).prod_right_ae] with t h1 h2
  simp only [Function.uncurry] at h1 h2
  simp only [mconv_apply, Pi.add_apply]
  exact integral_add h1 h2

/-- Homogeneity, pointwise and unconditional — `integral_smul` needs no integrability. -/
theorem mconv_smul (μ : Measure ℝ) (c : ℝ) (f : ℝ → ℝ) :
    mconv μ (c • f) = c • mconv μ f := by
  funext t
  simp only [mconv_apply, Pi.smul_apply, smul_eq_mul, integral_const_mul]

/-! ## The operator on `L¹` -/

/-- `Φ f = μ * f` as a linear map on `L¹`, via the integrable representative. -/
noncomputable def mconvₗ (μ : Measure ℝ) [IsFiniteMeasure μ] :
    (ℝ →₁[volume] ℝ) →ₗ[ℝ] (ℝ →₁[volume] ℝ) where
  toFun f :=
    (integrable_mconv μ (Lp.aestronglyMeasurable f) (L1.integrable_coeFn f)).toL1 _
  map_add' f g := by
    rw [← Integrable.toL1_add]
    refine (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr ?_
    refine (mconv_congr_ae μ (Lp.coeFn_add f g)).trans ?_
    exact mconv_add_ae μ (Lp.aestronglyMeasurable f) (L1.integrable_coeFn f)
      (Lp.aestronglyMeasurable g) (L1.integrable_coeFn g)
  map_smul' c f := by
    simp only [RingHom.id_apply]
    rw [← Integrable.toL1_smul']
    refine (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr ?_
    refine (mconv_congr_ae μ (Lp.coeFn_smul c f)).trans ?_
    rw [mconv_smul]

lemma coeFn_mconvₗ (μ : Measure ℝ) [IsFiniteMeasure μ] (f : ℝ →₁[volume] ℝ) :
    mconvₗ μ f =ᵐ[volume] mconv μ (f : ℝ → ℝ) :=
  Integrable.coeFn_toL1 (integrable_mconv μ (Lp.aestronglyMeasurable f) (L1.integrable_coeFn f))

/-- The `L¹` norm as a lower Lebesgue integral, the form `lintegral_enorm_mconv_le` speaks in. -/
private lemma norm_L1_eq (f : ℝ →₁[volume] ℝ) : ‖f‖ = (∫⁻ t, ‖(f : ℝ → ℝ) t‖ₑ).toReal := by
  rw [Lp.norm_def, eLpNorm_one_eq_lintegral_enorm]

/-- **Axiom (A1)**, in the form `def:cascade-family` states it: `Φ` is a bounded operator on
`L¹`, with norm at most `‖μ‖` — so a contraction for a probability measure.

The bound is `lintegral_enorm_mconv_le`, unchanged; only the packaging is new. -/
noncomputable def mconvL1 (μ : Measure ℝ) [IsFiniteMeasure μ] :
    (ℝ →₁[volume] ℝ) →L[ℝ] (ℝ →₁[volume] ℝ) :=
  (mconvₗ μ).mkContinuous (μ univ).toReal fun f => by
    rw [mconvₗ, LinearMap.coe_mk, AddHom.coe_mk,
      Integrable.norm_toL1_eq_lintegral_enorm, norm_L1_eq, ← ENNReal.toReal_mul]
    refine ENNReal.toReal_mono ?_ (lintegral_enorm_mconv_le μ (Lp.aestronglyMeasurable f))
    exact ENNReal.mul_ne_top (measure_ne_top μ univ) (L1.integrable_coeFn f).2.ne

lemma coeFn_mconvL1 (μ : Measure ℝ) [IsFiniteMeasure μ] (f : ℝ →₁[volume] ℝ) :
    mconvL1 μ f =ᵐ[volume] mconv μ (f : ℝ → ℝ) := coeFn_mconvₗ μ f

end Hemigroup
