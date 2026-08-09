/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.Instance
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

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

end Hemigroup
