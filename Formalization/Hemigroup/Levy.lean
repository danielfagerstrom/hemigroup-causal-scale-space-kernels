/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Causal measures and their Laplace transforms

M0 of the formalisation ladder: the vocabulary the rest of the development is stated in.

Blueprint: `blueprint/src/parts/02-preliminaries.tex`, Chapter 2, the notation preamble.
Nothing here is a blueprint node yet — this supplies the *objects* that Chapter 2's statements
quantify over, so that `lem:vanishing` and the rest have something to be about.

## Design

Two decisions, both taken from `blueprint/DESIGN-formalization-strategy.md`.

* Measures on `ℝ` carried by `[0,∞)`, not a bespoke half-line type. The article's kernels are
  convolved constantly — axiom (A6) is a convolution identity — so `Measure.conv` and its API,
  which live on a group, must stay applicable. Carrying a causality *predicate* keeps them; a
  subtype `Ici 0` would not.
* An `ℝ≥0∞`-valued transform first, real-valued second. The `lintegral` version needs no
  integrability side condition, so the elementary facts below are unconditional; the real
  version is derived from it, carrying the hypotheses.
-/

namespace Hemigroup

open MeasureTheory Set
open scoped ENNReal

/-! ## Causal measures -/

/-- A measure on `ℝ` is *causal* when it is carried by `[0,∞)`.

The article's kernels `μ_{x,y}` are causal by axiom (A3); this is that condition, stated so
that the ambient space stays `ℝ` and the convolution API remains applicable. -/
def IsCausal (μ : Measure ℝ) : Prop := μ (Iio 0) = 0

lemma isCausal_iff_ae (μ : Measure ℝ) : IsCausal μ ↔ ∀ᵐ t ∂μ, 0 ≤ t := by
  rw [IsCausal, ae_iff]
  simp only [not_le]
  rfl

lemma IsCausal.ae_nonneg {μ : Measure ℝ} (h : IsCausal μ) : ∀ᵐ t ∂μ, 0 ≤ t :=
  (isCausal_iff_ae μ).mp h

lemma isCausal_dirac {a : ℝ} (ha : 0 ≤ a) : IsCausal (Measure.dirac a) := by
  simp [IsCausal, Measure.dirac_apply' _ measurableSet_Iio, not_lt.mpr ha]

/-! ## The Laplace transform -/

/-- The Laplace transform of a measure on the half-line, valued in `ℝ≥0∞`.

Unconditional: no integrability hypothesis is needed, which is why this is the primitive and
`laplace` below is derived from it. -/
noncomputable def laplaceL (μ : Measure ℝ) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ t, ENNReal.ofReal (Real.exp (-(s * t))) ∂μ

/-- The Laplace transform as a real number. Equal to `laplaceL` under the hypotheses of
`laplaceL_ne_top_of_causal`, which is the only regime the article uses. -/
noncomputable def laplace (μ : Measure ℝ) (s : ℝ) : ℝ :=
  ∫ t, Real.exp (-(s * t)) ∂μ

@[simp] lemma laplaceL_zero_measure (s : ℝ) : laplaceL 0 s = 0 := by simp [laplaceL]

lemma laplaceL_zero (μ : Measure ℝ) : laplaceL μ 0 = μ univ := by
  simp [laplaceL]

/-- On a causal measure the integrand is bounded by `1` for `s ≥ 0`, so the transform is
bounded by the total mass. This is the estimate every later bound reduces to. -/
lemma laplaceL_le_mass {μ : Measure ℝ} (h : IsCausal μ) {s : ℝ} (hs : 0 ≤ s) :
    laplaceL μ s ≤ μ univ := by
  calc laplaceL μ s ≤ ∫⁻ _, 1 ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [h.ae_nonneg] with t ht
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr (by nlinarith))
    _ = μ univ := by simp

lemma laplaceL_ne_top_of_causal {μ : Measure ℝ} [IsFiniteMeasure μ] (h : IsCausal μ) {s : ℝ}
    (hs : 0 ≤ s) : laplaceL μ s ≠ ⊤ :=
  ((laplaceL_le_mass h hs).trans_lt (measure_lt_top μ univ)).ne

/-- A probability measure has transform `1` at the origin: the normalisation behind
`g_{x,y}(0+) = 0` in the article. -/
@[simp] lemma laplaceL_zero_prob (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    laplaceL μ 0 = 1 := by
  rw [laplaceL_zero, measure_univ]

/-- The transform is antitone in `s` on a causal measure: more damping, less mass. -/
lemma laplaceL_antitone {μ : Measure ℝ} (h : IsCausal μ) :
    ∀ ⦃s₁ s₂ : ℝ⦄, 0 ≤ s₁ → s₁ ≤ s₂ → laplaceL μ s₂ ≤ laplaceL μ s₁ := by
  intro s₁ s₂ _ h₁₂
  refine lintegral_mono_ae ?_
  filter_upwards [h.ae_nonneg] with t ht
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by nlinarith))

/-- Integrability of the exponential against a finite causal measure, for `s ≥ 0`. The bridge
from `laplaceL` to `laplace`. -/
lemma integrable_exp_of_causal {μ : Measure ℝ} [IsFiniteMeasure μ] (h : IsCausal μ) {s : ℝ}
    (hs : 0 ≤ s) : Integrable (fun t => Real.exp (-(s * t))) μ := by
  refine ⟨(Real.continuous_exp.comp (by fun_prop)).aestronglyMeasurable, ?_⟩
  have : ∀ᵐ t ∂μ, ‖Real.exp (-(s * t))‖ ≤ 1 := by
    filter_upwards [h.ae_nonneg] with t ht
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  exact (hasFiniteIntegral_const (1 : ℝ)).mono (by simpa using this)

/-- The real and `ℝ≥0∞` transforms agree, with no hypotheses at all: the integrand is
everywhere finite, and in the degenerate case where the `lintegral` is `⊤` both sides are `0`
by the Bochner convention. -/
lemma laplace_eq_toReal_laplaceL (μ : Measure ℝ) (s : ℝ) :
    laplace μ s = (laplaceL μ s).toReal := by
  rw [laplace, laplaceL, ← integral_toReal]
  · refine integral_congr_ae ?_
    filter_upwards with t
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
  · exact ((Real.continuous_exp.comp (by fun_prop)).aemeasurable.ennreal_ofReal)
  · filter_upwards with t using ENNReal.ofReal_lt_top

/-- The transform of a nonzero causal measure is strictly positive: the fact behind
"`\hat\mu(s) > 0` for all `s ≥ 0`" in the article's Chapter 2 preamble, and what makes
`g = -log \hat\mu` well defined. -/
lemma laplace_pos {μ : Measure ℝ} [IsFiniteMeasure μ] (h : IsCausal μ) (hμ : μ ≠ 0) {s : ℝ}
    (hs : 0 ≤ s) : 0 < laplace μ s := by
  rw [laplace]
  refine (integral_pos_iff_support_of_nonneg ?_ (integrable_exp_of_causal h hs)).mpr ?_
  · exact fun t => (Real.exp_pos _).le
  · have : Function.support (fun t => Real.exp (-(s * t))) = univ :=
      Set.eq_univ_of_forall fun t => (Real.exp_pos _).ne'
    rw [this]
    exact (Measure.measure_univ_pos.mpr hμ).bot_lt

end Hemigroup
