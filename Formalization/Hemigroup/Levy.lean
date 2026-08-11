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
import Mathlib.MeasureTheory.Group.Convolution

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

/-! ## An elementary inequality

`1 - e^{-u} ≤ u`, used in two unrelated places — the null-array estimate of chapter 5 and the
admissibility criterion of chapter 8 — which is why it sits here rather than in either. -/

/-- `1 - e^{-u} ≤ u`, so replacing an exponent by `1 - e^{-\text{exponent}}` can only decrease
it. -/
theorem one_sub_exp_neg_le (u : ℝ) : 1 - Real.exp (-u) ≤ u := by
  nlinarith [Real.add_one_le_exp (-u)]

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

/-! ## Lévy exponents, representation-first

`blueprint/DESIGN-formalization-strategy.md` argues for defining admissibility by the
representation rather than by derivative signs, and this is where that begins to pay: the
vanishing lemma below is three lines from the representation, against the blueprint's
concavity argument.

The identification of this notion with the blueprint's Definition 2.2 — smooth with completely
monotone derivative — is the Lévy–Khintchine theorem, ledger entry A3, and is *not* proved
here. That is deliberate and is what the trust boundary is for.
-/

/-- The Lévy exponent with drift `b₀` and Lévy measure `ν`, valued in `ℝ≥0∞`:
`s ↦ b₀ s + ∫ (1 - e^{-st}) ν(dt)`.

This is the right-hand side of the blueprint's (7.1), before the self-decomposability
restriction on `ν`. Valued in `ℝ≥0∞` so that no integrability hypothesis is needed. -/
noncomputable def levyExponent (b₀ : ℝ) (ν : Measure ℝ) (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (b₀ * s) + ∫⁻ t, ENNReal.ofReal (1 - Real.exp (-(s * t))) ∂ν

@[simp] lemma levyExponent_zero (b₀ : ℝ) (ν : Measure ℝ) : levyExponent b₀ ν 0 = 0 := by
  simp [levyExponent]

/-- **The vanishing lemma**, blueprint `lem:vanishing` (Lemma 2.4), in representation form: a
Lévy exponent that vanishes at a single positive point vanishes identically.

The blueprint proves this from concavity and the monotonicity of a completely monotone
derivative. Working from the representation instead, it is just the statement that a sum of
nonnegative terms vanishes only when each does: the drift is killed because `s₀ > 0`, and the
Lévy measure is killed because `1 - e^{-s₀t} > 0` off `t = 0`. -/
theorem levyExponent_eq_zero_of_eq_zero {b₀ : ℝ} {ν : Measure ℝ} (hb : 0 ≤ b₀)
    (hν : IsCausal ν) {s₀ : ℝ} (hs₀ : 0 < s₀) (h : levyExponent b₀ ν s₀ = 0) :
    ∀ s, 0 ≤ s → levyExponent b₀ ν s = 0 := by
  have hmeas : ∀ r : ℝ, Measurable fun t : ℝ => ENNReal.ofReal (1 - Real.exp (-(r * t))) :=
    fun r => (measurable_const.sub ((Real.measurable_exp.comp (by fun_prop)))).ennreal_ofReal
  -- A sum of two terms of `ℝ≥0∞` vanishes only if both do.
  rw [levyExponent, add_eq_zero] at h
  obtain ⟨hdrift, hjump⟩ := h
  -- The drift dies because `s₀ > 0`.
  have hb0 : b₀ = 0 := by
    have := ENNReal.ofReal_eq_zero.mp hdrift
    nlinarith
  -- The Lévy measure is carried by `{0}`, where the integrand vanishes for every `s`.
  have hae : ∀ᵐ t ∂ν, t = 0 := by
    rw [lintegral_eq_zero_iff (hmeas s₀)] at hjump
    filter_upwards [hjump, hν.ae_nonneg] with t ht htpos
    have h1 : 1 - Real.exp (-(s₀ * t)) ≤ 0 := ENNReal.ofReal_eq_zero.mp ht
    by_contra hne
    have htpos' : 0 < t := lt_of_le_of_ne htpos (Ne.symm hne)
    have : Real.exp (-(s₀ * t)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
    linarith
  intro s _
  rw [levyExponent, hb0]
  have : ∫⁻ t, ENNReal.ofReal (1 - Real.exp (-(s * t))) ∂ν = 0 := by
    rw [lintegral_eq_zero_iff (hmeas s)]
    filter_upwards [hae] with t ht
    simp [ht]
  simp [this]

/-! ## Convolution and dilation

The two operations axiom (A6) and axiom (A8) are stated in terms of. Both act on the Laplace
transform in the simplest possible way — convolution multiplies it, dilation reparametrises it —
and that is what lets `Injectivity.lean` turn the exponent identities of `Construction.lean`
into identities between measures.
-/

/-- Convolution of causal measures is causal: `x + y < 0` forces `x < 0` or `y < 0`. -/
lemma IsCausal.conv {μ ν : Measure ℝ} [SFinite μ] [SFinite ν] (hμ : IsCausal μ)
    (hν : IsCausal ν) : IsCausal (μ ∗ ν) := by
  rw [IsCausal, Measure.conv, Measure.map_apply (by fun_prop) measurableSet_Iio]
  have hsub : (fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Iio 0 ⊆ (Iio 0 ×ˢ univ) ∪ (univ ×ˢ Iio 0) := by
    rintro ⟨x, y⟩ h
    simp only [mem_preimage, mem_Iio] at h
    by_contra hc
    simp only [mem_union, mem_prod, mem_Iio, mem_univ, and_true, true_and, not_or, not_lt] at hc
    linarith [hc.1, hc.2]
  refine measure_mono_null hsub (measure_union_null ?_ ?_)
  · rw [Measure.prod_prod, hμ, zero_mul]
  · rw [Measure.prod_prod, hν, mul_zero]

/-- **The Laplace transform turns convolution into multiplication**, with no hypotheses beyond
what makes the convolution well behaved. This is axiom (A6) reduced to arithmetic. -/
lemma laplaceL_conv (μ ν : Measure ℝ) [SFinite ν] (s : ℝ) :
    laplaceL (μ ∗ ν) s = laplaceL μ s * laplaceL ν s := by
  have hf : Measurable fun z : ℝ => ENNReal.ofReal (Real.exp (-(s * z))) := by fun_prop
  rw [laplaceL, Measure.lintegral_conv hf]
  have hinner : ∀ x : ℝ, ∫⁻ y, ENNReal.ofReal (Real.exp (-(s * (x + y)))) ∂ν
      = ENNReal.ofReal (Real.exp (-(s * x))) * laplaceL ν s := by
    intro x
    rw [laplaceL, ← lintegral_const_mul _ (by fun_prop)]
    refine lintegral_congr fun y => ?_
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  simp_rw [hinner]
  rw [lintegral_mul_const _ (by fun_prop)]
  rfl

/-- The real-valued form. Unconditional, because `ENNReal.toReal` is multiplicative. -/
lemma laplace_conv (μ ν : Measure ℝ) [SFinite ν] (s : ℝ) :
    laplace (μ ∗ ν) s = laplace μ s * laplace ν s := by
  rw [laplace_eq_toReal_laplaceL, laplace_eq_toReal_laplaceL, laplace_eq_toReal_laplaceL,
    laplaceL_conv, ENNReal.toReal_mul]

/-- Dilation by `σ > 0` preserves causality. -/
lemma IsCausal.map_const_mul {μ : Measure ℝ} (h : IsCausal μ) {σ : ℝ} (hσ : 0 < σ) :
    IsCausal (μ.map (fun t => σ * t)) := by
  rw [IsCausal, Measure.map_apply (by fun_prop) measurableSet_Iio]
  refine measure_mono_null (fun t ht => ?_) h
  simp only [mem_preimage, mem_Iio] at ht
  exact mem_Iio.mpr (by nlinarith)

/-- **Dilation reparametrises the transform**: `(D_σ μ)ˆ(s) = μˆ(σ s)`. This is axiom (A8)
reduced to arithmetic. -/
lemma laplace_map_const_mul (μ : Measure ℝ) {σ : ℝ} (hσ : 0 < σ) (s : ℝ) :
    laplace (μ.map (fun t => σ * t)) s = laplace μ (σ * s) := by
  have hemb : MeasurableEmbedding (fun t : ℝ => σ * t) :=
    (Homeomorph.mulLeft₀ σ hσ.ne').toMeasurableEquiv.measurableEmbedding
  rw [laplace, hemb.integral_map, laplace]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  dsimp only
  congr 1
  ring

end Hemigroup
