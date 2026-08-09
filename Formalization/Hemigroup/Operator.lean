/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.Levy
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral

/-!
# The operators `Φ_{x,y} f = μ_{x,y} * f`, and axioms (A1)–(A5)

The last block of `thm:main-characterization` (⇐). Blueprint: `def:cascade-family`, clauses
(A1)–(A5).

These are the axioms about the operators *as operators on* `X = L¹`, and unlike (A6)–(A8) they
say nothing about the family — each is a statement about a single convolution. There is no new
analysis in them: (A2) and (A4) are one line each, (A3) is causality of `μ` read through the
integrand, and (A1) and (A5) are Tonelli plus translation invariance of Lebesgue measure.

**State: all five are proved**, and everything here is Lean core.

`lintegral_lintegral_sub_eq` is the one lemma the two analytic clauses share, and it is used
twice over in different registers: first to *estimate*, giving (A1); then to establish
integrability on the product (`integrable_uncurry_sub`), which is what licenses the Bochner swap
and so gives (A5) as `integral_mconv`, and simultaneously gives `integrable_mconv` — that `Φ`
maps `L¹` into `L¹`, the other half of (A1).

## A note on `(A3)`

The blueprint states causality as "if `f` vanishes a.e. on `(-∞,t₀)` then so does `Φ f`". The
`a.e.` on the hypothesis side cannot be taken pointwise in the conclusion: for `μ = δ_{r₀}` the
value `(μ * f)(t) = f(t - r₀)` samples `f` at a single point, which an a.e. hypothesis does not
control. The honest pointwise statement takes a pointwise hypothesis, which is what
`mconv_eq_zero_of_lt` does; the a.e. form then follows for a.e. `t` by Fubini, and is not
needed here.
-/

namespace Hemigroup

open MeasureTheory Set
open scoped ENNReal

/-- `Φ f = μ * f`, the convolution of a measure with a function:
`(μ * f)(t) = ∫ f(t - r) μ(dr)`. -/
noncomputable def mconv (μ : Measure ℝ) (f : ℝ → ℝ) : ℝ → ℝ := fun t => ∫ r, f (t - r) ∂μ

lemma mconv_apply (μ : Measure ℝ) (f : ℝ → ℝ) (t : ℝ) :
    mconv μ f t = ∫ r, f (t - r) ∂μ := rfl

/-! ## (A2) Time-translation covariance -/

/-- **Axiom (A2)**: convolution commutes with translation. -/
theorem mconv_comp_sub (μ : Measure ℝ) (f : ℝ → ℝ) (a : ℝ) :
    mconv μ (fun t => f (t - a)) = fun t => mconv μ f (t - a) := by
  funext t
  simp only [mconv_apply, sub_right_comm]

/-! ## (A4) Positivity -/

/-- **Axiom (A4)**: convolution preserves the positive cone. -/
theorem mconv_nonneg (μ : Measure ℝ) {f : ℝ → ℝ} (hf : ∀ t, 0 ≤ f t) (t : ℝ) :
    0 ≤ mconv μ f t := integral_nonneg fun _ => hf _

/-! ## (A3) Causality -/

/-- **Axiom (A3)**: a causal measure cannot move mass backwards. If `f` vanishes strictly before
`t₀`, so does `μ * f`. -/
theorem mconv_eq_zero_of_lt {μ : Measure ℝ} (hμ : IsCausal μ) {f : ℝ → ℝ} {t₀ : ℝ}
    (hf : ∀ t, t < t₀ → f t = 0) {t : ℝ} (ht : t < t₀) : mconv μ f t = 0 := by
  rw [mconv_apply]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hμ.ae_nonneg] with r hr
  exact hf _ (by linarith)

/-! ## (A1) and (A5): Tonelli

Both come from the same swap. `‖·‖ₑ` keeps everything in `ℝ≥0∞`, so no integrability side
condition is needed to perform it; the real-valued statements are read off afterwards.
-/

/-- **The Tonelli identity.** Integrating `t ↦ ∫ g(t - r) μ(dr)` over `ℝ` gives `‖μ‖` times the
integral of `g`. The swap is legitimate with no integrability hypothesis because everything is
`ℝ≥0∞`-valued, and the inner integral is unchanged by the translation because Lebesgue measure
is translation invariant.

Both (A1) and (A5) are read off this: (A1) by taking `g = ‖f ·‖ₑ` (below), **(A5)** by taking
`g = ENNReal.ofReal ∘ f` for `f ≥ 0`, where the statement reads
`∫⁻ (μ * f) = ‖μ‖ · ∫⁻ f` — unit area. -/
theorem lintegral_lintegral_sub_eq (μ : Measure ℝ) [SFinite μ] {g : ℝ → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ t, (∫⁻ r, g (t - r) ∂μ) = μ univ * ∫⁻ t, g t := by
  have huncurry : Measurable (Function.uncurry fun t r : ℝ => g (t - r)) :=
    hg.comp (measurable_fst.sub measurable_snd)
  calc ∫⁻ t, (∫⁻ r, g (t - r) ∂μ)
      = ∫⁻ r, (∫⁻ t, g (t - r) ∂volume) ∂μ :=
        lintegral_lintegral_swap huncurry.aemeasurable
    _ = ∫⁻ _, (∫⁻ t, g t) ∂μ := lintegral_congr fun r => lintegral_sub_right_eq_self _ r
    _ = μ univ * ∫⁻ t, g t := by rw [lintegral_const, mul_comm]

/-- **Axiom (A1)**, as an `L¹` bound: `∫ ‖μ * f‖ ≤ ‖μ‖ · ∫ ‖f‖`. For a probability measure the
factor is `1`, so `Φ` is a contraction. -/
theorem lintegral_enorm_mconv_le (μ : Measure ℝ) [SFinite μ] {f : ℝ → ℝ} (hf : Measurable f) :
    ∫⁻ t, ‖mconv μ f t‖ₑ ≤ μ univ * ∫⁻ t, ‖f t‖ₑ := by
  calc ∫⁻ t, ‖mconv μ f t‖ₑ ≤ ∫⁻ t, (∫⁻ r, ‖f (t - r)‖ₑ ∂μ) :=
        lintegral_mono fun t => enorm_integral_le_lintegral_enorm _
    _ = μ univ * ∫⁻ t, ‖f t‖ₑ := lintegral_lintegral_sub_eq μ hf.enorm

/-! ## (A5) for the Bochner integral

The `ℝ≥0∞` identity above is unit area already. Restating it for `∫` needs the two-variable
integrand to be integrable on the product — which is exactly what the same Tonelli bound gives,
now used to *establish* integrability rather than to estimate.
-/

/-- The two-variable integrand is integrable on `volume ⊗ μ`. This is the hypothesis both the
Bochner swap and the integrability of `μ * f` are waiting on. -/
theorem integrable_uncurry_sub (μ : Measure ℝ) [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hf : Measurable f) (hfi : Integrable f) :
    Integrable (Function.uncurry fun t r : ℝ => f (t - r)) (volume.prod μ) := by
  have hm : Measurable (Function.uncurry fun t r : ℝ => f (t - r)) :=
    hf.comp (measurable_fst.sub measurable_snd)
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  have hprod : ∫⁻ p, ‖Function.uncurry (fun t r : ℝ => f (t - r)) p‖ₑ ∂(volume.prod μ)
      = ∫⁻ t, (∫⁻ r, ‖f (t - r)‖ₑ ∂μ) := lintegral_prod _ hm.enorm.aemeasurable
  rw [hasFiniteIntegral_iff_enorm, hprod, lintegral_lintegral_sub_eq μ hf.enorm]
  exact ENNReal.mul_lt_top (measure_lt_top μ univ) hfi.2

/-- `μ * f` is itself integrable — the statement that `Φ` maps `L¹` into `L¹`, which is the
other half of (A1). -/
theorem integrable_mconv (μ : Measure ℝ) [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hf : Measurable f) (hfi : Integrable f) : Integrable (mconv μ f) := by
  exact (integrable_uncurry_sub μ hf hfi).integral_prod_left

/-- **Axiom (A5), unit area**, for the Bochner integral: `∫ (μ * f) = ‖μ‖ ∫ f`. For a
probability measure this is exactly `∫ Φ f = ∫ f`. -/
theorem integral_mconv (μ : Measure ℝ) [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hf : Measurable f) (hfi : Integrable f) :
    ∫ t, mconv μ f t = (μ univ).toReal * ∫ t, f t := by
  simp only [mconv_apply]
  rw [integral_integral_swap (integrable_uncurry_sub μ hf hfi)]
  simp_rw [integral_sub_right_eq_self]
  rw [integral_const, smul_eq_mul, measureReal_def]

end Hemigroup
