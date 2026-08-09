/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.Levy
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The operators `Φ_{x,y} f = μ_{x,y} * f`, and axioms (A1)–(A5)

The last block of `thm:main-characterization` (⇐). Blueprint: `def:cascade-family`, clauses
(A1)–(A5).

These are the axioms about the operators *as operators on* `X = L¹`, and unlike (A6)–(A8) they
say nothing about the family — each is a statement about a single convolution. There is no new
analysis in them: (A2) and (A4) are one line each, (A3) is causality of `μ` read through the
integrand, and (A1) and (A5) are Tonelli plus translation invariance of Lebesgue measure.

**State.** (A1)–(A4) are proved. (A5), unit area, is proved in its `ℝ≥0∞` form — that *is*
`lintegral_lintegral_sub_eq`, which for `g = ENNReal.ofReal ∘ f` with `f ≥ 0` says exactly that
convolution preserves mass. What is not written is the Bochner restatement
`∫ (μ * f) = ‖μ‖ ∫ f`, which needs the integrability bookkeeping to move between the two
integrals and to know `μ * f` is itself integrable; that in turn wants a
measurability-of-a-parametric-integral lemma. It is bookkeeping, but it is not free, and it is
not here.

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

end Hemigroup
