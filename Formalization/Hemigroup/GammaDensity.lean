/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.GammaKernels
import Mathlib.Probability.Distributions.Gamma

/-!
# `prop:gamma-density`: the Gamma family's kernel *is* the Gamma law

Blueprint: `prop:gamma-density`. For `F(s) = γ log(1+s)` the kernel `μ_{0,x}` is the Gamma
distribution of shape `γ` and rate `1/x` — the density `φ_x(t) = t^{γ-1}e^{-t/x}/(Γ(γ)x^γ)` the
blueprint writes out.

## Stated as an identity of measures, not of densities

The blueprint gives `φ_x` pointwise. Here the conclusion is
`kernel 0 x = ProbabilityTheory.gammaMeasure γ x⁻¹`, which says the same thing in the vocabulary
Mathlib already has: `gammaPDFReal a r t = r^a/Γ(a) · t^{a-1}e^{-rt}`, which at `a = γ`, `r = 1/x`
is exactly `φ_x`. Naming the law rather than its density is also what makes the statement useful —
everything Mathlib proves about `gammaMeasure` becomes available to the article, which is the
route by which `prop:gamma-moments` can retire its ledger entry.

## The route is the transform, and `kernel_unique` is what makes it enough

`(1+xs)^{-γ}` is the Gamma law's Laplace transform, and `kernel_unique` then identifies the
measure: it is Laplace injectivity on causal measures (`prop:laplace-uniqueness-causal`) packaged
for exactly this use, and the blueprint's proof names it.

**Mathlib has no transform for `gammaMeasure`** — no Laplace, no moment generating function, no
characteristic function; `Probability/Distributions/Gamma.lean` carries the density, the total
mass and the CDF and stops. So `laplace_gammaMeasure` is computed here, from
`integral_rpow_mul_exp_neg_mul_Ioi` — the same Gamma integral chapter 8 used for the stable
family's `F'`. That computation is the whole of the "separate piece of work" the node's status
line predicted, and the prediction was accurate.
-/

namespace Hemigroup

open MeasureTheory Set ProbabilityTheory

open scoped ENNReal

namespace SelfDecomposableExponent

variable {γ : ℝ}

/-- The Gamma law is carried by `[0,∞)`. -/
theorem isCausal_gammaMeasure {a r : ℝ} : IsCausal (gammaMeasure a r) := by
  rw [IsCausal, gammaMeasure, withDensity_apply _ measurableSet_Iio,
    setLIntegral_congr_fun measurableSet_Iio fun t ht => gammaPDF_of_neg (mem_Iio.mp ht),
    lintegral_zero]

/-- **The Gamma law's Laplace transform**: `E[e^{-sT}] = (r/(r+s))^a`.

Mathlib carries the Gamma density, its total mass and its CDF, but not this, so it is computed
here — the Gamma integral `∫₀^∞ t^{a-1}e^{-(r+s)t}dt = Γ(a)/(r+s)^a` and nothing else. -/
theorem laplace_gammaMeasure {a r s : ℝ} (ha : 0 < a) (hr : 0 < r) (hs : 0 ≤ s) :
    laplace (gammaMeasure a r) s = (r / (r + s)) ^ a := by
  have hrs : (0 : ℝ) < r + s := by linarith
  have hΓ : (0 : ℝ) < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have hcompl : ∀ᵐ t ∂volume, t ∉ Ioi (0 : ℝ) →
      (gammaPDF a r t).toReal • Real.exp (-(s * t)) = 0 := by
    filter_upwards [compl_mem_ae_iff.mpr (Real.volume_singleton (a := (0 : ℝ)))] with t htne hnot
    have hneg : t < 0 := lt_of_le_of_ne (not_lt.mp (by simpa using hnot)) (by simpa using htne)
    rw [gammaPDF_of_neg hneg, ENNReal.toReal_zero, zero_smul]
  have hpt : ∀ t ∈ Ioi (0 : ℝ), (gammaPDF a r t).toReal • Real.exp (-(s * t))
      = r ^ a / Real.Gamma a * (t ^ (a - 1) * Real.exp (-((r + s) * t))) := by
    intro t ht
    rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr t), smul_eq_mul,
      gammaPDFReal, if_pos (le_of_lt (mem_Ioi.mp ht)),
      show -((r + s) * t) = -(r * t) + -(s * t) by ring, Real.exp_add]
    ring
  rw [laplace, gammaMeasure, integral_withDensity_eq_integral_toReal_smul₀
      (f := gammaPDF a r) ((measurable_gammaPDFReal a r).ennreal_ofReal.aemeasurable)
      (.of_forall fun _ => ENNReal.ofReal_lt_top),
    ← setIntegral_eq_integral_of_ae_compl_eq_zero hcompl,
    setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    Real.integral_rpow_mul_exp_neg_mul_Ioi ha hrs, one_div, Real.inv_rpow hrs.le,
    Real.div_rpow hr.le hrs.le]
  have hrsa : (0 : ℝ) < (r + s) ^ a := Real.rpow_pos_of_pos hrs a
  field_simp

/-- **`prop:gamma-density`**: the Gamma family's kernel is the Gamma law of shape `γ` and rate
`1/x` — that is, the density is `φ_x(t) = t^{γ-1}e^{-t/x}/(Γ(γ)x^γ)`.

`kernel_unique` and the transform: two causal measures with the same Laplace transform on
`[0,∞)` are equal, which is `prop:laplace-uniqueness-causal`. -/
theorem gammaExponent_kernel_eq_gammaMeasure (hγ : 0 < γ) {x : ℝ} (hx : 0 < x) :
    (gammaExponent γ hγ.le).kernel 0 x = gammaMeasure γ x⁻¹ := by
  haveI : IsProbabilityMeasure (gammaMeasure γ x⁻¹) :=
    isProbabilityMeasure_gammaMeasure hγ (inv_pos.mpr hx)
  refine ((gammaExponent γ hγ.le).kernel_unique (μ := gammaMeasure γ x⁻¹)
    isCausal_gammaMeasure le_rfl hx.le fun s hs => ?_).symm
  rw [← laplace_kernel le_rfl hx.le hs]
  rcases hs.eq_or_lt with rfl | hspos
  · rw [laplace_gammaMeasure hγ (inv_pos.mpr hx) le_rfl, add_zero, div_self (inv_pos.mpr hx).ne',
      Real.one_rpow, laplace_kernel le_rfl hx.le le_rfl, increment_zero_left hx.le,
      mul_zero, show ((gammaExponent γ hγ.le).exponent 0).toReal
        = (gammaExponent γ hγ.le).toRealExponent 0 from rfl]
    simp [toRealExponent, exponent, levyExponentD, levyJump]
  · rw [laplace_gammaMeasure hγ (inv_pos.mpr hx) hs,
      gammaExponent_laplace_kernel hγ.le hx hspos]
    have hxs : (0 : ℝ) < 1 + x * s := by positivity
    rw [show x⁻¹ / (x⁻¹ + s) = (1 + x * s)⁻¹ by field_simp,
      ← Real.rpow_neg_one (1 + x * s), ← Real.rpow_mul hxs.le]
    norm_num

end SelfDecomposableExponent

end Hemigroup
