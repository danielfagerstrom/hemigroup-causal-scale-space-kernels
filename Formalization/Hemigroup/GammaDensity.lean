/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
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

/-! ## `prop:gamma-moments`: the higher moments, off the ledger

The blueprint routes this through `prop:moment-criterion` and hence ledger **A7**, and its own
annotation records the alternative: "with the density in hand the moments are a Gamma computation
and the ledger entry is not needed. Whichever is done first makes the other cheap."
`prop:gamma-density` was done first, so this is the cheap one.

Mathlib carries no moments for `gammaMeasure` either, so they are computed here from the same
Gamma integral the transform used — `∫₀^∞ t^{a+n-1}e^{-rt}dt = Γ(a+n)/r^{a+n}` — which is one
lemma serving three purposes in this file.
-/

/-- The Gamma integral at shifted shape, with a rate: the one fact every moment below reduces to.
-/
theorem integrableOn_rpow_shift_mul_exp {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (n : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ (a + (n : ℝ) - 1) * Real.exp (-(r * t))) (Ioi 0) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a + (n : ℝ) - 1) (b := r)
    (by linarith) le_rfl hr
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  change t ^ (a + (n : ℝ) - 1) * Real.exp (-r * t ^ (1 : ℝ))
    = t ^ (a + (n : ℝ) - 1) * Real.exp (-(r * t))
  rw [Real.rpow_one, neg_mul]

/-- The pointwise identity behind both moment lemmas: on `(0,∞)` the integrand `tⁿ·φ(t)` is the
Gamma density at shape `a + n`, up to the constant. -/
theorem gammaPDF_pow_apply {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    (gammaPDF a r t).toReal * t ^ n
      = r ^ a / Real.Gamma a * (t ^ (a + (n : ℝ) - 1) * Real.exp (-(r * t))) := by
  rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr t), gammaPDFReal,
    if_pos ht.le, show a + (n : ℝ) - 1 = (a - 1) + n by ring, Real.rpow_add ht,
    Real.rpow_natCast]
  ring

/-- **Every moment of the Gamma law is finite.** -/
theorem integrable_pow_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (n : ℕ) :
    Integrable (fun t : ℝ => t ^ n) (gammaMeasure a r) := by
  rw [gammaMeasure, integrable_withDensity_iff (f := gammaPDF a r)
    ((measurable_gammaPDFReal a r).ennreal_ofReal)
    (.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine Integrable.congr (f := fun t : ℝ => (Ioi (0 : ℝ)).indicator
    (fun t => r ^ a / Real.Gamma a * (t ^ (a + (n : ℝ) - 1) * Real.exp (-(r * t)))) t) ?_ ?_
  · rw [integrable_indicator_iff measurableSet_Ioi]
    exact (integrableOn_rpow_shift_mul_exp ha hr n).const_mul _
  · filter_upwards [compl_mem_ae_iff.mpr (Real.volume_singleton (a := (0 : ℝ)))] with t htne
    by_cases ht : t ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem ht, mul_comm (t ^ n),
        gammaPDF_pow_apply ha hr n (mem_Ioi.mp ht)]
    · have hneg : t < 0 := lt_of_le_of_ne (not_lt.mp (by simpa using ht)) (by simpa using htne)
      rw [indicator_of_notMem ht]
      simp [gammaPDF_of_neg hneg]

/-- **The Gamma law's moments**: `E[Tⁿ] = Γ(a+n)/(Γ(a)rⁿ)`.

Mathlib carries none of these either, so they come from the same Gamma integral the transform
used — one lemma serving the transform, the integrability and the value. -/
theorem integral_pow_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (n : ℕ) :
    (∫ t, t ^ n ∂(gammaMeasure a r)) = Real.Gamma (a + n) / (Real.Gamma a * r ^ n) := by
  have hΓ : (0 : ℝ) < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have hcompl : ∀ᵐ t ∂volume, t ∉ Ioi (0 : ℝ) → (gammaPDF a r t).toReal • t ^ n = 0 := by
    filter_upwards [compl_mem_ae_iff.mpr (Real.volume_singleton (a := (0 : ℝ)))] with t htne hnot
    have hneg : t < 0 := lt_of_le_of_ne (not_lt.mp (by simpa using hnot)) (by simpa using htne)
    rw [gammaPDF_of_neg hneg, ENNReal.toReal_zero, zero_smul]
  rw [gammaMeasure, integral_withDensity_eq_integral_toReal_smul₀
      (f := gammaPDF a r) ((measurable_gammaPDFReal a r).ennreal_ofReal.aemeasurable)
      (.of_forall fun _ => ENNReal.ofReal_lt_top),
    ← setIntegral_eq_integral_of_ae_compl_eq_zero hcompl]
  simp only [smul_eq_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi
      (fun t ht => gammaPDF_pow_apply ha hr n (mem_Ioi.mp ht)),
    integral_const_mul,
    Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity) hr, one_div, Real.inv_rpow hr.le,
    Real.rpow_add hr, Real.rpow_natCast]
  have hrn : (0 : ℝ) < r ^ n := pow_pos hr n
  have hra : (0 : ℝ) < r ^ a := Real.rpow_pos_of_pos hr a
  field_simp

/-- The Gamma law's variance, `a/r²`: `Γ(a+2)/Γ(a) = a(a+1)` against `(Γ(a+1)/Γ(a))² = a²`. -/
theorem variance_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    variance id (gammaMeasure a r) = a / r ^ 2 := by
  haveI := isProbabilityMeasure_gammaMeasure ha hr
  have hΓ : (0 : ℝ) < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have hmem : MemLp (id : ℝ → ℝ) 2 (gammaMeasure a r) := by
    refine memLp_two_iff_integrable_sq (by fun_prop) |>.mpr ?_
    exact (integrable_pow_gammaMeasure ha hr 2).congr (.of_forall fun t => rfl)
  have h1 : (∫ t, t ^ 1 ∂(gammaMeasure a r)) = a / r := by
    rw [integral_pow_gammaMeasure ha hr 1]
    rw [show a + ((1 : ℕ) : ℝ) = a + 1 by norm_num, Real.Gamma_add_one ha.ne']
    field_simp
  have h2 : (∫ t, t ^ 2 ∂(gammaMeasure a r)) = a * (a + 1) / r ^ 2 := by
    rw [integral_pow_gammaMeasure ha hr 2]
    rw [show a + ((2 : ℕ) : ℝ) = (a + 1) + 1 by push_cast; ring,
      Real.Gamma_add_one (by positivity), Real.Gamma_add_one ha.ne']
    field_simp
  rw [variance_eq_sub hmem]
  have hid1 : (gammaMeasure a r)[(id : ℝ → ℝ)] = a / r := by simpa using h1
  have hid2 : (gammaMeasure a r)[(id : ℝ → ℝ) ^ 2] = a * (a + 1) / r ^ 2 := by
    simpa [Pi.pow_apply] using h2
  rw [hid1, hid2]
  field_simp
  ring

/-- **`prop:gamma-moments`**: every moment of the Gamma family's delay is finite, and
`Var T_x = γx²`.

**Off ledger A7**, which the blueprint's route spends: with `prop:gamma-density` identifying the
kernel as Mathlib's Gamma law, the moments are a Gamma computation. The node's own annotation
predicted this — "whichever of the two is done first makes the other cheap" — and the density was
done first. -/
theorem gammaExponent_moments (hγ : 0 < γ) {x : ℝ} (hx : 0 < x) :
    (∀ n : ℕ, Integrable (fun t : ℝ => t ^ n) ((gammaExponent γ hγ.le).kernel 0 x)) ∧
      variance id ((gammaExponent γ hγ.le).kernel 0 x) = γ * x ^ 2 := by
  rw [gammaExponent_kernel_eq_gammaMeasure hγ hx]
  refine ⟨fun n => integrable_pow_gammaMeasure hγ (inv_pos.mpr hx) n, ?_⟩
  rw [variance_gammaMeasure hγ (inv_pos.mpr hx)]
  field_simp

end SelfDecomposableExponent

end Hemigroup
