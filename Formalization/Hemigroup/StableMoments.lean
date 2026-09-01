/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Hemigroup.ClosedForms
import Hemigroup.MeanDelay

/-!
# `prop:stable-moments`: every moment of the extremal stable delay is infinite

Blueprint: `prop:stable-moments` (Proposition 8.10), moments clause. For `F(s) = s^α` with
`0 < α < 1`, `E T_x^n = ∞` for every `n ≥ 1` and every `x > 0`, so the delay of the 2005 stable
kernels cannot be measured by any moment.

## The ledger entry the blueprint's proof spends is not needed

The blueprint reaches this through `prop:moment-criterion` — `E T_x^n < ∞` iff
`∫₁^∞ t^{n-1}k(t)dt < ∞` — which is ledger **A7**. That criterion's own annotation already records
that its `n = 1` case is *not* carried by the ledger, being `prop:moments`; and `n = 1` is all this
needs, because **infinite propagates upward**: `t ≤ 1 + t^n` for `t ≥ 0` and `n ≥ 1`, so on a
probability measure `E T ≤ 1 + E T^n`, and a divergent mean forces every higher moment to diverge.

So the route is `meanRate_ne_top_iff` (the mean is finite iff `k` is integrable at infinity) plus
`t^{-α}` failing that for `α < 1`, and then one elementary inequality. The two supporting lemmas
below are Lean core; the statement about `T_x` spends **A17** through `kernel`, as every statement
about the constructed family does, and cannot avoid it — `T_x` is what A17 constructs. What it does
avoid is A7. The `n = 1` case being cheap is exactly what `prop:moments` was split off to record,
and this is the first node to collect on it.

## The mode clause is elsewhere

The proposition's second clause — the mode scales as `x^{1/α}` — is not here. It needs a
definition of the mode, which this development does not have; see `prop:stable-mode`.
-/

namespace Hemigroup

open MeasureTheory Set

open scoped ENNReal

namespace SelfDecomposableExponent

variable {α : ℝ}

/-- **`t^{-α}` is not integrable at infinity for `α < 1`** — the divergence the whole clause runs
on, and the exact complement of `integrableOn_stableDensity_div`, where the extra `t^{-1}` is what
made the same exponent converge. -/
theorem not_integrableOn_stableDensity (hα : 0 < α) (hα1 : α < 1) :
    ¬ IntegrableOn (stableDensity α) (Ioi 1) := by
  intro h
  have hc : (0 : ℝ) < α / Real.Gamma (1 - α) := stableConst_pos hα hα1
  have hrpow : IntegrableOn (fun t : ℝ => t ^ (-α)) (Ioi 1) := by
    have := (h.congr_fun (g := fun t : ℝ => α / Real.Gamma (1 - α) * t ^ (-α)) ?_
      measurableSet_Ioi)
    · exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hc.ne') _).mp this
    · intro t ht
      have htpos : (0 : ℝ) < t := lt_trans zero_lt_one (mem_Ioi.mp ht)
      rw [stableDensity, if_pos htpos]
  exact absurd ((integrableOn_Ioi_rpow_iff zero_lt_one).mp hrpow) (by linarith)

/-- The stable family's mean delay diverges: `F'(0+) = ∞`. -/
theorem stableExponent_meanRate (hα : 0 < α) (hα1 : α < 1) :
    (stableExponent α hα hα1).meanRate = ⊤ := by
  by_contra h
  exact not_integrableOn_stableDensity hα hα1
    ((stableExponent α hα hα1).meanRate_ne_top_iff.mp h)

/-- **A divergent mean forces every higher moment to diverge**, on any probability measure carried
by the half-line: `t ≤ 1 + t^n` for `t ≥ 0` and `n ≥ 1`.

Stated separately because it is the whole of what `prop:stable-moments` needs beyond the `n = 1`
case, and it is what lets the node avoid ledger A7 — the criterion the blueprint invokes for
general `n` is only ever used here in the direction "infinite stays infinite". -/
theorem lintegral_pow_eq_top_of_lintegral_id_eq_top {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCausal μ) {n : ℕ} (hn : 1 ≤ n) (h : ∫⁻ t, ENNReal.ofReal t ∂μ = ⊤) :
    ∫⁻ t, ENNReal.ofReal (t ^ n) ∂μ = ⊤ := by
  by_contra hfin
  have hle : (∫⁻ t, ENNReal.ofReal t ∂μ)
      ≤ (∫⁻ _t, 1 ∂μ) + ∫⁻ t, ENNReal.ofReal (t ^ n) ∂μ := by
    rw [← lintegral_add_left' (aemeasurable_const) _]
    refine lintegral_mono_ae ?_
    filter_upwards [hμ.ae_nonneg] with t ht
    rcases le_total t 1 with h1 | h1
    · exact le_trans (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal h1)
        le_self_add
    · have hpow : t ≤ t ^ n := by
        calc t = t ^ 1 := (pow_one t).symm
          _ ≤ t ^ n := pow_le_pow_right₀ h1 hn
      calc ENNReal.ofReal t ≤ ENNReal.ofReal (t ^ n) := ENNReal.ofReal_le_ofReal hpow
        _ ≤ 1 + ENNReal.ofReal (t ^ n) := le_add_self
  rw [h] at hle
  simp only [lintegral_const, measure_univ, mul_one] at hle
  exact absurd (top_le_iff.mp hle) (by simp [hfin])

/-- **`prop:stable-moments`, the moments clause.** For the extremal stable family every moment of
the delay is infinite, at every scale — so the delay cannot be measured by the mean, and the
article's use of the mode is forced rather than stylistic.

**A17 and nothing else**, through `kernel`: the blueprint routes this through
`prop:moment-criterion` and hence ledger A7 as well, and it does not need to. -/
theorem stableExponent_lintegral_pow_kernel (hα : 0 < α) (hα1 : α < 1) {x : ℝ} (hx : 0 < x)
    {n : ℕ} (hn : 1 ≤ n) :
    ∫⁻ t, ENNReal.ofReal (t ^ n) ∂((stableExponent α hα hα1).kernel 0 x) = ⊤ := by
  have hmean : ∫⁻ t, ENNReal.ofReal t ∂((stableExponent α hα hα1).kernel 0 x) = ⊤ := by
    rw [(stableExponent α hα hα1).lintegral_id_kernel_zero hx,
      (stableExponent α hα hα1).lintegral_id_lawT₁, stableExponent_meanRate hα hα1,
      ENNReal.mul_top (by simpa using hx)]
  haveI : IsProbabilityMeasure ((stableExponent α hα hα1).kernel 0 x) :=
    isProbabilityMeasure_kernel le_rfl hx.le
  exact lintegral_pow_eq_top_of_lintegral_id_eq_top (isCausal_kernel le_rfl hx.le) hn hmean

end SelfDecomposableExponent

end Hemigroup
