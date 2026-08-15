/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.ClosedForms
import Hemigroup.MeanDelay

/-!
# `prop:gamma-kernels`: the Gamma family's transforms and mean

Blueprint: `prop:gamma-kernels` (Proposition 8.9), narrowed to its transform and mean clauses. For
`F(s) = γ log(1+s)`,

  `E[e^{-sT_x}] = (1 + xs)^{-γ}`,  `E[e^{-sμ_{a,b}}] = ((1+as)/(1+bs))^γ`,  `E T_x = γx`.

## Why these three and not the node's other clauses

All three are one computation from `gammaExponent_toRealExponent`, `laplace_kernel`, and — for the
mean — `prop:moments`, proved this week. The clauses left behind cost more and are separated so
that the node does not report their price for these:

* the explicit density `φ_x(t) = t^{γ-1}e^{-t/x}/(Γ(γ)x^γ)` is `prop:gamma-density`. Inverting
  `(1+xs)^{-γ}` means computing the Gamma density's transform and appealing to Laplace uniqueness
  — available, but a separate piece of work;
* all moments finite, and `Var T_x = γx²`, is `prop:gamma-moments`, which runs through
  `prop:moment-criterion` and hence ledger **A7**. Note the contrast with `prop:stable-moments`,
  which came *off* A7 this week: there the mean diverged and divergence propagates upward, so the
  `n = 1` case sufficed. Convergence does not propagate downward from `n = 1`, so the Gamma
  family's higher moments genuinely need the criterion — or the density, which is the other route.

That asymmetry is the reason the two example families split along different lines even though
their nodes had the same shape.
-/

namespace Hemigroup

open MeasureTheory Set

open scoped ENNReal

namespace SelfDecomposableExponent

variable {γ : ℝ}

/-- **The Gamma family's kernels**: `E[e^{-sT_x}] = (1 + xs)^{-γ}`. -/
theorem gammaExponent_laplace_kernel (hγ : 0 ≤ γ) {x s : ℝ} (hx : 0 < x) (hs : 0 < s) :
    laplace ((gammaExponent γ hγ).kernel 0 x) s = (1 + x * s) ^ (-γ) := by
  have hpos : (0 : ℝ) < 1 + x * s := by positivity
  rw [laplace_kernel le_rfl hx.le hs.le, increment_zero_left hx.le s,
    show ((gammaExponent γ hγ).exponent (x * s)).toReal
      = (gammaExponent γ hγ).toRealExponent (x * s) from rfl,
    gammaExponent_toRealExponent hγ (by positivity), Real.rpow_def_of_pos hpos]
  congr 1
  ring

/-- **The Gamma family's increments**: `E[e^{-sμ_{a,b}}] = ((1+as)/(1+bs))^γ`.

The ratio of two kernel transforms, which is what `increment_toReal` says in `ℝ` — the identity
being false in `ℝ≥0∞`, where subtraction is truncated. -/
theorem gammaExponent_laplace_increment (hγ : 0 ≤ γ) {a b s : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hs : 0 < s) :
    laplace ((gammaExponent γ hγ).kernel a b) s = ((1 + a * s) / (1 + b * s)) ^ γ := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hpa : (0 : ℝ) < 1 + a * s := by positivity
  have hpb : (0 : ℝ) < 1 + b * s := by positivity
  have hA : ((gammaExponent γ hγ).exponent (a * s)).toReal = γ * Real.log (1 + a * s) :=
    gammaExponent_toRealExponent hγ (by positivity)
  have hB : ((gammaExponent γ hγ).exponent (b * s)).toReal = γ * Real.log (1 + b * s) :=
    gammaExponent_toRealExponent hγ (by positivity)
  rw [laplace_kernel ha.le hab hs.le, increment_toReal ha.le hab hs.le, hA, hB,
    Real.rpow_def_of_pos (div_pos hpa hpb), Real.log_div hpa.ne' hpb.ne']
  congr 1
  ring

/-- The Gamma family's mean rate is `γ`: `∫₀^∞ γe^{-t}dt = γ`, and the drift is zero. -/
theorem gammaExponent_meanRate (hγ : 0 ≤ γ) : (gammaExponent γ hγ).meanRate
    = ENNReal.ofReal γ := by
  have hrep : ∀ t ∈ Ioi (0 : ℝ), (gammaExponent γ hγ).k t = γ * Real.exp (-t) := fun t ht => by
    change gammaDensity γ t = γ * Real.exp (-t)
    rw [gammaDensity, if_pos (mem_Ioi.mp ht)]
  have hint : IntegrableOn (gammaExponent γ hγ).k (Ioi 0) :=
    IntegrableOn.congr_fun ((integrableOn_exp_neg_Ioi 0).const_mul γ)
      (fun t ht => (hrep t ht).symm) measurableSet_Ioi
  have hval : (∫ t in Ioi (0 : ℝ), (gammaExponent γ hγ).k t) = γ := by
    rw [setIntegral_congr_fun measurableSet_Ioi hrep, integral_const_mul,
      integral_exp_neg_Ioi_zero, mul_one]
  rw [meanRate, show (gammaExponent γ hγ).b₀ = 0 from rfl, ENNReal.ofReal_zero, zero_add,
    ← ofReal_integral_eq_lintegral_ofReal hint
      ((ae_restrict_iff' measurableSet_Ioi).mpr
        (.of_forall fun t ht => (gammaExponent γ hγ).k_nonneg t ht)),
    hval]

/-- **The Gamma family's mean delay**: `E T_x = γ x`, the influence curve of
`prop:moments` with `F'(0+) = γ`. -/
theorem gammaExponent_lintegral_id_kernel (hγ : 0 ≤ γ) {x : ℝ} (hx : 0 < x) :
    ∫⁻ t, ENNReal.ofReal t ∂((gammaExponent γ hγ).kernel 0 x) = ENNReal.ofReal (γ * x) := by
  rw [(gammaExponent γ hγ).lintegral_id_kernel_zero hx,
    (gammaExponent γ hγ).lintegral_id_lawT₁, gammaExponent_meanRate hγ,
    ← ENNReal.ofReal_mul hx.le, mul_comm]

end SelfDecomposableExponent

end Hemigroup
