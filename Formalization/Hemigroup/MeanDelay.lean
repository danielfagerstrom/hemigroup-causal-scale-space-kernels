/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.MemoryFractional

/-!
# `prop:moments`: the mean delay and the influence curve

Blueprint: `prop:moments` (Proposition 8.4). `E T_x = x F'(0+) = x(b₀ + ∫₀^∞ k)`, finite iff `k`
is integrable at infinity, and the influence curve is linear in `x`.

## `F'(0+)` is `[0,∞]`-valued, and that is the statement rather than a convenience

The proposition's whole second clause is about when the mean is *infinite*, so the mean rate is
defined in `ℝ≥0∞` and the identity is stated there. No hypothesis of finiteness appears anywhere
below; where the blueprint says "finite if and only if", the Lean statement is
`meanRate ≠ ⊤ ↔ IntegrableOn k (Ioi 1)` and both sides may fail.

## The influence curve is linear because `μ_{0,x}` is the law of `x T₁`

The blueprint reaches linearity from the identity — `E T_x = xF'(0+)` is linear in `x` because the
right-hand side is. In Lean it is cheaper and comes first: `kernel_zero_eq_map_lawT₁`, proved for
chapter 11, says `μ_{0,x}` is the pushforward of `μ_{0,1}` under `t ↦ xt`, so *every* moment scales
and the mean identity is only ever needed at `x = 1`. That splits the proposition cleanly: the
scaling is a change of variables, and the Tauberian step `E T₁ = F'(0+)` is the rest.
-/

namespace Hemigroup

open MeasureTheory Set Filter

open scoped ENNReal Topology

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent)

/-- **`F'(0+) = b₀ + ∫₀^∞ k(t) dt`**, the mean rate, valued in `[0,∞]`. -/
noncomputable def meanRate : ℝ≥0∞ :=
  ENNReal.ofReal F.b₀ + ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (F.k t)

/-- **The mean rate is finite exactly when `k` is integrable at infinity.**

The other end costs nothing: `∫₀¹ k < ∞` is forced by the structure's own `ne_top` field
(`integrableOn_k`) and not assumed, so the only condition is at infinity — which is what the
blueprint asserts. -/
theorem meanRate_ne_top_iff : F.meanRate ≠ ⊤ ↔ IntegrableOn F.k (Ioi 1) := by
  have hnn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ F.k t := fun t ht => F.k_nonneg t ht
  have hsplit : (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (F.k t))
      = (∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (F.k t))
        + ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (F.k t) := by
    rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1),
      lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same]
  have hlow : (∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (F.k t)) ≠ ⊤ := by
    have h := F.integrableOn_k.2
    rw [hasFiniteIntegral_iff_enorm] at h
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono_ae ?_) h)
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (.of_forall fun t ht => ?_)
    rw [Real.enorm_eq_ofReal (hnn t (mem_Ioi.mpr ht.1))]
  constructor
  · intro h
    refine integrableOn_of_lintegral_ofReal_ne_top
      ((F.aemeasurable_k fun t ht => lt_trans zero_lt_one (mem_Ioi.mp ht)).aestronglyMeasurable)
      ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun t ht =>
        hnn t (mem_Ioi.mpr (lt_trans zero_lt_one (mem_Ioi.mp ht)))))
    rw [meanRate, hsplit] at h
    exact (ENNReal.add_ne_top.mp ((ENNReal.add_ne_top.mp h).2)).2
  · intro h
    have hhigh : (∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (F.k t)) ≠ ⊤ := by
      have h2 := h.2
      rw [hasFiniteIntegral_iff_enorm] at h2
      refine ne_of_lt (lt_of_le_of_lt (lintegral_mono_ae ?_) h2)
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun t ht => ?_)
      rw [Real.enorm_eq_ofReal (hnn t (mem_Ioi.mpr (lt_trans zero_lt_one (mem_Ioi.mp ht))))]
    rw [meanRate, hsplit]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.add_ne_top.mpr ⟨hlow, hhigh⟩⟩

/-- **The influence curve is linear**: every scale's delay law is the unit law dilated, so the
mean delay scales exactly.

This is `kernel_zero_eq_map_lawT₁` and a change of variables, and it holds whether or not the mean
is finite — which is why it is separated from the identity `E T₁ = F'(0+)` rather than deduced
from it. -/
theorem lintegral_id_kernel_zero {x : ℝ} (hx : 0 < x) :
    ∫⁻ t, ENNReal.ofReal t ∂(F.kernel 0 x)
      = ENNReal.ofReal x * ∫⁻ t, ENNReal.ofReal t ∂F.lawT₁ := by
  rw [F.kernel_zero_eq_map_lawT₁ hx,
    lintegral_map (by fun_prop) (measurable_const_mul x),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact lintegral_congr fun t => ENNReal.ofReal_mul hx.le

end SelfDecomposableExponent

end Hemigroup
