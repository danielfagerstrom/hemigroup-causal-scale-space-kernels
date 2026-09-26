/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Hemigroup.MemoryFractional

/-!
# `lem:zstar-log-growth` (11.23), the drift clause

The Lévy-data reading of the *second* clause of `def:standing-hypothesis`. The node splits into
four declarations (`Skeleton/Chapter11.lean` prices all four); this file carries the one that is
elementary, clause (2)'s drift case.

`b₀ > 0` forces `F(s)/log s → ∞`, and it does so for a reason that has nothing to do with the
Lévy measure, with `z_*`, or with an atom of `T₁` at the origin: the drift alone already gives
`F(s) ≥ b₀ s`, and `s / log s → ∞`. So the statement is unconditional, and it is the only one of
the four that can be read off the representation without a Tauberian argument.

`tendsto_id_div_log_atTop` is `Real.isLittleO_log_id_atTop` turned the other way up; Mathlib has
the little-o statement but not the divergence of `s / log s`.
-/

namespace Hemigroup

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- `s / log s → ∞`. Mathlib has `Real.isLittleO_log_id_atTop`; this is its reciprocal form. -/
lemma tendsto_id_div_log_atTop : Tendsto (fun s : ℝ => s / Real.log s) atTop atTop := by
  have h0 : Tendsto (fun s : ℝ => Real.log s / s) atTop (𝓝 0) := by
    simpa using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hpos : ∀ᶠ s : ℝ in atTop, Real.log s / s ∈ Ioi (0 : ℝ) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with s hs
    exact div_pos (Real.log_pos hs) (by linarith)
  have hwithin : Tendsto (fun s : ℝ => Real.log s / s) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h0 hpos
  have hinv : Tendsto (fun s : ℝ => (Real.log s / s)⁻¹) atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp hwithin
  refine hinv.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with s hs
  rw [inv_div]

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent)

/-- **`lem:zstar-log-growth`(2), drift case**: `b₀ > 0` forces the log-growth rate to diverge.
Unconditional — no no-atom hypothesis, since this is a statement about the exponent alone, not
about `T₁`'s moments. -/
theorem tendsto_toRealExponent_div_log_atTop_of_b₀_pos (hb : 0 < F.b₀) :
    Tendsto (fun s => F.toRealExponent s / Real.log s) atTop atTop := by
  refine tendsto_atTop_mono' _ ?_
    (Filter.Tendsto.const_mul_atTop hb tendsto_id_div_log_atTop)
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with s hs
  have hs0 : (0 : ℝ) ≤ s := by linarith
  have hlog : 0 < Real.log s := Real.log_pos hs
  have hdrift : F.b₀ * s ≤ F.toRealExponent s := by
    have hle : ENNReal.ofReal (F.b₀ * s) ≤ F.exponent s := by
      simp only [exponent, levyExponentD]; exact le_self_add
    have h2 := ENNReal.toReal_mono (F.ne_top s hs0) hle
    rwa [ENNReal.toReal_ofReal (mul_nonneg F.b₀_nonneg hs0)] at h2
  rw [mul_div_assoc']
  exact div_le_div_of_nonneg_right hdrift hlog.le

end SelfDecomposableExponent

end Hemigroup
