/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.Examples

/-!
# `Ein`, the entire exponential integral

Blueprint: the function named in `prop:extreme-rays` and `lem:dickman-superposition`,
`Ein(z) = ∫₀^z (1 - e^{-u})/u du`.

**Mathlib has no exponential integral of any kind** — no `Ein`, no `Ei`, no `E₁`; `Analysis/`
carries `Gamma`, `Beta`, `Zeta`, `Polylog` and nothing of this family. So `ein` is *defined* here,
on the pattern `riemannLiouville` set in chapter 11: the article cites Caravenna–Sun–Zygouras for
the Dickman subordinator's Lévy density and transform, not for any theorem about `Ein`, so this
adds a definition and no interface.

## Why the integrand needs no guard at the origin

`(1 - e^{-u})/u` extends continuously by `1` at `u = 0`, and Lean's `x / 0 = 0` gives it the value
`0` there instead. That is a discontinuity on a null set and no integral sees it, so no `if 0 < u`
guard is carried — unlike `SelfDecomposableExponent.k`, where the guard is load-bearing because
`k 0` is a *field* the structure constrains. The bound `0 ≤ (1 - e^{-u})/u ≤ 1` on `(0,∞)` is what
every estimate below reduces to, and it is `one_sub_exp_neg_le` divided by `u`.
-/

namespace Hemigroup

open MeasureTheory Set

open scoped ENNReal

/-- The integrand of `Ein`: `(1 - e^{-u})/u`, extended by Lean's `x / 0 = 0` at the origin. -/
noncomputable def einIntegrand (u : ℝ) : ℝ := (1 - Real.exp (-u)) / u

/-- **`Ein(z) = ∫₀^z (1 - e^{-u})/u du`.**

Total in `z`: for `z ≤ 0` the interval integral is `≤ 0`-oriented and the value is what the
orientation gives, which the article never asks about — every use is at `z ≥ 0`. -/
noncomputable def ein (z : ℝ) : ℝ := ∫ u in (0 : ℝ)..z, einIntegrand u

theorem einIntegrand_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ einIntegrand u := by
  have h : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  exact div_nonneg (by linarith) hu

/-- `(1 - e^{-u})/u ≤ 1`: the estimate every bound below reduces to, and `one_sub_exp_neg_le`
divided by `u`. -/
theorem einIntegrand_le_one {u : ℝ} (hu : 0 ≤ u) : einIntegrand u ≤ 1 := by
  rcases hu.eq_or_lt with rfl | hu'
  · simp [einIntegrand]
  · rw [einIntegrand, div_le_one hu']
    exact one_sub_exp_neg_le u

theorem measurable_einIntegrand : Measurable einIntegrand := by
  unfold einIntegrand
  fun_prop

/-- The integrand is interval-integrable on `[0,z]` for `z ≥ 0`: measurable, and bounded by `1`.

Stated on the right half-line and not on all of `ℝ`, because the bound is false to the left of the
origin — `(1 - e^{-u})/u` grows like `e^{|u|}/|u|` there. Every use is at `z ≥ 0`, and the layer
cake below asks for exactly `∀ t > 0`. -/
theorem intervalIntegrable_einIntegrand {z : ℝ} (hz : 0 ≤ z) :
    IntervalIntegrable einIntegrand volume 0 z := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hz]
  have hfin : volume (Ioc (0 : ℝ) z) ≠ ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  refine Integrable.mono' (g := fun _ : ℝ => (1 : ℝ)) (integrableOn_const (hs := hfin))
    measurable_einIntegrand.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (.of_forall fun u hu => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (einIntegrand_nonneg hu.1.le)]
  exact einIntegrand_le_one hu.1.le

end Hemigroup
