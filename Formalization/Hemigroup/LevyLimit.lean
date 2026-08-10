/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.NullArray
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# `thm:increments-bernstein`, part two: the test function

`NullArray.lean` produced `∫ (1 - e^{-st})\,d\Pi_n \to g_{x,y}(s)` with each `Π_n` finite. What
remains is to extract a limiting Lévy triple from `(Π_n)`, and the obstruction is that the total
masses `Π_n(\mathbb{R}) = n` diverge: mass piles up at the origin, and that pile is exactly the
drift `b_0` the triple is allowed to have.

The standard cure is to weight by `1 - e^{-t}`, which vanishes at the origin at the right rate.
This file builds the two objects that cure needs.

## The change of variable

`expTrans t = 1 - e^{-t}` carries `[0,∞]` homeomorphically onto `[0,1]`, sending `∞` to `1`. In
that coordinate the weighted measures live on the *compact* `[0,1]`, so a weak limit exists with
no tightness argument beyond "supported in a fixed compact". The two endpoints are the two
degenerate parts of a Lévy triple: mass at `0` is drift, mass at `1` would be a killing term.

## The test function

Under the weighting, `1 - e^{-st}` becomes

  `k_s(v) = (1 - (1-v)^s) / v`,

which is what has to be integrated against the weighted measure. It has a removable singularity
at `v = 0`, where its value is `s` — and *that* is why mass at the origin contributes `b_0 s`
rather than `0`. Filling the singularity in is the content of `continuous_levyRatio`, and it is
a derivative computation: `k_s(v)` is the difference quotient at `0` of `v ↦ 1 - (1-v)^s`, whose
derivative there is `s`.

`levyRatioBdd` is the same function clamped to `[0,1]`, so that it is a *bounded* continuous
function on `ℝ` and hence a legitimate test function for weak convergence. Clamping changes
nothing the measures can see: they are carried by `[0,1]`.
-/

namespace Hemigroup

open MeasureTheory Set Filter
open scoped Topology

/-! ## The change of variable -/

/-- `t ↦ 1 - e^{-t}`, carrying `[0,∞]` onto `[0,1]`. -/
noncomputable def expTrans (t : ℝ) : ℝ := 1 - Real.exp (-t)

@[simp] lemma expTrans_zero : expTrans 0 = 0 := by simp [expTrans]

lemma continuous_expTrans : Continuous expTrans := by unfold expTrans; fun_prop

lemma expTrans_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ expTrans t := by
  have : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  simp only [expTrans]
  linarith

lemma expTrans_lt_one (t : ℝ) : expTrans t < 1 := by
  have := Real.exp_pos (-t)
  simp only [expTrans]
  linarith

lemma expTrans_le_one (t : ℝ) : expTrans t ≤ 1 := (expTrans_lt_one t).le

lemma one_sub_expTrans (t : ℝ) : 1 - expTrans t = Real.exp (-t) := by simp [expTrans]

/-! ## The test function -/

/-- `k_s(v) = (1 - (1-v)^s)/v`, with the removable singularity at `v = 0` filled in by its
limit `s`. The value at `0` is the whole point: it is what turns mass at the origin into the
drift term. -/
noncomputable def levyRatio (s v : ℝ) : ℝ := if v = 0 then s else (1 - (1 - v) ^ s) / v

@[simp] lemma levyRatio_zero (s : ℝ) : levyRatio s 0 = s := if_pos rfl

lemma levyRatio_of_ne {v : ℝ} (hv : v ≠ 0) (s : ℝ) :
    levyRatio s v = (1 - (1 - v) ^ s) / v := if_neg hv

/-- **The change of variable, as an identity.** `k_s(1 - e^{-t}) \cdot (1 - e^{-t}) = 1 - e^{-st}`.

This is what lets `∫ (1 - e^{-st})\,d\Pi` be rewritten as `∫ k_s\,d\rho` for the weighted
measure `ρ`. The degenerate case `t = 0` is where the value `k_s(0) = s` is *not* used: both
sides are zero. -/
theorem levyRatio_expTrans_mul {s t : ℝ} (ht : 0 ≤ t) :
    levyRatio s (expTrans t) * expTrans t = 1 - Real.exp (-(s * t)) := by
  rcases eq_or_lt_of_le ht with rfl | htpos
  · simp
  · have hv : expTrans t ≠ 0 := by
      have : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      simp only [expTrans]
      linarith
    rw [levyRatio_of_ne hv, div_mul_cancel₀ _ hv, one_sub_expTrans,
      Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    ring_nf

/-- The numerator, `v ↦ 1 - (1-v)^s`, has derivative `s` at the origin. This is the removable
singularity, and the value `s` in `levyRatio` is exactly this derivative. -/
theorem hasDerivAt_one_sub_one_sub_rpow (s : ℝ) :
    HasDerivAt (fun v : ℝ => 1 - (1 - v) ^ s) s 0 := by
  have hbase : HasDerivAt (fun v : ℝ => 1 - v) (-1) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_sub 1
  have hpow : HasDerivAt (fun u : ℝ => u ^ s) (s * (1 : ℝ) ^ (s - 1)) (1 - 0) := by
    simpa using Real.hasDerivAt_rpow_const (p := s) (x := (1 : ℝ)) (Or.inl one_ne_zero)
  have hcomp := hpow.comp (0 : ℝ) hbase
  rw [Real.one_rpow, mul_one] at hcomp
  simpa using hcomp.const_sub 1

/-- **The test function is continuous**, singularity and all. -/
theorem continuous_levyRatio {s : ℝ} (hs : 0 < s) : Continuous (levyRatio s) := by
  rw [continuous_iff_continuousAt]
  intro v
  rcases eq_or_ne v 0 with rfl | hv
  · -- At the singularity: the difference quotient converges to the derivative.
    have hslope : Tendsto (fun v : ℝ => (1 - (1 - v) ^ s) / v) (𝓝[≠] (0 : ℝ)) (𝓝 s) := by
      have h := hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_one_sub_one_sub_rpow s)
      refine h.congr fun u => ?_
      rw [slope_def_field]
      simp [div_eq_inv_mul]
    have hpunct : Tendsto (levyRatio s) (𝓝[≠] (0 : ℝ)) (𝓝 (levyRatio s 0)) := by
      rw [levyRatio_zero]
      refine hslope.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact (levyRatio_of_ne hu s).symm
    rw [ContinuousAt, ← nhdsNE_sup_pure (0 : ℝ), Filter.tendsto_sup]
    exact ⟨hpunct, tendsto_pure_nhds _ _⟩
  · -- Away from it: a quotient of continuous functions, the denominator nonzero.
    have hnum : ContinuousAt (fun v : ℝ => 1 - (1 - v) ^ s) v := by
      have := (Real.continuousAt_rpow_const (1 - v) s (Or.inr hs.le)).comp
        (by fun_prop : ContinuousAt (fun u : ℝ => 1 - u) v)
      exact this.const_sub 1
    have : ContinuousAt (fun v : ℝ => (1 - (1 - v) ^ s) / v) v := hnum.div continuousAt_id hv
    refine this.congr ?_
    filter_upwards [compl_singleton_mem_nhds hv] with u hu
    exact (levyRatio_of_ne hu s).symm

/-! ## The bounded test function

Weak convergence tests against bounded continuous functions, and `levyRatio s` is unbounded off
`[0,1]` — `(1-v)^s` grows there. Clamping fixes that and costs nothing: the measures in play are
carried by `[0,1]`, where the two agree.
-/

/-- The clamp onto `[0,1]`. -/
noncomputable def clamp01 (v : ℝ) : ℝ := max 0 (min v 1)

lemma continuous_clamp01 : Continuous clamp01 := by unfold clamp01; fun_prop

lemma clamp01_mem (v : ℝ) : clamp01 v ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

@[simp] lemma clamp01_of_mem {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) : clamp01 v = v := by
  rw [clamp01, min_eq_left hv.2, max_eq_right hv.1]

/-- **The test function, bounded**: `k_s` clamped to `[0,1]`, as an element of `ℝ →ᵇ ℝ`.

No explicit bound is computed — a continuous function on the compact `[0,1]` is bounded, and
that is all weak convergence asks for. -/
private noncomputable def levyBound {s : ℝ} (hs : 0 < s) : ℝ :=
  ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (continuous_levyRatio hs).continuousOn).choose

private lemma levyBound_spec {s : ℝ} (hs : 0 < s) :
    ∀ v ∈ Icc (0 : ℝ) 1, ‖levyRatio s v‖ ≤ levyBound hs :=
  ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (continuous_levyRatio hs).continuousOn).choose_spec

noncomputable def levyRatioBdd {s : ℝ} (hs : 0 < s) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun v => levyRatio s (clamp01 v))
    ((continuous_levyRatio hs).comp continuous_clamp01) (levyBound hs)
    fun v => levyBound_spec hs _ (clamp01_mem v)

@[simp] lemma levyRatioBdd_apply {s : ℝ} (hs : 0 < s) (v : ℝ) :
    levyRatioBdd hs v = levyRatio s (clamp01 v) := rfl

/-- On `[0,1]`, where the measures live, the clamped function is the original. -/
lemma levyRatioBdd_of_mem {s : ℝ} (hs : 0 < s) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    levyRatioBdd hs v = levyRatio s v := by
  rw [levyRatioBdd_apply, clamp01_of_mem hv]

/-- The image of `[0,∞)` under the change of variable lands where the clamp is the identity. -/
lemma levyRatioBdd_expTrans {s : ℝ} (hs : 0 < s) {t : ℝ} (ht : 0 ≤ t) :
    levyRatioBdd hs (expTrans t) = levyRatio s (expTrans t) :=
  levyRatioBdd_of_mem hs ⟨expTrans_nonneg ht, expTrans_le_one t⟩

end Hemigroup
