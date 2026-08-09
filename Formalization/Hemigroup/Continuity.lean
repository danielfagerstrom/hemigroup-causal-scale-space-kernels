/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.Construction
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Towards axiom (A7): tightness of the kernel family

Axiom (A7) is continuity of `(a,b) ↦ Φ_{a,b}`, and the blueprint discharges it with the
continuity theorem for Laplace transforms — ledger **A5**. The open question this file exists to
settle is whether A5 has to become a second interface axiom, or whether the pieces are already
available: Mathlib has Prokhorov, and `prop:laplace-continuity`'s own assignment clause in
`AXIOMS.md` says the *tightness* argument is ours and is held `[T]`.

## What this file establishes

The tightness half, and it is elementary — a Markov bound read off the transform:

  `μ(t > T) · (1 - e^{-sT}) ≤ 1 - μ̂(s)`     (`measureReal_Ioi_mul_le`)

and, for the kernel family with `b` bounded above, the uniform tail estimate that follows
(`kernel_tail_le`). No compactness, no limit theorem — the whole content is that `1 - e^{-st}`
dominates `(1 - e^{-sT}) · 1_{t > T}`, which is monotonicity of the exponential.

So the blueprint's claim that tightness is ours is **correct**, and A5 is not needed for it.

## What remains, and why the question is not yet closed

Turning tightness into (A7) still needs two things this file does not have:

* pointwise convergence of the transforms, i.e. continuity of `F` in its argument. That is a
  dominated-convergence argument on the Lévy integral — the dominating function is `F` itself at
  the largest argument, so it is available, but it is not written here;
* the passage from "tight, with convergent transforms" to weak convergence: Prokhorov gives a
  convergent subsequence, `laplace_injective` identifies its limit, and the usual
  compact-plus-unique-limit-point argument upgrades that to the full sequence.

Neither step needs a cited interface. What they need is work. The honest status is therefore
that **A5 looks avoidable rather than proved avoidable**, and this file is the part of the
evidence that can be checked rather than asserted.
-/

namespace Hemigroup

open MeasureTheory Set

/-! ## A Markov bound from the transform -/

/-- **The tail of a causal probability measure is controlled by its Laplace transform.**

`μ(t > T) · (1 - e^{-sT}) ≤ 1 - μ̂(s)`. The content is pointwise: on `t > T` the integrand
`1 - e^{-st}` is at least `1 - e^{-sT}`, and off that set it is still nonnegative because the
measure is causal.

No hypothesis on `T` is needed — causality already supplies the sign that a `T ≥ 0` assumption
would have. -/
theorem measureReal_Ioi_mul_le {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsCausal μ)
    {s T : ℝ} (hs : 0 ≤ s) :
    (μ (Ioi T)).toReal * (1 - Real.exp (-(s * T))) ≤ 1 - laplace μ s := by
  have hint : Integrable (fun t => Real.exp (-(s * t))) μ := integrable_exp_of_causal hμ hs
  have h1 : 1 - laplace μ s = ∫ t, (1 - Real.exp (-(s * t))) ∂μ := by
    rw [laplace, integral_sub (integrable_const 1) hint, integral_const]
    simp
  have hind : Integrable ((Ioi T).indicator fun _ => 1 - Real.exp (-(s * T))) μ :=
    (integrable_const _).indicator measurableSet_Ioi
  rw [h1]
  calc (μ (Ioi T)).toReal * (1 - Real.exp (-(s * T)))
      = ∫ t, (Ioi T).indicator (fun _ => 1 - Real.exp (-(s * T))) t ∂μ := by
        rw [integral_indicator_const _ measurableSet_Ioi, smul_eq_mul, measureReal_def]
    _ ≤ ∫ t, (1 - Real.exp (-(s * t))) ∂μ := by
        refine integral_mono_ae hind ((integrable_const 1).sub hint) ?_
        filter_upwards [hμ.ae_nonneg] with t ht
        by_cases hcase : t ∈ Ioi T
        · rw [indicator_of_mem hcase]
          have : Real.exp (-(s * t)) ≤ Real.exp (-(s * T)) :=
            Real.exp_le_exp.mpr (by nlinarith [mem_Ioi.mp hcase])
          linarith
        · rw [indicator_of_notMem hcase]
          have : Real.exp (-(s * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
          linarith

/-- The tail bound in the form tightness needs: `μ(t > T) ≤ (1 - μ̂(s)) / (1 - e^{-sT})`. -/
theorem measureReal_Ioi_le_div {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsCausal μ)
    {s T : ℝ} (hs : 0 < s) (hT : 0 < T) :
    (μ (Ioi T)).toReal ≤ (1 - laplace μ s) / (1 - Real.exp (-(s * T))) := by
  have hden : 0 < 1 - Real.exp (-(s * T)) := by
    have : Real.exp (-(s * T)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
    linarith
  rw [le_div_iff₀ hden]
  exact measureReal_Ioi_mul_le hμ hs.le

/-! ## The uniform tail estimate for the kernel family -/

namespace SelfDecomposableExponent

variable {F : SelfDecomposableExponent} {a b s T B : ℝ}

/-- `1 - e^{-g} ≤ g`, the elementary step that replaces the transform by the exponent. -/
private lemma one_sub_exp_neg_le {g : ℝ} (_hg : 0 ≤ g) : 1 - Real.exp (-g) ≤ g := by
  have := Real.add_one_le_exp (-g)
  linarith

/-- **The uniform tail estimate.** For kernels with `b` bounded above by `B`, the tail is
controlled by `F` alone, uniformly in the pair:

  `μ_{a,b}(t > T) ≤ F(Bs) / (1 - e^{-sT})`.

Given `ε`, choosing `s` small makes `F(Bs)` small — because `F(0+) = 0` — and then `T` large
makes the denominator close to `1`. That is tightness, and every ingredient is ours. -/
theorem kernel_tail_le (ha : 0 < a) (hab : a ≤ b) (hbB : b ≤ B) (hs : 0 < s) (hT : 0 < T) :
    ((F.kernel a b) (Ioi T)).toReal
      ≤ (F.exponent (B * s)).toReal / (1 - Real.exp (-(s * T))) := by
  haveI := isProbabilityMeasure_kernel (F := F) ha hab
  have hden : 0 < 1 - Real.exp (-(s * T)) := by
    have : Real.exp (-(s * T)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
    linarith
  have hB : 0 < B := lt_of_lt_of_le (lt_of_lt_of_le ha hab) hbB
  -- `1 - μ̂(s) ≤ g_{a,b}(s) ≤ F(Bs)`, the second step because exponents add along `a ≤ b ≤ B`.
  have hnum : 1 - laplace (F.kernel a b) s ≤ (F.exponent (B * s)).toReal := by
    rw [laplace_kernel ha hab hs.le]
    refine (one_sub_exp_neg_le ENNReal.toReal_nonneg).trans ?_
    have hmono : F.increment a b s ≤ F.exponent (B * s) := by
      calc F.increment a b s ≤ F.exponent (b * s) := by
            rw [← exponent_add_increment (F := F) ha hab hs.le]; exact le_add_self
        _ ≤ F.exponent (B * s) := by
            rw [← exponent_add_increment (F := F) (lt_of_lt_of_le ha hab) hbB hs.le]
            exact le_self_add
    exact ENNReal.toReal_mono (F.ne_top _ (by positivity)) hmono
  refine (measureReal_Ioi_le_div (isCausal_kernel ha hab) hs hT).trans ?_
  gcongr

end SelfDecomposableExponent

end Hemigroup
