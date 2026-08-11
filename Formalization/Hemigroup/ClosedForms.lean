/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.ExponentDerivative
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Chapter 8's closed forms

Blueprint: `prop:gamma-family` (8.2). `Examples.lean` exhibits the kernels; this file evaluates
their exponents.

## Why these are derivative computations

The draft proves `F(s) = γ log(1+s)` by quoting Frullani's integral, and `F(s) = s^α` by quoting
the standard representation of the power. Neither is in Mathlib. But both are *antiderivative*
statements, and the development now has what it takes to run them that way:

* `lem:memory-kernel` gives `F'(s) = b₀ + ∫₀^∞ e^{-st} k(t) dt`, and for these kernels that
  integral is elementary — Mathlib's `integral_rpow_mul_exp_neg_mul_Ioi` evaluates it,
  the Gamma family at exponent `1` and the stable family at exponent `1-α`.
* `tendsto_toRealExponent_nhdsGT_zero` gives `F(0+) = 0`, which pins the constant.

So the two closed forms are the same argument twice: match derivatives on `(0,∞)`, match limits
at the origin, conclude. That is `eq_of_hasDerivAt_of_tendsto_zero`, and it is the reason the
plan's ordering was inverted — chapter 9's first lemma is chapter 8's tool.
-/

namespace Hemigroup

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- `∫₀^∞ e^{-rt} dt = 1/r`, the `a = 1` case of Mathlib's Gamma integral. -/
theorem integral_exp_neg_mul_Ioi {r : ℝ} (hr : 0 < r) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-(r * t)) = 1 / r := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1) (r := r) one_pos hr
  have hcongr : (∫ t in Ioi (0 : ℝ), t ^ ((1 : ℝ) - 1) * Real.exp (-(r * t)))
      = ∫ t in Ioi (0 : ℝ), Real.exp (-(r * t)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp
  rw [← hcongr, h]
  simp [Real.Gamma_one]

namespace SelfDecomposableExponent

/-! ## The Gamma family -/

/-- The Gamma family's `F'`: `γ/(1+s)`. -/
theorem gammaExponent_integral {γ : ℝ} (hγ : 0 ≤ γ) {s : ℝ} (hs : 0 < s) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(s * t)) * (gammaExponent γ hγ).k t) = γ / (1 + s) := by
  have hpt : ∀ t ∈ Ioi (0 : ℝ), Real.exp (-(s * t)) * (gammaExponent γ hγ).k t
      = γ * Real.exp (-((1 + s) * t)) := by
    intro t ht
    show Real.exp (-(s * t)) * gammaDensity γ t = γ * Real.exp (-((1 + s) * t))
    rw [gammaDensity, if_pos (mem_Ioi.mp ht),
      show -((1 + s) * t) = -(s * t) + -t by ring, Real.exp_add]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    integral_exp_neg_mul_Ioi (by linarith : (0 : ℝ) < 1 + s)]
  ring

/-- **`prop:gamma-family`**, the exponent: `F(s) = γ log(1+s)` for `k(t) = γ e^{-t}`.

The draft calls this Frullani's integral. Here it is the antiderivative statement: both sides
have derivative `γ/(1+s)` on `(0,∞)` and both vanish at `0+`. -/
theorem gammaExponent_toRealExponent {γ : ℝ} (hγ : 0 ≤ γ) {s : ℝ} (hs : 0 < s) :
    (gammaExponent γ hγ).toRealExponent s = γ * Real.log (1 + s) := by
  refine (gammaExponent γ hγ).eq_of_hasDerivAt_of_tendsto_zero
    (g := fun y => γ * Real.log (1 + y)) ?_ ?_ hs
  · intro x hx
    have hx1 : (0 : ℝ) < 1 + x := by linarith
    have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
      simpa using (hasDerivAt_id x).const_add 1
    have hlog : HasDerivAt (fun y : ℝ => γ * Real.log (1 + y)) (γ * (1 / (1 + x))) x :=
      (h1.log (ne_of_gt hx1)).const_mul γ
    have hval : (gammaExponent γ hγ).b₀
        + ∫ t in Ioi (0 : ℝ), Real.exp (-(x * t)) * (gammaExponent γ hγ).k t
        = γ * (1 / (1 + x)) := by
      rw [gammaExponent_integral hγ hx]
      show (0 : ℝ) + γ / (1 + x) = γ * (1 / (1 + x))
      ring
    rw [hval]
    exact hlog
  · have hc : ContinuousAt (fun y : ℝ => γ * Real.log (1 + y)) 0 := by
      fun_prop (disch := norm_num)
    simpa using Filter.Tendsto.mono_left hc nhdsWithin_le_nhds

/-- The leaky integrator's exponent, `log(1+s)`. -/
theorem leakyIntegrator_toRealExponent {s : ℝ} (hs : 0 < s) :
    leakyIntegrator.toRealExponent s = Real.log (1 + s) := by
  have h := gammaExponent_toRealExponent (γ := 1) zero_le_one hs
  rw [one_mul] at h
  exact h

end SelfDecomposableExponent

end Hemigroup
