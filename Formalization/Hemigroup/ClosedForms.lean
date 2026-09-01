/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the MIT license as described in the file LICENSES/MIT.txt.
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

/-! ## The extremal stable family

`k(t) = α t^{-α}/Γ(1-α)`, the kernels of the 2005 paper. This one lives here rather than in
`Examples.lean` because it names `Real.Gamma`, and the same file evaluates its exponent.

The two halves of `prop:admissibility-criterion` are separated by this kernel in a way the Gamma
family does not separate them: `k` is *unbounded* at the origin, and integrable there only
because `α < 1`; it is integrable against `dt/t` at infinity only because `α > 0`. So the
hypothesis `0 < α < 1` is used once on each side, and neither use is cosmetic. -/

variable {α : ℝ}

/-- The Lévy density of the extremal stable family, guarded at the origin. -/
noncomputable def stableDensity (α : ℝ) : ℝ → ℝ :=
  fun t => if 0 < t then α / Real.Gamma (1 - α) * t ^ (-α) else 0

lemma stableConst_pos (hα : 0 < α) (hα1 : α < 1) : 0 < α / Real.Gamma (1 - α) :=
  div_pos hα (Real.Gamma_pos_of_pos (by linarith))

lemma stableDensity_nonneg (hα : 0 < α) (hα1 : α < 1) (t : ℝ) : 0 ≤ stableDensity α t := by
  unfold stableDensity
  split
  · exact mul_nonneg (stableConst_pos hα hα1).le (Real.rpow_nonneg (by linarith) _)
  · exact le_rfl

lemma stableDensity_antitoneOn (hα : 0 < α) (hα1 : α < 1) :
    AntitoneOn (stableDensity α) (Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  have hxpos : (0 : ℝ) < x := mem_Ioi.mp hx
  have hypos : (0 : ℝ) < y := mem_Ioi.mp hy
  simp only [stableDensity, if_pos hxpos, if_pos hypos]
  refine mul_le_mul_of_nonneg_left ?_ (stableConst_pos hα hα1).le
  rw [Real.rpow_neg hxpos.le, Real.rpow_neg hypos.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hxpos _) (Real.rpow_le_rpow hxpos.le hxy hα.le)

/-- The stable kernel is integrable at the origin exactly because `α < 1`. -/
lemma integrableOn_stableDensity (hα : 0 < α) (hα1 : α < 1) :
    IntegrableOn (stableDensity α) (Ioc 0 1) := by
  have hrpow : IntegrableOn (fun t : ℝ => t ^ (-α)) (Ioc 0 1) :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < -α)).1
  refine IntegrableOn.congr_fun (hrpow.const_mul (α / Real.Gamma (1 - α))) ?_ measurableSet_Ioc
  intro t ht
  rw [stableDensity, if_pos ht.1]

/-- And integrable against `dt/t` at infinity exactly because `α > 0`. -/
lemma integrableOn_stableDensity_div (hα : 0 < α) (hα1 : α < 1) :
    IntegrableOn (fun t => stableDensity α t / t) (Ioi 1) := by
  have hrpow : IntegrableOn (fun t : ℝ => t ^ (-α - 1)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith : -α - 1 < -1) zero_lt_one
  refine IntegrableOn.congr_fun (hrpow.const_mul (α / Real.Gamma (1 - α))) ?_ measurableSet_Ioi
  intro t ht
  have htpos : (0 : ℝ) < t := lt_trans zero_lt_one (mem_Ioi.mp ht)
  simp only [stableDensity, if_pos htpos]
  rw [Real.rpow_sub htpos, Real.rpow_one]
  field_simp

/-- **The extremal stable family**, `k(t) = α t^{-α}/Γ(1-α)`. -/
noncomputable def stableExponent (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    SelfDecomposableExponent where
  b₀ := 0
  k := stableDensity α
  b₀_nonneg := le_rfl
  k_nonneg := fun t _ => stableDensity_nonneg hα hα1 t
  k_antitone := stableDensity_antitoneOn hα hα1
  k_zero := by simp [stableDensity]
  ne_top := fun s hs =>
    levyExponentD_ne_top_of_integrableOn (fun t _ => stableDensity_nonneg hα hα1 t) hs
      (lintegral_ofReal_ne_top_of_integrableOn (integrableOn_stableDensity hα hα1))
      (lintegral_ofReal_ne_top_of_integrableOn (integrableOn_stableDensity_div hα hα1))

/-- The stable family's `F'`: `α s^{α-1}`. The Gamma integral at exponent `1-α`. -/
theorem stableExponent_integral (hα : 0 < α) (hα1 : α < 1) {s : ℝ} (hs : 0 < s) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(s * t)) * (stableExponent α hα hα1).k t)
      = α * s ^ (α - 1) := by
  have hΓ : 0 < Real.Gamma (1 - α) := Real.Gamma_pos_of_pos (by linarith)
  have hpt : ∀ t ∈ Ioi (0 : ℝ), Real.exp (-(s * t)) * (stableExponent α hα hα1).k t
      = α / Real.Gamma (1 - α) * (t ^ ((1 - α) - 1) * Real.exp (-(s * t))) := by
    intro t ht
    show Real.exp (-(s * t)) * stableDensity α t = _
    rw [stableDensity, if_pos (mem_Ioi.mp ht), show (1 - α) - 1 = -α by ring]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith : (0 : ℝ) < 1 - α) hs]
  rw [one_div, Real.inv_rpow hs.le, ← Real.rpow_neg hs.le, show -(1 - α) = α - 1 by ring]
  field_simp

/-- **`prop:stable-family`**, the exponent: `F(s) = s^α` for `k(t) = α t^{-α}/Γ(1-α)`.

The draft calls the identity "the standard integral representation". Here it is again the
antiderivative statement, at the Gamma integral's exponent `1-α` instead of `1`. -/
theorem stableExponent_toRealExponent (hα : 0 < α) (hα1 : α < 1) {s : ℝ} (hs : 0 < s) :
    (stableExponent α hα hα1).toRealExponent s = s ^ α := by
  refine (stableExponent α hα hα1).eq_of_hasDerivAt_of_tendsto_zero
    (g := fun y => y ^ α) ?_ ?_ hs
  · intro x hx
    have hval : (stableExponent α hα hα1).b₀
        + ∫ t in Ioi (0 : ℝ), Real.exp (-(x * t)) * (stableExponent α hα hα1).k t
        = α * x ^ (α - 1) := by
      rw [stableExponent_integral hα hα1 hx]
      norm_num [stableExponent]
    rw [hval]
    exact Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx))
  · have hc : ContinuousAt (fun y : ℝ => y ^ α) 0 :=
      Real.continuousAt_rpow_const 0 α (Or.inr hα.le)
    have hlim : Filter.Tendsto (fun y : ℝ => y ^ α) (𝓝[>] (0 : ℝ)) (𝓝 ((0 : ℝ) ^ α)) :=
      Filter.Tendsto.mono_left hc nhdsWithin_le_nhds
    rwa [Real.zero_rpow (ne_of_gt hα)] at hlim

/-- The leaky integrator's exponent, `log(1+s)`. -/
theorem leakyIntegrator_toRealExponent {s : ℝ} (hs : 0 < s) :
    leakyIntegrator.toRealExponent s = Real.log (1 + s) := by
  have h := gammaExponent_toRealExponent (γ := 1) zero_le_one hs
  rw [one_mul] at h
  exact h

end SelfDecomposableExponent

end Hemigroup
