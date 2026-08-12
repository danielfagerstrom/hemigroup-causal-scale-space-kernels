/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.InversionSymbol
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Log-convexity of the negative moments

Blueprint: `lem:log-convexity` (12.4), the first node of chapter 12 to be formalised.

The blueprint proves midpoint log-convexity by Cauchy--Schwarz and then upgrades it with
continuity of `m`. That upgrade is avoidable: Hölder at the exponent pair `(1/θ, 1/(1-θ))` gives
the convexity inequality at every `θ ∈ [0,1]` directly, and Mathlib carries it in exactly the
form wanted, `lintegral_mul_norm_pow_le`, stated for two exponents summing to `1` rather than for
conjugate reciprocals. Nothing about continuity of `m` is needed.

Two statements, and the difference between them matters for chapter 12.

* `negMoment_le_rpow_mul_rpow` is the inequality in `[0,∞]`, and holds **unconditionally** --
  no standing hypothesis, no finiteness, no restriction to a strip. This is the honest form: the
  `ℝ≥0∞`-valued `negMoment` is log-convex as a map into `[0,∞]`, divergence included.
* `convexOn_log_negMoment` is the blueprint's reading, `ConvexOn ℝ · (log ∘ m)`, and needs a
  domain on which `m` is finite and positive. Positivity is `negMoment_pos`, which is where (H)'s
  first clause enters: without it `T₁` may sit at the origin, and the integral is over `(0,∞)`.

The blueprint states log-convexity on all of `(0,∞)`, which presupposes `z_* = ∞` -- clause (2) of
`lem:moment-recursion`, and the one clause of that lemma carried by ledger **A13**. So the domain
here is `Ioo 0 z_*`, which is what is available before A13 is spent; on the locality hypothesis
the two coincide.

`ConvexOn` rather than a bare inequality is deliberate: it is the shape Mathlib's
`Real.eq_Gamma_of_log_convex` (Bohr--Mollerup) consumes, and that is where chapter 12 is headed.
-/

namespace Hemigroup

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent)

/-! ## Hölder, in `[0,∞]` -/

/-- **`lem:log-convexity`, in `[0,∞]`.** For `θ ∈ [0,1]`,
`m(θζ₁ + (1-θ)ζ₂) ≤ m(ζ₁)^θ · m(ζ₂)^(1-θ)`.

Unconditional: no hypothesis on `F`, and no finiteness. Hölder with exponents `θ` and `1-θ`
applied to `t^(-ζ₁)` and `t^(-ζ₂)`, whose `θ`- and `(1-θ)`-powers multiply to `t^(-(θζ₁+(1-θ)ζ₂))`
because the base is positive on the domain of integration. -/
theorem negMoment_le_rpow_mul_rpow {ζ₁ ζ₂ θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ ≤ 1) :
    F.negMoment (θ * ζ₁ + (1 - θ) * ζ₂)
      ≤ F.negMoment ζ₁ ^ θ * F.negMoment ζ₂ ^ (1 - θ) := by
  have h1 : (0 : ℝ) ≤ 1 - θ := by linarith
  have hm₁ : AEMeasurable (fun t : ℝ => ENNReal.ofReal (t ^ (-ζ₁)))
      (F.lawT₁.restrict (Ioi 0)) := by
    fun_prop
  have hm₂ : AEMeasurable (fun t : ℝ => ENNReal.ofReal (t ^ (-ζ₂)))
      (F.lawT₁.restrict (Ioi 0)) := by
    fun_prop
  have hpt : ∀ t ∈ Ioi (0 : ℝ),
      ENNReal.ofReal (t ^ (-(θ * ζ₁ + (1 - θ) * ζ₂)))
        = ENNReal.ofReal (t ^ (-ζ₁)) ^ θ * ENNReal.ofReal (t ^ (-ζ₂)) ^ (1 - θ) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have harg : -(θ * ζ₁ + (1 - θ) * ζ₂) = -ζ₁ * θ + -ζ₂ * (1 - θ) := by ring
    rw [harg, Real.rpow_add ht0, Real.rpow_mul ht0.le, Real.rpow_mul ht0.le,
      ENNReal.ofReal_mul (Real.rpow_nonneg (Real.rpow_pos_of_pos ht0 _).le _),
      ← ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos ht0 _),
      ← ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos ht0 _)]
  have hL : F.negMoment (θ * ζ₁ + (1 - θ) * ζ₂)
      = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-ζ₁)) ^ θ
          * ENNReal.ofReal (t ^ (-ζ₂)) ^ (1 - θ) ∂F.lawT₁ := by
    rw [negMoment]
    exact setLIntegral_congr_fun measurableSet_Ioi hpt
  rw [hL]
  exact ENNReal.lintegral_mul_norm_pow_le hm₁ hm₂ hθ h1 (by ring)

/-! ## Positivity, and the real-valued reading -/

/-- The negative moments are **strictly positive**, at every real order: the `≠ 0` of
`negMoment_ne_zero`, in the form the logarithm below needs.

The content is there and not here: the integrand `t^(-ζ)` is positive on `(0,∞)`, and (H)'s first
clause puts all of `T₁`'s mass there. Without it the statement fails, a law with an atom at the
origin having that atom invisible to an integral over `(0,∞)`. -/
theorem negMoment_pos (h0 : F.lawT₁ {(0 : ℝ)} = 0) (ζ : ℝ) : 0 < F.negMoment ζ :=
  pos_iff_ne_zero.mpr (F.negMoment_ne_zero h0 ζ)

/-- **`lem:log-convexity`.** `ζ ↦ log m(ζ)` is convex on `(0, z_*)`.

The blueprint says `(0,∞)`; that is the same statement once `z_* = ∞`, which is
`lem:moment-recursion`(2) and the clause ledger **A13** carries. Stated here on the domain
available without it. -/
theorem convexOn_log_negMoment (h0 : F.lawT₁ {(0 : ℝ)} = 0) :
    ConvexOn ℝ (Ioo 0 F.zStar) (fun ζ => Real.log (F.negMoment ζ).toReal) := by
  refine ⟨convex_Ioo _ _, fun ζ₁ h₁ ζ₂ h₂ θ η hθ hη hsum => ?_⟩
  have hη' : η = 1 - θ := by linarith
  subst hη'
  -- finiteness of the three moments involved
  have hfin : ∀ ζ ∈ Ioo (0 : ℝ) F.zStar, F.negMoment ζ ≠ ⊤ :=
    fun ζ hζ => F.negMoment_ne_top_of_lt_zStar hζ.1 hζ.2
  have hmid : θ * ζ₁ + (1 - θ) * ζ₂ ∈ Ioo (0 : ℝ) F.zStar := by
    simpa [smul_eq_mul] using convex_Ioo (0 : ℝ) F.zStar h₁ h₂ hθ hη hsum
  have key := F.negMoment_le_rpow_mul_rpow (ζ₁ := ζ₁) (ζ₂ := ζ₂) hθ (by linarith)
  -- push the `[0,∞]` inequality down to `ℝ` and take logarithms
  have hp₁ := F.negMoment_pos h0 ζ₁
  have hp₂ := F.negMoment_pos h0 ζ₂
  have hpm := F.negMoment_pos h0 (θ * ζ₁ + (1 - θ) * ζ₂)
  have hreal : (F.negMoment (θ * ζ₁ + (1 - θ) * ζ₂)).toReal
      ≤ (F.negMoment ζ₁).toReal ^ θ * (F.negMoment ζ₂).toReal ^ (1 - θ) := by
    have := ENNReal.toReal_mono
      (ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg hθ (hfin ζ₁ h₁))
        (ENNReal.rpow_ne_top_of_nonneg (by linarith) (hfin ζ₂ h₂))) key
    rwa [ENNReal.toReal_mul, <-ENNReal.toReal_rpow, <-ENNReal.toReal_rpow] at this
  have hr₁ : 0 < (F.negMoment ζ₁).toReal := ENNReal.toReal_pos hp₁.ne' (hfin ζ₁ h₁)
  have hr₂ : 0 < (F.negMoment ζ₂).toReal := ENNReal.toReal_pos hp₂.ne' (hfin ζ₂ h₂)
  have hrm : 0 < (F.negMoment (θ * ζ₁ + (1 - θ) * ζ₂)).toReal :=
    ENNReal.toReal_pos hpm.ne' (hfin _ hmid)
  calc Real.log (F.negMoment (θ * ζ₁ + (1 - θ) * ζ₂)).toReal
      ≤ Real.log ((F.negMoment ζ₁).toReal ^ θ * (F.negMoment ζ₂).toReal ^ (1 - θ)) :=
        Real.log_le_log hrm hreal
    _ = θ * Real.log (F.negMoment ζ₁).toReal + (1 - θ) * Real.log (F.negMoment ζ₂).toReal := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hr₁, Real.log_rpow hr₂]
    _ = θ • Real.log (F.negMoment ζ₁).toReal + (1 - θ) • Real.log (F.negMoment ζ₂).toReal := by
        simp [smul_eq_mul]

end SelfDecomposableExponent

end Hemigroup
