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
    ConvexOn ℝ F.momentInterval (fun ζ => Real.log (F.negMoment ζ).toReal) := by
  refine ⟨F.convex_momentInterval, fun ζ₁ h₁ ζ₂ h₂ θ η hθ hη hsum => ?_⟩
  have hη' : η = 1 - θ := by linarith
  subst hη'
  -- finiteness of the three moments involved
  have hfin : ∀ ζ ∈ F.momentInterval, F.negMoment ζ ≠ ⊤ :=
    fun ζ hζ => F.negMoment_ne_top_of_lt_zStar hζ.1 hζ.2
  have hmid : θ * ζ₁ + (1 - θ) * ζ₂ ∈ F.momentInterval := by
    simpa [smul_eq_mul] using F.convex_momentInterval h₁ h₂ hθ hη hsum
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

/-! ## `lem:moment-recursion`(1): the symbol vanishes at the origin -/

/-- **`m(c) → 1` as `c ↓ 0`.**

Dominated convergence. Pointwise on `(0,∞)` the integrand `t^{-c} = exp(-c log t)` tends to `1`;
for `0 < c ≤ 1` it is dominated by `1 + t^{-1}`, integrable because (H)'s second clause puts `1`
strictly below `z_*`. That second clause is used here and nowhere else in this file. -/
theorem tendsto_negMoment_nhdsGT_zero (hH : F.StandingHypothesis) :
    Tendsto (fun c : ℝ => (F.negMoment c).toReal) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have h0 := F.lawT₁_singleton_zero hH.1
  have hae := F.ae_mem_Ioi_lawT₁ h0
  have hbound : Integrable (fun t : ℝ => 1 + t ^ (-(1 : ℝ))) F.lawT₁ :=
    (integrable_const 1).add (integrable_rpow_neg F hH one_pos (by simpa using hH.2))
  have hle1 : ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ), c ≤ 1 :=
    Filter.Eventually.mono (nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)))
      fun _ h => le_of_lt h
  have key : Tendsto (fun c : ℝ => ∫ t, t ^ (-c) ∂F.lawT₁) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ _t, (1 : ℝ) ∂F.lawT₁)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun t : ℝ => 1 + t ^ (-(1 : ℝ))) (Filter.Eventually.of_forall fun c => by fun_prop)
      ?_ hbound ?_
    · filter_upwards [self_mem_nhdsWithin, hle1] with c hc hc1
      filter_upwards [hae] with t ht
      have ht0 : (0 : ℝ) < t := ht
      have hnn : (0 : ℝ) ≤ t ^ (-(1 : ℝ)) := Real.rpow_nonneg ht0.le _
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
      rcases le_total t 1 with h1 | h1
      · have := Real.rpow_le_rpow_of_exponent_ge ht0 h1 (by linarith [mem_Ioi.mp hc] : -1 ≤ -c)
        linarith
      · have := Real.rpow_le_one_of_one_le_of_nonpos h1
          (by linarith [mem_Ioi.mp hc] : -c ≤ 0)
        linarith
    · filter_upwards [hae] with t ht
      have ht0 : (0 : ℝ) < t := ht
      have hexp : ∀ c : ℝ, t ^ (-c) = Real.exp (Real.log t * (-c)) :=
        fun c => Real.rpow_def_of_pos ht0 _
      have hcont : Continuous fun c : ℝ => Real.exp (Real.log t * (-c)) := by fun_prop
      simpa [hexp] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hrw : ∀ c : ℝ, ∫ t, t ^ (-c) ∂F.lawT₁ = (F.negMoment c).toReal :=
    fun c => F.integral_rpow_neg_eq_negMoment h0
  simpa [hrw] using key

/-- **`lem:moment-recursion`(1), `B(0) = 0`,** as the limit it actually is:
`B(-c) = c · m(c+1)/m(c) → 0` as `c ↓ 0`.

The blueprint states `B(0) = 0` under the hypothesis that `B` is a polynomial, and gets it by
continuity from this limit. The polynomial hypothesis is inert in the argument -- what the proof
uses is that `m(c) → 1`, that `m(c+1)` stays bounded, and that `c → 0` -- so the limit is stated
here without it, and `B(0) = 0` for a *continuous* `B` follows by uniqueness of limits. This is
the same pattern as `lem:mellin-vertical`: a hypothesis carried by the statement it is proved
under, rather than by the proof.

Boundedness of the numerator is `negMoment_le_of_le` at any `ζ ∈ (1, z_*)`; (H) is what makes
that interval nonempty. -/
theorem tendsto_inversionSymbol_nhdsGT_zero (hH : F.StandingHypothesis) :
    Tendsto (fun c : ℝ => F.inversionSymbol (c : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h0 := F.lawT₁_singleton_zero hH.1
  -- a witness above `1` with a finite moment; with `z_*` possibly infinite there is no midpoint
  -- of `(1, z_*)` to take, so the supremum hands the witness over instead
  obtain ⟨ζ, hζ1, hζtop⟩ := F.exists_one_lt_negMoment_ne_top hH
  -- the denominator
  have hden : Tendsto (fun c : ℝ => (F.negMoment c).toReal) (𝓝[>] (0 : ℝ)) (𝓝 1) :=
    F.tendsto_negMoment_nhdsGT_zero hH
  -- the numerator, by squeezing against `c · ((m(ζ)).toReal + 1)`
  have hsmall : ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ), c < ζ - 1 :=
    nhdsWithin_le_nhds (gt_mem_nhds (by linarith : (0 : ℝ) < ζ - 1))
  have hid : Tendsto (fun c : ℝ => c) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hlin : Tendsto (fun c : ℝ => c * ((F.negMoment ζ).toReal + 1)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hid.mul_const ((F.negMoment ζ).toReal + 1)
  have hnum : Tendsto (fun c : ℝ => c * (F.negMoment (c + 1)).toReal) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hlin
    · filter_upwards [self_mem_nhdsWithin] with c hc
      have hc0 : (0 : ℝ) < c := hc
      exact mul_nonneg hc0.le ENNReal.toReal_nonneg
    · filter_upwards [self_mem_nhdsWithin, hsmall] with c hc hcζ
      have hc0 : (0 : ℝ) < c := hc
      have hb : (F.negMoment (c + 1)).toReal ≤ (F.negMoment ζ).toReal + 1 := by
        have hmono := ENNReal.toReal_mono
          (ENNReal.add_ne_top.mpr ⟨hζtop, ENNReal.one_ne_top⟩)
          (F.negMoment_le_of_le (by linarith : (0:ℝ) ≤ c + 1) (by linarith : c + 1 ≤ ζ))
        rwa [ENNReal.toReal_add hζtop ENNReal.one_ne_top, ENNReal.toReal_one] at hmono
      exact mul_le_mul_of_nonneg_left hb hc0.le
  have hreal : Tendsto (fun c : ℝ => c * (F.negMoment (c + 1)).toReal / (F.negMoment c).toReal)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [Pi.div_def] using hnum.div hden one_ne_zero
  -- transport to the symbol
  have hstrip : ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ), ENNReal.ofReal c < F.zStar - 1 := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with c hc hcζ
    exact (ofReal_lt_sub_one_iff (le_of_lt hc)).mpr
      (F.ofReal_lt_zStar_of_lt (by linarith [mem_Ioi.mp hc]) (by linarith) hζtop)
  have heq : ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ),
      Complex.ofReal (c * (F.negMoment (c + 1)).toReal / (F.negMoment c).toReal)
        = F.inversionSymbol (c : ℂ) := by
    filter_upwards [self_mem_nhdsWithin, hstrip] with c hc hcz
    have hmem : (c : ℂ) ∈ verticalStrip 0 (F.zStar - 1) := ⟨by simpa using hc, by simpa using hcz⟩
    have hshift : ((c : ℂ) + 1) = ((c + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [F.inversionSymbol_eq hH hmem, hshift, F.negMomentC_ofReal h0 c,
      F.negMomentC_ofReal h0 (c + 1)]
    push_cast
    ring
  refine Tendsto.congr' heq ?_
  simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hreal

end SelfDecomposableExponent

end Hemigroup
