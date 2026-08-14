/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.MomentRecursion
import Hemigroup.GammaRecursion

/-!
# The order-two case of `thm:locality`: the moments are the Gamma form

Blueprint: the order-2 branch of `thm:locality`'s (⇒) direction (12.5) --- the step that turns the
recursion into `m(z) = c₂^z Γ(a+z)/Γ(a)` and so identifies `T₁` as `1/(c₂γ_a)`, the inverse-gamma
family of `prop:bessel-family`.

## The two citations enter as hypotheses, not as axioms

`thm:locality`'s (⇒) direction spends two interfaces, and both are *conclusions* that this file
takes as named hypotheses rather than as `axiom`s --- the same phrasing `thm:main-construction`
uses for A17, so that either can be demoted to a lemma the day it is proved without touching a
statement below.

* **`AllNegMomentsFinite`** is `lem:moment-recursion`(2), `z_* = ∞`, ledger **A13**.
* **The order bound** is Courrège, ledger **A14**: here it is simply the hypothesis that the
  operator is local of order `2`.

What is proved is everything between them: with `z_* = ∞` the recursion `m(z+1) = Q(z)m(z)` holds
on all of `(0,∞)` rather than on `(0, z_*-1)`, `Q` is the linear `c₂z + a₀` of
`symbolQuotient_two`, its coefficients are real with `c₂ > 0` and `a₀ > 0`, and
`lem:gamma-recursion-uniqueness` --- Bohr--Mollerup, proved in-repo --- closes it.

## Where the work actually is

Not in the Gamma form, which is one application of a lemma already proved. It is in `a₀ > 0`.

`a₀ = Q(0)` is a limit: `Q(z) = m(z+1)/m(z)` and `m(z) → 1` as `z ↓ 0`, so `a₀ = m(1)`, which is
positive because `T₁` charges only `(0,∞)`. Positivity of `Q` on `(0,∞)` gives only `a₀ ≥ 0` --- a
linear function positive on the open half-line may vanish at the origin --- so the limit has to be
taken, and taking it needs `m(z+1) → m(1)`, which is the same dominated-convergence argument as
`tendsto_negMoment_nhdsGT_zero` one unit to the right. It is available here and not in general:
the dominating function is `t^{-2} + 1`, integrable exactly because `2 < z_*`, which is what A13
supplies.
-/

namespace Hemigroup

open MeasureTheory Set Filter

open scoped ENNReal Topology

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent)

/-! ## `z_* = ∞`, as a hypothesis -/

/-- **Ledger A13's conclusion**, named: every negative moment of `T₁` is finite. This is
`lem:moment-recursion`(2), and it is what widens every strip in this file to the whole half-line.
-/
def AllNegMomentsFinite : Prop := ∀ ζ : ℝ, 0 < ζ → F.negMoment ζ ≠ ⊤

theorem zStar_eq_top (h : F.AllNegMomentsFinite) : F.zStar = ⊤ :=
  F.zStar_eq_top_of_forall_negMoment_ne_top h

theorem ofReal_lt_zStar_of_all (h : F.AllNegMomentsFinite) (c : ℝ) :
    ENNReal.ofReal c < F.zStar := by
  rw [F.zStar_eq_top h]
  exact ENNReal.ofReal_lt_top

theorem ofReal_lt_zStar_sub_one_of_all (h : F.AllNegMomentsFinite) (c : ℝ) :
    ENNReal.ofReal c < F.zStar - 1 := by
  rw [F.zStar_eq_top h, show (⊤ : ℝ≥0∞) - 1 = ⊤ from by simp]
  exact ENNReal.ofReal_lt_top

theorem momentInterval_eq_Ioi (h : F.AllNegMomentsFinite) : F.momentInterval = Ioi 0 := by
  ext c
  exact ⟨fun hc => hc.1, fun hc => ⟨hc, F.ofReal_lt_zStar_of_all h c⟩⟩

/-! ## `m` is right-continuous at `1`

The dominated-convergence argument of `tendsto_negMoment_nhdsGT_zero`, one unit to the right. The
dominating function is `t^{-2} + 1`, and `A13` is exactly what makes it integrable. -/

theorem tendsto_negMoment_succ_nhdsGT_zero (hH : F.StandingHypothesis)
    (h : F.AllNegMomentsFinite) :
    Tendsto (fun z : ℝ => (F.negMoment (z + 1)).toReal) (𝓝[>] (0 : ℝ))
      (𝓝 (F.negMoment 1).toReal) := by
  have h0 := F.lawT₁_singleton_zero hH.1
  have hae := F.ae_mem_Ioi_lawT₁ h0
  have hbound : Integrable (fun t : ℝ => t ^ (-(2 : ℝ)) + 1) F.lawT₁ :=
    (integrable_rpow_neg F hH two_pos (F.ofReal_lt_zStar_of_all h 2)).add (integrable_const 1)
  have hle1 : ∀ᶠ z : ℝ in 𝓝[>] (0 : ℝ), z ≤ 1 :=
    Filter.Eventually.mono (nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)))
      fun _ hx => le_of_lt hx
  have key : Tendsto (fun z : ℝ => ∫ t, t ^ (-(z + 1)) ∂F.lawT₁) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ t, t ^ (-(1 : ℝ)) ∂F.lawT₁)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun t : ℝ => t ^ (-(2 : ℝ)) + 1) (Filter.Eventually.of_forall fun z => by fun_prop)
      ?_ hbound ?_
    · filter_upwards [self_mem_nhdsWithin, hle1] with z hz hz1
      filter_upwards [hae] with t ht
      have ht0 : (0 : ℝ) < t := ht
      have hz0 : (0 : ℝ) < z := hz
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
      rcases le_total t 1 with h1 | h1
      · have := Real.rpow_le_rpow_of_exponent_ge ht0 h1 (by linarith : -2 ≤ -(z + 1))
        have hnn : (0 : ℝ) ≤ (1 : ℝ) := zero_le_one
        linarith
      · have := Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith : -(z + 1) ≤ 0)
        have hnn : (0 : ℝ) ≤ t ^ (-(2 : ℝ)) := Real.rpow_nonneg ht0.le _
        linarith
    · filter_upwards [hae] with t ht
      have ht0 : (0 : ℝ) < t := ht
      have hexp : ∀ z : ℝ, t ^ (-(z + 1)) = Real.exp (Real.log t * (-(z + 1))) :=
        fun z => Real.rpow_def_of_pos ht0 _
      have hcont : Continuous fun z : ℝ => Real.exp (Real.log t * (-(z + 1))) := by fun_prop
      have hlim := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Ioi 0))
      simpa [hexp, Real.rpow_def_of_pos ht0] using hlim
  have hrw : ∀ c : ℝ, ∫ t, t ^ (-c) ∂F.lawT₁ = (F.negMoment c).toReal :=
    fun c => F.integral_rpow_neg_eq_negMoment h0
  have hfun : (fun z : ℝ => (F.negMoment (z + 1)).toReal)
      = fun z : ℝ => ∫ t, t ^ (-(z + 1)) ∂F.lawT₁ := funext fun z => (hrw (z + 1)).symm
  rw [hfun, ← hrw 1]
  exact key

/-! ## The order-two classification -/

/-- **`thm:locality`(⇒), the order-two branch.** A local operator of order `2` forces
`m(z) = c₂^z Γ(a+z)/Γ(a)` on `(0,∞)`, with `c₂ > 0` and `a > 0` --- so `T₁ ≐ 1/(c₂γ_a)`, the
inverse-gamma family, and the time normalisation `c₂ = 2` gives `prop:bessel-family`.

The two citations are hypotheses: `hA13` is `lem:moment-recursion`(2) and the order `2` is
Courrège's bound. Everything between them is proved. -/
theorem exists_gamma_form_of_isLocalOfOrder_two (hH : F.StandingHypothesis)
    (hA13 : F.AllNegMomentsFinite) {c : ℝ} (hc : 0 < c) (hL : F.IsLocalOfOrder c 2) :
    ∃ c₂ a : ℝ, 0 < c₂ ∧ 0 < a ∧
      ∀ z : ℝ, 0 < z → (F.negMoment z).toReal
        = c₂ ^ z * Real.Gamma (a + z) / Real.Gamma a := by
  have h0 := F.lawT₁_singleton_zero hH.1
  have hc' : ENNReal.ofReal c < F.zStar - 1 := F.ofReal_lt_zStar_sub_one_of_all hA13 c
  set γ : ℕ → ℂ := fun j => hL.coeff j 1 with hγdef
  have hsymbol : ∀ z : ℂ, 0 < z.re → ENNReal.ofReal z.re < F.zStar - 1 →
      mellin (fun s => (F.profile s : ℂ)) z ≠ 0 →
      F.inversionSymbol z = ∑ j ∈ Finset.range (2 + 1), γ j * mellinEulerFactor j z :=
    fun z hz hz' hne =>
      (F.sameSymbolAction_of_isLocalOfOrder hH hc hc' hL).eqOn_of_ne_zero ⟨⟨hz, hz'⟩, hne⟩
  -- the recursion, on the whole half-line
  have hrec : ∀ z : ℝ, 0 < z → ∃ q : ℝ, 0 < q ∧ symbolQuotient γ 2 (z : ℂ) = (q : ℂ) ∧
      (F.negMoment (z + 1)).toReal = q * (F.negMoment z).toReal :=
    fun z hz => F.exists_pos_symbolQuotient_of_symbol_eq hH γ hsymbol hz
      (F.ofReal_lt_zStar_sub_one_of_all hA13 z)
  -- `Q` is linear, so its two coefficients are real
  obtain ⟨q₁, hq₁pos, hq₁, hrec₁⟩ := hrec 1 one_pos
  obtain ⟨q₂, hq₂pos, hq₂, -⟩ := hrec 2 two_pos
  rw [symbolQuotient_two] at hq₁ hq₂
  push_cast at hq₁ hq₂
  have hγ2 : γ 2 = ((q₂ - q₁ : ℝ) : ℂ) := by push_cast; linear_combination hq₂ - hq₁
  have hγ1 : γ 1 = ((2 * q₂ - 3 * q₁ : ℝ) : ℂ) := by
    push_cast; linear_combination 2 * hq₂ - 3 * hq₁
  -- so `q z = c₂ z + a₀` at every real point
  have hq : ∀ z : ℝ, ∀ q : ℝ, symbolQuotient γ 2 (z : ℂ) = (q : ℂ) →
      q = (q₂ - q₁) * z + (2 * q₁ - q₂) := by
    intro z q hqz
    rw [symbolQuotient_two, hγ2, hγ1] at hqz
    have hcast : (((q₂ - q₁) * z + (2 * q₁ - q₂) : ℝ) : ℂ) = ((q : ℝ) : ℂ) := by
      push_cast
      push_cast at hqz
      linear_combination hqz
    exact (by exact_mod_cast hcast : (q₂ - q₁) * z + (2 * q₁ - q₂) = q).symm
  set c₂ : ℝ := q₂ - q₁ with hc₂def
  set a₀ : ℝ := 2 * q₁ - q₂ with ha₀def
  have hqpos : ∀ z : ℝ, 0 < z → 0 < c₂ * z + a₀ := by
    intro z hz
    obtain ⟨q, hqpos, hqz, -⟩ := hrec z hz
    rw [← hq z q hqz]
    exact hqpos
  -- `c₂ > 0`: it is `γ₂`, nonzero by the order, and nonnegative because `Q > 0` far out
  have hc₂ne : c₂ ≠ 0 := by
    intro hzero
    refine hL.leading_ne_zero.choose_spec.2 ?_
    obtain ⟨x₀, hx₀, -⟩ := hL.leading_ne_zero
    have hcoeff := F.coeff_eq_of_isLocalOfOrder hL.toIsLocalOfOrderCore (le_refl 2)
      hL.leading_ne_zero.choose_spec.1
    rw [hcoeff, show hL.coeff 2 1 = γ 2 from rfl, hγ2, hzero]
    simp
  have hc₂pos : 0 < c₂ := by
    rcases lt_trichotomy c₂ 0 with hneg | hz | hpos
    · exfalso
      have hz₀ : (0 : ℝ) < (1 + |a₀|) / (-c₂) := div_pos (by positivity) (by linarith)
      have hpos := hqpos _ hz₀
      have hcalc : c₂ * ((1 + |a₀|) / (-c₂)) = -(1 + |a₀|) := by
        field_simp
      rw [hcalc] at hpos
      linarith [le_abs_self a₀, abs_nonneg a₀]
    · exact absurd hz hc₂ne
    · exact hpos
  -- `a₀ > 0`: it is `Q(0)`, and `Q(0) = m(1)`, which is positive
  have hm1 : 0 < (F.negMoment 1).toReal := F.negMoment_toReal_pos hH one_pos
    (F.ofReal_lt_zStar_of_all hA13 1)
  have ha₀pos : 0 < a₀ := by
    have hnum := F.tendsto_negMoment_succ_nhdsGT_zero hH hA13
    have hden := F.tendsto_negMoment_nhdsGT_zero hH
    have hprod : Tendsto (fun z : ℝ => (c₂ * z + a₀) * (F.negMoment z).toReal)
        (𝓝[>] (0 : ℝ)) (𝓝 (a₀ * 1)) := by
      refine Tendsto.mul ?_ hden
      have hlin : Tendsto (fun z : ℝ => c₂ * z + a₀) (𝓝[>] (0 : ℝ)) (𝓝 (c₂ * 0 + a₀)) :=
        (Tendsto.const_mul c₂ (tendsto_id.mono_left nhdsWithin_le_nhds)).add_const a₀
      simpa using hlin
    have heq : ∀ᶠ z : ℝ in 𝓝[>] (0 : ℝ),
        (F.negMoment (z + 1)).toReal = (c₂ * z + a₀) * (F.negMoment z).toReal := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      obtain ⟨q, -, hqz, hqrec⟩ := hrec z hz
      rw [hqrec, hq z q hqz]
    have := tendsto_nhds_unique (hnum.congr' heq) hprod
    rw [mul_one] at this
    linarith [this ▸ hm1]
  -- and now Bohr--Mollerup
  refine ⟨c₂, a₀ / c₂, hc₂pos, div_pos ha₀pos hc₂pos, ?_⟩
  refine eq_gamma_form_of_logConvex_of_recursion hc₂pos (div_pos ha₀pos hc₂pos)
    (fun z hz => F.negMoment_toReal_pos hH hz (F.ofReal_lt_zStar_of_all hA13 z)) ?_ ?_
    (F.tendsto_negMoment_nhdsGT_zero hH)
  · have := F.convexOn_log_negMoment h0
    rwa [F.momentInterval_eq_Ioi hA13] at this
  · intro z hz
    obtain ⟨q, -, hqz, hqrec⟩ := hrec z hz
    rw [hqrec, hq z q hqz]
    congr 1
    field_simp

end SelfDecomposableExponent

end Hemigroup
