/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Hemigroup.ZStarDriftless
import Hemigroup.MeanDelay
import Hemigroup.AdmissibleCone

/-!
# `lem:zstar-log-growth` (11.23), clauses (1) and (4): the limit is `z_*`

Clause (2) (`Hemigroup/ZStarLogGrowth.lean`, `Hemigroup/ZStarDriftless.lean`) gives the limit
`L = lim F(s)/log s` in `[0,∞]`: `∞` with drift, the catalogue height `k(0⁺)` without. Clause (1)
identifies it with `z_*`, the abscissa of the negative moments of `T₁`; clause (4) is then the
homogeneity of `z_*` on the admissible cone.

## The route: an Abelian comparison, and nothing else

The hinge is `Γ(ζ)·E[T₁^{-ζ}] = ∫₀^∞ s^{ζ-1}e^{-F(s)}ds` (`gamma_mul_negMoment`): Tonelli against
`lintegral_lintegral_gamma_of_ae_mem_Ioi`, the inner integral evaluated by `laplaceL_lawT₁`. It
is the route `stableExponent_negMoment_ne_top` takes, with `e^{-F}` in place of `e^{-s^α}`. On
`(0,S]` the integrand is at most `s^{ζ-1}`, integrable for `ζ > 0`, so only the tail decides:

* for `ζ < c < L`, eventually `F(s) ≥ c log s`, so `e^{-F(s)} ≤ s^{-c}` and the tail is dominated
  by `s^{ζ-1-c}`, integrable (`negMoment_ne_top_of_le_exponent`);
* for `L < c < ζ`, eventually `F(s) ≤ c log s`, so the tail dominates `s^{ζ-1-c}`, whose integral
  over `(S,∞)` is infinite (`negMoment_eq_top_of_exponent_le`).

`zStar_eq_of_tendsto` squeezes the supremum defining `z_*` between the two, for **any** limit `L`
in `[0,∞]`, and the drift case needs no separate reading off `negMoment`: `L = ∞` makes the second
bullet vacuous and the first gives every `ζ`. The no-atom hypothesis enters only through the
hinge, where `negMoment` (an integral over `Ioi 0`) has to be the whole integral against `T₁`.

Clause (4) is then arithmetic: `(cF)(s) = c·F(s)` (`exponent_smul`), so the scaled limit is
`c·L`, and `cF` inherits the no-atom hypothesis from `F → ∞`.
-/

namespace Hemigroup

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- `∫_S^∞ s^a ds = ∞` for `a ≥ -1`, in `lintegral` form. -/
theorem lintegral_Ioi_rpow_eq_top {S a : ℝ} (hS : 0 < S) (ha : -1 ≤ a) :
    ∫⁻ s in Ioi S, ENNReal.ofReal (s ^ a) = ⊤ := by
  by_contra hne
  have hint : IntegrableOn (fun s : ℝ => s ^ a) (Ioi S) := by
    refine ⟨(by fun_prop : Measurable fun s : ℝ => s ^ a).aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun s hs => Real.rpow_nonneg (lt_trans hS hs).le a))).mpr
      (lt_top_iff_ne_top.mpr hne)
  exact absurd ((integrableOn_Ioi_rpow_iff hS).mp hint) (not_lt.mpr ha)

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent)

theorem toRealExponent_nonneg (s : ℝ) : 0 ≤ F.toRealExponent s := ENNReal.toReal_nonneg

/-- **The hinge**: `Γ(ζ)·E[T₁^{-ζ}] = ∫₀^∞ s^{ζ-1}e^{-F(s)}ds`, for any exponent whose `T₁` has
no atom at the origin. -/
theorem gamma_mul_negMoment (h0 : F.lawT₁ {(0 : ℝ)} = 0) {ζ : ℝ} (hζ : 0 < ζ) :
    ENNReal.ofReal (Real.Gamma ζ) * F.negMoment ζ
      = ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (ζ - 1) * Real.exp (-F.toRealExponent s)) := by
  have hν := F.ae_mem_Ioi_lawT₁ h0
  have hmeas : Measurable (Function.uncurry fun t s : ℝ =>
      ENNReal.ofReal (s ^ (ζ - 1) * Real.exp (-(t * s)))) := by fun_prop
  have hswap := lintegral_lintegral_swap (μ := F.lawT₁) (ν := volume.restrict (Ioi (0 : ℝ)))
    hmeas.aemeasurable
  have hinner : ∀ s ∈ Ioi (0 : ℝ),
      (∫⁻ t, ENNReal.ofReal (s ^ (ζ - 1) * Real.exp (-(t * s))) ∂F.lawT₁)
        = ENNReal.ofReal (s ^ (ζ - 1) * Real.exp (-F.toRealExponent s)) := by
    intro s hs
    have hs' : (0 : ℝ) < s := hs
    have hcongr : (fun t : ℝ => ENNReal.ofReal (s ^ (ζ - 1) * Real.exp (-(t * s))))
        = fun t : ℝ => ENNReal.ofReal (s ^ (ζ - 1)) * ENNReal.ofReal (Real.exp (-(s * t))) := by
      funext t
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hs'.le _), show t * s = s * t from mul_comm t s]
    rw [hcongr, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    change ENNReal.ofReal (s ^ (ζ - 1)) * laplaceL F.lawT₁ s = _
    rw [F.laplaceL_lawT₁ hs'.le, ← ENNReal.ofReal_mul (Real.rpow_nonneg hs'.le _)]
  rw [F.negMoment_eq_lintegral h0, ← lintegral_lintegral_gamma_of_ae_mem_Ioi hν hζ, hswap]
  exact setLIntegral_congr_fun measurableSet_Ioi hinner

/-- **The convergent tail.** If eventually `F(s) ≥ c log s` with `c > ζ`, the `ζ`-th negative
moment is finite. -/
theorem negMoment_ne_top_of_le_exponent (h0 : F.lawT₁ {(0 : ℝ)} = 0) {ζ c S : ℝ}
    (hζ : 0 < ζ) (hζc : ζ < c) (hS : 1 ≤ S)
    (hF : ∀ s, S ≤ s → c * Real.log s ≤ F.toRealExponent s) : F.negMoment ζ ≠ ⊤ := by
  have hS0 : (0 : ℝ) < S := by linarith
  have hΓ : ENNReal.ofReal (Real.Gamma ζ) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.Gamma_pos_of_pos hζ)).ne'
  have hle : ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (ζ - 1) * Real.exp (-F.toRealExponent s))
      ≤ (∫⁻ s in Ioc 0 S, ENNReal.ofReal (s ^ (ζ - 1)))
        + ∫⁻ s in Ioi S, ENNReal.ofReal (s ^ (ζ - 1 - c)) := by
    rw [← Ioc_union_Ioi_eq_Ioi hS0.le]
    refine (lintegral_union_le _ _ _).trans (add_le_add ?_ ?_)
    · refine setLIntegral_mono' measurableSet_Ioc fun s hs => ENNReal.ofReal_le_ofReal ?_
      have hs0 : 0 < s := hs.1
      calc s ^ (ζ - 1) * Real.exp (-F.toRealExponent s) ≤ s ^ (ζ - 1) * 1 :=
            mul_le_mul_of_nonneg_left
              (Real.exp_le_one_iff.mpr (by linarith [F.toRealExponent_nonneg s]))
              (Real.rpow_nonneg hs0.le _)
        _ = s ^ (ζ - 1) := mul_one _
    · refine setLIntegral_mono' measurableSet_Ioi fun s hs => ENNReal.ofReal_le_ofReal ?_
      have hs0 : 0 < s := lt_trans hS0 hs
      rw [show ζ - 1 - c = (ζ - 1) + -c by ring, Real.rpow_add hs0]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hs0.le _)
      rw [Real.rpow_def_of_pos hs0]
      exact Real.exp_le_exp.mpr (by nlinarith [hF s (le_of_lt hs)])
  have h1 : (∫⁻ s in Ioc 0 S, ENNReal.ofReal (s ^ (ζ - 1))) ≠ ⊤ :=
    lintegral_ofReal_ne_top_of_integrableOn
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hS0.le).mp
        (intervalIntegral.intervalIntegrable_rpow' (by linarith)))
  have h2 : (∫⁻ s in Ioi S, ENNReal.ofReal (s ^ (ζ - 1 - c))) ≠ ⊤ :=
    lintegral_ofReal_ne_top_of_integrableOn (integrableOn_Ioi_rpow_of_lt (by linarith) hS0)
  intro htop
  have h := F.gamma_mul_negMoment h0 hζ
  rw [htop, ENNReal.mul_top hΓ] at h
  rw [← h, top_le_iff] at hle
  exact ENNReal.add_ne_top.mpr ⟨h1, h2⟩ hle

/-- **The divergent tail.** If eventually `F(s) ≤ c log s` with `c < ζ`, the `ζ`-th negative
moment is infinite. -/
theorem negMoment_eq_top_of_exponent_le (h0 : F.lawT₁ {(0 : ℝ)} = 0) {ζ c S : ℝ}
    (hζ : 0 < ζ) (hcζ : c < ζ) (hS : 1 ≤ S)
    (hF : ∀ s, S ≤ s → F.toRealExponent s ≤ c * Real.log s) : F.negMoment ζ = ⊤ := by
  have hS0 : (0 : ℝ) < S := by linarith
  have hge : ∫⁻ s in Ioi S, ENNReal.ofReal (s ^ (ζ - 1 - c))
      ≤ ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (ζ - 1) * Real.exp (-F.toRealExponent s)) := by
    calc _ ≤ ∫⁻ s in Ioi S, ENNReal.ofReal (s ^ (ζ - 1) * Real.exp (-F.toRealExponent s)) := by
          refine setLIntegral_mono' measurableSet_Ioi fun s hs => ENNReal.ofReal_le_ofReal ?_
          have hs0 : 0 < s := lt_trans hS0 hs
          rw [show ζ - 1 - c = (ζ - 1) + -c by ring, Real.rpow_add hs0]
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hs0.le _)
          rw [Real.rpow_def_of_pos hs0]
          exact Real.exp_le_exp.mpr (by nlinarith [hF s (le_of_lt hs)])
      _ ≤ _ := lintegral_mono_set (Ioi_subset_Ioi hS0.le)
  rw [lintegral_Ioi_rpow_eq_top hS0 (by linarith), top_le_iff,
    ← F.gamma_mul_negMoment h0 hζ] at hge
  exact (ENNReal.mul_eq_top.mp hge).elim (fun h => h.2) (fun h => absurd h.1 ENNReal.ofReal_ne_top)

/-- **The Abelian comparison.** Whatever the limit `L ∈ [0,∞]` of `F(s)/log s` is, it is `z_*`. -/
theorem zStar_eq_of_tendsto (h0 : F.lawT₁ {(0 : ℝ)} = 0) {L : ℝ≥0∞}
    (hL : Tendsto (fun s => ENNReal.ofReal (F.toRealExponent s / Real.log s)) atTop (𝓝 L)) :
    F.zStar = L := by
  refine le_antisymm ?_ ?_
  · refine sSup_le ?_
    rintro _ ⟨ζ, ⟨hζ, hfin⟩, rfl⟩
    by_contra hlt
    push Not at hlt
    obtain ⟨c, -, hLc, hcζ⟩ := ENNReal.lt_iff_exists_real_btwn.mp hlt
    have hcζ' : c < ζ := (ENNReal.ofReal_lt_ofReal_iff hζ).mp hcζ
    obtain ⟨S, hS⟩ := eventually_atTop.mp
      ((hL.eventually (gt_mem_nhds hLc)).and (eventually_gt_atTop (1 : ℝ)))
    refine hfin (F.negMoment_eq_top_of_exponent_le h0 hζ hcζ' (le_max_right S 1) fun s hs => ?_)
    obtain ⟨h1, h2⟩ := hS s ((le_max_left _ _).trans hs)
    have hlog : 0 < Real.log s := Real.log_pos h2
    exact ((div_lt_iff₀ hlog).mp (ENNReal.ofReal_lt_ofReal_iff'.mp h1).1).le
  · refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    rcases eq_or_ne r 0 with rfl | hr0
    · simp
    have hζ : (0 : ℝ) < r := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr0)
    rw [← ENNReal.ofReal_coe_nnreal] at hr ⊢
    obtain ⟨c, -, hrc, hcL⟩ := ENNReal.lt_iff_exists_real_btwn.mp hr
    have hrc' : (r : ℝ) < c := (ENNReal.ofReal_lt_ofReal_iff'.mp hrc).1
    obtain ⟨S, hS⟩ := eventually_atTop.mp
      ((hL.eventually (lt_mem_nhds hcL)).and (eventually_gt_atTop (1 : ℝ)))
    refine F.le_zStar_of_negMoment_ne_top hζ
      (F.negMoment_ne_top_of_le_exponent h0 hζ hrc' (le_max_right S 1) fun s hs => ?_)
    obtain ⟨h1, h2⟩ := hS s ((le_max_left _ _).trans hs)
    have hlog : 0 < Real.log s := Real.log_pos h2
    exact (le_div_iff₀ hlog).mp (ENNReal.ofReal_lt_ofReal_iff'.mp h1).1.le

/-- **`lem:zstar-log-growth`(1)**: the log-growth limit `F(s)/log s` exists in `[0,∞]` and equals
`z_*`. The no-atom hypothesis is load-bearing: `negMoment` and `zStar` integrate over `Ioi 0` and
are blind to an atom at the origin, exactly as in `lem:mellin-data` and
`lem:standing-kernel-readings`. -/
theorem tendsto_toRealExponent_div_log_atTop_zStar (h0 : F.lawT₁ {(0 : ℝ)} = 0) :
    Tendsto (fun s => ENNReal.ofReal (F.toRealExponent s / Real.log s)) atTop (𝓝 F.zStar) := by
  obtain ⟨L, hL⟩ : ∃ L, Tendsto (fun s => ENNReal.ofReal (F.toRealExponent s / Real.log s))
      atTop (𝓝 L) := by
    rcases F.b₀_nonneg.lt_or_eq with hb | hb
    · exact ⟨⊤, ENNReal.tendsto_ofReal_atTop.comp
        (F.tendsto_toRealExponent_div_log_atTop_of_b₀_pos hb)⟩
    · exact ⟨_, F.tendsto_toRealExponent_div_log_atTop_of_b₀_zero hb.symm⟩
  rwa [F.zStar_eq_of_tendsto h0 hL]

/-- `(cF)(s) = c·F(s)` in the real reading. -/
theorem toRealExponent_smul {c : ℝ} (hc : 0 ≤ c) {s : ℝ} (hs : 0 ≤ s) :
    (F.smul hc).toRealExponent s = c * F.toRealExponent s := by
  rw [toRealExponent, toRealExponent, F.exponent_smul hc hs, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hc]

/-- **`lem:zstar-log-growth`(4)**: `z_*` is homogeneous of degree one on the admissible cone. -/
theorem zStar_smul (h0 : F.lawT₁ {(0 : ℝ)} = 0) {c : ℝ} (hc : 0 < c) :
    (F.smul hc.le).zStar = ENNReal.ofReal c * F.zStar := by
  have hF := F.tendsto_toRealExponent_atTop_of_lawT₁_singleton_zero h0
  have h0' : (F.smul hc.le).lawT₁ {(0 : ℝ)} = 0 := by
    refine (F.smul hc.le).lawT₁_singleton_zero ((Tendsto.const_mul_atTop hc hF).congr' ?_)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    exact (F.toRealExponent_smul hc.le hs).symm
  refine (F.smul hc.le).zStar_eq_of_tendsto h0' ?_
  have hlim := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal c)
    (F.tendsto_toRealExponent_div_log_atTop_zStar h0) (Or.inr ENNReal.ofReal_ne_top)
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
  rw [F.toRealExponent_smul hc.le hs, mul_div_assoc, ENNReal.ofReal_mul hc.le]

end SelfDecomposableExponent

end Hemigroup
