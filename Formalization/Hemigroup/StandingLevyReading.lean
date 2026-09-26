/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Hemigroup.MemoryFractional

/-!
# `lem:standing-levy-reading` (11.22)

The reading of the first clause of `def:standing-hypothesis` — `F(∞) = ∞` — in the `(b₀, k)` data
of (7.1), rather than in the law of `T₁` that `lem:standing-kernel-readings` (11.21) uses.

## What the two clauses cost

Clause (1) is monotone convergence in `s` for `levyJump`, read in both directions of an `iff`:
the total Lévy mass `∫₀^∞ k(t)/t dt` is the increasing limit of `F`'s jump part, so the exponent
is unbounded exactly when the drift is positive or that mass is infinite. Nothing here needs the
law of `T₁`, and nothing needs an interface.

**The `ℝ≥0∞` bridge the annotation priced is not needed.** The target types were written expecting
an argument carrying an `ℝ≥0∞`-valued limit at `s → ∞` across to the `ℝ`-valued `atTop` reading
`toRealExponent` carries. In the event only the *divergent* side needs a limit at all: the
convergent side is a uniform bound, `levyJump k s ≤ levyMass k` for every `s`, which is
`1 - e^{-st} ≤ 1` and no convergence theorem. So monotone convergence is used once, along the
naturals, and in one direction.

Clause (2) is where self-decomposability does work a general Lévy exponent would not do. A
compound Poisson exponent with finite Lévy mass and no drift is bounded, so "nonzero implies
`F(∞) = ∞`" is *false* in `LE`; it holds here because the density of the Lévy measure against
`dt/t` is **nonincreasing**. If `k` is positive anywhere it is bounded below by that value on the
whole of `(0,t₀]`, and `∫₀^{t₀} dt/t = ∞`. The divergence is carried entirely by the origin, and
the admissible cone has no bounded nonzero member.

`lintegral_inv_Ioc_eq_top` is that computation. Mathlib has the divergence in its *integrability*
form (`intervalIntegrable_inv_iff`); what a lower bound on an `ℝ≥0∞`-valued mass needs is the
`lintegral` form, and the passage between them is `hasFiniteIntegral_iff_ofReal`.
-/

namespace Hemigroup

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## The total Lévy mass as the limit of the jump part -/

variable {k : ℝ → ℝ}

/-- The total mass of the Lévy measure of (7.1): `∫₀^∞ k(t)/t dt`, in `[0,∞]`. -/
noncomputable def levyMass (k : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (k t / t)

/-- The jump part never exceeds the total mass: `1 - e^{-st} ≤ 1`. No sign condition on `s` —
for `s < 0` the integrand is nonpositive and `ENNReal.ofReal` truncates it to `0`. -/
lemma levyJump_le_levyMass (hk : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ k t) (s : ℝ) :
    levyJump k s ≤ levyMass k := by
  refine lintegral_mono_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  have ht' : (0 : ℝ) < t := ht
  have hw : 1 - Real.exp (-(s * t)) ≤ 1 := by
    have := Real.exp_pos (-(s * t)); linarith
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_le_div_iff_of_pos_right ht']
  exact mul_le_of_le_one_left (hk t ht) hw

/-- **Monotone convergence in `s`.** Along the naturals the jump part increases to the total
mass — the one convergence argument clause (1) needs. -/
lemma tendsto_levyJump_atTop_levyMass (hk : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ k t)
    (hkm : AEMeasurable k (volume.restrict (Ioi (0 : ℝ)))) :
    Tendsto (fun n : ℕ => levyJump k n) atTop (𝓝 (levyMass k)) := by
  refine lintegral_tendsto_of_tendsto_of_monotone
    (fun n => aemeasurable_levyJump_integrand hkm n) ?_ ?_
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht m n hmn
    have ht' : (0 : ℝ) < t := ht
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_div_iff_of_pos_right ht']
    have hmn' : (m : ℝ) * t ≤ (n : ℝ) * t :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hmn) ht'.le
    have hexp : Real.exp (-((n : ℝ) * t)) ≤ Real.exp (-((m : ℝ) * t)) :=
      Real.exp_le_exp.2 (by linarith)
    exact mul_le_mul_of_nonneg_right (by linarith) (hk t ht)
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have ht' : (0 : ℝ) < t := ht
    have hexp : Tendsto (fun n : ℕ => Real.exp (-((n : ℝ) * t))) atTop (𝓝 0) := by
      refine Real.tendsto_exp_atBot.comp ?_
      refine tendsto_neg_atBot_iff.2 ?_
      exact Filter.Tendsto.atTop_mul_const ht' tendsto_natCast_atTop_atTop
    have hreal : Tendsto (fun n : ℕ => (1 - Real.exp (-((n : ℝ) * t))) * k t / t) atTop
        (𝓝 (k t / t)) := by
      have h1 : Tendsto (fun n : ℕ => (1 - Real.exp (-((n : ℝ) * t))) * k t / t) atTop
          (𝓝 ((1 - 0) * k t / t)) :=
        ((tendsto_const_nhds.sub hexp).mul tendsto_const_nhds).div_const t
      simpa using h1
    exact (ENNReal.continuous_ofReal.tendsto _).comp hreal

/-! ## The divergence at the origin -/

/-- `∫₀^{a} dt/t = ∞` for every `a > 0`, as an `ℝ≥0∞`-valued integral. -/
lemma lintegral_inv_Ioc_eq_top {a : ℝ} (ha : 0 < a) :
    ∫⁻ t in Ioc (0 : ℝ) a, ENNReal.ofReal t⁻¹ = ⊤ := by
  by_contra h
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) a)] fun t : ℝ => t⁻¹ := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    exact inv_nonneg.2 ht.1.le
  have hint : IntegrableOn (fun t : ℝ => t⁻¹) (Ioc (0 : ℝ) a) := by
    refine ⟨(by fun_prop : Measurable fun t : ℝ => t⁻¹).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hnn]
    exact lt_top_iff_ne_top.2 h
  have hii := (intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le).2 hint
  rw [intervalIntegrable_inv_iff] at hii
  rcases hii with h1 | h2
  · exact ha.ne h1
  · exact h2 (by rw [Set.uIcc_of_le ha.le]; exact ⟨le_rfl, ha.le⟩)

/-- **A nonzero admissible density has infinite Lévy mass.** `k` nonincreasing is what makes this
true; for a general Lévy density it is false. -/
lemma levyMass_eq_top_of_ne_zero
    (hanti : AntitoneOn k (Ioi (0 : ℝ))) {t₀ : ℝ} (ht₀ : 0 < t₀) (hpos : 0 < k t₀) :
    levyMass k = ⊤ := by
  have hne : ENNReal.ofReal (k t₀) ≠ 0 := (ENNReal.ofReal_pos.2 hpos).ne'
  have hconst : ∫⁻ t in Ioc (0 : ℝ) t₀, ENNReal.ofReal (k t₀) * ENNReal.ofReal t⁻¹
      = ENNReal.ofReal (k t₀) * ∫⁻ t in Ioc (0 : ℝ) t₀, ENNReal.ofReal t⁻¹ :=
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hbelow : ∫⁻ t in Ioc (0 : ℝ) t₀, ENNReal.ofReal (k t₀) * ENNReal.ofReal t⁻¹
      ≤ ∫⁻ t in Ioc (0 : ℝ) t₀, ENNReal.ofReal (k t / t) := by
    refine lintegral_mono_ae ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    have ht' : (0 : ℝ) < t := ht.1
    have hkt : k t₀ ≤ k t := hanti (mem_Ioi.mpr ht') (mem_Ioi.mpr ht₀) ht.2
    rw [← ENNReal.ofReal_mul hpos.le]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hkt (inv_nonneg.2 ht'.le)
  have hmass : ∫⁻ t in Ioc (0 : ℝ) t₀, ENNReal.ofReal (k t / t) ≤ levyMass k :=
    lintegral_mono_set Ioc_subset_Ioi_self
  refine top_le_iff.1 (le_trans ?_ hmass)
  calc (⊤ : ℝ≥0∞) = ENNReal.ofReal (k t₀) * ⊤ := (ENNReal.mul_top hne).symm
    _ = ∫⁻ t in Ioc (0 : ℝ) t₀, ENNReal.ofReal (k t₀) * ENNReal.ofReal t⁻¹ := by
        rw [hconst, lintegral_inv_Ioc_eq_top ht₀]
    _ ≤ ∫⁻ t in Ioc (0 : ℝ) t₀, ENNReal.ofReal (k t / t) := hbelow

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent)

/-- **`lem:standing-levy-reading`(1)**: `F(∞) = ∞` iff the exponent carries drift or infinite
Lévy mass — the reading of the first clause of (H) in the `(b₀, k)` data of (7.1). -/
theorem tendsto_toRealExponent_atTop_iff_levy :
    Tendsto F.toRealExponent atTop atTop ↔ 0 < F.b₀ ∨ levyMass F.k = ⊤ := by
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    obtain ⟨hb, hM⟩ := hcon
    have hb0 : F.b₀ = 0 := le_antisymm hb F.b₀_nonneg
    have hbd : ∀ s : ℝ, F.toRealExponent s ≤ (levyMass F.k).toReal := by
      intro s
      have hle : F.exponent s ≤ levyMass F.k := by
        simp only [exponent, levyExponentD, hb0, zero_mul, ENNReal.ofReal_zero, zero_add]
        exact levyJump_le_levyMass F.k_nonneg s
      exact ENNReal.toReal_mono hM hle
    obtain ⟨s, hs1⟩ := (h.eventually_ge_atTop ((levyMass F.k).toReal + 1)).exists
    linarith [hbd s]
  · rintro (hb | hM)
    · refine tendsto_atTop_mono' _ ?_ (Filter.Tendsto.const_mul_atTop hb tendsto_id)
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
      have hle : ENNReal.ofReal (F.b₀ * s) ≤ F.exponent s := by
        simp only [exponent, levyExponentD]; exact le_self_add
      have h2 := ENNReal.toReal_mono (F.ne_top s hs) hle
      rwa [ENNReal.toReal_ofReal (mul_nonneg F.b₀_nonneg hs)] at h2
    · refine tendsto_atTop.2 fun b => ?_
      rcases le_or_gt b 0 with hb | hb
      · filter_upwards with s using hb.trans ENNReal.toReal_nonneg
      · have hlim := tendsto_levyJump_atTop_levyMass F.k_nonneg
          (aemeasurable_of_antitoneOn F.k_antitone)
        rw [hM] at hlim
        have hev : ∀ᶠ n : ℕ in atTop, ENNReal.ofReal b < levyJump F.k n :=
          hlim.eventually (lt_mem_nhds ENNReal.ofReal_lt_top)
        obtain ⟨n, hn, hn0⟩ := (hev.and (eventually_gt_atTop 0)).exists
        have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
        filter_upwards [eventually_ge_atTop ((n : ℝ))] with s hs
        have hmono : F.exponent (n : ℝ) ≤ F.exponent s := exponent_mono F hnpos hs
        have hlow : ENNReal.ofReal b < F.exponent s := by
          refine lt_of_lt_of_le hn (le_trans ?_ hmono)
          simp only [exponent, levyExponentD]; exact le_add_self
        have hsn : (0 : ℝ) ≤ s := le_trans hnpos.le hs
        exact le_of_lt ((ENNReal.ofReal_lt_iff_lt_toReal hb.le (F.ne_top s hsn)).1 hlow)

/-- **`lem:standing-levy-reading`(2)**: a nonzero admissible exponent automatically satisfies the
first clause of (H) — so, within the admissible class, (H) reduces to its second clause,
`z_* > 1`. -/
theorem tendsto_toRealExponent_atTop_of_ne_zero
    (hF : ∃ s₀, 0 < s₀ ∧ F.exponent s₀ ≠ 0) :
    Tendsto F.toRealExponent atTop atTop := by
  refine F.tendsto_toRealExponent_atTop_iff_levy.2 ?_
  rcases F.b₀_nonneg.lt_or_eq with hb | hb
  · exact Or.inl hb
  · refine Or.inr ?_
    obtain ⟨s₀, hs₀, hne⟩ := hF
    have hjump : levyJump F.k s₀ ≠ 0 := by
      intro h
      refine hne ?_
      simp only [exponent, levyExponentD, ← hb, zero_mul, ENNReal.ofReal_zero, zero_add, h]
    have hex : ∃ t₀, 0 < t₀ ∧ 0 < F.k t₀ := by
      by_contra hc
      push_neg at hc
      refine hjump ?_
      have hz : levyJump F.k s₀ = ∫⁻ _t in Ioi (0 : ℝ), (0 : ℝ≥0∞) := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
        have hkt : F.k t = 0 := le_antisymm (hc t ht) (F.k_nonneg t ht)
        simp [hkt]
      simpa using hz
    obtain ⟨t₀, ht₀, hpos⟩ := hex
    exact levyMass_eq_top_of_ne_zero F.k_antitone ht₀ hpos

/-- **`lem:standing-levy-reading`**, assembled: both clauses, as the node states them. -/
theorem standing_levy_reading :
    (Tendsto F.toRealExponent atTop atTop ↔
        0 < F.b₀ ∨ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (F.k t / t) = ⊤) ∧
      ((∃ s₀, 0 < s₀ ∧ F.exponent s₀ ≠ 0) → Tendsto F.toRealExponent atTop atTop) :=
  ⟨F.tendsto_toRealExponent_atTop_iff_levy, F.tendsto_toRealExponent_atTop_of_ne_zero⟩

end SelfDecomposableExponent

end Hemigroup
