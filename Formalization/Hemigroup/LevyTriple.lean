/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the MIT license as described in the file LICENSES/MIT.txt.
Authors: Daniel Fagerström
-/
import Hemigroup.LevyLimit

/-!
# `thm:increments-bernstein`, part three: reading the triple off the limit

`LevyLimit.lean` produced a finite measure `ρ` on `[0,1]` with

  `g_{x,y}(s) = ∫ k_s dρ`  for every `s > 0`,   `k_s(v) = (1 - (1-v)^s)/v`, `k_s(0) = s`.

That single identity already contains the whole Lévy triple; what is left is to read it off,
which is a matter of looking at the three pieces of `[0,1]` separately.

## The three pieces

* **`{0}`** — `k_s(0) = s`, so this atom contributes `s · ρ({0})` and *is* the drift. This is why
  the removable singularity had to be filled in with the value `s` rather than anything else.
* **`(0,1)`** — the change of variable `v = 1 - e^{-t}` run backwards. Undoing the weighting
  means a density `1/v`, and what comes back is `∫ (1 - e^{-st}) dν` with `ν` carried by
  `(0,∞)`: the Lévy measure.
* **`{1}`** — `k_s(1) = 1` for every `s > 0`, a term that does not vanish as `s ↓ 0`. It is the
  killing term, and `g_{x,y}(\zp) = 0` is exactly what forbids it.

## The killing term

That last point is the only genuinely analytic step here, and it is short: `k_s` is bounded by
`1` on `[0,1]` for `s ≤ 1`, and converges pointwise as `s ↓ 0` to the indicator of `{1}` — the
value `1` survives at `v = 1` and nowhere else. Dominated convergence against the *finite* `ρ`
then reads

  `0 = g_{x,y}(\zp) = ρ({1})`.

No tightness, no tail estimate: the compact carrier that the change of variable bought in
`LevyLimit.lean` pays for this too.
-/

namespace Hemigroup

open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

/-! ## The test function on `[0,1]`

Two elementary estimates and one limit, all of them statements about `w^s` for `w ∈ [0,1]`.
-/

theorem levyRatio_nonneg {s v : ℝ} (hs : 0 ≤ s) (hv : v ∈ Icc (0 : ℝ) 1) :
    0 ≤ levyRatio s v := by
  rcases eq_or_ne v 0 with rfl | hvne
  · simpa using hs
  · have hv0 : 0 < v := lt_of_le_of_ne hv.1 (Ne.symm hvne)
    rw [levyRatio_of_ne hvne]
    refine div_nonneg ?_ hv0.le
    have : (1 - v) ^ s ≤ 1 := Real.rpow_le_one (by linarith [hv.2]) (by linarith [hv.1]) hs
    linarith

theorem levyRatio_le_one {s v : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    levyRatio s v ≤ 1 := by
  rcases eq_or_ne v 0 with rfl | hvne
  · simpa using hs1
  · have hv0 : 0 < v := lt_of_le_of_ne hv.1 (Ne.symm hvne)
    rw [levyRatio_of_ne hvne, div_le_one hv0]
    -- `1 - (1-v)^s ≤ v` is `w ≤ w^s` for `w = 1 - v ∈ [0,1]` and `s ≤ 1`.
    rcases eq_or_lt_of_le hv.2 with rfl | hv1
    · rw [sub_self, Real.zero_rpow hs.ne']
      norm_num
    · have hw : (0 : ℝ) < 1 - v := by linarith
      have hw1 : (1 : ℝ) - v ≤ 1 := by linarith [hv.1]
      have := Real.rpow_le_rpow_of_exponent_ge hw hw1 hs1
      rw [Real.rpow_one] at this
      linarith

/-- **The pointwise limit as `s ↓ 0`**: the test function collapses to the indicator of `{1}`.

Every point of `[0,1)` is killed — the origin because `k_s(0) = s`, the interior because
`(1-v)^s → 1` — and `v = 1` survives because `k_s(1) = 1` for every `s > 0`. That surviving
value is the killing term, and the next result is what rules it out. -/
theorem tendsto_levyRatio_nhdsGT {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun s : ℝ => levyRatio s v) (𝓝[>] (0 : ℝ))
      (𝓝 (({(1 : ℝ)} : Set ℝ).indicator (fun _ => (1 : ℝ)) v)) := by
  rcases eq_or_lt_of_le hv.1 with rfl | hv0
  · rw [indicator_of_notMem (by norm_num)]
    simp only [levyRatio_zero]
    exact tendsto_id.mono_left nhdsWithin_le_nhds
  · rcases eq_or_lt_of_le hv.2 with rfl | hv1
    · rw [indicator_of_mem (mem_singleton (1 : ℝ))]
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with s hs
      rw [levyRatio_of_ne one_ne_zero, sub_self, Real.zero_rpow (ne_of_gt hs), sub_zero, div_one]
    · rw [indicator_of_notMem (by simp only [mem_singleton_iff]; linarith)]
      have hvne : v ≠ 0 := ne_of_gt hv0
      have hw : (0 : ℝ) < 1 - v := by linarith
      have heq : ∀ s : ℝ, levyRatio s v = (1 - Real.exp (Real.log (1 - v) * s)) / v := fun s => by
        rw [levyRatio_of_ne hvne, Real.rpow_def_of_pos hw]
      simp only [heq]
      have hcont : Continuous fun s : ℝ => (1 - Real.exp (Real.log (1 - v) * s)) / v := by
        fun_prop
      simpa using (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))

/-- **No killing term.** If the pairing with the test function vanishes as `s ↓ 0`, the limit
measure has no atom at the right endpoint.

Dominated convergence, with the constant `1` as the bound — legitimate because `ρ` is finite,
which is what the weighting in `LevyLimit.lean` was for. -/
theorem measure_singleton_one_eq_zero {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    (hcar : ρ ((Icc (0 : ℝ) 1)ᶜ) = 0)
    (h : Tendsto (fun s : ℝ => ∫ v, levyRatio s v ∂ρ) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    ρ {(1 : ℝ)} = 0 := by
  have hae : ∀ᵐ v ∂ρ, v ∈ Icc (0 : ℝ) 1 := ae_iff.mpr hcar
  -- The dominated limit of the pairings is the mass of the atom.
  have hdct : Tendsto (fun s : ℝ => ∫ v, levyRatio s v ∂ρ) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ v, ({(1 : ℝ)} : Set ℝ).indicator (fun _ => (1 : ℝ)) v ∂ρ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ ?_
      (integrable_const 1) ?_
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact (continuous_levyRatio hs).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT (α := ℝ) zero_lt_one] with s hs
      filter_upwards [hae] with v hv
      rw [Real.norm_eq_abs, abs_of_nonneg (levyRatio_nonneg hs.1.le hv)]
      exact levyRatio_le_one hs.1 hs.2.le hv
    · filter_upwards [hae] with v hv using tendsto_levyRatio_nhdsGT hv
  have huniq := tendsto_nhds_unique hdct h
  rw [integral_indicator_const _ (measurableSet_singleton _), smul_eq_mul, mul_one] at huniq
  exact (ENNReal.toReal_eq_zero_iff _).mp huniq |>.resolve_right (measure_ne_top _ _)

/-! ## The transport back

`v ↦ -\log(1-v)` inverts the change of variable on `(0,1)`, and the weighting is undone by a
density `1/v`. Nothing here is an approximation: it is one substitution, stated for `lintegral`
so that no integrability hypothesis is needed anywhere.
-/

/-- The inverse of `expTrans` on `(0,1)`. -/
noncomputable def logTrans (v : ℝ) : ℝ := -Real.log (1 - v)

lemma measurable_logTrans : Measurable logTrans :=
  (Real.measurable_log.comp (by fun_prop)).neg

lemma logTrans_pos {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) : 0 < logTrans v := by
  have h1 : (0 : ℝ) < 1 - v := by linarith [hv.2]
  have h2 : (1 : ℝ) - v < 1 := by linarith [hv.1]
  rw [logTrans, neg_pos]
  exact Real.log_neg h1 h2

/-- **The Lévy measure of a limit measure on `[0,1]`**: the interior part, unweighted and moved
back to the half line. -/
noncomputable def levyMeasure (ρ : Measure ℝ) : Measure ℝ :=
  ((ρ.restrict (Ioo 0 1)).withDensity fun v => ENNReal.ofReal v⁻¹).map logTrans

/-- The Lévy measure is carried by `(0,∞)`, as `(7.1)` requires. -/
theorem isCausal_levyMeasure (ρ : Measure ℝ) : IsCausal (levyMeasure ρ) := by
  rw [IsCausal, levyMeasure, Measure.map_apply measurable_logTrans measurableSet_Iio]
  -- Off `(0,1)` is the only place the preimage can live.
  have hsub : logTrans ⁻¹' Iio 0 ⊆ (Ioo (0 : ℝ) 1)ᶜ := by
    intro v hv
    simp only [mem_preimage, mem_Iio] at hv
    exact fun hmem => absurd hv (not_lt.mpr (logTrans_pos hmem).le)
  refine measure_mono_null hsub ((withDensity_absolutelyContinuous _ _) ?_)
  rw [Measure.restrict_apply measurableSet_Ioo.compl, compl_inter_self]
  exact measure_empty

/-- **The substitution.** Pairing `1 - e^{-st}` against the Lévy measure is pairing the test
function against `ρ` on the interior — which is the change of variable of `LevyLimit.lean` read
backwards. -/
theorem lintegral_levyMeasure (ρ : Measure ℝ) {s : ℝ} (hs : 0 ≤ s) :
    ∫⁻ t, ENNReal.ofReal (1 - Real.exp (-(s * t))) ∂(levyMeasure ρ)
      = ∫⁻ v in Ioo (0 : ℝ) 1, ENNReal.ofReal (levyRatio s v) ∂ρ := by
  have hf : Measurable fun t : ℝ => ENNReal.ofReal (1 - Real.exp (-(s * t))) := by fun_prop
  have hd : Measurable fun v : ℝ => ENNReal.ofReal v⁻¹ := by fun_prop
  have hfc : Measurable fun v : ℝ => ENNReal.ofReal (1 - Real.exp (-(s * logTrans v))) :=
    hf.comp measurable_logTrans
  rw [levyMeasure, lintegral_map hf measurable_logTrans,
    lintegral_withDensity_eq_lintegral_mul _ hd hfc]
  refine setLIntegral_congr_fun measurableSet_Ioo fun v hv => ?_
  have hv0 : (0 : ℝ) < v := hv.1
  have hw : (0 : ℝ) < 1 - v := by linarith [hv.2]
  -- `e^{-s·logTrans v} = (1-v)^s`, so the integrand is `v⁻¹ (1 - (1-v)^s)`.
  have hexp : Real.exp (-(s * logTrans v)) = (1 - v) ^ s := by
    rw [Real.rpow_def_of_pos hw, logTrans]
    ring_nf
  simp only [Pi.mul_apply, Function.comp_apply, hexp]
  rw [← ENNReal.ofReal_mul (by positivity), levyRatio_of_ne hv0.ne', div_eq_inv_mul]

/-! ## The splitting

`[0,1]` is `{0}` together with `(0,1)` together with `{1}`, and each piece is one term of the
triple.
-/

/-- **The drift is the atom at the origin**, and nothing else survives outside the interior. -/
theorem lintegral_levyRatio_split {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    (hcar : ρ ((Icc (0 : ℝ) 1)ᶜ) = 0) (hone : ρ {(1 : ℝ)} = 0) (s : ℝ) :
    ∫⁻ v, ENNReal.ofReal (levyRatio s v) ∂ρ
      = ENNReal.ofReal s * ρ {(0 : ℝ)} + ∫⁻ v in Ioo (0 : ℝ) 1, ENNReal.ofReal (levyRatio s v) ∂ρ
      := by
  have hsplit : Icc (0 : ℝ) 1 = ({(0 : ℝ)} ∪ Ioo (0 : ℝ) 1) ∪ {(1 : ℝ)} := by
    ext v
    simp only [mem_Icc, mem_union, mem_singleton_iff, mem_Ioo]
    constructor
    · rintro ⟨h0, h1⟩
      rcases eq_or_lt_of_le h0 with rfl | h0'
      · exact Or.inl (Or.inl rfl)
      · rcases eq_or_lt_of_le h1 with rfl | h1'
        · exact Or.inr rfl
        · exact Or.inl (Or.inr ⟨h0', h1'⟩)
    · rintro ((rfl | ⟨h0, h1⟩) | rfl) <;> constructor <;> linarith
  have hres : ρ.restrict (Icc (0 : ℝ) 1) = ρ :=
    Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hcar)
  calc ∫⁻ v, ENNReal.ofReal (levyRatio s v) ∂ρ
      = ∫⁻ v in Icc (0 : ℝ) 1, ENNReal.ofReal (levyRatio s v) ∂ρ := by rw [hres]
    _ = (∫⁻ v in ({(0 : ℝ)} ∪ Ioo (0 : ℝ) 1), ENNReal.ofReal (levyRatio s v) ∂ρ)
          + ∫⁻ v in {(1 : ℝ)}, ENNReal.ofReal (levyRatio s v) ∂ρ := by
        rw [hsplit]
        refine lintegral_union (measurableSet_singleton _) ?_
        rw [Set.disjoint_union_left]
        constructor
        · simp
        · rw [Set.disjoint_singleton_right]
          exact fun h => absurd h.2 (lt_irrefl 1)
    _ = ∫⁻ v in ({(0 : ℝ)} ∪ Ioo (0 : ℝ) 1), ENNReal.ofReal (levyRatio s v) ∂ρ := by
        rw [Measure.restrict_eq_zero.mpr hone, lintegral_zero_measure, add_zero]
    _ = (∫⁻ v in {(0 : ℝ)}, ENNReal.ofReal (levyRatio s v) ∂ρ)
          + ∫⁻ v in Ioo (0 : ℝ) 1, ENNReal.ofReal (levyRatio s v) ∂ρ :=
        lintegral_union measurableSet_Ioo
          (by rw [Set.disjoint_singleton_left]; exact fun h => absurd h.1 (lt_irrefl 0))
    _ = ENNReal.ofReal s * ρ {(0 : ℝ)}
          + ∫⁻ v in Ioo (0 : ℝ) 1, ENNReal.ofReal (levyRatio s v) ∂ρ := by
        congr 1
        have hpt : ∫⁻ v in ({(0 : ℝ)} : Set ℝ), ENNReal.ofReal (levyRatio s v) ∂ρ
            = ∫⁻ _ in ({(0 : ℝ)} : Set ℝ), ENNReal.ofReal s ∂ρ :=
          setLIntegral_congr_fun (measurableSet_singleton _)
            (fun v hv => by rw [mem_singleton_iff.mp hv, levyRatio_zero])
        rw [hpt, setLIntegral_const]

/-! ## The theorem -/

namespace CascadeCore

variable {Fam : CascadeCore} {x y : ℝ}

/-- **`thm:increments-bernstein`**, in the representation vocabulary: every increment of a
causal cascade family is a Lévy exponent.

The blueprint concludes `g_{x,y} ∈ BF₀`; the development has no `BF₀` and never defines complete
monotonicity, so the conclusion is stated in `LE` — the same class named by its representation.
Bridging the two is ledger A3, and is not needed here.

Stated with the exponent's `ℝ≥0∞` reading on the left, which is how `levyExponent` is valued, so
that no integrability hypothesis appears anywhere. Causality of `ν` is part of the conclusion. -/
theorem exponent_hasLevyRep (Fam : CascadeCore) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    ∃ b₀ : ℝ, ∃ ν : Measure ℝ, 0 ≤ b₀ ∧ IsCausal ν ∧
      ∀ s : ℝ, 0 ≤ s → ENNReal.ofReal (Fam.exponent x y s) = levyExponent b₀ ν s := by
  obtain ⟨ρ, hρfin, hρcar, hρ⟩ := exists_limit_measure Fam hx hxy
  haveI : IsFiniteMeasure ρ := hρfin
  -- `g_{x,y}(\zp) = 0` kills the atom at the right endpoint.
  have hgzero : Tendsto (fun s : ℝ => Fam.exponent x y s) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc := (continuousOn_exponent_right Fam x y) 0 left_mem_Ici
    rw [ContinuousWithinAt, exponent_zero] at hc
    exact hc.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have hone : ρ {(1 : ℝ)} = 0 := by
    refine measure_singleton_one_eq_zero hρcar (hgzero.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (hρ s hs).symm
  refine ⟨ρ.real {(0 : ℝ)}, levyMeasure ρ, measureReal_nonneg, isCausal_levyMeasure ρ, ?_⟩
  intro s hs
  rcases eq_or_lt_of_le hs with rfl | hspos
  · simp
  -- Everything below is the identity `g(s) = ∫ k_s dρ` split into its three pieces.
  have hint : Integrable (fun v => levyRatio s v) ρ :=
    integrable_of_carried isCompact_Icc hρcar (continuous_levyRatio hspos)
  have hnn : 0 ≤ᵐ[ρ] fun v => levyRatio s v := by
    filter_upwards [ae_iff.mpr hρcar] with v hv using levyRatio_nonneg hspos.le hv
  have hdrift : ENNReal.ofReal (ρ.real {(0 : ℝ)} * s) = ENNReal.ofReal s * ρ {(0 : ℝ)} := by
    rw [ENNReal.ofReal_mul measureReal_nonneg, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top _ _), mul_comm]
  rw [← hρ s hspos, ofReal_integral_eq_lintegral_ofReal hint hnn,
    lintegral_levyRatio_split hρcar hone s, levyExponent, hdrift,
    lintegral_levyMeasure ρ hspos.le]

/-! ## `cor:strict-monotonicity`

One step, and no bridge: the vanishing lemma is stated on `LE` already, which is the whole
reason the theorem above concludes in `LE` rather than in `BF₀`.
-/

/-- **The increments are strictly positive.** (ND) says the increment does not vanish
*identically*; the vanishing lemma upgrades that to vanishing *nowhere* on `(0,∞)`, because a
Lévy exponent with one zero in `(0,∞)` is zero everywhere. -/
theorem exponent_pos (Fam : CascadeCore) {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) {s : ℝ}
    (hs : 0 < s) : 0 < Fam.exponent x y s := by
  rcases lt_or_eq_of_le (exponent_nonneg Fam x y hs.le) with hlt | heq
  · exact hlt
  exfalso
  obtain ⟨b₀, ν, hb, hν, hrep⟩ := exponent_hasLevyRep Fam hx hxy.le
  -- One zero in `(0,∞)` propagates to the whole half line.
  have hall := levyExponent_eq_zero_of_eq_zero hb hν hs
    (by rw [← hrep s hs.le, ← heq, ENNReal.ofReal_zero])
  obtain ⟨s₁, hs₁, hne⟩ := exists_exponent_ne_zero (Fam := Fam) hx hxy
  refine hne (le_antisymm ?_ (exponent_nonneg Fam x y hs₁))
  have h := hrep s₁ hs₁
  rw [hall s₁ hs₁] at h
  exact ENNReal.ofReal_eq_zero.mp h

/-- **`cor:strict-monotonicity`.** Under (ND), `G(\cdot, s)` is strictly increasing on `[0,∞)`
for every `s > 0`, and the increment is the difference. -/
theorem strict_monotonicity (Fam : CascadeCore) :
    ∀ x y : ℝ, 0 ≤ x → x < y → ∀ s : ℝ, 0 < s →
      Fam.G y s - Fam.G x s = Fam.exponent x y s ∧ 0 < Fam.exponent x y s :=
  fun _ _ hx hxy _ hs =>
    ⟨(exponent_eq_G_sub hx hxy.le hs.le).symm, exponent_pos Fam hx hxy hs⟩

/-- The same, as a strict monotonicity statement about `G`. -/
theorem G_strictMonoOn (Fam : CascadeCore) {s : ℝ} (hs : 0 < s) :
    StrictMonoOn (fun x => Fam.G x s) (Ici 0) := by
  intro a ha b _ hab
  have hsub := exponent_eq_G_sub (Fam := Fam) ha hab.le hs.le
  have hpos := exponent_pos Fam ha hab hs
  simp only
  linarith

end CascadeCore

end Hemigroup
