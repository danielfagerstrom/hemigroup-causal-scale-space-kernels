/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Hemigroup.NullArray
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Measure.Prokhorov

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
open scoped Topology NNReal ENNReal

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

/-- `k_1 \equiv 1`. This is why the total mass of the weighted measure is the `s = 1`
approximant, with nothing to compute. -/
@[simp] lemma levyRatio_one (v : ℝ) : levyRatio 1 v = 1 := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · rw [levyRatio_of_ne hv, Real.rpow_one]
    field_simp
    ring

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

/-- For a measure carried by `[0,1]`, clamping the test function changes no integral. -/
lemma integral_levyRatioBdd_of_carried {ν : Measure ℝ} (hν : ν ((Icc (0 : ℝ) 1)ᶜ) = 0)
    {s : ℝ} (hs : 0 < s) :
    ∫ v, levyRatioBdd hs v ∂ν = ∫ v, levyRatio s v ∂ν := by
  refine integral_congr_ae ?_
  filter_upwards [ae_iff.mpr hν] with v hv
  exact levyRatioBdd_of_mem hs hv

/-! ## A cluster point is pinned by what already converges

The extraction below produces a *cluster* point rather than a limit, because the space of finite
measures on `ℝ` carries no metrizability instance in Mathlib and so no subsequence can be pulled
out. Nothing is lost: every observable this development needs is a continuous real function of
the measure that *already converges along the full sequence*, and a convergent sequence has only
one cluster value.
-/

/-- If `Φ ∘ P` converges and `a` is a cluster point of `P`, then `Φ a` is the limit. -/
theorem eq_of_mapClusterPt {α : Type*} [TopologicalSpace α] {P : ℕ → α} {a : α} {Φ : α → ℝ}
    {L : ℝ} (hcl : MapClusterPt a atTop P) (hΦ : Continuous Φ)
    (hlim : Tendsto (fun n => Φ (P n)) atTop (𝓝 L)) : Φ a = L :=
  eq_of_nhds_neBot ((hcl.continuousAt_comp hΦ.continuousAt).clusterPt.mono hlim)

/-! ## The weighted approximants

`ρ_n` is `Π_n` transformed by `expTrans` and weighted by `v`. The weighting is what tames the
divergence: `Π_n(\RR) = n`, while `ρ_n(\RR) = ∫ (1 - e^{-t})\,d\Pi_n` converges. And the
transform is what puts everything on a fixed compact.
-/

namespace CascadeCore

variable {Fam : CascadeCore} {x y : ℝ}

/-- `Π_n` is carried by `[0,∞)`: a finite sum of causal measures. -/
lemma isCausal_partitionMeasure (Fam : CascadeCore) (x y : ℝ) (n : ℕ) :
    IsCausal (Fam.partitionMeasure x y n) := by
  rw [IsCausal, partitionMeasure, Measure.coe_finsetSum, Finset.sum_apply]
  exact Finset.sum_eq_zero fun i _ => isCausal_repr Fam _ _

/-- **`ρ_n`**: the `n`-th approximant, moved to `[0,1]` and weighted by `v`. -/
noncomputable def weightedPartition (Fam : CascadeCore) (x y : ℝ) (n : ℕ) : Measure ℝ :=
  ((Fam.partitionMeasure x y n).map expTrans).withDensity fun v => ENNReal.ofReal v

/-- Almost every point of the transformed measure lies in `[0,1]` — the change of variable
maps the half line there, and `Π_n` is carried by the half line. -/
lemma ae_mem_Icc_map_expTrans (Fam : CascadeCore) (x y : ℝ) (n : ℕ) :
    ∀ᵐ v ∂((Fam.partitionMeasure x y n).map expTrans), v ∈ Icc (0 : ℝ) 1 := by
  have h : ∀ᵐ t ∂(Fam.partitionMeasure x y n), expTrans t ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [(isCausal_partitionMeasure Fam x y n).ae_nonneg] with t ht
    exact ⟨expTrans_nonneg ht, expTrans_le_one t⟩
  exact (ae_map_iff continuous_expTrans.measurable.aemeasurable measurableSet_Icc).mpr h

instance instIsFiniteMeasureMapExpTrans (Fam : CascadeCore) (x y : ℝ) (n : ℕ) :
    IsFiniteMeasure ((Fam.partitionMeasure x y n).map expTrans) := by
  constructor
  rw [Measure.map_apply continuous_expTrans.measurable MeasurableSet.univ]
  simp

instance instIsFiniteMeasureWeightedPartition (Fam : CascadeCore) (x y : ℝ) (n : ℕ) :
    IsFiniteMeasure (Fam.weightedPartition x y n) := by
  constructor
  rw [weightedPartition, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  calc ∫⁻ v, ENNReal.ofReal v ∂((Fam.partitionMeasure x y n).map expTrans)
      ≤ ∫⁻ _, 1 ∂((Fam.partitionMeasure x y n).map expTrans) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_mem_Icc_map_expTrans Fam x y n] with v hv
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal hv.2
    _ < ⊤ := by
        rw [lintegral_one]
        exact measure_lt_top _ _

/-- **The change of variable, at the level of integrals.** Pairing the test function against
`ρ_n` is pairing `1 - e^{-st}` against `Π_n` — which is what `NullArray.lean` computes. -/
theorem integral_weightedPartition (Fam : CascadeCore) (x y : ℝ) (n : ℕ) {s : ℝ} (hs : 0 < s) :
    ∫ v, levyRatio s v ∂(Fam.weightedPartition x y n)
      = ∫ t, (1 - Real.exp (-(s * t))) ∂(Fam.partitionMeasure x y n) := by
  rw [weightedPartition,
    integral_withDensity_eq_integral_toReal_smul₀
      (Measurable.aemeasurable (by fun_prop))
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  -- On the transformed measure the density is just `v`.
  have hstep : ∫ v, (ENNReal.ofReal v).toReal • levyRatio s v
        ∂((Fam.partitionMeasure x y n).map expTrans)
      = ∫ v, v * levyRatio s v ∂((Fam.partitionMeasure x y n).map expTrans) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_mem_Icc_map_expTrans Fam x y n] with v hv
    rw [smul_eq_mul, ENNReal.toReal_ofReal hv.1]
  have hcont : Continuous fun v : ℝ => v * levyRatio s v :=
    continuous_id.mul (continuous_levyRatio hs)
  rw [hstep, integral_map continuous_expTrans.measurable.aemeasurable
    hcont.aestronglyMeasurable]
  refine integral_congr_ae ?_
  filter_upwards [(isCausal_partitionMeasure Fam x y n).ae_nonneg] with t ht
  rw [mul_comm]
  exact levyRatio_expTrans_mul ht

/-- **The mass of `ρ_n` is the `s = 1` approximant** — the very quantity `NullArray.lean` shows
converges, hence the uniform bound the extraction needs.

The identity is free rather than computed: `k_1 \equiv 1`, so pairing the test function against
`ρ_n` at `s = 1` *is* taking its total mass. -/
theorem measureReal_weightedPartition_univ (Fam : CascadeCore) (x y : ℝ) (n : ℕ) :
    (Fam.weightedPartition x y n).real univ
      = ∫ t, (1 - Real.exp (-((1 : ℝ) * t))) ∂(Fam.partitionMeasure x y n) := by
  have h := integral_weightedPartition Fam x y n one_pos
  simp only [levyRatio_one] at h
  rw [← h, integral_const, smul_eq_mul, mul_one]

/-! ### The two inputs to the compactness lemma

Prokhorov, in the form Mathlib states for finite measures, asks for exactly two things: a
uniform bound on the masses, and a uniform bound on the mass outside a compact. Here the second
is trivial — every `ρ_n` is carried by `[0,1]` — and the first is the convergence already
proved.
-/

/-- **The masses are uniformly bounded.** No estimate is made: the masses are the `s = 1`
approximants, which converge, and a convergent real sequence is bounded. -/
theorem exists_mass_bound (Fam : CascadeCore) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    ∃ C : ℝ, ∀ n : ℕ, (Fam.weightedPartition x y n).real univ ≤ C := by
  have hconv := tendsto_integral_partitionMeasure (Fam := Fam) hx hxy zero_le_one
  obtain ⟨C, hC⟩ := hconv.bddAbove_range
  refine ⟨C, fun n => ?_⟩
  rw [measureReal_weightedPartition_univ]
  exact hC ⟨n, rfl⟩

/-- **Every `ρ_n` is carried by `[0,1]`** — the change of variable put it there. -/
theorem weightedPartition_compl_Icc (Fam : CascadeCore) (x y : ℝ) (n : ℕ) :
    Fam.weightedPartition x y n ((Icc (0 : ℝ) 1)ᶜ) = 0 := by
  have hnull : ((Fam.partitionMeasure x y n).map expTrans) ((Icc (0 : ℝ) 1)ᶜ) = 0 :=
    ae_iff.mp (ae_mem_Icc_map_expTrans Fam x y n)
  rw [weightedPartition, withDensity_apply _ measurableSet_Icc.compl,
    Measure.restrict_eq_zero.mpr hnull, lintegral_zero_measure]

/-! ### The limiting measure

Prokhorov delivers a cluster point of `(ρ_n)` in `FiniteMeasure ℝ`, and pairing it against the
test function recovers the exponent — for *every* `s > 0` at once, since the cluster point is one
measure and each `s` supplies its own already-convergent observable.
-/

/-- **The weak limit of the weighted approximants.** A single finite measure on `[0,1]` whose
pairing with `k_s` is `g_{x,y}(s)`, for every `s > 0`.

This is the analytic heart of `thm:increments-bernstein`: everything after it is the change of
variable read backwards, splitting the limit at the two endpoints of `[0,1]`. -/
theorem exists_limit_measure (Fam : CascadeCore) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    ∃ ρ : Measure ℝ, IsFiniteMeasure ρ ∧ ρ ((Icc (0 : ℝ) 1)ᶜ) = 0 ∧
      ∀ s : ℝ, 0 < s → ∫ v, levyRatio s v ∂ρ = Fam.exponent x y s := by
  obtain ⟨C, hC⟩ := exists_mass_bound Fam hx hxy
  have hC0 : 0 ≤ C := le_trans measureReal_nonneg (hC 0)
  set P : ℕ → FiniteMeasure ℝ := fun n => ⟨Fam.weightedPartition x y n, inferInstance⟩ with hPdef
  -- The two Prokhorov inputs, in the shape the lemma states them.
  have hmass : ∀ n, (P n).mass ≤ C.toNNReal := by
    intro n
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal C hC0]
    have hmass' : ((P n).mass : ℝ≥0∞) = (Fam.weightedPartition x y n) univ :=
      FiniteMeasure.ennreal_mass
    have : ((P n).mass : ℝ) = (Fam.weightedPartition x y n).real univ := by
      rw [measureReal_def, ← hmass', ENNReal.coe_toReal]
    rw [this]
    exact hC n
  have hcar : ∀ n, (P n) ((Icc (0 : ℝ) 1)ᶜ) ≤ (0 : ℝ≥0) :=
    fun n => le_of_eq ((FiniteMeasure.null_iff_toMeasure_null _ _).mpr
      (weightedPartition_compl_Icc Fam x y n))
  -- Prokhorov, with a *constant* compact: the monotonicity side condition is free.
  have hcpt := isCompact_setOf_finiteMeasure_mass_le_compl_isCompact_le (E := ℝ)
    (u := fun _ => 0) (K := fun _ : ℕ => Icc (0 : ℝ) 1) C.toNNReal
    tendsto_const_nhds (fun _ => isCompact_Icc) (Or.inr monotone_const)
  obtain ⟨a, haS, hcl⟩ := hcpt.exists_mapClusterPt (f := atTop) (u := P)
    (Filter.tendsto_principal.mpr (Filter.Eventually.of_forall
      fun n => ⟨hmass n, fun _ => hcar n⟩))
  have hacar : (a : Measure ℝ) ((Icc (0 : ℝ) 1)ᶜ) = 0 :=
    (FiniteMeasure.null_iff_toMeasure_null _ _).mp (nonpos_iff_eq_zero.mp (haS.2 0))
  refine ⟨(a : Measure ℝ), inferInstance, hacar, fun s hs => ?_⟩
  -- The observable: pairing against the bounded test function, continuous in the measure.
  have hobs : Tendsto (fun n => ∫ v, levyRatioBdd hs v ∂(P n : Measure ℝ)) atTop
      (𝓝 (Fam.exponent x y s)) := by
    have hPcoe : ∀ n, ((P n : FiniteMeasure ℝ) : Measure ℝ) = Fam.weightedPartition x y n :=
      fun _ => rfl
    have hEq : ∀ n, ∫ v, levyRatioBdd hs v ∂(P n : Measure ℝ)
        = ∫ t, (1 - Real.exp (-(s * t))) ∂(Fam.partitionMeasure x y n) := fun n => by
      rw [hPcoe n, integral_levyRatioBdd_of_carried (weightedPartition_compl_Icc Fam x y n) hs]
      exact integral_weightedPartition Fam x y n hs
    simpa only [hEq] using tendsto_integral_partitionMeasure (Fam := Fam) hx hxy hs.le
  have := eq_of_mapClusterPt hcl
    (FiniteMeasure.continuous_integral_boundedContinuousFunction (levyRatioBdd hs)) hobs
  rwa [integral_levyRatioBdd_of_carried hacar hs] at this

end CascadeCore

end Hemigroup
