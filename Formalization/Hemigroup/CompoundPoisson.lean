/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Hemigroup.Levy
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.TightNormed
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The compound-Poisson construction

The proof of what was ledger A17: a drift `b₀ ≥ 0` and a causal Lévy measure `ν` with finite
exponent are the triple of a causal probability measure `μ`,
`laplace μ s = exp (-(b₀ s + ∫ (1 - e^{-st}) ν(dt)))` for `s ≥ 0`. `Interfaces.lean` restates it
under the axiom's old name, so no downstream statement changed.

The route is the one `Interfaces.lean` had sketched while A17 was an axiom.

1. **Finite `ν`.** The compound-Poisson measure `cp ν = e^{-‖ν‖} Σ ν^{*n}/n!` has transform
   `e^{-‖ν‖} Σ (ν̂ s)ⁿ/n! = exp (-(‖ν‖ - ν̂ s)) = exp (-∫ (1 - e^{-st}) ν(dt))`, because convolution
   multiplies transforms (`laplaceL_conv`). Its mass is its transform at `0`, which is `1`.
2. **Truncation.** `trunc ν n` is `ν` restricted to `(1/(n+1), ∞)`. It is finite because the
   exponent at `s = 1` bounds `(1 - e^{-ε}) ν(ε,∞)`, and its jump exponent increases to `ν`'s by
   monotone convergence (the integrand vanishes at `t = 0`, so the atom there is irrelevant).
3. **Tightness.** For a causal `μ`, `(1 - e^{-sr}) μ(r,∞) ≤ ∫ (1 - e^{-st}) μ(dt) = 1 - μ̂ s`, and
   along the sequence `1 - μ̂ₙ s ≤ Ψₙ(s) ≤ Ψ(s)`, which is small for small `s` by dominated
   convergence. Choosing `s` first and then `r` gives a uniform tail bound.
4. **Prokhorov.** Mathlib's `isCompact_closure_of_isTightMeasureSet` gives a cluster point `Q`
   of the sequence in `ProbabilityMeasure ℝ`. No subsequence is extracted: integration against a
   bounded continuous function is continuous, so `∫ g dQ` is a cluster point of a convergent real
   sequence, hence its limit. Tested against `t ↦ e^{-s max(t,0)}` this identifies the transform;
   tested against `t ↦ min(1, max(0,-t))` it shows `Q` is causal.
5. **Drift.** Translate `Q` by `b₀`.

Nothing here is a blueprint node: A17 was a Lean-side ledger entry with no node, and its
retirement is recorded there (`blueprint/AXIOMS.md`).
-/

namespace Hemigroup

namespace CompoundPoisson

open MeasureTheory Set Filter
open scoped ENNReal Topology BoundedContinuousFunction

/-- The jump part of the Lévy exponent: `s ↦ ∫ (1 - e^{-st}) ν(dt)`, valued in `ℝ≥0∞`. -/
noncomputable def jumpExp (ν : Measure ℝ) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ t, ENNReal.ofReal (1 - Real.exp (-(s * t))) ∂ν

lemma measurable_jumpIntegrand (s : ℝ) :
    Measurable fun t : ℝ => ENNReal.ofReal (1 - Real.exp (-(s * t))) :=
  (measurable_const.sub (Real.measurable_exp.comp (by fun_prop))).ennreal_ofReal

lemma levyExponent_eq (b₀ : ℝ) (ν : Measure ℝ) (s : ℝ) :
    levyExponent b₀ ν s = ENNReal.ofReal (b₀ * s) + jumpExp ν s := rfl

/-- On a finite causal measure the jump integral is `mass - transform`. -/
lemma jumpExp_eq_ofReal {μ : Measure ℝ} [IsFiniteMeasure μ] (h : IsCausal μ) {s : ℝ}
    (hs : 0 ≤ s) : jumpExp μ s = ENNReal.ofReal (μ.real univ - laplace μ s) := by
  have hnn : 0 ≤ᵐ[μ] fun t => 1 - Real.exp (-(s * t)) := by
    filter_upwards [h.ae_nonneg] with t ht
    have : Real.exp (-(s * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    simp only [Pi.zero_apply]
    linarith
  have hint : Integrable (fun t => 1 - Real.exp (-(s * t))) μ :=
    (integrable_const 1).sub (integrable_exp_of_causal h hs)
  rw [jumpExp, ← ofReal_integral_eq_lintegral_ofReal hint hnn,
    integral_sub (integrable_const 1) (integrable_exp_of_causal h hs), integral_const,
    smul_eq_mul, mul_one, laplace]

lemma jumpExp_toReal {μ : Measure ℝ} [IsFiniteMeasure μ] (h : IsCausal μ) {s : ℝ} (hs : 0 ≤ s) :
    (jumpExp μ s).toReal = μ.real univ - laplace μ s := by
  rw [jumpExp_eq_ofReal h hs, ENNReal.toReal_ofReal]
  rw [laplace_eq_toReal_laplaceL, measureReal_def]
  exact sub_nonneg.mpr (ENNReal.toReal_mono (measure_ne_top μ univ) (laplaceL_le_mass h hs))

/-- Markov's inequality in the form tightness needs. -/
lemma mul_measure_Ioi_le_jumpExp (μ : Measure ℝ) {s : ℝ} (hs : 0 ≤ s) (r : ℝ) :
    ENNReal.ofReal (1 - Real.exp (-(s * r))) * μ (Ioi r) ≤ jumpExp μ s := by
  rw [← setLIntegral_const]
  refine (setLIntegral_mono (measurable_jumpIntegrand s) fun t ht => ?_).trans
    (setLIntegral_le_lintegral _ _)
  refine ENNReal.ofReal_le_ofReal ?_
  have : Real.exp (-(s * t)) ≤ Real.exp (-(s * r)) :=
    Real.exp_le_exp.mpr (by nlinarith [mem_Ioi.mp ht])
  linarith

/-! ## Convolution powers and the compound-Poisson measure -/

/-- The `n`-fold convolution power, `ν^{*0} = δ₀`. -/
noncomputable def convPow (ν : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | n + 1 => convPow ν n ∗ ν

instance isFiniteMeasure_convPow (ν : Measure ℝ) [IsFiniteMeasure ν] (n : ℕ) :
    IsFiniteMeasure (convPow ν n) := by
  induction n with
  | zero => simp only [convPow]; infer_instance
  | succ n ih => simp only [convPow]; infer_instance

lemma isCausal_convPow {ν : Measure ℝ} [IsFiniteMeasure ν] (hν : IsCausal ν) (n : ℕ) :
    IsCausal (convPow ν n) := by
  induction n with
  | zero => exact isCausal_dirac le_rfl
  | succ n ih => exact ih.conv hν

lemma laplaceL_convPow (ν : Measure ℝ) [IsFiniteMeasure ν] (s : ℝ) (n : ℕ) :
    laplaceL (convPow ν n) s = laplaceL ν s ^ n := by
  induction n with
  | zero => simp [convPow, laplaceL]
  | succ n ih => rw [convPow, laplaceL_conv, ih, pow_succ]

/-- The compound-Poisson measure `e^{-‖ν‖} Σ ν^{*n}/n!`. -/
noncomputable def cp (ν : Measure ℝ) : Measure ℝ :=
  Measure.sum fun n : ℕ =>
    ENNReal.ofReal (Real.exp (-(ν univ).toReal) / n.factorial) • convPow ν n

lemma isCausal_cp {ν : Measure ℝ} [IsFiniteMeasure ν] (hν : IsCausal ν) : IsCausal (cp ν) := by
  rw [IsCausal, cp, Measure.sum_apply _ measurableSet_Iio]
  refine ENNReal.tsum_eq_zero.mpr fun i => ?_
  rw [Measure.smul_apply, show convPow ν i (Iio 0) = 0 from isCausal_convPow hν i, smul_zero]

/-- `Σ a xⁿ/n! = a eˣ` in `ℝ≥0∞`. -/
lemma tsum_ofReal_exp {a x : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) :
    ∑' n : ℕ, ENNReal.ofReal (a / n.factorial) * ENNReal.ofReal x ^ n
      = ENNReal.ofReal (a * Real.exp x) := by
  have hterm : ∀ n : ℕ, ENNReal.ofReal (a / n.factorial) * ENNReal.ofReal x ^ n
      = ENNReal.ofReal (a * (x ^ n / n.factorial)) := by
    intro n
    rw [← ENNReal.ofReal_pow hx, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
    ((Real.summable_pow_div_factorial x).mul_left a), tsum_mul_left]
  congr 2
  rw [Real.exp_eq_exp_ℝ]
  exact (NormedSpace.expSeries_div_hasSum_exp x).tsum_eq

lemma laplaceL_cp {ν : Measure ℝ} [IsFiniteMeasure ν] (hν : IsCausal ν) {s : ℝ} (hs : 0 ≤ s) :
    laplaceL (cp ν) s = ENNReal.ofReal (Real.exp (-(jumpExp ν s).toReal)) := by
  have hL : laplaceL ν s = ENNReal.ofReal (laplace ν s) := by
    rw [laplace_eq_toReal_laplaceL, ENNReal.ofReal_toReal (laplaceL_ne_top_of_causal hν hs)]
  have hlap : 0 ≤ laplace ν s := by
    rw [laplace_eq_toReal_laplaceL]; exact ENNReal.toReal_nonneg
  rw [laplaceL, cp, lintegral_sum_measure]
  simp_rw [lintegral_smul_measure, smul_eq_mul]
  have hfold : ∀ n, ∫⁻ t, ENNReal.ofReal (Real.exp (-(s * t))) ∂convPow ν n
      = laplaceL (convPow ν n) s := fun _ => rfl
  simp_rw [hfold, laplaceL_convPow, hL]
  rw [tsum_ofReal_exp (Real.exp_pos _).le hlap, jumpExp_toReal hν hs, ← Real.exp_add]
  congr 2
  simp [Measure.real]
  ring

lemma isProbabilityMeasure_cp {ν : Measure ℝ} [IsFiniteMeasure ν] (hν : IsCausal ν) :
    IsProbabilityMeasure (cp ν) := by
  constructor
  rw [← laplaceL_zero, laplaceL_cp hν le_rfl]
  simp [jumpExp]

lemma laplace_cp {ν : Measure ℝ} [IsFiniteMeasure ν] (hν : IsCausal ν) {s : ℝ} (hs : 0 ≤ s) :
    laplace (cp ν) s = Real.exp (-(jumpExp ν s).toReal) := by
  rw [laplace_eq_toReal_laplaceL, laplaceL_cp hν hs, ENNReal.toReal_ofReal (Real.exp_pos _).le]

/-! ## Truncation -/

/-- `ν` truncated to `(1/(n+1), ∞)`. -/
noncomputable def trunc (ν : Measure ℝ) (n : ℕ) : Measure ℝ :=
  ν.restrict (Ioi (1 / ((n : ℝ) + 1)))

lemma isCausal_trunc {ν : Measure ℝ} (n : ℕ) : IsCausal (trunc ν n) := by
  rw [IsCausal, trunc, Measure.restrict_apply measurableSet_Iio]
  refine measure_mono_null (fun t ht => ?_) measure_empty
  exfalso
  simp only [mem_inter_iff, mem_Iio, mem_Ioi] at ht
  have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  linarith [ht.1, ht.2]

lemma measure_Ioi_lt_top {ν : Measure ℝ} (h1 : jumpExp ν 1 ≠ ⊤) {ε : ℝ} (hε : 0 < ε) :
    ν (Ioi ε) < ⊤ := by
  have hc : ENNReal.ofReal (1 - Real.exp (-(1 * ε))) ≠ 0 := by
    refine (ENNReal.ofReal_pos.mpr ?_).ne'
    have : Real.exp (-(1 * ε)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  by_contra htop
  rw [not_lt, top_le_iff] at htop
  have := mul_measure_Ioi_le_jumpExp ν zero_le_one ε
  rw [htop, ENNReal.mul_top hc, top_le_iff] at this
  exact h1 this

lemma isFiniteMeasure_trunc {ν : Measure ℝ} (h1 : jumpExp ν 1 ≠ ⊤) (n : ℕ) :
    IsFiniteMeasure (trunc ν n) :=
  ⟨by rw [trunc, Measure.restrict_apply_univ]; exact measure_Ioi_lt_top h1 (by positivity)⟩

lemma jumpExp_trunc_le (ν : Measure ℝ) (n : ℕ) (s : ℝ) : jumpExp (trunc ν n) s ≤ jumpExp ν s :=
  lintegral_mono' Measure.restrict_le_self le_rfl

lemma tendsto_jumpExp_trunc {ν : Measure ℝ} (hν : IsCausal ν) (s : ℝ) :
    Tendsto (fun n => jumpExp (trunc ν n) s) atTop (𝓝 (jumpExp ν s)) := by
  set ρ := ν.withDensity (fun t => ENNReal.ofReal (1 - Real.exp (-(s * t))))
  have hmono : Monotone fun n : ℕ => Ioi (1 / ((n : ℝ) + 1)) := by
    intro m n hmn
    apply Ioi_subset_Ioi
    gcongr
  have hU : ⋃ n : ℕ, Ioi (1 / ((n : ℝ) + 1)) = Ioi 0 := by
    ext t
    simp only [mem_iUnion, mem_Ioi]
    constructor
    · rintro ⟨n, hn⟩
      exact lt_trans (by positivity) hn
    · intro ht
      exact exists_nat_one_div_lt ht
  have h := tendsto_measure_iUnion_atTop (μ := ρ) hmono
  rw [hU] at h
  have heq : ∀ n, jumpExp (trunc ν n) s = ρ (Ioi (1 / ((n : ℝ) + 1))) := fun n => by
    rw [withDensity_apply _ measurableSet_Ioi]; rfl
  have hlim : ρ (Ioi 0) = jumpExp ν s := by
    rw [withDensity_apply _ measurableSet_Ioi, jumpExp, ← lintegral_indicator measurableSet_Ioi]
    refine lintegral_congr_ae ?_
    filter_upwards [hν.ae_nonneg] with t ht
    rcases ht.eq_or_lt with h0 | h0
    · subst h0
      simp
    · simp [indicator_of_mem (mem_Ioi.mpr h0)]
  simp_rw [heq]
  rw [← hlim]
  exact h

/-- The jump exponent is continuous at the origin. -/
lemma tendsto_jumpExp_zero {ν : Measure ℝ} (hν : IsCausal ν) (h1 : jumpExp ν 1 ≠ ⊤) :
    Tendsto (jumpExp ν) (𝓝[>] 0) (𝓝 0) := by
  have := tendsto_lintegral_filter_of_dominated_convergence (μ := ν)
    (F := fun s t : ℝ => ENNReal.ofReal (1 - Real.exp (-(s * t)))) (l := 𝓝[>] (0 : ℝ))
    (f := fun _ => 0)
    (fun t => ENNReal.ofReal (1 - Real.exp (-(1 * t))))
    (Eventually.of_forall fun s => measurable_jumpIntegrand s)
    (by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with s hs
      filter_upwards [hν.ae_nonneg] with t ht
      refine ENNReal.ofReal_le_ofReal ?_
      have : Real.exp (-(1 * t)) ≤ Real.exp (-(s * t)) :=
        Real.exp_le_exp.mpr (by nlinarith [hs.1, hs.2])
      linarith)
    h1
    (Eventually.of_forall fun t => by
      have : Tendsto (fun s : ℝ => ENNReal.ofReal (1 - Real.exp (-(s * t)))) (𝓝 0)
          (𝓝 (ENNReal.ofReal (1 - Real.exp (-(0 * t))))) :=
        (ENNReal.continuous_ofReal.comp
          (by fun_prop : Continuous fun s : ℝ => 1 - Real.exp (-(s * t)))).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds)
  rw [lintegral_zero] at this
  exact this

/-! ## The limit -/

/-- A bounded continuous function agreeing with `t ↦ e^{-st}` on the half-line. -/
noncomputable def expBCF (s : ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun t => Real.exp (-(max s 0 * max t 0)))
    (by fun_prop) 1 fun t => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr
        (neg_nonpos.mpr (mul_nonneg (le_max_right _ _) (le_max_right _ _)))

lemma integral_expBCF {μ : Measure ℝ} (h : IsCausal μ) {s : ℝ} (hs : 0 ≤ s) :
    ∫ t, expBCF s t ∂μ = laplace μ s := by
  rw [laplace]
  refine integral_congr_ae ?_
  filter_upwards [h.ae_nonneg] with t ht
  change Real.exp (-(max s 0 * max t 0)) = _
  rw [max_eq_left hs, max_eq_left ht]

/-- A bounded continuous function positive exactly on the negative half-line. -/
noncomputable def negBCF : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun t => min 1 (max 0 (-t)))
    (by fun_prop) 1 fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one (le_max_left _ _))]
      exact min_le_left _ _

lemma integral_negBCF {μ : Measure ℝ} (h : IsCausal μ) : ∫ t, negBCF t ∂μ = 0 := by
  refine integral_eq_zero_of_ae ?_
  filter_upwards [h.ae_nonneg] with t ht
  change min 1 (max 0 (-t)) = 0
  rw [max_eq_left (by linarith), min_eq_right zero_le_one]

/-- **The pure-jump case.** A causal Lévy measure with finite exponent is the Lévy measure of a
causal probability measure: the compound-Poisson laws of its truncations are tight, and a cluster
point of them (Prokhorov) has the limiting transform. -/
theorem exists_jump {ν : Measure ℝ} (hν : IsCausal ν) (hfin : ∀ s, 0 ≤ s → jumpExp ν s ≠ ⊤) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ IsCausal μ ∧
      ∀ s, 0 ≤ s → laplace μ s = Real.exp (-(jumpExp ν s).toReal) := by
  have h1 := hfin 1 zero_le_one
  haveI : ∀ n, IsFiniteMeasure (trunc ν n) := isFiniteMeasure_trunc h1
  haveI : ∀ n, IsProbabilityMeasure (cp (trunc ν n)) :=
    fun n => isProbabilityMeasure_cp (isCausal_trunc n)
  let P : ℕ → ProbabilityMeasure ℝ := fun n => ⟨cp (trunc ν n), inferInstance⟩
  have hPval : ∀ n, (P n : Measure ℝ) = cp (trunc ν n) := fun n => rfl
  have hcp : ∀ n, IsCausal (cp (trunc ν n)) := fun n => isCausal_cp (isCausal_trunc n)
  -- The transforms along the sequence.
  have hlapn : ∀ s, 0 ≤ s → Tendsto (fun n => ∫ t, expBCF s t ∂(P n : Measure ℝ)) atTop
      (𝓝 (Real.exp (-(jumpExp ν s).toReal))) := by
    intro s hs
    simp_rw [hPval, integral_expBCF (hcp _) hs, laplace_cp (isCausal_trunc _) hs]
    exact ((Real.continuous_exp.comp continuous_neg).tendsto _).comp
      ((ENNReal.tendsto_toReal (hfin s hs)).comp (tendsto_jumpExp_trunc hν s))
  -- Tightness, from the transforms near the origin.
  have htight : IsTightMeasureSet {x | ∃ μ ∈ range P, (μ : Measure ℝ) = x} := by
    apply isTightMeasureSet_of_tendsto_measure_norm_gt
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    have hhalf0 : ENNReal.ofReal (1 / 2) ≠ 0 := (ENNReal.ofReal_pos.mpr (by norm_num)).ne'
    have hε2 : 0 < ENNReal.ofReal (1 / 2) * ε := ENNReal.mul_pos hhalf0 hε.ne'
    obtain ⟨s, hsJ, hs0⟩ :=
      (((tendsto_order.1 (tendsto_jumpExp_zero hν h1)).2 _ hε2).and self_mem_nhdsWithin).exists
    have hs0 : 0 < s := hs0
    filter_upwards [eventually_ge_atTop (Real.log 2 / s), eventually_ge_atTop 0] with r hr hr0
    refine iSup₂_le fun μ hμ => ?_
    obtain ⟨_, ⟨n, rfl⟩, rfl⟩ := hμ
    have hsub : {x : ℝ | r < ‖x‖} ⊆ Ioi r ∪ Iio 0 := by
      intro x hx
      simp only [mem_setOf_eq, Real.norm_eq_abs] at hx
      rcases le_or_gt 0 x with h | h
      · left
        rw [abs_of_nonneg h] at hx
        exact hx
      · right
        exact h
    have hhalf : (1 / 2 : ℝ) ≤ 1 - Real.exp (-(s * r)) := by
      have hsr : Real.log 2 ≤ s * r := by
        rw [div_le_iff₀ hs0] at hr
        linarith
      have : Real.exp (-(s * r)) ≤ 1 / 2 := by
        calc Real.exp (-(s * r)) ≤ Real.exp (-(Real.log 2)) := Real.exp_le_exp.mpr (by linarith)
          _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
      linarith
    have hJ : jumpExp (cp (trunc ν n)) s ≤ jumpExp ν s := by
      have hn_le := jumpExp_trunc_le ν n s
      have hn_ne : jumpExp (trunc ν n) s ≠ ⊤ := ne_top_of_le_ne_top (hfin s hs0.le) hn_le
      calc jumpExp (cp (trunc ν n)) s
          = ENNReal.ofReal (1 - Real.exp (-(jumpExp (trunc ν n) s).toReal)) := by
            rw [jumpExp_eq_ofReal (hcp n) hs0.le, laplace_cp (isCausal_trunc n) hs0.le]
            simp
        _ ≤ ENNReal.ofReal (jumpExp (trunc ν n) s).toReal :=
            ENNReal.ofReal_le_ofReal (one_sub_exp_neg_le _)
        _ = jumpExp (trunc ν n) s := ENNReal.ofReal_toReal hn_ne
        _ ≤ jumpExp ν s := hn_le
    have key : ENNReal.ofReal (1 / 2) * cp (trunc ν n) (Ioi r)
        ≤ ENNReal.ofReal (1 / 2) * ε :=
      (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hhalf) zero_le).trans
        ((mul_measure_Ioi_le_jumpExp _ hs0.le r).trans (hJ.trans hsJ.le))
    calc (P n : Measure ℝ) {x | r < ‖x‖} ≤ (P n : Measure ℝ) (Ioi r ∪ Iio 0) := measure_mono hsub
      _ ≤ (P n : Measure ℝ) (Ioi r) + (P n : Measure ℝ) (Iio 0) := measure_union_le _ _
      _ = cp (trunc ν n) (Ioi r) := by
          rw [hPval, show cp (trunc ν n) (Iio 0) = 0 from hcp n, add_zero]
      _ ≤ ε := (ENNReal.mul_le_mul_iff_right hhalf0 ENNReal.ofReal_ne_top).1 key
  -- Prokhorov: a cluster point of the sequence.
  obtain ⟨Q, -, hQ⟩ := (isCompact_closure_of_isTightMeasureSet htight).exists_mapClusterPt
    (f := atTop) (u := P)
    (le_principal_iff.2 (mem_map.2 (univ_mem' fun n => subset_closure (mem_range_self n))))
  have hident : ∀ (g : ℝ →ᵇ ℝ) (L : ℝ),
      Tendsto (fun n => ∫ t, g t ∂(P n : Measure ℝ)) atTop (𝓝 L) →
        ∫ t, g t ∂(Q : Measure ℝ) = L := by
    intro g L hL
    have h := hQ.tendsto_comp
      ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction g).tendsto Q)
    exact eq_of_nhds_neBot (ClusterPt.mono h hL)
  -- The cluster point is causal.
  have hQc : IsCausal (Q : Measure ℝ) := by
    have h0 : ∫ t, negBCF t ∂(Q : Measure ℝ) = 0 :=
      hident negBCF 0 (by simp_rw [hPval, integral_negBCF (hcp _)]; exact tendsto_const_nhds)
    have hae := (integral_eq_zero_iff_of_nonneg
      (fun t => le_min zero_le_one (le_max_left _ _)) (negBCF.integrable _)).1 h0
    rw [isCausal_iff_ae]
    filter_upwards [hae] with t ht
    by_contra hneg
    have : min 1 (max 0 (-t)) = 0 := ht
    have : 0 < min 1 (max 0 (-t)) := lt_min one_pos (lt_max_of_lt_right (by linarith))
    linarith
  refine ⟨Q, inferInstance, hQc, fun s hs => ?_⟩
  rw [← integral_expBCF hQc hs]
  exact hident _ _ (hlapn s hs)

/-- **The subordinator correspondence, existence half**: drift plus jumps. -/
theorem exists_laplace_eq_exp_neg_levyExponent {b₀ : ℝ} (hb₀ : 0 ≤ b₀)
    {ν : Measure ℝ} (hν : IsCausal ν) (hfin : ∀ s, 0 ≤ s → levyExponent b₀ ν s ≠ ⊤) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ IsCausal μ ∧
      ∀ s, 0 ≤ s → laplace μ s = Real.exp (-(levyExponent b₀ ν s).toReal) := by
  have hJ : ∀ s, 0 ≤ s → jumpExp ν s ≠ ⊤ := fun s hs =>
    ne_top_of_le_ne_top (hfin s hs) (by rw [levyExponent_eq]; exact le_add_self)
  obtain ⟨Q, hQp, hQc, hQl⟩ := exists_jump hν hJ
  have hemb : MeasurableEmbedding (fun t : ℝ => t + b₀) :=
    (Homeomorph.addRight b₀).toMeasurableEquiv.measurableEmbedding
  refine ⟨Q.map (fun t => t + b₀),
    Measure.isProbabilityMeasure_map hemb.measurable.aemeasurable, ?_, fun s hs => ?_⟩
  · rw [IsCausal, hemb.map_apply]
    refine measure_mono_null (fun t ht => ?_) hQc
    simp only [mem_preimage, mem_Iio] at ht ⊢
    linarith
  · rw [laplace, hemb.integral_map, levyExponent_eq,
      ENNReal.toReal_add ENNReal.ofReal_ne_top (hJ s hs), ENNReal.toReal_ofReal (mul_nonneg hb₀ hs),
      neg_add, Real.exp_add, ← hQl s hs, laplace, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only
    rw [← Real.exp_add]
    congr 1
    ring

end CompoundPoisson

end Hemigroup
