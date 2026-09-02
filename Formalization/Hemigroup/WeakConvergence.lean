/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Hemigroup.Injectivity
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Convergence of moments forces weak convergence on `[0,1]`

The convergence counterpart of `Injectivity.ext_of_moments`, and the file that settles ledger
**A5**: the continuity theorem, in the form this development uses, is **proved** here.
`#print axioms` on `tendsto_integral_of_tendsto_laplace` reduces to Lean core, so A5 does not
enter `trust-boundary.txt`.

Worth recording that the route I expected — Prokhorov for a convergent subsequence, portmanteau
for causality of the limit, `laplace_injective` to identify it, compact-plus-unique-cluster-point
to finish — was **not needed at all**. Pushing forward along `x = e^{-t}` lands the measures on a
compact carrier, where Weierstrass does the work compactness would have done, and the only price
is the clamping estimate on the way back. Mathlib's Prokhorov is never invoked.

`Injectivity.lean` showed that two finite measures carried by `[0,1]` with the same moments are
equal, by Weierstrass. The same `ε/3` argument, with "equal" replaced by "converging", shows
that measures carried by `[0,1]` whose moments converge converge weakly — and on a compact
carrier that needs **no tightness at all**, which is why this half is separated out.

Tightness re-enters only when this is transported back along `x = e^{-t}`, in the second half:
weak convergence of the pushforwards does not by itself give weak convergence of the originals,
because mass can escape to `t = +∞`, which is exactly the atom at `x = 0` that tightness rules
out.
-/

namespace Hemigroup

open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology ENNReal

/-! ## Polynomials -/

/-- Convergence of moments gives convergence of polynomial integrals, by linearity. -/
theorem tendsto_integral_polynomial_of_moments {ν : ℕ → Measure ℝ} {ν₀ : Measure ℝ}
    [∀ n, IsFiniteMeasure (ν n)] [IsFiniteMeasure ν₀]
    (hcar : ∀ n, (ν n) (Icc (0 : ℝ) 1)ᶜ = 0) (hcar₀ : ν₀ (Icc (0 : ℝ) 1)ᶜ = 0)
    (hmom : ∀ k : ℕ, Tendsto (fun n => ∫ x, x ^ k ∂(ν n)) atTop (𝓝 (∫ x, x ^ k ∂ν₀)))
    (p : Polynomial ℝ) :
    Tendsto (fun n => ∫ x, p.eval x ∂(ν n)) atTop (𝓝 (∫ x, p.eval x ∂ν₀)) := by
  have hint : ∀ (σ : Measure ℝ) [IsFiniteMeasure σ], σ (Icc (0 : ℝ) 1)ᶜ = 0 → ∀ i : ℕ,
      Integrable (fun x : ℝ => p.coeff i * x ^ i) σ := fun σ _ hσ i =>
    integrable_of_carried isCompact_Icc hσ (by fun_prop)
  simp only [Polynomial.eval_eq_sum_range]
  have hsum : ∀ n, ∫ x, ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * x ^ i ∂(ν n)
      = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * ∫ x, x ^ i ∂(ν n) := by
    intro n
    rw [integral_finsetSum _ (fun i _ => hint (ν n) (hcar n) i)]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  have hsum₀ : ∫ x, ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * x ^ i ∂ν₀
      = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * ∫ x, x ^ i ∂ν₀ := by
    rw [integral_finsetSum _ (fun i _ => hint ν₀ hcar₀ i)]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  simp only [hsum]
  rw [hsum₀]
  exact tendsto_finsetSum _ fun i _ => (hmom i).const_mul _

/-! ## The `ε/3` argument -/

/-- **Converging moments force converging integrals**, for measures carried by `[0,1]`.

The compact carrier is what makes this unconditional: Weierstrass approximates any bounded
continuous `f` uniformly on `[0,1]` by a polynomial, and the measures see nothing else. -/
theorem tendsto_integral_of_moments {ν : ℕ → Measure ℝ} {ν₀ : Measure ℝ}
    [∀ n, IsProbabilityMeasure (ν n)] [IsProbabilityMeasure ν₀]
    (hcar : ∀ n, (ν n) (Icc (0 : ℝ) 1)ᶜ = 0) (hcar₀ : ν₀ (Icc (0 : ℝ) 1)ᶜ = 0)
    (hmom : ∀ k : ℕ, Tendsto (fun n => ∫ x, x ^ k ∂(ν n)) atTop (𝓝 (∫ x, x ^ k ∂ν₀)))
    (f : ℝ →ᵇ ℝ) :
    Tendsto (fun n => ∫ x, f x ∂(ν n)) atTop (𝓝 (∫ x, f x ∂ν₀)) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  -- Approximate `f` by a polynomial to within `δ/4` on the carrier.
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 (fun x => f x)
    f.continuous.continuousOn (δ / 4) (by linarith)
  have hb : ∀ x ∈ Icc (0 : ℝ) 1, |f x - p.eval x| ≤ δ / 4 := fun x hx => by
    rw [abs_sub_comm]; exact (hp x hx).le
  -- The two `ε` terms, using that every measure here has mass one.
  have hfν : ∀ n, Integrable (fun x => f x) (ν n) := fun n =>
    integrable_of_carried isCompact_Icc (hcar n) f.continuous
  have hpν : ∀ n, Integrable (fun x => p.eval x) (ν n) := fun n =>
    integrable_of_carried isCompact_Icc (hcar n) (by fun_prop)
  have hstep : ∀ n, |∫ x, f x ∂(ν n) - ∫ x, p.eval x ∂(ν n)| ≤ δ / 4 := by
    intro n
    have h := abs_integral_sub_le_of_carried (hcar n) (hfν n) (hpν n) hb
    simpa using h
  have hstep₀ : |∫ x, f x ∂ν₀ - ∫ x, p.eval x ∂ν₀| ≤ δ / 4 := by
    have h := abs_integral_sub_le_of_carried hcar₀
      (integrable_of_carried isCompact_Icc hcar₀ f.continuous)
      (integrable_of_carried isCompact_Icc hcar₀ (by fun_prop)) hb
    simpa using h
  -- The middle term converges.
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp
    (tendsto_integral_polynomial_of_moments hcar hcar₀ hmom p) (δ / 4) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have hmid : |∫ x, p.eval x ∂(ν n) - ∫ x, p.eval x ∂ν₀| < δ / 4 := by
    simpa [Real.dist_eq] using hN n hn
  have := hstep n
  rw [Real.dist_eq]
  calc |∫ x, f x ∂(ν n) - ∫ x, f x ∂ν₀|
      ≤ |∫ x, f x ∂(ν n) - ∫ x, p.eval x ∂(ν n)|
        + |∫ x, p.eval x ∂(ν n) - ∫ x, p.eval x ∂ν₀|
        + |∫ x, p.eval x ∂ν₀ - ∫ x, f x ∂ν₀| := by
        have h1 := abs_sub_le (∫ x, f x ∂(ν n)) (∫ x, p.eval x ∂(ν n)) (∫ x, p.eval x ∂ν₀)
        have h2 := abs_sub_le (∫ x, f x ∂(ν n)) (∫ x, p.eval x ∂ν₀) (∫ x, f x ∂ν₀)
        linarith
    _ < δ := by
        rw [abs_sub_comm (∫ x, p.eval x ∂ν₀)]
        linarith [hstep₀]

/-! ## Transport back along `x = e^{-t}`

Weak convergence of the pushforwards is not enough on its own: `x ↦ -log x` blows up at `0`, so
a bounded continuous `f` on `ℝ` does not pull back to a bounded continuous function on `[0,1]`.
Clamping the logarithm below repairs continuity at the cost of changing `f` on the far tail —
and tightness is exactly the statement that the measures put little mass there.
-/

/-- The inverse of `expNeg`, clamped so as to stay continuous at the origin: equal to
`x ↦ -log x` on `[e^{-T}, ∞)` and constant below. -/
noncomputable def clampInv (T : ℝ) : C(ℝ, ℝ) :=
  ⟨fun x => -(Real.log (max x (Real.exp (-T)))),
    ((continuous_id.max continuous_const).log
      (fun x => ne_of_gt (lt_of_lt_of_le (Real.exp_pos _) (le_max_right x _)))).neg⟩

@[simp] lemma clampInv_apply (T x : ℝ) :
    clampInv T x = -(Real.log (max x (Real.exp (-T)))) := rfl

/-- On `[0,T]` the clamp is inactive and `clampInv` really does invert `expNeg`. -/
lemma clampInv_expNeg {t T : ℝ} (htT : t ≤ T) : clampInv T (expNeg t) = t := by
  have hmax : max (Real.exp (-t)) (Real.exp (-T)) = Real.exp (-t) :=
    max_eq_left (Real.exp_le_exp.mpr (by linarith))
  simp [clampInv_apply, expNeg, hmax, Real.log_exp]

/-- **The transport estimate.** Replacing `f` by its clamped pull-back costs at most twice the
sup-norm times the mass outside `[0,T]`, and for a causal measure that mass is the right tail. -/
theorem abs_integral_sub_integral_map_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCausal μ) {T : ℝ} (f : ℝ →ᵇ ℝ) :
    |∫ t, f t ∂μ - ∫ x, (f.compContinuous (clampInv T)) x ∂(μ.map expNeg)|
      ≤ 2 * ‖f‖ * (μ (Ioi T)).toReal := by
  set g : ℝ →ᵇ ℝ := f.compContinuous (clampInv T) with hg
  set h : ℝ →ᵇ ℝ := f - g.compContinuous ⟨expNeg, continuous_expNeg⟩ with hh
  have hmap : ∫ x, g x ∂(μ.map expNeg) = ∫ t, g (expNeg t) ∂μ :=
    measurableEmbedding_expNeg.integral_map _
  have hgi : Integrable (fun t : ℝ => g (expNeg t)) μ := by
    have hi := (g.compContinuous ⟨expNeg, continuous_expNeg⟩).integrable μ
    simpa [Function.comp_def] using hi
  have hsub : ∫ t, f t ∂μ - ∫ t, g (expNeg t) ∂μ = ∫ t, h t ∂μ := by
    simp only [hh, BoundedContinuousFunction.sub_apply,
      BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk]
    exact (integral_sub (f.integrable μ) hgi).symm
  rw [hmap, hsub]
  have hzero : ∀ t ∈ Icc (0 : ℝ) T, h t = 0 := by
    intro t ht
    simp only [hh, BoundedContinuousFunction.sub_apply,
      BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk, hg]
    rw [clampInv_expNeg ht.2]
    simp
  have hbdd : ∀ t, |h t| ≤ 2 * ‖f‖ := by
    intro t
    simp only [hh, BoundedContinuousFunction.sub_apply]
    have h1 : |f t| ≤ ‖f‖ := f.norm_coe_le_norm t
    have h2 : |(g.compContinuous ⟨expNeg, continuous_expNeg⟩) t| ≤ ‖f‖ := by
      simp only [BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk, hg]
      exact f.norm_coe_le_norm _
    calc |f t - (g.compContinuous ⟨expNeg, continuous_expNeg⟩) t|
        ≤ |f t| + |(g.compContinuous ⟨expNeg, continuous_expNeg⟩) t| := abs_sub _ _
      _ ≤ ‖f‖ + ‖f‖ := add_le_add h1 h2
      _ = 2 * ‖f‖ := by ring
  have hcompl : μ ((Icc (0 : ℝ) T)ᶜ) ≤ μ (Ioi T) := by
    have hsubset : (Icc (0 : ℝ) T)ᶜ ⊆ Iio 0 ∪ Ioi T := by
      intro x hx
      simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at hx
      exact hx.imp id id
    refine (measure_mono hsubset).trans ((measure_union_le _ _).trans ?_)
    rw [hμ, zero_add]
  calc |∫ t, h t ∂μ| ≤ ∫ t, ‖h t‖ ∂μ := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := μ) (fun t => h t)
    _ ≤ ∫ t, ((Icc (0 : ℝ) T)ᶜ).indicator (fun _ => 2 * ‖f‖) t ∂μ := by
        refine integral_mono_ae (h.integrable μ).norm
          ((integrable_const _).indicator measurableSet_Icc.compl) ?_
        filter_upwards with t
        by_cases hc : t ∈ Icc (0 : ℝ) T
        · rw [indicator_of_notMem (by simpa using hc), hzero t hc]
          simp
        · rw [indicator_of_mem (by simpa using hc)]
          simpa [Real.norm_eq_abs] using hbdd t
    _ = 2 * ‖f‖ * (μ ((Icc (0 : ℝ) T)ᶜ)).toReal := by
        rw [MeasureTheory.integral_indicator_const _ measurableSet_Icc.compl, smul_eq_mul,
          mul_comm, measureReal_def]
    _ ≤ 2 * ‖f‖ * (μ (Ioi T)).toReal :=
        mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (measure_ne_top _ _) hcompl)
          (by positivity)

/-! ## The continuity theorem, for causal measures

Ledger **A5** for the case this development uses — proved, not cited.
-/

/-- **Convergence of Laplace transforms plus tightness gives weak convergence**, for causal
probability measures on `ℝ`.

This is the half of `prop:laplace-continuity` (ledger A5) that `thm:main-characterization` (⇐)
uses: transforms to measures, probability form. Feller's Theorem 2a in its general shape carries
a boundedness hypothesis whose loss is the classical trap; the probability form carries it for
free, which is why the statement is restricted here.

The proof is the two halves above: push forward along `x = e^{-t}` onto the compact `[0,1]`,
where converging Laplace values at the naturals *are* converging moments and Weierstrass
finishes; then transport back, where tightness pays for the clamping of `-log` at the origin. -/
theorem tendsto_integral_of_tendsto_laplace {μ : ℕ → Measure ℝ} {μ₀ : Measure ℝ}
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure μ₀]
    (hcau : ∀ n, IsCausal (μ n)) (hcau₀ : IsCausal μ₀)
    (htight : ∀ η : ℝ, 0 < η → ∃ T : ℝ,
      (∀ n, ((μ n) (Ioi T)).toReal ≤ η) ∧ (μ₀ (Ioi T)).toReal ≤ η)
    (hlap : ∀ s : ℝ, 0 ≤ s → Tendsto (fun n => laplace (μ n) s) atTop (nhds (laplace μ₀ s)))
    (f : ℝ →ᵇ ℝ) :
    Tendsto (fun n => ∫ t, f t ∂(μ n)) atTop (nhds (∫ t, f t ∂μ₀)) := by
  haveI : ∀ n, IsProbabilityMeasure ((μ n).map expNeg) := fun n =>
    Measure.isProbabilityMeasure_map continuous_expNeg.measurable.aemeasurable
  haveI : IsProbabilityMeasure (μ₀.map expNeg) :=
    Measure.isProbabilityMeasure_map continuous_expNeg.measurable.aemeasurable
  -- Half one: the pushforwards converge weakly, by Weierstrass on `[0,1]`.
  have hweak : ∀ g : ℝ →ᵇ ℝ, Tendsto (fun n => ∫ x, g x ∂((μ n).map expNeg)) atTop
      (nhds (∫ x, g x ∂(μ₀.map expNeg))) := by
    refine tendsto_integral_of_moments (fun n => map_expNeg_compl_Icc (hcau n))
      (map_expNeg_compl_Icc hcau₀) fun k => ?_
    simp only [integral_pow_map_expNeg]
    exact hlap k (Nat.cast_nonneg k)
  -- Half two: transport back, paying for the clamp with tightness.
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set η : ℝ := δ / (8 * (‖f‖ + 1)) with hη_def
  have hnf : (0 : ℝ) ≤ ‖f‖ := norm_nonneg f
  have hη : 0 < η := by positivity
  obtain ⟨T, hTn, hT0⟩ := htight η hη
  set g : ℝ →ᵇ ℝ := f.compContinuous (clampInv T) with hg_def
  have hsmall : 2 * ‖f‖ * η ≤ δ / 4 := by
    have hX : (0 : ℝ) < 8 * (‖f‖ + 1) := by positivity
    rw [hη_def, ← mul_div_assoc, div_le_div_iff₀ hX (by norm_num : (0 : ℝ) < 4)]
    nlinarith [hnf, hδ.le]
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hweak g) (δ / 4) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have e₁ : |∫ t, f t ∂(μ n) - ∫ x, g x ∂((μ n).map expNeg)| ≤ δ / 4 :=
    (abs_integral_sub_integral_map_le (hcau n) f).trans
      ((mul_le_mul_of_nonneg_left (hTn n) (by positivity)).trans hsmall)
  have e₂ : |∫ x, g x ∂((μ n).map expNeg) - ∫ x, g x ∂(μ₀.map expNeg)| < δ / 4 := by
    simpa [Real.dist_eq] using hN n hn
  have e₃ : |∫ t, f t ∂μ₀ - ∫ x, g x ∂(μ₀.map expNeg)| ≤ δ / 4 :=
    (abs_integral_sub_integral_map_le hcau₀ f).trans
      ((mul_le_mul_of_nonneg_left hT0 (by positivity)).trans hsmall)
  rw [Real.dist_eq]
  calc |∫ t, f t ∂(μ n) - ∫ t, f t ∂μ₀|
      ≤ |∫ t, f t ∂(μ n) - ∫ x, g x ∂((μ n).map expNeg)|
        + |∫ x, g x ∂((μ n).map expNeg) - ∫ x, g x ∂(μ₀.map expNeg)|
        + |∫ x, g x ∂(μ₀.map expNeg) - ∫ t, f t ∂μ₀| := by
        have h1 := abs_sub_le (∫ t, f t ∂(μ n)) (∫ x, g x ∂((μ n).map expNeg))
          (∫ x, g x ∂(μ₀.map expNeg))
        have h2 := abs_sub_le (∫ t, f t ∂(μ n)) (∫ x, g x ∂(μ₀.map expNeg)) (∫ t, f t ∂μ₀)
        linarith
    _ < δ := by
        rw [abs_sub_comm (∫ x, g x ∂(μ₀.map expNeg))]
        linarith

end Hemigroup
