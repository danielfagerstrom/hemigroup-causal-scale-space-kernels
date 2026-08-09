/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.Levy
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Injectivity of the Laplace transform on causal measures

The M0 remainder: a finite causal measure on `ℝ` is determined by its Laplace transform on
`[0,∞)`. Blueprint: `prop:laplace-uniqueness` (Proposition 2.6), which is ledger **A6** on
paper — a cited interface. Here it is **proved**, so nothing in the Lean development needs to
trust it.

## The route, and why it is this one

Two routes were ruled out first.

* Mathlib's `Measure.ext_of_complexMGF_id_eq` needs the complex moment-generating functions to
  agree on *all* of `ℂ`, while `eqOn_complexMGF_of_mgf'` delivers agreement only on the open
  strip where the exponential is integrable. Mathlib's own `TODO` at that lemma records the gap
  as open, so the analytic-continuation route is not currently available.
* Applying Stone–Weierstrass on `ℝ` directly fails: for `s ≥ 0` the function `t ↦ e^{-st}` is
  unbounded on `ℝ`, and the obvious bounded surrogate (clamping `t` at `0`) is constant on
  `(-∞,0]` and so does not separate points.

What works is to move the problem to a compact set by the substitution `x = e^{-t}`, which is
exactly the classical proof. `expNeg` is injective and continuous, hence a measurable embedding
(Lusin–Souslin, `Continuous.measurableEmbedding`), and it carries a causal measure into `[0,1]`.
There the Laplace transform *at natural numbers* is the sequence of moments, polynomials are
dense by Weierstrass, and two finite measures agreeing on all bounded continuous functions are
equal.

Note that only `laplace μ n` for `n : ℕ` is used. The hypothesis is stated for all `s ≥ 0`
because that is the form every caller has, but the proof needs far less — which is the usual
strength of the moment route.
-/

namespace Hemigroup

open MeasureTheory Set

/-! ## The substitution `x = e^{-t}` -/

/-- The change of variable carrying the half-line onto `(0,1]`. -/
noncomputable def expNeg (t : ℝ) : ℝ := Real.exp (-t)

lemma continuous_expNeg : Continuous expNeg := by unfold expNeg; fun_prop

lemma injective_expNeg : Function.Injective expNeg := fun x y hxy => by
  have : -x = -y := Real.exp_eq_exp.mp hxy
  linarith

/-- `expNeg` is a measurable embedding: injective and continuous on a Polish space. This is what
lets the argument be transported back to the original measures at the end. -/
lemma measurableEmbedding_expNeg : MeasurableEmbedding expNeg :=
  continuous_expNeg.measurableEmbedding injective_expNeg

lemma expNeg_mem_Icc {t : ℝ} (ht : 0 ≤ t) : expNeg t ∈ Icc (0 : ℝ) 1 :=
  ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by linarith)⟩

/-- The pushforward of a causal measure is carried by the compact set `[0,1]`. This is the step
that makes Weierstrass applicable, and the only place causality is used. -/
lemma map_expNeg_compl_Icc {μ : Measure ℝ} (h : IsCausal μ) :
    (μ.map expNeg) (Icc (0 : ℝ) 1)ᶜ = 0 := by
  rw [Measure.map_apply continuous_expNeg.measurable measurableSet_Icc.compl]
  refine measure_mono_null (fun t ht => ?_) h
  by_contra hc
  exact ht (expNeg_mem_Icc (not_lt.mp hc))

instance isFiniteMeasure_map_expNeg {μ : Measure ℝ} [IsFiniteMeasure μ] :
    IsFiniteMeasure (μ.map expNeg) := by
  constructor
  rw [Measure.map_apply continuous_expNeg.measurable MeasurableSet.univ, preimage_univ]
  exact measure_lt_top μ univ

/-- **The Laplace transform at a natural number is a moment of the pushforward.** This is the
identity the whole proof turns on: `∫ x^n d(expNeg_* μ) = ∫ e^{-nt} dμ`. -/
lemma integral_pow_map_expNeg {μ : Measure ℝ} (n : ℕ) :
    ∫ x, x ^ n ∂(μ.map expNeg) = laplace μ n := by
  rw [measurableEmbedding_expNeg.integral_map, laplace]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [expNeg]
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-! ## Integrating continuous functions against a compactly carried measure -/

/-- A continuous function is integrable against a finite measure carried by a compact set — it
need not be bounded on all of `ℝ`, which is what lets polynomials be used below. -/
lemma integrable_of_carried {ν : Measure ℝ} [IsFiniteMeasure ν] {K : Set ℝ} (hK : IsCompact K)
    (hcar : ν Kᶜ = 0) {g : ℝ → ℝ} (hg : Continuous g) : Integrable g ν := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨hg.aestronglyMeasurable, ?_⟩
  have hae : ∀ᵐ x ∂ν, ‖g x‖ ≤ ‖C‖ := by
    rw [ae_iff]
    refine measure_mono_null (fun x hx => ?_) hcar
    simp only [mem_setOf_eq, not_le] at hx
    exact fun hxK => absurd ((hC x hxK).trans (le_abs_self C)) (not_le.mpr hx)
  exact (hasFiniteIntegral_const C).mono hae

/-- The `ε`-estimate: two integrals of functions that are uniformly `ε`-close on the carrier
differ by at most `ε` times the mass. -/
lemma abs_integral_sub_le_of_carried {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hcar : ν (Icc (0 : ℝ) 1)ᶜ = 0) {g₁ g₂ : ℝ → ℝ}
    (h₁ : Integrable g₁ ν) (h₂ : Integrable g₂ ν) {ε : ℝ}
    (hb : ∀ x ∈ Icc (0 : ℝ) 1, |g₁ x - g₂ x| ≤ ε) :
    |∫ x, g₁ x ∂ν - ∫ x, g₂ x ∂ν| ≤ ε * (ν univ).toReal := by
  rw [← integral_sub h₁ h₂]
  have hae : ∀ᵐ x ∂ν, ‖g₁ x - g₂ x‖ ≤ ε := by
    rw [ae_iff]
    refine measure_mono_null (fun x hx => ?_) hcar
    simp only [mem_setOf_eq, not_le, Real.norm_eq_abs] at hx
    exact fun hxK => absurd (hb x hxK) (not_le.mpr hx)
  calc |∫ x, (g₁ x - g₂ x) ∂ν|
      ≤ ∫ x, ‖g₁ x - g₂ x‖ ∂ν := by
        simpa [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (μ := ν) (fun x => g₁ x - g₂ x)
    _ ≤ ∫ _, ε ∂ν := integral_mono_ae (h₁.sub h₂).norm (integrable_const ε) hae
    _ = ε * (ν univ).toReal := by
        rw [integral_const, smul_eq_mul, mul_comm, measureReal_def]

/-! ## Equal moments force equal measures on `[0,1]` -/

/-- Equal moments give equal polynomial integrals, by linearity. -/
lemma integral_polynomial_eq_of_moments {ν ν' : Measure ℝ} [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    (hν : ν (Icc (0 : ℝ) 1)ᶜ = 0) (hν' : ν' (Icc (0 : ℝ) 1)ᶜ = 0)
    (hmom : ∀ n : ℕ, ∫ x, x ^ n ∂ν = ∫ x, x ^ n ∂ν') (p : Polynomial ℝ) :
    ∫ x, p.eval x ∂ν = ∫ x, p.eval x ∂ν' := by
  have hint : ∀ (σ : Measure ℝ) [IsFiniteMeasure σ], σ (Icc (0 : ℝ) 1)ᶜ = 0 → ∀ i : ℕ,
      Integrable (fun x : ℝ => p.coeff i * x ^ i) σ := fun σ _ hσ i =>
    integrable_of_carried isCompact_Icc hσ (by fun_prop)
  simp only [Polynomial.eval_eq_sum_range]
  rw [integral_finsetSum _ (fun i _ => hint ν hν i),
    integral_finsetSum _ (fun i _ => hint ν' hν' i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_const_mul, hmom i]

/-- Two finite measures carried by `[0,1]` with the same moments are equal. Weierstrass plus the
`ε`-estimate. -/
theorem ext_of_moments {ν ν' : Measure ℝ} [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    (hν : ν (Icc (0 : ℝ) 1)ᶜ = 0) (hν' : ν' (Icc (0 : ℝ) 1)ᶜ = 0)
    (hmom : ∀ n : ℕ, ∫ x, x ^ n ∂ν = ∫ x, x ^ n ∂ν') : ν = ν' := by
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  have hfν : Integrable (fun x => f x) ν :=
    integrable_of_carried isCompact_Icc hν f.continuous
  have hfν' : Integrable (fun x => f x) ν' :=
    integrable_of_carried isCompact_Icc hν' f.continuous
  -- `|∫f dν - ∫f dν'| ≤ δ` for every `δ > 0`, via a polynomial sandwiched between them.
  have key : ∀ δ : ℝ, 0 < δ → |∫ x, f x ∂ν - ∫ x, f x ∂ν'| ≤ δ := by
    intro δ hδ
    set M : ℝ := (ν univ).toReal + (ν' univ).toReal with hM
    have hM0 : 0 ≤ M := by positivity
    have hpos : 0 < δ / (M + 1) := by positivity
    obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 (fun x => f x)
      f.continuous.continuousOn _ hpos
    have hpν : Integrable (fun x => p.eval x) ν :=
      integrable_of_carried isCompact_Icc hν (by fun_prop)
    have hpν' : Integrable (fun x => p.eval x) ν' :=
      integrable_of_carried isCompact_Icc hν' (by fun_prop)
    have hb : ∀ x ∈ Icc (0 : ℝ) 1, |f x - p.eval x| ≤ δ / (M + 1) := fun x hx => by
      rw [abs_sub_comm]; exact (hp x hx).le
    have e₁ := abs_integral_sub_le_of_carried hν hfν hpν hb
    have e₂ := abs_integral_sub_le_of_carried hν' hfν' hpν' hb
    have emid : ∫ x, p.eval x ∂ν = ∫ x, p.eval x ∂ν' :=
      integral_polynomial_eq_of_moments hν hν' hmom p
    have htri : |∫ x, f x ∂ν - ∫ x, f x ∂ν'|
        ≤ |∫ x, f x ∂ν - ∫ x, p.eval x ∂ν| + |∫ x, f x ∂ν' - ∫ x, p.eval x ∂ν'| := by
      rw [emid]
      calc |∫ x, f x ∂ν - ∫ x, f x ∂ν'|
          = |(∫ x, f x ∂ν - ∫ x, p.eval x ∂ν') - (∫ x, f x ∂ν' - ∫ x, p.eval x ∂ν')| := by
            ring_nf
        _ ≤ _ := abs_sub _ _
    refine htri.trans ?_
    have : δ / (M + 1) * (ν univ).toReal + δ / (M + 1) * (ν' univ).toReal ≤ δ := by
      rw [← mul_add, ← hM, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    exact (add_le_add e₁ e₂).trans this
  have habs : |∫ x, f x ∂ν - ∫ x, f x ∂ν'| ≤ 0 :=
    le_of_forall_pos_le_add fun δ hδ => by simpa using key δ hδ
  exact sub_eq_zero.mp (abs_nonpos_iff.mp habs)

/-! ## The theorem -/

/-- **Injectivity of the Laplace transform on causal measures**, blueprint
`prop:laplace-uniqueness`. Two finite measures carried by `[0,∞)` with the same Laplace
transform on `[0,∞)` are equal.

Proved, not axiomatised. On paper this is ledger A6 (Feller Vol. 2, §XIII.1, Theorems 1 and
1a); the Lean development does not need that entry, and the corresponding line never enters
`trust-boundary.txt`. -/
theorem laplace_injective {μ ρ : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ρ]
    (hμ : IsCausal μ) (hρ : IsCausal ρ) (h : ∀ s, 0 ≤ s → laplace μ s = laplace ρ s) :
    μ = ρ := by
  -- The pushforwards agree, by Weierstrass on `[0,1]`.
  have hmap : μ.map expNeg = ρ.map expNeg := by
    refine ext_of_moments (map_expNeg_compl_Icc hμ) (map_expNeg_compl_Icc hρ) fun n => ?_
    rw [integral_pow_map_expNeg, integral_pow_map_expNeg]
    exact h n (Nat.cast_nonneg n)
  -- Transport back: `expNeg` is a measurable embedding, so the pushforward loses nothing.
  ext A hA
  have himg : MeasurableSet (expNeg '' A) := measurableEmbedding_expNeg.measurableSet_image' hA
  have hμA : (μ.map expNeg) (expNeg '' A) = μ A := by
    rw [Measure.map_apply continuous_expNeg.measurable himg,
      Set.preimage_image_eq A injective_expNeg]
  have hρA : (ρ.map expNeg) (expNeg '' A) = ρ A := by
    rw [Measure.map_apply continuous_expNeg.measurable himg,
      Set.preimage_image_eq A injective_expNeg]
  rw [← hμA, ← hρA, hmap]

end Hemigroup
