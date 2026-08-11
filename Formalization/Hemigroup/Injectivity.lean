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
open scoped ENNReal

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

/-! ## Beyond finite measures

Chapter 9 needs the transform to determine measures that are *not* finite: `κ^{(x)}`, the
potential kernel `ℓ^{(x)}` and Lebesgue measure all fail to be, and the Sonine identity compares
them. This is the general clause of ledger **A6**, and it is proved here rather than conceded —
so A6 stays off `trust-boundary.txt` in its general form as well as its restricted one.

The hypothesis that actually does the work is weaker than local finiteness, and worth stating
in its own terms: **the transform is finite at a single point**. That already forces enough,
because damping by `e^{-s₀t}` turns the measure into a finite one without losing any
information — the density is strictly positive everywhere, so the operation is invertible.
Local finiteness is then a consequence, not an assumption.
-/

/-- Damping a causal measure by `e^{-s₀ t}` shifts its transform. -/
theorem laplaceL_withDensity_expNeg (μ : Measure ℝ) (s₀ s : ℝ) :
    laplaceL (μ.withDensity fun t => ENNReal.ofReal (Real.exp (-(s₀ * t)))) s
      = laplaceL μ (s₀ + s) := by
  have hf : Measurable fun t : ℝ => ENNReal.ofReal (Real.exp (-(s₀ * t))) := by fun_prop
  have hg : Measurable fun t : ℝ => ENNReal.ofReal (Real.exp (-(s * t))) := by fun_prop
  rw [laplaceL, lintegral_withDensity_eq_lintegral_mul _ hf hg, laplaceL]
  refine lintegral_congr fun t => ?_
  rw [Pi.mul_apply, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

/-- **Injectivity of the Laplace transform without a finiteness assumption on the measures.**

Two causal measures whose transforms agree on `[s₀, ∞)`, one of them finite at `s₀`, are equal.
The measures themselves may be infinite — Lebesgue measure on the half line is the case chapter 9
needs.

The proof is the classical damping trick and nothing more: `e^{-s₀t}μ(dt)` is *finite* precisely
because the transform converges at `s₀`, its transform at `s` is `μ`'s at `s₀ + s`, so
`laplace_injective` applies; and the damping is undone by multiplying the density back, which is
legitimate because `e^{-s₀t}` is everywhere positive and finite. -/
theorem laplaceL_injective_of_ne_top {μ ρ : Measure ℝ} (hμ : IsCausal μ) (hρ : IsCausal ρ)
    {s₀ : ℝ} (hfin : laplaceL μ s₀ ≠ ⊤) (h : ∀ s, s₀ ≤ s → laplaceL μ s = laplaceL ρ s) :
    μ = ρ := by
  set f : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-(s₀ * t))) with hf_def
  set g : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (s₀ * t)) with hg_def
  have hfm : Measurable f := by fun_prop
  have hgm : Measurable g := by fun_prop
  -- The damped measures are finite: their masses are the transforms at `s₀`.
  have hmass : ∀ ν : Measure ℝ, ∫⁻ t, f t ∂ν = laplaceL ν s₀ := fun ν => rfl
  haveI : IsFiniteMeasure (μ.withDensity f) :=
    isFiniteMeasure_withDensity (by rw [hmass]; exact hfin)
  haveI : IsFiniteMeasure (ρ.withDensity f) :=
    isFiniteMeasure_withDensity (by rw [hmass, ← h s₀ le_rfl]; exact hfin)
  -- They are causal, being absolutely continuous with respect to causal measures.
  have hcau : ∀ ν : Measure ℝ, IsCausal ν → IsCausal (ν.withDensity f) := fun ν hν =>
    (withDensity_absolutelyContinuous ν f) hν
  -- Their transforms agree, by the shift.
  have hdamped : μ.withDensity f = ρ.withDensity f := by
    refine laplace_injective (hcau μ hμ) (hcau ρ hρ) fun s hs => ?_
    rw [laplace_eq_toReal_laplaceL, laplace_eq_toReal_laplaceL,
      laplaceL_withDensity_expNeg, laplaceL_withDensity_expNeg,
      h (s₀ + s) (by linarith)]
  -- Undo the damping: `f * g = 1` pointwise, so `withDensity g` inverts `withDensity f`.
  have hfg : f * g = 1 := by
    funext t
    rw [Pi.mul_apply, hf_def, hg_def, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
      neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one, Pi.one_apply]
  calc μ = μ.withDensity (f * g) := by rw [hfg, withDensity_one]
    _ = (μ.withDensity f).withDensity g := withDensity_mul _ hfm hgm
    _ = (ρ.withDensity f).withDensity g := by rw [hdamped]
    _ = ρ.withDensity (f * g) := (withDensity_mul _ hfm hgm).symm
    _ = ρ := by rw [hfg, withDensity_one]

/-- Local finiteness is a *consequence* of the transform converging, not a hypothesis: a causal
measure with `laplaceL μ s₀ < ∞` for some `s₀ > 0` is finite on every `[0,T]`. -/
theorem measure_Icc_ne_top_of_laplaceL_ne_top {μ : Measure ℝ} (hμ : IsCausal μ) {s₀ : ℝ}
    (hs₀ : 0 < s₀) (hfin : laplaceL μ s₀ ≠ ⊤) (T : ℝ) : μ (Icc 0 T) ≠ ⊤ := by
  have hle : μ (Icc 0 T) ≤ ENNReal.ofReal (Real.exp (s₀ * T)) * laplaceL μ s₀ := by
    rw [laplaceL, ← lintegral_const_mul _ (by fun_prop)]
    calc μ (Icc 0 T) = ∫⁻ _ in Icc 0 T, 1 ∂μ := by
          rw [lintegral_one, Measure.restrict_apply_univ]
      _ ≤ ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (s₀ * T)) *
            ENNReal.ofReal (Real.exp (-(s₀ * t))) ∂μ := by
          refine setLIntegral_mono' measurableSet_Icc fun t ht => ?_
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← ENNReal.ofReal_one]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [show (1 : ℝ) = Real.exp 0 by simp]
          exact Real.exp_le_exp.mpr (by nlinarith [ht.1, ht.2])
      _ ≤ ∫⁻ t, ENNReal.ofReal (Real.exp (s₀ * T)) *
            ENNReal.ofReal (Real.exp (-(s₀ * t))) ∂μ := setLIntegral_le_lintegral _ _
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hle

end Hemigroup
