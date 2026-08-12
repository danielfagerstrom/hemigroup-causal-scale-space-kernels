/-
Copyright (c) 2026 Daniel Fagerstrom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerstrom
-/
import Hemigroup.Subordinator

/-!
# The potential kernel, by Route B

Blueprint: `lem:potential-kernel` (Lemma 9.4) and `prop:sonine-pair-exists` (9.12).

`ell^(x)` is the measure with Laplace transform `1/phi_x`. The blueprint proves it exists by
Bernstein-Widder: `1/u` is completely monotone, `CM . BF` is contained in `CM` (ledger A2), and
the general-measure form of Bernstein-Widder (ledger A1) produces the measure. **That route is not
taken here**, because A1 is precisely the entry `DESIGN-formalization-strategy.md`'s
representation-first choice exists to keep off the critical path; taking it would falsify a claim
the article makes about its own trust base.

Route B **constructs** the measure instead, and never mentions complete monotonicity -- not even
as a consequence. `ell^(x)` is the subordinator's potential measure `U = int_0^infty mu_t dt`,
where `mu_t` is the law ledger A17 already supplies; its transform is
`int_0^infty e^(-t phi_x(s)) dt = 1/phi_x(s)` by Tonelli. **The trust boundary stays at two
entries**, and `#print axioms` on everything here gives A17 and nothing else.

## What the route cost, against what the work order said

Three things, and the work order predicted one of them.

* **The symbol's triple** (`exists_levyTriple_symbol`). Predicted, and the prediction named the
  wrong obstruction: see `Hemigroup/Subordinator.lean` for why `-dh` is not a Stieltjes measure in
  Mathlib's sense and what replaces it.
* **A measurable family** (`exists_subordinatorFamily`). *Not* predicted. A17 supplies `mu_t` for
  each `t` by choice, independently, so `int_0^infty mu_t dt` is not a measure at all without it.
  Getting it is where Route B's subordinator stops being a name and does work: the semigroup law
  and causality make `t |-> mu_t(-inf,r]` antitone, hence measurable, and Dynkin does the rest.
* **Nondegeneracy is needed later than expected.** `exists_levyTriple_symbol` was stated with it
  and does not use it; (ND) enters only at `symbol_pos`, where `1/phi_x` has to make sense.
-/

namespace Hemigroup

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent)

theorem exists_levyTriple_symbol {x : ℝ} (hx : 0 < x) :
    ∃ ν : Measure ℝ, IsCausal ν ∧ (∀ s, 0 ≤ s → levyExponent F.b₀ ν s ≠ ⊤) ∧
      ∀ s, 0 < s → ENNReal.ofReal (F.symbol x s) = levyExponent F.b₀ ν s := by
  -- The dilated density `h(u) = k(u/x)/x`: nonincreasing, nonnegative, vanishing at infinity.
  have hmono : AntitoneOn (fun u => F.k (u / x) / x) (Ioi 0) := by
    intro a ha b hb hab
    have h := antitoneOn_comp_div F.k_antitone hx ha hb hab
    dsimp only
    gcongr
  have hnn : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ F.k (u / x) / x := fun u hu =>
    div_nonneg (F.k_nonneg _ (mem_Ioi.mpr (div_pos (mem_Ioi.mp hu) hx))) hx.le
  have htend : Tendsto (fun u => F.k (u / x) / x) atTop (𝓝 0) := by
    have h1 : Tendsto (fun u : ℝ => u / x) atTop atTop :=
      Filter.Tendsto.atTop_div_const hx tendsto_id
    simpa using ((F.tendsto_k_atTop_nhds_zero.comp h1).div_const x)
  obtain ⟨ν, hνc, hνtail⟩ := exists_tailMeasure hmono htend
  -- `φ_x(s) = b₀ s + s ∫₀^∞ e^{-su} h(u) du`, from the derivative formula and the substitution.
  have hsym : ∀ s : ℝ, 0 < s → F.symbol x s
      = F.b₀ * s + s * ∫ u in Ioi (0 : ℝ), Real.exp (-(s * u)) * (F.k (u / x) / x) := by
    intro s hs
    rw [symbol, (F.hasDerivAt_toRealExponent (mul_pos hx hs)).deriv, F.integral_dilate_k hx s]
    ring
  -- The identity, on `(0,∞)`.
  have hkey : ∀ s : ℝ, 0 < s → ENNReal.ofReal (F.symbol x s) = levyExponent F.b₀ ν s := by
    intro s hs
    have hnonneg : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ Real.exp (-(s * r)) * (F.k (r / x) / x) :=
      fun r hr => by have := hnn r hr; positivity
    have hint0 : IntegrableOn
        (fun r => s * (Real.exp (-(s * r)) * (F.k (r / x) / x))) (Ioi 0) :=
      (F.integrableOn_dilate_k hx hs).const_mul s
    have hint : IntegrableOn
        (fun r => s * Real.exp (-(s * r)) * (F.k (r / x) / x)) (Ioi 0) :=
      hint0.congr_fun (fun r _ => by ring) measurableSet_Ioi
    have hIpos : (0 : ℝ) ≤ ∫ r in Ioi (0 : ℝ), Real.exp (-(s * r)) * (F.k (r / x) / x) :=
      integral_nonneg_of_ae ((ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall hnonneg))
    rw [levyExponent, lintegral_one_sub_exp_eq_tail hνc hs]
    have h1 : (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (s * Real.exp (-(s * r))) * ν (Ioi r))
        = ∫⁻ r in Ioi (0 : ℝ),
            ENNReal.ofReal (s * Real.exp (-(s * r)) * (F.k (r / x) / x)) := by
      refine lintegral_congr_ae ?_
      filter_upwards [hνtail] with r hr
      rw [hr, ← ENNReal.ofReal_mul (by positivity)]
    rw [h1, ← ofReal_integral_eq_lintegral_ofReal hint
        ((ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun r hr => by
          simpa only [Pi.zero_apply, mul_assoc] using mul_nonneg hs.le (hnonneg r hr))),
      show (∫ r in Ioi (0 : ℝ), s * Real.exp (-(s * r)) * (F.k (r / x) / x))
        = s * ∫ r in Ioi (0 : ℝ), Real.exp (-(s * r)) * (F.k (r / x) / x) by
        rw [← integral_const_mul]; exact integral_congr_ae (.of_forall fun r => by ring),
      ← ENNReal.ofReal_add (mul_nonneg F.b₀_nonneg hs.le) (mul_nonneg hs.le hIpos),
      hsym s hs]
  refine ⟨ν, hνc, fun s hs => ?_, hkey⟩
  rcases hs.eq_or_lt with rfl | hs'
  · simp [levyExponent]
  · rw [← hkey s hs']; exact ENNReal.ofReal_ne_top


/-- **Route B, step 2 — proved 2026-08-11.** The subordinator's laws, as a *measurable* family.

Everything but the triple: A17 applied to the scaled triple `(t b₀, tν)` at each `t ≥ 0` (the
scaling is `levyExponent_smul`), the family extended by `δ₀` below the origin, the semigroup law
`μ_{t+t'} = μ_t ∗ μ_{t'}` from the transform and `laplace_injective`, and then the measurability
that the work order omitted: `conv_Iic_le` makes `t ↦ μ_t(Iic r)` antitone, hence measurable, and
`measurable_of_antitone_measure_Iic` lifts that to every Borel set by Dynkin. -/
theorem exists_subordinatorFamily (hnd : F.Nondegenerate) {x : ℝ} (hx : 0 < x) :
    ∃ μ : ℝ → Measure ℝ, Measurable μ ∧ (∀ t, IsProbabilityMeasure (μ t)) ∧
      (∀ t, IsCausal (μ t)) ∧
      ∀ t, 0 ≤ t → ∀ s, 0 < s →
        laplaceL (μ t) s = ENNReal.ofReal (Real.exp (-(t * F.symbol x s))) := by
  classical
  obtain ⟨ν, hνc, hνfin, hνφ⟩ := F.exists_levyTriple_symbol hx
  -- A17 on the scaled triple `(t b₀, t ν)`, for each `t ≥ 0`.
  have key : ∀ t : ℝ, 0 ≤ t → ∃ m : Measure ℝ, IsProbabilityMeasure m ∧ IsCausal m ∧
      ∀ s, 0 ≤ s → laplace m s = Real.exp (-(t * F.symbol x s)) := by
    intro t ht
    have hscale : ∀ s, levyExponent (t * F.b₀) (ENNReal.ofReal t • ν) s
        = ENNReal.ofReal t * levyExponent F.b₀ ν s := fun s => levyExponent_smul ν ht s
    obtain ⟨m, hprob, hcaus, htr⟩ :=
      exists_isProbabilityMeasure_laplace_eq_exp_neg_levyExponent
        (mul_nonneg ht F.b₀_nonneg) (hνc.smul _)
        (fun s hs => by
          rw [hscale s]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hνfin s hs))
    refine ⟨m, hprob, hcaus, fun s hs => ?_⟩
    rw [htr s hs, hscale s]
    congr 2
    rcases hs.eq_or_lt with rfl | hs'
    · simp [symbol]
    · rw [← hνφ s hs', ← ENNReal.ofReal_mul ht,
        ENNReal.toReal_ofReal (mul_nonneg ht (F.symbol_pos hnd hx hs').le)]
  -- Choose the family, extended by `δ₀` below the origin.
  have hfam : ∃ μ : ℝ → Measure ℝ, (∀ t, IsProbabilityMeasure (μ t)) ∧ (∀ t, IsCausal (μ t)) ∧
      (∀ t, t < 0 → μ t = Measure.dirac 0) ∧
      ∀ t, 0 ≤ t → ∀ s, 0 ≤ s → laplace (μ t) s = Real.exp (-(t * F.symbol x s)) := by
    refine ⟨fun t => if ht : 0 ≤ t then (key t ht).choose else Measure.dirac 0, ?_, ?_, ?_, ?_⟩
    · intro t
      dsimp only
      by_cases ht : 0 ≤ t
      · rw [dif_pos ht]; exact (key t ht).choose_spec.1
      · rw [dif_neg ht]; infer_instance
    · intro t
      dsimp only
      by_cases ht : 0 ≤ t
      · rw [dif_pos ht]; exact (key t ht).choose_spec.2.1
      · rw [dif_neg ht]; exact isCausal_dirac le_rfl
    · intro t ht
      dsimp only
      rw [dif_neg (not_le.mpr ht)]
    · intro t ht s hs
      dsimp only
      rw [dif_pos ht]; exact (key t ht).choose_spec.2.2 s hs
  obtain ⟨μ, hprob, hcaus, hneg, htr⟩ := hfam
  haveI : ∀ t, IsProbabilityMeasure (μ t) := hprob
  -- `μ 0 = δ₀`, and the semigroup law.
  have hzero : μ 0 = Measure.dirac 0 := by
    refine laplace_injective (hcaus 0) (isCausal_dirac le_rfl) fun s hs => ?_
    rw [htr 0 le_rfl s hs, laplace, integral_dirac]
    simp
  have hsemi : ∀ t t', 0 ≤ t → 0 ≤ t' → μ (t + t') = μ t ∗ μ t' := by
    intro t t' ht ht'
    haveI : IsFiniteMeasure (μ t ∗ μ t') := by
      haveI : IsProbabilityMeasure (μ t ∗ μ t') := inferInstance
      infer_instance
    refine laplace_injective (hcaus (t + t')) ((hcaus t).conv (hcaus t')) fun s hs => ?_
    rw [laplace_conv, htr (t + t') (by linarith) s hs, htr t ht s hs, htr t' ht' s hs,
      ← Real.exp_add]
    ring_nf
  -- Antitone cumulative distributions, hence measurability.
  have hanti : ∀ r : ℝ, Antitone fun t => μ t (Iic r) := by
    intro r t₁ t₂ h12
    dsimp only
    have hstep : ∀ a b : ℝ, 0 ≤ a → a ≤ b → μ b (Iic r) ≤ μ a (Iic r) := by
      intro a b ha hab
      have hb : μ b = μ a ∗ μ (b - a) := by
        rw [← hsemi a (b - a) ha (by linarith)]; ring_nf
      rw [hb]
      exact conv_Iic_le (hcaus _) r
    rcases lt_or_ge t₁ 0 with h1 | h1
    · rcases lt_or_ge t₂ 0 with h2 | h2
      · rw [hneg t₁ h1, hneg t₂ h2]
      · calc μ t₂ (Iic r) ≤ μ 0 (Iic r) := hstep 0 t₂ le_rfl h2
          _ = μ t₁ (Iic r) := by rw [hzero, hneg t₁ h1]
    · exact hstep t₁ t₂ h1 h12
  refine ⟨μ, measurable_of_antitone_measure_Iic hprob hanti, hprob, hcaus, fun t ht s hs => ?_⟩
  rw [← htr t ht s hs.le, laplace_eq_toReal_laplaceL,
    ENNReal.ofReal_toReal (laplaceL_ne_top_of_causal (hcaus t) hs.le)]

/-- **`lem:potential-kernel`.** The potential kernel exists and is unique.

Route B's main argument, `sorry`-free: the mixture `∫₀^∞ μ_t dt` of the subordinator's laws is
causal because every `μ_t` is, its transform is `∫₀^∞ e^{-tφ_x(s)} dt = 1/φ_x(s)` by Tonelli,
local finiteness follows from convergence of that transform at a single point, and uniqueness is
Laplace injectivity for measures that are not finite. Only the two sub-lemmas above are open. -/
theorem existsUnique_potentialKernel (hnd : F.Nondegenerate) {x : ℝ} (hx : 0 < x) :
    ∃! ℓ : Measure ℝ, IsCausal ℓ ∧ (∀ T : ℝ, ℓ (Icc 0 T) ≠ ⊤) ∧
      ∀ s : ℝ, 0 < s → laplaceL ℓ s = ENNReal.ofReal (F.symbol x s)⁻¹ := by
  obtain ⟨μ, hmeas, hprob, hcaus, htrans⟩ := F.exists_subordinatorFamily hnd hx
  set ℓ := (volume.restrict (Ioi 0)).bind μ with hℓdef
  have hcausal : IsCausal ℓ := by
    have hz : ∀ t, μ t (Iio 0) = 0 := fun t => hcaus t
    rw [IsCausal, hℓdef, Measure.bind_apply measurableSet_Iio hmeas.aemeasurable]
    simp only [hz, lintegral_zero]
  have htr : ∀ s : ℝ, 0 < s → laplaceL ℓ s = ENNReal.ofReal (F.symbol x s)⁻¹ := by
    intro s hs
    have hφ : 0 < F.symbol x s := F.symbol_pos hnd hx hs
    rw [hℓdef, laplaceL, Measure.lintegral_bind hmeas.aemeasurable (by fun_prop)]
    have hcongr : ∀ t ∈ Ioi (0 : ℝ), (∫⁻ u, ENNReal.ofReal (Real.exp (-(s * u))) ∂(μ t))
        = ENNReal.ofReal (Real.exp (-(F.symbol x s * t))) := by
      intro t ht
      rw [show (∫⁻ u, ENNReal.ofReal (Real.exp (-(s * u))) ∂(μ t)) = laplaceL (μ t) s from rfl,
        htrans t (le_of_lt ht) s hs, mul_comm t (F.symbol x s)]
    rw [setLIntegral_congr_fun measurableSet_Ioi hcongr,
      show (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(F.symbol x s * t))))
        = laplaceL (volume.restrict (Ioi (0 : ℝ))) (F.symbol x s) from rfl,
      show volume.restrict (Ioi (0 : ℝ)) = volume.restrict (Ici (0 : ℝ)) from
        Measure.restrict_congr_set Ioi_ae_eq_Ici,
      laplaceL_volume_Ici hφ, one_div]
  have hfin : laplaceL ℓ 1 ≠ ⊤ := by
    rw [htr 1 zero_lt_one]; exact ENNReal.ofReal_ne_top
  refine ⟨ℓ, ⟨hcausal, fun T => measure_Icc_ne_top_of_laplaceL_ne_top hcausal zero_lt_one hfin T,
    htr⟩, ?_⟩
  rintro ρ ⟨hρcaus, -, hρtr⟩
  exact laplaceL_injective_of_ne_top hρcaus hcausal
    (by rw [hρtr 1 zero_lt_one]; exact ENNReal.ofReal_ne_top)
    fun s hs => by rw [hρtr s (by linarith), htr s (by linarith)]

/-- **`prop:sonine-pair-exists`**, the node split out in Phase 0: at the level of measures the
pair is unconditional. A collation of the three results above, and the reason it is worth
stating separately is that it needs no ledger entry, where the regularity clauses do. -/
theorem exists_sonine_pair (hnd : F.Nondegenerate) {x : ℝ} (hx : 0 < x) :
    ∃ ℓ : Measure ℝ, IsCausal ℓ ∧ (∀ T : ℝ, ℓ (Icc 0 T) ≠ ⊤) ∧
      ∃ _ : SFinite ℓ, (F.memoryKernel x ∗ ℓ).restrict (Ici 0) = volume.restrict (Ici 0) := by
  obtain ⟨ℓ, ⟨hcaus, hloc, htr⟩, -⟩ := F.existsUnique_potentialKernel hnd hx
  haveI : SigmaFinite ℓ := sigmaFinite_of_isCausal_of_measure_Icc_ne_top hcaus hloc
  exact ⟨ℓ, hcaus, hloc, inferInstance, F.sonine_conservation hnd hx ℓ hcaus htr⟩

end SelfDecomposableExponent

end Hemigroup
