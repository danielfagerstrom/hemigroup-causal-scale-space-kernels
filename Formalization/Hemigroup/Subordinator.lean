/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.Sonine

/-!
# The subordinator's laws as a measurable family

Blueprint: machinery for `lem:potential-kernel` (Lemma 9.4) by Route B, which builds the potential
kernel as `U = ∫₀^∞ μ_t dt` rather than representing it through Bernstein–Widder. See
`Formalization/Skeleton/Chapter9.lean` for the decomposition this serves.

## Why this file exists

Route B's work order read step 3 as "`U := ∫₀^∞ μ_t dt` as a measure, and Tonelli for its
transform", as though forming `U` were bookkeeping. It is not. Ledger A17 supplies `μ_t` for each
`t` **by choice, independently**, so nothing connects the choices across `t`; `∫₀^∞ μ_t dt` is not
a measure at all, and `Measure.bind` does not typecheck without `Measurable (fun t => μ_t)`.

The three lemmas here are what closes that gap, and the middle one is where Route B's
*subordinator* stops being a name and does work:

* `levyExponent_smul` — scaling a Lévy triple scales its exponent, so A17 applies at every `t`;
* `conv_Iic_le` — convolving with a causal probability measure can only move mass to the right,
  so it can only *decrease* the cumulative distribution. This is the increasing paths of the
  subordinator, stated at the level of measures;
* `measurable_of_antitone_measure_Iic` — a family of probability measures on `ℝ` with antitone
  cumulative distributions is measurable, by Dynkin from the π-system `{Iic r}`.

Together: the semigroup law `μ_{t+t'} = μ_t ∗ μ_{t'}` makes `t ↦ μ_t(Iic r)` antitone, antitone
functions are measurable, and Dynkin lifts that from the generating π-system to every Borel set.
So the increasing paths, which Route B's prose treats as intuition, are exactly what makes the
potential measure *exist*.

Nothing here mentions complete monotonicity, which is the point of Route B: the trust boundary
stays at two entries.
-/

namespace Hemigroup

open MeasureTheory Set
open scoped ENNReal

/-- Scaling a Lévy triple scales its exponent: `levyExponent (t b₀) (t ν) = t · levyExponent b₀ ν`.

What lets A17 be applied at every `t ≥ 0` from a single triple. -/
theorem levyExponent_smul {b₀ : ℝ} (ν : Measure ℝ) {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    levyExponent (t * b₀) (ENNReal.ofReal t • ν) s = ENNReal.ofReal t * levyExponent b₀ ν s := by
  rw [levyExponent, levyExponent, lintegral_smul_measure, mul_add, ← ENNReal.ofReal_mul ht,
    mul_assoc, smul_eq_mul]

/-- Scaling a causal measure keeps it causal. -/
theorem IsCausal.smul {ν : Measure ℝ} (hν : IsCausal ν) (c : ℝ≥0∞) : IsCausal (c • ν) := by
  rw [IsCausal, Measure.smul_apply, hν, smul_eq_mul, mul_zero]

/-- **Convolving with a causal probability measure can only decrease the cumulative
distribution**: `(α ∗ β)(-∞, r] ≤ α(-∞, r]` when `β` is carried by `[0,∞)`.

The increasing paths of a subordinator, at the level of measures — mass can only move right. Same
decomposition of the preimage as `IsCausal.conv`, with `Iic r ×ˢ univ` in place of the causal
half-plane. -/
theorem conv_Iic_le {α β : Measure ℝ} [SFinite α] [SFinite β] [IsProbabilityMeasure β]
    (hβ : IsCausal β) (r : ℝ) : (α ∗ β) (Iic r) ≤ α (Iic r) := by
  rw [Measure.conv, Measure.map_apply (by fun_prop) measurableSet_Iic]
  have hsub : (fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Iic r ⊆ (Iic r ×ˢ univ) ∪ (univ ×ˢ Iio 0) := by
    rintro ⟨u, v⟩ h
    simp only [mem_preimage, mem_Iic] at h
    rcases lt_or_ge v 0 with hv | hv
    · exact Or.inr (by simp [hv])
    · exact Or.inl (by simp only [mem_prod, mem_Iic, mem_univ, and_true]; linarith)
  calc (α.prod β) ((fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Iic r)
      ≤ (α.prod β) ((Iic r ×ˢ univ) ∪ (univ ×ˢ Iio 0)) := measure_mono hsub
    _ ≤ (α.prod β) (Iic r ×ˢ univ) + (α.prod β) (univ ×ˢ Iio 0) := measure_union_le _ _
    _ = α (Iic r) := by
        rw [Measure.prod_prod, Measure.prod_prod, hβ, mul_zero, add_zero, measure_univ, mul_one]

/-- **A family of probability measures on `ℝ` with antitone cumulative distributions is
measurable** — the clause `Measure.bind` needs, from the only structure the subordinator's laws
have in common.

`{Iic r}` is a π-system generating the Borel sets, an antitone function is measurable, and
Dynkin (`Measurable.measure_of_isPiSystem`) carries measurability from the π-system to every
Borel set. Finiteness is what makes the collection a λ-system, which is why this is stated for
probability measures and not for arbitrary ones. -/
theorem measurable_of_antitone_measure_Iic {μ : ℝ → Measure ℝ}
    (hp : ∀ t, IsProbabilityMeasure (μ t))
    (h : ∀ r : ℝ, Antitone fun t => μ t (Iic r)) : Measurable μ := by
  haveI : ∀ t, IsFiniteMeasure (μ t) := fun t => haveI := hp t; inferInstance
  have hgen : (inferInstance : MeasurableSpace ℝ)
      = MeasurableSpace.generateFrom (range (Iic : ℝ → Set ℝ)) := by
    rw [BorelSpace.measurable_eq (α := ℝ), borel_eq_generateFrom_Iic ℝ]
  refine Measurable.measure_of_isPiSystem hgen isPiSystem_Iic ?_ ?_
  · rintro _ ⟨r, rfl⟩
    exact (h r).measurable
  · haveI := hp
    simp only [measure_univ]
    exact measurable_const

end Hemigroup
