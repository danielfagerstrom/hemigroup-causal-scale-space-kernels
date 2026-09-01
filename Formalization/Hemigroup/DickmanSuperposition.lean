/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the MIT license as described in the file LICENSES/MIT.txt.
Authors: Daniel Fagerström
-/
import Hemigroup.AdmissibleCone
import Hemigroup.Subordinator

/-!
# `lem:dickman-superposition`: every admissible exponent is drift plus Dickman rays

Blueprint: `lem:dickman-superposition` (7.14), the representation clause of `prop:extreme-rays`.

Two statements. The **ray**: the Dickman density `k = 1_{(0,τ)}` has exponent `Ein(τs)`, which is
the closed form `Examples.lean` recorded as absent — absent only in the sense that `Ein` is not
elementary, which is a fact about the function and not about the integral. The **superposition**:
every admissible `F` is `b₀s + ∫ Ein(τs) ρ(dτ)` for `ρ` the tail measure `-dk`.

## The layer cake, for the third time in this development

Both halves of chapter 9's Route B ran on Mathlib's `lintegral_comp_eq_lintegral_meas_lt_mul`, and
so does this. The pairing is the same and only the antiderivative changes: there `g(r) = se^{-sr}`
with antiderivative `1 - e^{-su}`, here `g(t) = (1-e^{-st})/t` with antiderivative `Ein(su)`. What
the identity delivers each time is the exchange
`∫ G(τ) ρ(dτ) = ∫₀^∞ g(t)·ρ((t,∞)) dt` with **no σ-finiteness hypothesis on `ρ`** — which matters
here, because the tail measure of a bounded `k` puts infinite mass at the origin and only the
restriction to `(0,∞)` is σ-finite.

## The tail measure is chapter 9's, restricted

`exists_tailMeasure` was built for `lem:potential-kernel` and produces `ν` with `ν(r,∞) = k(r)` a.e.
It is a pushforward of Lebesgue measure under a quantile transform, so it charges `{0}` with the
whole of `[k(0+),∞)` whenever `k` is bounded — the Dickman ray being the extreme case. Restricting
to `(0,∞)` removes that atom without touching any tail, and it is what makes `ρ` a measure *on*
`(0,∞)`, which is what the blueprint's `ρ ∈ M₊(0,∞)` asks for.
-/

namespace Hemigroup

open MeasureTheory Set Filter

open scoped ENNReal Topology

/-! ## The ray -/

/-- **`lem:dickman-superposition`(1)**: the Dickman ray of delay `τ` has exponent `Ein(τs)`.

The Lévy density is `1_{(0,τ)}`, so the jump integral is `∫₀^τ (1-e^{-st})\,dt/t`, and the
substitution `u = st` is `intervalIntegral_dilate_einIntegrand`. The only measure-theoretic step is
trading the lower integral for an ordinary one, which the bound `(1-e^{-st})/t ≤ s` licenses. -/
theorem dickmanExponent_exponent {τ : ℝ} (hτ : 0 < τ) {s : ℝ} (hs : 0 ≤ s) :
    (dickmanExponent τ).exponent s = ENNReal.ofReal (ein (τ * s)) := by
  have hnn : ∀ u : ℝ, 0 ≤ u → 0 ≤ (1 - Real.exp (-(s * u))) / u := fun u hu =>
    dilate_einIntegrand_nonneg hs hu
  -- the integrand vanishes past the cutoff, so the jump integral lives on `(0,τ)`
  have hdisj : Disjoint (Ioo (0 : ℝ) τ) (Ici τ) := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hx2⟩ hx3
    exact absurd (mem_Ici.mp hx3) (not_le.mpr hx2)
  have hsplit : levyJump (dickmanDensity τ) s
      = ∫⁻ t in Ioo (0 : ℝ) τ, ENNReal.ofReal ((1 - Real.exp (-(s * t))) / t) := by
    rw [levyJump, ← Ioo_union_Ici_eq_Ioi hτ,
      lintegral_union measurableSet_Ici hdisj]
    have hzero : (∫⁻ t in Ici τ,
        ENNReal.ofReal ((1 - Real.exp (-(s * t))) * dickmanDensity τ t / t)) = 0 := by
      refine setLIntegral_eq_zero measurableSet_Ici fun t ht => ?_
      rw [dickmanDensity_eq_zero_of_le (mem_Ici.mp ht), mul_zero, zero_div,
        ENNReal.ofReal_zero]
      rfl
    rw [hzero, add_zero]
    refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    rw [dickmanDensity, if_pos ⟨ht.1, ht.2⟩, mul_one]
  -- and there it is an ordinary integral
  have hint : IntegrableOn (fun t : ℝ => (1 - Real.exp (-(s * t))) / t) (Ioo (0 : ℝ) τ) := by
    have h := intervalIntegrable_dilate_einIntegrand hs hτ.le
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hτ.le] at h
    exact h.mono_set Ioo_subset_Ioc_self
  rw [SelfDecomposableExponent.exponent, levyExponentD, dickmanExponent, zero_mul,
    ENNReal.ofReal_zero, zero_add, hsplit,
    ← ofReal_integral_eq_lintegral_ofReal hint
      ((ae_restrict_iff' measurableSet_Ioo).mpr (.of_forall fun t ht => hnn t ht.1.le))]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hτ.le,
    intervalIntegral_dilate_einIntegrand, mul_comm]

/-! ## The superposition -/

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent)

/-- **The tail measure of `k`, carried by `(0,∞)`.**

`exists_tailMeasure` supplies a measure with tail `k`; restricting to `(0,∞)` removes the atom the
quantile transform leaves at the origin whenever `k` is bounded, and changes no tail. -/
theorem exists_tailMeasure_k :
    ∃ ρ : Measure ℝ, ρ (Iic 0) = 0 ∧
      ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), ρ (Ioi r) = ENNReal.ofReal (F.k r) := by
  obtain ⟨ν, -, htail⟩ := exists_tailMeasure F.k_antitone F.tendsto_k_atTop_nhds_zero
  refine ⟨ν.restrict (Ioi 0), ?_, ?_⟩
  · rw [Measure.restrict_apply measurableSet_Iic]
    convert measure_empty (μ := ν)
    ext t
    simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_empty_iff_false, iff_false, not_and, not_lt]
    exact fun h => h
  · filter_upwards [htail, self_mem_ae_restrict measurableSet_Ioi] with r hr hr0
    rw [Measure.restrict_apply measurableSet_Ioi,
      Ioi_inter_Ioi, max_eq_left (mem_Ioi.mp hr0).le, hr]

/-- **`lem:dickman-superposition`(2)**: `F(s) = b₀ s + ∫ Ein(τs) ρ(dτ)`.

Mathlib's layer cake with `g(t) = (1-e^{-st})/t`, whose antiderivative on `[0,τ]` is `Ein(sτ)`. It
needs no σ-finiteness, which is what lets the tail measure be used as it comes. -/
theorem exponent_eq_lintegral_ein {ρ : Measure ℝ} (hρ : ρ (Iic 0) = 0)
    (htail : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), ρ (Ioi r) = ENNReal.ofReal (F.k r))
    {s : ℝ} (hs : 0 ≤ s) :
    F.exponent s = ENNReal.ofReal (F.b₀ * s) + ∫⁻ τ, ENNReal.ofReal (ein (τ * s)) ∂ρ := by
  have hcausal : 0 ≤ᵐ[ρ] (id : ℝ → ℝ) := by
    rw [Filter.EventuallyLE, ae_iff]
    refine measure_mono_null (fun t ht => ?_) hρ
    simp only [Pi.zero_apply, id_eq, not_le, mem_setOf_eq] at ht
    exact mem_Iic.mpr ht.le
  have hlayer := lintegral_comp_eq_lintegral_meas_lt_mul (μ := ρ) (f := (id : ℝ → ℝ))
    (g := fun t : ℝ => (1 - Real.exp (-(s * t))) / t) hcausal aemeasurable_id
    (fun t ht => intervalIntegrable_dilate_einIntegrand hs ht.le)
    ((ae_restrict_iff' measurableSet_Ioi).mpr
      (.of_forall fun t ht => dilate_einIntegrand_nonneg hs (le_of_lt ht)))
  have hL : (∫⁻ τ, ENNReal.ofReal (ein (τ * s)) ∂ρ)
      = ∫⁻ τ, ENNReal.ofReal (∫ t in (0 : ℝ)..(id τ), (1 - Real.exp (-(s * t))) / t) ∂ρ :=
    lintegral_congr fun τ => by
      simp only [id_eq]
      rw [intervalIntegral_dilate_einIntegrand, mul_comm]
  rw [exponent, levyExponentD, hL, hlayer, levyJump]
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [htail, self_mem_ae_restrict measurableSet_Ioi] with t ht ht0
  have ht0' : (0 : ℝ) < t := ht0
  rw [show {a : ℝ | t < id a} = Ioi t from rfl, ht,
    ← ENNReal.ofReal_mul (F.k_nonneg t ht0)]
  congr 1
  ring

end SelfDecomposableExponent


/-- **`lem:dickman-superposition` (7.14).** The Dickman ray of delay `τ` has exponent `Ein(τs)`,
and every admissible exponent is drift plus a superposition of Dickman rays against the tail
measure `-dk`.

Stated existentially in the measure, as the skeleton stated it: what has to hold is that a measure
with tail `k` *exists*, not that it is the quantile transform of `Subordinator.lean` that supplies
one. -/
theorem dickman_superposition :
    (∀ τ : ℝ, 0 < τ → ∀ s : ℝ, 0 ≤ s →
        (dickmanExponent τ).exponent s = ENNReal.ofReal (ein (τ * s))) ∧
      (∀ F : SelfDecomposableExponent, ∃ ρ : Measure ℝ,
        ρ (Iic 0) = 0 ∧
        (∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ρ (Ioi t) = ENNReal.ofReal (F.k t)) ∧
        ∀ s : ℝ, 0 ≤ s →
          F.exponent s
            = ENNReal.ofReal (F.b₀ * s) + ∫⁻ τ, ENNReal.ofReal (ein (τ * s)) ∂ρ) :=
  ⟨fun _ hτ _ hs => dickmanExponent_exponent hτ hs,
   fun F => by
     obtain ⟨ρ, hρ, htail⟩ := F.exists_tailMeasure_k
     exact ⟨ρ, hρ, htail, fun _ hs => F.exponent_eq_lintegral_ein hρ htail hs⟩⟩

end Hemigroup
