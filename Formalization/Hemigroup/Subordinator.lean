/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Hemigroup.Sonine
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Machinery for the potential kernel (Route B)

Blueprint: machinery for `lem:potential-kernel` (Lemma 9.4) by Route B, which builds the potential
kernel as `U = ∫₀^∞ μ_t dt` rather than representing it through Bernstein–Widder. See
`Formalization/Skeleton/Chapter9.lean` for the decomposition this serves.

## Why this file exists

Route B's work order read step 3 as "`U := ∫₀^∞ μ_t dt` as a measure, and Tonelli for its
transform", as though forming `U` were bookkeeping. It is not. Ledger A17 supplies `μ_t` for each
`t` **by choice, independently**, so nothing connects the choices across `t`; `∫₀^∞ μ_t dt` is not
a measure at all, and `Measure.bind` does not typecheck without `Measurable (fun t => μ_t)`.

The first three lemmas are what closes that gap, and the middle one is where Route B's
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

The file also carries the two smaller pieces Route B's step 1 turned out to need:
`lintegral_one_sub_exp_eq_tail`, which is Mathlib's layer-cake formula specialised to the Lévy
integrand, and `tendsto_k_atTop_nhds_zero`, which is what makes `-dk` a *finite* tail at every
positive delay.

Nothing here mentions complete monotonicity, which is the point of Route B: the trust boundary
stays at two entries.
-/

namespace Hemigroup

open MeasureTheory Set Filter
open scoped ENNReal Topology

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

/-- **The layer-cake identity for the Lévy integrand.**

`∫ (1 - e^{-su}) dν = ∫₀^∞ s e^{-sr} ν(r,∞) dr`, for any causal `ν`. This is Mathlib's
`lintegral_comp_eq_lintegral_meas_lt_mul` at `f = id` and `g r = s e^{-sr}`, whose antiderivative
on `[0,u]` is `1 - e^{-su}`. -/
theorem lintegral_one_sub_exp_eq_tail {ν : Measure ℝ} (hν : IsCausal ν) {s : ℝ} (hs : 0 < s) :
    ∫⁻ u, ENNReal.ofReal (1 - Real.exp (-(s * u))) ∂ν
      = ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (s * Real.exp (-(s * r))) * ν (Ioi r) := by
  have hanti : ∀ u : ℝ, (∫ r in (0 : ℝ)..u, s * Real.exp (-(s * r)))
      = 1 - Real.exp (-(s * u)) := by
    intro u
    have hderiv : ∀ r : ℝ, HasDerivAt (fun r => -Real.exp (-(s * r)))
        (s * Real.exp (-(s * r))) r := by
      intro r
      have h1 : HasDerivAt (fun r : ℝ => -(s * r)) (-s) r := by
        simpa using (hasDerivAt_id r).const_mul (-s)
      have h2 : HasDerivAt (fun r : ℝ => Real.exp (-(s * r)))
          (Real.exp (-(s * r)) * (-s)) r := h1.exp
      have h3 : HasDerivAt (fun r : ℝ => -Real.exp (-(s * r)))
          (-(Real.exp (-(s * r)) * (-s))) r := h2.neg
      convert h3 using 1
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hderiv r)
      (by apply Continuous.intervalIntegrable; fun_prop)]
    simp only [mul_zero, neg_zero, Real.exp_zero]
    ring
  have hkey := lintegral_comp_eq_lintegral_meas_lt_mul (f := fun u : ℝ => u)
    (g := fun r => s * Real.exp (-(s * r))) ν hν.ae_nonneg aemeasurable_id
    (fun t _ => by apply Continuous.intervalIntegrable; fun_prop)
    (.of_forall fun r => by positivity)
  simp only [hanti] at hkey
  rw [hkey]
  exact lintegral_congr fun r => mul_comm _ _


/-- **A causal measure finite on every `[0,T]` is σ-finite**: the half-line is exhausted by the
`[0,n]` and everything below the origin is null.

The converse direction of `measure_Icc_ne_top_of_laplaceL_ne_top`, and what
`prop:sonine-pair-exists` needs: `thm:sonine-conservation` is stated for an `SFinite` measure,
because it convolves, and the potential kernel arrives from `lem:potential-kernel` carrying local
finiteness instead. -/
theorem sigmaFinite_of_isCausal_of_measure_Icc_ne_top {μ : Measure ℝ} (hμ : IsCausal μ)
    (h : ∀ T : ℝ, μ (Icc 0 T) ≠ ⊤) : SigmaFinite μ := by
  refine Measure.sigmaFinite_of_countable
    (S := insert (Iio 0) (range fun n : ℕ => Icc (0 : ℝ) n)) ?_ ?_ ?_
  · exact (countable_range _).insert _
  · rintro s (rfl | ⟨n, rfl⟩)
    · rw [hμ]; exact ENNReal.zero_lt_top
    · exact lt_top_iff_ne_top.mpr (h _)
  · refine eq_univ_of_forall fun r => ?_
    rcases lt_or_ge r 0 with hr | hr
    · exact ⟨Iio 0, mem_insert _ _, hr⟩
    · obtain ⟨n, hn⟩ := exists_nat_ge r
      exact ⟨Icc 0 n, mem_insert_of_mem _ ⟨n, rfl⟩, ⟨hr, hn⟩⟩

/-! ## The tail measure

The Lévy measure of the symbol is `-dh` for the nonincreasing dilate `h`. It is **not** a Stieltjes
measure in Mathlib's sense: a `StieltjesFunction` is `ℝ → ℝ`, so its measure is finite on every
bounded interval, and `h` is unbounded at the origin for the stable family. The quantile transform
handles that natively — push Lebesgue measure on `(0,∞)` forward under the generalised inverse
`y ↦ sup {u > 0 : h u > y}`, and the mass that piles up near the origin is simply the mass at large
`y`.

What comes out is a sandwich, `h(r+) ≤ ν(r,∞) ≤ h(r)`, and the two sides agree off the countably
many discontinuities of `h`. That countability is `Monotone.countable_not_continuousAt`, applied
not to `h` — which is only `AntitoneOn (Ioi 0)` — but to `t ↦ -h(eᵗ)`, which is monotone on all of
`ℝ`. Composing with `exp` is what turns a half-line hypothesis into a global one.
-/

section TailMeasure

/-- The generalised inverse of a nonincreasing `h`: `tailInv h y = sup {u > 0 : h u > y}`. -/
noncomputable def tailInv (h : ℝ → ℝ) (y : ℝ) : ℝ := sSup {u : ℝ | 0 < u ∧ y < h u}

variable {h : ℝ → ℝ}

theorem tailInv_nonneg (y : ℝ) : 0 ≤ tailInv h y := by
  rcases eq_empty_or_nonempty {u : ℝ | 0 < u ∧ y < h u} with he | ⟨u, hu⟩
  · rw [tailInv, he, Real.sSup_empty]
  · by_cases hbd : BddAbove {u : ℝ | 0 < u ∧ y < h u}
    · exact le_trans hu.1.le (le_csSup hbd hu)
    · rw [tailInv, Real.sSup_of_not_bddAbove hbd]

theorem bddAbove_tailSet (htend : Tendsto h atTop (𝓝 0)) {y : ℝ} (hy : 0 < y) :
    BddAbove {u : ℝ | 0 < u ∧ y < h u} := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp (htend.eventually_lt_const hy)
  refine ⟨M, fun u hu => ?_⟩
  by_contra hc
  exact absurd (hM u (le_of_lt (not_le.mp hc))) (not_lt.mpr hu.2.le)

/-- The upper half of the sandwich: above `r`, the inverse only sees values below `h r`. -/
theorem lt_of_lt_tailInv (hmono : AntitoneOn h (Ioi 0))
    {y r : ℝ} (hr : 0 < r) (hlt : r < tailInv h y) : y < h r := by
  have hne : {u : ℝ | 0 < u ∧ y < h u}.Nonempty := by
    rcases eq_empty_or_nonempty {u : ℝ | 0 < u ∧ y < h u} with he | hne
    · rw [tailInv, he, Real.sSup_empty] at hlt; linarith
    · exact hne
  obtain ⟨u, hu, hru⟩ := exists_lt_of_lt_csSup hne hlt
  exact lt_of_lt_of_le hu.2 (hmono (mem_Ioi.mpr hr) (mem_Ioi.mpr hu.1) hru.le)

/-- The lower half: any `y` below `h u` is mapped past every `r < u`. -/
theorem lt_tailInv_of_lt (htend : Tendsto h atTop (𝓝 0)) {y u r : ℝ} (hy : 0 < y) (hu : 0 < u)
    (hru : r < u) (hlt : y < h u) : r < tailInv h y :=
  lt_of_lt_of_le hru (le_csSup (bddAbove_tailSet htend hy) ⟨hu, hlt⟩)

theorem antitoneOn_tailInv (htend : Tendsto h atTop (𝓝 0)) :
    AntitoneOn (tailInv h) (Ioi 0) := by
  intro y₁ h₁ y₂ h₂ h12
  rcases eq_empty_or_nonempty {u : ℝ | 0 < u ∧ y₂ < h u} with he | hne
  · rw [tailInv, he, Real.sSup_empty]; exact tailInv_nonneg _
  · exact csSup_le_csSup (bddAbove_tailSet htend (mem_Ioi.mp h₁)) hne
      (fun u hu => ⟨hu.1, lt_of_le_of_lt h12 hu.2⟩)

/-- **The tail measure.** `ν = (Leb on `(0,∞)`) ∘ tailInv⁻¹` has `ν(r,∞) = h(r)` at every
continuity point of `h`, hence almost everywhere. -/
theorem exists_tailMeasure (hmono : AntitoneOn h (Ioi 0)) (htend : Tendsto h atTop (𝓝 0)) :
    ∃ ν : Measure ℝ, IsCausal ν ∧
      ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), ν (Ioi r) = ENNReal.ofReal (h r) := by
  have hmeas : AEMeasurable (tailInv h) (volume.restrict (Ioi (0 : ℝ))) :=
    aemeasurable_of_antitoneOn (antitoneOn_tailInv htend)
  refine ⟨(volume.restrict (Ioi (0 : ℝ))).map (tailInv h), ?_, ?_⟩
  · rw [IsCausal, Measure.map_apply_of_aemeasurable hmeas measurableSet_Iio]
    convert measure_empty (μ := volume.restrict (Ioi (0 : ℝ)))
    ext y
    simp only [mem_preimage, mem_Iio, mem_empty_iff_false, iff_false, not_lt]
    exact tailInv_nonneg y
  · -- the sandwich, at continuity points
    have hup : ∀ r : ℝ, 0 < r →
        ((volume.restrict (Ioi (0 : ℝ))).map (tailInv h)) (Ioi r) ≤ ENNReal.ofReal (h r) := by
      intro r hr
      rw [Measure.map_apply_of_aemeasurable hmeas measurableSet_Ioi,
        Measure.restrict_apply' measurableSet_Ioi]
      refine le_trans (measure_mono (fun y hy => ?_)) (le_of_eq (by
        rw [Real.volume_Ioo, sub_zero]))
      exact ⟨mem_Ioi.mp hy.2, lt_of_lt_tailInv hmono hr hy.1⟩
    have hlow : ∀ r u : ℝ, 0 < r → r < u →
        ENNReal.ofReal (h u) ≤ ((volume.restrict (Ioi (0 : ℝ))).map (tailInv h)) (Ioi r) := by
      intro r u hr hru
      rw [Measure.map_apply_of_aemeasurable hmeas measurableSet_Ioi,
        Measure.restrict_apply' measurableSet_Ioi]
      have hvol : volume (Ioo (0 : ℝ) (h u)) = ENNReal.ofReal (h u) := by
        rw [Real.volume_Ioo, sub_zero]
      rw [← hvol]
      refine measure_mono ?_
      rintro y ⟨hy0, hyu⟩
      exact ⟨lt_tailInv_of_lt htend hy0 (lt_trans hr hru) hru hyu, hy0⟩
    -- `h` is continuous off a countable set: transport to `t ↦ h (exp t)`, antitone on all of `ℝ`.
    have hcount : {r : ℝ | 0 < r ∧ ¬ ContinuousWithinAt h (Ioi r) r}.Countable := by
      have hH : Monotone (fun t : ℝ => -h (Real.exp t)) := by
        intro a b hab
        exact neg_le_neg (hmono (mem_Ioi.mpr (Real.exp_pos a)) (mem_Ioi.mpr (Real.exp_pos b))
          (Real.exp_le_exp.mpr hab))
      refine Countable.mono ?_ (hH.countable_not_continuousAt.image Real.exp)
      rintro r ⟨hr, hnc⟩
      refine ⟨Real.log r, fun hc => hnc ?_, Real.exp_log hr⟩
      -- `-h ∘ exp` continuous at `log r` gives `h` continuous at `r`.
      have hc' : ContinuousAt (fun t : ℝ => h (Real.exp t)) (Real.log r) := by
        simpa using hc.neg
      have hlog : ContinuousAt Real.log r := Real.continuousAt_log (ne_of_gt hr)
      refine (ContinuousAt.congr (hc'.comp hlog) ?_).continuousWithinAt
      filter_upwards [Ioi_mem_nhds hr] with y hy
      simp [Real.exp_log (mem_Ioi.mp hy)]
    have h0 : volume {r : ℝ | 0 < r ∧ ¬ ContinuousWithinAt h (Ioi r) r} = 0 :=
      hcount.measure_zero volume
    have hnull : (volume.restrict (Ioi (0 : ℝ)))
        {r : ℝ | 0 < r ∧ ¬ ContinuousWithinAt h (Ioi r) r} = 0 := by
      rw [Measure.restrict_apply₀' measurableSet_Ioi.nullMeasurableSet]
      exact measure_mono_null inter_subset_left h0
    have hae : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))),
        r ∉ {r : ℝ | 0 < r ∧ ¬ ContinuousWithinAt h (Ioi r) r} := by
      rw [ae_iff]
      simpa using hnull
    filter_upwards [ae_restrict_mem measurableSet_Ioi, hae] with r hr hcont
    have hrp : (0 : ℝ) < r := mem_Ioi.mp hr
    have hcr : ContinuousWithinAt h (Ioi r) r := by
      by_contra hc
      exact hcont ⟨hrp, hc⟩
    refine le_antisymm (hup r hrp) ?_
    have hlim : Tendsto (fun u => ENNReal.ofReal (h u)) (𝓝[>] r) (𝓝 (ENNReal.ofReal (h r))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp hcr
    refine le_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact hlow r u hrp (mem_Ioi.mp hu)

end TailMeasure

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent)

/-- **`k` vanishes at infinity.**

Forced, not assumed: `k` is nonincreasing and nonnegative, and `∫₁^∞ k(t)/t dt < ∞`, so a
positive limit would make that integral diverge like the harmonic one. Route B needs it because
the tail measure `-dk` must be *finite* on `(r,∞)` for every `r > 0`, which is exactly
`k(r) < ∞` together with `k(∞) = 0`. -/
theorem tendsto_k_atTop_nhds_zero : Tendsto F.k atTop (𝓝 0) := by
  refine tendsto_order.mpr ⟨fun a ha => ?_, fun a ha => ?_⟩
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact lt_of_lt_of_le ha (F.k_nonneg t (mem_Ioi.mpr ht))
  · by_contra hcon
    rw [Filter.not_eventually] at hcon
    -- `k` never drops below `a`, by antitonicity and the frequent failures.
    have hall : ∀ u : ℝ, 0 < u → a ≤ F.k u := by
      intro u hu
      obtain ⟨x, hxk, hxu⟩ := (hcon.and_eventually (eventually_ge_atTop u)).exists
      exact le_trans (not_lt.mp hxk)
        (F.k_antitone (mem_Ioi.mpr hu) (mem_Ioi.mpr (lt_of_lt_of_le hu hxu)) hxu)
    -- then `k t / t` dominates `a / t`, which is not integrable at infinity.
    refine not_integrableOn_Ioi_inv (a := 1) ?_
    refine (F.integrableOn_k_div.const_mul a⁻¹).mono' (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : (1 : ℝ) < t := mem_Ioi.mp ht
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht1
    have hk : a ≤ F.k t := hall t ht0
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ t⁻¹), inv_eq_one_div,
      div_le_iff₀ ht0,
      show a⁻¹ * (F.k t / t) * t = a⁻¹ * F.k t from by field_simp]
    calc (1 : ℝ) = a⁻¹ * a := by field_simp
      _ ≤ a⁻¹ * F.k t := mul_le_mul_of_nonneg_left hk (inv_pos.mpr ha).le


end SelfDecomposableExponent

end Hemigroup
