/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Hemigroup.Subordinator

/-!
# `prop:pair-regularity`(2): the memory kernel is CM iff `k` is, iff `F'` is Stieltjes

Blueprint: `blueprint/src/parts/09-memory-kernels.tex`, node `prop:pair-regularity`.

`hasCMDensity_iff` states clause (2)'s **two equivalences** in the representation idiom of
`Hemigroup/MemoryKernel.lean` (`HasCMDensity`, `HasCMRep`, `HasStieltjesRep`), and proves them
**off the trust boundary**: `#print axioms` gives Lean core. The node stays `[A]` on ledger A9,
because of clause (1) (SSV Thm. 11.3), which is not stated here; the second assertion of clause
(2), about `ℓ^{(x)}` and `F ∈ CBF`, is not stated either, and it is the only place A9's two
structural inputs (SSV Thms. 7.3 and 6.2) enter.

## The route checked

1. **Dilation** (`hasCMRep_dilate`). The CM class is dilation-stable by transporting the
   representing measure, `σ ↦ x⁻¹ · map (· / x) σ`, with no analysis. It gives the `(⇐)` of
   the first equivalence, `memoryKernel`'s drift atom dropping out on `Ioi 0`, and, run with
   `x⁻¹`, its own inverse (`hasCMRep_of_dilate`).
2. **The a.e.-to-pointwise upgrade** (`eqOn_of_ae_of_antitoneOn`). `withDensity` sees a density
   only up to a null set, and `HasCMRep` is pointwise. An antitone function agreeing a.e. on the
   half-line with a continuous one agrees everywhere there: squeeze it between agreement points
   on either side. **This is where `F.k_antitone` is load-bearing**: without it the `(⇒)` of the
   first equivalence would be false in this idiom.
3. **The junk values** (`hasCMRep_of_ae`, `exists_integrable_rep`). Neither `HasCMRep` nor
   `HasStieltjesRep` constrains its measure beyond causality, so the Bochner integral may be a
   junk `0`. Integrability of `τ ↦ e^{-τt}` is an up-set in `t`; if it fails at some `t₀`, the
   represented function vanishes on `(0,t₀]`, hence — antitone and nonnegative — everywhere, and
   `σ = 0` serves. Otherwise the integral is continuous on `(0,∞)` and step 2 applies. The case
   split is taken once, inside `hasCMRep_of_ae`, which both `(⇒)` directions then call.
4. **The second equivalence** goes through one measure, `cmMeasure a b σ = b δ₀ + (a + ∫
   e^{-τt} σ(dτ)) dt`, whose transform is `b + a/s + ∫ (s+τ)⁻¹ σ(dτ)` by Tonelli
   (`laplaceL_cmMeasure`). Forward, `κ^{(1)} = cmMeasure 0 b₀ σ`, and its transform is `F'` by
   `laplaceL_memoryKernel`. Backward, `laplaceL_injective_of_ne_top` makes `κ^{(1)} =
   cmMeasure a b σ`, and restricting to `Ioi 0` gives `k = ∫ e^{-τt} d(a δ₀ + σ)` a.e., which
   step 3 upgrades.

**What the route found.** The blueprint's backward direction first proves `a = 0` (an `a/s` term
is an additive constant in `k`, which `∫₁^∞ k(t)t⁻¹dt < ∞` forbids). The checked proof never
needs it: the `a/s` term is absorbed as an atom `a δ₀` in the representing measure of `k`, which
`HasCMRep` allows, being stated for a causal measure on `[0,∞)`. (`a = 0` is still true, since
`k(t) → 0`; nothing here uses it.) And `SFinite σ`, which Tonelli wants and neither predicate
supplies, comes free: once the relevant transform is finite at one point,
`measure_Icc_ne_top_of_laplaceL_ne_top` and `sigmaFinite_of_isCausal_of_measure_Icc_ne_top` give
σ-finiteness, and when it is infinite the junk case of step 3 applies.
-/

namespace Hemigroup

open MeasureTheory Set Filter
open scoped ENNReal Topology

open SelfDecomposableExponent (HasCMRep HasCMDensity HasStieltjesRep)

/-! ### The tools: what the pointwise idiom of `HasCMRep` costs

Steps 2 and 3 of the route above, stated once for an arbitrary causal `σ`: integrability of
`τ ↦ e^{-τt}` is an up-set in `t` (`integrable_exp_of_le`), the representing integral is
continuous where it converges (`continuousOn_integral_exp`), an antitone function agreeing a.e.
with a continuous one agrees everywhere (`eqOn_of_ae_of_antitoneOn`), and together they turn an
a.e. representation of an antitone function into a pointwise one (`hasCMRep_of_ae`), the junk
case included.
-/

/-- On a causal measure, integrability of `τ ↦ e^{-τt}` passes upward in `t`. -/
theorem integrable_exp_of_le {σ : Measure ℝ} (hσ : IsCausal σ) {t t' : ℝ} (htt' : t ≤ t')
    (h : Integrable (fun τ => Real.exp (-(τ * t))) σ) :
    Integrable (fun τ => Real.exp (-(τ * t'))) σ := by
  refine h.mono (by fun_prop : Continuous fun τ : ℝ => Real.exp (-(τ * t'))).aestronglyMeasurable
    ?_
  filter_upwards [hσ.ae_nonneg] with τ hτ
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- Where the representing integral converges on the whole half-line, it is continuous there:
dominated convergence against `e^{-τt/2}`. -/
theorem continuousOn_integral_exp {σ : Measure ℝ} (hσ : IsCausal σ)
    (h : ∀ t, 0 < t → Integrable (fun τ => Real.exp (-(τ * t))) σ) :
    ContinuousOn (fun t => ∫ τ, Real.exp (-(τ * t)) ∂σ) (Ioi 0) := by
  intro t ht
  have ht0 : (0 : ℝ) < t := ht
  have hc := continuousAt_of_dominated (μ := σ) (F := fun t' τ => Real.exp (-(τ * t')))
    (x₀ := t) (bound := fun τ => Real.exp (-(τ * (t / 2))))
    (Eventually.of_forall fun t' =>
      (by fun_prop : Continuous fun τ : ℝ => Real.exp (-(τ * t'))).aestronglyMeasurable)
    (by
      filter_upwards [Ioi_mem_nhds (show t / 2 < t by linarith)] with t' ht'
      filter_upwards [hσ.ae_nonneg] with τ hτ
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr (by nlinarith [mem_Ioi.mp ht']))
    (h _ (by linarith))
    (Eventually.of_forall fun τ =>
      (by fun_prop : Continuous fun t' : ℝ => Real.exp (-(τ * t'))).continuousAt)
  exact hc.continuousWithinAt

/-- A property holding a.e. on `s` holds somewhere in every open interval inside `s`. -/
theorem exists_mem_Ioo_of_ae {s : Set ℝ} {p : ℝ → Prop} (h : ∀ᵐ t ∂volume.restrict s, p t)
    {a b : ℝ} (hab : a < b) (hsub : Ioo a b ⊆ s) : ∃ t ∈ Ioo a b, p t := by
  by_contra hne
  push Not at hne
  have h0 : volume.restrict s (Ioo a b) = 0 :=
    measure_mono_null (fun t ht => hne t ht) (ae_iff.mp h)
  rw [Measure.restrict_apply measurableSet_Ioo, inter_eq_left.mpr hsub, Real.volume_Ioo,
    ENNReal.ofReal_eq_zero] at h0
  linarith

/-- **Step 2, the a.e.-to-pointwise upgrade.** An antitone function agreeing a.e. on the
half-line with a continuous one agrees with it everywhere there: squeeze `f t` between agreement
points on either side of `t`. -/
theorem eqOn_of_ae_of_antitoneOn {f g : ℝ → ℝ} (hf : AntitoneOn f (Ioi 0))
    (hg : ContinuousOn g (Ioi 0)) (h : ∀ᵐ t ∂volume.restrict (Ioi 0), f t = g t) :
    ∀ t, 0 < t → f t = g t := by
  intro t ht
  have hgt : ContinuousAt g t := hg.continuousAt (Ioi_mem_nhds ht)
  refine le_antisymm ?_ ?_
  · by_contra hlt
    push Not at hlt
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hgt.tendsto.eventually_lt_const hlt)
    obtain ⟨s, hs, hfs⟩ := exists_mem_Ioo_of_ae h
      (show max (t - ε) (t / 2) < t from max_lt (by linarith) (by linarith))
      (fun s hs => lt_of_lt_of_le (by linarith : (0 : ℝ) < t / 2)
        ((le_max_right _ _).trans hs.1.le))
    have hs0 : (0 : ℝ) < s := lt_of_lt_of_le (by linarith : (0 : ℝ) < t / 2)
      ((le_max_right _ _).trans hs.1.le)
    have hdist : dist s t < ε := by
      rw [Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith [le_max_left (t - ε) (t / 2), hs.1, hs.2]
    have := hball hdist
    have := hf hs0 ht hs.2.le
    linarith
  · by_contra hlt
    push Not at hlt
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hgt.tendsto.eventually_const_lt hlt)
    obtain ⟨s, hs, hfs⟩ := exists_mem_Ioo_of_ae h (show t < t + ε by linarith)
      (fun s hs => lt_trans ht hs.1)
    have hdist : dist s t < ε := by
      rw [Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith [hs.1, hs.2]
    have := hball hdist
    have := hf ht (lt_trans ht hs.1) hs.1.le
    linarith

/-- **Steps 2 and 3 together.** An antitone nonnegative function represented a.e. on the
half-line by a causal `σ` is represented everywhere there, by `σ` or by `0`. The junk case is
the one where `τ ↦ e^{-τt₀}` is not integrable at some `t₀`: then the Bochner integral is `0`
on `(0,t₀]`, so `f` vanishes at points arbitrarily close to the origin, and being antitone and
nonnegative it vanishes on the whole half-line. -/
theorem hasCMRep_of_ae {f : ℝ → ℝ} (hf : AntitoneOn f (Ioi 0))
    (hf0 : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ f t) {σ : Measure ℝ} (hσ : IsCausal σ)
    (h : ∀ᵐ t ∂volume.restrict (Ioi 0), f t = ∫ τ, Real.exp (-(τ * t)) ∂σ) : HasCMRep f := by
  by_cases hint : ∀ t, 0 < t → Integrable (fun τ => Real.exp (-(τ * t))) σ
  · exact ⟨σ, hσ, eqOn_of_ae_of_antitoneOn hf (continuousOn_integral_exp hσ hint) h⟩
  · push Not at hint
    obtain ⟨t₀, ht₀, hni⟩ := hint
    refine ⟨0, by simp [IsCausal], fun u hu => ?_⟩
    rw [integral_zero_measure]
    obtain ⟨t, ht, hft⟩ := exists_mem_Ioo_of_ae h (lt_min ht₀ hu) Ioo_subset_Ioi_self
    have hjunk : ∫ τ, Real.exp (-(τ * t)) ∂σ = 0 :=
      integral_undef fun hi => hni (integrable_exp_of_le hσ (ht.2.le.trans (min_le_left _ _)) hi)
    refine le_antisymm ?_ (hf0 u hu)
    calc f u ≤ f t := hf ht.1 hu (ht.2.le.trans (min_le_right _ _))
      _ = 0 := by rw [hft, hjunk]

/-- The representing integral is a.e. measurable on the half-line, whatever `σ` is: it is the
real part of an antitone `ℝ≥0∞`-valued function. -/
theorem aemeasurable_integral_exp {σ : Measure ℝ} (hσ : IsCausal σ) :
    AEMeasurable (fun t => ∫ τ, Real.exp (-(τ * t)) ∂σ) (volume.restrict (Ioi 0)) := by
  have hG : AntitoneOn (fun t => ∫⁻ τ, ENNReal.ofReal (Real.exp (-(τ * t))) ∂σ) (Ioi 0) := by
    intro t ht t' _ htt'
    refine lintegral_mono_ae ?_
    filter_upwards [hσ.ae_nonneg] with τ hτ
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by nlinarith))
  refine ((aemeasurable_restrict_of_antitoneOn measurableSet_Ioi hG).ennreal_toReal).congr ?_
  exact Eventually.of_forall fun t => (integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun τ => (Real.exp_pos _).le)
    (by fun_prop : Continuous fun τ : ℝ => Real.exp (-(τ * t))).aestronglyMeasurable).symm

/-- A representation of an antitone nonnegative `k` can be taken with `τ ↦ e^{-τt}` integrable
for every `t > 0`: otherwise `k ≡ 0` on the half-line and `σ = 0` serves. -/
theorem exists_integrable_rep {k : ℝ → ℝ} (hk : AntitoneOn k (Ioi 0))
    (hk0 : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ k t) (h : HasCMRep k) :
    ∃ σ : Measure ℝ, IsCausal σ ∧ (∀ t, 0 < t → Integrable (fun τ => Real.exp (-(τ * t))) σ) ∧
      ∀ t, 0 < t → k t = ∫ τ, Real.exp (-(τ * t)) ∂σ := by
  obtain ⟨σ, hσ, hk'⟩ := h
  by_cases hint : ∀ t, 0 < t → Integrable (fun τ => Real.exp (-(τ * t))) σ
  · exact ⟨σ, hσ, hint, hk'⟩
  · push Not at hint
    obtain ⟨t₀, ht₀, hni⟩ := hint
    refine ⟨0, by simp [IsCausal], fun t _ => integrable_zero_measure, fun u hu => ?_⟩
    rw [integral_zero_measure]
    have hv : 0 < min u t₀ := lt_min hu ht₀
    have hkv : k (min u t₀) = 0 := by
      rw [hk' _ hv]
      exact integral_undef fun hi => hni (integrable_exp_of_le hσ (min_le_right _ _) hi)
    exact le_antisymm (hkv ▸ hk hv hu (min_le_left _ _)) (hk0 u hu)

/-! ### Step 1: the dilation -/

/-- The CM class is dilation-stable by transporting the representing measure,
`σ ↦ x⁻¹ · map (· / x) σ`, with no analysis. -/
theorem hasCMRep_dilate {g : ℝ → ℝ} {x : ℝ} (hx : 0 < x) (h : HasCMRep g) :
    HasCMRep fun t => g (t / x) / x := by
  obtain ⟨σ, hσ, hk⟩ := h
  refine ⟨ENNReal.ofReal x⁻¹ • σ.map (fun τ => τ / x), ?_, ?_⟩
  · have hpre : (fun τ : ℝ => τ / x) ⁻¹' Iio 0 = Iio 0 := by
      ext τ
      simp only [mem_preimage, mem_Iio]
      exact ⟨fun h => by
        by_contra h'
        exact absurd h (not_lt.mpr (div_nonneg (not_lt.mp h') hx.le)),
        fun h => div_neg_of_neg_of_pos h hx⟩
    change (ENNReal.ofReal x⁻¹ • σ.map (fun τ => τ / x)) (Iio 0) = 0
    rw [Measure.smul_apply, Measure.map_apply (by fun_prop : Measurable fun τ : ℝ => τ / x)
      measurableSet_Iio,
      hpre, hσ, smul_zero]
  · intro t ht
    change g (t / x) / x = _
    rw [integral_smul_measure,
      integral_map (by fun_prop : Measurable fun τ : ℝ => τ / x).aemeasurable
        (by fun_prop : Continuous fun τ : ℝ => Real.exp (-(τ * t))).aestronglyMeasurable,
      hk (t / x) (div_pos ht hx), ENNReal.toReal_ofReal (inv_nonneg.mpr hx.le), smul_eq_mul,
      div_eq_inv_mul]
    have hτ : ∀ τ : ℝ, τ / x * t = τ * (t / x) := fun τ => by ring
    simp only [hτ]

/-- The dilation undone: dilating by `x⁻¹` returns `g`. -/
theorem hasCMRep_of_dilate {g : ℝ → ℝ} {x : ℝ} (hx : 0 < x)
    (h : HasCMRep fun t => g (t / x) / x) : HasCMRep g := by
  have h' := hasCMRep_dilate (inv_pos.mpr hx) h
  convert h' using 1
  funext t
  rw [div_inv_eq_mul, div_mul_cancel₀ _ hx.ne', div_inv_eq_mul, mul_div_assoc, div_self hx.ne',
    mul_one]

/-- A drift atom at the origin plus a density on the half-line: restricting to `Ioi 0` keeps
the density alone. -/
theorem restrict_Ioi_dirac_add_withDensity (c : ℝ≥0∞) (d : ℝ → ℝ≥0∞) :
    (c • Measure.dirac (0 : ℝ) + (volume.restrict (Ioi 0)).withDensity d).restrict (Ioi 0)
      = (volume.restrict (Ioi 0)).withDensity d := by
  rw [Measure.restrict_add, Measure.restrict_smul,
    Measure.restrict_eq_zero.mpr (show Measure.dirac (0 : ℝ) (Ioi 0) = 0 by
      rw [Measure.dirac_apply' _ measurableSet_Ioi]; simp), smul_zero, zero_add,
    restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_self]

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent)

theorem restrict_memoryKernel (x : ℝ) :
    (F.memoryKernel x).restrict (Ioi 0)
      = (volume.restrict (Ioi 0)).withDensity fun t => ENNReal.ofReal (F.k (t / x) / x) :=
  restrict_Ioi_dirac_add_withDensity _ _

/-- **Step 1 of `prop:pair-regularity`(2)**: the `(⇐)` of the first equivalence. The drift atom
drops out on `Ioi 0`. -/
theorem hasCMDensity_memoryKernel_of_hasCMRep {x : ℝ} (hx : 0 < x) (h : HasCMRep F.k) :
    HasCMDensity (F.memoryKernel x) :=
  ⟨fun t => F.k (t / x) / x, hasCMRep_dilate hx h, restrict_memoryKernel F x⟩

/-! ### The `(⇒)` of the first equivalence -/

theorem antitoneOn_dilate {x : ℝ} (hx : 0 < x) :
    AntitoneOn (fun t => F.k (t / x) / x) (Ioi 0) := fun _ ha _ hb hab =>
  div_le_div_of_nonneg_right (antitoneOn_comp_div F.k_antitone hx ha hb hab) hx.le

/-- **The `(⇒)` of the first equivalence.** Equality of the two `withDensity` measures gives the
representation only a.e.; `hasCMRep_of_ae` upgrades it, and `F.k_antitone` is what it uses. -/
theorem hasCMRep_of_hasCMDensity_memoryKernel {x : ℝ} (hx : 0 < x)
    (h : HasCMDensity (F.memoryKernel x)) : HasCMRep F.k := by
  obtain ⟨m, ⟨σ, hσ, hm⟩, hμ⟩ := h
  rw [restrict_memoryKernel F x] at hμ
  have hm' : (volume.restrict (Ioi 0)).withDensity (fun t => ENNReal.ofReal (m t))
      = (volume.restrict (Ioi 0)).withDensity
          (fun t => ENNReal.ofReal (∫ τ, Real.exp (-(τ * t)) ∂σ)) :=
    withDensity_congr_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [hm t ht])
  rw [hm', withDensity_eq_iff_of_sigmaFinite
    (((aemeasurable_of_antitoneOn (antitoneOn_comp_div F.k_antitone hx)).div_const
      x).ennreal_ofReal)
    (aemeasurable_integral_exp hσ).ennreal_ofReal] at hμ
  refine hasCMRep_of_dilate hx (hasCMRep_of_ae (antitoneOn_dilate F hx)
    (fun t ht => div_nonneg (F.k_nonneg _ (div_pos ht hx)) hx.le) hσ ?_)
  filter_upwards [hμ, ae_restrict_mem measurableSet_Ioi] with t ht htpos
  exact (ENNReal.ofReal_eq_ofReal_iff (div_nonneg (F.k_nonneg _ (div_pos htpos hx)) hx.le)
    (integral_nonneg fun τ => (Real.exp_pos _).le)).mp ht

end SelfDecomposableExponent

/-! ### The second equivalence: step 4

Both directions go through one measure, `b δ₀ + (a + ∫ e^{-τt} σ(dτ)) dt`, whose transform is
`b + a/s + ∫ (s+τ)⁻¹ σ(dτ)` by Tonelli (`laplaceL_cmMeasure`). Forward, `κ^{(1)}` *is* that
measure with `a = 0`; backward, `laplaceL_injective_of_ne_top` makes it so. The backward
direction never needs `a = 0`: an `a/s` term is absorbed as an atom `a δ₀` in the representing
measure of `k`, which `HasCMRep` allows.
-/

/-- `b δ₀ + (a + ∫ e^{-τt} σ(dτ)) dt` on the half-line, in `ℝ≥0∞` form so that no integrability
is needed to write it. -/
noncomputable def cmMeasure (a b : ℝ) (σ : Measure ℝ) : Measure ℝ :=
  ENNReal.ofReal b • Measure.dirac 0 + (volume.restrict (Ioi 0)).withDensity
    fun t => ENNReal.ofReal a + ∫⁻ τ, ENNReal.ofReal (Real.exp (-(τ * t))) ∂σ

theorem isCausal_cmMeasure (a b : ℝ) (σ : Measure ℝ) : IsCausal (cmMeasure a b σ) := by
  rw [IsCausal, cmMeasure, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply' _ measurableSet_Iio, withDensity_apply _ measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi, Ioo_self]
  simp

theorem lintegral_exp_Ioi {s : ℝ} (hs : 0 < s) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(s * t))) = ENNReal.ofReal (1 / s) := by
  rw [Measure.restrict_congr_set Ioi_ae_eq_Ici]
  exact laplaceL_volume_Ici hs

theorem measurable_lintegral_exp (σ : Measure ℝ) [SFinite σ] :
    Measurable fun t => ∫⁻ τ, ENNReal.ofReal (Real.exp (-(τ * t))) ∂σ :=
  Measurable.lintegral_prod_right'
    (f := fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-(p.2 * p.1)))) (by fun_prop)

/-- The transform of `cmMeasure`, by Tonelli. -/
theorem laplaceL_cmMeasure {a b : ℝ} {σ : Measure ℝ} [SFinite σ] (hσ : IsCausal σ)
    (ha : 0 ≤ a) {s : ℝ} (hs : 0 < s) :
    laplaceL (cmMeasure a b σ) s = ENNReal.ofReal b + ENNReal.ofReal (a / s)
      + ∫⁻ τ, ENNReal.ofReal ((s + τ)⁻¹) ∂σ := by
  rw [laplaceL, cmMeasure, lintegral_add_measure, lintegral_smul_measure, lintegral_dirac,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_const.add (measurable_lintegral_exp σ))
      (by fun_prop)]
  simp only [Pi.mul_apply, add_mul, mul_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one,
    smul_eq_mul, mul_one]
  rw [lintegral_add_left (measurable_const.mul (by fun_prop)), lintegral_const_mul _ (by fun_prop),
    lintegral_exp_Ioi hs, ← ENNReal.ofReal_mul ha, mul_one_div, add_assoc]
  congr 2
  calc ∫⁻ t in Ioi 0, (∫⁻ τ, ENNReal.ofReal (Real.exp (-(τ * t))) ∂σ)
          * ENNReal.ofReal (Real.exp (-(s * t)))
      = ∫⁻ t in Ioi 0, ∫⁻ τ, ENNReal.ofReal (Real.exp (-(τ * t)))
          * ENNReal.ofReal (Real.exp (-(s * t))) ∂σ := by
        refine lintegral_congr fun t => ?_
        rw [lintegral_mul_const _ (by fun_prop)]
    _ = ∫⁻ τ, (∫⁻ t in Ioi 0, ENNReal.ofReal (Real.exp (-(τ * t)))
          * ENNReal.ofReal (Real.exp (-(s * t)))) ∂σ :=
        lintegral_lintegral_swap ((by fun_prop : Measurable fun p : ℝ × ℝ =>
          ENNReal.ofReal (Real.exp (-(p.2 * p.1)))
            * ENNReal.ofReal (Real.exp (-(s * p.1)))).aemeasurable)
    _ = ∫⁻ τ, ENNReal.ofReal ((s + τ)⁻¹) ∂σ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hσ.ae_nonneg] with τ hτ
        have hpt : ∀ t : ℝ, ENNReal.ofReal (Real.exp (-(τ * t)))
            * ENNReal.ofReal (Real.exp (-(s * t))) = ENNReal.ofReal (Real.exp (-((s + τ) * t))) :=
          fun t => by
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
            congr 2
            ring
        simp_rw [hpt]
        rw [lintegral_exp_Ioi (by linarith), one_div]

/-- `(s+τ)⁻¹`-integrals at two points `s, s' > 0` are comparable, so finiteness at one point is
finiteness at all. -/
theorem lintegral_inv_add_le {σ : Measure ℝ} (hσ : IsCausal σ) {s s' : ℝ} (hs : 0 < s)
    (hs' : 0 < s') :
    ∫⁻ τ, ENNReal.ofReal ((s' + τ)⁻¹) ∂σ
      ≤ ENNReal.ofReal (max 1 (s / s')) * ∫⁻ τ, ENNReal.ofReal ((s + τ)⁻¹) ∂σ := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [hσ.ae_nonneg] with τ hτ
  rw [← ENNReal.ofReal_mul (le_trans zero_le_one (le_max_left _ _))]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← div_eq_mul_inv, le_div_iff₀ (by linarith), inv_mul_le_iff₀ (by linarith)]
  have h1 := le_max_left 1 (s / s')
  have h2 := le_max_right 1 (s / s')
  have h3 : s' * (s / s') = s := mul_div_cancel₀ s hs'.ne'
  nlinarith

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent)

/-- **The `(⇒)` of the second equivalence.** `κ^{(1)}` is `cmMeasure 0 b₀ σ`, so its transform,
which is `F'`, is `b₀ + ∫ (s+τ)⁻¹ σ(dτ)`. -/
theorem hasStieltjesRep_of_hasCMRep (h : HasCMRep F.k) :
    HasStieltjesRep (deriv F.toRealExponent) := by
  obtain ⟨σ, hσ, hint, hk⟩ := exists_integrable_rep F.k_antitone F.k_nonneg h
  have h1 : laplaceL σ 1 ≠ ⊤ := by
    have := (hint 1 one_pos).lintegral_lt_top
    simp only [mul_one] at this
    simp only [laplaceL, one_mul]
    exact this.ne
  haveI : SigmaFinite σ := sigmaFinite_of_isCausal_of_measure_Icc_ne_top hσ
    (measure_Icc_ne_top_of_laplaceL_ne_top hσ one_pos h1)
  have hmk : F.memoryKernel 1 = cmMeasure 0 F.b₀ σ := by
    rw [SelfDecomposableExponent.memoryKernel, cmMeasure]
    congr 1
    refine withDensity_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [div_one, div_one, hk t ht, ENNReal.ofReal_zero, zero_add,
      ofReal_integral_eq_lintegral_ofReal (hint t ht)
        (Eventually.of_forall fun τ => (Real.exp_pos _).le)]
  refine ⟨0, F.b₀, σ, le_rfl, F.b₀_nonneg, hσ, fun s hs => ?_⟩
  have hL := F.laplaceL_memoryKernel one_pos hs
  rw [hmk, laplaceL_cmMeasure hσ le_rfl hs, zero_div, ENNReal.ofReal_zero, add_zero,
    SelfDecomposableExponent.symbol, one_mul, mul_div_cancel_left₀ _ hs.ne'] at hL
  have hD0 : 0 ≤ deriv F.toRealExponent s := by
    rw [(F.hasDerivAt_toRealExponent hs).deriv]
    exact add_nonneg F.b₀_nonneg (setIntegral_nonneg measurableSet_Ioi fun t ht =>
      mul_nonneg (Real.exp_pos _).le (F.k_nonneg t ht))
  have hJ : ∫⁻ τ, ENNReal.ofReal ((s + τ)⁻¹) ∂σ ≠ ⊤ := by
    intro hJ
    rw [hJ, add_top] at hL
    exact ENNReal.ofReal_ne_top hL.symm
  rw [zero_div, zero_add, integral_eq_lintegral_of_nonneg_ae
      (by filter_upwards [hσ.ae_nonneg] with τ hτ; exact inv_nonneg.mpr (by linarith))
      (by fun_prop : Measurable fun τ : ℝ => (s + τ)⁻¹).aestronglyMeasurable,
    ← ENNReal.toReal_ofReal hD0, ← hL, ENNReal.toReal_add ENNReal.ofReal_ne_top hJ,
    ENNReal.toReal_ofReal F.b₀_nonneg]

/-- **The `(⇐)` of the second equivalence.** Laplace uniqueness makes `κ^{(1)}` equal to
`cmMeasure a b σ`; on the half-line that gives `k = ∫ e^{-τt} d(a δ₀ + σ)` a.e., and
`hasCMRep_of_ae` upgrades it. When the `(s+τ)⁻¹`-integral diverges the Bochner integral in the
hypothesis is junk `0`, and `σ = 0` serves instead. -/
theorem hasCMRep_of_hasStieltjesRep (h : HasStieltjesRep (deriv F.toRealExponent)) :
    HasCMRep F.k := by
  obtain ⟨a, b, σ₀, ha, hb, hσ₀, hD₀⟩ := h
  -- normalise: the `(s+τ)⁻¹`-integral finite everywhere, or `σ₀` replaced by `0`
  have hconv : ∀ s, 0 < s → ∫ τ, (s + τ)⁻¹ ∂σ₀
      = (∫⁻ τ, ENNReal.ofReal ((s + τ)⁻¹) ∂σ₀).toReal := fun s hs =>
    integral_eq_lintegral_of_nonneg_ae
      (by filter_upwards [hσ₀.ae_nonneg] with τ hτ; exact inv_nonneg.mpr (by linarith))
      (by fun_prop : Measurable fun τ : ℝ => (s + τ)⁻¹).aestronglyMeasurable
  obtain ⟨σ, hσ, hJ, hD⟩ : ∃ σ : Measure ℝ, IsCausal σ ∧
      (∀ s, 0 < s → ∫⁻ τ, ENNReal.ofReal ((s + τ)⁻¹) ∂σ ≠ ⊤) ∧
      ∀ s, 0 < s → deriv F.toRealExponent s
        = a / s + b + (∫⁻ τ, ENNReal.ofReal ((s + τ)⁻¹) ∂σ).toReal := by
    by_cases h1 : ∫⁻ τ, ENNReal.ofReal ((1 + τ)⁻¹) ∂σ₀ = ⊤
    · refine ⟨0, by simp [IsCausal], by simp, fun s hs => ?_⟩
      have htop : ∫⁻ τ, ENNReal.ofReal ((s + τ)⁻¹) ∂σ₀ = ⊤ := by
        by_contra hne
        exact (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hne)
          (top_unique (h1 ▸ lintegral_inv_add_le hσ₀ hs one_pos))
      rw [hD₀ s hs, hconv s hs, htop]
      simp
    · exact ⟨σ₀, hσ₀, fun s hs => ne_top_of_le_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h1) (lintegral_inv_add_le hσ₀ one_pos hs),
        fun s hs => by rw [hD₀ s hs, hconv s hs]⟩
  have h1 : laplaceL σ 1 ≠ ⊤ := by
    refine ne_top_of_le_ne_top (hJ 1 one_pos) (lintegral_mono_ae ?_)
    filter_upwards [hσ.ae_nonneg] with τ hτ
    refine ENNReal.ofReal_le_ofReal ?_
    rw [one_mul, Real.exp_neg]
    exact inv_anti₀ (by linarith) (by linarith [Real.add_one_le_exp τ])
  haveI : SigmaFinite σ := sigmaFinite_of_isCausal_of_measure_Icc_ne_top hσ
    (measure_Icc_ne_top_of_laplaceL_ne_top hσ one_pos h1)
  have hmk : F.memoryKernel 1 = cmMeasure a b σ := by
    refine laplaceL_injective_of_ne_top F.isCausal_memoryKernel (isCausal_cmMeasure a b σ)
      (F.laplaceL_memoryKernel_ne_top one_pos one_pos) fun s hs => ?_
    have hs0 : 0 < s := one_pos.trans_le hs
    rw [F.laplaceL_memoryKernel one_pos hs0, laplaceL_cmMeasure hσ ha hs0,
      SelfDecomposableExponent.symbol, one_mul, mul_div_cancel_left₀ _ hs0.ne', hD s hs0,
      ENNReal.ofReal_add (by positivity) ENNReal.toReal_nonneg,
      ENNReal.ofReal_add (by positivity) hb, ENNReal.ofReal_toReal (hJ s hs0),
      add_comm (ENNReal.ofReal (a / s))]
  have hres := congrArg (fun μ : Measure ℝ => μ.restrict (Ioi 0)) hmk
  rw [restrict_memoryKernel F 1, cmMeasure, restrict_Ioi_dirac_add_withDensity,
    withDensity_eq_iff_of_sigmaFinite
      (((aemeasurable_of_antitoneOn (antitoneOn_comp_div F.k_antitone one_pos)).div_const
        1).ennreal_ofReal)
      (measurable_const.add (measurable_lintegral_exp σ)).aemeasurable] at hres
  -- the representing measure of `k` is `a δ₀ + σ`
  have hσ' : IsCausal (ENNReal.ofReal a • Measure.dirac 0 + σ) := by
    rw [IsCausal, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ measurableSet_Iio,
      hσ]
    simp
  refine hasCMRep_of_ae F.k_antitone F.k_nonneg hσ' ?_
  filter_upwards [hres, ae_restrict_mem measurableSet_Ioi] with t ht htpos
  simp only [div_one] at ht
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun τ => (Real.exp_pos _).le)
      (by fun_prop : Continuous fun τ : ℝ => Real.exp (-(τ * t))).aestronglyMeasurable,
    lintegral_add_measure, lintegral_smul_measure, lintegral_dirac, zero_mul, neg_zero,
    Real.exp_zero, ENNReal.ofReal_one, smul_eq_mul, mul_one, ← ht,
    ENNReal.toReal_ofReal (F.k_nonneg t htpos)]

/-- **`prop:pair-regularity`(2).** `κ^{(x)}` has a completely monotone density iff `k` does,
iff `F'` is Stieltjes. -/
theorem hasCMDensity_iff {x : ℝ} (hx : 0 < x) :
    (HasCMDensity (F.memoryKernel x) ↔ HasCMRep F.k) ∧
      (HasCMRep F.k ↔ HasStieltjesRep (deriv F.toRealExponent)) :=
  ⟨⟨hasCMRep_of_hasCMDensity_memoryKernel F hx, hasCMDensity_memoryKernel_of_hasCMRep F hx⟩,
    ⟨hasStieltjesRep_of_hasCMRep F, hasCMRep_of_hasStieltjesRep F⟩⟩

end SelfDecomposableExponent

end Hemigroup
