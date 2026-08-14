/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.DelayCore
import Hemigroup.Subordinator

/-!
# `def:phillips-generator`: the per-scale generator in Phillips form

Blueprint: `def:phillips-generator` (Definition 10.2). For `f ∈ 𝒟`,

  `φ_x(∂_t) f = b₀ f' + ∫₀^∞ (f - T_r f) ν_x(dr) = b₀ f' + x⁻¹ ∫₀^∞ (f - T_{xr} f) ν₁(dr)`,

with `ν₁` the Lévy tail measure `-dk` and `ν_x` its dilate. The lemma about it,
`lem:generator-properties` (10.3), is stated in `Skeleton/Chapter10.lean`; **this file carries the
definition and the facts about it that are proved**.

## The `X₀`-valued Bochner integral needs nothing new

`PLAN-chapters-8-12.md` had recorded the vector-valued integral as the expensive part of this
chapter. It is not: `X = L¹(ℝ)` is a complete normed real space, `transL1 r` is a continuous
linear map on it, and `r ↦ transL1 r f` is continuous (`continuous_transL1`, chapter 4), so the
integrand is strongly measurable and `MeasureTheory.integral` applies as written. The definition is
therefore *total* — Bochner's junk value where the integral diverges — and clause (1) of 10.3 is
what says it means something on `𝒟`.

Note the contrast with `lem:delay-core`, where the blueprint named a Bochner integral the
obligation did not need. Here the integral is in the *statement* and not merely in a proof, so it
has to be built; and building it costs nothing.

## `ν₁` is a parameter, not a construction

`HasLevyTail F ν` is the specification — `ν` causal with `ν((r,∞)) = k(r)` almost everywhere — and
every statement of chapter 10 quantifies over a `ν` meeting it. That is the discipline
`sonine_conservation` set, of stating a result against anything meeting the specification "so that
it does not wait on the existence half"; `exists_hasLevyTail` supplies one, from chapter 9's
quantile transform.

**Almost everywhere, and not everywhere.** The blueprint says "with `k` taken right-continuous and
`k(∞) = 0`, so that `ν₁((r,∞)) = k(r)`". A `k` that is only `AntitoneOn (Ioi 0)` has no
right-continuous representative this development can name, and `exists_tailMeasure` accordingly
delivers the tail identity at the continuity points of `k` — almost every `r`. That is exactly
enough, because every use of the tail below sits under an integral in `r`. The normalisation is a
convenience of the prose, and the same accounting was already made for the potential kernel.
-/

namespace Hemigroup

open MeasureTheory Set Filter

open scoped ENNReal Topology

/-! ## The dilated tail measure -/

/-- **`ν_x`**: `x⁻¹` times the pushforward of `ν₁` under `r ↦ xr`.

Written as a scaled pushforward rather than through a tail function, because that is the form the
change of variables consumes — see `phillipsGenerator_eq_smul_integral`, which is the blueprint's
own second display. -/
noncomputable def dilatedTail (ν : Measure ℝ) (x : ℝ) : Measure ℝ :=
  ENNReal.ofReal x⁻¹ • ν.map fun r => x * r

/-- The tail of `ν_x` in terms of `ν`'s: `ν_x((r,∞)) = ν((r/x,∞))/x`.

Unconditional on `ν` — pure measure algebra, with no tail hypothesis. Composed with
`HasLevyTail`'s a.e. identity this is the blueprint's `ν_x((r,∞)) = k(r/x)/x`, and splitting it
that way keeps the two halves of that "i.e." apart: one is a computation, the other inherits an
`ae` qualifier. -/
theorem dilatedTail_Ioi {x : ℝ} (hx : 0 < x) (ν : Measure ℝ) (r : ℝ) :
    dilatedTail ν x (Ioi r) = ENNReal.ofReal x⁻¹ * ν (Ioi (r / x)) := by
  have hpre : (fun s : ℝ => x * s) ⁻¹' Ioi r = Ioi (r / x) := by
    ext y
    simp only [mem_preimage, mem_Ioi, div_lt_iff₀ hx]
    rw [mul_comm]
  rw [dilatedTail, Measure.smul_apply, Measure.map_apply (by fun_prop) measurableSet_Ioi, hpre,
    smul_eq_mul]

/-- The integrand of the Phillips form is continuous in the delay, hence strongly measurable
against any measure. This is the whole of what the vector-valued integral needs. -/
theorem continuous_sub_transL1 (A : X) : Continuous fun r : ℝ => A - transL1 r A :=
  continuous_const.sub (continuous_transL1 A)

/-- `ν_x` is causal when `ν` is: the dilation `r ↦ xr` fixes the half-line. -/
theorem isCausal_dilatedTail {x : ℝ} (hx : 0 < x) {ν : Measure ℝ} (hν : IsCausal ν) :
    IsCausal (dilatedTail ν x) := by
  have hpre : (fun s : ℝ => x * s) ⁻¹' Iio 0 = Iio 0 := by
    ext y
    simp only [mem_preimage, mem_Iio]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  rw [IsCausal, dilatedTail, Measure.smul_apply,
    Measure.map_apply (by fun_prop) measurableSet_Iio, hpre, hν, smul_zero]

/-- **The change of variables**, once: an integral against `ν_x` is `x⁻¹` times the integral of the
dilated integrand against `ν`.

Everything the chapter says about `ν_x` factors through this — the definition's own second display
(`phillipsGenerator_eq_smul_integral`) and the bound of `lem:generator-properties`(1) alike. -/
theorem integral_dilatedTail {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : ℝ}
    (hx : 0 < x) (ν : Measure ℝ) {f : ℝ → E}
    (hf : AEStronglyMeasurable f (ν.map fun r => x * r)) :
    ∫ r, f r ∂(dilatedTail ν x) = x⁻¹ • ∫ r, f (x * r) ∂ν := by
  rw [dilatedTail, integral_smul_measure, integral_map (by fun_prop) hf,
    ENNReal.toReal_ofReal (by positivity)]

/-- Integrability against `ν_x`, likewise, is integrability of the dilated integrand against `ν`.
-/
theorem integrable_dilatedTail_iff {E : Type*} [NormedAddCommGroup E] {x : ℝ} (hx : 0 < x)
    (ν : Measure ℝ) {f : ℝ → E} (hf : AEStronglyMeasurable f (ν.map fun r => x * r)) :
    Integrable f (dilatedTail ν x) ↔ Integrable (fun r => f (x * r)) ν := by
  rw [dilatedTail, integrable_smul_measure (by simp [hx]) ENNReal.ofReal_ne_top,
    integrable_map_measure hf (by fun_prop)]
  rfl

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent)

/-! ## The specification of `ν₁` -/

/-- **`ν₁` is the Lévy tail measure of `F`**: causal, with `ν((r,∞)) = k(r)` for almost every
`r > 0`.

See the module docstring for why the tail identity is `ae` and why this is a specification rather
than a construction. -/
def HasLevyTail (ν : Measure ℝ) : Prop :=
  IsCausal ν ∧ ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), ν (Ioi r) = ENNReal.ofReal (F.k r)

/-- The specification is met — chapter 9's quantile transform, which was built for
`lem:potential-kernel` precisely because `StieltjesFunction` does not apply to a Lévy tail. -/
theorem exists_hasLevyTail : ∃ ν : Measure ℝ, F.HasLevyTail ν := by
  obtain ⟨ν, hcaus, htail⟩ := exists_tailMeasure F.k_antitone F.tendsto_k_atTop_nhds_zero
  exact ⟨ν, hcaus, htail⟩

/-! ## The generator -/

/-- **`φ_x(∂_t) f = b₀ f' + ∫₀^∞ (f - T_r f) ν_x(dr)`**, the per-scale generator in Phillips form.

Takes the pair `(A, B)` rather than `A` alone: `𝒟` is modelled by `HasCoreDerivL1 A B`, which
names the derivative, and an `L¹` class has no derivative to read off. Every statement about the
generator carries that hypothesis, and none of them is about a `B` the hypothesis does not pin —
`HasCoreDerivL1 A B` determines `B` up to `L¹` equality. -/
noncomputable def phillipsGenerator (ν : Measure ℝ) (x : ℝ) (A B : X) : X :=
  F.b₀ • B + ∫ r, (A - transL1 r A) ∂(dilatedTail ν x)

/-- **The blueprint's second display**: the dilation moved off the measure and onto the delay,
`φ_x(∂_t) f = b₀ f' + x⁻¹ ∫₀^∞ (f - T_{xr} f) ν₁(dr)`.

A change of variables and nothing else, and it is the form every estimate below uses, because it
puts the `x`-dependence in the integrand where dominated convergence can see it — which is how
10.3(4) reads continuity in `x` off a bound that does not involve `x`. -/
theorem phillipsGenerator_eq_smul_integral {x : ℝ} (hx : 0 < x) (ν : Measure ℝ) (A B : X) :
    F.phillipsGenerator ν x A B = F.b₀ • B + x⁻¹ • ∫ r, (A - transL1 (x * r) A) ∂ν := by
  rw [phillipsGenerator, integral_dilatedTail hx ν (continuous_sub_transL1 A).aestronglyMeasurable]

/-! ## `lem:generator-properties`(1): the integral converges, with the two-sided bound

The clause runs on one convergence fact about `ν₁` and one estimate about `T_r`, and neither is
new: `integrable_min_one_id` below is a layer cake against `∫₀¹k < ∞`, and the estimate is
`norm_transL1_sub_le`, proved for `lem:delay-core`. What the clause adds is the observation that
`min(2‖f‖₁, r‖f'‖₁) ≤ max(2‖f‖₁, ‖f'‖₁)·(1 ∧ r)`, which is where the two ends of `ν₁` are being
handled at once and why only `1 ∧ r` needs a name.
-/

/-- **`∫₀^∞ (1 ∧ r) ν₁(dr) < ∞`**, the convergence the whole of clause (1) reduces to.

The blueprint reaches it "from `∫₀¹ k < ∞` and `k(1) < ∞` by integration by parts". It is **one
layer cake** and the second hypothesis is unused:

  `∫ (1 ∧ r) ν(dr) = ∫₀^∞ ν{r : u < 1 ∧ r} du = ∫₀¹ ν((u,∞)) du = ∫₀¹ k(u) du`,

the middle step because `1 ∧ r > u` is unsatisfiable for `u ≥ 1` and is `r > u` below it. Fifth
appearance of the layer cake in this article, and the fourth time it has replaced a classical
integration by parts. The tail identity is needed only under an integral in `u`, which is why
`HasLevyTail`'s `ae` qualifier costs nothing. -/
theorem integrable_min_one_id {ν : Measure ℝ} (hν : F.HasLevyTail ν) :
    Integrable (fun r : ℝ => min 1 r) ν := by
  obtain ⟨hcaus, htail⟩ := hν
  have hnn : ∀ᵐ r ∂ν, 0 ≤ min 1 r := by
    filter_upwards [hcaus.ae_nonneg] with r hr
    exact le_min zero_le_one hr
  refine ⟨(continuous_const.min continuous_id).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have henorm : ∀ᵐ r ∂ν, ‖min 1 r‖ₑ = ENNReal.ofReal (min 1 r) := by
    filter_upwards [hnn] with r hr
    rw [Real.enorm_eq_ofReal hr]
  rw [lintegral_congr_ae henorm,
    lintegral_eq_lintegral_meas_lt ν hnn (continuous_const.min continuous_id).aemeasurable,
    ← Ioo_union_Ici_eq_Ioi (zero_lt_one : (0 : ℝ) < 1),
    lintegral_union measurableSet_Ici
      (Set.disjoint_left.mpr fun a ha hb => absurd (mem_Ici.mp hb) (not_le.mpr ha.2))]
  -- above `1` the superlevel set is empty; below it, it is `(u,∞)`.
  have hhigh : (∫⁻ u in Ici (1 : ℝ), ν {r : ℝ | u < min 1 r}) = 0 := by
    rw [setLIntegral_congr_fun measurableSet_Ici fun u hu => ?_, lintegral_zero]
    have : {r : ℝ | u < min 1 r} = ∅ := by
      ext r
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_lt]
      exact le_trans (min_le_left 1 r) (mem_Ici.mp hu)
    rw [this, measure_empty]
  have hlow : (∫⁻ u in Ioo (0 : ℝ) 1, ν {r : ℝ | u < min 1 r})
      = ∫⁻ u in Ioo (0 : ℝ) 1, ν (Ioi u) := by
    refine setLIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
    congr 1
    ext r
    simp only [mem_setOf_eq, mem_Ioi, lt_min_iff]
    exact and_iff_right hu.2
  rw [hhigh, hlow, add_zero]
  -- and the tail is `k`, whose integral over `(0,1]` is finite because `ne_top` says so.
  have htail' : ∀ᵐ u ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      ν (Ioi u) = ENNReal.ofReal (F.k u) :=
    ae_mono (Measure.restrict_mono Ioo_subset_Ioi_self le_rfl) htail
  rw [lintegral_congr_ae htail']
  exact lt_of_le_of_lt (lintegral_mono_set Ioo_subset_Ioc_self)
    (lt_top_iff_ne_top.mpr F.lintegral_ofReal_k_Ioc_ne_top)

/-- The dominating function of clause (1), against `ν₁` after the change of variables:
`min(c, xr·d) ≤ max(c, xd)·(1 ∧ r)` on the half-line, so one convergence fact covers every core
element and every scale. -/
theorem integrable_min_const_mul {ν : Measure ℝ} (hν : F.HasLevyTail ν) {c d : ℝ} (hc : 0 ≤ c)
    (hd : 0 ≤ d) : Integrable (fun r : ℝ => min c (d * r)) ν := by
  have hcont : Continuous fun r : ℝ => min c (d * r) := by fun_prop
  refine Integrable.mono' ((F.integrable_min_one_id hν).const_mul (max c d))
    hcont.aestronglyMeasurable ?_
  filter_upwards [hν.1.ae_nonneg] with r hr
  have hmin : 0 ≤ min c (d * r) := le_min hc (mul_nonneg hd hr)
  rw [Real.norm_eq_abs, abs_of_nonneg hmin]
  rcases le_total r 1 with h1 | h1
  · calc min c (d * r) ≤ d * r := min_le_right _ _
      _ ≤ max c d * min 1 r := by
          rw [min_eq_right h1]
          exact mul_le_mul_of_nonneg_right (le_max_right c d) hr
  · calc min c (d * r) ≤ c := min_le_left _ _
      _ = c * 1 := (mul_one c).symm
      _ ≤ max c d * min 1 r := by
          rw [min_eq_left h1]
          exact mul_le_mul_of_nonneg_right (le_max_left c d) zero_le_one

/-- **`lem:generator-properties`(1), convergence**: the Phillips integral converges absolutely in
`X₀`.

`norm_transL1_sub_le` under `integrable_min_const_mul`, and nothing else. Note where `f ∈ 𝒟` is
spent: the estimate `‖T_rf - f‖₁ ≤ r‖f'‖₁` is what makes the integrand small near `0`, and
`‖T_rf - f‖₁ ≤ 2‖f‖₁` — true of every `f ∈ X` — is what makes it bounded far out. The core
hypothesis buys only the first half, which is the half `ν₁`'s mass at the origin needs. -/
theorem integrable_sub_transL1 {ν : Measure ℝ} (hν : F.HasLevyTail ν) {x : ℝ} (hx : 0 < x)
    {A B : X} (hAB : HasCoreDerivL1 A B) :
    Integrable (fun r : ℝ => A - transL1 r A) (dilatedTail ν x) := by
  rw [integrable_dilatedTail_iff hx ν (continuous_sub_transL1 A).aestronglyMeasurable]
  have hcont : Continuous fun r : ℝ => A - transL1 (x * r) A :=
    (continuous_sub_transL1 A).comp (by fun_prop)
  refine Integrable.mono'
    (F.integrable_min_const_mul hν (c := 2 * ‖A‖) (d := x * ‖B‖) (by positivity) (by positivity))
    hcont.aestronglyMeasurable ?_
  filter_upwards [hν.1.ae_nonneg] with r hr
  rw [norm_sub_rev, show x * ‖B‖ * r = x * r * ‖B‖ from by ring]
  exact norm_transL1_sub_le (by positivity) hAB

/-- **`lem:generator-properties`(1), the bound**:
`‖φ_x(∂_t)f‖₁ ≤ b₀‖f'‖₁ + x⁻¹∫ min(2‖f‖₁, xr‖f'‖₁) ν₁(dr)`.

The `x⁻¹` sits outside the integral where the blueprint puts it inside, against `x⁻¹ν₁(dr)`; the
two readings agree by `integral_dilatedTail`. -/
theorem norm_phillipsGenerator_le {ν : Measure ℝ} (hν : F.HasLevyTail ν) {x : ℝ} (hx : 0 < x)
    {A B : X} (hAB : HasCoreDerivL1 A B) :
    ‖F.phillipsGenerator ν x A B‖
      ≤ F.b₀ * ‖B‖ + x⁻¹ * ∫ r, min (2 * ‖A‖) (x * r * ‖B‖) ∂ν := by
  have hcont : Continuous fun r : ℝ => min (2 * ‖A‖) (r * ‖B‖) := by fun_prop
  have hdom : Integrable (fun r : ℝ => min (2 * ‖A‖) (r * ‖B‖)) (dilatedTail ν x) := by
    refine (integrable_dilatedTail_iff hx ν hcont.aestronglyMeasurable).mpr ?_
    refine (F.integrable_min_const_mul hν (c := 2 * ‖A‖) (d := x * ‖B‖) (by positivity)
      (by positivity)).congr (.of_forall fun r => ?_)
    change min (2 * ‖A‖) (x * ‖B‖ * r) = min (2 * ‖A‖) (x * r * ‖B‖)
    rw [show x * ‖B‖ * r = x * r * ‖B‖ from by ring]
  have hbound : ∀ᵐ r ∂(dilatedTail ν x), ‖A - transL1 r A‖ ≤ min (2 * ‖A‖) (r * ‖B‖) := by
    filter_upwards [(isCausal_dilatedTail hx hν.1).ae_nonneg] with r hr
    rw [norm_sub_rev]
    exact norm_transL1_sub_le hr hAB
  have hchange : (∫ r, min (2 * ‖A‖) (r * ‖B‖) ∂(dilatedTail ν x))
      = x⁻¹ * ∫ r, min (2 * ‖A‖) (x * r * ‖B‖) ∂ν := by
    rw [integral_dilatedTail hx ν hcont.aestronglyMeasurable, smul_eq_mul]
  have hb₀ : ‖F.b₀ • B‖ = F.b₀ * ‖B‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg F.b₀_nonneg]
  calc ‖F.phillipsGenerator ν x A B‖
      ≤ ‖F.b₀ • B‖ + ‖∫ r, (A - transL1 r A) ∂(dilatedTail ν x)‖ := norm_add_le _ _
    _ ≤ F.b₀ * ‖B‖ + ∫ r, ‖A - transL1 r A‖ ∂(dilatedTail ν x) := by
        rw [hb₀]
        exact add_le_add le_rfl (norm_integral_le_integral_norm _)
    _ ≤ F.b₀ * ‖B‖ + ∫ r, min (2 * ‖A‖) (r * ‖B‖) ∂(dilatedTail ν x) :=
        add_le_add le_rfl
          (integral_mono_ae (F.integrable_sub_transL1 hν hx hAB).norm hdom hbound)
    _ = F.b₀ * ‖B‖ + x⁻¹ * ∫ r, min (2 * ‖A‖) (x * r * ‖B‖) ∂ν := by rw [hchange]

end SelfDecomposableExponent

end Hemigroup
