/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.DelayCore
import Hemigroup.Subordinator
import Hemigroup.TransformContinuity

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

/-! ## The causal transform as a bounded functional on `X`

The plan had priced clause (2) as the expensive one on the grounds that `Lap` is not a bounded
functional on `L¹(ℝ)`, so `ContinuousLinearMap.integral_comp_comm` — which discharges (3)
outright — would be unavailable. **That is true of the two-sided transform and false of the causal
one.** `laplaceFun` integrates over `(0,∞)` only, so its weight is `1_{(0,∞)}(t)e^{-st}`, which for
`s ≥ 0` is bounded by `1` on all of `ℝ`; and `mulCLM`, built in chapter 4 for exactly this shape,
turns any such weight into an element of `X →L[ℝ] ℝ`. So the exchange in (2) is the same one-liner
as in (3), and `laplaceCLM_apply` holds for *every* element of `X` — no causality hypothesis, and
so no obligation to show the Phillips integral itself is causal.
-/

/-- The causal Laplace weight `1_{(0,∞)}(t)e^{-st}`. -/
noncomputable def laplaceWeight (s : ℝ) : ℝ → ℝ :=
  (Ioi (0 : ℝ)).indicator fun t => Real.exp (-(s * t))

theorem measurable_laplaceWeight (s : ℝ) : Measurable (laplaceWeight s) :=
  (Real.measurable_exp.comp (by fun_prop)).indicator measurableSet_Ioi

/-- The bound that makes the transform a *bounded* functional, and the only place `s ≥ 0` is
used. To the left of the origin the indicator kills the growth of `e^{-st}`; to the right the
exponential is at most `1`. -/
theorem abs_laplaceWeight_le_one {s : ℝ} (hs : 0 ≤ s) (t : ℝ) : |laplaceWeight s t| ≤ 1 := by
  rw [laplaceWeight]
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · rw [indicator_of_mem ht, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith [mem_Ioi.mp ht])
  · rw [indicator_of_notMem ht, abs_zero]
    norm_num

/-- **The causal Laplace transform as a bounded functional on `X`**, of norm at most `1`. -/
noncomputable def laplaceCLM {s : ℝ} (hs : 0 ≤ s) : X →L[ℝ] ℝ :=
  mulCLM (laplaceWeight s) (measurable_laplaceWeight s) (abs_laplaceWeight_le_one hs)

/-- The functional *is* the transform, on every element of `X` — the indicator is doing the work
a causality hypothesis would otherwise have to do. -/
@[simp] theorem laplaceCLM_apply {s : ℝ} (hs : 0 ≤ s) (G : X) :
    laplaceCLM hs G = laplaceFun ((G : X) : ℝ → ℝ) s := by
  rw [laplaceCLM, mulCLM_apply, laplaceFun, ← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae (.of_forall fun t => ?_)
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · simp only [laplaceWeight, indicator_of_mem ht]
  · simp only [laplaceWeight, indicator_of_notMem ht, zero_mul]

/-- **The transform of a delay**: `Lap[T_rf](s) = e^{-sr}\hat f(s)`, for causal `f` and `r ≥ 0`.

Translation invariance of Lebesgue measure on the *whole* line, plus one a.e. identity: to the
right of the origin the weight factorises, `w_s(u+r) = e^{-sr}w_s(u)`, and to the left `f` vanishes
so both sides are zero. Causality is what makes the second half true — the weight itself does not
factorise there, the indicator having already cut it off. -/
theorem laplaceCLM_transL1 {s : ℝ} (hs : 0 ≤ s) {r : ℝ} (hr : 0 ≤ r) {A : X}
    (hA : A ∈ causalL1) :
    laplaceCLM hs (transL1 r A) = Real.exp (-(s * r)) * laplaceCLM hs A := by
  have hz : ∀ᵐ u : ℝ, u ≠ 0 := by
    filter_upwards [compl_mem_ae_iff.mpr (Real.volume_singleton (a := (0 : ℝ)))] with u hu
    simpa using hu
  rw [laplaceCLM, mulCLM_apply, mulCLM_apply]
  have hshift : (∫ t, laplaceWeight s t * ((transL1 r A : X) : ℝ → ℝ) t)
      = ∫ u, laplaceWeight s (u + r) * ((A : X) : ℝ → ℝ) u := by
    rw [← integral_sub_right_eq_self
      (fun u => laplaceWeight s (u + r) * ((A : X) : ℝ → ℝ) u) r]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_transL1 r A] with t ht
    rw [ht, sub_add_cancel]
  rw [hshift, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hA, hz] with u hu hune
  rcases lt_or_gt_of_ne hune with hneg | hpos
  · change laplaceWeight s (u + r) * ((A : X) : ℝ → ℝ) u
        = Real.exp (-(s * r)) * (laplaceWeight s u * ((A : X) : ℝ → ℝ) u)
    rw [hu hneg, mul_zero, mul_zero, mul_zero]
  · have hur : (0 : ℝ) < u + r := by linarith
    have hexp : Real.exp (-(s * (u + r))) = Real.exp (-(s * r)) * Real.exp (-(s * u)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    change laplaceWeight s (u + r) * ((A : X) : ℝ → ℝ) u
        = Real.exp (-(s * r)) * (laplaceWeight s u * ((A : X) : ℝ → ℝ) u)
    simp only [laplaceWeight, indicator_of_mem (mem_Ioi.mpr hur),
      indicator_of_mem (mem_Ioi.mpr hpos)]
    rw [hexp, mul_assoc]

/-- **`Lap[f'](s) = s\hat f(s)`** for `f ∈ 𝒟`, from the difference quotient.

The blueprint derives it "using `f(0) = 0`", which classically means integrating by parts and
watching the boundary term vanish. Here `f(0) = 0` has already been spent, once, inside
`HasCoreDeriv`; what is left is to apply the *bounded* functional `Lap_s` to `lem:delay-core`'s
limit `h⁻¹(T_hf - f) → -f'`. The left side is `h⁻¹(e^{-sh} - 1)\hat f(s)` by
`laplaceCLM_transL1`, whose limit is `-s\hat f(s)` because that quotient is the difference
quotient of `h ↦ e^{-sh}` at the origin; uniqueness of limits does the rest.

**No Fubini, no integration by parts, and no boundary term to make vanish.** The same shape the
plan keeps recording — the classical derivation asking for more than the obligation — and here
what it asked for was the exchange of two integrals. -/
theorem laplaceCLM_of_hasCoreDerivL1 {s : ℝ} (hs : 0 < s) {A B : X}
    (hAB : HasCoreDerivL1 A B) : laplaceCLM hs.le B = s * laplaceCLM hs.le A := by
  have hA : A ∈ causalL1 := coreL1_subset_causalL1 ⟨B, hAB⟩
  have hquot : Tendsto (fun r : ℝ => laplaceCLM hs.le (r⁻¹ • (transL1 r A - A)))
      (𝓝[>] (0 : ℝ)) (𝓝 (laplaceCLM hs.le (-B))) :=
    ((laplaceCLM hs.le).continuous.tendsto _).comp (tendsto_differenceQuotient hAB)
  have hvalue : (fun r : ℝ => laplaceCLM hs.le (r⁻¹ • (transL1 r A - A)))
      =ᶠ[𝓝[>] (0 : ℝ)] fun r => (Real.exp (-(s * r)) - 1) / r * laplaceCLM hs.le A := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [map_smul, map_sub, laplaceCLM_transL1 hs.le (mem_Ioi.mp hr).le hA, smul_eq_mul,
      div_eq_inv_mul]
    ring
  -- the scalar quotient is the derivative of `r ↦ e^{-sr}` at the origin
  have hslope : Tendsto (fun r : ℝ => (Real.exp (-(s * r)) - 1) / r) (𝓝[>] (0 : ℝ)) (𝓝 (-s)) := by
    have hd : HasDerivAt (fun r : ℝ => Real.exp (-(s * r))) (-s) 0 := by
      have h1 : HasDerivAt (fun r : ℝ => -(s * r)) (-s) 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).const_mul (-s)
      simpa using h1.exp
    have h := hasDerivAt_iff_tendsto_slope.mp hd
    refine (h.mono_left (nhdsWithin_mono _ fun r hr => ?_)).congr fun r => ?_
    · simpa using ne_of_gt (mem_Ioi.mp hr)
    · rw [slope_def_field]
      simp
  have hlim : Tendsto (fun r : ℝ => laplaceCLM hs.le (r⁻¹ • (transL1 r A - A)))
      (𝓝[>] (0 : ℝ)) (𝓝 (-s * laplaceCLM hs.le A)) :=
    (hslope.mul_const _).congr' hvalue.symm
  have := tendsto_nhds_unique hquot hlim
  rw [map_neg] at this
  linarith

/-- **The layer cake, a fifth time**: `∫ν(dr)∫₀^r h = ∫₀^∞ h(u)ν((u,∞))du` for `h ≥ 0` and `ν`
causal.

`lintegral_comp_eq_lintegral_meas_lt_mul` at `f = id`, exactly as chapter 9 used it for the
potential kernel and chapter 7 for the Dickman superposition; only the integrand changes. It is
the exchange `lem:generator-properties`(5) runs on, and stating it for a general nonnegative `h`
is what lets the signed case be got by domination rather than by splitting. -/
theorem lintegral_intervalIntegral_eq_tail {ν : Measure ℝ} (hν : IsCausal ν) {h : ℝ → ℝ}
    (hhnn : ∀ u, 0 ≤ h u) (hhi : ∀ r : ℝ, IntervalIntegrable h volume 0 r) :
    (∫⁻ r, ENNReal.ofReal (∫ u in (0 : ℝ)..r, h u) ∂ν)
      = ∫⁻ u in Ioi (0 : ℝ), ν (Ioi u) * ENNReal.ofReal (h u) :=
  lintegral_comp_eq_lintegral_meas_lt_mul (f := fun r : ℝ => r) (g := h) ν hν.ae_nonneg
    aemeasurable_id (fun r _ => hhi r) (.of_forall hhnn)

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

/-! ## `lem:generator-properties`(3) and (4)

Both run on clause (1) and one Mathlib theorem apiece, and the pair is worth reading together
because the theorems are the two ways an operator meets a Bochner integral. (3) pulls a
*continuous linear map* through it — `ContinuousLinearMap.integral_comp_comm`, which needs only
the integrability clause (1) supplies. (4) differentiates nothing and pulls nothing through: it is
dominated convergence in the parameter, `continuousAt_of_dominated`, with clause (1)'s bound
re-used as the dominating function.

That (4) can re-use the bound at all is what `phillipsGenerator_eq_smul_integral` buys. In the
`ν_x` form the scale sits in the *measure*, where a limit in `x` has nothing to dominate; in the
dilated form it sits in the integrand, and the bound `min(2‖f‖₁, xr‖f'‖₁)` is monotone in `x`, so
one bound at the top of a neighbourhood covers the whole neighbourhood.
-/

/-- **`lem:generator-properties`(3), commutation**: `φ_x(∂_t)` commutes with every `Φ` on `𝒟`.

Stated for an arbitrary finite measure. The blueprint says "every `Φ_{y,z}`", and neither
causality nor normalisation is used — `mconvL1_transL1` (chapter 3, (A2) for `mconvL1`) holds for
any finite measure and the rest is linearity — so the clause is proved off the constructed family
entirely, and with it off the ledger. -/
theorem mconvL1_phillipsGenerator {ν : Measure ℝ} (hν : F.HasLevyTail ν) {x : ℝ} (hx : 0 < x)
    {A B : X} (hAB : HasCoreDerivL1 A B) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    mconvL1 μ (F.phillipsGenerator ν x A B)
      = F.phillipsGenerator ν x (mconvL1 μ A) (mconvL1 μ B) := by
  rw [phillipsGenerator, phillipsGenerator, map_add, map_smul,
    ← ContinuousLinearMap.integral_comp_comm _ (F.integrable_sub_transL1 hν hx hAB)]
  congr 1
  refine integral_congr_ae (.of_forall fun r => ?_)
  change mconvL1 μ (A - transL1 r A) = mconvL1 μ A - transL1 r (mconvL1 μ A)
  rw [map_sub, mconvL1_transL1]

/-- **`lem:generator-properties`(4), continuity**: `x ↦ φ_x(∂_t)f` is continuous from `(0,∞)` to
`X₀`.

Dominated convergence in the dilated form. The dominating function is clause (1)'s, evaluated at
the top of a neighbourhood of the point: `min(2‖f‖₁, xr‖f'‖₁)` increases in `x`, so a single
`min(2‖f‖₁, 2x₀r‖f'‖₁)` dominates every `x < 2x₀` at once — which is the sense in which the
blueprint's "for `x` in a compact subset of `(0,∞)`" is discharged without ever forming a compact
set. -/
theorem continuousOn_phillipsGenerator {ν : Measure ℝ} (hν : F.HasLevyTail ν) {A B : X}
    (hAB : HasCoreDerivL1 A B) :
    ContinuousOn (fun y : ℝ => F.phillipsGenerator ν y A B) (Ioi 0) := by
  have hr : ∀ y : ℝ, Continuous fun r : ℝ => A - transL1 (y * r) A := fun y =>
    (continuous_sub_transL1 A).comp (by fun_prop)
  have hy : ∀ r : ℝ, Continuous fun y : ℝ => A - transL1 (y * r) A := fun r =>
    (continuous_sub_transL1 A).comp (by fun_prop)
  have key : ∀ y₀ : ℝ, 0 < y₀ →
      ContinuousAt (fun y : ℝ => ∫ r, (A - transL1 (y * r) A) ∂ν) y₀ := by
    intro y₀ hy₀
    refine continuousAt_of_dominated
      (bound := fun r => min (2 * ‖A‖) (2 * y₀ * ‖B‖ * r))
      (.of_forall fun y => (hr y).aestronglyMeasurable) ?_
      (F.integrable_min_const_mul hν (by positivity) (by positivity))
      (.of_forall fun r => (hy r).continuousAt)
    filter_upwards [Ioo_mem_nhds (show y₀ / 2 < y₀ by linarith)
      (show y₀ < 2 * y₀ by linarith)] with y hyw
    filter_upwards [hν.1.ae_nonneg] with r hrnn
    rw [norm_sub_rev]
    refine le_trans (norm_transL1_sub_le (by nlinarith [hyw.1]) hAB) (min_le_min le_rfl ?_)
    nlinarith [mul_nonneg hrnn (norm_nonneg B), hyw.2]
  refine ContinuousOn.congr ?_ fun y hyi =>
    F.phillipsGenerator_eq_smul_integral (mem_Ioi.mp hyi) ν A B
  intro y hyi
  have hy0 : 0 < y := mem_Ioi.mp hyi
  exact (continuousAt_const.add ((continuousAt_inv₀ hy0.ne').smul (key y hy0))).continuousWithinAt

/-! ## `lem:generator-properties`(2): the symbol

Three steps, none of them Fubini. The transform is a *bounded functional*, so it passes through
the Bochner integral exactly as `Φ` does in (3); `Lap[f'] = s\hat f` comes off the difference
quotient rather than off an integration by parts; and what is left is the scalar identity
`b₀s + ∫(1-e^{-sr})ν_x(dr) = sF'(xs)`, which is the layer cake against `lem:memory-kernel`.
-/

/-- **The Lévy integral of the delay factor**: `∫(1 - e^{-σr})ν₁(dr) = σ∫₀^∞ e^{-σt}k(t)dt`.

The layer cake in the form chapter 9 proved it (`lintegral_one_sub_exp_eq_tail`, the antiderivative
of `σe^{-σr}` being `1 - e^{-σr}`), and this is the step that makes `HasLevyTail` load-bearing: it
is where `ν₁`'s tail becomes `k`, and the identity is consumed under an integral in `r`, which is
why the specification's `ae` qualifier costs nothing. -/
theorem integral_one_sub_exp_tail {ν : Measure ℝ} (hν : F.HasLevyTail ν) {σ : ℝ} (hσ : 0 < σ) :
    (∫ r, (1 - Real.exp (-(σ * r))) ∂ν)
      = σ * ∫ t in Ioi (0 : ℝ), Real.exp (-(σ * t)) * F.k t := by
  have hnn : ∀ᵐ r ∂ν, 0 ≤ 1 - Real.exp (-(σ * r)) := by
    filter_upwards [hν.1.ae_nonneg] with r hr
    have : Real.exp (-(σ * r)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    linarith
  have hnn2 : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), 0 ≤ σ * Real.exp (-(σ * r)) * F.k r :=
    (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun r hr =>
      mul_nonneg (mul_nonneg hσ.le (Real.exp_pos _).le) (F.k_nonneg r hr))
  have hmeas2 : AEStronglyMeasurable (fun r => σ * Real.exp (-(σ * r)) * F.k r)
      (volume.restrict (Ioi (0 : ℝ))) :=
    (((measurable_const.mul (by fun_prop : Measurable fun r : ℝ =>
      Real.exp (-(σ * r)))).aemeasurable).mul (F.aemeasurable_k subset_rfl)).aestronglyMeasurable
  have htail : (∫⁻ r in Ioi (0 : ℝ),
        ENNReal.ofReal (σ * Real.exp (-(σ * r))) * ν (Ioi r))
      = ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (σ * Real.exp (-(σ * r)) * F.k r) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hν.2] with r hr
    rw [hr, ← ENNReal.ofReal_mul (by positivity)]
  rw [integral_eq_lintegral_of_nonneg_ae hnn (by fun_prop),
    lintegral_one_sub_exp_eq_tail hν.1 hσ, htail,
    ← integral_eq_lintegral_of_nonneg_ae hnn2 hmeas2, ← integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Ioi fun r _ => by ring

/-- The same integral against `ν_x`, which is where the scale enters:
`∫(1 - e^{-sr})ν_x(dr) = s∫₀^∞ e^{-xst}k(t)dt`. -/
theorem integral_one_sub_exp_dilatedTail {ν : Measure ℝ} (hν : F.HasLevyTail ν) {x : ℝ}
    (hx : 0 < x) {s : ℝ} (hs : 0 < s) :
    (∫ r, (1 - Real.exp (-(s * r))) ∂(dilatedTail ν x))
      = s * ∫ t in Ioi (0 : ℝ), Real.exp (-(x * s * t)) * F.k t := by
  have hcont : Continuous fun r : ℝ => 1 - Real.exp (-(s * r)) := by fun_prop
  rw [integral_dilatedTail hx ν hcont.aestronglyMeasurable, smul_eq_mul]
  have hrw : (∫ r, (1 - Real.exp (-(s * (x * r)))) ∂ν)
      = ∫ r, (1 - Real.exp (-(x * s * r))) ∂ν := by
    refine integral_congr_ae (.of_forall fun r => ?_)
    change 1 - Real.exp (-(s * (x * r))) = 1 - Real.exp (-(x * s * r))
    rw [show s * (x * r) = x * s * r from by ring]
  rw [hrw, F.integral_one_sub_exp_tail hν (by positivity : (0 : ℝ) < x * s), ← mul_assoc,
    inv_mul_cancel_left₀ hx.ne']

/-- **`lem:generator-properties`(2), the symbol**:
`Lap[φ_x(∂_t)f](s) = φ_x(s)\hat f(s)`, with `φ_x(s) = sF'(xs)` — chapter 9's `symbol`.

The clause that pins the definition: it is true of a `ν` with `F`'s tail and of no other, so the
`HasLevyTail` hypothesis is load-bearing here and the parameterisation costs nothing in content.
The two Bernstein representations of `φ_x` agreeing is `integral_one_sub_exp_dilatedTail` against
`hasDerivAt_toRealExponent`. -/
theorem laplaceFun_phillipsGenerator {ν : Measure ℝ} (hν : F.HasLevyTail ν) {x : ℝ} (hx : 0 < x)
    {A B : X} (hAB : HasCoreDerivL1 A B) {s : ℝ} (hs : 0 < s) :
    laplaceFun ((F.phillipsGenerator ν x A B : X) : ℝ → ℝ) s
      = F.symbol x s * laplaceFun ((A : X) : ℝ → ℝ) s := by
  have hA : A ∈ causalL1 := coreL1_subset_causalL1 ⟨B, hAB⟩
  rw [← laplaceCLM_apply hs.le, ← laplaceCLM_apply hs.le, phillipsGenerator, map_add, map_smul,
    ← ContinuousLinearMap.integral_comp_comm _ (F.integrable_sub_transL1 hν hx hAB)]
  have hpt : ∀ᵐ r ∂(dilatedTail ν x), laplaceCLM hs.le (A - transL1 r A)
      = (1 - Real.exp (-(s * r))) * laplaceCLM hs.le A := by
    filter_upwards [(isCausal_dilatedTail hx hν.1).ae_nonneg] with r hr
    rw [map_sub, laplaceCLM_transL1 hs.le hr hA]
    ring
  rw [integral_congr_ae hpt, integral_mul_const,
    F.integral_one_sub_exp_dilatedTail hν hx hs,
    laplaceCLM_of_hasCoreDerivL1 hs hAB, smul_eq_mul, symbol,
    (F.hasDerivAt_toRealExponent (by positivity : (0 : ℝ) < x * s)).deriv]
  ring

/-! ## `lem:generator-properties`(5): the memory-kernel form

The blueprint compares the two operators through their transforms and separates them with
`prop:laplace-uniqueness`. **The Lean proof does not, and needs no uniqueness theorem at all.**
`setIntegralCLM (Ioc 0 t)` is a bounded functional — the third one this chapter pushes through the
Bochner integral, after `mconvL1 μ` and `laplaceCLM` — so the primitive of `φ_x(∂_t)f` can be
*evaluated* rather than characterised:

  `∫₀^t φ_x(∂_t)f = b₀f(t) + ∫ ν_x(dr) ∫_{(t-r,t]} f`,

and what is left is one scalar Fubini turning `∫ν_x(dr)∫_{(0,r)}f(t-u)du` into
`∫₀^∞ f(t-u)ν_x((u,∞))du`, which the tail identity reads as `κ^{(x)} * f` minus its drift atom.
Equality then holds at **every** `t`, not almost every, and the ledger entry the blueprint's route
would have spent is not spent.
-/

/-- The primitive of `φ_x(∂_t)f`, evaluated: `setIntegralCLM` through the Bochner integral. -/
theorem setIntegral_phillipsGenerator {ν : Measure ℝ} (hν : F.HasLevyTail ν) {x : ℝ} (hx : 0 < x)
    {A B : X} (hAB : HasCoreDerivL1 A B) (S : Set ℝ) :
    (∫ ρ in S, ((F.phillipsGenerator ν x A B : X) : ℝ → ℝ) ρ)
      = F.b₀ * (∫ ρ in S, ((B : X) : ℝ → ℝ) ρ)
        + ∫ r, (∫ ρ in S, ((A - transL1 r A : X) : ℝ → ℝ) ρ) ∂(dilatedTail ν x) := by
  rw [← setIntegralCLM_apply, phillipsGenerator, map_add, map_smul, smul_eq_mul,
    ← ContinuousLinearMap.integral_comp_comm _ (F.integrable_sub_transL1 hν hx hAB)]
  simp only [setIntegralCLM_apply]

/-- Each term of that evaluation, on a core representative: `∫₀^t (f - T_rf) = ∫_{(t-r,t]} f`. -/
theorem setIntegral_sub_transL1 {A : X} {f : ℝ → ℝ} (hA : ((A : X) : ℝ → ℝ) =ᵐ[volume] f)
    (hfi : Integrable f) (hfc : ∀ u : ℝ, u < 0 → f u = 0) {r : ℝ} (hr : 0 ≤ r) (t : ℝ) :
    (∫ ρ in Ioc (0 : ℝ) t, ((A - transL1 r A : X) : ℝ → ℝ) ρ)
      = (∫ ρ in Ioc (0 : ℝ) t, f ρ) - ∫ ρ in Ioc (0 : ℝ) (t - r), f ρ := by
  have hrep : ((A - transL1 r A : X) : ℝ → ℝ)
      =ᵐ[volume] fun ρ => f ρ - f (ρ - r) := by
    filter_upwards [Lp.coeFn_sub A (transL1 r A), coeFn_transL1 r A, hA,
      (measurePreserving_sub_const r).quasiMeasurePreserving.ae hA] with ρ h1 h2 h3 h4
    rw [h1, Pi.sub_apply, h2, h3, h4]
  have hshift : (∫ ρ in Ioc (0 : ℝ) t, f (ρ - r)) = ∫ ρ in Ioc (0 : ℝ) (t - r), f ρ := by
    rcases le_or_gt 0 t with ht | ht
    · rw [setIntegral_Ioc_eq_intervalIntegral_of_causal (hfi.comp_sub_right r)
          (fun u hu => hfc (u - r) (by linarith)) t,
        intervalIntegral.integral_comp_sub_right f r, zero_sub,
        intervalIntegral.integral_of_le (by linarith : -r ≤ t - r),
        setIntegral_Ioc_of_causal hfi hfc (by linarith : -r ≤ (0 : ℝ)) (t - r)]
    · rw [Ioc_eq_empty (not_lt.mpr ht.le),
        Ioc_eq_empty (not_lt.mpr (by linarith : t - r ≤ 0))]
      simp
  rw [setIntegral_congr_ae measurableSet_Ioc (hrep.mono fun ρ hρ _ => hρ),
    integral_sub hfi.integrableOn ((hfi.comp_sub_right r).integrableOn), hshift]

end SelfDecomposableExponent

end Hemigroup
