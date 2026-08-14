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
  rw [phillipsGenerator, dilatedTail, integral_smul_measure,
    integral_map (by fun_prop) (continuous_sub_transL1 A).aestronglyMeasurable,
    ENNReal.toReal_ofReal (by positivity)]

end SelfDecomposableExponent

end Hemigroup
