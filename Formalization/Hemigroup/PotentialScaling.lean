/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Hemigroup.Sonine

/-!
# `lem:potential-kernel-scaling`: the potential kernel scales

Blueprint: `lem:potential-kernel-scaling` (Lemma 9.16). `ℓ^{(x)}` is `x` times the pushforward of
`ℓ^{(1)}` under `t ↦ xt`.

## The node's recorded blocker dissolves the way chapter 10's did

The status line said this clause "presupposes a *named* `ℓ^{(x)}`: the Lean statement asserts
existence and uniqueness, so the object must be chosen before a scaling law can be predicated of
it, and that choice is a definition this development has not needed for anything else".

It does not have to be chosen. **State the law against any two measures meeting the
specification** — that is what `thm:sonine-conservation` and `prop:sonine-pair-exists` already do
with their `ℓ`, and what chapter 10 does with `ν₁` through `HasLevyTail`. The uniqueness half of
`lem:potential-kernel` is exactly what makes the hypothesis pin the objects down, so quantifying
over them loses nothing; and no definition without a consumer gets introduced.

Third time this week that "we would have to name the object first" turned out to be avoidable, and
the reason is the same each time: **a specification is a hypothesis, and a hypothesis can be
quantified over.** What cannot be quantified over is a *construction*, which is why chapter 9 built
one for the tail measure and none for this.

## The proof is a comparison of transforms

`\hat{ℓ^{(x)}}(s) = 1/(sF'(xs))`, `\hat{ℓ^{(1)}}(xs) = 1/(xsF'(xs))`, and the dilation
reparametrises the transform (`laplaceL_map_const_mul`, the `ℝ≥0∞` twin of chapter 2's
`laplace_map_const_mul`). Laplace injectivity for locally finite causal measures does the rest —
the same `laplaceL_injective_of_ne_top` chapter 9 was built around.
-/

namespace Hemigroup

open MeasureTheory Set

open scoped ENNReal

/-- **Dilation reparametrises the transform**, in `ℝ≥0∞`: `(D_σ μ)ˆ(s) = μˆ(σs)`.

The `laplaceL` twin of `laplace_map_const_mul`. Needed separately because the potential kernel is
not finite, so its transform has no real-valued reading. -/
theorem laplaceL_map_const_mul (μ : Measure ℝ) {σ : ℝ} (hσ : 0 < σ) (s : ℝ) :
    laplaceL (μ.map fun t => σ * t) s = laplaceL μ (σ * s) := by
  have hemb : MeasurableEmbedding (fun t : ℝ => σ * t) :=
    (Homeomorph.mulLeft₀ σ hσ.ne').toMeasurableEquiv.measurableEmbedding
  rw [laplaceL, hemb.lintegral_map, laplaceL]
  refine lintegral_congr fun t => ?_
  congr 2
  ring

/-- A dilated causal measure is causal. -/
theorem isCausal_map_const_mul {μ : Measure ℝ} (hμ : IsCausal μ) {σ : ℝ} (hσ : 0 < σ) :
    IsCausal (μ.map fun t => σ * t) := by
  have hpre : (fun t : ℝ => σ * t) ⁻¹' Iio 0 = Iio 0 := by
    ext y
    simp only [mem_preimage, mem_Iio]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  rw [IsCausal, Measure.map_apply (by fun_prop) measurableSet_Iio, hpre, hμ]

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent)

/-- **`lem:potential-kernel-scaling`**: any two measures meeting the potential-kernel
specification at scales `1` and `x` are related by the dilation, `ℓ^{(x)} = x·(ℓ^{(1)} ∘ (x·)⁻¹)`.

Stated against the specification rather than against a construction — see the module docstring. -/
theorem potential_kernel_scaling (hnd : F.Nondegenerate) {x : ℝ} (hx : 0 < x)
    {ℓ₁ ℓx : Measure ℝ} (h1c : IsCausal ℓ₁) (hxc : IsCausal ℓx)
    (h1 : ∀ s : ℝ, 0 < s → laplaceL ℓ₁ s = ENNReal.ofReal (F.symbol 1 s)⁻¹)
    (hxs : ∀ s : ℝ, 0 < s → laplaceL ℓx s = ENNReal.ofReal (F.symbol x s)⁻¹) :
    ℓx = ENNReal.ofReal x • ℓ₁.map (fun t => x * t) := by
  refine laplaceL_injective_of_ne_top hxc ?_ (?_ : laplaceL ℓx 1 ≠ ⊤) fun s hs => ?_
  · rw [IsCausal, Measure.smul_apply, (isCausal_map_const_mul h1c hx), smul_zero]
  · rw [hxs 1 zero_lt_one]
    exact ENNReal.ofReal_ne_top
  · have hspos : (0 : ℝ) < s := lt_of_lt_of_le zero_lt_one hs
    have hxspos : (0 : ℝ) < x * s := by positivity
    have hderiv : 0 < deriv F.toRealExponent (x * s) :=
      F.deriv_toRealExponent_pos hnd hxspos
    rw [hxs s hspos, laplaceL, lintegral_smul_measure, ← laplaceL,
      laplaceL_map_const_mul ℓ₁ hx s, h1 (x * s) hxspos, smul_eq_mul,
      ← ENNReal.ofReal_mul hx.le]
    congr 1
    rw [symbol, symbol, one_mul]
    field_simp

end SelfDecomposableExponent

end Hemigroup
