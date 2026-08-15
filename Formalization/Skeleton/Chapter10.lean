/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.PhillipsGenerator

/-!
# The target types of `lem:generator-properties` (10.3)

**This file carries `sorry`s and is not part of the `Hemigroup` library.**

`lem:delay-core` (10.1) was stated here and has moved; its declarations are listed at the foot of
this docstring. What the file holds now is the five clauses of `lem:generator-properties`, each a
named sub-lemma, with a `sorry`-free collation above them. The definition they are about,
`def:phillips-generator` (10.2), is *proved* and lives in `Hemigroup/PhillipsGenerator.lean` —
a definition has no `sorry` to carry.

| clause | declaration | state |
|---|---|---|
| (1) convergence | `integrable_sub_transL1` | **proved**, `Hemigroup/PhillipsGenerator.lean` |
| (1) the bound | `norm_phillipsGenerator_le` | **proved**, same file |
| (2) the symbol | `laplaceFun_phillipsGenerator` | **proved**, same file |
| (3) commutation | `mconvL1_phillipsGenerator` | **proved**, same file |
| (4) continuity in `x` | `continuousOn_phillipsGenerator` | **proved**, same file |
| (5) the memory-kernel form | `mconv_memoryKernel_ae_eq` | open — transform, then uniqueness |
| the node | `generator_properties` | `sorry`-free collation |

## Why this is not blocked, since the chapter was filed as blocked

The status line said chapter 10 waits on C₀-semigroup and closed-operator theory. That was written
before `𝒟` and `T_r` existed. They exist now, and **no clause below mentions a generator's domain,
a resolvent, or a generation theorem**; the one place semigroup language appears is (4)'s "strong
continuity of `T`", which is `continuous_transL1`, proved in chapter 4. The C₀ reason belongs to
`thm:scale-cauchy` and `prop:fixed-scale-semigroup`, and `thm:scale-cauchy` is blocked a second
way in any case, through `prop:scale-evolution`(2), which is distributional.

## Three things the statements had to decide

**`ν₁` is a parameter.** Every clause quantifies over a `ν` meeting `HasLevyTail`, rather than
over a construction, so that the chapter does not wait on an existence half — the discipline
`sonine_conservation` set, and `exists_hasLevyTail` closes the gap. The tail identity in that
specification is `ae` and not pointwise, because `k` is only nonincreasing; see
`Hemigroup/PhillipsGenerator.lean`'s docstring.

**The `Φ`-clause is stated for an arbitrary causal probability measure**, not for `F.kernel y z`.
That is strictly more general, it is what the proof actually uses — convolutions commute — and it
keeps the clause off ledger A17, which quantifying over the constructed family would have put it
on. Same reading as `lem:delay-core`'s own `Φ`-clause, one notch more general.

**Clause (5) is stated in the primitive vocabulary, not through absolute continuity.** The
blueprint says `κ^{(x)} * f` "is a.e. equal to an absolutely continuous function with
`(κ^{(x)}*f)' = φ_x(∂_t)f` a.e."; below it says `κ^{(x)} * f` agrees a.e. with the *primitive* of
`φ_x(∂_t)f`. Those are the same statement, and the primitive form is the one `𝒟` is defined in and
the one that carries the blueprint's trailing remark `(κ^{(x)}*f)(0+) = 0` for free, the primitive
vanishing at the origin by construction. The reason is `HasCoreDeriv`'s reason: the passage from
absolute continuity back to the primitive is the Lebesgue fundamental theorem, which Mathlib does
not carry.

## Work order, and where the cost actually is

Clauses (1), (2), (3) and (4) are **done** and have moved. Only (5) is left, and the estimate
that survives is the one about it.

**The estimate for (2) did not survive, and it is worth saying exactly how it was wrong.** It read:
`Lap` is not a bounded functional on `L¹(ℝ)`, `e^{-st}` being unbounded to the left of the origin,
so `ContinuousLinearMap.integral_comp_comm` — which discharges (3) outright — does not apply, and
the exchange must be done on causal representatives in `[0,∞]`. Every clause of that is true of
the **two-sided** transform and false of the article's, which integrates over `(0,∞)` only. Its
weight is `1_{(0,∞)}(t)e^{-st}`, bounded by `1` on all of `ℝ` for `s ≥ 0`, so `mulCLM` — chapter
4's, built for exactly this shape — makes it an element of `X →L[ℝ] ℝ`, and (2)'s exchange is the
same one-liner as (3)'s. The bound that was supposed to fail is what the indicator supplies for
free. Two further steps also came in under: `Lap[f'] = s\hat f` is the difference quotient of
`lem:delay-core` under a *continuous* functional rather than an integration by parts, and the
scalar identity is chapter 9's `lintegral_one_sub_exp_eq_tail` verbatim.

### (5), open — the route is settled and three of its four steps are proved

**The route changed, and it no longer goes through a uniqueness theorem.** The blueprint compares
the two operators through their transforms and separates them with `prop:laplace-uniqueness`. That
is not needed: `setIntegralCLM (Ioc 0 t)` is a *bounded functional* — the third one this chapter
pushes through the Bochner integral, after `mconvL1 μ` and `laplaceCLM` — so the primitive of
`φ_x(∂_t)f` can be **evaluated** rather than characterised. The identity then holds at every `t`
rather than almost every, and the earlier plan to reduce to `f' ≥ 0` so that both sides become
measures is not needed either; it was an artefact of the transform route.

Proved and in `Hemigroup/PhillipsGenerator.lean`, with no consumer yet:

| step | declaration |
|---|---|
| the primitive, evaluated | `setIntegral_phillipsGenerator` |
| each term of it | `setIntegral_sub_transL1` — `∫₀^t (f - T_rf) = ∫₀^t f - ∫₀^{t-r} f` |
| the exchange, for `h ≥ 0` | `lintegral_intervalIntegral_eq_tail` — the layer cake, a fifth time |

**What is left is one signed Fubini and one unfolding.** The Fubini is
`∫ν_x(dr)∫₀^r f(t-u)du = ∫₀^∞ f(t-u)ν_x((u,∞))du`; its integrability side condition is *clause
(1)'s convergence again*, because `|∫₀^r f(t-u)du| ≤ min(‖f‖₁, Mr)` with `M = sup|f|`
(`HasCoreDeriv.abs_le`), which is `integrable_min_const_mul`'s integrand. Two ways to get the
signed case from the nonnegative one, and the second looks cheaper: split `f(t-·)` into positive
and negative parts and add, or split `f'` and use that both operators are linear in `f`, which
makes `f` nondecreasing and the integrand nonnegative outright. The unfolding is
`mconv (memoryKernel x) f t = b₀f(t) + ∫₀^∞ f(t-u)k(u/x)/x du`, against
`memoryKernel = b₀δ₀ + ...`, after which the tail identity closes the gap.

Note what the change of route costs elsewhere: `mconv_eq_setIntegral_mconv` no longer needs
generalising to a locally finite measure. That refactor was flagged twice as "worth making when a
second consumer appears"; the second consumer has now gone away.

## `lem:delay-core`, discharged

| clause | declaration (under `Hemigroup/`) |
|---|---|
| density in `X₀` | `dense_coreL1` |
| invariance under `T_r` | `hasCoreDerivL1_transL1` |
| invariance under `Φ_{x,y}` | `hasCoreDerivL1_mconvL1` |
| the difference quotient | `tendsto_differenceQuotient` |
| the estimate | `norm_transL1_sub_le` |
| the node | `delay_core` |

What the statement-first step bought there was the modelling decision — `X₀` a predicate on
`X = L¹(ℝ)`, `𝒟` a predicate on genuine functions, defined by the primitive — checked by
`memCore_iff_signaling_hypotheses`, an `iff` and not a one-way check. And the cost estimate was
wrong by most of the work, because `continuous_transL1` and `approxId` were both already in the
development. That is the lesson this file is being reopened under: the estimates above are stated
so that the next round can be measured against them.
-/

namespace Skeleton

open MeasureTheory Set Filter

open scoped ENNReal Topology

open Hemigroup

namespace GeneratorProperties

variable (F : Hemigroup.SelfDecomposableExponent) {ν : Measure ℝ} {x : ℝ} {A B : X}

/-- **`lem:generator-properties`(5), the memory-kernel form**: `κ^{(x)} * f` agrees a.e. with the
primitive of `φ_x(∂_t)f`, so the Phillips form coincides on `𝒟` with chapter 9's operator.

The blueprint's "absolutely continuous, with derivative `φ_x(∂_t)f` a.e." read in the primitive
vocabulary `𝒟` is defined in — which also carries its trailing `(κ^{(x)}*f)(0+) = 0`, a primitive
vanishing at the origin by construction. -/
theorem mconv_memoryKernel_ae_eq (hν : F.HasLevyTail ν) (hx : 0 < x) {f g : ℝ → ℝ}
    (hfg : HasCoreDeriv f g) (hA : ((A : X) : ℝ → ℝ) =ᵐ[volume] f)
    (hB : ((B : X) : ℝ → ℝ) =ᵐ[volume] g) :
    mconv (F.memoryKernel x) f
      =ᵐ[volume] fun t => ∫ ρ in Ioc (0 : ℝ) t,
        ((F.phillipsGenerator ν x A B : X) : ℝ → ℝ) ρ := by
  sorry

end GeneratorProperties

open GeneratorProperties

/-- **`lem:generator-properties` (Lemma 10.3).** The five properties of the Phillips form on the
core: absolute convergence with the two-sided bound, the symbol `φ_x(s) = sF'(xs)`, commutation
with every `Φ`, continuity in the scale, and agreement with chapter 9's memory-kernel operator.

The collation the node carries, assembled from the five sub-lemmas above and `sorry`-free. -/
theorem generator_properties (F : Hemigroup.SelfDecomposableExponent) {ν : Measure ℝ}
    (hν : F.HasLevyTail ν) {x : ℝ} (hx : 0 < x) {A B : X} (hAB : HasCoreDerivL1 A B) :
    (Integrable (fun r : ℝ => A - transL1 r A) (dilatedTail ν x) ∧
        ‖F.phillipsGenerator ν x A B‖
          ≤ F.b₀ * ‖B‖ + x⁻¹ * ∫ r, min (2 * ‖A‖) (x * r * ‖B‖) ∂ν) ∧
      (∀ s : ℝ, 0 < s →
        laplaceFun ((F.phillipsGenerator ν x A B : X) : ℝ → ℝ) s
          = F.symbol x s * laplaceFun ((A : X) : ℝ → ℝ) s) ∧
      (∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], IsCausal μ →
        mconvL1 μ (F.phillipsGenerator ν x A B)
          = F.phillipsGenerator ν x (mconvL1 μ A) (mconvL1 μ B)) ∧
      ContinuousOn (fun y : ℝ => F.phillipsGenerator ν y A B) (Ioi 0) ∧
      (∀ f g : ℝ → ℝ, HasCoreDeriv f g → ((A : X) : ℝ → ℝ) =ᵐ[volume] f →
        ((B : X) : ℝ → ℝ) =ᵐ[volume] g →
        mconv (F.memoryKernel x) f
          =ᵐ[volume] fun t => ∫ ρ in Ioc (0 : ℝ) t,
            ((F.phillipsGenerator ν x A B : X) : ℝ → ℝ) ρ) :=
  ⟨⟨F.integrable_sub_transL1 hν hx hAB, F.norm_phillipsGenerator_le hν hx hAB⟩,
   fun _ hs => F.laplaceFun_phillipsGenerator hν hx hAB hs,
   fun μ _ _ => F.mconvL1_phillipsGenerator hν hx hAB μ,
   F.continuousOn_phillipsGenerator hν hAB,
   fun _ _ hfg hA hB => mconv_memoryKernel_ae_eq F hν hx hfg hA hB⟩

end Skeleton
