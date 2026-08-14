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
| (2) the symbol | `laplaceFun_phillipsGenerator` | open — Fubini and `lem:memory-kernel` |
| (3) commutation | `mconvL1_phillipsGenerator` | open — `ContinuousLinearMap.integral_comp_comm` |
| (4) continuity in `x` | `continuousOn_phillipsGenerator` | open — dominated convergence |
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

Clause (1) is **done** and has moved; it cost what the estimate said, and the estimate was that
`integrable_min_one_id` — `∫(1∧r)ν(dr) < ∞` — is one layer cake and not the integration by parts
the blueprint's proof names, with the `k(1) < ∞` half of that argument's hypothesis unused. It is.
The rest: (3), (4) moderate; (2) and (5) the bulk.

3. (3) is `ContinuousLinearMap.integral_comp_comm` applied to `mconvL1 μ`, which **is** a
   continuous linear map, together with `hasCoreDerivL1_mconvL1` to know the right-hand side is
   the generator of a core element. It needs (1) for the integrability hypothesis.
4. (4) is dominated convergence in the dilated form `phillipsGenerator_eq_smul_integral`, where
   the `x`-dependence sits in the integrand: continuity in `x` for each `r` is
   `continuous_transL1`, and the dominating function is the (1)-bound with `x` ranging over a
   compact subset of `(0,∞)`.
5. (2) is the one to price honestly. `Lap` is **not** a bounded functional on `L¹(ℝ)`, `e^{-st}`
   being unbounded to the left of the origin, so `ContinuousLinearMap.integral_comp_comm` — which
   discharges (3) outright — does not apply here. The exchange has to be done on causal
   representatives in `[0,∞]`, the move chapter 2's Tonelli identity and `lem:delay-core`'s
   estimate both make. The scalar identity underneath is
   `b₀s + ∫(1-e^{-sr})ν_x(dr) = sF'(xs)`, which is the layer cake again against
   `hasDerivAt_toRealExponent`.
6. (5) wants `mconv_eq_setIntegral_mconv` for a **locally finite** causal measure: `κ^{(x)}` has
   total mass `F'(0+)`, which `prop:moments` has just finished proving may be `⊤`, and the
   existing lemma assumes `IsFiniteMeasure`. Generalising it is the refactor the plan flagged as
   worth making and not yet worth making; this is the consumer that makes it worth making.
   The uniqueness step then looks blocked on signed-measure Laplace injectivity, the development
   having `laplaceL_injective_of_ne_top` for measures — until linearity is used: both operators
   are linear in `f`, and splitting `f'` into positive and negative parts (each in `X₀`, each
   primitive in `𝒟`) reduces to `f' ≥ 0`, where `f` is nondecreasing, `f - T_rf ≥ 0`, and both
   sides of the identity are measures.

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

/-- **`lem:generator-properties`(2), the symbol**: `Lap[φ_x(∂_t)f](s) = φ_x(s) f̂(s)`, with
`φ_x(s) = sF'(xs)` — which is `symbol`, defined in chapter 9.

The clause that pins the definition: it is true of a `ν` with `F`'s tail and of no other, so the
`HasLevyTail` hypothesis is load-bearing and the parameterisation costs nothing in content. -/
theorem laplaceFun_phillipsGenerator (hν : F.HasLevyTail ν) (hx : 0 < x)
    (hAB : HasCoreDerivL1 A B) {s : ℝ} (hs : 0 < s) :
    laplaceFun ((F.phillipsGenerator ν x A B : X) : ℝ → ℝ) s
      = F.symbol x s * laplaceFun ((A : X) : ℝ → ℝ) s := by
  sorry

/-- **`lem:generator-properties`(3), commutation**: `φ_x(∂_t)` commutes with every `Φ_{y,z}` on
`𝒟`.

Stated for an arbitrary causal probability measure, which is what the proof uses and what keeps
the clause off ledger A17. -/
theorem mconvL1_phillipsGenerator (hν : F.HasLevyTail ν) (hx : 0 < x)
    (hAB : HasCoreDerivL1 A B) (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : IsCausal μ) :
    mconvL1 μ (F.phillipsGenerator ν x A B)
      = F.phillipsGenerator ν x (mconvL1 μ A) (mconvL1 μ B) := by
  sorry

/-- **`lem:generator-properties`(4), continuity**: `x ↦ φ_x(∂_t)f` is continuous from `(0,∞)` to
`X₀`. -/
theorem continuousOn_phillipsGenerator (hν : F.HasLevyTail ν) (hAB : HasCoreDerivL1 A B) :
    ContinuousOn (fun y : ℝ => F.phillipsGenerator ν y A B) (Ioi 0) := by
  sorry

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
   fun _ hs => laplaceFun_phillipsGenerator F hν hx hAB hs,
   fun μ _ hμ => mconvL1_phillipsGenerator F hν hx hAB μ hμ,
   continuousOn_phillipsGenerator F hν hAB,
   fun _ _ hfg hA hB => mconv_memoryKernel_ae_eq F hν hx hfg hA hB⟩

end Skeleton
