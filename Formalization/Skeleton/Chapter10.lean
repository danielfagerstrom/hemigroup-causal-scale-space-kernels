/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.DelayCore

/-!
# The target types of chapter 10

**This file carries `sorry`s and is not part of the `Hemigroup` library.** What is stated here is
`lem:delay-core` (Lemma 10.1) and nothing else: the setting it is about — `X₀`, `T_r`, `𝒟` — is
defined and its elementary theory proved in `Hemigroup/DelayCore.lean`, because definitions carry
no claim and the chapter needs them before it needs a theorem.

## Why chapter 10 at all, given that nothing waits on it

Nothing does. `thm:signaling-form` is complete, and the round that completed it found that chapter
11 uses none of 10.1's content — density, `T_r`-invariance and `Φ`-invariance are cited by the
draft's proof and needed by no statement. So this node discharges `\uses` edges rather than
unblocking anything, and it is worth doing for two reasons that are not "the graph": `𝒟` has been
named in three chapters and defined in none, and the rest of chapter 10 (`def:phillips-generator`,
`lem:generator-properties`) is *stated on `𝒟`* — so the setting is the part of chapter 10 that is
not blocked on the C₀-semigroup theory Mathlib lacks.

## The modelling decision, and where it is checked

`X₀` is a predicate on `X = L¹(ℝ)` and `𝒟` is primarily a predicate on genuine functions; both
choices, and the reasons, are in `Hemigroup/DelayCore.lean`'s module docstring. The check that the
choice is right is `memCore_iff_signaling_hypotheses`, an `iff` between `HasCoreDeriv f g` and the
six hypotheses `thm:signaling-form` takes about its signal. Chapter 11 was written by taking those
six as hypotheses because `𝒟` did not exist; the `iff` says the definition now supplies exactly
them — neither less (which would leave chapter 11 unable to cite `f ∈ 𝒟`) nor more (which would
mean chapter 10 had quietly strengthened the class its siblings quantify over).

## The five clauses, and what each is expected to cost

The collation `delay_core` is `sorry`-free and rests on the five named sub-lemmas below, which is
article-kit's decomposition gate.

1. `dense_coreL1` — density in `X₀`. The blueprint says "standard", and the cheap route is not
   the standard one: the usual proof approximates by smooth or step functions, of which the step
   functions are not in `𝒟` at all. The mollification `f_h := h⁻¹ 1_{[0,h]} ∗ f` is in `𝒟`
   outright, with derivative `h⁻¹(f - T_h f) ∈ X₀`, and converges to `f` by continuity of
   translation in `L¹` — the same fact clause 4 needs, so the two share their one real input.
2. `hasCoreDerivL1_transL1` — invariance under `T_r`. Stated as `(T_r f)' = T_r f'` rather than as
   `T_r f ∈ 𝒟`, because that is what the blueprint's proof establishes and what
   `def:phillips-generator` will consume.
3. `hasCoreDerivL1_mconvL1` — invariance under `Φ_{x,y}`, at the level
   `lem:convolution-representation` supplies it: a causal probability measure, not an abstract
   family. That is the honest content of the node's `\uses` edge; reading it back onto a
   `CascadeCore` is the representation theorem and not this lemma.
4. `tendsto_differenceQuotient` — `(T_h f - f)/h → -f'` in `X₀`. Continuity of translation in `L¹`
   is the input; the blueprint's `[0,h)` boundary term is where `f(0) = 0` is used, and it is the
   only clause that uses it.
5. `norm_transL1_sub_le` — the two-sided estimate. The `2‖f‖₁` half is the triangle inequality
   and the isometry; the `r‖f'‖₁` half is the integrated form of clause 4, i.e. a Bochner
   integral `T_r f - f = -∫₀^r T_ρ f' dρ`.

Clause 1 is the one to attempt first even though it is stated first for the blueprint's reasons:
its mollifier is the same object as clause 4's difference quotient, so the two are one piece of
work seen from two sides, and clause 5 follows clause 4.
-/

namespace Skeleton

open MeasureTheory Set Filter

open scoped Topology

open Hemigroup

/-! ## `lem:delay-core` (10.1) -/

/-- **Density.** `𝒟` is dense in `X₀`.

Stated as `X₀ ⊆ closure 𝒟` rather than with `Dense`, which would ask for density in `X`: `𝒟` is
not dense in `X`, and `coreL1_subset_causalL1` is the half of that already proved. -/
theorem dense_coreL1 : causalL1 ⊆ closure coreL1 := by
  sorry

/-! Clauses 2 and 3 — invariance under `T_r` and under `Φ_{x,y}` — are **proved**, and have moved
to `Hemigroup/DelayCore.lean` as `hasCoreDerivL1_transL1` and `hasCoreDerivL1_mconvL1`. -/

/-- **The difference quotient**: `h⁻¹(T_h f - f) → -f'` in `X₀` as `h ↓ 0`. -/
theorem tendsto_differenceQuotient {F G : X} (h : HasCoreDerivL1 F G) :
    Tendsto (fun r : ℝ => r⁻¹ • (transL1 r F - F)) (𝓝[>] (0 : ℝ)) (𝓝 (-G)) := by
  sorry

/-- **The estimate**: `‖T_r f - f‖₁ ≤ min(2‖f‖₁, r‖f'‖₁)`. -/
theorem norm_transL1_sub_le {r : ℝ} (hr : 0 ≤ r) {F G : X} (h : HasCoreDerivL1 F G) :
    ‖transL1 r F - F‖ ≤ min (2 * ‖F‖) (r * ‖G‖) := by
  sorry

/-- **`lem:delay-core` (Lemma 10.1).** `𝒟` is dense in `X₀` and invariant under every `T_r` and
every `Φ_{x,y}`, the difference quotient converges to `-f'` in `X₀`, and the delay of a core
element is controlled two ways.

The collation the node carries. Its parts are the five lemmas above; this statement is where the
graph's edge to `lem:convolution-representation` is discharged, since the `Φ`-clause is stated for
the convolution operators that node produces. -/
theorem delay_core :
    causalL1 ⊆ closure coreL1 ∧
      (∀ r : ℝ, 0 ≤ r → ∀ F ∈ coreL1, transL1 r F ∈ coreL1) ∧
      (∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], IsCausal μ → ∀ F ∈ coreL1,
        mconvL1 μ F ∈ coreL1) ∧
      (∀ F G : X, HasCoreDerivL1 F G →
        Tendsto (fun r : ℝ => r⁻¹ • (transL1 r F - F)) (𝓝[>] (0 : ℝ)) (𝓝 (-G))) ∧
      (∀ r : ℝ, 0 ≤ r → ∀ F G : X, HasCoreDerivL1 F G →
        ‖transL1 r F - F‖ ≤ min (2 * ‖F‖) (r * ‖G‖)) :=
  ⟨dense_coreL1,
   fun _ hr _ ⟨G, hG⟩ => ⟨transL1 _ G, hasCoreDerivL1_transL1 hr hG⟩,
   fun μ _ hμ _ ⟨G, hG⟩ => ⟨mconvL1 μ G, hasCoreDerivL1_mconvL1 μ hμ hG⟩,
   fun _ _ h => tendsto_differenceQuotient h,
   fun _ hr _ _ h => norm_transL1_sub_le hr h⟩

end Skeleton
