/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.Ein

/-!
# The target types of chapter 7's appended nodes

**This file carries `sorry`s and is not part of the `Hemigroup` library.**

`prop:extreme-rays` (7.7) asserted four things at four prices — the cone, the `Ein`
superposition, injectivity of `(b₀,ρ) ↦ F`, and the extreme rays — and reported the maximum. It
is the Lemma 7.1 shape for the third time in this chapter, so it has been narrowed in place and
the two cheap clauses appended as `lem:admissible-cone` (7.13) and `lem:dickman-superposition`
(7.14). Their target types are here.

## What stays behind in 7.7, and why

**Injectivity** is uniqueness of the Lévy–Khintchine triple, which is how the blueprint's proof
reaches it — ledger A3, quantifying over `BF`, which this development has no vocabulary for. It is
*plausibly* avoidable: `hasDerivAt_toRealExponent` gives `F'(s) = b₀ + ∫e^{-st}k(t)dt`, and
`laplaceL_injective_of_ne_top` is Laplace injectivity for locally finite measures, so `F`
determines `k` a.e. with no statement about `BF` at all. That is a piece of work in its own right
and it is not attempted here; it is recorded in the node's annotation so the next reader does not
have to rediscover that the citation overstates the obligation. Same shape as chapter 9's Route B,
which replaced Bernstein–Widder by a construction.

**The extreme rays** need a Choquet argument, and the obstruction is not that Mathlib lacks
`IsExtreme` — it has it. It is that `ρ = ∫ δ_τ ρ(dτ)` has to be read as a barycentre in a cone of
measures, which is a theory the development would have to build.

## The two statements, and why they are existential

Neither names the construction that discharges it. `admissible_cone` says a sum *exists* with the
right data and the right exponent rather than naming `SelfDecomposableExponent.add`, and
`dickman_superposition` says a measure with tail `k` *exists* rather than naming the quantile
transform of `Hemigroup/Subordinator.lean` that will build it. That is the rule chapter 9's Route B
paid to learn — **a decomposition should say what each piece must achieve, not with what** — and
here it costs nothing, since the definitions move into the library when the proofs land.
-/

namespace Skeleton

open MeasureTheory Set

open scoped ENNReal

open Hemigroup

/-- **`lem:admissible-cone` (7.13).** The admissible exponents are closed under addition and
under multiplication by a nonnegative scalar, and the correspondence with the data `(b₀, k)` is
linear. -/
theorem admissible_cone (F G : SelfDecomposableExponent) {c : ℝ} (hc : 0 ≤ c) :
    (∃ H : SelfDecomposableExponent, H.b₀ = F.b₀ + G.b₀ ∧ H.k = F.k + G.k ∧
        ∀ s : ℝ, 0 ≤ s → H.exponent s = F.exponent s + G.exponent s) ∧
      (∃ H : SelfDecomposableExponent, H.b₀ = c * F.b₀ ∧ H.k = c • F.k ∧
        ∀ s : ℝ, 0 ≤ s → H.exponent s = ENNReal.ofReal c * F.exponent s) := by
  sorry

/-- **`lem:dickman-superposition` (7.14).**

(1) The Dickman ray of delay `τ` has exponent `Ein(τs)` — the closed form `Examples.lean` recorded
as absent, which it is only in the sense that `Ein` is not elementary. (2) Every admissible
exponent is drift plus a superposition of Dickman rays against the tail measure `-dk`. -/
theorem dickman_superposition :
    (∀ τ : ℝ, 0 < τ → ∀ s : ℝ, 0 ≤ s →
        (dickmanExponent τ).exponent s = ENNReal.ofReal (ein (τ * s))) ∧
      (∀ F : SelfDecomposableExponent, ∃ ρ : Measure ℝ,
        ρ (Iic 0) = 0 ∧
        (∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ρ (Ioi t) = ENNReal.ofReal (F.k t)) ∧
        ∀ s : ℝ, 0 ≤ s →
          F.exponent s
            = ENNReal.ofReal (F.b₀ * s) + ∫⁻ τ, ENNReal.ofReal (ein (τ * s)) ∂ρ) := by
  sorry

end Skeleton
