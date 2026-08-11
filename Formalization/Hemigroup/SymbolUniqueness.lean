/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.InversionSymbol

/-!
# Rigidity of the inversion symbol

Blueprint: `lem:symbol-rigidity` (11.15), the transform-level core split out of
`lem:symbol-uniqueness` (11.4) — the node that earns the definite article in *the* inversion.

## What is here and what is not

The draft's Lemma 11.4 runs in two steps of very different cost:

1. *Evaluate both operators on the profiles and take Mellin transforms*, turning the
   eigenfunction relation `A[H(s·)] = s H(s·)` into `B₁(-z) s^{-z} H̃(z) = B₂(-z) s^{-z} H̃(z)`.
   This is `def:inversion-operator`'s transform-level identity, which is exactly what ledger
   **A12** carries — that absolute integrability on the line suffices for the contour integral to
   recover `B(θ)g`. It is not reachable while A12 is blocked upstream.
2. *`H̃ ≠ 0` off an isolated set, so the two symbols agree.* This needs nothing but
   `eventually_mellin_profile_ne_zero`, and it is the step that does the mathematical work: it is
   why the eigenfunction relation pins the symbol rather than merely constraining it.

Step 2 is this file. Step 1 keeps `lem:symbol-uniqueness`'s number and stays unproved, so that
the graph shows the chapter waiting on A12 at the one place it actually does.

## "B₁ = B₂ on the strip" has to say which equality it means

The blueprint concludes `B₁ = B₂ on the strip`, and for the article's symbols that cannot be
pointwise equality of functions: `B(-z) = H̃(z+1)/H̃(z)` is *meromorphic*, with poles at the zeros
of `H̃`, and at a pole a Lean function still has a value — a junk one. So the unconditional
statement is `SameSymbolAction.eventuallyEq`, agreement on a punctured neighbourhood of every
point of the strip, which is what equality of meromorphic functions means and what the article's
"everywhere on the strip by meromorphy" is asserting.

`SameSymbolAction.eqOn` recovers honest pointwise equality, at the price of a continuity
hypothesis that says the symbols have no poles. Both are proved; which one a consumer wants
depends on whether its symbols are analytic, and making the reader choose is the point.
-/

namespace Hemigroup

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent)

/-- Two candidate symbols act identically on the profiles, read through the Mellin transform:
`B₁(z) H̃(z) = B₂(z) H̃(z)` throughout the symbol's strip `0 < Re z < z_* - 1`.

This is the hypothesis `def:inversion-operator` produces from the eigenfunction relation
`A[H(s·)] = s H(s·)`, and it is where `lem:symbol-uniqueness` becomes formalisable: the reduction
*to* this relation is the A12 step, everything *from* it is below. -/
def SameSymbolAction (B₁ B₂ : ℂ → ℂ) : Prop :=
  ∀ w ∈ verticalStrip 0 (F.zStar - 1),
    B₁ w * mellin (fun s => (F.profile s : ℂ)) w
      = B₂ w * mellin (fun s => (F.profile s : ℂ)) w

namespace SameSymbolAction

variable {F} {B₁ B₂ : ℂ → ℂ}

/-- Off the zeros of `H̃` the symbols agree, by cancellation and nothing else. This is the
blueprint's "almost everywhere on the line". -/
theorem eqOn_of_ne_zero (h : F.SameSymbolAction B₁ B₂) :
    EqOn B₁ B₂ {w ∈ verticalStrip 0 (F.zStar - 1) |
      mellin (fun s => (F.profile s : ℂ)) w ≠ 0} := by
  rintro w ⟨hw, hne⟩
  exact mul_right_cancel₀ hne (h w hw)

/-- **`lem:symbol-rigidity`**: the symbols agree near every point of the strip, the point itself
excepted — that is, they are the same meromorphic function.

The zeros of `H̃` are isolated (`eventually_mellin_profile_ne_zero`), so the cancellation above
applies on a punctured neighbourhood of *every* point, including the zeros themselves. No
hypothesis on `B₁` or `B₂` is needed, which is the reason this rather than `eqOn` is the primary
form: the article's symbols have poles exactly where this statement makes no claim about the
value. -/
theorem eventuallyEq (h : F.SameSymbolAction B₁ B₂) (hH : F.StandingHypothesis) {z : ℂ}
    (hz : z ∈ verticalStrip 0 (F.zStar - 1)) : B₁ =ᶠ[𝓝[≠] z] B₂ := by
  have hz' : z ∈ verticalStrip 0 F.zStar := ⟨hz.1, by have := hz.2; linarith⟩
  have hstrip : ∀ᶠ w in 𝓝[≠] z, w ∈ verticalStrip 0 (F.zStar - 1) :=
    nhdsWithin_le_nhds ((isOpen_verticalStrip 0 (F.zStar - 1)).mem_nhds hz)
  filter_upwards [hstrip, F.eventually_mellin_profile_ne_zero hH hz'] with w hw hne
  exact mul_right_cancel₀ hne (h w hw)

/-- At a point where both symbols are continuous — in particular at any point that is a pole of
neither — the agreement is pointwise, the punctured neighbourhood determining the value. -/
theorem eq_of_continuousAt (h : F.SameSymbolAction B₁ B₂) (hH : F.StandingHypothesis) {z : ℂ}
    (hz : z ∈ verticalStrip 0 (F.zStar - 1)) (h₁ : ContinuousAt B₁ z)
    (h₂ : ContinuousAt B₂ z) : B₁ z = B₂ z :=
  tendsto_nhds_unique (h₁.continuousWithinAt.tendsto.congr' (h.eventuallyEq hH hz))
    h₂.continuousWithinAt.tendsto

/-- **`lem:symbol-rigidity`**, the pole-free case: symbols continuous throughout the strip agree
on it outright. This is the blueprint's `B₁ = B₂` read as equality of functions, and it is the
form a consumer with analytic symbols wants. -/
theorem eqOn (h : F.SameSymbolAction B₁ B₂) (hH : F.StandingHypothesis)
    (h₁ : ∀ z ∈ verticalStrip 0 (F.zStar - 1), ContinuousAt B₁ z)
    (h₂ : ∀ z ∈ verticalStrip 0 (F.zStar - 1), ContinuousAt B₂ z) :
    EqOn B₁ B₂ (verticalStrip 0 (F.zStar - 1)) := fun z hz =>
  h.eq_of_continuousAt hH hz (h₁ z hz) (h₂ z hz)

end SameSymbolAction

end SelfDecomposableExponent

end Hemigroup
