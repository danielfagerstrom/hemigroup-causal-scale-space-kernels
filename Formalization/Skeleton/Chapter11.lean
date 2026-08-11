/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.MellinData

/-!
# The target types of chapter 11

`thm:signaling-form` is Theorem 4′, and by the author's account the formulation the article
exists for. This file states the chapter's remaining entry-point clause before proving it, per
the convention that has now caught a missing hypothesis three times in chapter 9 and a
mis-scoped node here.

## Why this chapter is reachable and chapter 10 is not

Checked against the `\uses` graph, 2026-08-11: `thm:signaling-form` uses the standing hypothesis,
`lem:mellin-data`, `def:inversion-operator`, `lem:symbol-uniqueness`,
`lem:memory-fractional-integrals`, `def:cascade-family` and `thm:main-characterization`. **No
chapter 9 node, and no semigroup theory.** Theorem 4′ is not derived from the Sonine pairs; the
Sonine line and the signalling line are parallel developments off the main characterization.
Chapter 10 contributes exactly one node, `lem:delay-core`, and `thm:scale-cauchy` (Theorem 3′) is
a leaf that nothing outside chapter 10 uses — so Mathlib's missing semigroup theory blocks the
leaf and not the article.

## What has moved out of this file — **2026-08-11**

`lem:mellin-data`'s first two clauses are proved and live in `Hemigroup/MellinData.lean`:

* `Hemigroup.SelfDecomposableExponent.mellin_profile` — the identity `H̃(z) = Γ(z) E[T₁^{-z}]`;
* `Hemigroup.SelfDecomposableExponent.norm_mellin_profile_le` — the bound.

Both came out of the one `ℝ≥0∞` computation `lintegral_lintegral_gamma`, which is the Fubini
side condition, the bound, and the finiteness under vertical integrability all at once; and both
reduce to Lean core. Writing the statement first paid again: it showed that the exchange of
integrals is licensed *exactly* by `Re z < z_*` (so no new hypothesis was invented), and that the
first clause of (H) is load-bearing rather than decorative — without `μ{0} = 0` the hinge is
false, because the inner Gamma integral diverges at an atom that `negMoment`, restricted to
`(0,∞)`, cannot see.

## What is left, and why — **ledger A12's retirement is blocked upstream, not here**

The blueprint's `lem:mellin-data` also concludes that `H̃` is absolutely integrable on every
vertical line of the strip. That clause is worth more than the other two, because
`Complex.VerticalIntegrable (mellin H) c` is **verbatim** the hypothesis Mathlib's
`mellinInv_mellin_eq` asks for: proving it is what would turn ledger A12 from a cited interface
into a theorem. It has been split off as its own blueprint node (`lem:mellin-vertical`, 11.13)
under the chapter-7 convention, because it costs differently from the two clauses above.

**And it does not follow from the bound inside Mathlib as it stands.** The bound is
`|H̃(c+iτ)| ≤ E[T₁^{-c}] · |Γ(c+iτ)|`; integrating it in `τ` needs the super-polynomial decay of
`|Γ(c+iτ)|`. Mathlib has no such estimate — `Analysis/SpecialFunctions/Stirling.lean` is
Stirling's formula for `n !` alone, and there is no bound on `‖Complex.Gamma‖` along a vertical
line anywhere in the library.

This sharpens the A12 assessment recorded in `blueprint/AXIOMS.md` a third time, and in a way
worth stating plainly, because the previous two both got the *location* of the difficulty wrong.
The correction of 2026-08-11 concluded that A12 is retirable "at a formalisation cost, not a
mathematical one", the remaining pieces being the operator formulation and `ContinuousAt`. That
is right about the article and incomplete about Lean: the vertical integrability the correction
described as *already proved by* `lem:mellin-data` is proved there by an estimate on `Γ` that
Mathlib does not have. So A12's retirement is blocked on an upstream gap — a queue item for
Mathlib, not a decision about this article — and that is a different kind of obstacle from either
earlier reading.
-/

namespace Skeleton

open MeasureTheory Set Filter
open scoped ENNReal Topology

open Hemigroup Hemigroup.SelfDecomposableExponent

variable (F : Hemigroup.SelfDecomposableExponent)

/-- **`lem:mellin-vertical`** (11.13), the consequence ledger A12's retirement turns on: the
profile's transform is absolutely integrable on every vertical line of the strip.

This is `norm_mellin_profile_le` together with the super-polynomial decay of `|Γ(c+iτ)|`. It is
stated separately, and in Mathlib's own vocabulary, because it is exactly the hypothesis
`mellinInv_mellin_eq` asks for — so this node is the bridge between the chapter and the inversion
theorem.

**Blocked on Mathlib, not on the article.** See the module docstring: the missing input is a
bound on `‖Complex.Gamma (c + τ * I)‖` as `|τ| → ∞`, which the library does not carry in any
form. Everything on this side of that estimate is done. -/
theorem verticalIntegrable_mellin_profile (hH : F.StandingHypothesis) {c : ℝ} (hc : 0 < c)
    (hc' : c < F.zStar) :
    Complex.VerticalIntegrable (mellin (fun s => (F.profile s : ℂ))) c := by
  sorry

end Skeleton
