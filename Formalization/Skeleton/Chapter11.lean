/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.Sonine
import Mathlib.Analysis.MellinInversion

/-!
# The target types of chapter 11

`thm:signaling-form` is Theorem 4′, and by the author's account the formulation the article
exists for. This file states the chapter's entry point before proving it, per the convention that
has now caught a missing hypothesis three times in chapter 9.

## Why this chapter is reachable and chapter 10 is not

Checked against the `\uses` graph, 2026-08-11: `thm:signaling-form` uses the standing hypothesis,
`lem:mellin-data`, `def:inversion-operator`, `lem:symbol-uniqueness`,
`lem:memory-fractional-integrals`, `def:cascade-family` and `thm:main-characterization`. **No
chapter 9 node, and no semigroup theory.** Theorem 4′ is not derived from the Sonine pairs; the
Sonine line and the signalling line are parallel developments off the main characterization.
Chapter 10 contributes exactly one node, `lem:delay-core`, and `thm:scale-cauchy` (Theorem 3′) is
a leaf that nothing outside chapter 10 uses — so Mathlib's missing semigroup theory blocks the
leaf and not the article.

## Ledger A12 is retirable

Mathlib has `Analysis/MellinInversion.lean`. Its `mellinInv_mellin_eq` assumes
`Complex.VerticalIntegrable (mellin f) σ` — absolute convergence of the *inversion* integral — where
Widder's Theorem 9a takes a symmetric limit and so covers conditionally convergent ones. That
looked like a gap and is not one: `def:inversion-operator` **already** quantifies over `g` with
`B(-z) g̃(z)` absolutely integrable on the line, so the article imposes Mathlib's hypothesis
itself. See `blueprint/AXIOMS.md` A12 for the full comparison and the correction it records.

What makes the absolute integrability available is the `Γ` factor below: `H̃(z) = Γ(z) E[T₁^{-z}]`
and `|Γ(c+iτ)|` decays super-polynomially. The *symbol* `B` alone grows — the `Γ`s cancel in the
ratio `H̃(z+1)/H̃(z)` — but `B` is never inverted alone; it multiplies a transform carrying the
decay, and the product is `H̃(z+1)`, which decays again.

## Design decisions this file takes

* **`T₁` is `F.kernel 0 1`**, the kernel `μ_{0,1}` the construction already produces, with
  `kernel_spec` giving `laplace (F.kernel 0 1) s = exp(-F(s))`. No new object is introduced, and
  in particular the density `φ₁` is *not* — the chapter's Mellin data is a statement about the
  law, and `prop:pair-regularity`'s absolute continuity (ledger A9) is not needed to state it.
* **The profile is the Laplace transform, not the density.** `H(s) = E[e^{-sT₁}]`, so `H̃` is the
  Mellin transform of a function `ℝ → ℝ` and Mathlib's `mellin` applies directly.
* **Negative moments are `ℝ≥0∞`-valued.** `E[T₁^{-ζ}]` is exactly the quantity that may diverge —
  `z_*` is defined by where it stops being finite — so carrying it in `[0,∞]` keeps `z_*`
  definable without a side condition. Same reason `levyExponent` is `ℝ≥0∞`-valued, and chapter 9
  is a cautionary tale about departing from it: `sonine_conservation`'s specification was stated
  with a Bochner integral and was wrong, because a Bochner integral reads `0` where the true
  value is `⊤`.
-/

namespace Skeleton

open MeasureTheory Set Filter
open scoped ENNReal Topology

open Hemigroup Hemigroup.SelfDecomposableExponent

variable (F : Hemigroup.SelfDecomposableExponent)

/-! ## The objects of `lem:mellin-data` -/

/-- The law of `T₁`: the kernel `μ_{0,1}` of the construction. -/
noncomputable def lawT₁ : Measure ℝ := F.kernel 0 1

/-- **The profile** `H(s) = E[e^{-sT₁}]`, whose Mellin transform the chapter is about. -/
noncomputable def profile (s : ℝ) : ℝ := laplace (lawT₁ F) s

/-- **The negative moment** `E[T₁^{-ζ}]`, in `[0,∞]` because divergence is the point. -/
noncomputable def negMoment (ζ : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-ζ)) ∂(lawT₁ F)

/-- **`z_*`**, the abscissa beyond which the negative moments diverge. -/
noncomputable def zStar : ℝ := sSup {ζ : ℝ | 0 < ζ ∧ negMoment F ζ ≠ ⊤}

/-- **The standing hypothesis (H)**, `def:standing-hypothesis`: no atom at zero delay, and the
negative moments survive past the first. -/
def StandingHypothesis : Prop :=
  Filter.Tendsto F.toRealExponent atTop atTop ∧ 1 < zStar F

/-! ## `lem:mellin-data`

The chapter's entry point, and the one node here whose substrate is entirely in place: Tonelli
plus the Gamma integral, both of which the development already uses.
-/

/-- **`lem:mellin-data`**, the identity: `H̃(z) = Γ(z) · E[T₁^{-z}]` on the strip.

The proof is Fubini on `∫₀^∞ s^{z-1} ∫ e^{-st} dμ(t) ds`, exchanging to
`∫ (∫₀^∞ s^{z-1} e^{-st} ds) dμ(t) = ∫ Γ(z) t^{-z} dμ(t)`.

**The inner integral is already in Mathlib**, as `Complex.integral_cpow_mul_exp_neg_mul_Ioi`:
`0 < a.re → 0 < r → ∫ t in Ioi 0, (t:ℂ)^(a-1) * exp (-(r*t)) = (1/r)^a * Gamma a`. Taking
`a = z` and `r = t` gives `(1/t)^z · Γ(z)`, which is `Γ(z) · t^{-z}` for `t > 0`. So no
substitution is needed and the Gamma function enters as Mathlib's, not as a definition of ours.

**The side condition is the strip condition, not an extra hypothesis.** Fubini needs the
uncurried integrand integrable for `volume.restrict (Ioi 0) ⊗ lawT₁`, and its absolute value
integrates to

  `∫∫ s^{c-1} e^{-st} ds dμ(t) = Γ(c) · ∫ t^{-c} dμ(t) = Γ(c) · negMoment c`,

by the same Mathlib lemma applied to the real part. So joint integrability holds **iff**
`negMoment c ≠ ⊤`, which is exactly `c < zStar`. This is the same shape as chapter 8's
`prop:admissibility-criterion`: the condition that makes the analysis go through turns out to be
characteristic rather than merely sufficient, and recognising that is what keeps a hypothesis
from being invented. Prove the `ℝ≥0∞` computation first and both the exchange and the bound
below fall out of it. -/
theorem mellin_profile (hH : StandingHypothesis F) {z : ℂ} (hz : 0 < z.re)
    (hz' : z.re < zStar F) :
    mellin (fun s => (profile F s : ℂ)) z = Complex.Gamma z * ∫ t, (t : ℂ) ^ (-z) ∂(lawT₁ F) := by
  sorry

/-- **`lem:mellin-data`**, the bound: `|H̃(c+iτ)| ≤ E[T₁^{-c}] · |Γ(c+iτ)|`.

Immediate from the identity, since `|t^{-(c+iτ)}| = t^{-c}` for `t > 0`. -/
theorem norm_mellin_profile_le (hH : StandingHypothesis F) {c : ℝ} (hc : 0 < c)
    (hc' : c < zStar F) (τ : ℝ) :
    ‖mellin (fun s => (profile F s : ℂ)) (c + τ * Complex.I)‖
      ≤ (negMoment F c).toReal * ‖Complex.Gamma (c + τ * Complex.I)‖ := by
  sorry

/-- **`lem:mellin-data`**, the consequence ledger A12's retirement turns on: the profile's
transform is absolutely integrable on every vertical line of the strip.

This is the bound above together with the super-polynomial decay of `|Γ(c+iτ)|`. It is stated
separately, and in Mathlib's own vocabulary, because it is exactly the hypothesis
`mellinInv_mellin_eq` asks for — so this node is the bridge between the chapter and the
inversion theorem, and the reason A12 costs formalisation rather than a new assumption. -/
theorem verticalIntegrable_mellin_profile (hH : StandingHypothesis F) {c : ℝ} (hc : 0 < c)
    (hc' : c < zStar F) :
    Complex.VerticalIntegrable (mellin (fun s => (profile F s : ℂ))) c := by
  sorry

end Skeleton
