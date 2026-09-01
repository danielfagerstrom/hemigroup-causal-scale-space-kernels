/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the MIT license as described in the file LICENSES/MIT.txt.
Authors: Daniel Fagerström
-/
import Hemigroup.InversionOperator

/-!
# Rigidity of the inversion symbol

Blueprint: `lem:symbol-rigidity` (11.15), the transform-level core split out of
`lem:symbol-uniqueness` (11.4) — the node that earns the definite article in *the* inversion.

## Both steps of Lemma 11.4 are here

The draft's Lemma 11.4 runs in two steps of very different cost:

1. *Evaluate both operators on the profiles and take Mellin transforms*, turning the
   eigenfunction relation `A[H(s·)] = s H(s·)` into `B₁(-z) s^{-z} H̃(z) = B₂(-z) s^{-z} H̃(z)`.
2. *`H̃ ≠ 0` off an isolated set, so the two symbols agree.* This needs nothing but
   `eventually_mellin_profile_ne_zero`, and it is the step that does the mathematical work: it is
   why the eigenfunction relation pins the symbol rather than merely constraining it.

Step 2 was proved first, as `lem:symbol-rigidity` (11.15), when step 1 was thought to be waiting
on ledger A12. It was not: what A12 was left carrying is the *production* of `B(θ)g`, and an
operator "of the form `x⁻¹B(θ)`" is one whose `B(θ)g` is given rather than produced. That is
`RealisesAction`, and step 1 is `sameSymbolAction_of_realisesAction` below.

**The route needs no injectivity of the inverse Mellin transform**, which is the obvious thing to
reach for and would be a second citation. Two operators agreeing on `H(s·)` have the *same*
realising function there — `x⁻¹h₁ = x⁻¹h₂` is `h₁ = h₂` on `(0,∞)` — so their transforms agree at
every point, and the symbols can be read off directly. The realising function carries the
information that injectivity would otherwise have to recover.

**One dilation suffices.** The blueprint quantifies the eigenfunction relation over all `s > 0`;
the proof uses a single `s`, because the dilate contributes only the factor `s^{-z}`, which never
vanishes and cancels. So the hypothesis below fixes `s`, and the quantified form is strictly
weaker information than it appears to be.

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
  have hz' : z ∈ verticalStrip 0 F.zStar := ⟨hz.1, lt_of_lt_sub_one hz.2⟩
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

/-! ## `lem:symbol-uniqueness`, step 1: from the operator relation to the transform relation -/

/-- **`lem:symbol-uniqueness`, step 1.** If two symbols act on one dilate `H(s·)` through the
*same* realising function — which is what it means for the two operators `x⁻¹B₁(θ)` and
`x⁻¹B₂(θ)` to agree there, and in particular what the eigenfunction relation
`A_i[H(s·)] = s H(s·)` says — then they act identically on the profile throughout the strip.

Feeding `lem:symbol-rigidity` (`SameSymbolAction.eventuallyEq`) completes `lem:symbol-uniqueness`.

Two things about the proof are worth naming. It uses no injectivity of the inverse Mellin
transform: the shared realising function `h` has one transform, so `B₁ w · g̃(w) = h̃(w) =
B₂ w · g̃(w)` at every point where the identity holds, and `g̃(w) = s^{-w}H̃(w)` cancels its
nonvanishing factor. And the conclusion is pointwise on the whole strip, including the zeros of
`H̃`, where both sides are `0` — which is why `RealisesAction.mellin_eq` is conditioned on
`H̃ ≠ 0` rather than merely holding almost everywhere. An a.e. hypothesis would conclude nothing
at any named point. -/
theorem sameSymbolAction_of_realisesAction {s : ℝ} (hs : 0 < s) {B₁ B₂ : ℂ → ℂ}
    (h₁ : ∀ c : ℝ, 0 < c → ENNReal.ofReal (c + 1) < F.zStar →
      F.RealisesAction c B₁ (fun u : ℝ => (F.profile (s * u) : ℂ))
        (fun x : ℝ => (s : ℂ) * (x : ℂ) * (F.profile (s * x) : ℂ)))
    (h₂ : ∀ c : ℝ, 0 < c → ENNReal.ofReal (c + 1) < F.zStar →
      F.RealisesAction c B₂ (fun u : ℝ => (F.profile (s * u) : ℂ))
        (fun x : ℝ => (s : ℂ) * (x : ℂ) * (F.profile (s * x) : ℂ))) :
    F.SameSymbolAction B₁ B₂ := by
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  intro w hw
  by_cases hne : mellin (fun u => (F.profile u : ℂ)) w = 0
  · rw [hne, mul_zero, mul_zero]
  obtain ⟨hw0, hw1⟩ := hw
  have hre : ((w.re : ℂ) + (w.im : ℝ) * Complex.I) = w := Complex.re_add_im w
  have hgw : mellin (fun u : ℝ => (F.profile (s * u) : ℂ)) w
      = (s : ℂ) ^ (-w) * mellin (fun u => (F.profile u : ℂ)) w :=
    F.mellin_profile_comp_mul hs w
  have key : ∀ B : ℂ → ℂ,
      (∀ c : ℝ, 0 < c → ENNReal.ofReal (c + 1) < F.zStar →
        F.RealisesAction c B (fun u : ℝ => (F.profile (s * u) : ℂ))
          (fun x : ℝ => (s : ℂ) * (x : ℂ) * (F.profile (s * x) : ℂ))) →
      mellin (fun x : ℝ => (s : ℂ) * (x : ℂ) * (F.profile (s * x) : ℂ)) w
        = B w * mellin (fun u : ℝ => (F.profile (s * u) : ℂ)) w := by
    intro B hB
    have := (hB w.re hw0 (ofReal_add_one_lt_of_lt_sub_one hw0.le hw1)).mellin_eq w.im
      (by rwa [hre])
    rwa [hre] at this
  have heq : B₁ w * mellin (fun u : ℝ => (F.profile (s * u) : ℂ)) w
      = B₂ w * mellin (fun u : ℝ => (F.profile (s * u) : ℂ)) w :=
    (key B₁ h₁).symm.trans (key B₂ h₂)
  have hspow : (s : ℂ) ^ (-w) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    rintro ⟨h0, -⟩
    exact hs0 h0
  refine mul_right_cancel₀ hspow ?_
  rw [hgw] at heq
  calc B₁ w * mellin (fun u => (F.profile u : ℂ)) w * (s : ℂ) ^ (-w)
      = B₁ w * ((s : ℂ) ^ (-w) * mellin (fun u => (F.profile u : ℂ)) w) := by ring
    _ = B₂ w * ((s : ℂ) ^ (-w) * mellin (fun u => (F.profile u : ℂ)) w) := heq
    _ = B₂ w * mellin (fun u => (F.profile u : ℂ)) w * (s : ℂ) ^ (-w) := by ring

/-- **`lem:symbol-uniqueness`.** `A` is the unique inversion within the covariant Mellin class:
any symbol `B` whose operator satisfies the eigenfunction relation agrees with `F.inversionSymbol`
on a punctured neighbourhood of every point of the strip — that is, as a meromorphic function.

The article's own symbol qualifies, by `realisesSymbolAction_profile`; so the statement is not
vacuous, and the definite article in "*the* inversion" is earned. -/
theorem eventuallyEq_inversionSymbol_of_realisesAction (hH : F.StandingHypothesis) {s : ℝ}
    (hs : 0 < s) {B : ℂ → ℂ}
    (hB : ∀ c : ℝ, 0 < c → ENNReal.ofReal (c + 1) < F.zStar →
      F.RealisesAction c B (fun u : ℝ => (F.profile (s * u) : ℂ))
        (fun x : ℝ => (s : ℂ) * (x : ℂ) * (F.profile (s * x) : ℂ)))
    {z : ℂ} (hz : z ∈ verticalStrip 0 (F.zStar - 1)) :
    F.inversionSymbol =ᶠ[𝓝[≠] z] B :=
  (F.sameSymbolAction_of_realisesAction hs
    (fun c hc hc' => F.realisesSymbolAction_profile hH hc hc' hs) hB).eventuallyEq hH hz

end SelfDecomposableExponent

end Hemigroup
