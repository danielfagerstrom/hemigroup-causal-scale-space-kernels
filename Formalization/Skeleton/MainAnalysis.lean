/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.MainAnalysis

/-!
# The target type of `thm:main-analysis`

**This file carries a `sorry` and is not part of the `Hemigroup` library.**

Unlike the previous entries this library has carried, the `sorry` here does not stand for work
left undone. It stands for a **review decision**, and it is written down so that the decision has
a precise object.

## The whole hypothesis is proved

`Hemigroup/MainAnalysis.lean`'s `CascadeCore.similarity_form` gives, for a family satisfying
(A1)–(A8) and (ND): the gauge `χ`, the convolution representation, the transform in similarity
form `\hat μ_{x,y}(s) = \exp[-(F(χ(y)s) - F(χ(x)s))]` with `F = G(1,\cdot)`, the fact that
`F(b\,\cdot) - F(a\,\cdot) \in \LE` for **all** `0 < a ≤ b`, and `F \not\equiv 0`.

## What the `sorry` stands for

Exactly `lem:selfdecomposable-derivative` in the direction (1) ⇒ (3): a `\LE` function whose
dilation increments are all in `\LE` has a Lévy measure with a nonincreasing density `k(t)/t` —
that is, `F = levyExponentD b₀ k` for some `b₀ ≥ 0` and antitone `k`.

That is a theorem about `BF` as a class of functions, not about hemigroup families. The
blueprint marks it *not intended to be formalised*: (1) ⇒ (2) is closure of `BF` under pointwise
limits applied to a difference quotient (ledger **A4**), and (2) ⇒ (3) needs uniqueness of the
Lévy–Khintchine triple to identify the density (ledger **A3**). Its converse, (3) ⇒ (1), *is*
proved — `SelfDecomposable.levyExponentD_increment` — which is exactly why
`thm:main-construction` stays off both ledger entries while this direction cannot.

So proving `main_analysis` means adding a second line to `blueprint/trust-boundary.txt`. That
file says in its own words that adding a line is a review decision and not a fix, and this is the
first time since A17 that the question has arisen. The alternatives are real: leave the analysis
direction unformalised and keep the trust base at one entry, or take the interface and have
`thm:main-characterization` go green at the cost of two more ledger citations. Nothing in the
Lean forces the choice, which is why it is stated rather than made.
-/

namespace Skeleton

open MeasureTheory Set

open Hemigroup

/-- **`thm:main-analysis`**: every family satisfying (A1)–(A8) and (ND) comes from an admissible
exponent of the form `(7.1)`.

Everything but the last conjunct is `CascadeCore.similarity_form`; the last conjunct is the one
appeal to `lem:selfdecomposable-derivative`. -/
theorem main_analysis (Fam : CascadeCore) {S : ℝ → ℝ → ℝ}
    (hcov : IsScaleCovariant Fam (Ioi 0) S) :
    ∃ χ : ℝ → ℝ, ∃ b₀ : ℝ, ∃ k : ℝ → ℝ,
      χ 0 = 0 ∧ StrictMonoOn χ (Ici 0) ∧ SurjOn χ (Ici 0) (Ici 0) ∧
      0 ≤ b₀ ∧ AntitoneOn k (Ioi 0) ∧ (∀ t, 0 < t → 0 ≤ k t) ∧
      (∀ x y : ℝ, 0 ≤ x → x ≤ y → Fam.Φ x y = mconvL1 (Fam.repr x y)) ∧
      (∀ x y s : ℝ, 0 ≤ x → x ≤ y → 0 ≤ s →
        ENNReal.ofReal (Fam.G 1 (χ y * s) - Fam.G 1 (χ x * s))
          = levyExponentD b₀ k (χ y * s) - levyExponentD b₀ k (χ x * s)) ∧
      (∀ s : ℝ, 0 ≤ s → ENNReal.ofReal (Fam.G 1 s) = levyExponentD b₀ k s) ∧
      (∃ s : ℝ, 0 < s ∧ Fam.G 1 s ≠ 0) := by
  sorry

end Skeleton
