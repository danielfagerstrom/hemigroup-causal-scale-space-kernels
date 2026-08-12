/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.InversionOperator
import Hemigroup.Locality
import Hemigroup.MellinEuler

/-!
# The target types of chapter 12

**This file carries `sorry`s and is not part of the `Hemigroup` library.**

## What is already proved, and lives under `Hemigroup/`

| node | declaration | file |
|---|---|---|
| `lem:log-convexity` (12.4) | `convexOn_log_negMoment` | `Locality.lean` |
| `lem:symbol-vanishes-at-origin` (12.9) | `tendsto_inversionSymbol_nhdsGT_zero` | `Locality.lean` |
| `lem:gamma-recursion-uniqueness` (12.10) | `eq_gamma_form_of_logConvex_of_recursion` | `GammaRecursion.lean` |
| — (the engine of 12.2) | `mellin_pow_mul_iteratedDeriv` | `MellinEuler.lean` |

`IsTestFunction` and `mellinEulerFactor` moved to `MellinEuler.lean` with that last one: they are
no longer target types but the vocabulary of a proved theorem.

What remains here is chapter 12's structural layer --- `def:locality-pmp` and
`lem:local-polynomial-symbol` --- where the work is not analytic but definitional, and where
writing the statement is most of the decision.

## The modelling choice, and why it went this way

The blueprint's Definition 12.1 reads: `A` is *local of order `n`* if it agrees on
`C_c^∞((0,∞))` with a differential expression `∑_{j≤n} c_j(x) ∂_x^j` with `c_j` continuous and
`c_n ≢ 0`. That can be rendered either as a bare `Prop` --- an existential over the coefficients
--- or as a **structure bundling them**, which is what `IsLocalOfOrder` below does.

Bundling is not the literal transcription, and the reason to prefer it is
`lem:local-polynomial-symbol`, whose conclusion is a statement *about the coefficients*:
`c_j(x) = γ_j x^{j-1}`. Under the `Prop` reading that conclusion cannot be stated without first
re-introducing an existential and then asserting something inside it, so every downstream use
would `obtain` the coefficients again and would have no way to say that the `c_j` it obtained are
the same ones. With the structure they are fields, `hL.coeff j`, and the lemma says what the
blueprint says.

The cost is that `IsLocalOfOrder` is data, so two proofs of locality are not definitionally
equal. Nothing in the chapter compares them, and the leading-coefficient condition --- which is
what makes the *order* well defined --- is a field rather than a side condition, which is if
anything clearer.

The one place the cost is visible is that the (⇐) direction cannot be a `theorem` returning
`F.IsLocalOfOrder c n`, that type being data rather than a proposition. It returns
`Nonempty (F.IsLocalOfOrder c n)`, which is the `Prop` reading of "A is local of order n" and is
what `thm:locality` quantifies over; a caller that needs the coefficients themselves takes the
structure instead. Both are available and neither is the default in disguise.

## The reading of the maximum principle

`inversionOperator` is `ℂ`-valued, and `(Ag)(x₀) ≤ 0` is not a statement about a complex number.
`SatisfiesPMP` below quantifies over real-valued test functions and asserts the inequality of the
*real part*. That is the intended content --- in the application `A` maps real functions to real
functions --- but it is a choice, and stating it as `.re ≤ 0` rather than proving realness first
is the weaker and therefore safer of the two.

(The other reading that had to be fixed, `C_c^∞((0,∞))` meaning `tsupport g ⊆ Ioi 0` rather than
mere compact support, is now recorded where it is spent: `MellinEuler.lean`'s docstring, since
that is the file whose integrations by parts would otherwise acquire a boundary term.)

## What the remaining work is

The (⇐) direction now needs no analysis: `mellin_pow_mul_iteratedDeriv` is proved, and what is
left is to run it through `mellin_inversionOperator_eq` and Mellin injectivity. The (⇒) direction
needs in addition that a differential expression is determined by its coefficients, which is a
prescribed-jet test-function construction and is the chapter's largest remaining item.
-/

namespace Hemigroup

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent)

/-- **`def:locality-pmp`, the locality half.** `A` is *local of order `n`* at height `c`.

A structure rather than a `Prop`, so that `lem:local-polynomial-symbol` can say what the
blueprint says about *these* coefficients. -/
structure IsLocalOfOrder (c : ℝ) (n : ℕ) where
  /-- The coefficients `c_j` of the differential expression. -/
  coeff : ℕ → ℝ → ℂ
  /-- Each is continuous on the half-line. -/
  continuousOn_coeff : ∀ j, ContinuousOn (coeff j) (Ioi 0)
  /-- The leading coefficient does not vanish identically, which is what fixes the order. -/
  leading_ne_zero : ∃ x₀ : ℝ, 0 < x₀ ∧ coeff n x₀ ≠ 0
  /-- Agreement with the differential expression, on the test class and on the half-line. -/
  eq_sum_iteratedDeriv : ∀ {g : ℝ → ℂ}, IsTestFunction g → ∀ {x : ℝ}, 0 < x →
    F.inversionOperator c g x = ∑ j ∈ Finset.range (n + 1), coeff j x * iteratedDeriv j g x

/-- **`def:locality-pmp`, the maximum-principle half**, in its real-valued reading. -/
def SatisfiesPMP (c : ℝ) : Prop :=
  ∀ {g : ℝ → ℝ}, IsTestFunction (fun x => (g x : ℂ)) → ∀ {x₀ : ℝ}, 0 < x₀ → 0 ≤ g x₀ →
    (∀ x : ℝ, 0 < x → g x ≤ g x₀) →
      (F.inversionOperator c (fun x => (g x : ℂ)) x₀).re ≤ 0

/-- **`lem:local-polynomial-symbol`, the (⇐) direction.** A polynomial symbol, expanded in
falling factorials, gives a differential expression whose coefficients are `γ_j x^{j-1}`. -/
theorem isLocalOfOrder_of_symbol_eq (hH : F.StandingHypothesis) {c : ℝ} (hc : 0 < c)
    (hc' : c < F.zStar - 1) {n : ℕ} (γ : ℕ → ℂ) (hγ : γ n ≠ 0)
    (hsymbol : ∀ z : ℂ, 0 < z.re → z.re < F.zStar - 1 →
      F.inversionSymbol z = ∑ j ∈ Finset.range (n + 1), γ j * mellinEulerFactor j z) :
    Nonempty (F.IsLocalOfOrder c n) := by
  sorry

/-- **`lem:local-polynomial-symbol`, the (⇒) direction.** Locality forces the symbol to be a
polynomial, and covariance forces the coefficients to be `γ_j x^{j-1}`.

The covariance `A Δ_σ = σ^{-1} Δ_σ A` is what turns "some continuous `c_j`" into the homogeneous
form; the blueprint gets it by comparing coefficients of `g^{(j)}(x/σ)`, which in Lean is a
prescribed-jet test-function construction. -/
theorem exists_symbol_eq_of_isLocalOfOrder (hH : F.StandingHypothesis) {c : ℝ} (hc : 0 < c)
    (hc' : c < F.zStar - 1) {n : ℕ} (hL : F.IsLocalOfOrder c n) :
    ∃ γ : ℕ → ℂ, γ n ≠ 0 ∧
      (∀ j ∈ Finset.range (n + 1), ∀ x : ℝ, 0 < x →
        hL.coeff j x = γ j * (x : ℂ) ^ ((j : ℤ) - 1)) ∧
      (∀ z : ℂ, 0 < z.re → z.re < F.zStar - 1 →
        F.inversionSymbol z = ∑ j ∈ Finset.range (n + 1), γ j * mellinEulerFactor j z) := by
  sorry

end SelfDecomposableExponent

end Hemigroup
