/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the MIT license as described in the file LICENSES/MIT.txt.
Authors: Daniel Fagerström
-/
import Hemigroup.LocalityOrderOne
import Hemigroup.LocalityOrderTwo

/-!
# `thm:locality`'s (⇒) direction, collated

Blueprint: the moment content of `thm:locality`'s (⇒) direction (12.5), split off as
`lem:local-moment-classification` so that the [T] part of a node carrying ledger **A14** is
reported separately from the entry --- the convention this chapter has used three times already
(`lem:symbol-vanishes-at-origin`, `lem:moment-recursion-quotient`, `lem:pmp-verification`).

## What the collation adds to the two branches

Two things, and the first is not bookkeeping.

**Order `0` is impossible**, and cheaply. `def:locality-pmp` asks the leading coefficient not to
vanish identically, so an operator local of order `0` would have `c_0 \not\equiv 0`; but
`lem:moment-recursion`(1) says `γ_0 = 0`, and covariance says `c_0(x) = γ_0 x^{-1}`, which is
identically `0`. So the two clauses of the definition are already incompatible at order `0`, with
no analysis in between --- and the theorem's case list is a *dichotomy* rather than a trichotomy
for that reason rather than by inspection.

**And the two branches are then exhaustive**, so the classification is one statement: under the
order bound, the moments are either a pure power or the Gamma form, with nothing else possible.

## Where the maximum principle went

Nowhere: it does not appear. `thm:locality`'s (⇒) direction uses the PMP *only* through ledger
**A14**, whose conclusion is the order bound, and the order bound is the hypothesis `n ≤ 2` here.
A collation that took `SatisfiesPMP` as a hypothesis and never used it would misreport where the
principle is spent, so it does not.

Both citations of that direction are hypotheses, as in the two branches: `hA13` is
`lem:moment-recursion`(2) and `hn` is Courrège's bound. `#print axioms` accordingly shows A17 and
neither.
-/

namespace Hemigroup

open MeasureTheory Set Filter

open scoped ENNReal Topology

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent)

/-- **There is no local operator of order zero.**

The two clauses of `def:locality-pmp` are incompatible there, and no analysis is involved:
`leading_ne_zero` asks `c_0` not to vanish identically, covariance gives `c_0(x) = γ_0 x^{-1}`,
and `lem:moment-recursion`(1) gives `γ_0 = 0`.

Note what is *not* needed: A13. The vanishing of `γ_0` is `lem:symbol-vanishes-at-origin` turned
into a value, which lives on the strip the standing hypothesis already supplies. -/
theorem not_isLocalOfOrder_zero (hH : F.StandingHypothesis) {c : ℝ} (hc : 0 < c)
    (hc' : ENNReal.ofReal c < F.zStar - 1) (hL : F.IsLocalOfOrder c 0) : False := by
  have hsymbol : ∀ z : ℂ, 0 < z.re → ENNReal.ofReal z.re < F.zStar - 1 →
      mellin (fun s => (F.profile s : ℂ)) z ≠ 0 →
      F.inversionSymbol z
        = ∑ j ∈ Finset.range (0 + 1), hL.coeff j 1 * mellinEulerFactor j z :=
    fun z hz hz' hne =>
      (F.sameSymbolAction_of_isLocalOfOrder hH hc hc' hL).eqOn_of_ne_zero ⟨⟨hz, hz'⟩, hne⟩
  have hγ0 : hL.coeff 0 1 = 0 :=
    F.coeff_zero_eq_zero_of_symbol_eq hH (fun j => hL.coeff j 1) hsymbol
  obtain ⟨x₀, hx₀, hne⟩ := hL.leading_ne_zero
  refine hne ?_
  rw [F.coeff_eq_of_isLocalOfOrder hL.toIsLocalOfOrderCore le_rfl hx₀, hγ0, zero_mul]

/-- **`thm:locality`(⇒), the moment classification.** Under the order bound, a local operator
leaves exactly two possibilities for the negative moments of `T₁`:

* `m(z) = c'^z` --- the deterministic delay `T₁ = 1/c'`, order one, case (1) of the theorem;
* `m(z) = c₂^z Γ(a+z)/Γ(a)` --- the inverse-gamma law `T₁ ≐ 1/(c₂γ_a)`, order two, case (2).

Order `0` is ruled out by `not_isLocalOfOrder_zero` and orders above `2` by the hypothesis `hn`,
which is what ledger **A14** concludes from the positive maximum principle; `hA13` is
`lem:moment-recursion`(2). Both are hypotheses rather than axioms, so `#print axioms` shows A17
and neither. -/
theorem exists_moment_form_of_isLocalOfOrder (hH : F.StandingHypothesis)
    (hA13 : F.AllNegMomentsFinite) {c : ℝ} (hc : 0 < c) {n : ℕ} (hn : n ≤ 2)
    (hL : F.IsLocalOfOrder c n) :
    (∃ c' : ℝ, 0 < c' ∧ ∀ z : ℝ, 0 < z → (F.negMoment z).toReal = c' ^ z) ∨
      (∃ c₂ a : ℝ, 0 < c₂ ∧ 0 < a ∧ ∀ z : ℝ, 0 < z →
        (F.negMoment z).toReal = c₂ ^ z * Real.Gamma (a + z) / Real.Gamma a) := by
  have hc' : ENNReal.ofReal c < F.zStar - 1 := F.ofReal_lt_zStar_sub_one_of_all hA13 c
  interval_cases n
  · exact (F.not_isLocalOfOrder_zero hH hc hc' hL).elim
  · exact Or.inl (F.exists_pow_form_of_isLocalOfOrder_one hH hA13 hc hL)
  · exact Or.inr (F.exists_gamma_form_of_isLocalOfOrder_two hH hA13 hc hL)

end SelfDecomposableExponent

end Hemigroup
