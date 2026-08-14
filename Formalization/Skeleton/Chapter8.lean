/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.MeanDelay

/-!
# The target type of `prop:moments`

**This file carries a `sorry` and is not part of the `Hemigroup` library.**

`prop:moments` (8.4) asserts three things: `E T_x = x F'(0+)`, that `F'(0+) = b₀ + ∫₀^∞ k` is
finite iff `k` is integrable at infinity, and that the influence curve is linear in `x`. Two of
the three are proved and live in `Hemigroup/MeanDelay.lean`; the collation below rests on the
third, which is the only named sub-lemma.

| clause | status |
|---|---|
| linearity in `x` | `lintegral_id_kernel_zero` — proved |
| finiteness criterion | `meanRate_ne_top_iff` — proved |
| `E T₁ = F'(0+)` | `mean_delay_unit` below — **open** |

## What the split found, and it was not the split the plan expected

`PLAN-chapters-8-12.md` split this node once already, in Phase 0, moving the higher-moment
criterion out as `prop:moment-criterion` because it costs ledger A7 and the mean does not. What is
left divides again, and along a line the blueprint does not draw: it reaches linearity *from* the
identity — `E T_x = xF'(0+)` is linear in `x` because the right-hand side is — where in Lean
linearity is **cheaper than the identity and independent of it**. `kernel_zero_eq_map_lawT₁`,
proved for chapter 11, says `μ_{0,x}` is the pushforward of `μ_{0,1}` under `t ↦ xt`, so every
moment scales by a change of variables, finite or not. The identity is then only ever needed at
`x = 1`.

That is worth recording as the same shape as `lem:delay-core`'s estimate: a clause the prose
derives from the main result turns out to rest on something weaker, and separating them is what
makes the main result's cost visible.

## Work order for `mean_delay_unit`

The blueprint's proof is "differentiating the transform at the origin", which in `[0,∞]` is
monotone convergence twice over — no differentiation and no Tauberian theorem, because the
difference quotient is *monotone*:

1. `antitoneOn_einIntegrand` and `tendsto_einIntegrand_nhdsNE_zero` (both proved,
   `Hemigroup/Ein.lean`) make `s ↦ (1-e^{-st})/s` nonincreasing in `s` with limit `t`, so along
   `s_n = 1/(n+1)` the integrands increase to `t`. Monotone convergence gives
   `E T₁ = ⨆ₙ ∫ (1-e^{-s_n t})/s_n dμ = ⨆ₙ (1 - H(s_n))/s_n`, `H` the profile.
2. The same lemma applied inside the Lévy integral gives `F(s)/s = b₀ + ∫ einIntegrand(st) k(t) dt`
   increasing to `meanRate` as `s ↓ 0`. **This is the clause the node's annotation names** —
   "monotone convergence in (7.1) and nothing else".
3. What joins them is a squeeze, and it is the only step that is not monotone convergence:
   `w e^{-w} ≤ 1 - e^{-w} ≤ w` at `w = F(s_n)`, with `F(s_n) → 0`
   (`tendsto_toRealExponent_nhdsGT_zero`). Both bounding sequences are monotone, so the two
   suprema agree — including when both are `⊤`, which is the case the second clause of the
   proposition exists to describe and the one a real-valued argument would have to exclude.

Step 3 is where the `ℝ≥0∞` bookkeeping sits, and it is why this is stated rather than proved in
the round that proved the other two clauses.
-/

namespace Skeleton

open MeasureTheory Set

open scoped ENNReal

open Hemigroup

/-- **The mean delay at unit scale**: `E T₁ = F'(0+) = b₀ + ∫₀^∞ k`, in `[0,∞]`. -/
theorem mean_delay_unit (F : SelfDecomposableExponent) :
    ∫⁻ t, ENNReal.ofReal t ∂F.lawT₁ = F.meanRate := by
  sorry

/-- **`prop:moments` (Proposition 8.4).** The mean delay is `x F'(0+)`, so the influence curve is
exactly linear in the canonical gauge; and it is finite exactly when `k` is integrable at
infinity. -/
theorem moments (F : SelfDecomposableExponent) :
    (∀ x : ℝ, 0 < x →
        ∫⁻ t, ENNReal.ofReal t ∂(F.kernel 0 x) = ENNReal.ofReal x * F.meanRate) ∧
      (F.meanRate ≠ ⊤ ↔ IntegrableOn F.k (Ioi 1)) :=
  ⟨fun _ hx => by rw [F.lintegral_id_kernel_zero hx, mean_delay_unit F],
   F.meanRate_ne_top_iff⟩

end Skeleton
