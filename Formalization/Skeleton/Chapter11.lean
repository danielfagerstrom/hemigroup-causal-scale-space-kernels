/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.MemoryFractional
import Hemigroup.InversionOperator

/-!
# The target types of chapter 11

`thm:signaling-form` is Theorem 4′, and by the author's account the formulation the article exists
for. Clauses (1) and (3) are proved and have moved; what is stated here is the analytic core of
clause (2)'s Mellin form.

## What moved, and when

| node | declaration | file (under `Hemigroup/`) |
|---|---|---|
| `lem:mellin-data` (11.2) | `mellin_profile`, `norm_mellin_profile_le` | `MellinData.lean` |
| `lem:inversion-symbol` (11.14) | `meromorphicOn_inversionSymbol` + 5 | `InversionSymbol.lean` |
| `lem:symbol-rigidity` (11.15) | `SameSymbolAction.eventuallyEq` | `SymbolUniqueness.lean` |
| `lem:mellin-vertical` (11.13) | `verticalIntegrable_mellin_profile` | `MellinVertical.lean` |
| `lem:inversion-operator-action` (11.16) | `inversionOperator` + 3 | `InversionOperator.lean` |

All of it reduces to ledger **A17** and nothing else.

## Two of them are worth reading about

`lem:mellin-vertical` was recorded, twice, as blocked on Mathlib: the bound of `lem:mellin-data`
reduces vertical integrability to the decay of `|Γ(c+iτ)|`, and Mathlib has no such estimate —
`Stirling.lean` is Stirling's formula for `n !` alone. That was true about Mathlib and false about
the obligation. The classical asymptotic `|Γ(c+iτ)| ∼ √(2π)|τ|^{c-1/2}e^{-π|τ|/2}` does need
Stirling in the complex plane; **integrability needs only quadratic decay**, and quadratic decay is
two lines of the functional equation. See `Hemigroup/MellinVertical.lean`.

`lem:inversion-operator-action` is the split that writing `def:inversion-operator` in Lean forced.
The blueprint's definition sets `(A g)(x)` to a contour integral and glosses it as `x⁻¹(B(θ)g)(x)`,
the gloss being what ledger A12 licenses. Formalising it separates the two: the operator is total
and needs no hypothesis at all, while the gloss needs a *referent* for `B(θ)g` — the function `h`
with `h̃ = B(-z)g̃(z)` on the line. Given that `h`, everything is interface-free. So 11.16 is [T],
`def:inversion-operator` keeps A12, and what A12 now carries is exactly the production of `h` —
which, by `lem:profile-eigenfunction`, is never called upon. See `Hemigroup/InversionOperator.lean`
for the second finding, about which equality the identity on the line can be asked for.

## The analytic core of `lem:memory-fractional-integrals` (11.5) — **discharged**

Clause (2) of Theorem 4′ is what is left of the chapter, and it runs through 11.5:
`ũ(t,·)(z) = H̃(z)·(Iᶻf)(t)`, the memory line at time `t` holding the analytic family of
Riemann–Liouville integrals of the past signal. Two things had to be settled before stating it.

**Mathlib has no fractional integral of any order.** There is no `Riemann–Liouville` anywhere in
the library — `Analysis/` carries Mellin, Fourier, convolution and distributions, but nothing
fractional. So `Iᶻ` is defined here. That is a definition and a few of its properties, not an
interface: the draft cites Samko–Kilbas–Marichev for the *notation and theory* of `Iᶻ`, and
nothing in chapter 11 needs more of that theory than the definition.

**The field is `L¹`-valued and the lemma is pointwise in `t`, so the statement below is about a
function.** `Φ_{x,y}` in `Hemigroup/Family.lean` maps `X →L[ℝ] X` with `X` an `L¹` space, and an
`L¹` class has no value at a point; `u(t,x)` is meaningful only after choosing a representative or
weakening to "a.e. `t`". Rather than decide that here, what was stated — and is now proved, as
`Hemigroup.mellin_delayed_average` in `Hemigroup/MemoryFractional.lean` — is the *analytic core*:
the substitution `y = x·T₁` applied to a genuine function `f`, with the integrand written as
`E[f(t - x T₁)]` outright. Identifying that integrand with `Φ_{0,x} f` is a separate, `L¹`-level
step, and it is the one that carries the modelling decision (settled as (a), a.e. in `t`, on
2026-08-12). The core was needed under either reading, which is why it went first.

## The derivative clause of `lem:memory-fractional-integrals` — **discharged**

`thm:signaling-form`(2)'s Mellin form is proved on the transform side
(`lem:signaling-mellin-form`): `B(1-z)ũ(t,·)(z-1) = H̃(z)(I^{z-1}f)(t)`. What is left is to
identify the right-hand side with `∂̃_t u(t,·)(z)`, and that is 11.5's derivative clause, which the
draft proves in one line: `∂_t u(t,x) = E[f'(t - xT₁)]`, and `Iᶻf' = I^{z-1}I^1f' = I^{z-1}f`
using `f(0) = 0`.

**Writing it down shows the node it cites is not what it needs.** The draft reaches this through
`f ∈ 𝒟` and hence `lem:delay-core` (10.1) — density of the core, invariance under the delay
semigroup and under `Φ`, the `L¹` difference quotient. None of that is used. What is used is two
facts, stated below, and `𝒟` enters only as a convenient source of their hypotheses:

* the field half — **and stating it as a pointwise derivative was wrong.** `f ∈ 𝒟` is absolutely
  continuous, so `f' = g` only a.e., and the field `E[f(t-xT₁)]` is a convolution of two `L¹`
  functions, hence `L¹` and not continuous; `E[g(t-xT₁)]` has no pointwise values to be a
  derivative *at*. Continuity could be bought with absolute continuity of `T₁`'s law — Sato
  Thm. 27.13, an interface — for nothing. The article never meant the pointwise reading: `∂_t` in
  chapter 10 is the `X₀ = L¹` derivative, and what `lem:delay-core`'s `Φ`-invariance argument
  establishes is `μ * f = 1_{[0,∞)} * (μ * f')`. So the true statement is that the field of `f` is
  the **primitive** of the field of `f'`, which is `delayedField_eq_setIntegral` and needs no
  interface;
* `riemannLiouville_integral` — the fractional-integral identity `Iᶻf' = I^{z-1}f`, which is
  Fubini over a triangle plus `∫_ρ^t (t-r)^{z-2}dr = (t-ρ)^{z-1}/(z-1)`, and mentions neither the
  field nor the core. **Proved**, and moved into `Hemigroup/MemoryFractional.lean`; what is left
  here is the field half alone.

So the correction recorded one round ago — that `lem:delay-core` is what chapter 11 waits on — was
itself wrong, and in the same way: a node was read as a prerequisite because the *proof* invokes
it, not because the *obligation* needs it. That is the third time in this chapter, and by now the
pattern deserves its name: **what a proof cites is an upper bound on what a statement needs.**

Both pieces are proved, and with them `thm:signaling-form`(2)'s Mellin form
(`mellin_signaling_form`).

## `lem:standing-levy-reading` (11.22) — the two target types below

Added 2026-08-29, alongside `lem:standing-kernel-readings` (11.21, proved, in
`Hemigroup/MemoryFractional.lean`), when `def:standing-hypothesis`'s embedded glosses were split
out of the definition. This is the one of the two glosses stated in the `(b₀,k)` data of (7.1)
rather than in `T₁`'s law, and it is genuinely more work: the first clause needs a monotone
(or dominated) convergence argument for `levyJump` as `s → ∞`, bridging an `ℝ≥0∞`-valued limit at
`s → ∞` to the `ℝ` atTop reading `toRealExponent` already carries, in *both* directions of an
`iff`; the second needs a small divergence computation, `∫₀^{t₀} t⁻¹dt = ∞`, that nothing in the
library currently states. Priced against the target types below, not against the paper proof
(the paper proof's own route — through complete monotonicity — is not available at all, the
development having no `CM` predicate; see `DESIGN-formalization-strategy.md`): this is
**statable, not cheap**, and nothing downstream consumes it (the definition's own clauses are
what every proof in chapters 11–12 actually uses, per 11.21's remark that all of (H)'s bite is in
the second clause). So it stays here, `\notready`, rather than being attempted inline.
-/

namespace Skeleton

open MeasureTheory Set Filter
open scoped ENNReal Topology

open Hemigroup Hemigroup.SelfDecomposableExponent

/-- **`lem:standing-levy-reading`(1)**: `F(∞) = ∞` iff the exponent carries drift or infinite
Lévy mass — the reading of the first clause of (H) in the `(b₀, k)` data of (7.1), rather than in
the law of `T₁` that `lem:standing-kernel-readings` uses. -/
theorem tendsto_toRealExponent_atTop_iff_levy (F : SelfDecomposableExponent) :
    Tendsto F.toRealExponent atTop atTop ↔
      0 < F.b₀ ∨ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (F.k t / t) = ⊤ := by
  sorry

/-- **`lem:standing-levy-reading`(2)**: a nonzero admissible exponent automatically satisfies the
first clause of (H) — so, within the admissible class, (H) reduces to its second clause, `z_* >
1`. `F ≢ 0` is phrased as `exponent_strictMono` already phrases it: some positive point where the
exponent does not vanish. -/
theorem tendsto_toRealExponent_atTop_of_ne_zero (F : SelfDecomposableExponent)
    (hF : ∃ s₀, 0 < s₀ ∧ F.exponent s₀ ≠ 0) :
    Tendsto F.toRealExponent atTop atTop := by
  sorry

end Skeleton
