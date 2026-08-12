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

## What is stated here: the derivative clause of `lem:memory-fractional-integrals`

`thm:signaling-form`(2)'s Mellin form is proved on the transform side
(`lem:signaling-mellin-form`): `B(1-z)ũ(t,·)(z-1) = H̃(z)(I^{z-1}f)(t)`. What is left is to
identify the right-hand side with `∂̃_t u(t,·)(z)`, and that is 11.5's derivative clause, which the
draft proves in one line: `∂_t u(t,x) = E[f'(t - xT₁)]`, and `Iᶻf' = I^{z-1}I^1f' = I^{z-1}f`
using `f(0) = 0`.

**Writing it down shows the node it cites is not what it needs.** The draft reaches this through
`f ∈ 𝒟` and hence `lem:delay-core` (10.1) — density of the core, invariance under the delay
semigroup and under `Φ`, the `L¹` difference quotient. None of that is used. What is used is two
facts, stated below, and `𝒟` enters only as a convenient source of their hypotheses:

* `hasDerivAt_delayedField` — differentiation under the integral sign, which needs `f` to be an
  integral of an `L¹` function and nothing about `Φ`;
* `riemannLiouville_integral` — the fractional-integral identity `Iᶻf' = I^{z-1}f`, which is
  Fubini over a triangle plus `∫_ρ^t (t-r)^{z-2}dr = (t-ρ)^{z-1}/(z-1)`, and mentions neither the
  field nor the core.

So the correction recorded one round ago — that `lem:delay-core` is what chapter 11 waits on — is
itself wrong, and in the same way: a node was read as a prerequisite because the *proof* invokes
it, not because the *obligation* needs it. That is the third time in this chapter, and by now the
pattern deserves its name: **what a proof cites is an upper bound on what a statement needs.**
-/

namespace Skeleton

open MeasureTheory Set Filter Hemigroup

variable (F : Hemigroup.SelfDecomposableExponent)

/-! ## `lem:memory-fractional-integrals`, the derivative clause -/

/-- **The field half**: `∂_t u(t,x) = E[f'(t - x T₁)]`, i.e. differentiation under the integral
sign for the delayed field.

`f` is presented as the integral of `g`, which is what absolute continuity with `f(0) = 0`
amounts to and is all the statement uses. Nothing here is about `Φ` or the core. -/
theorem hasDerivAt_delayedField {g f : ℝ → ℝ} (hgm : Measurable g) (hg : Integrable g)
    (hf : ∀ r : ℝ, f r = ∫ ρ in Ioc (0 : ℝ) r, g ρ) {x : ℝ} (hx : 0 < x) (t : ℝ) :
    HasDerivAt (fun τ : ℝ => F.delayedField f τ x) (F.delayedField g t x) t := by
  sorry

/-- **The transform half**: `Iᶻ f' = I^{z-1} f` when `f(0) = 0`, which is the step that turns
`H̃(z)(Iᶻf')(t)` into the `H̃(z)(I^{z-1}f)(t)` that `lem:signaling-mellin-form` produces.

The draft derives it as `Iᶻf' = I^{z-1}I^1f' = I^{z-1}f`, i.e. from the semigroup property of the
Riemann–Liouville family. It is cheaper not to have that property: writing `f` as the integral of
`g` and exchanging the order of integration over the triangle `0 < ρ ≤ r ≤ t` leaves the inner
integral `∫_ρ^t (t-r)^{z-2}dr = (t-ρ)^{z-1}/(z-1)`, and `Γ(z) = (z-1)Γ(z-1)` finishes it. The
strip condition `Re z > 1` is exactly what makes that inner integral converge. -/
theorem riemannLiouville_integral {z : ℂ} (hz : 1 < z.re) {g : ℝ → ℝ} (hgm : Measurable g)
    {t : ℝ} (hg : IntegrableOn g (Ioc 0 t)) (ht : 0 < t) :
    riemannLiouville (z - 1) (fun r => ∫ ρ in Ioc (0 : ℝ) r, g ρ) t
      = riemannLiouville z g t := by
  sorry

end Skeleton
