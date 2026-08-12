/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
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

## What is stated here: the analytic core of `lem:memory-fractional-integrals` (11.5)

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
weakening to "a.e. `t`". Rather than decide that here, the statement below is the *analytic core*
— the substitution `y = x·T₁` applied to a genuine function `f` — with the integrand written as
`E[f(t - x T₁)]` outright. Identifying that integrand with `Φ_{0,x} f` is a separate, `L¹`-level
step, and it is the one that carries the modelling decision. See `PLAN-chapters-8-12.md`, which
records the fork rather than resolving it: the core is needed under either reading, so it is
what gets stated.
-/

namespace Skeleton

open MeasureTheory Set Filter Hemigroup

open scoped Topology

variable (F : Hemigroup.SelfDecomposableExponent)

/-! ## `lem:memory-fractional-integrals` (11.5), analytic core -/

/-- The **Riemann–Liouville integral of complex order** `z`,
`(Iᶻf)(t) = Γ(z)⁻¹ ∫₀ᵗ (t-r)^{z-1} f(r) dr`, for `Re z > 0`.

Defined here because Mathlib has no fractional integral of any order. Total in `z` and `t`:
`Complex.Gamma` and `cpow` are total, so no side condition is carried in the definition and the
hypotheses live on the theorems, as they do for `inversionOperator`. -/
noncomputable def riemannLiouville (z : ℂ) (f : ℝ → ℝ) (t : ℝ) : ℂ :=
  (Complex.Gamma z)⁻¹ * ∫ r in Ioc (0 : ℝ) t, ((t - r : ℝ) : ℂ) ^ (z - 1) * (f r : ℂ)

/-- **`lem:memory-fractional-integrals`**, the analytic core: the Mellin transform in `x` of the
delayed average `x ↦ E[f(t - x T₁)]` is `H̃(z)` times the Riemann–Liouville integral of order `z`.

The whole content is the substitution `y = x·T₁` under Tonelli, which turns
`∫₀^∞ x^{z-1} E[f(t - xT₁)] dx` into `E[T₁^{-z}] ∫₀^t y^{z-1} f(t-y) dy`; `lem:mellin-data` then
replaces `E[T₁^{-z}]Γ(z)` by `H̃(z)`. The exchange needs `Re z > 1`, which is where the strip of
this lemma differs from `lem:mellin-data`'s and why (H)'s second clause `z_* > 1` is what makes
the chapter non-empty. -/
theorem mellin_delayed_average (hH : F.StandingHypothesis) {z : ℂ} (hz : 1 < z.re)
    (hz' : z.re < F.zStar) {f : ℝ → ℝ} (hf : Integrable f)
    (hcausal : ∀ r : ℝ, r < 0 → f r = 0) {t : ℝ} (ht : 0 < t) :
    mellin (fun x : ℝ => ∫ τ, (f (t - x * τ) : ℂ) ∂F.lawT₁) z
      = mellin (fun s => (F.profile s : ℂ)) z * riemannLiouville z f t := by
  sorry

end Skeleton
