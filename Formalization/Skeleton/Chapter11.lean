/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Hemigroup.MemoryFractional
import Hemigroup.InversionOperator
import Hemigroup.AdmissibleCone

/-!
# The target types of chapter 11

`thm:signaling-form` is Theorem 4′, and by the author's account the formulation the article exists
for. Every target type this file held is proved and has moved into the library (the table below);
nothing is stated here any more, and the file is kept for the record of what each cost.

## What moved, and when

| node | declaration | file (under `Hemigroup/`) |
|---|---|---|
| `lem:mellin-data` (11.2) | `mellin_profile`, `norm_mellin_profile_le` | `MellinData.lean` |
| `lem:inversion-symbol` (11.14) | `meromorphicOn_inversionSymbol` + 5 | `InversionSymbol.lean` |
| `lem:symbol-rigidity` (11.15) | `SameSymbolAction.eventuallyEq` | `SymbolUniqueness.lean` |
| `lem:mellin-vertical` (11.13) | `verticalIntegrable_mellin_profile` | `MellinVertical.lean` |
| `lem:inversion-operator-action` (11.16) | `inversionOperator` + 3 | `InversionOperator.lean` |
| `lem:mode-rigidity` (11.25) | `mode_rigidity` | `ModeRigidity.lean` |
| `lem:standing-levy-reading` (11.22) | `standing_levy_reading` + 2 | `StandingLevyReading.lean` |
| `lem:zstar-log-growth`(2), drift case | `…_div_log_atTop_of_b₀_pos` | `ZStarLogGrowth.lean` |
| `lem:zstar-log-growth`(2), driftless case | `…_div_log_atTop_of_b₀_zero` | `ZStarDriftless.lean` |
| `lem:zstar-log-growth`(1) and (4) | `…_div_log_atTop_zStar`, `zStar_smul` | `ZStarAbelian.lean` |

All of it reduces to Lean core.

`lem:mode-rigidity` was priced here at a session's work for one reason — Mathlib carries no way to
patch a function given on translates of one finite-width strip, related by a functional equation
on their overlaps, into a single entire periodic function. That was right about Mathlib and about
the blueprint's *order* of steps, and wrong about the obligation: exchange the middle two steps
(spread the hypothesis's boundedness over the whole strip first, remove the singularities there,
and only then glue) and the gluing is of analytic pieces, where well-definedness is the whole of
it. See the module docstring of `Hemigroup/ModeRigidity.lean`. That is the fourth time in this
chapter that what a proof cites, or the order it cites it in, turned out to be an upper bound on
what the statement needs.

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

## `lem:standing-levy-reading` (11.22) — **discharged**

Both target types are proved, in `Hemigroup/StandingLevyReading.lean`, on Lean core.

The pricing here — "statable, not cheap" — read the obligation off the *proof sketch* again, and
again the sketch was an upper bound. Two things it asked for turned out not to be needed:

* **the `ℝ≥0∞`-to-`ℝ` bridge, in both directions of the `iff`.** Only the divergent direction
  needs a limit. The convergent direction is a uniform bound, `levyJump k s ≤ levyMass k`, which
  is `1 - e^{-st} ≤ 1` and no convergence theorem at all — and it needs no sign condition on `s`
  either, `ENNReal.ofReal` truncating the negative case. So monotone convergence is used once,
  along the naturals, in one direction;
* **a statement the library lacks.** The divergence `∫₀^{t₀} t⁻¹dt = ∞` is indeed absent from
  Mathlib in `lintegral` form, but it is present in *integrability* form
  (`intervalIntegrable_inv_iff`), and `hasFiniteIntegral_iff_ofReal` is the passage between them —
  six lines, not a development.

What the proof did make visible is where the class is used. Clause (2) — nonzero implies
`F(∞) = ∞` — is **false** for a general Lévy exponent: a driftless compound Poisson with finite
Lévy mass is bounded. It holds here only because the density against `dt/t` is nonincreasing, so
a single point where `k` is positive bounds `k` below on all of `(0,t₀]` and the mass diverges at
the origin. Self-decomposability, not Lévy structure, is what makes the admissible cone have no
bounded nonzero member.

## `lem:zstar-log-growth` (11.23) — **discharged**, all four declarations

**Clause (2) is proved in both cases**, unconditionally. The **drift** case
(`Hemigroup/ZStarLogGrowth.lean`, Lean core) needs no Tauberian argument: `F(s) ≥ b₀ s` from the
representation, and `s / log s → ∞`, which is `Real.isLittleO_log_id_atTop` turned the other way
up. The **driftless** case (`Hemigroup/ZStarDriftless.lean`, Lean core) is the one with content,
and it is the sixth time in this chapter that what a proof cites was an upper bound on what its
statement needs — see below. Clauses (1) and (4) stay `\notready`; what each waits on is recorded
at its declaration.

The node is the Lévy-data reading of (H)'s *second* clause, which 11.22 does not supply (it
reads only the first). `z_* = lim F(s)/log s`, and — the finding writing the type down produced —
only the identification of that limit *with* `z_*` needs a no-atom hypothesis; the value of the
limit itself, `∞` if `b₀ > 0` and `k(0⁺) := sup_{t>0} k(t)` if `b₀ = 0`, is an unconditional fact
about the exponent, via `B(s) := s F'(s) = b₀ s + ∫₀^∞ e^{-u} k(u/s) du` (substitute `u = st`) and
monotone convergence in `k(u/s) ↑ k(0⁺)` as `s → ∞`. That splits the `\lean` tag into four
declarations rather than one: `tendsto_toRealExponent_div_log_atTop_zStar` needs the no-atom
hypothesis (`negMoment`/`zStar` integrate over `Ioi 0` and are blind to an atom at the origin, the
same trap `lem:standing-levy-reading`'s target types were written to avoid); the other three do
not. `zStar_smul` is priced as the cheapest of the four — a direct corollary of the first once it
exists, via `exponent_smul` (already proved, `Hemigroup/AdmissibleCone.lean`) and the arithmetic of
a scaled limit.

**A plausible shortcut, no longer needed for clause (2).** The blueprint proof of clause (1) invokes
`lem:selfdecomposable-exponents`(2) — `B` is a Bernstein function, hence nondecreasing — to get
`F(e^{(\cdot)})` convex and hence its difference quotient convergent. But `B`'s monotonicity is
also immediate from the explicit formula above (increasing `s` increases each `k(u/s)`
pointwise), without appeal to the general Bernstein-closure fact, which is ledger A18. If that
substitutes cleanly, clause (1) would reduce to Lean core rather than crossing A18 — a
question only an attempt at clause (1)'s proof, not this survey, can settle. What the driftless
case of (2) settled is weaker and better: clause (2) needs neither `B` nor A18, because it needs no
derivative at all.

**The obstacle recorded here belonged to one route, not to the statement.** This file, the
blueprint node, the changelog and the handoff all said that the driftless case of (2) waits on an
`∞/∞` L'Hôpital that Mathlib does not carry (`Mathlib/Analysis/Calculus/LHopital.lean` is the `0/0`
form in every variant), plus a case split on `k(0⁺) = ∞`. That is a true statement about the
blueprint's route — through `B(s) = sF'(s)` and the Cesàro step
`F(s)/log s = (log s)⁻¹∫₁^s B(v)v⁻¹dv → lim B` — and a false one about the obligation. The proof in
`Hemigroup/ZStarDriftless.lean` never differentiates: it splits the defining integral, bounds below
on `(M/s,t₀]` using `k ≥ k(t₀)` there and `1 - e^{-st} ≥ 1 - e^{-M}`, bounds above by splitting at
`1/s` and using `1 - e^{-st} ≤ st` before and `≤ 1` after, and assembles the two with
`tendsto_order` — which takes `k(0⁺) = ∞` in its stride, there being then no level above the
supremum to check, so the case split disappears with the derivative. Sixth instance of the
chapter's pattern, and the first where the recorded obstacle was a *missing Mathlib theorem* rather
than a cited node: the moral now covers the tools a proof reaches for as well as the lemmas.

**Clauses (1) and (4) — discharged 2026-09-26** (Q-0021), in `Hemigroup/ZStarAbelian.lean`, Lean
core, and the node is `\leanok`. (1) was (2) plus the Abelian comparison through
`Γ(ζ)·E[T₁^{-ζ}] = ∫₀^∞ s^{ζ-1}e^{-F(s)}ds`, as recorded here; what the record over-priced is the
drift case, which needed no separate reading off `negMoment`: the comparison is proved for any
limit in `[0,∞]`, and `L = ∞` makes its divergent half vacuous. (4) was the corollary priced.
-/

namespace Skeleton

open MeasureTheory Set Filter
open scoped ENNReal Topology

open Hemigroup Hemigroup.SelfDecomposableExponent


end Skeleton
