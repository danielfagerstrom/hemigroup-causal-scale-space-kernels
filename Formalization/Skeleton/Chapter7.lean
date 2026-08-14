/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.DickmanSuperposition

/-!
# The target types of chapter 7's appended nodes — **discharged**

`prop:extreme-rays` (7.7) asserted four things at four prices — the cone, the `Ein`
superposition, injectivity of `(b₀,ρ) ↦ F`, and the extreme rays — and reported the maximum. It
is the Lemma 7.1 shape for the third time in this chapter, so it was narrowed in place and the two
cheap clauses appended as `lem:admissible-cone` (7.13) and `lem:dickman-superposition` (7.14).
Both are now proved and have moved. **This file holds no declarations.**

| node | declaration (under `Hemigroup/`) |
|---|---|
| `lem:admissible-cone` (7.13) | `SelfDecomposableExponent.admissible_cone`, in `AdmissibleCone.lean` |
| `lem:dickman-superposition` (7.14) | `dickman_superposition`, in `DickmanSuperposition.lean` |

## What stays behind in 7.7

**Injectivity** is uniqueness of the Lévy–Khintchine triple, which is how the blueprint's proof
reaches it — ledger A3, quantifying over `BF`, which this development has no vocabulary for. It is
*plausibly* avoidable: `hasDerivAt_toRealExponent` gives `F'(s) = b₀ + ∫e^{-st}k(t)dt`, and
`laplaceL_injective_of_ne_top` is Laplace injectivity for locally finite measures, so `F`
determines `k` a.e. with no statement about `BF` at all. That is a piece of work in its own right
and it is not attempted here; it is recorded in the node's annotation so the next reader does not
have to rediscover that the citation overstates the obligation. Same shape as chapter 9's Route B,
which replaced Bernstein–Widder by a construction.

**The extreme rays** need a Choquet argument, and the obstruction is not that Mathlib lacks
`IsExtreme` — it has it. It is that `ρ = ∫ δ_τ ρ(dτ)` has to be read as a barycentre in a cone of
measures, which is a theory the development would have to build.

## The two statements were existential, and stayed that way

Neither named the construction that discharges it: `admissible_cone` says a sum *exists* with the
right data and the right exponent rather than naming `SelfDecomposableExponent.add`, and
`dickman_superposition` says a measure with tail `k` *exists* rather than naming the quantile
transform of `Hemigroup/Subordinator.lean` that supplies one. That is the rule chapter 9's Route B
paid to learn — **a decomposition should say what each piece must achieve, not with what** — and it
cost nothing: the proved statements are the stated ones verbatim, with the definitions moved into
the library beneath them.
-/
