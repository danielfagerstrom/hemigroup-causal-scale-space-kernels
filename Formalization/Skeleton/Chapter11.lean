/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.MellinVertical

/-!
# The target types of chapter 11 — **all discharged**

`thm:signaling-form` is Theorem 4′, and by the author's account the formulation the article exists
for. This file held chapter 11's target types while they were being proved. **Nothing is left in
it**, which is the outcome the statement-first convention exists to reach.

## What moved, and when

| node | declaration | file |
|---|---|---|
| `lem:mellin-data` (11.2) | `mellin_profile`, `norm_mellin_profile_le` | `Hemigroup/MellinData.lean` |
| `lem:inversion-symbol` (11.14) | `meromorphicOn_inversionSymbol` and five others | `Hemigroup/InversionSymbol.lean` |
| `lem:symbol-rigidity` (11.15) | `SameSymbolAction.eventuallyEq` | `Hemigroup/SymbolUniqueness.lean` |
| `lem:mellin-vertical` (11.13) | `verticalIntegrable_mellin_profile` | `Hemigroup/MellinVertical.lean` |

All of it reduces to ledger **A17** and nothing else.

## The last one is the one worth reading about

`lem:mellin-vertical` was recorded, twice, as blocked on Mathlib: the bound of `lem:mellin-data`
reduces vertical integrability to the decay of `|Γ(c+iτ)|`, and Mathlib has no such estimate —
`Stirling.lean` is Stirling's formula for `n !` alone. That was true about Mathlib and false about
the obligation. The classical asymptotic `|Γ(c+iτ)| ∼ √(2π)|τ|^{c-1/2}e^{-π|τ|/2}` does need
Stirling in the complex plane; **integrability needs only quadratic decay**, and quadratic decay is
two lines of the functional equation. See `Hemigroup/MellinVertical.lean`.

So chapter 11's remaining work is no longer upstream. What `def:inversion-operator` still needs
from `mellinInv_mellin_eq` is the *operator* formulation — exhibiting the function whose Mellin
transform is `B(-z) g̃(z)` — and a `ContinuousAt` hypothesis. Both are about this article rather
than about Mathlib, which is where ledger A12's correction of 2026-08-11 said the cost would sit
once the estimate was in hand.
-/
