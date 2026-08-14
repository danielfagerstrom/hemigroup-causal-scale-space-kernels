/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.DelayCore

/-!
# The target types of chapter 10 — **discharged**

`lem:delay-core` (Lemma 10.1) was stated here, `sorry`-marked in five clauses with a `sorry`-free
collation above them, and has since been proved in full. Everything has moved into
`Hemigroup/DelayCore.lean`, which also carries the chapter's setting — `X₀`, the delay semigroup,
and the core `𝒟`. **This file holds no declarations.**

| clause | declaration (under `Hemigroup/`) |
|---|---|
| density in `X₀` | `dense_coreL1` |
| invariance under `T_r` | `hasCoreDerivL1_transL1` |
| invariance under `Φ_{x,y}` | `hasCoreDerivL1_mconvL1` |
| the difference quotient | `tendsto_differenceQuotient` |
| the estimate | `norm_transL1_sub_le` |
| the node | `delay_core` |

## What the statement-first step bought, since that is what it is for

**The modelling decision, taken once and checked.** `X₀` is a predicate on `X = L¹(ℝ)` and `𝒟` is
primarily a predicate on genuine functions; the reasons are in `Hemigroup/DelayCore.lean`'s module
docstring, and the check is `memCore_iff_signaling_hypotheses`, an `iff` between `f ∈ 𝒟` and the
six hypotheses `thm:signaling-form` takes about its signal. Chapter 11 was written taking those
six directly, `𝒟` having no definition at the time; the `iff` says the definition now supplies
exactly them, neither fewer nor more.

**And the cost estimate was wrong by most of the work.** The five clauses were priced on one
analytic input, continuity of translation in `L¹`, expected to be built here because Mathlib has
no lemma of that name. Mathlib does have it, as `Lp.compMeasurePreserving_continuous`; and this
development had already proved it, six chapters earlier, as `continuous_transL1` in
`Hemigroup/Representation.lean`. So had it proved the *causal* mollifier the density clause needs,
as `approxId` with `tendsto_bconv_approxId`. Writing the statements is what made those two
requirements explicit enough to recognise; a survey would have missed both.
-/
