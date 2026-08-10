/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.LevyLimit

/-!
# The target type of `thm:increments-bernstein`

**This file carries a `sorry` and is not part of the `Hemigroup` library.** It states what the
theorem *is*, so that the blueprint node can name a Lean declaration and be `\notready` rather
than untagged — the middle state the dependency graph exists to show. When the proof lands the
declaration moves into `Hemigroup/`, this file goes away, and the node becomes `\leanok`.

## Why the statement rather than the proof came first

The hard part of this node was never the analysis; it was the vocabulary. The blueprint
concludes `g_{x,y} ∈ BF₀`, and the development has no `BF₀` — it never defines complete
monotonicity, by design. So the conclusion had to be restated in `LE`, the same class named by
its representation, which is what `levyExponent` is. Writing the target type down is what makes
that settlement visible; up to now the graph could not distinguish it from "nobody has decided
what to state".

## What is already proved, in `Hemigroup`

* `CascadeCore.tendsto_integral_partitionMeasure` — the null-array estimate:
  `∫ (1 - e^{-st}) dΠ_n → g_{x,y}(s)`, with `Π_n` finite at every `n`.
* `levyRatio`, `continuous_levyRatio`, `levyRatioBdd` — the test function, singularity filled.
* `CascadeCore.weightedPartition`, `integral_weightedPartition`,
  `measureReal_weightedPartition_univ` — the weighted approximants and their two properties.

## What the `sorry` stands for

Three steps. Extract a weak limit `ρ` of `(ρ_n)` — the masses are bounded by the `s = 1`
approximant and the carriers all sit in `[0,1]`, so this is Prokhorov with a constant compact.
Split `ρ` at its two endpoints: `b₀ := ρ({0})` is the drift, and `ρ({1})` is a killing term that
`g_{x,y}(\zp) = 0` forces to vanish. Transport `ρ` restricted to `(0,1)` back through
`v ↦ -log(1-v)` with density `1/v` to get `ν`.
-/

namespace Skeleton

open MeasureTheory Set
open Hemigroup

/-- **`thm:increments-bernstein`**, in the representation vocabulary: every increment of a
causal cascade family is a Lévy exponent.

Stated with the exponent's `ℝ≥0∞` reading on the left, which is how `levyExponent` is valued —
no integrability hypothesis is then needed anywhere in the statement. Causality of `ν` is part
of the conclusion: the Lévy measure is carried by `[0,∞)`, as `(7.1)` requires. -/
theorem exponent_hasLevyRep (Fam : CascadeCore) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    ∃ b₀ : ℝ, ∃ ν : Measure ℝ, 0 ≤ b₀ ∧ IsCausal ν ∧
      ∀ s : ℝ, 0 ≤ s → ENNReal.ofReal (Fam.exponent x y s) = levyExponent b₀ ν s := by
  sorry

end Skeleton
