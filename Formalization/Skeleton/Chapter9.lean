/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.MemoryKernel

/-!
# The target types of chapter 9

**This file carries `sorry`s and is not part of the `Hemigroup` library.** Phase 2 of
`blueprint/PLAN-chapters-8-12.md`: state the chapter before proving it, so that the design
decisions are taken once, visibly, and the remaining work becomes countable rather than
estimated.

Writing these down has already earned its keep — three findings that a proof-first order would
have hit one at a time, halfway through:

**1. The vocabulary question is settled, and the design does not bend.** `HasCMRep` and
`HasStieltjesRep` in `Hemigroup/MemoryKernel.lean` state complete monotonicity and the Stieltjes
class as *representations*. `prop:pair-regularity`(2) is expressible with no new predicate. See
that file's docstring.

**2. Two statements here needed something the development did not have** — Laplace injectivity
for measures that are not finite, since `κ^{(x)}`, `ℓ^{(x)}` and Lebesgue measure are none of
them finite and `sonine_conservation` compares them. **Discharged 2026-08-11** as
`Hemigroup.laplaceL_injective_of_ne_top`, so ledger A6 stays off the trust boundary in its
general form too. Writing these statements is what showed it was a prerequisite rather than a
detail; the sharpening it produced — that the real hypothesis is convergence of the transform at
one point, not local finiteness — came out of trying to prove it.

**3. `lem:potential-kernel` is where a third trust-boundary entry would enter.** It asserts a
measure with a prescribed Laplace transform, which is Bernstein–Widder in its general
(locally finite) form — ledger A1. Unlike A17 and A18 this one is *not* forced yet: the function
whose transform is prescribed is `1/φ_x`, and the development might reach it through the
subordinator correspondence it already trusts. Deciding that is Phase 5 work, and the statement
below is deliberately written so either route can discharge it.
-/

namespace Skeleton

open MeasureTheory Set
open scoped ENNReal

open Hemigroup Hemigroup.SelfDecomposableExponent

variable (F : Hemigroup.SelfDecomposableExponent)

/-! ## `lem:memory-kernel` — **discharged 2026-08-11**

The derivative formula `F'(s) = b₀ + ∫₀^∞ e^{-st} k(t) dt` has moved into the library as
`Hemigroup.SelfDecomposableExponent.hasDerivAt_toRealExponent`, and its node is `\leanok`.

What it cost, against what was expected: the differentiation itself is Mathlib's, and every side
condition turned out to be free. The dominating function `e^{-(s/2)t} k(t)` is integrable because
`lem:criterion-converse` extracts both integrability facts from class membership, so no
hypothesis on `k` beyond the structure's own fields is needed. The chapter was written as though
`∫₀¹ k < ∞` were a condition to check per family; it is not.

What remains of the draft's Lemma 9.1 is its second clause, the memory kernel's transform, split
off as node 9.15 and stated below — the two clauses cost differently, and a node reporting the
maximum cost of its clauses misreports its cheap ones.
-/

/-! ## `lem:memory-kernel-transform` — **discharged 2026-08-11**

`laplace (F.memoryKernel x) s = F.symbol x s / s` has moved into the library as
`Hemigroup.SelfDecomposableExponent.laplace_memoryKernel`, and its node is `\leanok`.

The mathematical content is one substitution, `τ = t/x`. What it cost is measure-theoretic
bookkeeping: `κ^{(x)}` is the first object here that is neither finite nor a probability measure,
`laplace` is a Bochner integral, and the measure is a sum of an atom and a density — so the
integrability of the exponential has to be established separately against each piece, and the
density is only a.e. measurable because `k` is.
-/

/-! ## `lem:potential-kernel`

Existence *and* uniqueness of `ℓ^{(x)}`. Uniqueness is Laplace injectivity for locally finite
measures (see the module docstring); existence is the open question of the chapter, and as of
2026-08-11 it is **deliberately deferred**, not stalled.

**Why deferring is the right order.** `sonine_conservation` below is stated against an arbitrary
`ℓ` meeting the specification rather than against a chosen one, so the chapter's headline does
not depend on how existence is discharged — only `prop:sonine-pair-exists` (9.12) does. Proving
Sonine first therefore costs no interface and settles whether the potential kernel is on the
critical path at all.

**The two routes, when the decision comes.** (A) The blueprint's own proof: `1/u` is completely
monotone, `CM ∘ BF` is `CM` (ledger A2), and Bernstein–Widder for general measures (ledger A1)
produces the measure. Short and faithful, but A1 is precisely the entry
`DESIGN-formalization-strategy.md`'s representation-first choice exists to keep off the critical
path, so taking it would falsify a design claim this article makes. (B) The subordinator's
potential measure: `U = ∫₀^∞ μ_t dt` with `μ_t` from A17, already on the boundary, whose
transform is `∫₀^∞ e^{-tφ_x(s)} dt = 1/φ_x(s)` by Tonelli. This adds no entry, but needs
`φ_x ∈ LE` with its triple exhibited — drift `b₀`, Lévy measure `-dk` — and `k` is only
`AntitoneOn`, so it needs a right-continuous modification before a Stieltjes measure exists.
-/

/-- **`lem:potential-kernel`.** The potential kernel exists, is unique, and scales. -/
theorem existsUnique_potentialKernel {x : ℝ} (hx : 0 < x) :
    ∃! ℓ : Measure ℝ, IsCausal ℓ ∧ (∀ T : ℝ, ℓ (Icc 0 T) ≠ ⊤) ∧
      ∀ s : ℝ, 0 < s → laplace ℓ s = (F.symbol x s)⁻¹ := by
  sorry

/-! ## `thm:sonine-conservation` and its corollary -/

/-- **`thm:sonine-conservation`.** `κ^{(x)} ∗ ℓ^{(x)} = Leb` on `[0,∞)`.

Stated against an arbitrary `ℓ` satisfying the potential-kernel specification rather than
against a chosen one, so that it does not depend on how `existsUnique_potentialKernel` is
discharged.

**`IsCausal ℓ` added 2026-08-11**, and it is not a formality. Without it the statement is not
reachable by the only available route and is very likely false: the proof compares transforms
and concludes with `laplaceL_injective_of_ne_top`, which needs both measures carried by
`[0,∞)`, and `IsCausal (μ ∗ ν)` needs it of both factors too. The specification as first written
pinned `ℓ` only through its transform on `(0,∞)`, which does not confine a measure to the
half-line. `lem:potential-kernel` asserts causality of `ℓ^{(x)}` and always did — the omission
was in this statement, not in the mathematics, and writing the proof is what found it. -/
theorem sonine_conservation {x : ℝ} (hx : 0 < x) (ℓ : Measure ℝ) [SFinite ℓ] (hcaus : IsCausal ℓ)
    (hℓ : ∀ s : ℝ, 0 < s → laplace ℓ s = (F.symbol x s)⁻¹) :
    (F.memoryKernel x ∗ ℓ).restrict (Ici 0) = volume.restrict (Ici 0) := by
  sorry

/-- **`prop:sonine-pair-exists`**, the node split out in Phase 0: at the level of measures the
pair is unconditional. A collation of the three results above, and the reason it is worth
stating separately is that it needs no ledger entry, where the regularity clauses do. -/
theorem exists_sonine_pair {x : ℝ} (hx : 0 < x) :
    ∃ ℓ : Measure ℝ, IsCausal ℓ ∧ (∀ T : ℝ, ℓ (Icc 0 T) ≠ ⊤) ∧
      ∃ _ : SFinite ℓ, (F.memoryKernel x ∗ ℓ).restrict (Ici 0) = volume.restrict (Ici 0) := by
  sorry

/-! ## `prop:pair-regularity`(2), the Phase 1 decision made concrete

The statement that forced the vocabulary question. Note that no predicate `CompletelyMonotone`
appears: `HasCMRep` and `HasStieltjesRep` are representations, and the equivalence below is
therefore statable in the development's existing idiom.

Crossing to the blueprint's derivative-sign reading of the same classes costs ledger **A1**,
once, in the statement — never inside a proof. That is the discipline `prop:bernstein-toolbox`(3)
already documents for `BF₀` against `LE`.
-/

/-- **`prop:pair-regularity`(2).** `κ^{(x)}` has a completely monotone density iff `k` does,
iff `F'` is Stieltjes. -/
theorem hasCMDensity_iff {x : ℝ} (hx : 0 < x) :
    (HasCMDensity (F.memoryKernel x) ↔ HasCMRep F.k) ∧
      (HasCMRep F.k ↔ HasStieltjesRep (deriv F.toRealExponent)) := by
  sorry

end Skeleton
