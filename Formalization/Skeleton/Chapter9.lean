/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
-- `Hemigroup.Sonine` rather than `MemoryKernelTransform`: Route B's main argument below uses
-- `laplaceL_volume_Ici`, which is where `thm:sonine-conservation` needed it too.
import Hemigroup.Subordinator

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

open MeasureTheory Set Filter
open scoped ENNReal Topology

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
measures (see the module docstring); existence was the open question of the chapter.

**Route B chosen 2026-08-11.** Deferring it was the right order — `sonine_conservation` is stated
against an arbitrary `ℓ` meeting the specification, so the chapter's headline turned out not to
depend on this at all and is now proved interface-free. Only `prop:sonine-pair-exists` (9.12)
needs existence.

*The route not taken.* (A) is the blueprint's own proof: `1/u` is completely monotone,
`CM ∘ BF ⊆ CM` (ledger A2), and Bernstein–Widder for general measures (ledger A1) produces the
measure. Short and faithful to the text, but A1 is precisely the entry
`DESIGN-formalization-strategy.md`'s representation-first choice exists to keep off the critical
path; taking it would falsify a design claim the article makes about its own trust base.

*The route taken.* (B) constructs the measure instead of representing it, and **never mentions
complete monotonicity** — not even as a consequence. `ℓ^{(x)}` is the subordinator's potential
measure `U = ∫₀^∞ μ_t dt`, where `μ_t` is the law A17 already supplies; its transform is
`∫₀^∞ e^{-tφ_x(s)} dt = 1/φ_x(s)` by Tonelli. The trust boundary stays at two entries.

**Route B, decomposed 2026-08-11.** The main argument below is now `sorry`-free and rests on two
explicitly named sub-lemmas, which is article-kit's decomposition gate. Writing the decomposition
down before proving any of it earned its keep again, and this time the finding is in a step the
work order called routine.

1. `exists_levyTriple_symbol` — `φ_x ∈ LE` with its triple *exhibited*. A theorem to prove, not a
   hypothesis and not an axiom. Integrating `∫₀^∞ s e^{-su} h(u) du` by parts, with
   `h(u) = k(u/x)/x`, turns it into `∫₀^∞ (1 - e^{-su}) ν(du)` with `ν = -dh`, so the triple is
   drift `b₀` and Lévy measure `-dh`. The Stieltjes measure `-dh` is the real cost: `k` is only
   `AntitoneOn`, so it needs a right-continuous modification first, and Mathlib's
   `StieltjesFunction` then produces the measure. (That name is flagged in
   `PLAN-chapters-8-12.md` as a false friend for the Stieltjes *class*; for this, the other
   meaning, it is exactly the right tool.)

2. `exists_subordinatorFamily` — the laws `μ_t`, with transform `e^{-tφ_x(s)}`, **as a measurable
   family**.

3. The rest is proved below: `U := ∫₀^∞ μ_t dt` is `Measure.bind`, its transform is Tonelli plus
   `∫₀^∞ e^{-tφ} dt = 1/φ`, local finiteness is `measure_Icc_ne_top_of_laplaceL_ne_top`, and
   uniqueness is `laplaceL_injective_of_ne_top`.

**The finding: `Measurable μ` is a hypothesis with content, and the work order omitted it.**
Step 3 was written as "`U := ∫₀^∞ μ_t dt` as a measure, and Tonelli for its transform", as though
forming `U` were bookkeeping. It is not. A17 supplies `μ_t` for each `t` **by choice,
independently**, so nothing connects the choices across `t` and `∫₀^∞ μ_t dt` is not a measure at
all — `Measure.bind` will not even typecheck without `Measurable μ`. This is the same shape as the
`IsCausal ℓ` omission that writing `sonine_conservation` found: a clause that reads as a
formality and is in fact the whole reachability of the statement.

It is not an obstacle, and the route to it is worth recording because it is where the
*subordinator* structure finally gets used rather than merely named:

* `μ_{t+t'} = μ_t ∗ μ_{t'}`, from the transform and `laplace_injective`;
* hence `t ↦ μ_t (Iic r)` is **antitone** — `μ_{t+t'}(Iic r) = ∫ μ_t(Iic (r-u)) dμ_{t'}(u) ≤
  μ_t(Iic r)`, because `μ_{t'}` is causal so `u ≥ 0` a.e. — and an antitone function is
  measurable;
* `{Iic r}` is a π-system generating the Borel σ-algebra and the `μ_t` are finite, so the sets
  where `t ↦ μ_t A` is measurable form a λ-system: Dynkin gives every Borel `A`;
* `Measure.measurable_of_measurable_coe` assembles it.

So the increasing paths of the subordinator, which Route B's prose treats as intuition, are
exactly what makes the potential measure *exist*. Nothing here needs complete monotonicity, and
the trust boundary stays at two entries.
-/

/-! ## `lem:potential-kernel` and `prop:sonine-pair-exists` -- **discharged 2026-08-11**

Route B is complete. `existsUnique_potentialKernel` and `exists_sonine_pair` have moved into the
library as `Hemigroup/PotentialKernel.lean`, together with the two steps they rest on
(`exists_levyTriple_symbol`, `exists_subordinatorFamily`) and the general machinery in
`Hemigroup/Subordinator.lean`. Their nodes are `\leanok`, and `#print axioms` gives A17 and
nothing else -- so the trust boundary is still two entries and the article's claim that the
representation-first design keeps A1 off the critical path survives contact with the proof.

What the round found, all of it by writing statements before proving them:

* `Measurable mu` was missing from the work order, and it is the whole reachability of
  `U = int mu_t dt`;
* `F.Nondegenerate` was present in `exists_levyTriple_symbol` and inert;
* `SFinite nu` was demanded by a decomposition written around an anticipated proof method
  (Tonelli), and vanished when the method turned out to be Mathlib's layer cake;
* the Stieltjes route named in the work order fails for a reason the work order did not
  anticipate -- see `Hemigroup/Subordinator.lean`.
-/

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
