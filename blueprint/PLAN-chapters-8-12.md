# Chapters 8–12: a plan

Written 2026-08-10, after chapters 2–7 closed. Companion to
`DESIGN-formalization-strategy.md`, which it does not supersede.

## Why this needs a plan and chapters 2–7 did not

Chapters 2–7 were one long climb with a single interface at the top. The ledger tells a
different story about what is left:

| | chapters 2–7 | chapters 8–12 |
|---|---|---|
| `[A]` ledger entries in play | A1–A4, A17, A18 | **A7–A16** — nine of the twelve |
| trust-boundary entries spent | 2 (A17, A18) | unknown, plausibly 4–6 |
| nodes whose conclusion needs vocabulary the development lacks | 2, both restated in `LE` | at least 5 |
| Mathlib substrate | measure theory, Prokhorov, DCT — all present | Mellin, semigroups, distributions, Sonine — **surveyed separately** |

The difference is not size, it is *kind*. Chapters 2–7 were about the hemigroup family, and
almost everything about the family turned out to be provable. Chapters 8–12 are increasingly
about **classes of functions** — completely monotone, Stieltjes, complete Bernstein, HCM — and
statements about those classes are exactly what the trust boundary exists to hold at arm's
length. Expect the ratio of interface to proof to invert.

Three consequences shape the phases below: the blueprint needs splitting first, the vocabulary
question has to be settled before any Lean, and the scope should probably be cut.

---

## Phase 0 — Split the blueprint (no Lean)

The Lemma 7.1 lesson: *a node that reports the maximum cost of its clauses lies about its cheap
ones.* Splitting 7.1 into `lem:selfdecomposable-increment` and
`lem:selfdecomposable-derivative` is what let `thm:main-construction` stay off A3 and A4, and
what made A18's scope reviewable. Chapters 8–12 have the same defect in eight places.

| Node | The problem | Proposed split |
|---|---|---|
| `prop:pair-regularity` (9.7) | **Three clauses, three different costs.** (1) is a [T] restatement of three earlier nodes; (2) is A9 *entire*; (3) is A9 for two structural inputs with [T] computations joining them. | `prop:sonine-pair-exists` [T] · `prop:special-bernstein-potential` [A] · `prop:cm-sonine-pair` [A]+[T] |
| `prop:volterra` (9.8) | Identity (9.1) is a transform computation [T]; uniqueness is a scalar ODE [T]; absolute continuity is A10. The [A] tag currently shades all three. | `prop:kernel-moment-identity` [T] (9.1 + uniqueness) · `prop:volterra-density` [A] (9.2) |
| `prop:moments` (8.4) | First-moment identity and the influence curve are [T] by monotone convergence; the higher-moment equivalence is A7. The Assignment clause already says so in prose. | `prop:mean-delay` [T] · `prop:moment-criterion` [A] |
| `prop:bessel-family` (8.3) | Transform evaluation is a classical integral [T]; self-decomposability is A8; the parabolic-gauge reading is a forward reference asserted nowhere. | `prop:inverse-gamma-transform` [T] · `prop:bessel-family` [A] |
| `prop:scale-evolution` (9.2) | (1) is the chain rule; (2) is a distributional identity needing Tonelli, a Laplace inversion, and `Distr(ℝ)`. Wildly different. | `lem:transform-ode` [T] · `prop:scale-evolution` [T, hard] |
| `thm:scale-cauchy` (10.4) | Invariance / existence / uniqueness, three clauses, the third quantifying over a solution class. | three nodes, or at minimum three proofs |
| `thm:signaling-form` (11.6) | Eigenfunctions / the field solves it / uniqueness in the covariant Mellin class. | three nodes |
| `thm:locality` (12.5) | Carries **A14 and A15 on two different steps of one direction**, and (⇐) needs neither. Exactly the 7.1 shape. | split (⇒) from (⇐); within (⇒), the order bound (A14) from the Krull–Webster uniqueness (A15) |

Phase 0 output: a blueprint whose `[A]` tags sit on the clauses that actually need them, with
the numbering agreement against the draft preserved (the shared counter makes added nodes
renumber — check `linkage check` and the draft's cross-references after each split).

---

## Phase 1 — Settle the vocabulary question

`DESIGN-formalization-strategy.md` keeps `CompletelyMonotone` out of the development. Chapters 9
and 12 are, on their face, *about* complete monotonicity. So the design either bends or a
restatement is found. **This must be decided before any Lean is written**, because it determines
what the target types even say.

The forcing node is `prop:pair-regularity`(3): *κ has a completely monotone density iff k is
completely monotone iff F′ lies in the Stieltjes class.*

**Option A — define the predicate.** Reverses the design decision. `CompletelyMonotone` then
propagates through every statement that mentions it, and A1/A2 become statable as Lean axioms.
Cost is permanent and wide.

**Option B — restate representation-first, as `LE` was.** *Recommended.* Complete monotonicity
of `k` is, by Bernstein–Widder, exactly `∃ σ ≥ 0, k t = ∫ e^{-τt} σ(dτ)` — a representation, no
derivative signs. The Stieltjes class is *already written as a representation in the blueprint*:
`h(s) = a/s + b + ∫ σ(dτ)/(s+τ)`. So clause (3) can be stated in the development's existing
idiom with no new predicate, exactly as `BF₀ → LE` was handled for chapters 5–7. What crossing
that bridge costs is A1, once, in the statement — the same discipline `prop:bernstein-toolbox`(3)
already documents.

Under Option B the design decision holds and chapter 9 becomes expressible. Chapter 12's HCM
tower needs the same treatment and should be checked against it before Phase 6 is scheduled — a
representation for HCM exists but is less standard.

---

## Phase 2 — Skeleton target types, before proofs

The user's suggestion, and it lands hardest here. Writing a target type is what *forces* Phase 1
to be answered concretely rather than deferred: you cannot state `prop:pair-regularity`(3)
without having decided what "completely monotone" means in the development.

Write, `sorry`-marked, in `Formalization/Skeleton/`:

1. `prop:mean-delay`, `prop:stable-family`, `prop:gamma-family` — chapter 8's [T] core.
2. `lem:memory-kernel`, `lem:potential-kernel`, `thm:sonine-conservation`,
   `cor:exact-inversion` — chapter 9's spine.
3. `prop:sonine-pair-exists` and `prop:cm-sonine-pair` — the Phase 1 decision, made concrete.

Tag the corresponding nodes `\notready`. The graph then shows the whole of chapters 8–9 as
*stated, unproved* rather than absent, and the estimate of what remains stops being a guess.

Do **not** skeleton chapters 10–12 yet — see Phase 6.

---

## Phase 3 — Prerequisites the development does not have

Three gaps that chapters 2–7 never hit, each a prerequisite rather than a node:

- **Laplace injectivity for locally finite measures.** `laplace_injective` is proved for
  *finite* measures. `thm:sonine-conservation` compares `κ * ℓ` with Lebesgue measure and
  `prop:scale-evolution` inverts a transform — both locally finite, neither covered. This is the
  general clause of A6, currently *proved* in the restricted case and absent from the trust
  boundary. Extending it keeps A6 off the boundary; failing to extend it puts A6 on. **Attempt
  the proof before conceding the interface.**
- **The derivative `F′`.** Chapters 8 and 9 need `F'(s) = b₀ + ∫ e^{-st} k(t) dt` by
  differentiation under the integral (Mathlib has this). Worth stating plainly: the design
  excludes the *predicate* `CompletelyMonotone`, not derivatives. No conflict.
- **The potential kernel.** `lem:potential-kernel` inverts a Bernstein function and needs
  Bernstein–Widder for *locally finite* measures — A1's general form. Almost certainly a new
  interface; it should be phrased representation-first and scoped as narrowly as A17 was.

---

## Phase 4 — Chapter 8

The natural first Lean, and the warm-up already on the list: exhibit the leaky integrator
(`k = e^{-t}`) and the Dickman ray (`k = 1_{[0,1)}`) as `SelfDecomposableExponent` instances.
Then `prop:stable-family` and `prop:gamma-family`, which are concrete integral identities —
the standard representation of `s^α`, and Frullani for `log(1+s)`.

`prop:bessel-family` needs Bessel `K`. If Mathlib has no Bessel functions this node is
blueprint-only, and that is an acceptable outcome — say so in the annotation rather than
leaving it untagged and ambiguous.

---

## Phase 5 — Chapter 9, the Sonine core

The mathematically interesting chapter and the one worth the effort: `κ * ℓ ≡ 1` is a clean
theorem, and given Phase 3's injectivity it is a transform computation. `cor:exact-inversion`
follows immediately. `prop:scale-evolution`(2) is the hard node — distributional, and gated on
what Mathlib offers.

---

## Phase 6 — Chapters 10–12, gated

Do not schedule these until the Mathlib survey is in hand. Each rests on machinery the
development has never touched: C₀ semigroups, generators and cores (chapter 10, A11); the Mellin
transform and its inversion (chapter 11, A12); Courrège's classification and Krull–Webster
(chapter 12, A14/A15).

**Scope recommendation, stated plainly.** Treat chapters 8–9 as the target and 10–12 as
blueprint-only unless the survey says otherwise. That is a legitimate outcome, not a retreat:
the blueprint is the text of record, and an article whose Lean development covers §§2–9 with a
four-entry trust boundary is a stronger artifact than one that claims §§2–12 by importing a
dozen interfaces. `README.md` should say which it is.

---

## Side finding: the hub cannot see this article

`linkage demand` currently reads the wiki's **ssf** manifest — every demanded label comes back
`NOT a blueprint node yet`, because they belong to the sibling article. So the hub has no `hcs`
manifest, and demand-driven prioritisation is unavailable for this repo. Publishing one is cheap
and would let the hub's actual claims order the work above. Worth doing before Phase 0.

---

## Verification, per phase

Unchanged from chapters 2–7, and it has caught real errors at each step:

```bash
linkage check                      # blueprint / Lean / ledger / paper edges
scripts/build-blueprint.sh         # all four views — LaTeX errors the grep-based checks miss
cd Formalization && lake build     # includes the sorry guard on Hemigroup/
lake env lean CIAxiomGuard.lean    # per-declaration axiom report
```

Two rules that earned their place: every new `\leanok` node gets a `#print axioms` line in
`CIAxiomGuard.lean` in the same commit, and no ledger entry is written without a
librarian-verified page anchor.
