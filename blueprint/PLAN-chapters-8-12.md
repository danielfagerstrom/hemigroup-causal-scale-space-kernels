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
| Mathlib substrate | measure theory, Prokhorov, DCT — all present | surveyed 2026-08-11; see below |

The difference is not size, it is *kind*. Chapters 2–7 were about the hemigroup family, and
almost everything about the family turned out to be provable. Chapters 8–12 are increasingly
about **classes of functions** — completely monotone, Stieltjes, complete Bernstein, HCM — and
statements about those classes are exactly what the trust boundary exists to hold at arm's
length. Expect the ratio of interface to proof to invert.

Three consequences shape the phases below: the blueprint needs splitting first, the vocabulary
question has to be settled before any Lean, and the scope needs a decision.

**Scope decided 2026-08-11: chapters 8–9 now, re-evaluate after.** Chapters 10–12 are not
abandoned and not scheduled; the survey below re-scopes them, and the re-evaluation happens
against finished work on 8–9 rather than against a forecast.

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

**How to split without breaking the numbering.** The blueprint's numbers agree with the draft's,
and the shared counter renumbers everything after an insertion. Chapter 7 already solved this:
*narrow the existing node in place, keeping its number, and append the split-off clause at the
end of the chapter*, where it takes a number the draft does not use (that is how
`lem:selfdecomposable-increment` and `-derivative` became 7.11 and 7.12). Follow that convention
here; record the appended numbers in each file's header comment, as chapter 7 does.

Phase 0 output: a blueprint whose `[A]` tags sit on the clauses that actually need them, with
the draft's numbering untouched. Run `linkage check` and `scripts/build-blueprint.sh` after each
split.

---

## Phase 1 — Settle the vocabulary question

`DESIGN-formalization-strategy.md` keeps `CompletelyMonotone` out of the development. Chapters 9
and 12 are, on their face, *about* complete monotonicity. So the design either bends or a
restatement is found. **This must be decided before any Lean is written**, because it determines
what the target types even say.

The forcing node is `prop:pair-regularity`(2), post-split: *κ has a completely monotone density iff k is
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
to be answered concretely rather than deferred: you cannot state `prop:pair-regularity`(2)
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

## The Mathlib substrate, surveyed 2026-08-11

The survey changed the shape of this plan, and in the opposite direction from my first guess:
chapter 11 is far more tractable than assumed and **chapter 10 is the real blocker**.

| Needed for | Mathlib | Consequence |
|---|---|---|
| **Mellin transform** (ch. 11) | `Analysis/MellinTransform.lean` — `mellin`, `MellinConvergent`, strip-holomorphy (`mellin_differentiableAt_of_isBigO_rpow`) | present and usable |
| **Mellin inversion** (ch. 11, A12) | `mellinInv_mellin_eq` — pointwise, one vertical line, L¹ both sides + `ContinuousAt`, derived from Fourier inversion | **A12 may be dischargeable rather than trusted.** No strip version and no contour shift, so "inversion anywhere in the strip" is a derivation |
| **Mellin convolution** (ch. 11) | absent — no `mellin (f ⋆ g) = mellin f · mellin g`, no packaged `dx/x` Haar measure | build it |
| **Fractional integrals** (ch. 9, 11) | absent as such, **but** `posConvolution` (the causal half-line convolution) + `betaIntegral_scaled` + `betaIntegral_eq_Gamma_mul_div` compose to the Riemann–Liouville semigroup law almost immediately | much cheaper than "absent" suggests |
| **Krull–Webster** (ch. 12, A15) | Bohr–Mollerup for Gamma is present (`Real.eq_Gamma_of_log_convex`); the internals `Real.BohrMollerup.tendsto_logGammaSeq` are already abstract in `f`, but hard-wired to the increment `log y` | **A15 is plausibly provable**, by generalising the increment. Tractable work, not reuse |
| **Pringsheim–Landau** (ch. 12, A13) | absent for integral transforms; the analytic core is present (`Analysis/Complex/Positivity.lean`, `TaylorSeries.lean`) and the Dirichlet-series analogue is proved | plausibly provable with effort |
| **C₀ semigroups, generators, cores** (ch. 10) | **absent, and so is closed-operator theory.** Only bounded generators via `NormedSpace.exp`, Banach-algebra `resolvent`, and a topological `Flow` with no linearity | **the blocker** |
| **Phillips subordination** (ch. 10, A11) | absent | interface, unavoidably |
| **Positive maximum principle, Courrège** (ch. 12, A14) | greenfield | interface, unavoidably |
| **CM / Bernstein / Stieltjes classes** | absent. `AbsolutelyMonotoneOn` exists with *no* representation theory | **confirms Phase 1's Option B is forced**, not merely preferred |
| **Laplace transform** | absent as such. `complexMGF` + `ext_of_complexMGF_eq` give genuine injectivity — but for **finite** measures only | Phase 3's locally-finite injectivity gets no help; it is real work or an interface |
| **Volterra equations** | absent; only ODE Picard–Lindelöf and `ContractingWith` | see below — less bad than it looks |
| **Log-convexity** | no `LogConvexOn` at all; only the raw `ConvexOn ℝ s (log ∘ f)` idiom, used twice | manual but fine |
| **Lévy processes, infinite divisibility** | absent | already reflected in the ledger |

### Three false friends, recorded so a future session does not misread a grep

- `MeasureTheory/Measure/Stieltjes.lean`'s `StieltjesFunction` is a **monotone right-continuous
  function used to build a measure** — *not* the Stieltjes class `S` of Bernstein-function theory.
- `Analysis/SpecialFunctions/Bernstein.lean` and `RingTheory/Polynomial/Bernstein.lean` are
  **Bernstein polynomials** (Weierstrass approximation). Unrelated to Bernstein functions.
- `Measure/LevyConvergence.lean` and `LevyProkhorovMetric.lean` are Lévy's **continuity theorem**
  and the weak-convergence metric — not Lévy-process theory.

### What this does to `prop:volterra`

"Volterra absent" reads worse than it is. The Lean content of that node, after the Phase 0 split,
is the identity (9.1) — a transform computation — and uniqueness among probability measures,
which is a scalar linear ODE in the Laplace variable. Neither needs a Volterra solution theory.
Only the *numerical* reading in `rem:volterra-computation` does, and remarks carry no Lean tag.

---

## Phase 6 — chapters 10–12, re-scoped by the survey

**Chapter 11 — attempt it.** Mellin exists, inversion exists in a usable if narrow form, and the
fractional-integral machinery for `lem:memory-fractional-integrals` is nearly free. The gaps —
Mellin convolution, inversion across a strip — are constructions, not missing theory. There is a
real prospect of **discharging A12 rather than trusting it**, which would be the same win as A5
and A6 in chapter 2.

**Chapter 12 — attempt the two provable interfaces, keep A14.** A15 (Krull–Webster) and A13
(Pringsheim–Landau) both have their machinery present in adjacent form; each is a self-contained
piece of work worth doing on its own terms. A14 (Courrège) is greenfield and stays an interface.
Check the HCM representation against Phase 1 before scheduling `prop:local-ladder`.

**Chapter 10 — blueprint-only, on current evidence.** `thm:scale-cauchy` is stated on an operator *core*, with a
generator and a `C([0,∞); X₀) ∩ C¹((0,∞); X₀)` solution class. Mathlib has no C₀-semigroup
theory and, more decisively, no closed-operator theory to build one on. Formalising this means
building Hille–Yosida-adjacent infrastructure first — a separate project, and not this article's.
Say so in the node annotation rather than leaving it untagged.

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

---

# Re-evaluation, 2026-08-11

Written after chapters 8 and 9 were taken as far as they go. This is the checkpoint the scope
decision asked for ("start with 8–9, then re-evaluate").

## What landed

| node | | how |
|---|---|---|
| `prop:admissibility-criterion` (8.7) | new | the one obligation every example shares, proved once |
| `lem:criterion-converse` (8.8) | new | the criterion is characteristic, not merely sufficient |
| `prop:stable-family` (8.1) | ✓ | antiderivative, Gamma integral at exponent `1-α` |
| `prop:gamma-family` (8.2) | ✓ | antiderivative, Gamma integral at exponent `1` |
| `lem:memory-kernel` (9.1) | ✓ | differentiation under the integral sign |
| `lem:memory-kernel-transform` (9.15) | new, ✓ | the substitution `τ = t/x` |
| `thm:sonine-conservation` (9.5) | ✓ | transform comparison; **reduces to Lean core** |

Trust boundary unchanged at two entries. 27 nodes `\leanok`.

**The ordering lesson.** The plan had chapter 8's closed forms before chapter 9. That was wrong:
both are antiderivative computations, so `lem:memory-kernel` — chapter 9's *first* lemma — is
chapter 8's tool. Proving 9.1 first bought 8.1 and 8.2 together. Where a chapter's opening lemma
is a *technique* rather than a result, it should be scheduled ahead of the chapter that reads
best first.

**The prerequisite lesson.** Phase 3 (Laplace injectivity beyond finite measures) looked at the
time like unglamorous groundwork. It is the whole of `thm:sonine-conservation`: with it in hand
the Sonine proof is twenty lines. Prerequisites found by *stating* a chapter are worth more than
the schedule suggests, because the statement is what reveals them.

## What is blocked, and on what

`lem:potential-kernel`'s existence half is deferred by decision, not stalled — see
`Formalization/Skeleton/Chapter9.lean` for the two routes and what each costs. Everything else
left in chapter 9 waits on it or is an `[A]` node.

## Chapters 10–12 against Mathlib as it stands today

The 2026-08-09 survey is out of date in one direction and confirmed in the others.

**Mathlib now has distributions.** `Analysis/Distribution/` carries test functions, the space
`𝓓'(Ω,F)`, `delta`, and `lineDerivCLM` — a distributional directional derivative as a continuous
linear map. So the blanket claim "Mathlib has no distribution theory" is **false as of this
check**, and `prop:scale-evolution`'s status note has been corrected. It is still not enough:
the file's own docstring says it "contains very few mathematical statements", and what
`prop:scale-evolution` and `cor:exact-inversion` need — the embedding of a locally integrable
function as a distribution, and convolution of a distribution with a measure — is not there.
Closer than it was, and worth re-checking each time Mathlib is bumped, rather than treated as
permanently out of reach.

**Mellin is available.** `Analysis/MellinTransform.lean` *and* `Analysis/MellinInversion.lean`.
Chapter 11's `lem:mellin-data` and `lem:symbol-uniqueness` are the most likely next formalisable
nodes outside chapter 9, and ledger A12 (Mellin inversion on a strip) may be retirable rather
than cited. That is worth checking before any of chapter 11 is attempted, because A12 is the
chapter's spine.

**No Bessel functions.** `K_a` is absent, so `prop:bessel-family` (8.3), `ex:bessel-quadratic`
(11.10) and `thm:locality` (12.5) — the whole memory line — cannot be *stated*, let alone proved.
This is unchanged and is not a scheduling problem: it is a missing Mathlib theory.

**No semigroup generator theory.** Nothing matching a `C₀`-semigroup or Hille–Yosida. Chapter
10's `thm:scale-cauchy` (Theorem 3′) and `lem:generator-properties` are out of reach, and A11
(Phillips subordination) stays cited.

**Bohr–Mollerup is available**, as the original plan noted, which is what chapter 12's
`lem:log-convexity` would use — but `thm:locality` above it needs Bessel, so the lemma would be
formalised into a chapter whose conclusion cannot be stated.

## Recommendation

1. **Decide `lem:potential-kernel`.** It is the only thing blocking the rest of chapter 9, and it
   is a review decision, not work.
2. **Then chapter 11's Mellin nodes**, not chapter 10. `lem:mellin-data` and
   `lem:symbol-uniqueness` are the only nodes in 10–12 with a real Mathlib substrate. Check first
   whether `MellinInversion` retires ledger A12; if it does, that is worth more than the nodes.
3. **Chapters 10 and 12 are not schedulable** until Mathlib grows semigroup theory and Bessel
   functions respectively. They should be recorded as blocked-on-upstream in `README.md` rather
   than carried as pending work — the distinction matters, because the first is a queue and the
   second is a dependency.

---

# Decisions taken, 2026-08-11 (evening)

## Ledger A1 agrees with `scale-space-foundations`

The original plan required that A1's anchor here agree with SSF's A5 — same theorem, and a
disagreement would mean one of them is wrong. **Checked: they agree exactly.** Both point at
[Feller] Vol. 2, §XIII.4, Theorem 1 together with Theorem 1a, pp. 439–440, and both record the
anchor as verified against the held scan.

One structural difference, not a conflict: SSF's A5 is composite — Bernstein *plus* "the power
symbol is a Bernstein function for `0 ≤ α ≤ 1`" — where this article's A1 is Bernstein alone and
the composition rule is A2, pinned separately. SSF's own note flags that its composition clause
is not pinned to a numbered line; ours is. The finer split is the better one, and if the two
articles are ever reconciled it should be in this direction.

## `lem:potential-kernel`: Route B

Decided. The potential kernel is built as the subordinator's potential measure, not represented
via Bernstein–Widder. **The trust boundary stays at two entries**, and the article's claim that
the representation-first design keeps A1 off the critical path survives.

The point worth recording, because it is easy to state wrongly: Route B does not use a
*consequence* of complete monotonicity. It does not use complete monotonicity at all. The
classical argument proves `1/φ_x` is CM and then invokes Bernstein–Widder to produce a measure;
Route B produces the measure directly, by integrating the subordinator's laws over time. Nothing
in the development ever needs the predicate.

Work order is in `Formalization/Skeleton/Chapter9.lean`. The one real cost is the Stieltjes
measure `-dk`, which needs a right-continuous modification of `k` first — `k` is only
`AntitoneOn` by hypothesis, and that has been the recurring tax of this development.

## Chapter 10 is a leaf; chapter 11 is not blocked by it

Checked against the `\uses` graph rather than assumed. `thm:scale-cauchy` (Theorem 3′) is used by
exactly one node — `rem:recovering-thm3`, inside chapter 10 itself. So are
`def:phillips-generator`, `lem:generator-properties` and `prop:fixed-scale-semigroup`. Mathlib's
missing semigroup theory therefore blocks **only that leaf**, not the article.

Chapter 11 needs one node from chapter 10: `lem:delay-core`, via `lem:memory-fractional-integrals`.

And a correction to a natural guess: **Theorem 4′ is not derived from the Sonine pairs.**
`thm:signaling-form` uses the standing hypothesis, `lem:mellin-data`, `def:inversion-operator`,
`lem:symbol-uniqueness`, `lem:memory-fractional-integrals`, `def:cascade-family` and
`thm:main-characterization` — no chapter 9 node appears. The Sonine line and the signalling line
are parallel developments off the main characterization, not sequential.

**Consequence for priority.** Theorem 4′ needs Mellin — which Mathlib has, transform *and*
inversion — plus `lem:delay-core`. It does not need semigroup theory. Chapter 11 is therefore
the most reachable unformalized part of the article, not the least, and the earlier
recommendation understated it. Given that the signalling form is the formulation the author
intends to build on, it should be promoted above finishing chapter 9.

## The A12 check, 2026-08-11

Asked because ledger A12 is chapter 11's spine and Mathlib turned out to have
`Analysis/MellinInversion.lean`. **Answer: A12 is not retired.** Full reasoning in the ledger
entry; the short form is that Mathlib's `mellinInv_mellin_eq` requires the *inversion* integral to
converge absolutely (`VerticalIntegrable (mellin f) σ`), where Widder's Theorem 9a takes a
symmetric limit and therefore covers conditionally convergent inversion integrals. Mathlib's
`mellinInv` is an ordinary line integral, not a principal value.

The standing hypothesis (H) does not close the gap and is not the kind of hypothesis that could:
`z_*` is the abscissa of the negative-moment function, so (H) fixes the **width of the strip** on
which the forward transform converges. Vertical integrability is **decay along the line**. The two
are orthogonal.

**This is a better outcome than a bare "no".** It converts a formalisation question into a
mathematical one with a known price: A12 becomes retirable the moment (H) or
`def:inversion-operator` carries a vertical-decay clause. Whether that clause is acceptable is a
question about the article, and it should be checked family by family before it is adopted — the
stable family's symbol is a ratio of Gammas and decays exponentially, the Gamma family's is
rational and decays only polynomially and may fail. That check is cheap and worth doing, because
it also tells us whether Theorem 4′ as stated is about a class the examples actually inhabit.

**Revised order for chapter 11.** The Mellin substrate is real but does not reach the chapter's
spine unchanged, so the chapter is not the free win the previous section suggested. Its cheapest
genuine target is instead `lem:mellin-data` — the *forward* transform and its strip, where
`MellinConvergent` and (H) line up directly and no inversion is involved. That node is worth
doing on its own account, and doing it will settle the vertical-decay question empirically for the
families, which is what the retirement decision needs.

### Correction to the A12 check, same day

The section above concluded that A12 is not retired because Mathlib needs absolute convergence of
the inversion integral where Widder does not, and that closing the gap would cost a new
vertical-decay hypothesis to be checked family by family. **The conclusion was wrong, and it was
wrong for an avoidable reason: I compared Mathlib against Widder's theorem instead of against the
article's use of it.**

`def:inversion-operator` already assumes the inversion integrand is absolutely integrable on the
line — it is written into the definition's quantifier. So the article never relies on Widder's
conditional-convergence generality, and A12's own Assignment clause already says the entry carries
only the sufficiency of absolute integrability. That is exactly `mellinInv_mellin_eq`'s
hypothesis.

`lem:mellin-data` also already proves the vertical integrability that I said would have to be
assumed: `H̃(z) = Γ(z) E[T_1^{−z}]`, and `|Γ(c+iτ)|` decays super-polynomially. The symbol `B`
alone does grow — the Γ factors cancel in the ratio — but `B` is never inverted alone; it
multiplies a transform carrying the Γ decay, and the product is `H̃(z+1)`.

**Revised conclusion.** A12 is retirable at a formalisation cost, not a mathematical one. The two
remaining pieces are matching the operator formulation to Mathlib's function-recovery statement,
and supplying `ContinuousAt`. Neither touches the article's hypotheses. Attempt this before
treating A12 as permanent.

**The general lesson, worth more than the specific finding.** The question "does Mathlib retire
this ledger entry?" is not answered by comparing Mathlib to the *cited theorem*. Ledger entries
name a citation, but what they actually carry is the article's *use* of it, which is often
narrower — here, narrower in exactly the direction that made the difference. Read the Assignment
clause and the consuming node first; the citation is the last thing to compare against.

---

# Chapter 11's entry point, proved — 2026-08-11 (late)

`lem:mellin-data` is machine-checked, as
`Hemigroup.SelfDecomposableExponent.mellin_profile` and `norm_mellin_profile_le`. Trust boundary
unchanged at two entries; `#print axioms` gives A17 and nothing else, inherited through `kernel`
because `T₁` is `μ_{0,1}`. 28 nodes `\leanok`.

## The hinge did what the plan hoped, and one thing it did not

The `ℝ≥0∞` computation `∫∫ s^{c-1}e^{-ts} ds dμ(t) = Γ(c)·E[T₁^{-c}]` was written first, on the
grounds that it is the Fubini side condition, the bound, and the vertical-integrability statement
at once. Two of those three came out of it in a few lines each, exactly as expected. The third
did not, and the reason is the finding of this round.

What the hinge *did* settle, and it is worth recording because it is the reusable part: it makes
the exchange of integrals licensed **iff** `c < z_*`. The left-hand side is the total mass of the
absolute value against the product measure, so joint integrability is not merely implied by the
strip condition — it is equivalent to it. That is `prop:admissibility-criterion`'s shape a second
time, and it is what stopped a hypothesis being invented for the Fubini step.

It also showed that the first clause of (H) is load-bearing rather than decorative. `F(∞) = ∞` is
used exactly once, to give `T₁ > 0` a.s.; without it the hinge is *false*, because the inner Gamma
integral diverges at an atom that `negMoment`, an integral over `(0,∞)`, cannot see.

## The A12 finding: the obstacle is upstream, and the earlier readings misplaced it twice

The bound `|H̃(c+iτ)| ≤ E[T₁^{-c}]·|Γ(c+iτ)|` is proved. Integrating it in `τ` needs the
super-polynomial decay of `|Γ(c+iτ)|`, and **Mathlib has no bound on `‖Complex.Gamma‖` along a
vertical line at all**: `Analysis/SpecialFunctions/Stirling.lean` is Stirling for `n !` only.

So the A12 story now has three readings, and the third is a different *kind* of answer:

| | reading | where the cost sits |
|---|---|---|
| first | compare Mathlib to the **cited theorem** (Widder 9a) | a new vertical-decay hypothesis, to be checked family by family — **wrong** |
| correction | compare Mathlib to the article's **use** of it (`def:inversion-operator`) | a formalisation cost: the operator formulation and `ContinuousAt` — right about the article, **incomplete about Lean** |
| this round | **write the statement in Lean and try** | an upstream gap: `Γ`'s vertical decay, absent from Mathlib |

The correction's own general lesson was that reading the Assignment clause beats reading the
citation. That is true and it was not enough: getting the mathematical question right can still
miss a lemma the Lean proof needs and the paper takes for granted. Attempting the statement is
what located this one, in an afternoon.

**Consequence for scheduling.** A12 is still retirable and still costs the article nothing. But it
is now a *dependency*, not a *queue item*: either Γ's decay arrives upstream, or it is proved here
as a piece of work in its own right (Stirling in the complex plane, or the reflection formula plus
a bound on `|1/Γ|` — neither small). It belongs on the same list as chapter 10's semigroup theory
and chapter 12's Bessel `K`, not ahead of it.

## The blueprint surgery this forced

`lem:mellin-data` stated four things — identity, bound, vertical integrability, and the symbol `B`
with its meromorphy — of which the first two are now proved, the third is blocked upstream, and
the fourth is complex analysis on a strip. That is the Lemma 7.1 shape for the third time, so 11.2
was narrowed in place and the split-off clauses appended as `lem:mellin-vertical` (11.13) and
`lem:inversion-symbol` (11.14). The `\uses` edges of 11.3, 11.4, 11.6, 11.8 and 11.9 were rewired
onto whichever of the three they actually consume, and 11.2's edge to `prop:moment-criterion`
(ledger A7) was dropped: that node is about *positive* integer moments, and what is left of 11.2
is about negative ones. The Lean is the check — A7 appears nowhere in `#print axioms`.

**The general point, since it has now recurred at every split.** Narrowing a node means narrowing
its edges too. An edge left behind on a node that no longer uses it is not harmless: it puts a
`\leanok` node behind a cited interface in the graph, which is precisely the claim the graph
exists to make checkable.

## Next

1. `lem:inversion-symbol` (11.14) — analyticity of `H̃` on the strip and the meromorphy of `B`.
   It is what `def:inversion-operator`, `lem:symbol-uniqueness` and `rem:poles` all consume, so it
   is the gate on the rest of chapter 11. Mathlib has `mellin_differentiableAt_of_isBigO_rpow`.
2. `lem:symbol-uniqueness` (11.4) — the node that earns the definite article in "the" inversion.
3. `lem:potential-kernel`, Route B, to unblock the rest of chapter 9.

---

# `lem:inversion-symbol` proved — 2026-08-11 (same round)

Item 1 above, done the same day it was scheduled. `Hemigroup/InversionSymbol.lean`: `H̃` analytic on
`0 < Re z < z_*`, non-vanishing at the real points, zeros isolated, and the symbol
`B(-z) = z·E[T₁^{-z-1}]/E[T₁^{-z}]` analytic off those zeros and meromorphic on `0 < Re z < z_*-1`.
A17 and nothing else; 29 nodes `\leanok`.

## The route the plan named was not the route that worked

The plan said "Mathlib has `mellin_differentiableAt_of_isBigO_rpow`", and it does — but using it
means proving `H(s) = O(s^{-a})` for every `a < z_*`, which is true (`H` is antitone, so
`H(s)s^a/a ≤ ∫₀^s u^{a-1}H(u)du ≤ Γ(a)E[T₁^{-a}]`) and is *work*, and which re-derives from the
Mellin integral exactly what `lem:mellin-data` already says.

The identity gives a shorter route, and the shortness is not the interesting part. `m(z) =
E[T₁^{-z}] = E[e^{-z log T₁}]` is the **complex MGF of `-log T₁`**, so Mathlib's
`analyticAt_complexMGF` applies, and its hypothesis is that `Re z` lie in the *interior* of the set
of exponents `c` with `E[T₁^{-c}] < ∞`. That set contains `(0, z_*)`, which is open — so the
interior step is free and no boundary case arises — and membership is
`negMoment_ne_top_of_lt_zStar`, already proved for `lem:mellin-data`.

**So the strip of analyticity and the strip of the identity are the same strip for the same
reason**, not two conditions that happen to coincide. That is worth more than the saved lines: it
says `z_*` is a single abscissa governing the whole chapter, which is what the article claims and
what a proof through `IsBigO` would have obscured behind an unrelated decay estimate.

**The transferable form of the lesson.** When a node's content is `f = g·h` with `g` and `h`
already understood, prove the *analytic* facts about `f` through the factorisation rather than
through `f`'s own defining integral. Chapter 9 learned the same thing about `lem:memory-kernel`
being a technique rather than a result; this is the complex-analytic version.

## Two smaller things worth keeping

**The closed form needs no non-vanishing hypothesis.** `B(-z) = H̃(z+1)/H̃(z) = z m(z+1)/m(z)` is
`Γ(z+1) = zΓ(z)` and nothing else, and Lean's `x/0 = 0` makes both sides vanish together at a zero
of `H̃`. Stating it unconditionally is the honest choice: a hypothesis `H̃(z) ≠ 0` would read as
though it had been checked, when in fact it is not needed.

**Non-vanishing is proved at the real points, and that is the whole of it.** `Γ(c) > 0` and
`E[T₁^{-c}] > 0` for real `c ∈ (0, z_*)`; the identity theorem on the strip — convex, hence
preconnected — turns that into isolated zeros everywhere. `lem:symbol-uniqueness` consumes exactly
this, so it is now unblocked.

## Next

1. `lem:symbol-uniqueness` (11.4). Its proof is: evaluate both candidate symbols on the profiles,
   take Mellin transforms, cancel `H̃` off the isolated set just proved, conclude everywhere by
   meromorphy. Both inputs are now in the library.
2. `lem:potential-kernel`, Route B, to unblock the rest of chapter 9.
3. Unchanged and still not schedulable: `lem:mellin-vertical` (Γ's vertical decay, missing
   upstream), chapter 10 (semigroup theory), chapter 12 (Bessel `K`).

---

# `lem:symbol-uniqueness`: the rigidity half proved, the rest is A12 — 2026-08-11

`Hemigroup/SymbolUniqueness.lean`. A17 and nothing else; 30 nodes `\leanok`.

## The node split again, and this time it marks the chapter's boundary

11.4 runs in two steps. Step 1 turns the operator relation `A[H(s·)] = s H(s·)` into a relation
between Mellin transforms — that is `def:inversion-operator`'s transform-level identity, which is
exactly what ledger **A12** carries. Step 2 cancels `H̃` off its isolated zeros. Step 2 is the
mathematical content: it is what makes the eigenfunction relation *pin* the symbol rather than
merely constrain it. It is now `lem:symbol-rigidity` (11.15) and proved; 11.4 keeps its number and
its statement and stays unproved.

**This is where chapter 11 stops being a queue.** With 11.2, 11.14 and 11.15 done, every remaining
node in the chapter — 11.3 itself, 11.4's step 1, 11.5, 11.6 — runs through
`def:inversion-operator`. So chapter 11 now joins chapters 10 and 12 on the blocked-upstream list,
and for a sharper reason than either: not a missing theory but a single missing estimate, the
vertical decay of `|Γ(c+iτ)|`. Everything on this side of that estimate is done.

That is a better place to have stopped than it sounds. The chapter's three genuinely mathematical
nodes are formalised, and the boundary is now a single named lemma rather than a vague
"Mathlib doesn't have Mellin theory".

## What Lean forced the prose to decide

The draft concludes `B₁ = B₂ on the strip`. For meromorphic symbols — and `B(-z) =
H̃(z+1)/H̃(z)` has poles at the zeros of `H̃` — pointwise equality of functions is the wrong
reading: in Lean a function still has a value at a pole, a junk one, so the statement as written
would be false. The unconditional form is agreement on a punctured neighbourhood of every point,
which is what equality of *meromorphic* functions means and what "everywhere on the strip by
meromorphy" is actually asserting. Pointwise equality comes back under a continuity hypothesis
that says, in as many words, that the symbols have no poles.

Both are proved and a consumer has to pick. **The general point:** where a paper says "equal" of
objects that are only defined up to a discrete set, the formalisation cannot stay silent about
which equality, and the choice it is forced into is information the prose was eliding. Compare the
`BF₀` / `LE` discipline: the same phenomenon one level down.

## Next

1. `lem:potential-kernel`, Route B — now the only schedulable item, and it unblocks the rest of
   chapter 9 (`prop:sonine-pair-exists`, `cor:exact-inversion`). Work order is in
   `Formalization/Skeleton/Chapter9.lean`; the one real cost is the Stieltjes measure `-dk`, which
   needs a right-continuous modification of `k` first.
2. If Route B lands, `prop:sonine-pair-exists` (9.12) follows immediately.
3. Blocked upstream, unchanged: A12's Γ estimate (chapter 11), semigroup theory (chapter 10),
   Bessel `K` (chapter 12).

---

# Route B decomposed; the main argument is sorry-free — 2026-08-11

`Skeleton/Chapter9.lean`. `existsUnique_potentialKernel` now carries no `sorry` and rests on two
explicitly named sub-lemmas — article-kit's decomposition gate, in the shape it was written for.
What is proved is the *sufficiency* of the decomposition, before any of the hard analysis: the
mixture is `Measure.bind`, its transform is Tonelli plus `∫₀^∞ e^{-tφ} dt = 1/φ`, local finiteness
is `measure_Icc_ne_top_of_laplaceL_ne_top`, uniqueness is `laplaceL_injective_of_ne_top`.

## The finding: `Measurable μ` is a hypothesis with content

The work order wrote step 3 as "`U := ∫₀^∞ μ_t dt` as a measure, and Tonelli for its transform",
as though forming `U` were bookkeeping. **It is not.** A17 supplies `μ_t` for each `t` *by choice,
independently*, so nothing connects the choices across `t`; `∫₀^∞ μ_t dt` is not a measure, and
`Measure.bind` does not typecheck without `Measurable μ`.

Not an obstacle — but the route to it is where Route B's *subordinator* finally does work rather
than being named:

* `μ_{t+t'} = μ_t ∗ μ_{t'}`, from the transform and `laplace_injective`;
* hence `t ↦ μ_t(Iic r)` is **antitone** (`μ_{t+t'}(Iic r) = ∫ μ_t(Iic (r−u)) dμ_{t'}(u) ≤
  μ_t(Iic r)`, since `μ_{t'}` is causal), and antitone functions are measurable;
* `{Iic r}` is a π-system generating the Borel sets and the `μ_t` are finite, so Dynkin lifts that
  to every Borel set;
* `Measure.measurable_of_measurable_coe` assembles it.

The increasing paths, which Route B's prose treats as intuition, are exactly what make the
potential measure *exist*.

**Same shape as two earlier findings, and that is now a pattern worth naming.** `IsCausal ℓ` was
missing from `sonine_conservation`'s specification; `laplaceL` rather than `laplace` was wrong in
the same statement; `Measurable μ` is missing from this work order. Each reads as a formality and
each carries the reachability of the statement it belongs to. **Writing the decomposition down
before proving it is what finds them**, and it costs an afternoon where discovering them
mid-proof costs a rewrite.

## Next

1. `exists_levyTriple_symbol` — the Stieltjes measure `-d[k(·/x)/x]` and the integration by parts.
   The larger of the two, and the one that needs a right-continuous modification of `k`.
2. `exists_subordinatorFamily` — A17 per `t`, then the measurability argument above.
3. Then `prop:sonine-pair-exists` (9.12) follows immediately, and chapter 9 closes except for its
   `[A]` nodes.

---

# Route B: the measurable family, proved — 2026-08-11

`Hemigroup/Subordinator.lean` (new, three general lemmas, all Lean core) plus the assembly in
`Skeleton/Chapter9.lean`. **Route B now has exactly one open sub-lemma**,
`exists_levyTriple_symbol`.

## The measurability gap is closed, and Mathlib had the hard part

`Measurable.measure_of_isPiSystem` is the Dynkin step, already in Mathlib and stated for exactly
this situation: measurability of `a ↦ μ a s` on a generating π-system plus finiteness gives it on
every measurable set. With `borel_eq_generateFrom_Iic`, `isPiSystem_Iic` and `Antitone.measurable`
alongside it, the whole argument is about twenty lines. The part that is *ours* is the single
inequality `conv_Iic_le`: convolving with a causal probability measure can only move mass right,
so it can only decrease the cumulative distribution — the increasing paths of the subordinator,
stated at the level of measures.

**What that inequality is doing is worth stating plainly.** Route B was chosen because it
constructs the potential measure rather than representing it, and the article's prose describes it
as "integrating the subordinator's laws over time". Formalising it shows the subordinator is not
decoration: without `μ_{t+t'} = μ_t ∗ μ_{t'}` and causality there is no antitonicity, without
antitonicity no measurability, and without measurability no measure. The increasing paths are what
make `U` *exist*.

## A note on where general lemmas live

`levyExponent_smul`, `conv_Iic_le` and `measurable_of_antitone_measure_Iic` are fully proved and
mention nothing of chapter 9, so they belong in `Hemigroup/`, not in the skeleton — even though
their only consumer is a statement that still carries a `sorry` upstream. The consequence is that
CI's sorry guard cannot see them, so they are listed in `CIAxiomGuard.lean` explicitly; that is
the only check that they are interface-free. Worth remembering as the general rule: **a proved
general lemma goes in the library whatever the state of its consumer**, and the guard list is what
keeps that from being a hole.

## Next

1. `exists_levyTriple_symbol` — the last open piece of Route B, and the largest: the Stieltjes
   measure `-d[k(·/x)/x]` (needing a right-continuous modification of `k`, since `k` is only
   `AntitoneOn`) and the integration by parts that turns `s∫e^{-su}h(u)du` into
   `∫(1-e^{-su})ν(du)`.
2. `prop:sonine-pair-exists` (9.12), which is `existsUnique_potentialKernel` plus
   `sonine_conservation` plus σ-finiteness of `ℓ` from local finiteness and causality.
