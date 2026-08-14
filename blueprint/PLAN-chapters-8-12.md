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

---

# `prop:sonine-pair-exists` reduced to the same one sub-lemma — 2026-08-11

Three lines once `lem:potential-kernel` was decomposed, plus one library lemma. **Chapter 9's
whole `[T]` remainder now waits on exactly one thing**, `exists_levyTriple_symbol`.

The only content of its own was σ-finiteness. `thm:sonine-conservation` is stated for an `SFinite`
measure because it convolves; `lem:potential-kernel` delivers *local* finiteness. For a causal
measure the two coincide — exhaust `[0,∞)` by the `[0,n]`, everything below the origin is null —
and that is `sigmaFinite_of_isCausal_of_measure_Icc_ne_top`, the converse of the implication
chapter 9 already needed in the other direction (`measure_Icc_ne_top_of_laplaceL_ne_top`: a
convergent transform forces local finiteness).

**Worth noting as a pattern.** Both implications are about the *same* pair of properties, and each
was discovered by writing a statement that needed it rather than by planning for it. A chapter's
"regularity plumbing" is not a fixed list one can enumerate up front; it accumulates from the
statements, which is another argument for the statement-first order.

## Next

1. `exists_levyTriple_symbol`, the last open piece of chapter 9's `[T]` line.
2. After it: chapter 9's remaining nodes are `[A]` (`prop:pair-regularity` on A9,
   `prop:volterra-density` on A10) or distributional (`prop:scale-evolution`,
   `cor:exact-inversion`), so the chapter closes to what its ledger entries allow.

---

# Route B step 1, decomposed; two findings — 2026-08-11

`exists_levyTriple_symbol` is `sorry`-free and rests on three named sub-lemmas
(`exists_tailMeasure`, `lintegral_one_sub_exp_eq_tail`, `tendsto_k_atTop_nhds_zero`), of which
only the first is substantial. The chain from there to `prop:sonine-pair-exists` is complete.

## Finding 1: nondegeneracy is not needed, and the statement said it was

The skeleton statement carried `hnd : F.Nondegenerate`, inherited from its consumers, and the
proof never touches it. The triple exists for **every** admissible `F`, degenerate ones included,
because the identity `φ_x(s) = b₀s + s∫e^{-su}h(u)du` is just `hasDerivAt_toRealExponent`
rearranged through `integral_dilate_k`. (ND) enters chapter 9 only where `1/φ_x` has to make sense
— `symbol_pos`, inside `lem:potential-kernel` proper. Hypothesis dropped.

Worth contrasting with the earlier findings, which all ran the other way: `IsCausal`, `laplaceL`
and `Measurable μ` were *missing* clauses that carried the reachability of their statements. This
one is a clause that was **present and inert**. Both directions are failures of the same kind —
the statement not saying what the proof needs — and both are found the same way, by writing the
statement and trying.

## Finding 2: the Stieltjes route does not survive contact with the stable family

The work order said to build `-dh` with Mathlib's `StieltjesFunction`, and `Monotone.stieltjesFunction`
does hand over the right-continuous modification for free — which was the cost the plan
anticipated (`k` is only `AntitoneOn`). But that is not where it breaks. **A `StieltjesFunction`
is `ℝ → ℝ`, so its measure is finite on every bounded interval, and a Lévy measure need not be:**
`h` is unbounded at the origin for the stable family (`k(t) = αt^{-α}/Γ(1-α)`), so `ν(0,1] = ∞`
there. `-dh` is therefore not a Stieltjes measure in Mathlib's sense at all.

`exists_tailMeasure` is therefore stated **by the property that is wanted** — the tail
`ν(r,∞) = h(r)` a.e. — rather than by a construction, so either route can discharge it: a
countable sum of Stieltjes pieces over `[1/(n+1), 1/n]`, or the pushforward of Lebesgue on `(0,∞)`
under the generalised inverse `y ↦ sup{u > 0 : h(u) > y}`, which handles the infinite mass
natively and looks the shorter of the two.

**The transferable point:** a work order that names a *tool* ("use `StieltjesFunction`") is more
brittle than one that names a *property*. The tool was right about the difficulty it flagged and
wrong about the obstruction, and only writing the statement separated the two.

## Next

1. `exists_tailMeasure` — the last substantial piece of chapter 9's `[T]` line.
2. `lintegral_one_sub_exp_eq_tail` — the layer-cake identity, Tonelli on `ν ⊗ volume`.
3. `tendsto_k_atTop_nhds_zero` — `k` is antitone, nonnegative, and `∫₁^∞ k(t)/t dt < ∞`, so its
   limit cannot be positive.

---

# Two of the three sub-lemmas were Mathlib's — 2026-08-11

`lintegral_one_sub_exp_eq_tail` and `tendsto_k_atTop_nhds_zero` are proved and in
`Hemigroup/Subordinator.lean`. **`exists_tailMeasure` is now the only thing open in the whole of
chapter 9's `[T]` line.**

## The layer cake was already there, under a name that does not say "Lévy"

The identity `∫(1−e^{−su})dν = ∫₀^∞ s e^{−sr} ν(r,∞) dr` is Mathlib's
`lintegral_comp_eq_lintegral_meas_lt_mul` — the layer-cake formula / Cavalieri's principle — at
`f = id` and `g(r) = s e^{−sr}`, whose antiderivative on `[0,u]` is `1 − e^{−su}`. Four lines once
found, plus a short `HasDerivAt` for the antiderivative.

**And the σ-finiteness hypothesis the decomposition assumed was not needed.** The statement was
written with `[SFinite ν]` because the plan was to prove it by Tonelli on `ν ⊗ volume`; the layer
cake holds for arbitrary measures, so the hypothesis came off — and with it the `SFinite` clause
`exists_tailMeasure` was being asked to supply. A hypothesis introduced by an anticipated *proof
method* rather than by the statement, removed once the method changed. Worth watching for: it is
the same failure mode as naming a tool instead of a property, one level down.

## `k(∞) = 0` is forced, not assumed

`k` is nonincreasing and nonnegative and `∫₁^∞ k(t)/t dt < ∞` (`integrableOn_k_div`), so a
positive limit would make that integral dominate the harmonic one —
`not_integrableOn_Ioi_inv` closes it. Route B needs this because the tail measure must be finite
on `(r,∞)` for every `r > 0`, which is exactly `k(r) < ∞` together with `k(∞) = 0`. Another
regularity fact that fell out of a statement rather than being planned for.

## Next

`exists_tailMeasure`, alone. Two routes, and the second still looks shorter:

1. a countable sum of Stieltjes pieces over `[1/(n+1), 1/n]`;
2. `ν := (volume.restrict (Ioi 0)).map hinv` with `hinv y = sSup {u > 0 : h u > y}`, which handles
   the infinite mass at the origin natively. The sandwich `h(r+) ≤ ν(r,∞) ≤ h(r)` falls out of two
   inclusions, and `h(r+) = h(r)` off a countable set because a monotone function has countably
   many discontinuities — applied to `u ↦ h(e^u)`, which is antitone on *all* of `ℝ` and so
   dodges the fact that `h` itself is only `AntitoneOn (Ioi 0)` and unbounded at the origin.

---

# Route B is complete — 2026-08-11

`exists_tailMeasure` is proved, and with it the whole of chapter 9's `[T]` line.
`lem:potential-kernel` and `prop:sonine-pair-exists` are `\leanok`; `Hemigroup/PotentialKernel.lean`
and `Hemigroup/Subordinator.lean` hold the development. **`#print axioms` gives A17 and nothing
else** — A1 and A2 absent, which is the whole point: the blueprint's own proof of 9.4 goes through
Bernstein–Widder for general measures, and the article's claim that its representation-first design
keeps A1 off the critical path is now machine-checked in the one place it was most at risk.
32 nodes `\leanok`. `exists_levyTriple_symbol` reduces to **Lean core**.

## The tail measure: the quantile transform, and where the countability came from

`ν := (Leb on (0,∞)) ∘ tailInv⁻¹` with `tailInv h y = sup {u > 0 : h u > y}`. Two inclusions give
the sandwich `h(r+) ≤ ν(r,∞) ≤ h(r)`, and the two ends agree off the countably many
discontinuities of `h`.

The countability is `Monotone.countable_not_continuousAt` — but not applied to `h`, which is only
`AntitoneOn (Ioi 0)` and unbounded at the origin. Applied instead to `t ↦ -h(eᵗ)`, which is
monotone on **all** of `ℝ`. **Composing with `exp` is what turns a half-line hypothesis into a
global one**, and it is worth remembering as a general move: this development is full of
`AntitoneOn (Ioi 0)` hypotheses that Mathlib's monotone-function theory does not accept, and the
multiplicative-to-additive change of variable converts them at no cost.

## The scaling clause was split off

9.4 also asserted `ℓ^{(x)} = x · (ℓ^{(1)} ∘ (t ↦ xt))`. That clause presupposes a *named*
`ℓ^{(x)}`, and the Lean statement is an existence-and-uniqueness one — the object has to be chosen
before a scaling law can be predicated of it, and this development has never needed that choice:
`thm:sonine-conservation` and `prop:sonine-pair-exists` both quantify over an arbitrary `ℓ` meeting
the specification. Appended as `lem:potential-kernel-scaling` (9.16), `[T]`, untagged; it is a
transform comparison plus 9.4's uniqueness clause once someone wants the definition.

## Tally of what the statement-first order found, across Route B

Four findings, all from writing statements before proving them, and no two of the same kind:

| | what | kind |
|---|---|---|
| `Measurable μ` | missing from the work order | a clause carrying the reachability of the statement |
| `F.Nondegenerate` | present in `exists_levyTriple_symbol`, unused | an inert clause |
| `SFinite ν` | demanded by the decomposition, not by the statement | a clause introduced by an anticipated *proof method* |
| `StieltjesFunction` | named by the work order, wrong for the job | a *tool* named where a *property* was meant |

The last two are the ones worth carrying forward. A decomposition should say what each piece must
*achieve*, not how it will be proved or with what: the layer cake removed the `SFinite` hypothesis
the Tonelli plan had introduced, and stating the tail measure by its tail rather than by
`StieltjesFunction` is what left both constructions available when the named one turned out not to
apply.

## Next

Chapter 9 is closed to what its ledger allows. What remains anywhere is `[A]` or blocked upstream:

1. `prop:pair-regularity`(2) — ledger A9, an interface by design.
2. `prop:scale-evolution`, `cor:exact-inversion` — distributional; Mathlib's `Analysis/Distribution/`
   still lacks the embedding of a locally integrable function and convolution with a measure.
   Re-check on each Mathlib bump.
3. `lem:mellin-vertical` — Γ's vertical decay, absent upstream; it is what would retire A12 and
   with it the rest of chapter 11.
4. Chapters 10 and 12 — C₀-semigroup theory and Bessel `K`, both absent upstream.

---

# Gamma's vertical decay, and A12 unblocked — 2026-08-11

`lem:mellin-vertical` is proved. `Hemigroup/MellinVertical.lean`; A17 and nothing else; 33 nodes
`\leanok`. `Skeleton/Chapter11.lean` now holds no declarations at all.

## The obstruction was a claim about the proof, not about the obligation

Two earlier readings put this clause upstream: the bound of `lem:mellin-data` reduces vertical
integrability to the decay of `|Γ(c+iτ)|`, and Mathlib has no such estimate — `Stirling.lean` is
Stirling's formula for `n !` alone. Both halves of that were checked and the first is true. The
second was wrong, and wrong in a way worth naming: **it was reasoning about what the classical
proof of the classical fact needs.**

The classical fact is `|Γ(c+iτ)| ∼ √(2π)|τ|^{c−1/2}e^{−π|τ|/2}`, and that does need Stirling in the
complex plane. The obligation is *integrability*, which needs only quadratic decay:

* `|Γ(σ+iτ)| ≤ Γ(σ)` for `σ > 0` — the imaginary part only rotates Euler's integrand;
* `Γ(z+2) = (z+1)zΓ(z)`, and `|z|, |z+1| ≥ |τ|` because both have imaginary part `τ`, so
  `|Γ(c+iτ)|τ² ≤ Γ(c+2)`.

Adding them: `|Γ(c+iτ)|(1+τ²) ≤ Γ(c) + Γ(c+2)`. About forty lines, no Stirling, and the three
`Gamma` lemmas are general enough to be worth upstreaming.

## Four assessments of one ledger entry

| | compared against | verdict | error |
|---|---|---|---|
| 1 | the **cited theorem** (Widder 9a) | not retirable; needs a new hypothesis | the article never uses Widder's generality |
| 2 | the article's **use** of it | retirable at formalisation cost | right about the article, silent about Lean |
| 3 | the **named lemma** the classical proof needs | blocked upstream on Γ decay | reasoned about the proof, not the obligation |
| 4 | **the statement, by attempting it** | proved | — |

Each reading was a refinement of the last and each was still an argument *about* the proof rather
than an attempt at it. **A survey answers "is this theory present?"; only attempting the proof
answers "is this theorem reachable?"** — and here the two answers differed by two orders of
magnitude of work. That is the strongest form of the statement-first lesson this project has
produced, because the three wrong answers were each carefully argued and recorded.

## Where A12 stands

Not retired, but the reason is now entirely internal. `mellinInv_mellin_eq` recovers a *function*
from its own transform; `def:inversion-operator` needs the integral against `B(−z)g̃(z)` to agree
with the functional-calculus reading, so one must exhibit the `h` whose Mellin transform is that
product, plus `ContinuousAt`. Those are the two pieces the correction of the same day named, and
they are about this article.

## Next

1. `def:inversion-operator` — the operator formulation. It is the gate on the rest of chapter 11
   (11.4's step 1, 11.5, 11.6) and no longer waits on anything upstream.
2. Still blocked upstream, unchanged: chapter 10 (C₀-semigroups), chapter 12 (Bessel `K`),
   `prop:scale-evolution` and `cor:exact-inversion` (distributions).
3. `prop:pair-regularity`(2) is `[A]` by design (ledger A9).

---

# `def:inversion-operator`, and what A12 is left carrying — 2026-08-12

Proved. `Hemigroup/InversionOperator.lean`; A17 and nothing else; 35 nodes `\leanok`.
`Skeleton/Chapter11.lean` holds no declarations again, and chapter 11's `sorry` count is zero.

## Formalising a definition split it in two

The blueprint sets `(Ag)(x)` to a contour integral and glosses it as `x^{-1}(B(θ)g)(x)`, the gloss
being what A12 licenses. Writing it in Lean separates the two completely, and the separation is
the finding:

* **The operator needs no hypothesis at all.** `mellinInv` is an ordinary integral, so `A g` is
  total in `g`. What the blueprint writes as a restriction on the *domain* of `A` belongs on the
  theorems that compute it, not on the definition. The parametrisation `z = c + iy` turns the
  blueprint's `dz/2πi` into Mathlib's `dy/2π` exactly, so the contour integral *is* `mellinInv`.
* **The gloss needs a referent.** `B(θ)g` is a functional calculus for an operator with poles, so
  the second display is not a rewriting of the first — it asserts that a function exists. That is
  the same gap the fourth reading of A12 saw from the Mathlib side: `mellinInv_mellin_eq` recovers
  a function from its *own* transform and says nothing about the integral of a product.

So the Lean statement takes the referent as a hypothesis — `RealisesSymbolAction`, an `h` with
`h̃ = B(-z)g̃(z)` on the line and the two convergence clauses — and proves everything downstream:
`A g = x^{-1}h` at points of continuity, `Ãg(z) = h̃(z-1)` at *every* `z`. The proved content is the
new node `lem:inversion-operator-action` (11.16), `[T]`; `def:inversion-operator` keeps its number,
its statement and A12, now narrowed to the single step that produces `h`. Same discipline as the
11.2 split, and the Lemma 7.1 precedent behind both.

## The unforeseen finding is about the statement, not the proof

**The realising identity can only be asked for almost everywhere on the line.** `B` is a quotient
with poles at the zeros of `H̃`; where `H̃` vanishes the product `B(-z)g̃(z)` vanishes with it — in
Lean because `x/0 = 0`, in the prose because a meromorphic function has no value at a pole — while
`h̃(z)` need not. A pointwise reading of the hypothesis is therefore satisfied by *no* `g` at all.
The zeros are isolated, so they meet the line in a null set and the inversion integral does not see
them; `integral_congr_ae` discards them, and it is available precisely because `mellinInv`
integrates over the line rather than evaluating on it.

This is the second time in chapter 11 that "equality on the strip" has had to say which equality it
means — `lem:symbol-rigidity` was the first — and both times it was writing the statement, not
reading it, that raised the question. Worth noting that the two answers differ: rigidity wanted a
*punctured neighbourhood* (the meromorphic reading), this wants *almost everywhere* (the measure
reading). The prose says "on the strip" for both.

## The consequence for A12, which is now a checkable question

A12 carries one step: that absolute integrability of `B(-z)g̃(z)` on the line produces `h`.
Everything ever assigned to it beyond that is proved.

And it is now a question about **this article**. Every use of `A` applies it to a profile
`H(s·)`, where the referent is explicit:

```
g(x) = H(sx),   h(x) = s x H(sx),   h̃(z) = s^{-z} H̃(z+1)
```

— the last being `lem:inversion-symbol`'s recursion `B(-z) = H̃(z+1)/H̃(z)` with the denominator
cleared, so that `h̃(z) = B(-z) g̃(z)` holds wherever `H̃(z) ≠ 0`, i.e. off a null set of the line.
Note that `Ag(x) = x^{-1}h(x) = s H(sx)`, which *is* the eigenfunction relation of Theorem 4′: the
instance and the theorem are the same computation. If every use supplies its own `h`, A12 retires
with no citation spent.

The one thing that instance still needs, and it is not free: **the zeros of `H̃` on the line form a
null set.** Isolated zeros give a set discrete in the strip, hence countable, hence null on the
line — but "discrete implies countable" has to be found or proved in Mathlib, and that is the piece
to scout before claiming the instance is routine. Recording it here rather than discovering it
mid-proof is the whole point of this file.

## The profile instance, same day — A12's use is empty

Done in the same round, and it changes the answer above rather than deferring it.
`lem:profile-eigenfunction` (11.17) is proved: for `g = H(s·)` the realising function is
`h(x) = s x H(sx)`, exhibited, and `realisesSymbolAction_profile` discharges all three fields.
A17 and nothing else.

Three things came out of it worth keeping.

**The instance and the eigenfunction relation are the same statement.** `A g = x⁻¹h` with
`h(x) = s x H(sx)` is `s H(sx)` — the weight `x⁻¹` in the definition of `A` is exactly what
cancels the weight `x` that shifts the transform. So proving the instance *is* proving
`thm:signaling-form`(1); there was no second step.

**Hence A12 is never invoked.** The one step it is still assigned — that absolute integrability
produces `B(θ)g` — is not used, because the function is written down instead. And the profile
dilate is the only shape in which `A` is ever applied here: clause (2)'s Laplace form is clause (1)
applied to `û(s,·) = f̂(s)H(s·)`. The `[A]` tag stays on 11.3, because it records the *paper's*
stance and the paper is entitled to cite Widder for its inversion integral — the A5/A6 situation of
chapter 2 exactly. What is new is that the record underneath it is complete.

**The null-set step was correctly flagged and correctly priced.** Isolated zeros give a set
discrete in the strip, `ℂ` is hereditarily Lindelöf, so it is countable and its preimage on a line
is null. Mathlib has every piece (`isDiscrete_of_codiscreteWithin`,
`IsLindelof.countable_of_isDiscrete`) and the proof is fifteen lines. What the flag bought was not
avoiding a surprise but knowing where to look; scouting it took longer than proving it.

And it caught something in the prose. The draft's proof of clause (1) says of `B(-z)g̃(z)` that
"no pole of `B` intervenes, the product containing no division". True of the *simplified* product
`s^{-z}H̃(z+1)`, false of `B` read as a function — where the division is present and cancelling it
is what needs the zeros to be null. **The prose does algebra on symbols; the formalisation does it
on functions, and that is where the gap between them lives.** It is the same shape as the two
"which equality on the strip" findings, and the third instance of it in this chapter.

## `lem:symbol-uniqueness`, same round — it was outside the quantifier

Both halves proved; A17 alone. The node had been recorded as waiting on A12 because step 1 was
read as needing `def:inversion-operator`'s transform identity, hence the *production* of `B(θ)g`.
That was a misreading of the node's own hypothesis: it quantifies over operators **of the form**
`x⁻¹B(θ)`, and an operator of that form is one whose `B(θ)g` is *given*. The step A12 carries sits
outside the quantifier.

Which is the same lesson as chapter 11's other three, arriving from a new direction: the previous
ones came from writing statements down, this one from reading a hypothesis that had been written
down already. "Blocked on X" deserves the same scepticism whether X is upstream or internal.

Two things the proof turned out not to need, both worth recording because both were anticipated:

* **No Mellin injectivity.** A12's own entry had flagged that this node "may want Widder Thm 6a".
  It does not: two operators agreeing on `H(s·)` share a realising function there, so their
  transforms agree at every point and the symbols come off by cancelling `s^{-z}H̃(z)`. **One
  anticipated citation retired without being spent.**
* **One dilation suffices.** The statement quantifies over all `s > 0`; the proof uses one.

**And it corrected a choice made one commit earlier.** `RealisesAction.mellin_eq` was first an
`∀ᵐ` on the line — all `inversionOperator_eq` needs. Too weak here: a uniqueness theorem concludes
an equality of symbols at *named* points, and an a.e. hypothesis concludes nothing at any of them.
The right condition is the identity wherever `H̃` does not vanish, which is what the profile
instance proves and which makes `SameSymbolAction` hold on the whole strip (at a zero both sides
vanish). Weakest the consumer can use, strongest the producer can supply, and they coincide — but
only writing the consumer showed it. The a.e. version survives as a derived lemma.

---

# The last of chapter 11, scouted — and a modelling fork that is not mine to take

`thm:signaling-form`(2)'s Mellin form runs through `lem:memory-fractional-integrals` (11.5):
`ũ(t,·)(z) = H̃(z)·(Iᶻf)(t)`. Scouting it turned up two things, one cheap and one a decision.

## Cheap: Mathlib has no fractional integral, of any order

There is no Riemann–Liouville anywhere in the library — `Analysis/` carries Mellin, Fourier,
convolution and distributions and nothing fractional. So `Iᶻ` is *defined* in the development
(`Skeleton.riemannLiouville`). That is not an interface and does not touch the ledger: the draft
cites Samko–Kilbas–Marichev for the notation and theory of `Iᶻ`, and nothing in chapter 11 uses
more of that theory than the definition. Worth noting for the record that this makes the second
SKM citation in §11 load-bearing in a way the first (retracted in favour of Widder, ledger A12)
was not — it is where the object comes from, not where a theorem does.

## The decision: the field is `L¹`-valued and Lemma 11.5 is pointwise in `t`

`Φ_{x,y}` in `Hemigroup/Family.lean` maps `X →L[ℝ] X` with `X` an `L¹` space. **An `L¹` class has
no value at a point**, and 11.5 asserts an identity at each `t > 0`. So `u(t,x) = (Φ_{0,x}f)(t)`
is not, as it stands, a statement the development can make. Two readings, and they cost
differently:

**(a) Weaken to almost every `t`.** `u(t,x)` is then the convolution `(μ_{0,x} * f)(t)`, defined
a.e. for `f ∈ L¹`, and 11.5 becomes an a.e. identity. Cheap, faithful to how the rest of the
development treats the field, and nothing in Theorem 4′(2)'s Mellin form obviously needs more.
The cost lands on `∂_t u`: the derivative clause of 11.5 needs `f ∈ 𝒟` and an a.e. reading of a
derivative of an `L¹`-valued object, which is exactly the kind of thing that is fine until it is
not.

**(b) Build a pointwise model of the field.** A chosen representative — for causal `f` and `x > 0`
the convolution with a probability measure has a canonical continuous-in-`t` version when `f`
does — makes every statement of chapters 10–12 pointwise and removes the friction permanently.
It is a new layer under three chapters, and it is the layer chapter 10 would want anyway if
Mathlib's C₀-semigroup theory ever unblocks it.

**Recommendation: (a) now, and let chapter 10 force (b) if it ever becomes schedulable.** The
reason is that (b)'s value is almost entirely in chapter 10, which is blocked for independent
reasons; paying for it now would be building a layer against a consumer that may never arrive.

**What is decision-free, and is therefore what got stated.** The *analytic core* of 11.5 —
`Skeleton.mellin_delayed_average` — takes the integrand as `E[f(t - xT₁)]` for a genuine function
`f` and proves the substitution `y = x·T₁`. Both readings need it, unchanged. What the readings
differ about is only the step that identifies that integrand with `Φ_{0,x}f`.

## Decided (a), and the core is proved — 2026-08-12

**(a) taken.** The identification of `E[f(t - xT₁)]` with `Φ_{0,x}f` will be an a.e.-in-`t`
statement; no pointwise model of the field is built. (b) stays available and stays unbuilt, since
its value is almost entirely in chapter 10, which is blocked for independent reasons.

**The analytic core is proved**, as `Hemigroup.mellin_delayed_average`
(`Hemigroup/MemoryFractional.lean`), A17 alone, and appended to the blueprint as
`lem:delayed-average-mellin` (11.18). `lem:memory-fractional-integrals` keeps its number and its
full statement, on the pattern of the other three chapter-11 splits.

Three things it settled:

* **`Iᶻ` is defined, not cited.** Mathlib has no fractional integral of any order, so
  `Hemigroup.riemannLiouville` gives it a definition. This adds no interface — SKM is cited for the
  notation and theory of `Iᶻ`, of which the chapter uses only the definition.
* **The exchange is licensed by the two ends of the strip, one apiece.** Inside, the dilate of the
  past integrand is integrable because `Re z > 1`; outside, the dilation leaves `τ^{-z}`, whose
  expectation is finite because `Re z < z_*`. The same shape as `lem:mellin-data`'s hinge with the
  lower end moved from `0` to `1` — **and the move is what makes (H) ask for `z_* > 1`**. Below `1`
  the lemma has no strip to live in. That is also where `prop:extreme-rays`'s observation that
  every extreme ray has `z_* = 1` bites, and it is worth saying in the text that the two facts are
  the same fact.
* **`f` has to be measurable, not merely a.e.-measurable.** The integrand composes `f` with
  `(x,τ) ↦ t - xτ`, and a `volume`-null set need not pull back to a null set for the product
  measure, since `lawT₁` may have atoms. Choosing a measurable representative is free for an `L¹`
  class, so the article pays nothing; but it is the kind of hypothesis that is invisible on paper
  and mandatory in Lean, and worth recording as such.

## The identification, same round — and (a) does not avoid choosing a representative

Done: `coeFn_Phi_zero` gives `(Φ_{0,x}f)(t) = E[f(t - xT₁)]` a.e. in `t` for each `x > 0`, and
`mellin_delayedField` is the first clause of 11.5 outright. One new lemma was needed and it is
worth having on its own account: `kernel_zero_eq_map_lawT₁`, **the canonical gauge at the level of
measures** — `μ_{0,x}` is the law of `x·T₁`. The article reads this off the notation; here the
kernels come from their transforms, so it is Laplace injectivity (`kernel_unique`) applied to two
causal measures with transform `e^{-F(xs)}`.

**The finding, and it qualifies the decision rather than confirming it.** "For each `x`, for a.e.
`t`" does *not* give "for a.e. `t`, for every `x`" — the null set depends on `x`. The Mellin
transform in the second display is an integral over `x` at a *fixed* `t`, so it cannot be taken of
`(Φ_{0,x}f)(t)` as it stands, **whichever way the identification is read**. A representative has to
be named either way.

So (a) did not avoid the pointwise field; it localised it. What is defined is one function,
`delayedField f t x = E[f(t - xT₁)]`, with `coeFn_Phi_zero` as its bridge — where (b) would have
made the same choice once, globally, under all of chapters 10–12. That is a better description of
the trade than the one recorded when the fork was written: the question was never *whether* to
name a representative but *how widely*. Worth remembering if chapter 10 ever becomes schedulable,
because it means (b)'s cost is not "a new layer" so much as "the same choice, promoted".

## The Mellin form, same round — and an off-by-one in a stated strip

`lem:signaling-mellin-form` (11.19) is proved: `B(1-z)ũ(t,·)(z-1) = H̃(z)(I^{z-1}f)(t)`, which is
Theorem 4′(2)'s displayed computation entire. A17 alone.

**Chaining the two lemmas found a gap in the draft, and it is a range.** 11.5 states
`1 < Re z < z_*`. 11.6(2) states the same range and applies 11.5 **at `z-1`** — which that range
does not cover. The chain does not close as written.

It closes on the hypotheses actually present: 11.6(2) assumes `f ∈ 𝒟`, and `f ∈ 𝒟` is *bounded*
(`f(0) = 0` with `f' ∈ X₀` gives `‖f‖_∞ ≤ ‖f'‖₁`). Boundedness moves 11.5's lower endpoint from `1`
to `0`, because the weight `y^{c-1}` is then integrable at the origin on its own rather than having
to be absorbed by `t^{c-1}`. So **nothing about the result changes; what changes is what the lemma
says.** Draft and blueprint now say it.

Worth naming the shape, because it is not the same as the chapter's other findings. Those were
about *which statement* a piece of prose was making (which equality, which set). This one is a
plain range error that survived because the second clause's hypothesis was quietly doing work the
first clause's range did not advertise. It is exactly the kind of thing that is invisible while
the lemmas are read one at a time and immediate on composing them — and composition is what a
formalisation does whether or not one is looking for it.

The refactor it forced is worth keeping: the strip hypothesis is now *supplied* rather than
assumed. `integrableOn_pastIntegrand` (from `Re z > 1` and `f ∈ L¹`) and
`integrableOn_pastIntegrand_of_bounded` (from `Re z > 0` and `f` bounded) are two producers of one
hypothesis that the four downstream lemmas take as input, so the strip appears once, at the place
that decides it.

## The derivative clause, stated — and `lem:delay-core` is not what it needs either

The previous section's "Next" said chapter 11 waits on `lem:delay-core` (10.1). Writing the
derivative clause down shows that is wrong, and wrong in a way the chapter has now produced three
times. The draft reaches the clause through `f ∈ 𝒟`, hence 10.1 — density of the core, invariance
under the delay semigroup and under `Φ`, the `L¹` difference quotient — and **uses none of it**.
What it uses is two facts, now stated in `Skeleton/Chapter11.lean`:

* `hasDerivAt_delayedField` — differentiation under the integral sign for `∂_t E[f(t - xT₁)]`.
  Needs `f` to be an integral of an `L¹` function; says nothing about `Φ` or the core.
* `riemannLiouville_integral` — the identity `Iᶻf' = I^{z-1}f`. Mentions neither the field nor the
  core. The draft derives it from the semigroup property `Iᶻ I¹ = I^{z+1}`; it is cheaper without
  that property, by exchanging the order of integration over the triangle `0 < ρ ≤ r ≤ t`, which
  leaves `∫_ρ^t (t-r)^{z-2}dr = (t-ρ)^{z-1}/(z-1)` — and `Re z > 1` is exactly what makes that
  inner integral converge, the same endpoint as everywhere else in this chapter.

`𝒟` enters only as a convenient source of those hypotheses (and, per the previous section, of
boundedness). **What a proof cites is an upper bound on what a statement needs** — that is the
pattern, and it has now cost three separate "blocked on X" entries in this chapter: A12 twice
(once upstream, once on the wrong side of a quantifier) and 10.1 here. The reliable test is the
same each time: write the statement and see what the *obligation* asks for, not what the argument
happens to invoke.

## `Iᶻf' = I^{z-1}f`, proved — 2026-08-12

`lem:fractional-integral-derivative` (11.20). Fubini over the triangle `0 < ρ ≤ r ≤ t`, inner
integral `∫_ρ^t (t-r)^{z-2}dr = (t-ρ)^{z-1}/(z-1)`, then `Γ(z) = (z-1)Γ(z-1)`.

Two things worth keeping.

**Avoiding the semigroup property was the whole economy.** The draft derives this as
`Iᶻf' = I^{z-1}I¹f' = I^{z-1}f`, i.e. from `I^{z-1}I¹ = Iᶻ` — a Beta-integral identity that Mathlib
does not have and that would have to be proved in its own right, on top of `Iᶻ` itself being a
local definition. Substituting `f(r) = ∫₀^r g` and exchanging the order of integration needs only
`integral_cpow`, which Mathlib does have, with the hypothesis `-1 < Re r` matching `Re z > 1` on the
nose. Same lesson as A12's fourth reading: the classical *derivation* asks for more than the
*statement* does.

**`Re z > 1` has now been arrived at three independent times** — the delayed average's inner
integrability, the application of 11.5 at `z-1`, and this inner integral's convergence. Three
different obligations, one endpoint, and it is the endpoint (H) asks for. That is not a
coincidence worth leaving unremarked in the text: it is why `z_* > 1` is the right hypothesis and
not an artefact.

**And it reduces to Lean core alone** — not even A17. It is the first result in the development of
which that is true and which is not a general-purpose lemma about `Γ`, because it is a statement
about the Riemann–Liouville family that mentions no hemigroup object.

## Chapter 11 is complete, Theorem 4′ included — 2026-08-12

All six conjuncts of `thm:signaling-form` are proved and assembled into one declaration,
`signaling_form`. 42 nodes `\leanok`; the repo's only `sorry` is chapter 9's `hasCMDensity_iff`,
ledger A9 by design; A17/A18 are still the whole trust boundary.

**This round began with a correction.** The chapter's *lemmas* were all `\leanok` while
`thm:signaling-form` was not, and reporting the chapter as finished on that basis was wrong: clause
(2) asserts four things and only the Mellin form had been proved. **A theorem node exists precisely
because it asserts more than its lemmas do** — which is what the dependency graph is for, and which
a summary that counts lemmas cannot see. The three missing pieces then took one round:

* causality in `t` — pointwise and immediate, `f(t-xτ) = 0` for `t < 0`;
* boundary attainment `Φ_{0,x}f → f` in `X₀` — (A7) with (A6), i.e. structure fields;
* the Laplace form — `û(s,x) = f̂(s)H(sx)` by Fubini and a translation, then homogeneity of `A`
  applied to `lem:profile-eigenfunction`.

**Assembling it found one more thing**, and it is the same shape as the round's other findings:
`f ∈ 𝒟` had been carried along as "the primitive of a causal `g ∈ L¹`", and that is *not* all of
it. A primitive of an `L¹` function tends to `∫₀^∞ g`, so it lies in `L¹` only when that limit
vanishes; `𝒟` asks for `f ∈ X₀` *and* `f' ∈ X₀` and thereby imposes it. The bundled statement needs
`Integrable f` as a separate hypothesis, and only assembling the clauses made the omission visible
— each clause individually was fine without it.

Running tally of what `f ∈ 𝒟` is actually for, now that the chapter is closed: boundedness (widens
11.5's strip), being a primitive (gives the derivative clause its meaning), and integrability (the
Laplace form). Density, `T_r`-invariance and `Φ`-invariance — the substance of `lem:delay-core`,
which the draft's proof cites — are used nowhere.
## The three "formalisation debts" are deliberate — a correction, 2026-08-12

The previous section proposed discharging them as "the highest-leverage work left in the repo".
That was wrong, and wrong in the way this chapter has now produced four times: **a tool's output
was read as a work queue without checking what the nodes say about themselves.** `linkage check`
even labels them *"a formalisation debt (permitted, ADR-0010 rule 2), not a defect"*.

Each of the three is documented, in its own status annotation, as a decision already taken:

* **`lem:selfdecomposable-derivative`** — *"Taken as `A18`, not proved — a review decision recorded
  2026-08-10."* Both directions run through `prop:bernstein-toolbox`: A4 (closure of `BF` under
  pointwise limits) and A3 (uniqueness of the Lévy–Khintchine triple). Neither is a statement about
  the hemigroup family, and **neither can even be stated here**, since both quantify over `BF` and
  the development has no `CM`. Formalising this node means formalising A3 and A4, which is exactly
  what the trust boundary declines to do.
* **`lem:selfdecomposable-exponents`** — a collation whose expensive half is the node above, hence
  A18. *"This node is therefore not marked as proved in Lean."*
* **`thm:main-characterization`** — a collation. All three halves *are* machine-checked; the node
  carries no tag *"because it is a collation and an equivalence is established by its parts rather
  than by a statement of its own"*, and the separation is what keeps `(⇐)` on A17 and `(⇒)` on A18
  without either borrowing the other's.

The third is the one where a choice exists, and it is the author's rather than mine: it *could* be
given a bundling declaration, exactly as `thm:signaling-form` just was, since its three halves are
proved. That would turn the article's other headline node green at the cost of a statement whose
`(⇐)` half is a definition rather than a proposition — which is presumably why the note argues the
other way. **Not taken unilaterally.**

## What is actually open

23 `[T]` nodes lack `\leanok`. Sorted by why:

| why | nodes |
|---|---|
| deliberate (above) | `lem:selfdecomposable-derivative`, `lem:selfdecomposable-exponents`, `thm:main-characterization` |
| no Lean counterpart by design (`CM`, `BF`, chapters 10/12 vocabulary) | `def:completely-monotone`, `def:bernstein-function`, `def:locality-pmp`, `def:phillips-generator` |
| blocked upstream (C₀-semigroups, Bessel `K`, distributions) | `thm:scale-cauchy`, `lem:generator-properties`, `prop:scale-evolution`, `cor:exact-inversion`, `lem:transform-ode`, `lem:log-convexity`, `lem:local-polynomial-symbol` |
| available, nothing depends on them | `lem:delay-core`, `cor:semigroup-case`, `prop:moments`, `prop:stable-moments`, `prop:gamma-kernels`, `prop:extreme-rays`, `prop:volterra`, `lem:potential-kernel-scaling` |

**Superseded in part, 2026-08-13.** Three of the rows above have moved, and the row that moved
furthest is worth naming because the reason it was written was wrong. `lem:log-convexity`,
`def:locality-pmp` and `lem:local-polynomial-symbol` are now `\leanok`. Chapter 12 was filed as
*blocked upstream (Bessel `K`)* and as *no Lean counterpart by design*, and neither applied to
these nodes: Bessel `K` is needed by the chapter's **ladder**, not by its classification step, and
`def:locality-pmp` needs no `CM` vocabulary at all — it is a statement about a differential
expression and the inversion operator. What the classification step did need was two computations
Mathlib does not carry, the Mellin symbol of the Euler operator (test functions, by parts) and the
same identity on the profiles (no parts, the derivative being already an integral); both are now
proved. The lesson is the one this document already makes about `lem:mellin-vertical`: *"blocked on
Mathlib" is a claim about a specific missing lemma and has to name it*, and a chapter-level reason
never survives contact with a node.

`def:standing-hypothesis` was a **missing tag** rather than missing work — `StandingHypothesis` has
existed in `MellinData.lean` since chapter 11 started and every theorem in the chapter takes it as
a hypothesis. Now tagged. It is worth noting that the inventory above is the first time this repo
has had one; the per-node annotations are excellent and the aggregate view was missing, which is
precisely how "the three advisories are the work left" survived as a plan.

## Next

Chapter 11 needs nothing further. What remains in the article:

1. **The three formalisation debts** that `linkage check` reports as advisories:
   `lem:selfdecomposable-derivative`, `lem:selfdecomposable-exponents` and
   `thm:main-characterization` are proved on paper only and are now reached by most of the
   `\leanok` nodes. This is the highest-leverage work left in the repo.
2. `lem:delay-core` (10.1) — not blocked on Mathlib, and no longer needed by chapter 11 either, so
   optional rather than queued. Formalising it would discharge a `\uses` edge and nothing more.
3. Blocked upstream, unchanged: chapter 10's C₀-semigroup content, chapter 12 (Bessel `K`),
   `prop:scale-evolution` and `cor:exact-inversion` (distributions).
4. `prop:pair-regularity`(2) is `[A]` by design (ledger A9) — the repo's one `sorry`.

---

# Chapter 10's setting, built; `lem:delay-core` stated — 2026-08-14

`Hemigroup/DelayCore.lean` (definitions and their elementary theory, all Lean core) and
`Skeleton/Chapter10.lean` (the five clauses, `sorry`; the collation above them `sorry`-free).
`lem:delay-core` is `\lean{Skeleton.delay_core}\notready`. 81 nodes, 52 `\leanok` — unchanged,
which is the point of the middle state.

## The modelling decision, and the one argument that settled it

Chapter 10 is stated about three objects the development had never built: `X₀`, the delay
semigroup, and the core `𝒟`. Only the first looks like a free choice, and it is not.

**`X₀` is a predicate on `X = L¹(ℝ)`, not a subtype.** `DESIGN-formalization-strategy.md`'s M0
already took this decision one level down and gave the reason — *"measures on ℝ supported in
`[0,∞)` rather than on a bespoke half-line type, so `Measure.conv` and the convolution API apply
directly"* — and the argument transfers verbatim: `Φ_{x,y}`, `transL1`, `dilL1` and `mconvL1` are
all operators on `X`, and a subtype needs every one re-mounted. What settles it rather than
merely favouring it is that **(A3) is already the theorem "every `Φ_{x,y}` restricts to `X₀`"**,
stated as `VanishesBefore t₀ f → VanishesBefore t₀ (Φ x y f)`. A subtype would be a second way of
saying what the axiom says.

**`𝒟` is a predicate on genuine functions, and `coreL1` is its image in `X`.** This is the
decision with consequences, and chapter 11 forces the direction. Its hypotheses are *pointwise*
(`Measurable f`, `∀ r < 0, f r = 0`, `∀ r, f r = ∫_{(0,r]} g`), because `delayedField` exists
precisely to name a representative an `L¹` class does not have. A purely `L¹`-level `𝒟` could not
*derive* those; it could only assert them again — which would be exactly the drift the task was to
avoid. So the function level is primary.

That is the (a)/(b) fork answered one notch further along. The record from 2026-08-12 was that
*"the question was never whether to name a representative but how widely"*. `HasCoreDeriv` is that
naming at the width chapter 10 needs, and it costs nothing extra: (b)'s "new layer under three
chapters" is, again, the same choice promoted.

## The check is an equivalence, and that is not decoration

`memCore_iff_signaling_hypotheses` states `HasCoreDeriv f g` ↔ the six hypotheses
`thm:signaling-form` takes about its signal. Both halves earn their place. Left to right is the
obligation — the model must *supply* what chapter 11 assumed while `𝒟` had no definition. Right to
left says the model adds nothing: `𝒟` is not a strengthening smuggled in under a chapter-10 name,
which is the failure a one-way check would not see. Only one of the six is not a field of the
structure, `Measurable f`, and it comes from continuity of the primitive.

## `𝒟` is defined by the primitive, and Mathlib's absolute continuity is the derived fact

The blueprint writes `𝒟 = {f ∈ X₀ : f absolutely continuous, f' ∈ X₀, f(0) = 0}`, and Mathlib
*now has* `AbsolutelyContinuousOnInterval` (`MeasureTheory/Function/AbsolutelyContinuous.lean`,
new since the 2026-08-11 survey). Defining `𝒟` that way would have been wrong, for the reason the
`StieltjesFunction` episode already recorded: **it names a tool where a property is meant.** Every
consumer uses the primitive form `f = ∫₀^· g`; getting there from absolute continuity is the
Lebesgue fundamental theorem, which Mathlib does **not** have, while the direction it does have
(`IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`) is the one nothing uses.

So `𝒟` is defined by the primitive and `HasCoreDeriv.absolutelyContinuousOnInterval` recovers the
blueprint's wording as a theorem. Three clauses then come for free — `causal`, `apply_zero`
(`f(0) = 0` is the empty domain of integration), `abs_le` — and the fourth, `f ∈ X₀`, stays a
separate field, as `SignalingForm.lean` found by assembling clauses that were each fine without it.

**Worth naming, because it inverts an expectation.** A new Mathlib theory arriving is normally
what unblocks a node. Here the new theory arrived and the right move was still not to use it, and
the reason was legible only after asking what the *consumers* of the definition need. Same test as
"read the Assignment clause and the consuming node first, the citation last" — one level down,
about a definition rather than a ledger entry.

## What the five clauses are expected to cost

1. `dense_coreL1` — the blueprint says "standard", and the standard route does not work: step
   functions are dense in `X₀` and are not in `𝒟` at all. The mollification
   `f_h := h⁻¹ 1_{[0,h]} ∗ f` is in `𝒟` outright, with derivative `h⁻¹(f - T_h f)`, and converges
   by continuity of translation in `L¹` — **the same input clause 4 needs**, so the two are one
   piece of work seen from two sides and should be attacked together.
2. `hasCoreDerivL1_transL1` — stated as `(T_r f)' = T_r f'` rather than `T_r f ∈ 𝒟`, because that
   is what the blueprint proves and what `def:phillips-generator` will consume.
3. `hasCoreDerivL1_mconvL1` — invariance under `Φ` at the level `lem:convolution-representation`
   supplies it, i.e. for a causal probability measure. Reading it back onto a `CascadeCore` is the
   representation theorem, not this lemma.
4. `tendsto_differenceQuotient` — continuity of translation in `L¹`; the blueprint's `[0,h)`
   boundary term is **the only place `f(0) = 0` is used**.
5. `norm_transL1_sub_le` — the `2‖f‖₁` half is the triangle inequality and the isometry; the
   `r‖f'‖₁` half is the integrated form of clause 4.

## Next

1. Clauses 1 and 4 together, through continuity of translation in `L¹`; then 5, which follows 4.
2. Clauses 2 and 3 are independent of those and cheaper.
3. Unchanged and still not schedulable: the rest of chapter 10 (C₀-semigroups), chapter 12's
   ladder (Bessel `K`), `prop:scale-evolution` and `cor:exact-inversion` (distributions).

## Two clauses proved, and both analytic inputs were already in the library — same day

`hasCoreDerivL1_transL1` and `hasCoreDerivL1_mconvL1` are proved and have moved into
`Hemigroup/DelayCore.lean`. Three clauses left, all `sorry` in `Skeleton/Chapter10.lean`.

**The round's finding is a saving, and it runs opposite to this file's usual one.** The plan above
priced clauses 1 and 4 on one input, continuity of translation in `L¹`, and expected to build it:
Mathlib has no such lemma, and the classical `C_c`-approximation proof is not small. Both halves of
that were checked and both are beside the point.

* Mathlib *does* have it, as `Lp.compMeasurePreserving_continuous` — joint continuity of
  `(g, φ) ↦ g ∘ φ` over measure-preserving `φ` varying in `C(ℝ,ℝ)`. Not findable by name: no
  occurrence of "translation", no `eLpNorm` along a neighbourhood filter.
* And **this development already proved it**, as `continuous_transL1` in
  `Hemigroup/Representation.lean`, in 2026, for chapter 4's Wendel-style representation argument —
  which needs `r ↦ τ_r g` strongly measurable and buys that with continuity.
* The same file also already carries the *causal* mollifier, `approxId ε = ε⁻¹·1_{(0,ε)}`, together
  with `ρ_ε * f → f` in `L¹` (`tendsto_bconv_approxId`). Chapter 4 needed it carried by `[0,ε]`
  for an unrelated reason — its approximants must be causal probability densities for Prokhorov —
  and causality is exactly what makes `ρ_ε * f` land in `𝒟` rather than merely near it. So the
  density clause's one real input is not new work either.

The usual finding in this file is that a node's *stated* prerequisite exceeds what the obligation
needs. This is the mirror image: the obligation's genuine prerequisites were both already proved,
six chapters earlier, inside an argument with no visible relation to this one. The move that
located them is the same one — write the statement, ask what it consumes — but what it turned up
was a **library** fact rather than a Mathlib one. **A survey of Mathlib would have missed both**,
and the plan's cost estimate for clauses 1 and 4 was wrong by most of their size.

Worth generalising: this repo now has fifty-odd files, and "does the development already have
this?" has become a question worth asking with the same seriousness as "does Mathlib?".

**One smaller thing, recorded because it is a direction to move in.**
`mconv_eq_setIntegral_mconv` — `μ ∗ f` is the primitive of `μ ∗ g` whenever `f` is the primitive
of `g` — is the analytic content of the `Φ`-invariance clause, and it is
`delayedField_eq_setIntegral` with the law of `xT₁` replaced by an arbitrary causal probability
measure. The chapter-11 lemma is the special case, proved first because chapter 11 was formalised
first. Nothing is broken by the duplication and it is not worth a refactor today; but it is an
instance of a general fact having been proved in the narrow form its first consumer needed, which
is the shape `Hemigroup/Subordinator.lean` was created to avoid.

## The two quantitative clauses, proved — density is all that is left

`tendsto_differenceQuotient` and `norm_transL1_sub_le`, in `Hemigroup/DelayCore.lean`. Lean core.
`Skeleton/Chapter10.lean` holds one `sorry`, clause 1.

Two departures from the blueprint's route, neither changing anything but both worth recording,
because in each case the blueprint names a construction the obligation does not need.

**The estimate needs no `X`-valued Bochner integral.** The blueprint gets `‖T_rf - f‖₁ ≤ r‖f'‖₁`
from `T_rf - f = -∫₀^r T_ρ f' dρ` as a Bochner integral in `X₀`, plus `‖T_ρ f'‖₁ = ‖f'‖₁`. Working
in `ℝ≥0∞` instead — bound the pointwise `‖f(t-r) - f(t)‖` by `∫_{(0,r]}‖f'(t-u)‖du` and exchange —
gives the same constant with no integrability side condition and no vector-valued integral at all.
The same move as chapter 2's Tonelli identity, and the same reason.

**The limit needs no separate treatment of `[0,h)`.** The blueprint splits the difference quotient
into an estimate on `[h,∞)` handled by continuity of translation and a boundary term on `[0,h)`
handled by `f(0) = 0`. In the primitive model there is no boundary term: the identity
`h⁻¹(T_hf - f) + f' = -h⁻¹∫₀^h (T_uf' - f')du` is exact on all of `ℝ`, so **the quotient is an
average of translation defects and cannot exceed their supremum**, and `f(0) = 0` is spent once,
inside `HasCoreDeriv`, making the identity hold at all rather than repairing it at an endpoint.
That is `norm_differenceQuotient_le`, and stating it separately from the limit is what made the
`ε` in the limit a two-line choice.

Both are instances of the pattern this file keeps recording from the other side: *the classical
derivation asks for more than the statement does*. Here what it asked for was a construction —
a Bochner integral, an interval split — rather than a citation, which is a form the pattern had
not taken before.

## Next

`dense_coreL1`, alone. `ρ_ε * f ∈ 𝒟` with derivative `ε⁻¹(f - T_ε f)`, plus
`tendsto_bconv_approxId`; both halves are chapter 4's, and what has to be written is the
identification of `∫_{(0,t]} ε⁻¹(f - T_ε f)` with `ρ_ε * f`.

## `lem:delay-core` is proved — 2026-08-14

All five clauses. `Hemigroup/DelayCore.lean`; the node is `\lean{Hemigroup.delay_core}\leanok`;
**Lean core throughout**, so the whole of chapter 10's Lemma 10.1 is interface-free. 53 nodes
`\leanok`. `Skeleton/Chapter10.lean` holds no declarations, one round after it was created.

### Density: the standard route is the wrong route, and chapter 4 had the right one

The blueprint says "standard", and the sentence hides which standard argument. Step functions are
dense in `X₀` and are in `𝒟` **nowhere**; Mathlib's `MemLp.exists_hasCompactSupport_eLpNorm_sub_le`
gives compactly supported approximants that are not causal. What works is mollification, and it
has to be by a *causal* mollifier for `ρ_ε * f` to land in `𝒟` rather than merely near it.

`approxId ε = ε⁻¹·1_{(0,ε)}` is exactly that, and it was built in chapter 4, where causality was
needed for a different reason: the approximants `Φ ρ_ε` had to be causal probability densities for
the Prokhorov argument. So the density clause is `tendsto_bconv_approxId` plus one computation,
that `ρ_ε * f` is the primitive of `ε⁻¹(f - T_ε f)` — Chasles twice, once on each side.

### What the statement-first step bought, priced honestly

The five clauses cost about 350 lines, against an estimate that treated continuity of translation
in `L¹` as the main expense. That estimate was wrong by most of the work, in the direction of
*less*, because the fact was already proved here. Set against that, what the skeleton commit
actually earned was the **modelling decision**, and it earned it twice over:

* `𝒟` defined by the primitive rather than by absolute continuity. Mathlib's
  `AbsolutelyContinuousOnInterval` had arrived since the last survey, so the blueprint's own
  wording was expressible — and unusable, because the passage to `f = ∫₀^· f'` is the Lebesgue
  fundamental theorem and Mathlib carries only the converse. Every one of the five clauses uses
  the primitive form. **A new upstream theory arriving is normally what unblocks a node; here it
  arrived and the right move was still not to use it**, and that was legible only from the
  consumers.
* `memCore_iff_signaling_hypotheses`, the `iff`. Chapter 11 quantifies over the consequences of
  `f ∈ 𝒟` because `𝒟` had no definition when it was written; the equivalence is what says the
  definition supplies exactly those, and the `⇐` half is what would have caught a `𝒟` quietly
  strengthened to suit chapter 10.

### Two constructions the blueprint names and the obligation does not need

Recorded in `CIAxiomGuard.lean` and in the node's annotation. The estimate needs no `X₀`-valued
Bochner integral (bound pointwise, exchange in `ℝ≥0∞`), and the limit needs no separate treatment
of `[0,h)` (the identity `h⁻¹(T_hf - f) + f' = -h⁻¹∫₀^h (T_uf' - f')du` is exact on all of `ℝ`, so
the quotient is an *average* of translation defects). Both are the familiar pattern — the
classical derivation asks for more than the statement does — in a form it had not taken here
before: what it asked for was a **construction** rather than a citation.

## Next

Chapter 10 is finished to what Mathlib allows. `def:phillips-generator`, `lem:generator-properties`,
`thm:scale-cauchy` and `prop:fixed-scale-semigroup` all quantify over a generator and a
`C([0,∞);X₀) ∩ C¹((0,∞);X₀)` solution class, and Mathlib still has no closed-operator theory to
build one on. Note that they are *stateable* now in a way they were not this morning — `𝒟` and
`T_r` exist — so the gap is precisely Hille–Yosida-adjacent infrastructure and nothing else.

What is schedulable is `PLAN`'s **available, nothing depends on them** row, unchanged and now the
only such row: `prop:moments`, `prop:stable-moments`, `prop:gamma-kernels`, `prop:extreme-rays`,
`prop:volterra`, `lem:potential-kernel-scaling`, `cor:semigroup-case`. Re-check each against its
node before starting; that inventory has been wrong before, in both directions.

---

# `prop:extreme-rays`, split and half proved — 2026-08-14

`lem:admissible-cone` (7.13) and `lem:dickman-superposition` (7.14), in
`Hemigroup/AdmissibleCone.lean` and `Hemigroup/DickmanSuperposition.lean`, with `Ein` defined in
`Hemigroup/Ein.lean`. Lean core throughout. 55 nodes `\leanok`, 83 in the blueprint;
`Skeleton/Chapter7.lean` holds no declarations, one round after it was created.

## The node was the Lemma 7.1 shape for the third time in one chapter

7.7 asserted four things: the admissible exponents form a convex cone; the map
`(b₀,ρ) ↦ b₀s + ∫Ein(τs)ρ(dτ)` is a linear bijection onto it; hence the extreme rays are the pure
delay and the Dickman rays; and every admissible family is a *unique* superposition. The first two
are elementary. The third and fourth are not, and they are not hard for the same reason:

* **injectivity** is uniqueness of the Lévy–Khintchine triple — ledger **A3**, which quantifies
  over `BF` and cannot be stated here;
* **the extreme rays** need a Choquet argument, and the obstruction is *not* that Mathlib lacks
  `IsExtreme`. It has it. It is that `ρ = ∫δ_τ ρ(dτ)` has to be read as a barycentre in a cone of
  measures.

The node's own status line already said "not formalised: it needs Lebesgue–Stieltjes measures and
a Choquet argument". Half of that was wrong in the way this file keeps recording: the
Lebesgue–Stieltjes measure is not needed at all — `exists_tailMeasure` from chapter 9 supplies `ρ`,
and it was built precisely because `StieltjesFunction` does *not* apply to a Lévy tail. A
chapter-level "not formalised" reason had gone stale against work done two chapters later.

## What the injectivity clause is actually worth, recorded rather than attempted

Worth writing down because it is the same shape as chapter 9's Route B and might retire an A3
appeal. `hasDerivAt_toRealExponent` gives `F'(s) = b₀ + ∫₀^∞ e^{-st}k(t)dt`, and
`laplaceL_injective_of_ne_top` is Laplace injectivity for locally finite measures. So `F`
determines the measure `k(t)dt`, hence `k` a.e., hence `ρ` — with **no statement about `BF` as a
class**. That is a piece of work in its own right and it has not been done; it is in the node's
annotation so the next reader does not have to rediscover that the citation overstates the
obligation.

## Three things the proofs turned up

**`ℝ≥0∞` is why the cone is cheap.** Additivity of `levyJump` in `k` is a statement about
`lintegral`, so `lintegral_add_left'` needs only `AEMeasurable` of one summand and no
integrability side condition — where the classical argument has to know both integrals are finite
first. Here finiteness is the *conclusion*: it is exactly the `ne_top` field, and it comes out of
the additivity rather than being needed for it.

**The layer cake, for the third time.** `lintegral_comp_eq_lintegral_meas_lt_mul` carried both
halves of Route B and now carries this; only the antiderivative changes, from `1 - e^{-su}` to
`Ein(su)`. And its lack of a σ-finiteness hypothesis is load-bearing rather than convenient: the
tail measure of a *bounded* `k` — the Dickman ray being the extreme case — is a pushforward that
puts infinite mass at the origin, so `ρ` is σ-finite only after restriction to `(0,∞)`. Restricting
is what makes it a measure *on* `(0,∞)`, which is what the blueprint's `ρ ∈ M₊(0,∞)` says.

**And a docstring in `Examples.lean` was overcautious.** It records the Dickman exponent as having
"no elementary closed form", which is true and was read as "no closed form to prove". `Ein` is not
elementary and the identity `F_τ(s) = Ein(τs)` is one substitution; Mathlib has no exponential
integral of any kind, so `ein` is defined here on the pattern `riemannLiouville` set in chapter 11
— a definition, not an interface, since the article cites Caravenna–Sun–Zygouras for the Dickman
density and transform and not for a theorem about `Ein`.

## Next

`PLAN`'s *available, nothing depends on them* row, minus the entry just done: `prop:moments`,
`prop:stable-moments`, `prop:gamma-kernels`, `prop:volterra`, `lem:potential-kernel-scaling`,
`cor:semigroup-case`. Re-check each against its node before starting.

---

# `cor:semigroup-case`, proved — 2026-08-14

`Hemigroup/SemigroupCase.lean`. **Lean core**: the corollary spends no ledger entry, every input
being chapters 4–6 or `thm:increments-bernstein`. 56 nodes `\leanok`. No skeleton file was needed;
the decomposition into three general lemmas was enough to keep the main argument straight.

## Two Cauchy equations, and they are not the same problem

The proof uses Cauchy's functional equation twice, and Lean makes the asymmetry visible where the
prose does not.

* **Additive, on `[0,∞)`** — `x ↦ G(x,s)`. Mathlib's `map_real_smul` (continuous additive maps of
  real vector spaces are linear) does **not** apply on a half-line, so it needs an odd extension:
  `oddExtend h x = h(x⁺) - h(x⁻)`, continuous by construction because `max x 0` and `max (-x) 0`
  are, and additive because a difference of values depends only on the difference of arguments.
* **Multiplicative, on `(0,∞)`** — the multiplier of the action. Conjugating by `exp`/`log` puts it
  on **all** of `ℝ`, where `map_real_smul` applies with no extension at all.

So the equation the draft cites a lemma for (`fagerstrom2005temporal`, Lemma 2 — the multiplicative
one) is the *cheaper* of the two here, and the one it treats as obvious is the one that costs
forty lines. Worth recording next to `lem:mellin-vertical`'s lesson: which step is expensive in
Lean is not predictable from which step a paper pauses over.

## The formalisation collapsed two unknown functions into one

The blueprint's proof introduces `c` with `S_σ x = c(σ)x` and `c(σ)g(s) = g(σs)`, carries both
until Cauchy identifies `c(σ) = σ^α`, and only then concludes `g(s) = g(1)s^α`. Under the stated
normalisation `g_{0,1}(1) = 1` they are the same function: `(6.1)` at `s = 1` reads
`G(S_σ x, 1) = G(x, σ)`, and homogeneity turns the left side into `S_σ x` and the right into
`x·G(1,σ)`. So `S_σ x = x·G(1,σ)`, i.e. **`c = F` on `(0,∞)`**, and Cauchy is applied once.

That is not a shortcut around the mathematics — it is what the normalisation is *for* — and it is
the kind of thing a two-function presentation hides. The node's annotation now says it.

## `α ≤ 1` needs subadditivity, not membership of `BF₀`

The proof reads the bound off `F ∈ BF₀`, which the development cannot state. What the bound
actually uses is subadditivity, `F(s+t) ≤ F(s) + F(t)`, which is
`(1-e^{-su})(1-e^{-tu}) ≥ 0` rearranged under the Lévy integral and is therefore visible in `LE`
directly. At `s = t = 1` it gives `2^α ≤ 2`. So the bound costs no bridge and no ledger entry —
the same discipline `lem:selfdecomposable-increment` follows, and the third time in this chapter
that reading the obligation rather than the citation kept a proof interface-free.

## Next

`PLAN`'s *available, nothing depends on them* row, minus the two just done: `prop:moments`,
`prop:stable-moments`, `prop:gamma-kernels`, `prop:volterra`, `lem:potential-kernel-scaling`.
Re-check each against its node before starting.

---

# `prop:moments` stated; two clauses of three proved — 2026-08-14

`Hemigroup/MeanDelay.lean` (the two proved clauses and the definition of `meanRate`),
`Skeleton/Chapter8.lean` (the collation, `sorry`-free above one named sub-lemma). The node is
`\lean{Skeleton.moments}\notready`. 56 nodes `\leanok`; two `\notready`.

## The node divides again, and along a line the blueprint does not draw

Phase 0 already split this node once, moving the higher-moment criterion out as
`prop:moment-criterion` because it costs ledger A7 and the mean does not. What is left divides
again:

| clause | status |
|---|---|
| linearity of the influence curve | `lintegral_id_kernel_zero` — **proved** |
| finite iff `k` integrable at infinity | `meanRate_ne_top_iff` — **proved** |
| `E T₁ = F'(0+)` | open |

**The interesting one is the first.** The blueprint derives linearity *from* the identity —
`E T_x = xF'(0+)` is linear in `x` because the right-hand side is. In Lean the dependency runs the
other way: `kernel_zero_eq_map_lawT₁`, proved for chapter 11, says `μ_{0,x}` is the pushforward of
`μ_{0,1}` under `t ↦ xt`, so **every** moment scales by a change of variables, finite or not, and
the identity is needed only at `x = 1`. Same shape as `lem:delay-core`'s estimate: a clause the
prose derives from the main result rests on something weaker, and separating them is what makes
the main result's cost visible.

**And `[0,∞]` is the statement, not a convenience.** The proposition's second clause is about when
the mean is *infinite*, so `meanRate` is `ℝ≥0∞`-valued and no finiteness hypothesis appears
anywhere. The finiteness criterion is then one line of bookkeeping, because `∫₀¹ k < ∞` is forced
by the structure's own `ne_top` field (`integrableOn_k`) rather than assumed — so the only
condition is at infinity, which is exactly what the blueprint asserts.

## What the open clause needs, and why it is not differentiation

The blueprint says "differentiating the transform at the origin". In `[0,∞]` there is no
differentiation and no Tauberian theorem, because the difference quotient is **monotone**:

1. `antitoneOn_einIntegrand` — proved this round, in `Hemigroup/Ein.lean` — makes
   `s ↦ (1-e^{-st})/s` nonincreasing in `s` for each `t ≥ 0`. Along `s_n = 1/(n+1)` the integrands
   increase to `t`, so monotone convergence gives `E T₁ = ⨆ₙ (1 - H(s_n))/s_n`.
2. The same lemma inside the Lévy integral gives `F(s)/s = b₀ + ∫ einIntegrand(st)k(t)dt`
   increasing to `meanRate`. This is the clause the node's annotation names — *"monotone
   convergence in (7.1) and nothing else"*.
3. A squeeze joins them: `we^{-w} ≤ 1-e^{-w} ≤ w` at `w = F(s_n) → 0`. Both bounds are monotone,
   so the suprema agree — including when both are `⊤`, the case the proposition's second clause
   exists to describe and the one a real-valued argument would have to exclude.

Step 3 is the whole of the remaining cost and it is `ℝ≥0∞` bookkeeping, not analysis.

**Worth recording about `antitoneOn_einIntegrand` itself**, since it is the only genuinely new
mathematics of the round: the obvious route is the sign of the derivative, whose numerator is
`e^{-u}(1+u) - 1`, i.e. `1 + u ≤ e^u` — true, available, and needing the mean value theorem to get
back from the derivative to the function. The representation `(1-e^{-u})/u = ∫₀¹ e^{-uv}dv` needs
none of that: antitonicity is monotonicity of the integrand. Third time in this repo that replacing
a derivative by an integral was the shorter route (`lem:memory-kernel`, `lem:fractional-integral-
derivative`, here).

## Next

`PLAN`'s *available* row, minus what is done: `mean_delay_unit` (the clause above),
`prop:stable-moments`, `prop:gamma-kernels`, `prop:volterra`, `lem:potential-kernel-scaling`.

---

# `prop:moments` proved entire — 2026-08-14

`Hemigroup/MeanDelay.lean`, with the four facts about the difference quotient in
`Hemigroup/Ein.lean`. The node is `\lean{Hemigroup.moments}\leanok`; **57 nodes `\leanok`**, one
`\notready` (`prop:pair-regularity`). `Skeleton/Chapter8.lean` held only the open clause and the
collation, so it is gone, on the precedent of `Skeleton/Chapter12.lean`. The repo's only avoidable
`sorry` is now discharged: what remains is `hasCMDensity_iff`, which is ledger A9 by design.

Trust boundary unchanged. The identity spends **A17**, through `lawT₁ = μ_{0,1}`, as everything
that quantifies over the constructed family does; the monotone convergence *inside* the Lévy
integral (`tendsto_ofReal_inv_mul_exponent`) is Lean core, which is the reading one wants — the
Lévy side is a statement about `k` alone and does not know the family exists.

## The transform is used once, and everything else is monotone convergence

The three-step work order held, and the proportions it predicted did not. Stated as declarations:

| step | declaration | what it is |
|---|---|---|
| the law's quotient | `tendsto_lintegral_quotient_lawT₁` | monotone convergence |
| the exponent's quotient | `tendsto_ofReal_inv_mul_exponent` | monotone convergence |
| the two are the same quotient | `lintegral_quotient_lawT₁` | the transform, once |
| the squeeze | inside `lintegral_id_lawT₁` | `we^{-w} ≤ 1-e^{-w} ≤ w` |

`lintegral_quotient_lawT₁` is the only place the transform appears at all: it evaluates
`∫(1-e^{-st})/s \,d\mu_{0,1}` as `(1-e^{-F(s)})/s`, and the `ℝ≥0∞` subtraction it needs
(`1 - \mathrm{laplaceL}`) is bounded above by the probability mass, so `lintegral_sub` applies with
no hypothesis beyond causality. After that the two sides are two sequences of `ofReal`s of real
numbers, and the argument is about `w_n = F(s_n)` and nothing else.

## The `⊤` case cost nothing, and the reason is worth stating precisely

The plan expected the infinite case to be most of the work, and the route it sketched — take both
suprema and reach `⨆ A ≥ B_m` for each `m` through `ENNReal.mul_iSup` — would have needed an index
shift, because `A_n ≥ B_m · c_n` holds only for `n ≥ m`. **Working with `Tendsto` instead of `⨆`
removes the shift and the case split together.** Both sequences are monotone, so their limits are
their suprema and monotone convergence hands them over directly; and

    ENNReal.Tendsto.mul : Tendsto ma f (𝓝 a) → (a ≠ 0 ∨ b ≠ ⊤) →
                          Tendsto mb f (𝓝 b) → (b ≠ 0 ∨ a ≠ ⊤) → Tendsto (ma * mb) f (𝓝 (a*b))

has **both** side conditions discharged by `b = 1` alone, whatever `a` is. So `B_n · c_n → F'(0+)`
with no finiteness hypothesis, and `le_of_tendsto_of_tendsto'` closes the inequality in the
infinite case by the same line as in the finite one. The `0 · ⊤` pathology that makes `ℝ≥0∞`
multiplication discontinuous never arises, because the factor being killed tends to `1` and not
to `0`.

That is the general lesson and not a trick: *in `ℝ≥0∞`, a squeeze whose gap is multiplicative and
tends to `1` is unconditional, where a squeeze whose gap is additive would need the two sides to be
finite before they could be subtracted.* The classical proof differentiates and therefore works
additively, which is exactly why it has to assume the mean finite; the `[0,∞]` statement is not a
weakening of that proof but a different one.

## Two smaller things

**The quotient identity needs no hypothesis at all.** `(1-e^{-st})/s = t·einIntegrand(st)` is
`dilate_einIntegrand` with the two arguments exchanged, and it holds at `s = 0` and at `t = 0`
alike because Lean's `x / 0 = 0` makes both sides vanish in each. So neither monotone-convergence
step carries a guard, and the `t = 0` atom the law may have — nothing here excludes it, (H) not
being assumed — passes through untouched.

**`positivity` does not see through a `private def`.** `0 ≤ (s_n)⁻¹` had to be supplied as
`inv_nonneg.mpr (hpos n).le` in four places. Not a problem, but the failure mode is a bare
"failed to prove positivity" with no indication that the definition is the reason, which is worth
knowing before it is met at scale.

## Next

`PLAN`'s *available, nothing depends on them* row, minus what is done: `prop:stable-moments`,
`prop:gamma-kernels`, `prop:volterra`, `lem:potential-kernel-scaling`. And chapter 10's
`def:phillips-generator` and `lem:generator-properties`, whose blocked status is re-examined in
the next entry.

---

# Chapter 10 re-checked: `def:phillips-generator` and `lem:generator-properties` are not blocked — 2026-08-14

Nothing formalised this round; this entry is a **reclassification**, made the way the chapter-12
correction says to make one — by reading the nodes rather than the chapter-level status line that
was written above them. The verdict: 10.2 and 10.3 move from *blocked upstream* to *available,
nothing depends on them*. 10.4 (`thm:scale-cauchy`) and 10.5 (`prop:fixed-scale-semigroup`) stay
blocked, and the C₀-semigroup reason belongs to them alone.

`Skeleton/Chapter10.lean` is deliberately left holding no declarations. The statement-first rule
opens a node by writing its target type `sorry`-marked, and doing that today would re-add a
`sorry` to a repo that has just cleared its last avoidable one, for a node nobody is about to
attack. The reclassification is the deliverable; the skeleton entry belongs to the round that
takes the node on.

## Why the old status was stale, and it was stale in the ordinary way

"All of chapter 10 needs C₀-semigroup theory" was written when `𝒟` and `T_r` did not exist. They
exist now — `Hemigroup/DelayCore.lean`, this morning — and once the objects are there, what the
two nodes ask for is visible clause by clause:

| clause | what it needs | available? |
|---|---|---|
| 10.2, the definition | `𝒟`, `T_r`, `ν₁` | `DelayCore`, `transL1`, `exists_tailMeasure` |
| 10.3(1), absolute convergence | `norm_transL1_sub_le` and `∫(1∧r)ν_x < ∞` | yes |
| 10.3(2), the symbol | Fubini and `lem:memory-kernel` | yes |
| 10.3(3), commutation | `Φ` is a CLM, so it passes through the integral | yes |
| 10.3(4), continuity in `x` | dominated convergence, `continuous_transL1` | yes |
| 10.3(5), agreement with `κ^{(x)}*` | `laplaceL_memoryKernel`, Laplace uniqueness | yes |

**No clause mentions a generator's domain, a resolvent, or a generation theorem.** The one place
semigroup language appears is (4)'s "strong continuity of `T`", which is `continuous_transL1` —
chapter 4's, and one of the two facts the last round found the development already had.

The `X₀`-valued Bochner integral, which the plan had recorded as the expensive part of the
chapter, needs nothing new either: `X = L¹(ℝ)` is a complete normed real space, `transL1 r` is a
continuous linear map on it, and `r ↦ transL1 r f` is continuous, so the integrand is strongly
measurable and `MeasureTheory.integral` applies as written. Note that this is the *opposite* of
`lem:delay-core`'s finding, where the blueprint named a Bochner integral the obligation did not
need: here the integral is in the statement and not merely in the proof, so it has to be built —
and building it costs nothing.

## Three things the reading turned up, none of them a block

**The right-continuity normalisation is unavailable and unnecessary.** 10.2 says "with `k` taken
right-continuous and `k(∞) = 0`, so that `ν₁((r,∞)) = k(r)`". A `k` that is only nonincreasing has
no right-continuous representative this development can name, and `exists_tailMeasure` accordingly
gives the tail identity for **a.e.** `r`. That is exactly enough: every use of the tail is under
an integral in `r`. Chapter 9 made the same accounting for the potential kernel; the normalisation
is a convenience of the prose.

**`∫(1∧r)ν_x(dr) < ∞` is one layer cake, not integration by parts.** The proof of (1) reaches it
"from `∫₀¹k < ∞` and `k(1) < ∞` by integration by parts". Directly:
`∫(1∧r)ν₁(dr) = ∫₀¹ ν₁((u,∞))du = ∫₀¹ k(u)du`, which is `integrableOn_k` — and the `k(1) < ∞` half
of the cited hypothesis is not used at all. Fifth appearance of
`lintegral_comp_eq_lintegral_meas_lt_mul` in this article, and the fourth time it has replaced a
classical integration by parts.

**The uniqueness step of (5) is about a signed function, and linearity fixes that.**
`laplaceL_injective_of_ne_top` is about measures; the `V` of (5) is a signed locally integrable
function. Both `φ_x(∂_t)` and `κ^{(x)} * ·` are linear in `f`, and `f' ≥ 0` is preserved by
splitting `f'` into positive and negative parts (each is in `X₀`, and each primitive is in `𝒟`),
so it is enough to prove (5) for `f' ≥ 0` — where `f` is nondecreasing, `f - T_rf ≥ 0`, and both
sides of the identity are measures. Recorded because the obstruction looks real until the
linearity is used, and someone will otherwise reach for a signed-measure Laplace uniqueness the
development does not have.

## What it will actually cost, said in advance

Not free. Clause (2) is the one to price honestly: `Lap` is **not** a bounded functional on
`L¹(ℝ)`, `e^{-st}` being unbounded to the left of the origin, so `ContinuousLinearMap.integral_
comp_comm` — which does discharge (3) outright — does not apply to it. The exchange has to be done
on causal representatives in `[0,∞]`, the move chapter 2's Tonelli identity and `lem:delay-core`'s
estimate both make. Clause (5) additionally wants `mconv_eq_setIntegral_mconv` for a *locally
finite* causal measure, `κ^{(x)}` having total mass `F'(0+)`, which `prop:moments` has just finished
proving may be `⊤`; the existing lemma assumes `IsFiniteMeasure`. That is the generalisation the
previous entry already flagged as worth making and not worth making yet — this is the consumer
that makes it worth making.

Estimate: 10.2 small, 10.3 clauses (1), (3), (4) moderate, clauses (2) and (5) the bulk.

## What stays blocked, and why the distinction is not cosmetic

`thm:scale-cauchy` quantifies over a solution class `C([0,∞);X₀) ∩ C¹((0,∞);X₀)` and needs the
generation theory. It is also blocked a second way, through `prop:scale-evolution`(2), which is
distributional and which no Mathlib bump has yet made stateable — so it would remain out of reach
even with Hille–Yosida in hand. `prop:fixed-scale-semigroup` is the chapter's only `[A]` node
(Phillips, ledger A11) and records the semigroup reading for its own sake;
`thm:scale-cauchy` does not use it.

So the sentence that should be carried forward is **"chapter 10 is everything but the Cauchy
problem"**, and not "chapter 10 is blocked".

## Next

`PLAN`'s *available, nothing depends on them* row, now: `prop:stable-moments`,
`prop:gamma-kernels`, `prop:volterra`, `lem:potential-kernel-scaling`, `def:phillips-generator`,
`lem:generator-properties`. Re-check each against its node before starting; this inventory has
been wrong before, in both directions, and this entry is the second time in a week that a
chapter-level "blocked" turned out to have gone stale against work done since.

---

# Chapter 10 opened: `def:phillips-generator` defined, `lem:generator-properties` stated — 2026-08-14

`Hemigroup/PhillipsGenerator.lean` (10.2, **proved** — a definition has no `sorry` to carry) and
`Skeleton/Chapter10.lean` (10.3, five clauses `sorry`-marked under a `sorry`-free collation).
**58 nodes `\leanok`**, two `\notready` (`lem:generator-properties`, `prop:pair-regularity`).
Lean core throughout the definition, `exists_hasLevyTail` included. Trust boundary unchanged.

`Skeleton/Chapter10.lean` is the **first file here to be reopened**. It was emptied by
`lem:delay-core` this morning and now carries 10.3, which is the library working the way it was
built to: proving 10.1 constructed the setting that made 10.2 and 10.3 stateable, and the
chapter-level "blocked on C₀-semigroup theory" had been written before that setting existed.

## What the definition cost, against what the plan said it would

`PLAN` had the `X₀`-valued Bochner integral down as the expensive part of the chapter. It is
**seven lines**, and every piece of it was already here:

* `X = L¹(ℝ)` is a complete normed real space, so `MeasureTheory.integral` applies;
* `transL1 r` is a `→L[ℝ]`, so the integrand is a difference of continuous linear images;
* `r ↦ transL1 r f` is continuous — `continuous_transL1`, chapter 4 — so
  `Continuous.aestronglyMeasurable` gives strong measurability against *any* measure.

So the definition is **total**, with Bochner's junk value where the integral diverges, and clause
(1) of 10.3 is what says it means something on `𝒟` rather than what makes it well formed.

Worth setting beside `lem:delay-core`'s finding, which was the same object pointing the other way:
there the blueprint named a Bochner integral the *obligation did not need*, and going through
`ℝ≥0∞` was shorter. Here the integral is in the **statement** and not in a proof, so it has to be
built — and building it is free. The moral is not "avoid vector-valued integrals" but the narrower
one the plan keeps re-learning: *price the obligation, not the derivation*, in both directions.

## Three decisions the statements forced, which is what statement-first is for

**`ν₁` is a parameter, not a construction.** Every clause quantifies over a `ν` meeting
`HasLevyTail F ν` — causal, with `ν((r,∞)) = k(r)` a.e. — and `exists_hasLevyTail` supplies one
from chapter 9's quantile transform. That is `sonine_conservation`'s discipline ("stated against
an arbitrary `ℓ` meeting the specification, so that it does not wait on the existence half"), and
here it buys something extra: **the tail identity can only be `ae`**, because a `k` that is merely
`AntitoneOn (Ioi 0)` has no right-continuous representative this development can name. The
blueprint's "with `k` taken right-continuous" is a normalisation of the prose. It is also exactly
enough, every use of the tail sitting under an integral in `r` — but that is a fact about the
*consumers*, and writing the specification is what made it a checkable claim instead of a hope.

**The commutation clause is stated for an arbitrary causal probability measure.** Not for
`F.kernel y z`. It is what the proof uses — convolutions commute — it is strictly more general,
and it keeps clause (3) **off ledger A17**, which quantifying over the constructed family would
have put it on. `lem:delay-core`'s own `Φ`-clause is stated at the same level; this is one notch
further, and the notch is a ledger entry.

**Clause (5) is stated as a primitive, not as absolute continuity.** The blueprint says
`κ^{(x)} * f` is a.e. equal to an absolutely continuous function with derivative
`φ_x(∂_t)f`; the Lean statement says it agrees a.e. with the *primitive* of `φ_x(∂_t)f`. Same
assertion, and the primitive form is the one `𝒟` is defined in, the one Mathlib can get to
(the converse being the Lebesgue fundamental theorem), and the one that carries the blueprint's
trailing `(κ^{(x)}*f)(0+) = 0` for free — a primitive vanishes at the origin by construction. That
remark, which the prose proves in a sentence about `κ^{(x)}([0,t]) → b₀`, costs nothing here. The
third time the `𝒟`-as-primitive decision has paid, and the first time it has retired a step of a
proof rather than a hypothesis.

## The work order, with the estimate written down so it can be checked

Clauses (1), (3), (4) moderate; (2) and (5) the bulk. In `Skeleton/Chapter10.lean` in full; the
part worth repeating is where the two expensive ones actually get expensive.

**(2) cannot use the move that discharges (3).** `mconvL1 μ` is a continuous linear map, so
`ContinuousLinearMap.integral_comp_comm` pulls it straight through the Bochner integral. `Lap` is
**not** a continuous linear map on `L¹(ℝ)` — `e^{-st}` is unbounded to the left of the origin — so
the same move is unavailable and the exchange goes through causal representatives in `[0,∞]`,
as in chapter 2's Tonelli identity and `lem:delay-core`'s estimate. Two clauses of one lemma,
one of them a one-liner and the other not, for a reason invisible in the prose, which writes both
as "Fubini".

**(5) has a prerequisite the previous entry had already named.** It wants
`mconv_eq_setIntegral_mconv` for a *locally finite* causal measure; the existing lemma assumes
`IsFiniteMeasure`, and `κ^{(x)}` has total mass `F'(0+)`, which `prop:moments` has just finished
proving may be `⊤`. The generalisation was flagged two entries ago as "worth making and not worth
making today". This is the consumer that makes it worth making, and the sequence — general fact
proved narrowly, narrow form outlived by its first consumer, generalisation deferred until a
second consumer appears — is exactly the one `Hemigroup/Subordinator.lean` was created to avoid.

## Next

Prove 10.3, starting at `integrable_min_one_id` — `∫(1∧r)ν(dr) = ∫₀¹ν((u,∞))du = ∫₀¹k`, one layer
cake, and not the integration by parts the blueprint's proof names. Otherwise `PLAN`'s *available*
row: `prop:stable-moments`, `prop:gamma-kernels`, `prop:volterra`, `lem:potential-kernel-scaling`.
