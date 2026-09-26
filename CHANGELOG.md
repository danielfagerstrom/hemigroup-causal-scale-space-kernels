# Changelog

One entry per release, headed `## <tag> — <date> — <title>`, saying what changed and why, and which
statements were renumbered, strengthened, weakened or withdrawn (`../article-kit/docs/RELEASE.md`,
rule 2). Work since the last release accumulates under Unreleased.

## Unreleased

### `lem:standing-levy-reading` proved; the other two `\notready` nodes surveyed (2026-09-26, Q-0021)

**`lem:standing-levy-reading` (11.22) is machine-checked**, both clauses, as
`Hemigroup.SelfDecomposableExponent.standing_levy_reading` in
`Formalization/Hemigroup/StandingLevyReading.lean`; the node carries `\leanok` on statement and
proof. Statements unchanged from the August target types, so no ledger row. `#print axioms` gives
Lean core. Node count: 68 `\leanok` → 69.

**`lem:zstar-log-growth` (11.23): one of four clauses proved.** Clause (2)'s drift case is
`Hemigroup.SelfDecomposableExponent.tendsto_toRealExponent_div_log_atTop_of_b₀_pos`
(`Formalization/Hemigroup/ZStarLogGrowth.lean`, Lean core). The node keeps `\notready`; the other
three target types stay in `Skeleton/Chapter11.lean`.

**The pricing was wrong again, in the same direction.** 11.22 was priced "statable, not cheap" on
two counts, and the proof undercut both:

- the `[0,∞]`-to-`ℝ` bridge was wanted in *both* directions of the `iff`. Only the divergent
  direction needs a limit at all; the convergent one is the uniform bound
  `levyJump k s ≤ levyMass k`, which is `1 - e^{-st} ≤ 1` and no convergence theorem, and which
  needs no sign condition on `s` either — `ENNReal.ofReal` truncates the negative case. Monotone
  convergence is used once, along the naturals, in one direction;
- `∫₀^{t₀} t⁻¹dt = ∞` is indeed absent from Mathlib in `lintegral` form, but present in
  integrability form (`intervalIntegrable_inv_iff`), and `hasFiniteIntegral_iff_ofReal` crosses
  between them in six lines.

That is the fifth time in this chapter that what a proof cites was an upper bound on what its
statement needs. The blueprint proof of 11.22 was rewritten to the checked route (decision D-D
governs the *paper*; the blueprint is the text of record and follows the Lean).

**What the proof taught.** Clause (2) — a nonzero admissible exponent satisfies (H)'s first
clause — is **false** for a general Lévy exponent: a driftless compound Poisson with finite Lévy
mass is bounded and nonzero. It holds here only because the density against `dt/t` is
nonincreasing, so one point where `k` is positive bounds `k` below on all of `(0,t₀]` and the mass
diverges at the origin. Self-decomposability, not Lévy structure, is what leaves the admissible
cone with no bounded nonzero member.

**What the three remaining clauses of 11.23 wait on** (routes written out, none attempted; the
node's status paragraph and `Skeleton/Chapter11.lean` carry the detail). The driftless case of (2)
is the bottleneck and the only one with real content: its first half is `B(s) = sF'(s)` from
`hasDerivAt_toRealExponent` plus the same monotone convergence 11.22 uses, and its second is the
Cesàro step `F(s)/log s = (log s)⁻¹∫₁^s B(v)dv/v → lim B`, for which **Mathlib's L'Hôpital is the
`0/0` form only** — `Mathlib/Analysis/Calculus/LHopital.lean` has no `∞/∞` companion at `atTop`.
Clause (1) is that limit plus an Abelian comparison through
`Γ(ζ)E[T₁^{-ζ}] = ∫₀^∞ s^{ζ-1}e^{-F(s)}ds`, already in the library as the route
`stableExponent_negMoment_ne_top` takes; clause (4) is a corollary of (1). None is blocked on the
trust boundary. The "plausible shortcut" recorded for clause (1) — `B`'s monotonicity from the
explicit formula rather than from ledger A18 — is still untested: the drift case does not touch
`B`.

**`prop:pair-regularity`(2): "ledger A9 by design" is right about the node and not established
about the declaration.** The handoff has carried that phrase as the reason `Skeleton.hasCMDensity_iff`
is not attempted. The node is `[A]` because of clause (1) (SSV Thm. 11.3, the potential measures of
special subordinators), which the target type does not state; and within clause (2), A9's two
structural inputs (SSV Thm. 7.3 and Thm. 6.2) are used *only* for the second assertion, about
`ℓ^{(x)}` and `F ∈ CBF`, which the target type also does not state. What it does state — the two
equivalences — the blueprint proves from `lem:memory-kernel`'s derivative formula by Tonelli one
way and Laplace uniqueness the other, citing neither theorem. So the reason it stays open is that
nobody has written the proof, and the converse is real work (the `a = 0` step, then
`laplaceL_injective_of_ne_top`, then the a.e.-versus-everywhere care `HasCMRep`'s pointwise form
imposes) — not the trust boundary. Recorded at the node and at the declaration; not acted on.

### `lem:mode-rigidity` proved (2026-09-25, Q-0020)

`Skeleton.mode_rigidity` is now `Hemigroup.mode_rigidity`, in
`Formalization/Hemigroup/ModeRigidity.lean`, and 11.25 carries `\leanok` on statement and proof.
The statement is unchanged from the target type written in August, so no ledger row: nothing was
narrowed, split, restated or admitted. `#print axioms` gives Lean core and nothing else — not even
A18 — and `CIAxiomGuard.lean` has the line. Node count: 67 `\leanok` → 68; three `\notready` nodes
remain (`lem:standing-levy-reading`, `lem:zstar-log-growth`, `prop:pair-regularity`(2)).

**The pricing was wrong, and in an instructive way.** The node was priced at a session's work for
a construction Mathlib does not carry: gluing a function given on translates of one finite-width
strip, related by a functional equation on their overlaps, into one entire periodic function. That
is true of Mathlib and true of the *order* of steps the blueprint proof assumes; it is not true of
the obligation. Exchanging the middle two steps removes the construction:

- the hypothesis's boundedness already propagates over the whole strip `(0, z_*)` without leaving
  it — for `z` in the strip some integer translate `Re z + k` lies in `[c, c+1]`, and every
  intermediate translate lies between `Re z` and `Re z + k`, hence in the strip, that being an
  interval;
- so the singularities are removed *first*, on the strip, and the gluing is then of analytic
  pieces, where the whole of it is the well-definedness of `P(z) := q(z - n)` in `n` — and that is
  where `z_* > 1`, i.e. (H), is spent;
- the points the propagation misses (those whose integer orbit inside the strip meets a zero of
  `H̃`) form a countable set, and a countable set in `ℂ` has dense complement, so continuity closes
  the gap. The same device — a bound on a set with countable complement is a bound everywhere a
  continuous function is defined — does three jobs in the file, the third being to promote
  `p(z) = p(z-1)` from "off the zeros" to an identity of analytic functions.

Nothing meromorphic appears in the formalisation; Mathlib's
`Complex.differentiableOn_update_limUnder_of_bddAbove` and
`Differentiable.exists_const_forall_eq_of_bounded` are the only analysis used. This is the fourth
time in chapter 11 that what a proof cites, or the order it cites it in, turned out to be an upper
bound on what the statement needs.

The blueprint proof is rewritten to the checked route, per the framework's "proof of record
follows the machine-checked route". The paper's printed proof stays classical (decision D-D), and
the paper's §1.1 inventory of what is and is not machine-checked is *not* touched here: like the
A17 prose, it belongs to whichever pass prepares a `v1.1`. `blueprint/render-allowlist.txt` gains
`bigcup`, `lceil`, `rceil`, standard commands the rewritten proof uses.

### Ledger A17 retired: the subordinator existence is proved (2026-09-21, Q-0022)

`Hemigroup.exists_isFiniteMeasure_laplace_eq_exp_neg_levyExponent` was an axiom (ledger A17) and
is now a `theorem`. Its statement is unchanged, so no downstream statement changed. The proof is
new, in `Formalization/Hemigroup/CompoundPoisson.lean`, and follows the route the interface had
named when it was admitted:

- for a finite causal `ν`, the compound-Poisson measure `e^{−‖ν‖} Σ ν^{*n}/n!` has transform
  `exp(−∫(1 − e^{−st}) ν(dt))`;
- truncating `ν` to `(1/(n+1), ∞)` gives finite measures whose exponents increase to `ν`'s;
- the resulting laws are tight (a Markov bound from the transforms near `s = 0`), so Mathlib's
  Prokhorov theorem gives a weak cluster point. Testing it against two bounded continuous
  functions identifies its transform and shows it is causal. No subsequence is needed.
- the drift is a translation.

The name left `blueprint/trust-boundary.txt`, and the trust base is now Lean core plus A18.
`AXIOMS.md` keeps the A17 entry, marked retired, because identifiers are never reused.
`REVIEW-fidelity.md` has row R28. `README.md`, `CIAxiomGuard.lean`'s header and
`Interfaces.lean` say so. The per-node prose that still reads "on A17 alone" is listed in
`notes/HANDOFF.md` for the pass that prepares a `v1.1`.

### The instruction files cleaned to article-kit ADR-0001 (2026-09-21)

No statement, proof, Lean declaration, ledger entry or findings-ledger row changed. The instruction
files were cleaned to what they are for, following the pilot in `spatial-hemigroup-scale-space`:

- `linkage init --sync` installed the shared session rules in `.claude/rules/article-kit/`, with
  `adr/README.md` and `records/README.md`.
- `CLAUDE.md` holds this article's standing rules only; its status section and the general
  tooling rules (now the session rules) are gone, and the author's standing instructions kept in
  per-project memory (commit and push each step, the article's priorities, the editorial
  decisions in force) moved into it. `README.md`'s status section is one short `## State` section
  with today's numbers. `notes/HANDOFF.md` is new.
- Records moved, content unchanged: `notes/PLAN-chapters-8-12.md`, `PLAN-content-review.md`,
  `PLAN-fidelity-review.md`, `PLAN-publication.md`, `DECISIONS.md` and `NOTES-exposition.md` to
  `records/`. The findings ledger `notes/REVIEW-fidelity.md` moved to `blueprint/REVIEW-fidelity.md`,
  where article-kit's process keeps it. The full-path references in three Lean docstrings and
  `paper/main.tex`'s header comment follow; `LICENSE.md` names `records/` beside `notes/`.
- `notes/ROADMAP.md` is deleted: its three items were delivered (the content review, the shared
  statements, the prose pass). What is open is in `notes/HANDOFF.md`.
- `notes/reviews/` and `notes/PLAN-review-response.md` stay where they are, because the published
  AI statement names `notes/reviews/` by path, beside the plan.

## v1.0.0 — 2026-09-02 — first release

The monograph, published on Zenodo (version DOI 10.5281/zenodo.22259187, concept DOI
10.5281/zenodo.22259186). The development up to the release is in git and
`records/PLAN-publication.md`.
