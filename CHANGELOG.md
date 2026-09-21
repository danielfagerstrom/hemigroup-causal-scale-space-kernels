# Changelog

One entry per release, headed `## <tag> — <date> — <title>`, saying what changed and why, and which
statements were renumbered, strengthened, weakened or withdrawn (`../article-kit/docs/RELEASE.md`,
rule 2). Work since the last release accumulates under Unreleased.

## Unreleased

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
