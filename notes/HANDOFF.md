# Handoff

For the next session in this repository. **Rewritten at every session close, never appended to**:
it says what is true now, not what a session did (that is `CHANGELOG.md`). If it grows past a page,
something in it belongs elsewhere (`../article-kit/docs/PROCESS.md`, "Where each kind of text
lives").

## Where the work is

The article is published (`v1.0.0`). Formalization resumed here for one item, by the author's
decision (hub queue Q-0025, below): **A17 is proved** (Q-0022, `Hemigroup/CompoundPoisson.lean`),
so the trust base is Lean core plus A18. Continuing research runs in the hub
(`wiki/hemigroup-programme.md`) and in the later papers' repositories. A new version would start
at `PROCESS.md`'s release section with a `CHANGELOG.md` entry.

## Read first

1. `CLAUDE.md`: this article's rules (the trust boundary, the collation nodes, the two
   vocabularies, the editorial decisions in force).
2. `README.md` § State, and `linkage check` for the node counts.
3. The annotation of any node before working on it; `records/PLAN-chapters-8-12.md` holds the
   reasoning behind what is formalized and what is not.

## Open

1. **`lem:mode-rigidity`** is the first Lean target if formalization resumes: it sits on verified
   ground, and proving it would move the abstract's existence-and-uniqueness sentence inside the
   machine-checked perimeter. Target type `Skeleton.mode_rigidity`
   (`Formalization/Skeleton/Chapter11.lean`); the missing piece is the construction gluing a
   function on overlapping strip-translates into one entire periodic function, which Mathlib does
   not carry.
2. **The other `\notready` nodes**: `lem:standing-levy-reading` and `lem:zstar-log-growth`
   (`Skeleton/Chapter11.lean`), and `prop:pair-regularity`(2), ledger A9 by design
   (`Skeleton/Chapter9.lean`).
3. **Prose still saying "A17" after its retirement.** The blueprint annotations (chapters 7, 8,
   9, 11), the per-declaration comments in `CIAxiomGuard.lean` and `REVIEW-fidelity.md`'s cards
   say a declaration prints "A17 (and nothing else)"; it now prints Lean core, or Lean core plus
   A18. The guard's header and `AXIOMS.md` say so once; rewriting each occurrence, and the paper's
   §1.1 statement of what rests on what, belongs to whichever pass prepares a `v1.1`.
4. **Blocked upstream**: the scale-Cauchy problem (C₀-semigroups, distributions), and the locality
   chapter's ladder (Bessel `K`).

## Waiting on the author

- **Decided (Q-0025, 2026-09-21): (b)** resume formalization in Paper I with Q-0022 (A17 to a
  lemma) only; Q-0020 and Q-0021 are decided after it; no `v1.1` until something is proved.
- Q-0022 is now done (A17 proved), so the open questions are Q-0020 and Q-0021, and whether a
  `v1.1` is cut to carry the smaller trust base (it would also carry item 3 above).
