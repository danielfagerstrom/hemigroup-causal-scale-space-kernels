# Handoff

For the next session in this repository. **Rewritten at every session close, never appended to**:
it says what is true now, not what a session did (that is `CHANGELOG.md`). If it grows past a page,
something in it belongs elsewhere (`../article-kit/docs/PROCESS.md`, "Where each kind of text
lives").

## Where the work is

The article is published (`v1.0.0`). Formalization resumed here by the author's decision (hub
queue Q-0025 and Q-0041, below): **A17 is proved** (Q-0022, `Hemigroup/CompoundPoisson.lean`), so
the trust base is Lean core plus A18, and **`lem:mode-rigidity` is proved** (Q-0020,
`Hemigroup/ModeRigidity.lean`), on Lean core alone. Continuing research runs in the hub
(`wiki/hemigroup-programme.md`) and in the later papers' repositories. A new version would start
at `PROCESS.md`'s release section with a `CHANGELOG.md` entry.

## Read first

1. `CLAUDE.md`: this article's rules (the trust boundary, the collation nodes, the two
   vocabularies, the editorial decisions in force).
2. `README.md` § State, and `linkage check` for the node counts.
3. The annotation of any node before working on it; `records/PLAN-chapters-8-12.md` holds the
   reasoning behind what is formalized and what is not.

## Open

1. **The remaining `\notready` nodes**: `lem:standing-levy-reading` and `lem:zstar-log-growth`
   (`Skeleton/Chapter11.lean`), and `prop:pair-regularity`(2), ledger A9 by design
   (`Skeleton/Chapter9.lean`). The first two are Q-0021's subject; their own annotations price
   them, and `lem:zstar-log-growth`(1) carries a recorded shortcut that would keep it off A18.
   Read `ModeRigidity.lean`'s module docstring before pricing either: this chapter's pricings have
   now been wrong four times, each time because the *order* of steps a proof sketch assumes was
   read as the obligation.
2. **Prose still saying "A17" after its retirement.** The blueprint annotations (chapters 7, 8,
   9, 11), the per-declaration comments in `CIAxiomGuard.lean` and `REVIEW-fidelity.md`'s cards
   say a declaration prints "A17 (and nothing else)"; it now prints Lean core, or Lean core plus
   A18. The guard's header and `AXIOMS.md` say so once; rewriting each occurrence belongs to
   whichever pass prepares a `v1.1`. **The same pass owns the paper**: §1.1's inventory still
   lists `lem:mode-rigidity` among the four `Skeleton/` targets and says nothing about the node
   being machine-checked, and decision D-D's one sentence saying the verified proof takes another
   route than the printed one is not in chapter 9 yet. Nothing in the published paper was touched
   by Q-0020, deliberately.
3. **Blocked upstream**: the scale-Cauchy problem (C₀-semigroups, distributions), and the locality
   chapter's ladder (Bessel `K`).

## Waiting on the author

- **Decided (Q-0025, 2026-09-21): (b)** resume formalization in Paper I with Q-0022 (A17 to a
  lemma) only. **Decided (Q-0041): (a)** resume Q-0020 and Q-0021 in rank order; no `v1.1`
  decided.
- Q-0022 and Q-0020 are now done, so the open questions are Q-0021 and whether a `v1.1` is cut
  to carry the smaller trust base and the two newly proved nodes (it would also carry item 2).
