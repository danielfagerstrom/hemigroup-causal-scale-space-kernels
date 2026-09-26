# Handoff

For the next session in this repository. **Rewritten at every session close, never appended to**:
it says what is true now, not what a session did (that is `CHANGELOG.md`). If it grows past a page,
something in it belongs elsewhere (`../article-kit/docs/PROCESS.md`, "Where each kind of text
lives").

## Where the work is

The article is published (`v1.0.0`). Formalization resumed here by the author's decision (hub
queue Q-0025 and Q-0041), and the queue it resumed for is done:

- **A17 is proved** (Q-0022);
- **`lem:mode-rigidity`** (Q-0020), **`lem:standing-levy-reading`** and **all of
  `lem:zstar-log-growth`** are proved (Q-0021);
- **`prop:pair-regularity`(2)'s two equivalences** are proved on Lean core (Q-0021). The node stays
  `[A]` on ledger A9, for clause (1).

The trust base is Lean core plus A18. The node count is 71 `\leanok` of 106.
`Formalization/Skeleton/` holds no `sorry`-marked target type; its files are kept for their record
of what each node cost. Continuing research runs in the hub (`wiki/hemigroup-programme.md`) and in
the later papers' repositories. A new version would start at `PROCESS.md`'s release section with a
`CHANGELOG.md` entry.

## Read first

1. `CLAUDE.md`: this article's rules (the trust boundary, the collation nodes, the two
   vocabularies, the editorial decisions in force).
2. `README.md` § State, and `linkage check` for the node counts.
3. The annotation of any node before working on it. `records/PLAN-chapters-8-12.md` holds the
   reasoning behind what is formalized and what is not. The module docstrings of
   `Hemigroup/PairRegularity.lean` and `Hemigroup/ZStarAbelian.lean` hold the routes last checked.

## Open

1. **No formalization target is queued.** What stays unformalized is by decision or blocked
   upstream:
   - the two `[depend]` advisories (A18 and the collation over it; see `CLAUDE.md`);
   - the scale-Cauchy problem (C₀-semigroups, distributions);
   - the locality chapter's ladder (Bessel `K`);
   - `prop:pair-regularity`'s clause (1) and clause (2)'s second assertion (A9);
   - the implementation and jet chapters, outside the Lean plan by decision.
2. **The `v1.1` pass owns the prose** that still says "A17", or calls nodes open that are now proved:
   - the blueprint annotations in chapters 7, 8, 9 and 11;
   - the per-declaration comments in `CIAxiomGuard.lean` and the cards in `REVIEW-fidelity.md`;
   - the paper's §1.1 inventory, which lists `Skeleton/` targets that no longer exist;
   - the D-D sentences owed where the verified proof takes another route than the printed one. In
     chapter 9 (`prop:pair-regularity`) the checked route never proves `a = 0`: it absorbs `a/s` as
     an atom. In chapter 11 (`lem:zstar-log-growth`) existence of the limit comes from clause (2),
     not from convexity through `B = sF'`.

   Nothing in the published paper has been touched, deliberately.
3. **The gates.**
   - `linkage axioms --check` now exits 0.
   - `build-blueprint.sh --quick` passes. Its proof-level `\leanok` check made
     `prop:pair-regularity`'s proof carry `\leanok` too, and the annotation says both marks cover
     only the two equivalences.
   - The full web step was not re-run after the scaffold's `PYTHONUTF8=1` adoption.
4. **A standing caution, seven instances in chapters 9–11.** What a proof reaches for is an upper
   bound on what its statement needs, and that covers the tools it reaches for as well as the nodes
   it cites. The latest two instances:
   - `lem:zstar-log-growth`(1)'s "drift case read off `negMoment` separately" was not needed: the
     comparison holds for any limit;
   - `prop:pair-regularity`'s "`a = 0` step" was not needed either.

## Waiting on the author

- **Decided (Q-0025, 2026-09-21): (b)**; **decided (Q-0041): (a)**, resume Q-0020 and Q-0021 in
  rank order; no `v1.1` decided.
- Q-0022, Q-0020 and Q-0021 are done. The open question is whether a `v1.1` is cut. It would carry
  the smaller trust base, the newly proved nodes (`lem:mode-rigidity`, `lem:standing-levy-reading`,
  `lem:zstar-log-growth`, `prop:pair-regularity`(2)) and item 2.
