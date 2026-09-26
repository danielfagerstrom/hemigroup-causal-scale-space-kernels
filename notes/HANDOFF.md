# Handoff

For the next session in this repository. **Rewritten at every session close, never appended to**:
it says what is true now, not what a session did (that is `CHANGELOG.md`). If it grows past a page,
something in it belongs elsewhere (`../article-kit/docs/PROCESS.md`, "Where each kind of text
lives").

## Where the work is

The article is published (`v1.0.0`). Formalization resumed here by the author's decision (hub
queue Q-0025 and Q-0041): **A17 is proved** (Q-0022), **`lem:mode-rigidity` is proved** (Q-0020),
and **`lem:standing-levy-reading` is proved** with `lem:zstar-log-growth`'s drift clause beside it
(Q-0021). The trust base is Lean core plus A18. Node count: 69 `\leanok` of 106. Continuing
research runs in the hub (`wiki/hemigroup-programme.md`) and in the later papers' repositories. A
new version would start at `PROCESS.md`'s release section with a `CHANGELOG.md` entry.

## Read first

1. `CLAUDE.md`: this article's rules (the trust boundary, the collation nodes, the two
   vocabularies, the editorial decisions in force).
2. `README.md` § State, and `linkage check` for the node counts.
3. The annotation of any node before working on it; `records/PLAN-chapters-8-12.md` holds the
   reasoning behind what is formalized and what is not, and the `Skeleton/` module docstrings hold
   what each open target type waits on.

## Open

1. **Four `sorry`-marked target types remain**, all surveyed 2026-09-26 (Q-0021) with the route
   and the obstacle written at each declaration:
   - `lem:zstar-log-growth`, three of four clauses (`Skeleton/Chapter11.lean`). The **driftless
     case of (2)** is the bottleneck and the only one with real content; its Cesàro step needs an
     `∞/∞` L'Hôpital that Mathlib does not carry (`LHopital.lean` is the `0/0` form only), plus a
     case split on `k(0⁺) = ∞`. (1) is that limit plus an Abelian comparison; (4) is a corollary
     of (1). Nothing is blocked on the trust boundary, and nothing downstream consumes them.
   - `prop:pair-regularity`(2) (`Skeleton/Chapter9.lean`). **"Ledger A9 by design" is right about
     the node and not established about the declaration** — read that docstring before repeating
     the phrase. A9's cited theorems are used only for the second assertion, which the target type
     does not state; the two equivalences it does state are Tonelli plus Laplace uniqueness. What
     is unknown is whether the declaration can be discharged off the boundary.
2. **Prose still saying "A17" after its retirement.** The blueprint annotations (chapters 7, 8,
   9, 11), the per-declaration comments in `CIAxiomGuard.lean` and `REVIEW-fidelity.md`'s cards
   say a declaration prints "A17 (and nothing else)"; it now prints Lean core, or Lean core plus
   A18. The guard's header and `AXIOMS.md` say so once; rewriting each occurrence belongs to
   whichever pass prepares a `v1.1`. **The same pass owns the paper**: §1.1's inventory still
   lists four `Skeleton/` targets by their old names and says nothing about `lem:mode-rigidity`
   or `lem:standing-levy-reading` being machine-checked, and decision D-D's one sentence saying
   the verified proof takes another route than the printed one is not in chapter 9 yet. Nothing
   in the published paper has been touched, deliberately.
3. **Two gates fail for reasons this line of work did not cause**, both pre-existing and both
   out of scope until someone owns them:
   - `linkage axioms --check` exits 1: LINKAGE.md rule 5 now wants a source transcription for
     every entry grounding an admitted interface, and **A18 has none** (no `**Verbatim:**` block,
     no `blueprint/AXIOMS-verbatim.md`). Twenty further entries carry the same advisory
     non-fatally. Nothing in the repository has ever satisfied this; it is a newer `linkage`
     requirement.
   - `bash scripts/build-blueprint.sh`'s **web step fails on this machine only**: plasTeX writes
     the `\lean`-tag decl list with Python's default cp1252 encoding, and
     `lem:zstar-log-growth`'s tag has carried `b₀` since 2026-08-29. `--quick` (PDF, control
     chars, manifest) passes. A one-line `PYTHONUTF8=1` in the script, or ASCII-only decl names,
     would fix it; CI on Linux is unaffected.
4. **Blocked upstream**: the scale-Cauchy problem (C₀-semigroups, distributions), and the locality
   chapter's ladder (Bessel `K`).

## Waiting on the author

- **Decided (Q-0025, 2026-09-21): (b)**; **decided (Q-0041): (a)** resume Q-0020 and Q-0021 in
  rank order; no `v1.1` decided.
- Q-0022, Q-0020 and Q-0021 are done, so the open question is whether a `v1.1` is cut to carry the
  smaller trust base and the three newly proved nodes (it would also carry item 2).
