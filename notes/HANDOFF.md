# Handoff

For the next session in this repository. **Rewritten at every session close, never appended to**:
it says what is true now, not what a session did (that is `CHANGELOG.md`). If it grows past a page,
something in it belongs elsewhere (`../article-kit/docs/PROCESS.md`, "Where each kind of text
lives").

## Where the work is

The article is published as **`v1.1.0`** (2026-09-27; version DOI 10.5281/zenodo.22992450,
concept DOI 10.5281/zenodo.22259186, the tag at `7ca1047`), the first release of this article
through `linkage release`. `v1.0.0` (2 September 2026, DOI 10.5281/zenodo.22259187) is its first
version. The post-release steps are done: the hub's pin and `site` block, the source page
`@fagerstrom2026hemigroup`, the programme page and the log, and the site's `/papers/` route.

- The trust base is Lean core plus A18. A17 is proved; the node count is 71 `\leanok` of 106.
- `CHANGELOG.md`'s Unreleased section holds two code-only changes since the tag, toward the next
  version: the 34 Lean style warnings of the export build cleared (Q-0178, no statement changed,
  `CIAxiomGuard.lean`'s output byte-identical), and `Basic.lean`'s docstring saying that
  `ScaleSpaceCore` is provenance, not a dependency (Q-0183).
- The export's staging tree is `C:/Users/danie/dev/hemigroup-causal-scale-space-kernels-export`,
  beside this repository where `lake-store` links it. The repository is public and single-module,
  so there is no separate public export repository; `repo_url` in `linkage.toml` is this one.
- `Formalization/Skeleton/` holds no `sorry`-marked target type; its files are kept for their
  record of what each node cost.

## Read first

1. `CLAUDE.md`: this article's rules (the trust boundary, the collation nodes, the two
   vocabularies, the editorial decisions in force).
2. `CHANGELOG.md`'s `v1.1.0` entry and its Unreleased section.
3. `../article-kit/docs/RELEASE.md` rule 6 (a version after the first), before any next version.

## Open

1. **Fidelity ledger R36 is open.** Two claims under `\leanok` nodes have no declaration:
   `lem:zstar-log-growth`(3), which §1.1 counts as verified, and the closing gloss of
   `lem:standing-levy-reading`(2). Both are true, and both elaborate in a few lines from the tagged
   declarations (Lean core). The proposed fix is Lean up: two corollaries in `ZStarAbelian.lean`,
   added to the tags and the axiom guard. The alternative is to narrow §1.1. Cards T2.4a–c in
   `blueprint/REVIEW-fidelity.md` now cover the three nodes R35 recorded as uncarded, so they
   may be cited as audited.
2. **The AI statement's figures** ("By the numbers", computed 5 September 2026) predate the
   September Lean work. They are printed as dated lower bounds in `v1.1.0`; a next version
   re-derives them with `chronicler stats`, which an unattended session cannot run.
3. **Nothing is queued for a next version.** Q-0023 (the scale-Cauchy problem and the locality
   ladder) is blocked on Mathlib.

## Standing

- **Version tags are three-part** (`v1.0.0`, `v1.1.0`); the export writes the plain `vX.Y` in its
  own metadata, which the author accepted as cosmetic.
- **A standing caution, seven instances in chapters 9–11.** What a proof reaches for is an upper
  bound on what its statement needs, and that covers the tools it reaches for as well as the nodes
  it cites.
- No formalization target is queued. What stays unformalized is by decision or blocked upstream:
  the two `[depend]` advisories (A18 and the collation over it); the scale-Cauchy problem; the
  locality chapter's ladder (Bessel `K`); `prop:pair-regularity`'s clause (1) and clause (2)'s
  second assertion (A9); the implementation and jet chapters.
