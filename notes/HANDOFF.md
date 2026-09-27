# Handoff

For the next session in this repository. **Rewritten at every session close, never appended to**:
it says what is true now, not what a session did (that is `CHANGELOG.md`). If it grows past a page,
something in it belongs elsewhere (`../article-kit/docs/PROCESS.md`, "Where each kind of text
lives").

## Where the work is

The article is published (`v1.0.0`). **`v1.1.0` is prepared up to `RELEASE.md`'s checklist item 3**
(Q-0158): items 1 and 2 are done, the paper's prose is brought to the development, and what
remains is the author's.

- The trust base is Lean core plus A18. A17 is proved (Q-0022); `lem:mode-rigidity` (Q-0020),
  `lem:standing-levy-reading`, all of `lem:zstar-log-growth` and `prop:pair-regularity`(2)'s two
  equivalences (Q-0021) are proved. The node count is 71 `\leanok` of 106.
- The paper's §1.1 lists all of this; the abstract, §7 and §13 say "one cited fact". The three
  D-D sentences are in (after the printed proofs of Lemma 9.4, Lemma 9.20 and Proposition A.9).
  Lemmas 9.9 and 10.4 read in their corrected forms in the built PDF.
- `CHANGELOG.md` has the `v1.1.0` entry, dated 2026-09-27 provisionally.
- `Formalization/Skeleton/` holds no `sorry`-marked target type; its files are kept for their
  record of what each node cost.

## Read first

1. `CLAUDE.md`: this article's rules (the trust boundary, the collation nodes, the two
   vocabularies, the editorial decisions in force).
2. `../article-kit/docs/RELEASE.md` § "The checklist", from item 3, and rule 6.
3. `CHANGELOG.md`'s `v1.1.0` entry, which the version-history section is reworded from.

## Open: the author's steps, in `RELEASE.md`'s numbering

   **The release goes through `linkage release`** (the author, 2026-09-27), the first time for
   this article: `linkage.toml` now carries `[release]` and one `[[modules]]` table (`kernels`,
   tag `v1.1.0`). This repository is public and single-module, so there is no public export
   repository: `<export>` is a local staging tree, `C:/Users/danie/dev/hemigroup-causal-scale-space-kernels-export`, beside this repository where `lake-store` links it (the zip is named after the PDF), which the
   Zenodo commands read and zip; `repo_url` is this repository. It needs article-kit's fix for
   three-part tags and primed names (article-kit PR #27); without it the rule 6 gate is skipped
   silently. `linkage release export --dry-run` passes except for what the freeze sets.

0. **Rehearse on the sandbox first** (the author, `ZENODO_SANDBOX_TOKEN`): `export --draft`,
   `zenodo reserve --sandbox`, `upload`, `status`, `publish`, as `RELEASE.md` "The commands".
3. **Reserve the DOI**: `linkage release export --draft --out <export>`, then
   `linkage release zenodo reserve --export <export> --record 22259187`, a new version of the
   v1.0.0 record under concept DOI 10.5281/zenodo.22259186 (without `--record` it would open a
   new concept).
4. **Freeze the paper.**
   - The `\date` in `paper/main.tex` in the later-version form of rule 6: `v1.1.0`, its date and
     version DOI, then "first released as `v1.0.0`, 2 September 2026 (DOI
     10.5281/zenodo.22259187)", with the concept DOI as the thing to cite.
   - §1.1's "Where to look" sentence still names the `v1.0.0` tag and its version DOI; a comment
     beside it marks it. Set it with the `\date`.
   - The version-history section, unnumbered, after the conclusions and before the references.
     Its template, `scaffold/paper/version-history.tex.in`, is **not in this repository** (it is
     in `article-kit`, and `linkage init --sync` last ran here on 2026-09-26 without bringing
     it). Seed from article-kit's copy, reworded from the changelog entry.
   - If the freeze date is not 2026-09-27, change the changelog heading's date to match.
   - Build into `paper/`, read page 1 and the version history, commit.
5. to 10. as `RELEASE.md` has them: export with `--doi … --build`; tag `v1.1.0` here; in
   `<export>`, `git init`, commit and tag `v1.1.0` (the zip `upload --tag v1.1.0` archives), no
   public repository; the deposit; the library, the site, the hub, the next cycle.

## Before the freeze, for the author to judge

- **The AI statement's figures** ("By the numbers", computed 5 September 2026) predate the
  September Lean work (A17's proof, Q-0020, Q-0021, Q-0141). They are dated, so still true as
  lower bounds; re-deriving them needs `chronicler stats`, which an unattended session cannot run.
- **Three proved nodes have no fidelity card** (`lem:mode-rigidity`, `lem:standing-levy-reading`,
  `lem:zstar-log-growth`; R33 covers the last one's hypotheses only). No *interface* was admitted
  after the fidelity review: A19–A21 (2026-09-01) have no Lean name, so they are outside the
  trust boundary the cards audit.
- The version tag: `v1.1.0` was chosen to match `v1.0.0`'s three-part form. The export writes
  the plain `vX.Y` in its metadata.

## Standing

- **A standing caution, seven instances in chapters 9–11.** What a proof reaches for is an upper
  bound on what its statement needs, and that covers the tools it reaches for as well as the nodes
  it cites.
- No formalization target is queued. What stays unformalized is by decision or blocked upstream:
  the two `[depend]` advisories (A18 and the collation over it); the scale-Cauchy problem; the
  locality chapter's ladder (Bessel `K`); `prop:pair-regularity`'s clause (1) and clause (2)'s
  second assertion (A9); the implementation and jet chapters.
