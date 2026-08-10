# hemigroup-causal-scale-space-kernels — Claude Code context

**What this is.** An article satellite of the research constellation (slug `hcs`):
*"Time-Causal Scale Space from Hemigroup Axioms: Characterization of the Kernels."*
A machine-checked Lean 4 formalisation and a self-published monograph, both driven by one
blueprint.

## Where this sits

- **Framework** — `article-kit` (the `linkage` CLI, the LaTeX scaffolding, the reusable CI,
  the shared `mathematician` agent). `linkage.toml` binds this repo to it. Do not edit the
  framework-owned files under `blueprint/src/` here; `linkage check` reports drift.
- **Shared Lean** — `scale-space-lean` (`ScaleSpaceCore`), pinned to a tag in
  `Formalization/lakefile.toml`. It carries nothing resting on a cited interface, so
  importing it adds nothing to this article's trust base.
- **Hub** — `$WIKI_VAULT`: positioning, literature, and the editorial plan, in the outline
  page `wiki/outlines/hemigroup-causal-scale-space-kernels.md`.
- **Librarian** — `$LIBRARY_DIR`: all sources. `library resolve <citekey> --json`.

## Scope & conventions

- **Verified core, axiomatized analysis.** Prove the structural content; take the deep
  analysis (Bernstein-function theory, self-decomposability, the Lévy–Khintchine
  representation) as clearly-labelled `[A]` interfaces, each grounded in `AXIOMS.md` with a
  page anchor. Verify with `#print axioms` — it must reduce to Lean core plus the names in
  `blueprint/trust-boundary.txt`.
- **The blueprint is the text of record.** The wiki and the paper transclude its nodes
  verbatim; they may not restate them. Write statements *and* proofs as publication-quality
  mathematics — "see Lean" is not a proof.
- **Descriptive, non-hyped naming.** Name results plainly.
- **This is a sibling of `scale-space-foundations`, not a chapter of it.** Never refer to
  another deliverable by section number.

## Status

Blueprint written through §12; Lean through §4 plus the constructive half and the uniqueness
clause of the main theorem. See `README.md` for the node-level state and what is next. The
working text is `draft/hemigroup-causal-scale-space-kernels.md` (15 sections, Theorems 3′/4′/5′);
the blueprint is written *from* it.

**Two vocabularies, one class.** The paper argues in `BF₀` (derivative signs, Def. 2.2); the Lean
development argues in `LE` (the Lévy representation, Def. 2.7) and never defines complete
monotonicity at all — see `blueprint/DESIGN-formalization-strategy.md`. Prop. 2.3(3), ledger A3,
is the bridge. **A node whose conclusion is stated only in `BF₀` cannot carry a `\lean` tag**, so
when transcribing or revising a statement that concludes in `BF₀`, give the `\LE` reading
alongside it. Do that before the Lean is written, not after.
