# hemigroup-causal-scale-space-kernels

**Time-Causal Scale Space from Hemigroup Axioms: Characterization of the Kernels.**

Replaces the one-parameter **semigroup** cascade `Φ_τ Φ_τ' = Φ_{τ+τ'}` with a two-parameter
**hemigroup** `Φ_{y,z} Φ_{x,y} = Φ_{x,z}`, keeping full continuous scale covariance, and
characterizes the admissible kernels as `L⁻¹[e^{-F(xs)}]` with `F` a Bernstein function of
nonincreasing Lévy density.

This is a satellite of the research constellation (slug `hcs`). It holds the artifacts; the
positioning and literature work live in the wiki hub's outline page.

| Directory | What |
|---|---|
| `draft/` | the working text, 15 sections — the raw material the blueprint is written from |
| `blueprint/` | the shared spec (LaTeX): each statement tagged `[T]` proved-target or `[A]` analytic interface, with `AXIOMS.md` as the trust boundary |
| `Formalization/` | Lean 4 (`lake` + Mathlib `v4.31.0`), requiring the shared `ScaleSpaceCore` |
| `paper/` | the monograph; its theorem statements are shared with the blueprint so they cannot drift |
| `scripts/`, `figures/` | the figure generator and its output |

## Status

**Scaffolded, not yet written.** The blueprint has its chapter structure but no statement
nodes, `AXIOMS.md` has no entries, and nothing is formalised. `linkage check` passes
trivially — zero nodes is consistent, not complete.

The next work, in order:

1. **Sources.** Resolve citekeys through the librarian for the Bernstein-function spine
   (Schilling–Song–Vondraček; Feller Vol. 2 §XIII). Both are already in the library.
2. **Ledger.** Write the `AXIOMS.md` entries for what will be taken on trust, each with a
   page anchor. Note the overlap with `scale-space-foundations` A5 — same Bernstein theorem,
   so the anchors should agree.
3. **Blueprint nodes.** Transcribe the draft's numbered statements (Def. 2.1 → Thm 7.3 →
   Theorems 3′/4′/5′) as labelled nodes with `\statusT`/`\statusA`. The blueprint is the text
   of record: statements *and* proofs are written as publication-quality mathematics, not
   pointers.
4. **Lean.** `\lean{...}` tags follow the blueprint, `\leanok` once proved.

## Relation to `scale-space-foundations`

A **sibling deliverable, not a chapter.** Both derive covariant time-causal kernel families
that generalize the 2005 stable kernels, but by a different axiom relaxation. Per the hub's
convention, neither article refers to the other by section number — there is more than one
deliverable, and a page that says "the article" cannot say which it means.

## Commands

```bash
linkage check                 # every blueprint / Lean / ledger / paper edge
linkage manifest              # project blueprint-manifest-hcs.json for the hub
linkage demand                # unproved nodes the hub's claims rest on
cd Formalization && lake build
cd blueprint/src && latexmk   # blueprint PDF
```

The framework lives in [`article-kit`](https://github.com/danielfagerstrom/article-kit);
`linkage.toml` binds this repo to it. CI needs an `ARTICLE_KIT_TOKEN` secret with
Contents:read on `article-kit` and `scale-space-lean` while both are private.
