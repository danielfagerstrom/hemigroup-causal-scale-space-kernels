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

**Written through §12; formalised through §9 and chapter 11's entry point, plus all three halves of the main theorem.**

The blueprint carries all of §§2–12 — 69 statement nodes — and `AXIOMS.md` has 18 ledger
entries, each with a page anchor. The Lean development is ~8,500 lines, `sorry`-free, and rests
on Lean core plus **two** axioms, which do not mix:

* **A17**, the existence half of the subordinator correspondence — what the *constructive*
  direction needs. Phrased so it can be demoted to a lemma without touching a downstream
  statement, the day the compound-Poisson construction is carried out.
* **A18**, self-decomposability in the direction (1) ⇒ (3) — what the *analysis* direction needs,
  and nothing else does. Taken as a reviewed decision on 2026-08-10, anchored on
  Schilling–Song–Vondraček Prop. 5.17, p. 57, and expected to be permanent: its hard leg needs
  differentiability of Bernstein functions, which is the derivative-sign vocabulary this
  development excludes by design.

CI checks both with `#print axioms` against `blueprint/trust-boundary.txt` on every push, per
declaration — so the article's claim that the analysis direction crosses the boundary where the
constructive one does not is machine-checked rather than asserted.

Thirty-two nodes carry `\lean{...}\leanok`:

| Chapter | Proved in Lean |
|---|---|
| 2 Preliminaries | `def:levy-exponent`, `lem:vanishing`, `prop:laplace-uniqueness-causal`, `prop:laplace-uniqueness-sigma-finite`, `lem:laplace-local-finiteness`, `prop:laplace-continuity-causal`, `lem:transform-tightness` |
| 3 Axioms | `def:cascade-family` — the structure, checked against a model |
| 4 Convolution representation | `lem:convolution-representation`, `lem:transform-continuity` — chapter complete |
| 5 The cascade | `lem:additivity`, `thm:increments-bernstein`, `cor:strict-monotonicity` — chapter complete |
| 6 Scale covariance | `lem:covariance-laplace`, `lem:action-rigidity`, `prop:canonical-gauge` — chapter complete |
| 7 Main theorem | `lem:selfdecomposable-increment`, `thm:main-construction` (⇐), `thm:main-analysis` (⇒), `prop:main-uniqueness` — all three halves |
| 8 Examples and moments | `prop:admissibility-criterion`, `lem:criterion-converse`, `prop:stable-family`, `prop:gamma-family` |
| 9 Memory kernels | `lem:memory-kernel`, `lem:memory-kernel-transform`, `thm:sonine-conservation`, `lem:potential-kernel`, `prop:sonine-pair-exists` — the chapter's `[T]` line, complete |
| 11 The signaling form | `lem:mellin-data` — Theorem 4$'$'s entry point: the Mellin identity and its bound; `lem:inversion-symbol` — the symbol `B`, analytic and meromorphic on the strip; `lem:symbol-rigidity` — the eigenfunction relation pins `B` |

The two `[A]` nodes of chapter 2 that the formalisation was expected to lean on — Feller's
continuity theorem (A5) and his uniqueness theorem (A6) — turned out not to be needed: the
restricted cases the article actually uses are proved here, so neither name appears in
`trust-boundary.txt`. They keep their `[A]` tags because that is the *paper's* stance; the
`[T]` nodes beneath them record what is machine-checked. The same has now happened to A4
(closure of BF under pointwise limits), which chapter 5's argument spends and the Lean proof of
`thm:increments-bernstein` does not: the representation comes straight off the weak limit, so
that proof reduces to Lean core.

The next work, in order. `blueprint/PLAN-chapters-8-12.md` carries the reasoning; the
distinction that matters is between a **queue** and a **dependency**, because only the first is
schedulable:

1. **Chapter 11, towards Theorem 4$'$** — the formulation the article exists for, and the most
   reachable unformalised part of it. `lem:mellin-data`, `lem:inversion-symbol` and
   `lem:symbol-rigidity` are done. What is left of the chapter now runs through
   `def:inversion-operator`, so it waits on A12 with `lem:mellin-vertical` — which moves
   chapter 11 from the queue to the dependency list below.
2. **Chapter 9 is closed to what its ledger allows.** Route B is done: the potential kernel is
   *constructed* as the subordinator's potential measure rather than represented through
   Bernstein–Widder, so the trust boundary stays at two entries and A1 stays off the critical
   path — checked by `#print axioms`, not asserted. What is left in the chapter is `[A]`
   (`prop:pair-regularity` on A9, `prop:volterra-density` on A10) or distributional
   (`prop:scale-evolution`, `cor:exact-inversion`), which Mathlib cannot yet state.
3. **Blocked on upstream Mathlib, not queued.** `lem:mellin-vertical` (11.13) needs a decay
   estimate for `|Γ(c+iτ)|` along a vertical line, which Mathlib does not carry in any form — and
   that clause is what would retire ledger A12, on which the rest of chapter 11 now rests.
   Chapter 10 needs C₀-semigroup and closed-operator theory; chapter 12 needs Bessel `K`. None of
   the three is a scheduling decision.

## Relation to `scale-space-foundations`

A **sibling deliverable, not a chapter.** Both derive covariant time-causal kernel families
that generalize the 2005 stable kernels, but by a different axiom relaxation. Per the hub's
convention, neither article refers to the other by section number — there is more than one
deliverable, and a page that says "the article" cannot say which it means.

## Commands

```bash
scripts/build-blueprint.sh    # all four views, in order (~25s) — use at a round boundary
scripts/build-blueprint.sh --quick   # skip the web build (~13s) — the inner loop
scripts/build-blueprint.sh --serve   # then serve the dependency graph on :8000

linkage check                 # every blueprint / Lean / ledger / paper edge
linkage manifest              # project blueprint-manifest-hcs.json for the hub
linkage demand                # unproved nodes the hub's claims rest on
cd Formalization && lake build
```

Activate the post-commit hook once per clone — it re-emits `.manifest-preview.json` after
any commit touching `blueprint/`, `Formalization/` or `scripts/`:

```bash
git config core.hooksPath .githooks
```

### The three views of the blueprint

The same source renders three ways, and only the first two are built by CI:

| View | Built by | Published at | Shows |
|---|---|---|---|
| `blueprint/src/print.pdf` | `latexmk`; CI via Tectonic | `/blueprint.pdf` | statements and proofs as typeset mathematics |
| `blueprint/web/` | `plastex`; CI via the `web` job | `/blueprint/` | the same, plus the **dependency graph** and `[T]`/`[A]` tags |
| `.manifest-preview.json` | `linkage manifest` | — (the hub's copy is CI-written) | what the hub transcludes, pandoc-rendered |

The web view is the one to look at while transcribing — it is the only one that shows the
`\uses` graph. It is deployed with the PDFs to this article's gated Cloudflare Pages project
(`hcs-docs`), so the graph is a link one can send; `blueprint/web/` itself stays gitignored,
because it is a build product. `scripts/build-blueprint.sh` keeps the three in step locally,
and the shared `docs.yml` does the same in CI.

The framework lives in [`article-kit`](https://github.com/danielfagerstrom/article-kit);
`linkage.toml` binds this repo to it. CI needs an `ARTICLE_KIT_TOKEN` secret with
Contents:read on `article-kit` and `scale-space-lean` while both are private.
