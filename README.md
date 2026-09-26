# Time-Causal Scale Space from Hemigroup Axioms

**Characterization of the Kernels** — a monograph, with a machine-checked core.

Scale-space theory asks which families of smoothing operators an uncommitted observer may
use to measure a signal at all scales at once. For *temporal* signals — where measurement
must be causal and the observer carries its past in its own state — this article replaces
the classical one-parameter **semigroup** cascade `Φ_τ Φ_τ' = Φ_{τ+τ'}` with the weaker
two-parameter **hemigroup**

```
Φ_{y,z} Φ_{x,y} = Φ_{x,z},        0 ≤ x ≤ y ≤ z,
```

keeps full continuous scale covariance, and characterizes the admissible kernel families
completely: they are `L⁻¹[e^{-F(xs)}]` with `F` the Laplace exponent of a
self-decomposable law — a Bernstein function with nonincreasing Lévy density — so the
kernels are the marginal laws of self-similar additive (Sato) subordinators. The enlarged
class contains members with all moments finite (foremost the Gamma family, implemented
exactly by cascades of first-order filters), and the theory is developed through the
memory line: a well-posed signaling form, a locality theorem, non-creation settled in
both directions, and the temporal N-jet.

**Read the paper**: the published release is at
[research.danielfagerstrom.com](https://research.danielfagerstrom.com/papers/hemigroup-time-causal-kernels/) —
[paper.pdf](https://research.danielfagerstrom.com/papers/hemigroup-time-causal-kernels/paper.pdf) ·
[blueprint.pdf](https://research.danielfagerstrom.com/papers/hemigroup-time-causal-kernels/blueprint.pdf) · the
[web blueprint](https://research.danielfagerstrom.com/papers/hemigroup-time-causal-kernels/blueprint/) with its
[dependency graph](https://research.danielfagerstrom.com/papers/hemigroup-time-causal-kernels/blueprint/dep_graph_document.html),
every node colored by verification status. That URL names the `v1.0.0` release and is
permanent; `.../v1.0.0/` addresses it explicitly, and the unversioned path follows the
latest release. The same CI-built PDFs are on the
[`artifacts`](../../tree/artifacts) branch
([paper.pdf](../../raw/artifacts/paper.pdf) ·
[blueprint.pdf](../../raw/artifacts/blueprint.pdf)), and `paper/main.pdf` builds from
`paper/`. Those track `main`; the public site serves the release, and the frozen, citable
version is the archived release below.

## What is in this repository

| Directory | What |
|---|---|
| `paper/` | the monograph (LaTeX); its theorem statements are shared with the blueprint so the two cannot drift |
| `blueprint/` | the shared specification: every statement tagged `[T]` (proved target) or `[A]` (cited analytic interface), with `AXIOMS.md` as the page-anchored trust ledger, `REVIEW-fidelity.md` as the fidelity review's findings ledger, and a rendered dependency graph |
| `Formalization/` | the Lean 4 development (`lake` + Mathlib, pinned), building on the shared library [`scale-space-lean`](https://github.com/danielfagerstrom/scale-space-lean) |
| `draft/` | the working text the article was written from — kept as the starting point of record |
| `scripts/`, `figures/` | the figure and experiment generators and their committed output; every number quoted in the paper's numerical example is produced by these scripts |
| `records/` | the development's process records — the plans, the editorial decisions and the exposition notes — kept as provenance |
| `notes/` | the two external reviews (`notes/reviews/`) and the plan responding to them, and the handoff for the next development session |

**How to read it.** The paper is the deliverable. The blueprint holds the same statements
as a dependency-graphed specification, each node marked by verification status — `[T]`
nodes are proved (on paper, and where tagged `\leanok`, in Lean), `[A]` nodes are cited
analytic interfaces, every one grounded in `blueprint/AXIOMS.md` with a page reference
checked against the source. The Lean tree mirrors the blueprint's `\lean{}` tags. The
blueprint's chapters render in the article's order, so the two read side by side; the
part *filenames* (`11-signaling.tex` renders as Chapter 9) and the Lean tree's file names
keep the draft's section numbers as provenance, with every node's `% draft:` comment as
the bridge.

## Verifying the machine-checked results

The toolchain is pinned in-tree — Lean 4 `v4.31.0`, Mathlib `v4.31.0`, `ScaleSpaceCore`
at tag `v0.1.1` — so verification is reproducible with two commands:

```bash
cd Formalization
lake build                        # builds the sorry-free library
lake env lean CIAxiomGuard.lean   # prints the axiom usage of every named declaration
                                  # and exits nonzero on any drift from the trust boundary
```

The library `Formalization/Hemigroup` is `sorry`-free and rests on Lean core plus **one**
axiom (`blueprint/trust-boundary.txt`):

* **A18**, self-decomposability in the direction (1) ⇒ (3) — what the *analysis* direction
  needs, and nothing else does. A reviewed decision, anchored on Schilling–Song–Vondraček
  Prop. 5.17, p. 57, and expected to be permanent: its hard leg needs differentiability of
  Bernstein functions, which is the derivative-sign vocabulary this development excludes
  by design.

The released `v1.0.0` also rested on **A17**, the existence half of the subordinator
correspondence, which the *constructive* direction needs. It has since been proved (the
compound-Poisson construction with Mathlib's Prokhorov theorem,
`Formalization/Hemigroup/CompoundPoisson.lean`) with its statement unchanged, so the
constructive direction and the uniqueness clause now reduce to Lean core.

CI checks this with `#print axioms` per declaration on every push — so the article's claim
that the analysis direction crosses the boundary where the constructive one does not is
machine-checked rather than asserted.

## State

Published as `v1.0.0`. **Both headline theorems are machine-checked in full**: the
characterization (Theorem 7.3: construction, analysis and uniqueness) and the signaling
form (Theorem 9.17). The blueprint has 106 statement nodes, 71 of them `\leanok`; all 89
statements the paper shares with it are verbatim; `AXIOMS.md` has 21 ledger entries, each
with a page anchor; the trust base is Lean core plus A18 (A17, in the trust base of `v1.0.0`,
is proved on `main` since; no `v1.1` carries it yet). `linkage check` reports
two advisories, both deliberate: `lem:selfdecomposable-derivative` is A18 itself, and
`lem:selfdecomposable-exponents` is a collation over it. The fidelity review
(`blueprint/REVIEW-fidelity.md`, verdict at its head) found that the Lean proves what the
article states.

What is not formalized, and why, is inventoried in the paper's §1.1: the scale-Cauchy
problem waits on distribution theory absent from Mathlib; `Formalization/Skeleton/` holds no
`sorry`-marked target type any more (§1.1's inventory, like its A17 sentence, is rewritten by
whichever pass prepares a `v1.1`: since `v1.0.0`, `lem:mode-rigidity`,
`lem:standing-levy-reading`, all of `lem:zstar-log-growth` and `prop:pair-regularity`(2)'s two
equivalences have been proved, the last on Lean core with the node still `[A]` for its clause
(1)); the
locality chapter's remaining nodes are cited analytic interfaces
(Widder, Courrège, Krull–Webster, Bondesson) plus the Bessel-K special function; and the
implementation and jet chapters are outside the Lean plan by decision. History:
`CHANGELOG.md` and git.

## Relation to `scale-space-foundations`

A **sibling article by the same author, not a chapter of this one.** Both derive
covariant time-causal kernel families that generalize the 2005 stable kernels, but by a
different axiom relaxation; neither refers to the other by section number.

## Development tooling

The blueprint/paper/Lean consistency checks (`linkage check`), the manifest projection,
and the shared CI workflows live in the author's `article-kit` framework, which is
private; `linkage.toml` binds this repository to it, and the CI needs an
`ARTICLE_KIT_TOKEN` secret, so forks' CI will not run as-is. None of that is needed to
*verify* this repository: the two `lake` commands above are self-contained, and the
LaTeX builds are plain `latexmk`/Tectonic (`paper/main.tex`,
`blueprint/src/print.tex`). Local helpers:

```bash
scripts/build-blueprint.sh           # the blueprint's PDF + web views (needs plastex)
git config core.hooksPath .githooks  # optional post-commit manifest preview
```

## License

Dual-licensed by content — see [`LICENSE.md`](LICENSE.md): prose, mathematics and
figures (`paper/`, `blueprint/`, `draft/`, `figures/`, `notes/`, `records/`) under
**CC BY 4.0**; code (`Formalization/`, `scripts/`) under **Apache 2.0**.

## Citing

The v1.0.0 release (September 2, 2026) is archived on Zenodo. To cite the work
independently of version, use the concept DOI
[10.5281/zenodo.22259186](https://doi.org/10.5281/zenodo.22259186), which always
resolves to the latest version; the citation below pins this release:

```bibtex
@misc{fagerstrom2026hemigroup,
  author  = {Fagerstr{\"o}m, Daniel},
  title   = {Time-Causal Scale Space from Hemigroup Axioms:
             Characterization of the Kernels},
  year    = {2026},
  month   = {9},
  doi     = {10.5281/zenodo.22259187},
  version = {v1.0.0},
  url     = {https://github.com/danielfagerstrom/hemigroup-causal-scale-space-kernels}
}
```
