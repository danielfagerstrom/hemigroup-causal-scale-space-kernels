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

**Read the paper**: `paper/main.pdf` builds from `paper/`, and the latest CI-built PDFs
are on the [`artifacts`](../../tree/artifacts) branch
([paper.pdf](../../raw/artifacts/paper.pdf) ·
[blueprint.pdf](../../raw/artifacts/blueprint.pdf)).

## What is in this repository

| Directory | What |
|---|---|
| `paper/` | the monograph (LaTeX); its theorem statements are shared with the blueprint so the two cannot drift |
| `blueprint/` | the shared specification: every statement tagged `[T]` (proved target) or `[A]` (cited analytic interface), with `AXIOMS.md` as the page-anchored trust ledger and a rendered dependency graph |
| `Formalization/` | the Lean 4 development (`lake` + Mathlib, pinned), building on the shared library [`scale-space-lean`](https://github.com/danielfagerstrom/scale-space-lean) |
| `draft/` | the working text the article was written from — kept as the starting point of record |
| `scripts/`, `figures/` | the figure and experiment generators and their committed output; every number quoted in the paper's numerical example is produced by these scripts |
| `notes/` | the development's process records — plans, reviews, and decisions of record — kept as provenance |

**How to read it.** The paper is the deliverable. The blueprint holds the same statements
as a dependency-graphed specification, each node marked by verification status — `[T]`
nodes are proved (on paper, and where tagged `\leanok`, in Lean), `[A]` nodes are cited
analytic interfaces, every one grounded in `blueprint/AXIOMS.md` with a page reference
checked against the source. The Lean tree mirrors the blueprint's `\lean{}` tags. Since
2026-09-01 the blueprint's chapters render in the article's order — the signaling chapter
is Chapter 9 as the signaling section is §9 — so the two read side by side; the part
*filenames* (`11-signaling.tex` renders as Chapter 9) and the Lean tree's file names keep
the draft's section numbers as provenance, with every node's `% draft:` comment as the
bridge.

## Verifying the machine-checked results

The toolchain is pinned in-tree — Lean 4 `v4.31.0`, Mathlib `v4.31.0`, `ScaleSpaceCore`
at tag `v0.1.0` — so verification is reproducible with two commands:

```bash
cd Formalization
lake build                        # builds the sorry-free library
lake env lean CIAxiomGuard.lean   # prints the axiom usage of every named declaration
                                  # and exits nonzero on any drift from the trust boundary
```

The development is ~8,500 lines, `sorry`-free, and rests on Lean core plus **two** axioms
(`blueprint/trust-boundary.txt`), which do not mix:

* **A17**, the existence half of the subordinator correspondence — what the *constructive*
  direction needs. Phrased so it can be demoted to a lemma without touching a downstream
  statement, the day the compound-Poisson construction is carried out.
* **A18**, self-decomposability in the direction (1) ⇒ (3) — what the *analysis* direction
  needs, and nothing else does. Taken as a reviewed decision on 2026-08-10, anchored on
  Schilling–Song–Vondraček Prop. 5.17, p. 57, and expected to be permanent: its hard leg
  needs differentiability of Bernstein functions, which is the derivative-sign vocabulary
  this development excludes by design.

CI checks both with `#print axioms` per declaration on every push — so the article's claim
that the analysis direction crosses the boundary where the constructive one does not is
machine-checked rather than asserted.

## Status

**Both headline theorems are machine-checked in full** — the characterization
(Theorem 7.3: construction, analysis, and uniqueness) and the signaling form
(Theorem 9.17). The paper is written through §13 plus the appendix; the blueprint carries
all of its mathematics — 106 statement nodes — and `AXIOMS.md` has 21 ledger entries,
each with a page anchor. The implementation and N-jet chapters carry statement nodes
without Lean tags, deliberately outside the Lean plan.

**Content-reviewed 2026-08-16…-24** (`notes/PLAN-content-review.md`, decisions in
`notes/DECISIONS.md`): fourteen blind draft reviews were worked section by section — four
global decisions first, then every section, with shared-statement fixes landing
blueprint-side. An external-review response in ten batches followed
(`notes/PLAN-review-response.md`), and the path to publication is
`notes/PLAN-publication.md`.

**Fidelity-reviewed 2026-08-15** (`notes/PLAN-fidelity-review.md`, executed in
`notes/REVIEW-fidelity.md`): every `\leanok` node was audited statement-by-statement
against the article and the blueprint — definitions unfolded to Mathlib primitives,
partial functions' junk values audited, blind restatements from the draft alone,
adversarial-vacuity passes on the headline theorems, the two axioms compared row by row
with image-verified source pages, and `Formalization/Hemigroup/Witnesses.lean` showing
the headline hypotheses jointly satisfiable at named models. Verdict: the Lean proves
what the article states — no proved conjunct is vacuous, junk-valued or weaker than the
article's proof. Eleven statement-tightenings were landed as conjuncts, and two places
where the article's statement outran its proof were corrected in the text of record.

Sixty-seven nodes carry `\lean{...}\leanok`:

| Chapter (draft numbering) | Proved in Lean |
|---|---|
| 2 Preliminaries | `def:levy-exponent`, `lem:vanishing`, `prop:laplace-uniqueness-causal`, `prop:laplace-uniqueness-sigma-finite`, `lem:laplace-local-finiteness`, `prop:laplace-continuity-causal`, `lem:transform-tightness` |
| 3 Axioms | `def:cascade-family` — the structure, checked against a model |
| 4 Convolution representation | `lem:convolution-representation`, `lem:transform-continuity` — chapter complete |
| 5 The cascade | `lem:additivity`, `thm:increments-bernstein`, `cor:strict-monotonicity` — chapter complete |
| 6 Scale covariance | `lem:covariance-laplace`, `lem:action-rigidity`, `prop:canonical-gauge` — chapter complete |
| 7 Main theorem | `lem:selfdecomposable-increment`, `thm:main-construction` (⇐), `thm:main-analysis` (⇒), `prop:main-uniqueness` — all three halves; and `lem:admissible-cone`, `lem:dickman-superposition` — the two clauses of `prop:extreme-rays` that need neither uniqueness of the Lévy–Khintchine triple nor a Choquet argument, so that the cone and the `Ein` superposition are machine-checked and only the bijection and the extreme rays are not; and `cor:semigroup-case` — the one-parameter case, recovering the 2005 stable kernels `F(s) = s^α`, `0 < α ≤ 1`, together with the pure delay at `α = 1` |
| 8 Examples and moments | `prop:admissibility-criterion`, `lem:criterion-converse`, `prop:stable-family`, `prop:gamma-family`, `prop:gamma-kernels` — the Gamma family's kernel and increment transforms and its mean delay `E T_x = γx`; `prop:gamma-density` and `prop:gamma-moments` — its kernel *is* Mathlib's Gamma law of shape `γ` and rate `1/x`, and every moment is finite with `Var T_x = γx²`; Mathlib carries neither the transform nor the moments of its own Gamma law, so both come from one Gamma integral, and the identification is what took this node off ledger A7; `prop:stable-moments` — every moment of the extremal stable delay is infinite, which came off ledger A7 once the mean was proved; `prop:moments` — the mean delay `E T_x = xF'(0+)` in `[0,∞]`, with no finiteness hypothesis on either side: monotone convergence twice and a squeeze, in place of the differentiation at the origin the blueprint's proof performs |
| 9 Memory kernels | `lem:memory-kernel`, `lem:memory-kernel-transform`, `thm:sonine-conservation`, `lem:potential-kernel`, `prop:sonine-pair-exists`, `lem:potential-kernel-scaling` — the potential kernel dilates, `ℓ^{(x)} = x·(ℓ^{(1)}∘(x·)⁻¹)`, stated against the specification so that it is Lean core and reaches no ledger entry at all; `prop:volterra` and `prop:volterra-uniqueness` — the Volterra identity `t μ_x(dt) = (θ_x ∗ μ_x)(dt)` and the fact that it determines `μ_x`; the identity's one new step is that the Laplace transform differentiates under the integral against a *constant* bound, and the uniqueness is the scalar ODE that bound made available |
| 10 The scale-Cauchy problem | `lem:delay-core` — the core `𝒟`, dense in `X₀` and invariant under the delay semigroup and under every `Φ`, with the `L¹` difference quotient and the two-sided delay estimate; and `def:phillips-generator` — the per-scale generator `φ_x(∂_t)f = b₀f' + ∫(f - T_rf)ν_x(dr)`, an `X₀`-valued Bochner integral that needed no theory the development did not have. `lem:generator-properties` — all five clauses, Lean core: absolute convergence with the two-sided bound, the symbol `φ_x(s) = sF'(xs)`, commutation with every `Φ`, continuity in the scale, and agreement with chapter 9's memory-kernel operator. The chapter is now everything but the Cauchy problem |
| 11 The signaling form | `lem:mellin-data`, `lem:mellin-vertical`, `lem:inversion-symbol`, `lem:symbol-rigidity`, `def:inversion-operator`, `lem:inversion-operator-action`, `lem:profile-eigenfunction`, `lem:symbol-uniqueness`, `lem:delayed-average-mellin`, `lem:signaling-mellin-form`, `lem:fractional-integral-derivative`, `lem:memory-fractional-integrals`, `thm:signaling-form` — Theorem 4′'s Mellin data, the symbol `B`, the inversion operator, its eigenfunction relation `A[H(s·)] = s·H(s·)` (Theorem 4′(1)), the uniqueness that earns the definite article in *the* inversion (Theorem 4′(3)), and Theorem 4′(2)'s Mellin form up to its derivative clause; `lem:standing-kernel-readings` — the two readings `def:standing-hypothesis`'s clauses used to assert as unchecked parentheticals, now proved (its siblings `lem:standing-levy-reading` and `lem:zstar-log-growth` are both `\notready`; see `Formalization/Skeleton/Chapter11.lean`). **The chapter has a well-posedness ending**: `def:mellin-solution` names what a solution of the signaling problem *is*; `lem:mode-rigidity` kills the period-one ambiguity the eigenvalue recursion has, under a normalisation the field satisfies for free, and is `\notready` with a sorry-marked target type (priced, not attempted: the missing piece is a periodic-extension construction Mathlib does not carry); `cor:signaling-wellposed` assembles existence and *solution*-uniqueness; `cor:signaling-classical` upgrades the Mellin-level identity to a genuine pointwise PDE under a decay hypothesis satisfied by the Gamma, stable and Bessel-K families and correctly failed by the pure delay; and `cor:signaling-hadamard` assembles Hadamard's three demands plus stability under pointwise perturbation of the exponent, so that the chapter's well-posedness claim is a stated and proved corollary rather than arc prose. None of the five carry a `\leanok` proof |
| 12 Locality | `lem:log-convexity`, `def:locality-pmp`, `lem:local-polynomial-symbol`, `lem:symbol-vanishes-at-origin`, `lem:moment-recursion-quotient`, `lem:pmp-verification`, `lem:local-moment-classification`, `lem:gamma-recursion-uniqueness` — the chapter's classification step, as an equivalence: `A` is local of order `n` iff its symbol is the corresponding polynomial, read off the zeros of `H̃`; the moment recursion `m(z+1) = Q(z)m(z)` on the range that needs no A13; the maximum principle verified where `thm:locality` exhibits its operators; ledger **A15** (Krull–Webster) discharged in the order-two case it is applied to, from Mathlib's Bohr–Mollerup. What is left in the chapter is `[A]`: A13 (`z_* = ∞`), A14 (the *order bound* — the opposite use of the maximum principle), A16 |

The two `[A]` nodes of chapter 2 that the formalisation was expected to lean on — Feller's
continuity theorem (A5) and his uniqueness theorem (A6) — turned out not to be needed: the
restricted cases the article actually uses are proved here, so neither name appears in
`trust-boundary.txt`. They keep their `[A]` tags because that is the *paper's* stance; the
`[T]` nodes beneath them record what is machine-checked. The same has happened to A4
(closure of BF under pointwise limits), which chapter 5's argument spends and the Lean
proof of `thm:increments-bernstein` does not: the representation comes straight off the
weak limit, so that proof reduces to Lean core.

What is *not* formalized, and why, is inventoried in the paper's §1.1 and reasoned
through in `notes/PLAN-chapters-8-12.md`: the scale-Cauchy problem waits on distribution
theory absent from Mathlib, chapter 12's remaining nodes are cited analytic interfaces
(Widder, Courrège, Krull–Webster, Bondesson) plus the Bessel-K special function, and the
implementation/jet chapters are outside the Lean plan by decision.

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
figures (`paper/`, `blueprint/`, `draft/`, `figures/`, `notes/`) under
**CC BY 4.0**; code (`Formalization/`, `scripts/`) under **Apache 2.0**.

## Citing

Until the archival release (a DOI is minted with the release tag), cite the repository:

```bibtex
@misc{fagerstrom2026hemigroup,
  author = {Fagerstr{\"o}m, Daniel},
  title  = {Time-Causal Scale Space from Hemigroup Axioms:
            Characterization of the Kernels},
  year   = {2026},
  url    = {https://github.com/danielfagerstrom/hemigroup-causal-scale-space-kernels}
}
```
