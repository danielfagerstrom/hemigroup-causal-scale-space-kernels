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

**Written through §12; formalised through §9, chapter 11 entire, and chapter 12's classification
step, plus all three halves of the main theorem.**

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

Fifty-eight nodes carry `\lean{...}\leanok`:

| Chapter | Proved in Lean |
|---|---|
| 2 Preliminaries | `def:levy-exponent`, `lem:vanishing`, `prop:laplace-uniqueness-causal`, `prop:laplace-uniqueness-sigma-finite`, `lem:laplace-local-finiteness`, `prop:laplace-continuity-causal`, `lem:transform-tightness` |
| 3 Axioms | `def:cascade-family` — the structure, checked against a model |
| 4 Convolution representation | `lem:convolution-representation`, `lem:transform-continuity` — chapter complete |
| 5 The cascade | `lem:additivity`, `thm:increments-bernstein`, `cor:strict-monotonicity` — chapter complete |
| 6 Scale covariance | `lem:covariance-laplace`, `lem:action-rigidity`, `prop:canonical-gauge` — chapter complete |
| 7 Main theorem | `lem:selfdecomposable-increment`, `thm:main-construction` (⇐), `thm:main-analysis` (⇒), `prop:main-uniqueness` — all three halves; and `lem:admissible-cone`, `lem:dickman-superposition` — the two clauses of `prop:extreme-rays` that need neither uniqueness of the Lévy–Khintchine triple nor a Choquet argument, so that the cone and the `Ein` superposition are machine-checked and only the bijection and the extreme rays are not; and `cor:semigroup-case` — the one-parameter case, recovering the 2005 stable kernels `F(s) = s^α`, `0 < α ≤ 1`, together with the pure delay at `α = 1` |
| 8 Examples and moments | `prop:admissibility-criterion`, `lem:criterion-converse`, `prop:stable-family`, `prop:gamma-family`, `prop:moments` — the mean delay `E T_x = xF'(0+)` in `[0,∞]`, with no finiteness hypothesis on either side: monotone convergence twice and a squeeze, in place of the differentiation at the origin the blueprint's proof performs |
| 9 Memory kernels | `lem:memory-kernel`, `lem:memory-kernel-transform`, `thm:sonine-conservation`, `lem:potential-kernel`, `prop:sonine-pair-exists` — the chapter's `[T]` line, complete |
| 10 The scale-Cauchy problem | `lem:delay-core` — the core `𝒟`, dense in `X₀` and invariant under the delay semigroup and under every `Φ`, with the `L¹` difference quotient and the two-sided delay estimate; and `def:phillips-generator` — the per-scale generator `φ_x(∂_t)f = b₀f' + ∫(f - T_rf)ν_x(dr)`, an `X₀`-valued Bochner integral that needed no theory the development did not have. `lem:generator-properties` is stated in five clauses with four proved — (1) absolute convergence and the two-sided bound, (2) the symbol `φ_x(s) = sF'(xs)`, (3) commutation with every `Φ`, (4) continuity in the scale — leaving only the memory-kernel form |
| 11 The signaling form | `lem:mellin-data`, `lem:mellin-vertical`, `lem:inversion-symbol`, `lem:symbol-rigidity`, `def:inversion-operator`, `lem:inversion-operator-action`, `lem:profile-eigenfunction`, `lem:symbol-uniqueness`, `lem:delayed-average-mellin` — Theorem 4$'$'s Mellin data, the symbol `B`, the inversion operator, its eigenfunction relation `A[H(s·)] = s·H(s·)` (Theorem 4$'$(1)), the uniqueness that earns the definite article in *the* inversion (Theorem 4$'$(3)), `lem:signaling-mellin-form`, `lem:fractional-integral-derivative`, `lem:memory-fractional-integrals`, `thm:signaling-form` — Theorem 4$'$'s Mellin data, the symbol `B`, the inversion operator, its eigenfunction relation (Theorem 4$'$(1)), the uniqueness that earns the definite article in *the* inversion (Theorem 4$'$(3)), and Theorem 4$'$(2)'s Mellin form up to its derivative clause |
| 12 Locality | `lem:log-convexity`, `def:locality-pmp`, `lem:local-polynomial-symbol`, `lem:symbol-vanishes-at-origin`, `lem:moment-recursion-quotient`, `lem:pmp-verification`, `lem:local-moment-classification`, `lem:gamma-recursion-uniqueness` — the chapter's classification step, as an equivalence: `A` is local of order `n` iff its symbol is the corresponding polynomial, read off the zeros of `H̃`; the moment recursion `m(z+1) = Q(z)m(z)` on the range that needs no A13; the maximum principle verified where `thm:locality` exhibits its operators; ledger **A15** (Krull–Webster) discharged in the order-two case it is applied to, from Mathlib's Bohr–Mollerup. What is left in the chapter is `[A]`: A13 (`z_* = ∞`), A14 (the *order bound* — the opposite use of the maximum principle), A16 |

The two `[A]` nodes of chapter 2 that the formalisation was expected to lean on — Feller's
continuity theorem (A5) and his uniqueness theorem (A6) — turned out not to be needed: the
restricted cases the article actually uses are proved here, so neither name appears in
`trust-boundary.txt`. They keep their `[A]` tags because that is the *paper's* stance; the
`[T]` nodes beneath them record what is machine-checked. The same has now happened to A4
(closure of BF under pointwise limits), which chapter 5's argument spends and the Lean proof of
`thm:increments-bernstein` does not: the representation comes straight off the weak limit, so
that proof reduces to Lean core.

Where the work stands. `blueprint/PLAN-chapters-8-12.md` carries the reasoning; the
distinction that matters is between a **queue** and a **dependency**, because only the first is
schedulable. What is schedulable today is the row `PLAN` calls *available, nothing depends on
them* — `prop:stable-moments`, `prop:gamma-kernels`, `prop:volterra`,
`lem:potential-kernel-scaling`, and chapter 10's `lem:generator-properties`, four of whose five
clauses are proved. Everything else:

0. **`prop:moments` (8.4) is done.** The mean rate `F'(0+) = b₀ + ∫₀^∞ k` is `[0,∞]`-valued — the proposition's second
   clause is about when it is infinite — so `meanRate_ne_top_iff` carries no finiteness
   hypothesis, and the influence curve's linearity is `lintegral_id_kernel_zero`, which does
   **not** depend on the mean-delay identity: `μ_{0,x}` is the law of `xT₁`, so every moment
   scales by a change of variables. The identity `E T₁ = F'(0+)` itself needs no differentiation
   and no Tauberian theorem, the difference quotient `(1-e^{-st})/s` being *monotone* in `s`; what
   the `[0,∞]` reading buys is that the infinite case — the one the second clause exists to
   describe — comes out of the same argument rather than being excluded from it.

0. **`prop:extreme-rays` is split and half of it is done.** The node asserted four things at four
   prices and reported the maximum; the cone and the `Ein` superposition are now
   `lem:admissible-cone` and `lem:dickman-superposition`, both Lean core. What 7.7 keeps is
   injectivity of `(b₀,ρ) ↦ F` — ledger A3 as its proof spends it, though the annotation now
   records that `F'(s) = b₀ + ∫e^{-st}k(t)dt` plus Laplace injectivity for locally finite measures
   would reach it with no statement about `BF` at all — and the extreme rays, which need a Choquet
   argument.

1. **`lem:delay-core` (10.1) is done**, and with it everything in chapter 10 that does not need
   C₀-semigroup theory. The setting is built in `Formalization/Hemigroup/DelayCore.lean`: `X₀` as
   a predicate on `X = L¹(ℝ)`, the delay semigroup as `transL1`, and the core `𝒟` as a predicate
   on genuine functions defined by the primitive `f = ∫₀^· f'` — absolute continuity is recovered
   as a consequence, the converse being the Lebesgue fundamental theorem, which Mathlib lacks.
   That `𝒟` supplies exactly the six hypotheses `thm:signaling-form` takes about its signal —
   chapter 11 having been written before `𝒟` had a definition — is
   `memCore_iff_signaling_hypotheses`, an equivalence and not a one-way check. Lean core
   throughout. Nothing depended on the lemma, so it discharges `\uses` edges rather than
   unblocking anything. **Chapter 11 is complete,
   Theorem 4$'$ included** — all six conjuncts of `thm:signaling-form` are machine-checked and
   assembled into one declaration, and none of the chapter spends ledger A12, although three of
   its nodes had been recorded as waiting on it.
2. **Chapter 9 is closed to what its ledger allows.** Route B is done: the potential kernel is
   *constructed* as the subordinator's potential measure rather than represented through
   Bernstein–Widder, so the trust boundary stays at two entries and A1 stays off the critical
   path — checked by `#print axioms`, not asserted. What is left in the chapter is `[A]`
   (`prop:pair-regularity` on A9, `prop:volterra-density` on A10) or distributional
   (`prop:scale-evolution`, `cor:exact-inversion`), which Mathlib cannot yet state.
3. **Blocked on upstream Mathlib, not queued.** Chapter 10's `thm:scale-cauchy` and
   `prop:fixed-scale-semigroup` need C₀-semigroup and closed-operator theory — but only those two.
   `def:phillips-generator` and `lem:generator-properties` were re-checked on 2026-08-14 against
   the setting `lem:delay-core` built; neither mentions a generator's domain, a resolvent, or a
   generation theorem, and 10.2 has since been *defined* and 10.3 stated. (`thm:scale-cauchy` is
   blocked through `prop:scale-evolution` in any case, so the C₀ gap is not the binding one there
   either.) Chapter 12 needs Bessel `K`; `prop:scale-evolution` and `cor:exact-inversion` need a
   locally integrable function read as a distribution and a distribution convolved with a measure,
   neither of which `Analysis/Distribution/` yet has. None of the three is a scheduling decision,
   and all are worth re-checking on each Mathlib bump.

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
