# hemigroup-causal-scale-space-kernels — Claude Code context

> **Note for public readers.** This file is working context for the author's AI-assisted
> development sessions, kept in the repository as provenance and so that development can
> continue. It speaks the internal dialect of the author's research constellation and references
> private infrastructure — a wiki hub (`$WIKI_VAULT`), a source librarian (`$LIBRARY_DIR`), and the
> `article-kit` framework — that is not part of this repository. Nothing in the paper, the
> blueprint, or the Lean development depends on any of it; the public verification route is the
> two `lake` commands in `README.md`.

This file holds **this article's standing rules and nothing else**, in the present tense. The
process every article follows and the rules every article shares load from
`.claude/rules/article-kit/` (framework-owned; `../article-kit/docs/PROCESS.md` is the map). The
state is `README.md`; what the next session needs is `notes/HANDOFF.md`; history is `CHANGELOG.md`
and git; decisions are `adr/`; plans, review archives and process accounts are `records/`. Nothing
dated, no status, no record of what a session did goes here.

**What this is.** Paper I of the hemigroup programme (slug `hcs`): *Time-Causal Scale Space from
Hemigroup Axioms: Characterization of the Kernels*, a monograph with a machine-checked core, both
driven by one blueprint. It is published (`v1.0.0`, concept DOI 10.5281/zenodo.22259186); one
module. Its spatial counterpart is Paper V (`spatial-hemigroup-scale-space`), its SSVM extraction
`hemigroup-kernels-ssvm`. It is a sibling of `scale-space-foundations`, not a chapter of it.

## Where this sits

- **Framework**: `article-kit` (the `linkage` CLI, the scaffolding under `blueprint/src/`, the
  reusable CI, the session rules). `linkage.toml` binds this repository to it.
- **Shared Lean**: `scale-space-lean` (`ScaleSpaceCore`), pinned to a tag in
  `Formalization/lakefile.toml`. It carries nothing resting on a cited interface, so importing it
  adds nothing to this article's trust base.
- **Hub**: `$WIKI_VAULT`; thread page `wiki/hemigroup-programme.md`, source page
  `wiki/sources/@fagerstrom2026hemigroup.md`, outline `wiki/outlines/hemigroup-causal-scale-space-kernels.md`.
- **Librarian**: `$LIBRARY_DIR`; `library resolve <citekey> --json`.

## This article's rules

- **Verified core, axiomatized analysis.** Prove the structural content; take the deep analysis
  (Bernstein-function theory, self-decomposability, the Lévy–Khintchine representation) as `[A]`
  interfaces grounded in `blueprint/AXIOMS.md`. `#print axioms` reduces to Lean core plus the two
  names of `blueprint/trust-boundary.txt` (A17, the constructive direction; A18, the analysis
  direction), whose comments say what each carries and what it does not.
- **The findings ledger is `blueprint/REVIEW-fidelity.md`.** A statement change, admission or
  retirement gets the next free row there and a `% CHANGED` marker at the node.
- **Two collation nodes carry bundles, and the halves carry the ledger.**
  `thm:main-characterization` and `thm:signaling-form` each have a bundling declaration
  (`main_characterization`, `signaling_form`). The bundles depend on every ledger entry their parts
  do, so **the per-half `#print axioms` lines in `CIAxiomGuard.lean` are the load-bearing ones**:
  for Theorem 2′ they show `(⇐)` on A17 and `(⇒)` on A18 with neither borrowing the other's. Never
  replace them with the bundle's line.
- **Two vocabularies, one class.** The paper argues in `BF₀` (derivative signs); the Lean
  development argues in `LE` (the Lévy representation) and never defines complete monotonicity
  (`blueprint/DESIGN-formalization-strategy.md`). Ledger A3 is the bridge. **A node whose conclusion
  is stated only in `BF₀` cannot carry a `\lean` tag**: when writing or revising such a statement,
  give the `\LE` reading beside it, before the Lean is written.
- **`Formalization/Skeleton/`** holds the `sorry`-marked target types of `\notready` nodes. CI's
  sorry guard scans `Formalization/Hemigroup` only, so the library stays `sorry`-free and the
  README's claim needs no footnote. A declaration moves into `Hemigroup/` when proved.
- **`linkage check`'s two `[depend]` advisories are deliberate**, not a work queue:
  `lem:selfdecomposable-derivative` is ledger A18 by a review decision, and
  `lem:selfdecomposable-exponents` is a collation over it. Formalising them means formalising A3
  and A4, which the trust boundary declines and which cannot be stated without `CM`. Read the
  node's own annotation before treating any advisory as work.
- **Theorem 4′ (the signaling form) is the point of the article**, the formulation the author
  builds on; weight its chapter above tidiness elsewhere. The scale-Cauchy problem (Theorem 3′) is
  a leaf nothing outside its chapter uses.
- **For a node that cannot be formalized**, check it in detail and make it plausible by landing its
  objects in a known probability class (the self-decomposable laws, the Dickman subordinators),
  with worked instances on the Gamma and stable families, as the 2005 article did.
- **Editorial decisions in force** (rationale in `records/DECISIONS.md`): the pure delay is in the
  class, so kernels are measures and every property failing on the drift ray is stated under
  `k ≢ 0`; hypothesis (H) has one home (`def:standing-hypothesis`) and every summary carries it;
  the canonical gauge `x̃` is the working gauge, and the parabolic gauge is written `ξ`, never `x̃`;
  economy claims are exact or removed, and §1.1 is the one statement of what rests on what. The
  section structure is fixed in `paper/main.tex`'s header.
- **The paper's printed proofs stay classical** (decision D-D, this article's exception to the
  framework's "proof of record follows the Lean route"): where the verified proof takes another
  route, one sentence at the point of claim says so, and the printed proof is not rewritten.
- **The published text names `notes/reviews/` by path**, beside `notes/PLAN-review-response.md`:
  both stay where they are.
- **Commit and push after each completed step** (a proved node, a blueprint split, a ledger
  correction), one step per commit, the full gate first, the message naming the node and what it
  cost and taught. History is linear. A post-commit hook re-emits `.manifest-preview.json`.
- **The Lean language server** (`.mcp.json`, `lean-lsp-mcp` on `Formalization`): a large file such
  as `Skeleton/Chapter11.lean` takes about two minutes to elaborate on the first diagnostics call,
  after which goal queries are instant; `lean_local_search` stays local, the Mathlib search tools
  reach the network.

## Commands

```bash
cd Formalization && lake build && lake env lean CIAxiomGuard.lean   # check the exit code
linkage check && linkage axioms --check
bash scripts/build-blueprint.sh           # --quick for the PDF only; control-character check first
python scripts/check-control-chars.py
cd paper && latexmk -pdf main.tex
```

A paper-only step skips `lake`.
