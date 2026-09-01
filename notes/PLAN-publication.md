# PLAN — path to publication (2026-09-01)

Working plan for taking the monograph from its current state — review response R0–R10
complete, blueprint complete w.r.t. the mathematical material (105 nodes, 21 ledger
entries), all merged through PR #36 — to a published, public state. Drawn up at the
author's request from the assessment discussion of 2026-09-01; the author's adjustments
are folded in and marked.

Conventions, as for the review-response plan: every batch is one PR, validated locally by
the control-char guard and the ref/label/statement-sync checks, full gate in Docs CI.
Statements shared with the blueprint are changed in both documents or not at all. Batches
marked (author) are author-led, with Claude assisting on request; the rest Claude
executes on the author's go.

## Standing decisions (author, 2026-09-01)

- **Draft alignment is retired as a goal.** The blueprint reorders to the *article's*
  order (P2). `draft/` itself is KEPT in the repo — it was the starting point of the
  article work and is load-bearing for provenance (the blueprint's `% draft:` comments
  cite its line numbers).
- **AI-tic cleaning** rides on tooling the author is building in `article-kit`; effort is
  capped ("probably not that much") and P3 is scoped accordingly — a targeted manual pass
  regardless, the tooling as a bonus.
- **The AI usage statement** will be grounded in the author's session/git-log analysis in
  the `ai-archive` repo; the author updates that first, then P4 rewrites
  `paper/ai-statement.tex` from it.
- **Formalization is deferred past publication entirely**, including the one candidate
  worth doing (the mode-rigidity/wellposed arc, which sits on already-`\leanok` ground and
  needs only classical complex analysis available in Mathlib). Recorded under
  post-publication, not gated on.

## Decision points — RESOLVED (author, 2026-09-01)

- **DP1 — Licenses:** CC BY 4.0 for the paper/blueprint prose (figures included);
  code under Apache 2.0. *(Revised 2026-09-01 during P6 review: the original decision
  was MIT, but the author chose to follow the Lean-ecosystem convention — Apache 2.0,
  matching Mathlib — rather than mix code licenses; he is an emeritus ASF member, so
  the fit is natural.)*
  **Flagged consequence:** `scale-space-lean` must go public and be Apache-2.0-licensed before
  or with P7 — `lake build` fetches `ScaleSpaceCore` at tag v0.1.0 from GitHub, so
  §1.1's one-command verification holds for an outside reader only when that repo is
  reachable. `article-kit` stays private for now: the public README advertises only the
  two `lake` commands as reproducible, not `linkage check`.
- **DP2 — Process documents:** keep whatever is helpful or adds provenance; gather the
  process files under `notes/` so they do not clutter the load-bearing parts. Documents
  referring to non-public material get a one-line header note rather than removal where
  they are needed for continued development (CLAUDE.md foremost); removal only where
  they would genuinely confuse. The repo stays in a state where development can
  continue. Git history is rewritten only for secrets or the genuinely embarrassing —
  by default it stays, because the commit-level provenance (session trailers) is what
  the ai-archive analysis rests on. Candidate addition: the two external review
  documents under `notes/reviews/` with model attribution, so the review-response plan
  is readable next to what it answers.
- **DP3 — Channels:** Zenodo first, arXiv later when access is arranged; the
  announcement carries both the repository and the PDF. Mechanics: enable the
  GitHub–Zenodo integration BEFORE minting the release tag (or reserve the DOI) so the
  DOI can be printed in the PDF and cited in the README; cite the concept DOI, which
  survives revisions; add the arXiv ID to README and Zenodo metadata when it lands.
- **DP4 — Second review round:** yes, light, folded into P5's opening: fresh agent
  reviewers on the polished full PDF, scoped to residual overclaims, coherence of the
  reworked claim layer and R8 front matter to fresh eyes, and language — explicitly not
  a re-litigation of the mathematics, which has been through R0–R10.

## Batches

### P1 — the stability corollary                                        [status: DONE 2026-09-01]

Landed as `cor:signaling-hadamard` ("the signaling problem is well posed"), a shared
statement node after rem:classical-families in §9 / chapter 11 (`\statusT`, no lean tag;
node count 105 → 106, ledger untouched). Clauses: existence and uniqueness restated from
cor:signaling-wellposed; the data contraction (sup over scales, and along the evolution);
exponent stability — F_n → F pointwise gives weak kernel convergence by
prop:laplace-continuity, upgraded to L¹ field convergence at every scale by an inline
Scheffé argument (the one estimate that is not a restatement). rem:signaling-stability
recast as the boundary-of-claim remark (label kept): what is not claimed is a topology
adapted to A — with the honest example F + s/n, whose strips do not converge. "Well posed"
restored in the §9 arc, §1, §1.1 ("well-posedness arc" returns), and the abstract.

First, because it touches claim language that P3 would otherwise polish twice.
- New corollary after rem:signaling-stability (or absorbing it): Hadamard's three demands
  assembled with one clause each — existence and uniqueness from cor:signaling-wellposed;
  continuous dependence on the data as the L1 contraction, sup over scales; stability
  under exponent perturbation as prop:laplace-continuity read on the solutions (F_n -> F
  pointwise gives weak convergence of the fields at every scale). No new mathematics: the
  proof is assembly.
- With Hadamard satisfied clause by clause, the phrase "well posed" is honestly restored:
  the corollary carries it in its title, and the arc prose, §1 and the abstract are
  re-swept (this partially unwinds R4's renaming — deliberately: R4 renamed because the
  claim outran the proofs, and this batch makes the proofs reach the claim).
- rem:signaling-stability is recast or absorbed: its "what is not claimed" clause
  (topology adapted to A, operator perturbation) survives verbatim as the honest boundary.
- Blueprint: the corollary is a shared statement node in the signaling chapter (statusT,
  no lean tag); ledger untouched.
- Estimate: half a day.

### P2 — blueprint reorder to the article's order                       [status: DONE 2026-09-01]

Landed: content.tex reordered to the article's order (axioms 2, preliminaries 3, ...,
signaling 9, locality 10, implementation 11, jet 12; memory-kernels + scale-Cauchy as one
Appendix A via `\appendix`, matching the paper's single appendix). content.tex's
numbering-rationale header rewritten: draft alignment retired, `% draft:` comments are the
bridge, part filenames keep their draft numbers as provenance. Every part's header now
records what it renders as; 28 rendered chapter-number references in prose and annotations
updated to the new numbers ("the appendix" for the moved pair), each verified a unique
match; historical comments ("Numbered 11.25") left as-is under the header note. Three
blueprint-chapter references in AXIOMS.md switched to chapter names; README carries the
convention note. Labels and \uses edges untouched (the graph is label-based).

- content.tex: reorder the \input lines to the paper's order — measurement/axioms,
  preliminaries, representation, cascade, covariance, characterization, examples,
  signaling, locality, implementation, jet, then the appendix pair (memory kernels,
  scale-Cauchy) last. Chapters renumber to match the paper's sections; the appendix pair
  is numbered/labelled as the appendix material it is in the article.
- Rewrite content.tex's numbering-rationale header: the draft-alignment argument is
  retired (author decision above); the % draft: provenance comments in the parts remain
  the bridge to the draft, which stays in the repo as the starting point of record.
- Sweep the historical comments that cite blueprint numbers ("Numbered 11.25", "part 1")
  and annotate where the number no longer matches the rendered one; labels and \uses
  edges are untouched (the graph is label-based, so this batch is presentation only).
- Check nothing structural assumes chapter order (linkage manifest is label-based; LaTeX
  \ref works forward; plasTeX does not care) — one careful CI run is the gate.
- Estimate: half a day.

### P3 — language polish: the tic pass                                  [status: DONE 2026-09-01]

Executed restrained, per the author's instruction ("don't overdo it; don't imitate my
style"): a survey of the named target list found the paper largely clean already — earlier
batches had removed most instances — so the pass is eight surgical edits, not a rewrite.
Removed: the two literal named-tic survivors ("deserves stating plainly" in §11, the
"exactly as far as it can be" flourish in §1); the worst em-dash pileup ("--- are --- we
record this without proof here ---" in rem:markov-media, a verbatim-shared remark changed
identically in both copies); two of the eight "What X is Y" frontings (§1.1's "What
survives is exactly", and P1's own connective in §9, which had also reintroduced an "earns
the phrase" flourish R4 removed — both rewritten); two rhetorical "exactly"s in §1; "Three
glosses." given a verb. Kept deliberately: the load-bearing "exactly"s (characterization
claims), the price metaphor (thematic), "Two things follow."/"Four problems remain." (one
each), the §9 "What survives is dilation structure" pivot, and all shared statement
bodies. The author's own long-sentence pass preceded this. Further polish, if any, falls
to P5's read-through.

- Target list, named so the pass is surgical (each fine once, but they repeat):
  "deserves stating plainly"; "worth being exact about"; the "honest form / honest
  reading" family; "not an accident of"; enumeration openers ("Three glosses.", "Two
  things follow."); em-dash triads; the "What survives... what cannot" anaphora;
  "exactly as far as it can be"-style flourishes. Vary or trim, keep the voice — the
  2005-IJCV register the decisions of record ask for.
- Mechanism: the author's article-kit tooling if it lands in time (author); a manual
  per-section pass regardless (Claude), one PR per few sections so the diffs stay
  reviewable. Statements shared with the blueprint: polish in both or not at all — prefer
  polishing prose *around* statements and leaving statement bodies stable.
- Effort cap per the author: this is a diminishing-returns pass, not a rewrite.

### P4 — AI usage statement                                             [status: open] (author)

- The author updates the ai-archive analysis (sessions + git logs) to cover the latest
  work and derives the accurate division of labour between author and agents.
- Then paper/ai-statement.tex is rewritten from that material: what the agents did
  (drafting, proof repair, the impossibility theorem's proof, verification passes,
  figures, review response), what the author did (direction, decisions of record,
  mathematical judgment, external review orchestration, all merges), and how
  verification was grounded (the ledger's image-verified anchors, the Lean development,
  CI gates). Honest, specific, dated.

### P5 — final review and the full artifact gate                        [status: DONE 2026-09-01]

Executed (P4 running in parallel, author-led):
- **DP4 light review, two fresh agents.** Overclaims/front-matter: ten findings, all
  fixed — one factually false sentence (§1's "(H)" coverage claimed for every §8 family;
  the catalogue's Pareto and Mittag-Leffler members fail it — now "every family worked");
  §1.1's self-contradiction on lem:zstar-log-growth (and lem:standing-levy-reading,
  verified \notready, added to the exception); the abstract's integer-shape gate on the
  Gamma cascade; "explicit right inverse" in §1 and §13; the abstract/§13 transport
  member; §11's lead compressed the graded Thorin claim (now "finite Thorin truncations,
  realized as banks ... exactly when integer"); §1.1's duplicated §10 inventory deduped;
  a "The memory line." spine marker; the pointwise qualifier on §1's exponent-dependence
  claim; the α-gauge named in rem:gauge-freedom (both copies). Verdict: claim layer
  publish-ready, no further round needed. Copy-editor: ten mechanical findings, all
  fixed — the "non-completely-monotone monotone" stutter (both copies), a double colon,
  and eight same-word spelling splits harmonized to the majority forms (normalization,
  formalized, behavior, artifact, factorization, gray-level, colored; the realis- family
  kept as the term of art), blueprint copies included where shared.
- **Read-through of the built PDF, front to back** (88 pages, from the artifacts
  branch): clean; float placement good; rendered bibliography well-formed, all 43
  entries cited and resolving both ways, citekey-year quirks canonical.
- **Figures regenerated**: every quoted number in ex:numerical-experiment and Tables 4-5
  confirmed against fresh output; fig-kernels/fig-kernels-mode were stale output of an
  older script (legend drift) — regenerated and committed, and make-figures.py now
  writes into figures/ (it wrote into scripts/).
- **PDF mechanics**: hyperref pdftitle/pdfauthor added (the built PDF had none);
  \emergencystretch clears the paragraph-level overfull boxes; the one display overfull
  (cor:signaling-hadamard clause 3, 11.9pt) split into two displays in both copies.
  \date{\today} freeze stays with P7 per the plan.
- **Companion-note honesty**: "(in preparation)" at the first load-bearing mention in
  §8, §10 (both copies), and §13.
- **The Lean gate** (build, sorry guard, axiom guard to completion with exit codes) runs
  fresh in this PR's CI via a dated trigger comment in CIAxiomGuard.lean — lean.yml is
  path-filtered and had no reason to run since the last Formalization change; its verdict
  is checked on the PR before merge. linkage check is the PR's docs/blueprint job.

- Full read-through of the built PDF, front to back (per DP4: with or without a second
  agent-review round first).
- The artifact gate, run fresh and to completion with exit codes checked:
  - lake build in Formalization/ (library sorry-free, Skeleton compiles);
  - lake env lean CIAxiomGuard.lean — the axiom audit, read in full, not tail-only;
  - figure regeneration: make-figures.py and make-fig-experiment.py re-run, quoted
    numbers in the text confirmed against the regenerated output;
  - linkage check clean (statement sync, ledger contract, render allowlist);
  - bibliography audit: every citekey resolves, formatting pass on the rendered
    bibliography, the known citekey-year quirks (feller2009introduction etc.) left
    canonical per AXIOMS.md's source notes.
- PDF mechanics: float placement and overfull-box sweep of the final build; hyperref
  pdftitle/pdfauthor metadata; \date{\today} frozen to the publication date (in the
  publication commit, so the tag pins it).
- Companion-note honesty check: every "companion note" pointer reads as in-preparation
  unless the note is public by then.

### P6 — repository public-readiness                                    [status: DONE 2026-09-01]

Executed:
- **Keep-list first**: everything tracked was classified; nothing needed deletion.
  draft/ stays (author decision); figures' sources and scripts stay; .claude/,
  .githooks/, .vscode/ and linkage.toml stay (development continues; each is
  self-describing, and none carries secrets — env-var names only).
- **notes/ gathering (DP2)**: the nine process documents moved to notes/ — the four
  paper/ PLAN/DECISIONS files, the four blueprint/ PLAN/REVIEW/NOTES files, and
  ROADMAP.md — with the full-path references updated (CLAUDE.md, README, two Lean
  docstrings, main.tex's header comment). blueprint/DESIGN-formalization-strategy.md
  stays in blueprint/ as load-bearing documentation; AXIOMS.md, trust-boundary.txt and
  render-allowlist.txt are load-bearing and stay. The two external review documents are
  not in the repo; adding them under notes/reviews/ with model attribution remains open
  for the author.
- **CLAUDE.md**: public-readers header note (internal dialect, private infrastructure,
  nothing public depends on it) — kept for continued development per DP2.
- **README**: rewritten for a public reader — what this is, how to read it, the two
  self-contained lake verification commands (linkage/article-kit demoted to a
  development-tooling note per DP1), the full formalization status and per-chapter Lean
  table retained, license section, citation stub (DOI at P7).
- **Licenses (DP1)**: LICENSE.md (the split) + LICENSES/CC-BY-4.0.txt and
  LICENSES/Apache-2.0.txt (SPDX texts). The 70 Lean file headers carried Mathlib-style
  "Apache 2.0 ... file LICENSE" boilerplate pointing at a nonexistent LICENSE; they were
  first flipped to MIT per the original DP1, then — on the author's revision of DP1
  during PR #42 review — back to Apache 2.0, now pointing at LICENSES/Apache-2.0.txt.
- **Sweeps**: no secret patterns, no personal absolute paths, no stale references to
  the moved files. CI note: forks' CI will not run (private article-kit reusable
  workflows + ARTICLE_KIT_TOKEN); documented in README as not needed for verification.
- **Remaining for P7 (author)**: make scale-space-lean public + Apache 2.0 (DP1's flagged
  consequence); make this repo public; the external reviews under notes/reviews/ if
  desired.

- Keep-list first, then delete (the cleanup needs both): draft/ STAYS (author decision);
  PLAN/REVIEW/NOTES per DP2 (recommend keep, possibly under notes/); figures' sources and
  scripts stay; .claude/, linkage.toml and CI configs reviewed for anything
  internal-only.
- CLAUDE.md: trim or replace for a public audience (it speaks the constellation's
  internal dialect — wiki vault, librarian, session discipline); a public CONTRIBUTING
  or README section takes over the reproduction instructions.
- README rewritten for a public reader: what this is, how to read it (paper vs blueprint
  vs Lean), how to verify (the two commands), status, license.
- License files added per DP1.
- Sweep for secrets, personal paths, and internal URLs in tracked files; check CI
  workflows reference no secrets a fork would need.
- Stale-material deletion last, against the keep-list.

### P7 — publish                                                        [status: open]

- Freeze the date, build the final PDF, final commit.
- Mint the release tag (the §1.1 pinning note closes: the paper's own revision is now
  pinned alongside the in-tree toolchain pins); make the repository public.
- Publish per DP3: preview site; arXiv and/or Zenodo if chosen (Zenodo gives the tagged
  release a DOI worth citing in the README).
- Post-publication follow-ups recorded, not gated: formalize the mode-rigidity/
  wellposed arc (first Lean target — it sits on already-verified ground and would move
  the abstract's existence-uniqueness sentence inside the machine-checked perimeter);
  the SSVM extraction paper; the companion note; the open problems of §13.

## Order and dependencies

P1 first (claim language settles before polish). P2 independent, any time before P5.
P3 after P1; P4 (author) in parallel with anything. P5 after P1–P4. P6 after P5's
read-through settles the text; P7 last. Suggested: P1 -> P2 -> P3 (with P4 in parallel)
-> P5 -> P6 -> P7.

## Effort estimates (rough)

P1 half a day; P2 half a day; P3 a few short passes, capped by the author's tooling
decision; P4 author-paced; P5 one session plus the read-through; P6 one session plus the
DP1/DP2 decisions; P7 mechanics, half a day. The only open-ended item is the P5
read-through, which is exactly the item that should be.
