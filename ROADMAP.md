# Roadmap — hemigroup-causal-scale-space-kernels

The backlog for **this article**: its theorems, ledger entries, blueprint nodes and paper prose.

**This is not the framework's backlog.** A new `linkage` check, a manifest field, scaffolding or CI
belongs in `article-kit/ROADMAP.md` — the test is *would a second article need it?* A missing source
is not a roadmap item: dispatch the `librarian` agent, which queues it with `library acquire request`.
Positioning and literature live in the hub's outline page. Like the hub's `Notes/ROADMAP.md`, this
file is **work**, not knowledge; `README.md` holds the node-level state.

---

## Now

### 1. Paper review worklist — fourteen blind draft reviews, 2026-08-15  ·  🟡 open

Fourteen independent `draft-reviewer` runs over `paper/*.tex` (§§1–13 + Appendix A), each blind: no
reviewer saw another's report, none was given a summary of the paper or the drafting history. About
120 located flags. Pooled, they collapse into ten threads that recur *across* sections — which is not
something any single review could report, since blindness is per-section.

Raw reports: `paper/review/2026-08-15/` (gitignored; one file per section, with the exact anchors).

**Ranked by how many independent reviewers hit the same underlying fact, not by any one reviewer's
severity label** — thread A's §4 instance was labelled `[low-med]` and its §7 instance `[high]`, and
they are the same defect. Once flags are pooled, local severity stops being informative.

#### The one that blocks submission

- **`lem:local-polynomial-symbol`'s (⇒) direction.** Marked *"under active revision blueprint-side …
  needs an approximation argument routing through the profiles"* in a LaTeX comment; the rendered
  proof ends flatly, with no hedge a reader can see. §1.5 describes the same gap as *"available but
  laborious"* — labour, not argument. §12's classification cannot do without this lemma. **Decide
  which is true and make the prose say it at the point of claim**; if the step is not settled, §1.5's
  wording cannot stand. Everything else on this list is editorial by comparison.

#### Four decisions that discharge most of the volume

1. **Is the pure delay in the class?** (thread A, 7 sections) Dropping 2005's pointwise-continuity
   requirement admitted an α = 1 member with no density; the prose still describes a class of
   densities throughout. §1 "precisely the sub-case"; §2 `rem:axiom-provenance`'s "nothing else" and
   "the convolution *kernels*"; §4 delivers measures and Φ_{x,x} = Id gives δ₀; §7 cites Sato 27.13
   (a *nondegenerate* theorem) for "every kernel is absolutely continuous", and "never multimodal"
   inherits it; §8 `rem:heavy-tails` "the only k compatible with homogeneity" — a remark §1 cites for
   the headline thesis; §9 "(H) excludes the extreme boundary and nothing else" (the pure delay is
   extreme and is *not* excluded); §10 case (1) excluded only by an axiom `rem:drift-boundary` calls
   optional. Also the b₀ omissions in §11 (rationality) and the appendix (the atom that does not
   dilate). **One answer settles all of it.**
2. **Where does (H) get stated?** (thread B, 6 sections) Every memory-line result is conditional;
   the prose states them flat. §1 never mentions it; §2's embodiment promise is unconditional; §8
   advertises Gamma for all γ > 0 where §9 needs γ > 1 and §13 lists γ ≤ 1 as open; §9 contradicts
   itself twice inside one paragraph; §12 says "the entire temporal jet" where orders reach z\*−1.
3. **One gauge notation.** (thread G, 6 sections) §6 declares the parabolic gauge "used in the
   sequel"; §§8–10, 12 and the appendix all open "Throughout … the *canonical* gauge". §8's
   `prop:stable-moments` contradicts its own section's declaration. §12 applies a parabolic-gauge
   operator to a canonical-gauge theorem. Three spellings of one object, one reusing `x̃` for its
   opposite, plus an unexplained factor ½.
4. **What do the economy claims actually claim?** (thread D, 5 sections) Each is a count a reader can
   falsify by reading on: §3 "needed at exactly three places … never invoke Bernstein–Widder" (§7's
   constructive direction invokes it); §4 "no other axiom enters except (A3)–(A5), each used once"
   ((A3) twice within thirty lines); §7's printed imports vs §1.1's certified trust base; §10's
   silently reinstated Mellin uniqueness, which §1.5 lists as eliminated; §13's "the results here rest
   on two cited facts", dropping §1.1's "*the verified*" scope and false for `thm:locality`.

#### The rest

- **Notation** (thread F, 8 sections). Collisions: `T` (delay semigroup vs Sato subordinator) · `g`
  (test function vs exponent) · `c₂` (function vs scalar, inside a theorem statement) · `k` (Laguerre
  vs memory kernel) · `Δ` · `a` (inverse-gamma shape vs stable index) · `θ` · `γ`/`γ_a`/`γ_E` · `x̃`.
  Never defined anywhere: **the covariant Mellin class** — the quantifier of a uniqueness theorem —
  plus `\SDclass`, `\GGC`, `\CBF`, `D^{1/α}_{x,−}`, `𝒟′`, `X*`, `t₀`/`t_m`, "complete Bernstein
  function", "boundary-hitting", and "trust boundary" (repo vocabulary, used once, in print).
- **Figures** (thread H, 7 sections). Three figures; two are kernel plots in §11 (output, not
  concept). Wanted: the orbit and straightened axis (§6), the headline characterization (§7), **the
  signaling geometry the whole second half is sold on** (§9), the ladder with its cut and slice (§10),
  the filter bank (§11), the tapped cascade (§12), the three-level containment (§13).
- **Statement environments carrying non-statement material** (thread I, 4 sections). §8
  (`prop:bessel-family` asserts an identification its proof never touches; `prop:moments` states a
  definition) · §9 (a lemma statement holding a proof fragment and a page of exegesis) · §10
  (`prop:local-ladder`'s *statement* carries a conjecture and the justification of one of its own
  claims) · §11 (two propositions with unproved editorial clauses).
- **Frontier misplacement** (thread J, besides the blocker above). §4 "nothing rests on the trust
  boundary" while the proof invokes a fact §3 presents as cited. §9 `rem:markov-media` states three
  theorem-strength claims flat, promises §10 takes them up (§10 contains no "Markov"), §13 lists them
  as open, and §11 tables them as settled.
- **Orphans and unnumbered results.** §8's `prop:admissibility-criterion` and `lem:criterion-converse`
  are referenced nowhere in the paper, though the section opens by promising every family uses them —
  the blueprint's `\uses{}` does route three proofs through the criterion, and the paper's reordering
  dropped the invocations. Appendix `prop:fixed-scale-semigroup` is orphaned by its own admission.
  §13's `rem:strata` introduces new, unnumbered mathematics *with an inline proof* in the conclusion,
  which §1's positioning paragraph then leans on.
- **Missing limitations passage** (§13). The honest constraints exist and are never gathered: purely
  temporal; the Bessel corner has no finite-dimensional time-recursive realization; stable members
  with α < ½ admit no Markov medium; (H) excludes the cone's extreme boundary; no empirical
  validation. A referee will otherwise read the section as costless.
- **`paper/ai-statement.tex` is empty** — a `\section*{}` and a "[to be written]" comment. The
  disclosure paragraph is drafted in the hub's private `writing-style-and-ai-use.md` §2.

#### Two threads that are **not** this article's work

- **Blueprint context dropped in transcription** (thread C, 5 sections) — a transclusion-seam defect,
  filed as `article-kit/ROADMAP.md` item 10. Two instances change truth values: the blueprint records
  that (ND) was "borrowed silently" and that *without it the identity is false*, and it deliberately
  splits Laplace uniqueness into finite and σ-finite nodes "precisely because κ, ℓ and Lebesgue are
  none of them finite" — the paper collapsed them into one, and five appendix proofs lean on the
  wrong one. Fixing those two here is this article's work; stopping it recurring is the framework's.
- **Pointers no checker can see** (thread E) — filed against `linkage paper`,
  `article-kit/ROADMAP.md` item 3. Article-side instances to fix once that exists (or by hand now):
  `prop:pair-regularity(3)` should be `(2)` in `03-preliminaries.tex:88` (**found independently three
  times**, by the §3, appendix and §11 reviewers); §4's bare `§XIII`; §10's two identities cited to
  `lem:mellin-data` that belong to `lem:inversion-symbol`; and the hand-written `\tag{7.1}`, `(9.1)`,
  `(9.2)` — `(7.1)` collides with the auto-numbered `Lemma 7.1` in the same sentence, and `(9.1)` sits
  in Appendix A where §9 is a different section.

**Sequencing.** The blocker first, then the four decisions — most of the remaining flags are
downstream of them, so acting thread-by-thread before deciding would mean editing the same sentences
twice. Prose edits should follow `ai-prose-patterns.md` §3's discipline: late, on frozen text, one
item per invocation, exact-anchor replacement, one commit per pass.

### 2. Shared statements — pin or resolve the 11 non-verbatim markers  ·  🟡 open 2026-08-15

`linkage check` now compares each `% shared with blueprint` statement against its blueprint node
(article-kit #10). Result: **51 of 62 verified byte-identical, 11 not** — and none of the 11 is drift
in the sense of an accident. They fall into four kinds, and the kind decides who acts:

**(a) The paper merges several blueprint nodes — 5.** `prop:extreme-rays`, `prop:stable-moments`,
`prop:gamma-kernels`, `def:inversion-operator`, `prop:volterra`. The blueprint splits statements so
Lean progress is legible; the paper states the pieces whole. **25 of 87 blueprint nodes are marked by
no paper marker at all** for this reason — `thm:main-construction` / `thm:main-analysis` /
`prop:main-uniqueness` against the paper's one `thm:main-characterization`, `prop:gamma-density` +
`prop:gamma-moments`, `prop:stable-mode`, `prop:volterra-uniqueness`, `lem:dickman-superposition` +
`lem:admissible-cone`, `lem:profile-eigenfunction`. **Action:** name every node the statement renders,
then pin — `% shared with blueprint prop:volterra, prop:volterra-uniqueness@<sha>`.

**(b) Document-local cross-references — 3.** `lem:memory-fractional-integrals` (`\ref{sec:appendix-memory}`
vs `\S10`), `lem:generator-properties` (vs `Chapter~9`), `prop:bessel-family` (vs `Theorems 10.4, 11.6
and 12.5`). Both documents are right in their own numbering, so byte-equality is unreachable; these are
pin-only. Worth considering whether the closing pointer belongs in a *shared statement* at all — §8's
reviewer flagged `prop:bessel-family`'s for asserting what its proof does not establish. Note the
blueprint side hardcodes numbers where the paper uses `\ref`, which goes stale by construction.

**(c) Blueprint-internal bookkeeping inside a shared statement — 2.** `prop:admissibility-criterion`
ends "…which is why this node's dependency list records only `\ref{def:levy-exponent}`";
`def:locality-pmp` says the profiles "were added to the test class **after formalisation**". Neither
belongs in a statement the paper shares. **Blueprint-side, so the mathematician's** — the paper is
right in both.

**(d) Formatting — 1.** `prop:scale-evolution`: the blueprint wraps a clause in
`\begin{enumerate}\item[]`; no content difference.

**Do (a) and (b) with `linkage check --pin-shared`, one statement at a time.** Pinning asserts that
someone read the statement against that version of the node, so pinning the backlog wholesale would
make the check a rubber stamp on day one. Several of these already carry hand-written annotations
saying exactly this (`— "§10" adapted to the appendix.`); the pin makes them checkable.

Once (a)–(d) are pinned or resolved, CI adopts `linkage check --strict-shared` and the paper can no
longer fork from the blueprint silently.

### 3. Surface prose — em-dashes and long sentences  ·  🟡 open

`linkage prose stats` against two baselines (the author's own four papers, 24.8k words; nine pre-2022
scale-space papers, 87k words):

- **em-dash 15.2/kw** against 0.3 and 0.3 — the only feature over *both* baselines, ~45×. In §13
  nearly every one is paired, bracketing an aside inside an already-long sentence.
- **35% of sentences over 30 words** against 17% and 20%. Same phenomenon as the em-dashes, not a
  second one — the short-sentence share is already at baseline (12% vs 11%), so the floor is fine and
  only the ceiling is breached.
- Semicolons at 11.7/kw look alarming against the author baseline (0.1) and are **ordinary for the
  field** (7.8). A voice deviation, not a register one — optional, and the author's call.
- Worst sections: `12-jet` (56% > 30w), `13-discussion` (57%), `10-locality` (50%, em 24.1),
  `04-representation` (50%), `11-implementation` (48%), `01-introduction` (46%).
- Everything else measured — salience hedges, boosters, attitude markers, reveal frames, signposting,
  vague attribution — is at or **below** both baselines, with raw counts of 0–2. There is no
  discourse-level tic problem in this paper.

Do this pass **after** item 1, on frozen text: these are the edits `ai-prose-patterns.md` warns get
regenerated if anything upstream is still moving.
