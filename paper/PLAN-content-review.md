# PLAN — content review of the paper, 2026-08-15

The improvement session that follows the fourteen blind draft reviews (`ROADMAP.md` item 1; raw
reports in the gitignored `paper/review/2026-08-15/`). Scope: **content** — scope, hypotheses,
notation, structure, figures, missing passages. **Not** AI-language artefacts: those are ROADMAP item 3
and come last, on frozen text, because fixing tics early only has them regenerated in a different
form by later content edits.

## Standing facts that shape the plan

- **The blueprint is the text of record and CI is strict** (`b32fc8f`): every `% shared with
  blueprint` statement must stay byte-identical to its node. A flag whose anchor sits inside a shared
  block is a **blueprint-side** edit — dispatched to the `mathematician`, then re-synced into the paper
  — never a paper edit. Proofs and prose outside shared blocks are paper-side.
- **The fidelity review (`blueprint/REVIEW-fidelity.md`) postdates the section reviews.** R2, R3, R8,
  R10, R27 and the shared-statement re-syncs (`5056a80`, `094a2a5`) changed text the reviewers read.
  Every flag on §§9, 10, 12 and the appendix is re-checked against the current file before it is acted
  on; stale flags are recorded as stale, not silently dropped.
- **The former "blocker" is stale.** `lem:local-polynomial-symbol` is `\leanok` in both directions in
  the blueprint. What remains is paper-side: the `SYNC FLAG` in `10-locality.tex`'s header, the printed
  (⇒) proof, and §1.5's "available but laborious". Handled in the §10 step and the §1 step.
- **Work in the main checkout.** The `paper-writing` worktree is 50 commits behind with nothing
  unpushed; paper edits and blueprint syncs now interleave, so one checkout. Commit and push per step.
- **Gate for a paper-only step:** `scripts/check-control-chars.py`, `linkage check`,
  `scripts/build-blueprint.sh --quick`, `latexmk` in `paper/`. Add `lake build` +
  `lake env lean CIAxiomGuard.lean` when a blueprint-side edit touched a `\lean`-tagged node.

- **Sub-agent models are chosen per task, never inherited.** The session runs on Fable for the
  analysis; every `Agent` call passes `model` explicitly — `sonnet` for read-only reads, greps and
  figure scripting, `opus` for the `mathematician` (blueprint/Lean edits) — so the session's budget is
  spent on judgement, not on dispatch.

## Shape of the session

Global → local (sequential) → global → language.

### Step 0 — decisions of record

Four decisions discharge most of the ~120 flags; they are taken **before** any section is edited, so no
sentence is edited twice. Each is presented with the flag evidence and a recommendation; the outcome is
recorded in `paper/DECISIONS.md` (tracked) and, where it changes a statement, in the blueprint.

| # | thread | question | recommendation to argue |
|---|---|---|---|
| D-A | A (7 §§) | Is the pure delay (α = 1, μ = δ_x, no density) in the class? | **Yes** — the theorem says so. Fix the prose that says "densities"/"kernels"; state absolute continuity and unimodality under `k ≢ 0`, as the appendix already does; §1's "precisely the sub-case" and `rem:heavy-tails`' "the only k" reworded. |
| D-B | B (6 §§) | Where is (H) stated, and how do results downstream carry it? | One home: §9's opening (`def:standing-hypothesis`), plus one sentence in §1's roadmap and a qualifier on §2's embodiment promise; §8's Gamma advertisement notes γ > 1 for the memory line; §12's "entire jet" bounded by z_*−1. |
| D-G | G (6 §§) | One gauge notation. | Canonical gauge is the working gauge from §6 on; the parabolic gauge is *introduced where used* with its own symbol (never `x̃` for both); the factor ½ explained at first use. §6's "used in the sequel" corrected. |
| D-D | D (5 §§) | What do the economy claims claim? | Every count is made exact or removed. §1.1 (what is machine-checked) is the single statement of what rests on what; §3, §4, §7, §10, §13 cite it rather than restate it. |

Also settled in Step 0, as **registries carried through every section step**:

- **Notation registry** (thread F): the nine collisions and the twelve undefined symbols, each with a
  chosen resolution (rename / define at first use / drop). Blueprint-side where the symbol is in a
  shared statement.
- **Figure list** (thread H). **Be generous** — there is no length constraint now (author's decision,
  2026-08-16); a journal cut is a later problem. All seven wanted figures are made, plus any a section
  step finds owed. The SSF work (`$WIKI_VAULT/wiki/outlines/spatio-temporal-scale-space.md`, same
  review method) produced sixteen figures, several on the same content; its scripts live in
  `$WIKI_VAULT/scripts/` (pure-stdlib SVG emitters, made for Obsidian) and are the design source —
  reuse the picture, re-emit for LaTeX (PDF via `scripts/make-figures.py`'s matplotlib route, or
  SVG→PDF). Correspondence:

  | wanted here | SSF analogue to reuse | notes |
  |---|---|---|
  | §2 axioms: point property, covariance/cascade squares | `point_property.py`, `covariance_square.py` | cascade square becomes the *hemigroup* triangle Φ_{y,z}Φ_{x,y} = Φ_{x,z}; sits beside `fig-cascade` |
  | §6 orbit and straightened axis | `parabolic_grading.py` (orbits in a quadrant) | here: the `S_σ` orbit on the scale axis and the gauge `χ` straightening it |
  | §7 headline characterization | `memory_family_map.py` (inclusion diagram) | the cone of admissible `F`; semigroup slice = stable ray; extreme rays; (H)-boundary; Gamma, Bessel marked |
  | §8 kernel gallery | `stable_kernel_gallery.py`, `covariant_memory_figure.py` (ν-dial, log-log tails), `mode-comparison.png` | the existing `fig-kernels*.png` may move here from §11 |
  | §9 signaling geometry | `memory_halfline.py` | boundary-fed half-line, `u(t,x)`, the inversion `A` — the figure the second half is sold on |
  | §10 ladder with cut and slice | — (new) | |
  | §11 filter bank | — (new; cascade of first-order sections) | |
  | §12 tapped cascade | — (new; taps on the §11 cascade) | |
  | §13 three-level containment | `memory_family_map.py` | possibly the same figure as §7's, revisited |

  Made in `scripts/`, placed during the owning section's step; the §7/§13 map made once, in §7.
- **Pointer list** (thread E): `prop:pair-regularity(3)`→(2), the bare `§XIII`, `lem:mellin-data`→
  `lem:inversion-symbol`, the hand-written `\tag{7.1}`/`(9.1)`/`(9.2)`. Mechanical; done in the
  owning steps.

### Steps 1–14 — one section per step

Order: **§2, §3, §4, §5, §6, §7, §8, §9, §10, §11, §12, App. A, then §1, then §13.** The introduction
and the discussion summarise everything else, so they are edited last, against the final content.

Each step, the same shape:

1. **Briefing** (me): the reviewer's flags for the section, each triaged —
   *stale* (cite what resolved it) · *blueprint-side* (shared statement; names the node) ·
   *decision-driven* (D-A/B/G/D applied) · *local* — plus my own read for content improvements the
   reviewer did not raise, plus this section's instances from the three registries.
   Language artefacts are noted, not fixed.
2. **Author input**: additions, vetoes, priorities. The agreed edit list is the step's scope.
3. **Apply**: paper-side edits directly; blueprint-side edits via the `mathematician`, then re-sync
   the paper copy; figures via `scripts/`. Never `git add -A`.
4. **Gate, commit, push.** One commit per section, message naming the section and the threads it
   discharged.

Per-section notes known now (from the reports and the current state):

- **§2** — `rem:axiom-provenance`'s "nothing else" and "kernels" (D-A); embodiment promise (D-B).
- **§3** — economy claim on Bernstein–Widder (D-D); `prop:pair-regularity(3)`; `T` collision;
  LE/BF₀ integrability note dropped in transcription (thread C — restore).
- **§4** — "(A3) once" (D-D); "nothing rests on the trust boundary" (J); `§XIII`; `g` collision;
  measures-not-densities (D-A).
- **§5** — covariance-free note and change-of-variables step dropped (C — restore); `lem:additivity`'s statement says `G(x,0+) = 0` where the Lean (`Additivity.lean:162`) and the proof have the value at 0 — same one-token fix as `lem:transform-continuity` (found by the mathematician in the §4 step).
- **§6** — gauge declaration (D-G); `lem:action-rigidity` gloss dropped (C); orbit figure.
- **§7** — `rem:extreme-rays` under `k ≢ 0` (D-A); §1.1 vs printed imports (D-D); `\Mplus`
  overload and lemma clause (1)'s `0 < a` are **blueprint-side**; move the (H)-boundary half of
  `rem:extreme-rays` to §9 (D-B); reading of `sF'(s)`; characterization figure; `\tag{7.1}`.
- **§8** — orphaned `prop:admissibility-criterion`/`lem:criterion-converse` (restore the three
  invocations the blueprint's `\uses` routes); `prop:bessel-family`'s closing pointer and
  `prop:moments`' definition-in-statement (I; blueprint-side); `prop:stable-moments`' gauge (D-G);
  `rem:heavy-tails` (D-A); Gamma γ > 1 (D-B).
- **§9** — re-check first (R2, R10 changed `thm:signaling-form`, `lem:symbol-uniqueness`); "(H)
  excludes … nothing else" (D-A/D-B); **deposit from §7's `rem:extreme-rays` (cut there per D-B item 5):** every extreme ray has `F(s) ~ log s`, hence `z_* = 1`, so the extreme rays with `b₀ = 0` lie on (H)'s boundary; (H) asks `z_* > 1` and §9 needs the strict inequality at three points — convergence of the Mellin integral of the delayed field (`lem:memory-fractional-integrals`), that lemma applied at `z−1` in Thm 11.6(2), and convergence of `∫_ρ^t (t−r)^{z−2}dr` in the same proof — three obligations, one endpoint, so the boundary of (H) is characteristic of the theory; rewrite per D-B item 4 (b₀ > 0 gives z_* = ∞; Gamma at γ ≤ 1 excluded though not extreme); the covariant Mellin class **defined**; `rem:markov-media`'s
  three flat claims (J — down-grade to conjecture, or point at §13's open list); lemma statement
  carrying exegesis (I); signaling-geometry figure.
- **§10** — drop the `SYNC FLAG`, re-sync the (⇒) proof from blueprint part 12; Mellin uniqueness
  reinstated (D-D); `prop:local-ladder`'s statement carrying a conjecture (I); `c₂` collision; ladder
  figure; case (1)/`rem:drift-boundary` (D-A).
- **§11** — b₀ omission in the rationality claim (D-A); `Δ`, `a`, `θ` collisions; two propositions
  with editorial clauses (I); Markov table vs §13's open list (J).
- **§12** — re-check first (R3 changed `def:locality-pmp`); "entire jet" (D-B); parabolic-gauge
  operator applied to canonical-gauge theorem (D-G); `k` collision; tapped-cascade figure.
- **App. A** — restore "(ND) borrowed silently / without it the identity is false" (C); five proofs
  citing the collapsed Laplace-uniqueness node — point each at the finite or σ-finite refinement
  the blueprint uses (C); the drift atom that does not dilate (D-A); `(9.1)`/`(9.2)`; orphaned
  `prop:fixed-scale-semigroup`.
- **§1** — "precisely the sub-case" (D-A); (H) sentence (D-B); §1.5's "available but laborious"
  rewritten against the proved lemma; §1.1 confirmed as the single trust-base statement (D-D).
- **§13** — "rest on two cited facts" scoped as §1.1 is (D-D); `rem:strata`'s unnumbered
  mathematics-with-proof (number it or move it); **limitations passage written**; Markov claims
  listed once, consistently with §9/§11.

### Step 15 — global sweep on the frozen content

**Repetition check (author, after §2).** Local improvements — a fuller section lead, per-axiom
motivation, then the axioms — can add up to a section that says each thing more than once. Not acted
on now; at the sweep, read each section once for lead/body/statement redundancy and cut.

Mechanical re-checks across all files, since each section step could only see its own instance:
gauge names; every "(H)"/"Assume (H)"; every "absolutely continuous"/"density"; the economy sentences;
each registry entry; hand-written tags; orphans (`\label` with no `\ref`). Then: figures not yet
placed, `ai-statement.tex` written (from the hub's `writing-style-and-ai-use.md` §2), ROADMAP items 1
and 2 closed, `main.tex`'s header and `README.md` updated. Optionally re-run `draft-reviewer` blind on
the most-changed sections for a second aggregation before freezing.

### Step 16 — the language pass (ROADMAP item 3)

Only now. Per `ai-prose-patterns.md` §3: one item per invocation, exact-anchor replacement, one commit
per pass; em-dashes and >30-word sentences first (the only two features over both baselines).

## Progress

| step | section | state | commit |
|---|---|---|---|
| 0 | decisions | done — `DECISIONS.md` | |
| 1 | §2 | done | see git log |
| 2 | §3 | done | see git log |
| 3 | §4 | done | see git log |
| 4 | §5 | done | see git log |
| 5 | §6 | done | see git log |
| 6 | §7 | done | see git log |
| 7 | §8 | | |
| 8 | §9 | | |
| 9 | §10 | | |
| 10 | §11 | | |
| 11 | §12 | | |
| 12 | App. A | | |
| 13 | §1 | | |
| 14 | §13 | | |
| 15 | global sweep | | |
| 16 | language pass | | |
