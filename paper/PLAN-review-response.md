# PLAN — response to the external review (2026-09-01)

Working plan for revising the paper in response to the detailed external review
(`hemigroup_detailed_review_sol5_6_extra_high.md`, "the review" below; the second review
contributed two presentation items, folded into R8/R9). The review's verdict was *major
revision*: the theorem layer stands, but several headline claims outrun what is proved, one
proof has a genuine gap, and a number of statements need scoping. Assessment session
2026-09-01: most findings verified independently and accepted; a few scoped down; one
answered by a proposed new theorem (R2).

Conventions: every batch is one PR, validated by the control-char guard and the ref/bib
checks before push, full gate in Docs CI. Statements shared with the blueprint are changed
in both documents or not at all; everything below is paper-side unless noted. Page
references ("p. 33") are to the reviewed PDF build.

## Standing decisions (author, 2026-09-01 assessment discussion)

- The monograph stays **one document**. The review's split recommendation is realized as
  the planned SSVM extraction (characterization paper), out of scope here.
- The review's storytelling advice is adopted where it serves the monograph's multi-audience
  genre, declined where it reviews the monograph as a journal submission.

## Decision points — RESOLVED (author, 2026-09-01)

- **D1 — "well posed":** rename now ("existence and uniqueness in the profile-dominated
  Mellin class"); the stability-theorem question is deliberately left open for a later
  revisit. The free L1-contraction stability remark for the scale-Cauchy reading goes in
  with R4.
- **D2 — theorem numbering:** keep the 3'/4'/5' lineage labels, with the constraint that
  the explanation must be self-contained --- the reader must NOT need the 2005 article:
  the convention sentence in §1 states in-paper what each primed theorem is the analogue
  of (the paper already restates each recovered original where it recovers it).
- **D3 — §1.1:** light compression, kept in the main text.
- **D4 — signal model:** narrow the application rhetoric now; natural-signal example
  deferred (revisit for the SSVM paper).
- **D5 — Figure 14:** caption fix only ("in this run"); no re-render.

## Batches

### R0 — verification pass                                    [status: DONE 2026-09-01]

Findings (fixes for 1 and 3 landed inline with this batch, being small and verified):
1. **Gauge slip confirmed and FIXED** (§6, post-canonical-gauge prose). The text claimed
   S_sigma x = sigma x and chi = identity in the semigroup case; in the semigroup's own
   additive parameter tau the action is S_sigma tau = sigma^alpha tau and
   chi(tau) = tau^{1/alpha}. Rewritten with both coordinates named and
   rem:recovering-thm3 cross-referenced; coincidence only at alpha = 1.
2. **Laplace-uniqueness propositions are positive-measure only** (prop:laplace-uniqueness,
   prop:laplace-uniqueness-sigma-finite). Signed applications to inventory in R6:
   the V(t) = 0 arguments in prop:scale-evolution, lem:generator-properties(5), and the
   §9 corollary proofs. Fix (R6): a paper-only signed corollary after the sigma-finite
   proposition, by decomposition into positive and negative parts.
3. **Kent claim was wrong beyond the review's finding, and FIXED.** Verified against the
   source (library page images, printed pp. 207-208): Kent's setting is a *nonsingular
   diffusion on an interval*, interior first passage r0 < a < b < r1, conclusion the
   *Bondesson class* on [0, infinity] (possibly defective). The paper's sentence concluded
   "every diffusion hitting time lies in the Thorin subclass" --- wrong twice: Bondesson
   strictly contains Thorin, and Bondesson members need not even be self-decomposable
   (CM Levy density ell does not make t*ell(t) nonincreasing), hence need not be
   admissible. Sentence rewritten with Kent's hypotheses, the Bondesson conclusion, and
   the honest scoping; "every law just named" downstream adjusted to "every admissible
   law just named". The R6 Kent item is thereby done.
4. `make-figureps.py`: not present at the current head (only the correct
   `make-figures.py` in §11). Either fixed earlier or a reviewer misread. No action.
5. Headline inventory for R3-R5 sweeps: 48 occurrences across 10 files (grep terms:
   non-creation, well[- ]posed, substrate, conservation of information, exactly
   invertible, dilation-closed); per-file counts recorded in the session log, re-grep at
   sweep time.

### R1 — page-33 proof repair (prop:gamma-regularity extrema clause)  [status: DONE 2026-09-01]

Done as specified below: statement clause (1) restated with the VD bound for integrable
and bounded g (essential sign changes), the level form and zero-crossing clause derived
from it, and the extremum clause hypotheses f in core with extrema counted as essential
sign changes of the derivative; proof rewritten via the derivative route
(d/dt u = mu * f' from the primitive structure), with a parenthetical recording why the
level route cannot bound the extremum count (disjoint value ranges). Paper-only
(no blueprint node). Original spec:

The inference "n local extrema admit a level with n+1 sign changes" is false (disjoint
value ranges); verified by counterexample. Repair by the derivative route:
- restate the extremum clause with an explicit function class (absolutely continuous f,
  f' in L1, sign changes of f' counted with the deadband/compression convention),
- prove it via (mu * f)' = mu * f' and variation diminution applied to f' (same Karlin
  citations; librarian re-check that Ch. 5 Thm 4.2 covers the application),
- keep the per-level bound S^-(u - c) <= S^-(f - c) as is (it is correct),
- state how flat extrema are counted.
Paper-only (prop:gamma-regularity has no blueprint node). Downstream text that quotes the
extremum form (§11 Table 1 row, §12 C2 item, §13 summary) re-checked for consistency.

### R2 — the impossibility theorem (the review's Issue 1, answered)      [status: open]

Attempt the new result: *no admissible family other than the pure delay has all interior
increments variation-diminishing.* Sketch (assessment session): increments VD forces each
increment exponent to be drift + unit-weight exponential atoms (Schoenberg form of
exp(g_{x,y})); matching Dirichlet exponents of k(t/y) - k(t/x) forces the atom set to be
invariant under multiplication by every ratio y/x > 1, hence with weights >= 1 its
sum of reciprocals diverges, contradicting finite mean; so k = 0.
- Write statement + proof as a proposition next to rem:pf-hemigroup in §8; the remark is
  then recast: the semigroup obstruction (Karlin) and the hemigroup obstruction (this
  proposition) together show endpoint variation diminution is the strongest form that can
  exist, achieved exactly by the integer-atom members.
- Needs a clean lemma for uniqueness of exponents in finite/countable exponential sums
  (the paper's Laplace-uniqueness tools should suffice).
- If the proof does NOT close: fall back to the review's framing (property weakened, not
  obstruction dissolved) in R3, and record the statement as a conjecture/open problem.
- Candidate for blueprint promotion + Lean later; paper-only in this revision.

### R3 — non-creation claims sweep                                       [status: open; after R2]

Language depends on R2's outcome (impossibility proved: "scale-monotone non-creation is
impossible in the class; the endpoint form is optimal and achieved"; otherwise: "endpoint
variation diminution relative to the input; the scale-monotone form is not recovered").
Sweep every headline occurrence:
- abstract (non-creation sentence), §1 (non-creation paragraph + contributions bullet),
- §8: proposition name ("non-creation in time" -> endpoint form), rem:pf-hemigroup recast,
- §11: Table 1 row rename ("endpoint VD relative to input") + the substrate paragraph's
  regularity tie-in,
- §12: experiment C2 item (already honest post-correction; align vocabulary), fig-fingerprint
  caption gains "in this run",
- §13: summary sentence, strata "non-creation subclass" phrasing (limit kernel, scale-time),
- appendix: cor:past-dominating framing untouched (it is a genuine conditional
  scale-monotone statement — say so explicitly as the contrast).

### R4 — well-posedness language (per D1)                                [status: open]

Rename across abstract, §1, §9 (arc prose + corollary name if D1 says rename), §13.
Add the L1-contraction stability remark for the scale-Cauchy reading (one paragraph,
trivial from contractivity) regardless of D1, so the honest statement is "existence,
uniqueness in the stated class, and stability in the evolution reading".

### R5 — Thorin substrate separation                                     [status: open]

- §11 prop:thorin-subclass discussion: split the bold claim into (i) admissible atomic
  approximation, any positive weights (proved); (ii) exact finite first-order realization,
  integer weights (proved); (iii) rational fitting for real weights (heuristic, cite
  oustaloup2000frequency where it already is; no error theorem claimed).
- Add the fractional-sample-delay caveat for the drift (one sentence).
- Do not advertise "sections per decade" earlier than the heuristic paragraph; check §1 and
  abstract phrasing ("approximate the entire completely-monotone subclass" stays, since
  prop:thorin-subclass's weak-convergence clause does hold for real weights — the
  overclaim is only the *rational/first-order* rider).
- Constructive integer-weight approximation theorem with error bounds: recorded as an open
  problem / companion-note candidate, not attempted here.

### R6 — scoping batch (Issue 6 + appendix corrections)                  [status: open; after R0]

- rem:markov-media: mark as context with precise citations or explicit forward pointer to
  the separate article; Table 1 medium row gets an evidentiary label.
- Kent sentence: DONE with R0.3 (see above).
- §13 strata: "finite truncations ... not dilation-closed" disambiguated — the
  fixed-time-constant cascade of the published construction, not the truncated exponent's
  similarity family (which IS covariant by prop:thorin-subclass).
- Signed Laplace uniqueness: add the signed/L1 corollary (Jordan decomposition reduction)
  as a paper-only remark in §3, referenced where used.
- Appendix: "identifies with the locality corner" -> "contains the local families
  classified in §10"; the V.2 endpoint sentence corrected (the *coefficient* t - b0 x
  vanishes; the density need not — gamma = 1 positive, gamma < 1 divergent); the
  post-V.2 uniqueness/Picard paragraph explicitly labelled heuristic; the Sonine
  motivation's "each infinitesimal smoothing step is exactly invertible" reworded to the
  one-sided D-has-right-inverse form (keeping the body text's D-vs-Phi distinction).

### R7 — signal-model scope (Issue 5, per D4)                            [status: open]

- A remark (§2 or §3): the kernels are probability measures, so convolution extends to
  bounded measurable signals with the same pointwise definition E f(t - x T1); which
  arguments genuinely need L1 (transforms, the characterization) and which conclusions
  survive extension (pointwise field, PMP/sign statements, the experiment's step).
- Scope sentence in §1 and §13: mathematical foundations + exact implementation route;
  application rhetoric aligned with D4.

### R8 — front-matter rebuild on the four-question spine                 [status: open; after R3–R5]

- Abstract rebuilt at ~200 words: the axiom move, the characterization, one Gamma
  consequence, one memory-line consequence, one honest what-is-and-is-not-preserved
  sentence (uses R3 language), machine-checking.
- §1 first two pages reordered around the four questions (which assumption; what replaces
  stable; what new members; what is/isn't preserved); the trade-off stated before the
  headline consequences.
- Fast-track reader guide at the end of §1 (practitioners vs theorists), one short
  paragraph.
- §1.1 per D3; add repository URL, immutable tag/commit, Lean/Mathlib versions, and the
  one-command verification instruction.
- Numbering convention sentence per D2.

### R9 — notation and navigation apparatus                               [status: open]

- Notation/gauge table in §3: g_{x,y}, G, F, H, B, m, phi_x, k, kappa^(x), ell^(x); the
  original, canonical, semigroup (tau = x^alpha), and parabolic coordinates; one column of
  delay-catalogue readings (absorbs the second review's Rosetta table).
- Optional: compact theorem-dependency map (§1 or endpaper).
- Metaphor audit: keep random-delay/subordinator primary; trim where two metaphors compete
  in one passage (light touch, author taste governs).

### R10 — presentation batch                                             [status: open]

- hyperref: hidelinks (or colored text, no boxes).
- Table 1: split or per-row evidentiary labels (proved / heuristic / context), consistent
  with R3/R6 renames.
- ex:numerical-experiment: state the counting conventions (deadband, compression of flat
  runs, boundary handling) in the text, matching make-fig-experiment.py.
- Figure 14 per D5.
- Fix the script-name typo found in R0.4.

## Order and dependencies

R0 first (feeds R1, R3, R6). R2 before R3. R1 independent, can run parallel to R2.
R4–R7 independent of each other, after their decision points. R8 last of the content
batches (front matter rewritten once the claim language is settled). R9–R10 anytime.
Suggested sequence: R0 -> R1 -> R2 -> R3 -> (R4, R5, R6, R7 in any order) -> R8 -> R9 -> R10.

## Effort estimates (rough)

R0 half a session; R1 one session; R2 one to two sessions (math risk lives here);
R3 one session; R4 small; R5 small-medium; R6 one session; R7 small; R8 one to two
sessions; R9 one session; R10 small. The claim-layer work (R3–R6) is wide but shallow;
the only genuinely open-ended item is R2, which has an explicit fallback.

## Out of scope, recorded

- The SSVM characterization paper (the review's "split", by other means).
- Constructive integer-weight Thorin approximation with error bounds (companion-note
  candidate; noted as open in R5).
- Natural-signal experiment if D4 chooses narrowing (revisit for the SSVM paper, where one
  real signal would earn its place).
- Blueprint/Lean promotion of R1's repaired proof and R2's theorem (after the paper text
  settles).
