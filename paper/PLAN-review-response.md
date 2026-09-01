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

### R2 — the impossibility theorem (the review's Issue 1, answered)  [status: DONE 2026-09-01]

**The theorem closed — no fallback needed.** prop:vd-impossibility in §8, after
rem:pf-hemigroup: if every interior increment operator of an admissible family is
variation-diminishing, the family is the pure delay; the endpoint form is the strongest
VD property the class can carry, attained by the integer-atom members. The proof
architecture improved on the sketch below: a smoothing trick (convolve the increment with
a Gamma shape-2 density, itself PF) reduces everything to the *density* form of Schoenberg
already anchored in prop:gamma-regularity — no measure-level PF theory, no endpoint-PF
step, no Bondesson closure needed — then Lévy-tail comparison across two smoothing scales
gives integer-atomic representing measures for the increment tails, and a dilation-orbit
argument replicates any atom into uncountably many unit atoms inside one locally finite
measure. Companion remark rem:ladder-vd records the sharpness: increments of a *single*
ratio can all be VD (condition mult(q tau) >= mult(tau)), and the limit kernel realizes
it — each q-rung is one exponential kernel, so sign-change counts are monotone rung to
rung along geometric ladders: scale-monotone non-creation is available in the
discrete-covariance stratum and impossible under full covariance. **R3's language branch
is thereby resolved to the strong form** ("impossible in the class; endpoint form
optimal and attained"). Candidate for blueprint/Lean promotion recorded. Original spec:

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

### R3 — non-creation claims sweep                                       [status: DONE 2026-09-01]

Executed in the strong form (R2 closed): "settled in both directions --- the scale-monotone
form impossible (prop:vd-impossibility), the endpoint form classified and attained
(prop:gamma-regularity)". Every headline occurrence swept:
- abstract: non-creation sentence rewritten to the both-directions form;
- §1: non-creation paragraph rewritten (impossibility first, endpoint form as what exists,
  ladder sentence via rem:ladder-vd + cor:past-dominating), "non-creation subclass" ->
  "variation-diminishing subclass", contributions bullet -> both-directions form;
- §8: prop:gamma-regularity retitled "non-creation from the signal; ...";
  rem:pf-hemigroup retitled "causal non-creation: what survives, and what cannot", its
  claims scoped to the endpoint form ("carries its endpoint form", "dissolves the
  obstruction for the endpoint form");
- §11: Table 1 row -> "non-creation from the signal"; substrate paragraph already in
  variation-diminishing vocabulary, unchanged;
- §12: C2 item -> "Non-creation from the signal", "not asserted" strengthened to "not
  merely unasserted but impossible in the class (prop:vd-impossibility)"; fig-fingerprint
  caption -> "holds in this run" (D5);
- §13: summary sentence -> both-directions form; stratum-2 limit-kernel passage gains the
  rem:ladder-vd rung-monotonicity clause and "variation-diminishing subclass";
- appendix: "counting non-creation from the signal" precision; cor:past-dominating framing
  untouched (a genuine conditional pointwise statement, already contrasted in §8's remark).
Final grep: no "non-creation in time"/"non-creation subclass" remains in the .tex sources.

### R4 — well-posedness language (per D1)                                [status: DONE 2026-09-01]

Renamed per D1 ("existence and uniqueness in the profile-dominated Mellin class"):
- cor:signaling-wellposed retitled "the signaling problem: existence and uniqueness in
  the profile-dominated Mellin class" — a SHARED statement, changed in the paper and the
  blueprint together; the label is an identifier and stays;
- §9 arc prose: "genuinely well posed" -> "genuinely solved"; the "earns the phrase
  well posed" sentence replaced by the named claim + a pointer to the stability remark
  (paper) / by the named claim alone (blueprint, where the remark does not exist);
- abstract: "well-posed signaling problem" -> "signaling problem, solved with existence
  and uniqueness in an explicit class";
- §1: "the problem is well posed" -> "solved with existence and uniqueness", with the
  nonexpansive-dependence clause added; §1.1 "well-posedness arc" -> "solution-theory arc";
- appendix Theorem-3' intro: "a well-posed Cauchy problem" -> "a Cauchy problem with a
  uniqueness clause"; the Prüss citation's "well-posedness" kept (an attributed result).
NEW rem:signaling-stability (paper-only, after rem:classical-families): Hadamard's three
demands named; L1-contraction of mu_{0,x}* gives nonexpansive dependence on the signal at
every scale, and mu_{x,y}* the same along the evolution (the scale-Cauchy reading); what
is NOT claimed (stability in a topology adapted to A) stated, the full-Hadamard question
explicitly left open per D1. §13 had no well-posed occurrence (verified by grep).

### R5 — Thorin substrate separation                                     [status: DONE 2026-09-01]

- §11 bold-claim paragraph split into the three statuses, labelled in place: (i) *proved,
  any positive weights* — admissible atomic truncations, weak convergence, in-class
  approximation (prop:thorin-subclass); (ii) *proved, integer weights* — exact finite
  first-order realization per increment (prop:gamma-cascade per node); (iii) *heuristic,
  real weights* — rational fitting per rem:local-implementation(iii)/oustaloup2000frequency,
  no error theorem claimed, and the constructive integer-weight approximation with bounds
  recorded as open in the text itself. Section intro's "reduces to banks" likewise graded
  ("approximated from inside the axiom class ..., exactly rational when the weights are
  integers").
- rem:local-implementation(iii): the log-state-count advertisement removed from the early
  remark; it now defers to the post-proposition heuristic paragraph (which already carried
  the honest "no error bound claimed" form). No "sections per decade" before that
  paragraph; §1 and abstract checked — their "first-order" claims attach to the Gamma
  family (exact) and to the weak-convergence clause, both proved, so unchanged per plan.
- Drift caveat added (practice paragraph): the pure delay is a time shift, exact on a
  sampled grid only at integer sample counts, otherwise a fractional delay approximated by
  standard interpolation/allpass designs, no error claim. The proposition's "exactly
  implementable as a sample delay" softened to "itself a pure time shift"; fig-filterbank
  caption "the drift's exact sample delay" -> "the drift's pure time shift".

### R6 — scoping batch (Issue 6 + appendix corrections)                  [status: DONE 2026-09-01]

- rem:markov-media: paper-only body paragraph added after the (verbatim-shared) remark
  naming its evidentiary status — context, its two without-proof claims belonging to the
  separate memory-line-inverse-problem article, with what IS proved (thm:locality's local
  case; the Gamma first-jump computation) stated; Table 1 medium row labelled
  "(context, stated without proof)".
- Kent sentence: DONE with R0.3.
- §13 strata: the dilation-closure sentence now separates the two truncations — the
  published construction's fixed-time-constant cascade (hypoexponential, discrete
  covariance only) from the truncated exponent's similarity family (admissible and fully
  covariant by prop:thorin-subclass, approximating the limit kernel from inside the class).
- Signed Laplace uniqueness: NEW paper-only cor:laplace-uniqueness-signed in §3 after the
  sigma-finite proposition (Jordan decomposition reduction, with proof). Cited at the four
  signed use-sites found by audit: prop:scale-evolution proof, lem:generator-properties(5),
  thm:scale-cauchy(3), cor:signaling-wellposed proof. All other uniqueness applications
  audited positive-measure-only (incl. R2's proof). Blueprint prose at the mirrored proofs
  keeps its shorthand — its record of correctness is the Lean proof; promotion of the
  signed corollary rides with the R1/R2 blueprint-promotion decision.
- Appendix: "identifies with the locality corner" -> "contains the local families
  classified in §10"; the V.2 endpoint sentence corrected in BOTH paper and blueprint
  (shared statement): the *coefficient* t - b0 x vanishes, phi_x vanishes below the
  endpoint but need not vanish at it; the post-V.2 paragraph explicitly labelled heuristic
  twice, with the gamma = 1 positive / gamma < 1 divergent illustration added and "the
  proved uniqueness lives at (V.1)" stated; the intro's two "exactly invertible" phrases
  reworded to the one-sided right-inverse form (D^(x) inverted, one composition order, not
  the cascade step Phi), matching the honest post-corollary body text.

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
