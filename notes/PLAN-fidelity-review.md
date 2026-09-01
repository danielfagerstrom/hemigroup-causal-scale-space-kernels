# Fidelity review: does the Lean prove what the article claims?

**Status: executed, P0–P6, 2026-08-15.** The cards, the findings ledger and the verdict are in
`REVIEW-fidelity.md`; this file is the plan they followed. Short answer: yes — no proved conjunct
is vacuous, junk-valued or weaker than the article's proof; eleven statement-tightenings and two
article-side corrections were landed on the way (commits `65505a5` … `0bee0a6` and after).
The method is packaged for other articles as article-kit's `fidelity-review` skill
(`article-kit/.claude/skills/fidelity-review/`, from `4ab8e7c`): this plan, generalised, plus
the card and review templates, the six agent prompts, and the F7 sweep script.

Written 2026-08-15, at the point where the formalisation is closed to what Mathlib allows.
Companion to `PLAN-chapters-8-12.md` (what is proved and why the rest is not) and
`DESIGN-formalization-strategy.md` (the `BF₀`/`LE` vocabulary decision). This plan is about a
different question: not *whether* the nodes are proved, but whether the proved statements are
the article's statements.

## 1. The question, sharpened

The kernel has checked every proof. What it has not checked — what nothing mechanical can
check — is the *statement*: that the Lean proposition a `\lean{}` tag points at means what the
blueprint node says, which means what the draft's numbered theorem says. That correspondence
was written by hand, mostly by the same sessions that wrote the proofs, and a proof-writer's
statement drifts toward what is provable. So the review is a fidelity audit, and it has a small,
closed list of ways a proved theorem can fail to be the claimed one:

| failure mode | what it looks like | why it is silent |
|---|---|---|
| **F1 vacuous hypothesis** | a hypothesis (or a field of a structure) that nothing satisfies, or only trivial things | the theorem is true and useless; `lake build` cannot tell |
| **F2 junk-value conclusion** | a conclusion that holds because a partial function returned its default: `Bochner integral = 0` when non-integrable, `Real.sSup ∅ = 0`, `x / 0 = 0`, `ENNReal.toReal ⊤ = 0`, `Real.log` of a non-positive, `mellin` of a non-convergent integrand | the equation is provable, and it does not say the article's sentence |
| **F3 weakened conclusion** | the Lean concludes strictly less: an existence where the article says unique, a.e. where the article says pointwise, "for some `c`" where the article says "for every `c` in the range", `A g = h` where the article says `g ∈ dom A` and `A g = h`, `(b₀,k)` where the article says "`F` of the form (7.1)" | each clause reads right; the missing clause is not there to read |
| **F4 strengthened hypothesis / narrowed domain** | an extra measurability or integrability hypothesis, `Ioi 0` for `Ici 0`, a `≤` where the article has `<` (or the reverse), a hypothesis quantified over more than the article demands (all `c'` vs. one `c`), a structure field that is a *normalisation* the article does not impose | the theorem is a special case; whether the article's readers are in it is the question |
| **F5 definitional divergence** | the Lean object is not the article's object: `zStar`, `StandingHypothesis`, `IsLocalOfOrder`, `inversionOperator`'s normalisation, `IsOneParameter`, `memoryKernel`, `potential kernel` "constructed against the specification" | every theorem about the object is correct and about something else |
| **F6 interface fidelity** | ledger A17 / A18 stated *stronger* than the cited source, or with a hypothesis the source has dropped | the only place an outright inconsistency can enter; everything downstream inherits it |
| **F7 proof-route divergence** | the blueprint proof cites Bernstein–Widder / Feller / a `\uses` edge; the Lean proves it another way (README already lists several: `prop:moments`, `thm:increments-bernstein`, chapter 9 Route B) | not a correctness issue; an *honesty* issue in the text of record and a `\uses`-graph issue |
| **F8 three-way drift** | draft (the article) ≠ blueprint (text of record, transcluded by the paper) ≠ Lean; the draft has Theorem 7.3 with "(χ, F) unique up to χ(1)=1", the blueprint has three nodes, the Lean has a bundle plus three halves | the paper transcludes the blueprint, so a blueprint that drifted from the draft *is* the published claim |

So: yes, the questions asked — did we prove the main statements or something weaker or
vacuous, are hypotheses too strong, are domains right, how faithful is the blueprint prose to
the Lean — are the right ones. They are F1–F5 and F7. Two are missing and are added above:
**F6**, because a mis-stated axiom is the one defect that makes *everything* suspect at once and
the ledger's page anchors were verified against the *source's* statement, not against the Lean
declaration's; and **F8**, because "the article's statements" live in `draft/` and the paper
reads them from the blueprint, so the audit is a three-column comparison, not two.

What is deliberately **not** on the list: re-verifying proofs (the kernel did that), style, and
whether the informal proofs are *complete* as mathematics (that is `draft-reviewer`'s job, and
independent of the Lean). F7 is the lowest priority of the eight — it changes exposition, not
what is true — and is done last.

## 2. Method: the fidelity card

Every audited node gets one card, and the review's output is the collection of cards plus a
findings ledger. A card is short and has a fixed shape, so that cards can be compared and so
that a fresh reader can check one in ten minutes:

```
### <node label>  ·  <draft numbering>  ·  <Lean declaration(s)>
Draft says:      <the statement, quoted or tightly paraphrased>
Blueprint says:  <ditto; note any difference from the draft>
Lean says:       <the statement with every project definition unfolded to Mathlib primitives —
                  what a reader who trusts Mathlib and nothing of ours has to accept>
Hypotheses:      <side-by-side; each Lean hypothesis classified: same / weaker / stronger /
                  absent-in-article / absent-in-Lean>
Conclusion:      <ditto; each Lean conjunct matched to an article clause; article clauses with
                  no Lean conjunct listed>
Junk-value audit:<every partial function in the statement and why its default cannot fire, or
                  which theorem rules it out>
Witness:         <a concrete F / family that satisfies every hypothesis at once — name of the
                  Lean `example` that says so>
Verdict:         faithful / faithful-with-note / weaker (say how) / stronger-hyp (say how) /
                  divergent-def (say how)
Actions:         <Lean strengthening, blueprint annotation, draft edit, or nothing>
```

Four techniques, in the order they are cheapest:

1. **Unfold to primitives.** For every definition in a headline statement, write out what it is
   in Mathlib terms (`#print`, and read the definiens). The Lean-says line is written from that,
   not from docstrings. Docstrings are the *claim*; the definiens is the fact. In particular:
   `laplace` (Bochner? `lintegral.toReal`?), `mellin` (Mathlib's, junk `0` off convergence),
   `mellinInv` (Mathlib's, with its `(2π)⁻¹` and `i` conventions — compare with Def. 11.3's
   normalisation), `inversionOperator` (total, docstring says so), `zStar` (`sSup` in `ℝ≥0∞`,
   docstring explains why), `levyExponentD` (`ℝ≥0∞`-valued; every `.toReal` downstream is an F2
   candidate), `kernel` (`Classical.choose` off A17), `repr` (chosen off `existsUnique_repr`).
2. **Witnesses.** For each headline theorem, a Lean `example` instantiating *all* its
   hypotheses simultaneously at a named model — the Gamma family (`GammaDensity.lean` identifies
   it with Mathlib's Gamma law, so it is the strongest anchor), the stable family, and the pure
   drift `b₀ > 0, k = 0`. A hypothesis no witness satisfies is F1 until shown otherwise; a
   witness that needs `hc' : c + 1 < zStar` and can only supply it for `γ > 2` (say) is a
   domain finding. These go in `Formalization/Hemigroup/Witnesses.lean` (sorry-guarded like the
   rest; nothing cites it) and are listed in `CIAxiomGuard.lean` so they cannot rot.
3. **Blind restatement.** A fresh `mathematician` agent that has *not* seen the Lean is given
   the draft statement and the project's definition files (`Family.lean`, `Construction.lean`,
   `MellinData.lean`, `InversionOperator.lean`, `LocalOperator.lean`) and asked to write the
   Lean statement it would expect. Diff against the actual one. This is the only technique that
   finds F3 — a missing conjunct is invisible when you read the conjuncts that are there.
4. **Adversarial vacuity.** A second fresh agent per Tier-1 node, prompted to *make the theorem
   trivial*: find a way the hypotheses are unsatisfiable, or a way the conclusion follows from a
   junk value without the mathematics. It reports either an attack or "no attack found, because
   ⟨named theorem⟩ rules it out". Cheap, and it is what F2 needs.

For F6, the technique is different: the librarian fetches the anchored page (SSV Thm 5.2 p. 49;
Prop. 5.17 p. 57 with Def. 5.14 p. 55), and the card compares the *source's* hypotheses and
conclusion clause by clause with the `axiom` declaration in `Interfaces.lean` — the direction
of every inequality of strength must be "axiom ≤ source". `AXIOMS.md` already carries a
hypothesis-translation note for A17; the card checks it rather than trusting it.

For F7/F8, the technique is a diff: for each Tier-1/2 node, the blueprint proof's cited
ingredients versus the Lean proof's actual imports and the `#print axioms` line; and the draft
statement versus the blueprint statement (the paper's `\input` of the blueprint node makes the
second the one that gets published).

## 3. Priority: what to audit, in order

Prioritised by (a) whether it is a headline claim of the article, (b) how much of the
development sits beneath it — an F5 in `def:cascade-family` invalidates every card above it —
and (c) how much hand-written statement there is to get wrong. Definitions come *before* the
theorems that use them, because a divergent definition makes the theorem's card meaningless.

### Tier 0 — the definitions everything stands on (audit first, one card each)

| object | file | what to look at |
|---|---|---|
| `CascadeCore` / `IsScaleCovariant` / `CascadeFamily` | `Family.lean` | (A1)–(A8), (ND) clause by clause against Def. 3.1. Known deliberate choices, to be *confirmed* not rediscovered: (A5) on `X₊` only; (A3) a.e. in and out; `S` bundled as data; (A7) on `{0 ≤ x ≤ y}` into `X`. Check `dilL1` is `D_σ` with the article's normalisation, `transL1` is `τ_a` with the article's sign. |
| `SelfDecomposableExponent` | `Construction.lean` | (7.1) as a structure: `ne_top` replaces the two integrability conditions (equivalence is *claimed* in the docstring — check it is a theorem or a ledger note); `k_zero : k 0 = 0` is a normalisation the article does not impose — F4 unless the article's `k` is on `(0,∞)` only (it is; then confirm no theorem's conclusion depends on `k 0`). Also: the article's `F ≢ 0` appears as `∃ s₀, 0 < s₀ ∧ F.exponent s₀ ≠ 0` — check that is equivalent to `F ≢ 0` and not merely implied by it. |
| `levyExponentD`, `levyExponent`, `laplace`, `laplaceL`, `IsCausal` | `SelfDecomposable.lean`, `Levy.lean` | `ℝ≥0∞`-valued; where each `.toReal` in a *statement* is protected by a finiteness fact. `IsCausal μ := μ (Iio 0) = 0` — the article's kernels are on `[0,∞)`; confirm no statement needs `μ (Iic 0)`. |
| `kernel`, `repr` | `Construction.lean`, `Representation.lean` | both are chosen (`Classical.choose`); every property used downstream must come through a named `_spec` lemma; check `IsProbabilityMeasure` and `IsCausal` are proved, not chosen. |
| `zStar`, `StandingHypothesis`, `profile`, `lawT₁`, `negMoment` | `MellinData.lean` | Def. 11.1: `F(∞) = ∞` is rendered `Tendsto toRealExponent atTop atTop` — fine only because `ne_top` holds; `z_*` in `ℝ≥0∞` (docstring is right and this card confirms it); the article's "equivalently `∫₀^∞ e^{-F} < ∞`" — is that equivalence proved anywhere? If not, note it as unproved-in-Lean, harmless. |
| `inversionOperator`, `inversionSymbol`, `RealisesAction`, `verticalStrip` | `InversionOperator.lean`, `InversionSymbol.lean` | Def. 11.3 against Mathlib's `mellinInv` normalisation; `inversionSymbol` indexed by the Mellin variable — write out `B(-z)` vs `inversionSymbol z` explicitly on the card, since Theorem 4′(2d) writes `B(1-z)` and the Lean writes `inversionSymbol (z-1)`; `RealisesAction.mellin_eq` conditioned on `H̃ ≠ 0` — matches the article's remark in the proof of 11.6(1), record where the article *states* it. |
| `IsLocalOfOrder`, `SatisfiesPMP` | `LocalOperator.lean` | Def. 12.1: "agrees on `C_c^∞` with a differential operator of order `n`" — this is the definition most likely to have been shaped by the proof (the classification lemma is an *iff*, so the definition is load-bearing in both directions). Compare with the draft's wording; check `IsTestFunction` (`MellinEuler.lean`) is `C_c^∞(0,∞)` or a proper subclass, and if a subclass, whether Def. 12.1 quantifies over the same one. |
| `IsOneParameter` | `SemigroupCase.lean` | Cor. 7.4: "`Φ_{x,y}` depends only on `y − x`" — check the rendering and the normalisation `g_{0,1}(1) = 1`. |
| `phillipsGenerator`, `memoryKernel`, `symbol`, potential kernel | `PhillipsGenerator.lean`, `MemoryKernel.lean`, `PotentialKernel.lean` | Def. 10.2 and Lemma 9.1/9.4: `memoryKernel` is `−dk` dilated; the potential kernel is *constructed* as the subordinator's potential measure ("against the specification") — the card must state which specification and show the node's statement is the article's, not the construction's. |

### Tier 1 — the article's headline claims

1. **`thm:main-characterization` (Theorem 7.3 = Theorem 2′)** — `main_characterization`,
   read *through its three halves* `SelfDecomposableExponent.cascadeFamily`,
   `CascadeCore.main_analysis`, `gauge_and_exponent_unique`. Things already noticed in a first
   scan, to be settled on the card:
   * **(⇒) does not conclude in the article's terms.** It yields `χ, b₀, k` with
     `Fam.Φ x y = mconvL1 (Fam.repr x y)` and a Laplace identity written with
     `(levyExponentD b₀ k _).toReal`. It does **not** assert `levyExponentD b₀ k s ≠ ⊤`, does not
     produce an `F : SelfDecomposableExponent`, and does not say `Fam.repr x y = F.kernel (χ x) (χ y)`.
     Finiteness is presumably *forced* (a probability measure's transform lies in `(0,1]`, and
     `toReal ⊤ = 0` would break that), but the reader has to derive it; and the article's
     sentence is "there exist χ and F of the form (7.1) with `Φ_{x,y} f = μ_{x,y} ∗ f`,
     `μ̂_{x,y} = exp[−(F(χ(y)s) − F(χ(x)s))]`". Candidate action: a **round-trip corollary**
     `∃ χ F, … ∧ ∀ x y, Fam.Φ x y = mconvL1 (F.kernel (χ x) (χ y))`, so that ⇒ lands in the
     type ⇐ starts from. That is F3 unless the derivation is written down.
   * **Uniqueness** is stated for two `SelfDecomposableExponent`s and a `χ` with *equal kernels*
     `F'.kernel (χ u) (χ v) = F.kernel u v`; the article says the pair `(χ, F)` representing a
     given *family* is unique. The bridge is injectivity of `μ ↦ mconvL1 μ` (or
     `existsUnique_repr`) — confirm it is available and record which lemma; the χ hypotheses
     (positive, monotone non-strict, `→ 0`) are *weaker* than "increasing bijection", which is
     the good direction, and the card says so.
   * (⇐) is a `def` (`cascadeFamily`) with `hF : ∃ s₀, 0 < s₀ ∧ F.exponent s₀ ≠ 0`; the bundle
     turns it into `∃ Fam, ∀ x y, Fam.Φ x y = mconvL1 (F.kernel x y)`. Confirm the witness's `S`
     is `σ·x` (the article's canonical gauge) — the bundle does not say so.
   * The whole `#print axioms` story (A17 on ⇐ and uniqueness, A18 on ⇒) is already CI-checked;
     the card just cites the guard lines.
2. **`thm:signaling-form` (Theorem 11.6 = Theorem 4′)** — `signaling_form`. Already noticed:
   * **(3) uniqueness** hypothesises `RealisesAction c' B …` for *every* `c'` in the range;
     the article says "unique operator in the covariant Mellin class with property (1)", and (1)
     itself is stated "for every `c ∈ (0, z_*−1)`". So the quantifier is probably the article's
     — but Lemma 11.4's hypothesis and Def. 11.3's "fix `c`" need to be read together, and the
     card decides F4-or-faithful. Also: the conclusion is `=ᶠ[𝓝[≠] z]` — agreement as germs on
     the strip. Article: "agrees with `B` as a meromorphic function on the strip". Same thing if
     `B` is meromorphic; the Lean does not assume `B` meromorphic, so it concludes less about
     an object it assumes less about. Faithful-with-note, probably; write the note.
   * **(2d)** carries `mellin (profile) (z − 1) ≠ 0` as a hypothesis. The article's proof says
     "valid wherever that does not vanish, which is all of the strip off an isolated set". So
     the *statement* in the article is stronger than the Lean (it asserts the identity on the
     strip; the Lean asserts it off the zeros of `H̃`). Either the article's statement should
     say "off the zeros of `H̃(z−1)`", or the Lean should show the zero set is discrete and the
     identity extends by continuity. F3/F8 — decide which side moves.
   * **(2d) junk audit**: both sides are Mathlib `mellin` (Bochner, junk `0`). The identity is
     nontrivial only if the left side's `MellinConvergent` is proved on the strip. Find the
     lemma (`lem:mellin-data`, `lem:delayed-average-mellin`) and cite it on the card.
   * **(2b)** is stated for all `q : X` and `Φ 0 x q → q` — stronger than the article's
     `u(·,x) → f`; note as such.
   * **(1)** is stated only for `x > 0`, `s > 0`, and `hc' : c + 1 < zStar` — matches Def. 11.3's
     `c ∈ (0, z_*−1)`; confirm `c > 0` (article) vs `0 < c` (Lean) and that the *domain* clause of
     the article ("`H(s·)` is in the domain of Definition 11.3") has a Lean counterpart —
     `inversionOperator` is total, so the domain claim lives in `RealisesSymbolAction`; check the
     theorem (or a sibling) asserts it, else F3.
   * Hypotheses on `f`: `Measurable g`, `Integrable g`, causal `g`, `Measurable f`,
     `Integrable f`, `f = ∫₀^· g`. Compare with `MemCore` (`DelayCore.lean`) — README says
     `memCore_iff_signaling_hypotheses` is an equivalence; the card cites it and closes F4.
3. **`thm:main-analysis` and its supply chain** (chapters 4–6): `existsUnique_repr`,
   `additivity`, `increments_bernstein` (`thm:increments-bernstein`), `strict_monotonicity`,
   `covariance_laplace`, `action_rigidity`, `canonical_gauge`, `similarity_form`. Each is a
   short card; the point is F3/F4 accumulation — a `≤` that became `<` in chapter 5 propagates
   to the main theorem's hypotheses silently.
4. **Ledger A17, A18** (`Interfaces.lean`) — F6, one card each, source pages fetched by the
   librarian. Specific things to check: A17's `hfin` is "finite at every `s ≥ 0`" where the
   source has `∫ (1∧t) ν(dt) < ∞` (docstring argues equivalence — verify the direction *used*,
   which is source ⇒ axiom-hypothesis satisfiable, i.e. the axiom asks no more than the source
   gives); A18's `hincr` asks increments for `0 < a ≤ b` and concludes with no `k 0`
   normalisation and no integrability clauses (docstring says these are consequences — confirm
   `levyExponentD c₀ k s = ofReal (F s) ≠ ⊤` indeed yields them, in a lemma, not in prose).
   Also confirm neither axiom is *stronger* than needed by its one consumer, so that its scope
   is minimal (README claims this; the card checks it).
5. **`cor:semigroup-case` (Cor. 7.4)** — recovers the 2005 kernels; a natural cross-check
   because the target statement is independently known. `IsOneParameter` fidelity (Tier 0) plus
   the conclusion `F(s) = s^α, 0 < α ≤ 1` — check the `α = 1` pure-delay case is included and
   the `α > 1` case is *excluded by the theorem*, not by the definition.

### Tier 2 — the "theorem content" the introduction promises

6. **`thm:sonine-conservation` (Thm 9.5)** and `lem:potential-kernel`, `lem:memory-kernel`,
   `prop:sonine-pair-exists`, `prop:volterra` — chapter 9's Route B means the *objects* were
   built differently from how the article defines them; each card must show the object is the
   article's (F5), then that the identity is the article's.
7. **`lem:generator-properties` (Lemma 10.3)**, `def:phillips-generator`, `lem:delay-core` — five
   clauses; the symbol clause `φ_x(s) = sF'(xs)` uses `deriv toRealExponent` — F2 audit
   (`deriv` is junk `0` where not differentiable; where is differentiability proved?).
8. **`lem:local-polynomial-symbol` and the chapter-12 chain** (`lem:local-moment-classification`,
   `lem:gamma-recursion-uniqueness`, `lem:pmp-verification`) — Theorem 5′'s proved part. The
   iff's *definition side* is Tier 0; here check that "the corresponding polynomial" is the
   article's polynomial (coefficients, degree, sign) and that "read off the zeros of `H̃`" is
   stated, not only used.

### Tier 3 — the rest

9. Chapter 8 (`prop:admissibility-criterion`, the families, `prop:moments`, `prop:gamma-*`,
   `prop:stable-moments`) — low risk (concrete), high value as *witnesses* for Tier 1; do the
   witness file first and the cards will mostly write themselves.
10. Chapter 2 refinements (`prop:laplace-uniqueness-causal`, `-sigma-finite`, `-continuity-causal`,
    `lem:transform-tightness`, `lem:vanishing`) — check each `[T]` refinement's statement is the
    restricted case the article *uses*, and that the `[A]` parent's `\uses` still point at it.
11. F7 sweep — for every `\leanok` node, blueprint-proof ingredients vs. Lean-proof ingredients;
    where they differ, the blueprint gets a one-line "The formal proof takes a different route:
    …" note (some already exist), and any `\uses` edge the Lean does not need is reviewed (kept
    if the *text's* proof needs it, since the blueprint proof is the publication text).

## 4. Deliverables

* `blueprint/REVIEW-fidelity.md` — the cards (Tier 0–2 in full; Tier 3 abbreviated) and a
  **findings ledger** at the top: one line per finding, tagged F1–F8, with severity
  (*claim-changing* / *statement-tightening* / *note-only*) and its resolution commit.
* `Formalization/Hemigroup/Witnesses.lean` — the `example`s of §2(2), listed in
  `CIAxiomGuard.lean`.
* Fixes, each its own commit, in the direction the finding dictates: Lean strengthening (e.g.
  the round-trip corollary for Theorem 2′), blueprint statement or annotation edit (with a
  `\LE`-reading where the conclusion is in `BF₀`, per CLAUDE.md), draft edit where the draft is
  the one that is loose. Every fix re-runs the full gate (`lake build`, `CIAxiomGuard.lean` to
  completion with exit code checked, `scripts/build-blueprint.sh`, `linkage check`).
* README/`PLAN-chapters-8-12.md`: no change unless a finding changes the status table.

## 5. Execution

Sequenced so that nothing is audited against a definition that has not itself been audited.

| phase | scope | how | rough size |
|---|---|---|---|
| **P0** | Tier 0 cards | me, by unfolding; one `mathematician` agent per definition file for the blind restatement of the *definition* from the draft | 9 cards |
| **P1** | Witnesses file | one `mathematician` agent: instantiate every hypothesis of `main_characterization`, `signaling_form`, `cor:semigroup-case`, `lem:local-polynomial-symbol` at the Gamma family (`γ > 1`, then `γ > 2` if `hc'` needs it), the stable family, and pure drift | 1 file, ~150 lines |
| **P2** | Tier 1 cards 1–2 | for each: (a) my unfolded Lean-says line, (b) blind restatement by a fresh agent, (c) adversarial-vacuity pass by a second fresh agent, (d) merge; the two already-noticed items (round-trip; (2d)'s zero set) go straight to the findings ledger for decision | 2 cards, likely 2–4 fixes |
| **P3** | Tier 1 cards 3–5 (supply chain, A17/A18 with librarian page fetch, Cor. 7.4) | as P2 but a single agent per card | ~12 cards |
| **P4** | Tier 2 | one agent per chapter | ~10 cards |
| **P5** | Tier 3, F7 sweep, F8 draft↔blueprint diff | scripted where possible (`linkage` already knows the `\lean` tags and `\uses` edges; a script can list, per node, blueprint-proof `\ref`s vs. Lean imports); agents only for the residue | 1 script + notes |
| **P6** | Findings ledger closed; every finding resolved or recorded as accepted-with-note | me | — |

Rules of engagement, drawn from CLAUDE.md and from what this review is for:

* An agent auditing a statement **does not get to see its proof first**, and the blind
  restatement is written before the actual Lean statement is read. Order matters; it is the whole
  value of the technique.
* A finding is *not* fixed inside the card-writing pass. It goes to the ledger with a proposed
  direction (Lean up / blueprint down / draft edit), and the fix is a separate commit that names
  the finding. Statement-changing fixes to Tier 1 are confirmed with the author before landing;
  note-only ones are not.
* "Faithful" on a card requires a **witness** and a **junk-value audit** line; a card without
  both is not done.
* Any card that touches a `\lean` tag re-checks that the tag points at the declaration that
  proves *all* of the node's clauses (the `thm:signaling-form` lesson) — not a sibling that
  proves the headline one.
* Commit and push after each card batch, explicit paths only.

## 6. What "done" looks like

Every Tier 0–2 node has a card with a verdict; every non-faithful verdict has a ledger entry
that is either resolved by a commit or explicitly accepted with the reason in the blueprint's
annotation of that node; `Witnesses.lean` shows the headline theorems' hypotheses are jointly
satisfiable at three named models; and the article's Theorem 2′ has, if the P2 decision goes
that way, a round-trip statement in which the analysis direction concludes in exactly the type
the construction starts from.
