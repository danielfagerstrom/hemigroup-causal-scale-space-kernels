# Audit: `\lean{}` declarations that state less than their node (Q-0138)

2026-09-26. A report, not a fix: no node, tag, Lean file, `AXIOMS.md` or `trust-boundary.txt` was
changed. It is the input to Q-0139, the author's decision on whether a node with a partially
formalized statement is split, as `lem:potential-kernel-scaling` was split from
`lem:potential-kernel`, or kept whole.

## Method

Every node in `blueprint/src/parts/*.tex` that carries `\lean{}` was read. That is **71 nodes**,
all with `\leanok` on the statement, and every one with a proof has `\leanok` on the proof too.
For each node:

1. The statement's clauses were listed: numbered items, the two directions of an iff, the parts
   of a conjunction, any "in particular", "consequently" or "moreover".
2. The type of each declaration named in `\lean{}` was read from `Formalization/Hemigroup/`,
   down to its `:=`.
3. Each clause was marked as covered by those types or not. A clause counts as covered when it
   follows from them by a definitional unfolding or a one-step logical move (transitivity, or
   instantiating at a point). It does not count as covered when it needs a separate declaration,
   even one that exists.

Two kinds of shortfall came out, and they call for different fixes:

- **Kind U, unstated.** No Lean declaration states the clause.
- **Kind L, unlisted.** A declaration states the clause, usually one the node's own annotation
  names, but it is missing from the node's `\lean{}`. Nothing checks it against the node. The
  cheap fix is to add it to `\lean{}`; no split is needed.

For orientation, `linkage check` was run once (read-only). It passed with `LINKAGE CHECK OK`: 106
nodes, 71 with `\leanok`. The only advisories are the two known `[depend]` ones and the `[uses]`
paper-reference ones. `lake build` was not run, since this audit reads types and proves nothing.

**Confidence scale.** *High*: the clauses are numbered or the connective is explicit, and the
Lean type can be read unambiguously. *Medium*: the clause boundary is prose ("i.e.",
"consequently") or the reading of the Lean needs a step. *Low*: whether the text makes a claim at
all is a matter of interpretation.

## Flagged nodes: at least one clause not stated by any Lean declaration (kind U)

S = `\leanok` on the statement, P = `\leanok` on the proof ("—" means a definition, which has no
proof block).

| Node | Clauses stated | Clauses in the named Lean | Clauses missing | S / P | Recommendation | Confidence |
|---|---|---|---|---|---|---|
| `prop:pair-regularity` (ch. 9) | (1) ℓ⁽ˣ⁾ = cδ₀ + nonincreasing density ⇔ 1/F′ ∈ BF, x-independent; (2a) κ_c CM ⇔ k CM; (2b) k CM ⇔ F′ ∈ 𝒮; (2c) then ℓ_c is CM, so (κ_c, ℓ_c) is a CM Sonine pair; (2d) k CM ⇒ F ∈ CBF | (2a), (2b) (`hasCMDensity_iff`, in the representation idiom) | (1), (2c), (2d), which are exactly where A9 enters | ✓ / ✓ | **Split.** A child (e.g. `prop:pair-regularity-special`, a number the draft does not use) holding (1), (2c) and (2d), with `\ledger{A9}` and `\uses{prop:pair-regularity, lem:potential-kernel, thm:sonine-conservation}`. The parent keeps (2a)–(2b) and its tag and becomes [T] (reading the predicates as CM is A1, spent in the statement). `prop:thorin-subclass` and `rem:sonine-literature` would then `\uses` whichever half they read. | High: numbered clauses, and the annotation already says the same |
| `def:inversion-operator` (ch. 11) | (a) the definition (Ag)(x) = x⁻¹(2πi)⁻¹∫₍c₎ x⁻ᶻ B(−z) g̃(z) dz; (b) the display "= (x⁻¹B(θ)g)(x)", i.e. that such a function B(θ)g exists | (a) (`inversionOperator`, defined for every g) | (b), the functional-calculus reading, which is ledger A12. A12 is not a Lean axiom, so the tag does not close it modulo an interface. | ✓ / — | **Split**, for the same reason as `prop:pair-regularity`: this is the same defect (`\leanok` together with a clause resting on a ledger entry that is not a Lean axiom). The child is a lemma or remark with the second display, `\ledger{A12}`, `\uses{def:inversion-operator, lem:inversion-symbol}`; the definition becomes pure [T]. **Or leave**, if Q-0139 accepts [A] on a definition whose article use is empty (`lem:profile-eigenfunction` shows it is). | Medium: the second display reads as a rewriting, and only the annotation says it is a claim |
| `lem:memory-fractional-integrals` (ch. 11) | (a) f ∈ X₀ causal: ũ(t,·)(z) = H̃(z)(I^z f)(t) for 1<Re z<z*, absolutely convergent; (b) f ∈ core: the same for ∂_t u with I^{z−1}f; (c) "in that case the identity extends to 0<Re z<z*" | (b) at 1<Re z (`mellin_delayedField_deriv`), without the convergence claim | (a) is kind L (`mellin_delayedField`, tagged on its child `lem:delayed-average-mellin`); the absolute convergence is kind L (`mellinConvergent_delayedField[_pair]`); (c) has no declaration | ✓ / ✓ | **Split (c)**, if it is kept as a claim: a child "the wider strip for core signals", `\uses{lem:memory-fractional-integrals, lem:delayed-average-mellin}`. Read as the u-identity for bounded f, (c) is `mellin_delayedField` with `integrableOn_pastIntegrand_of_bounded`, so a one-line Lean corollary would do instead. Widen `\lean{}` for (a) and the convergence. No `\leanok` consumer reads (c): `thm:signaling-form` works at 1<Re z. | Low for (c), because it is ambiguous whether "the identity" is u's or ∂_t u's; high for the rest |
| `lem:zstar-log-growth` (ch. 11) | (1) lim F/log s exists, = z*; (2) = ∞ if b₀>0, = k(0⁺) if b₀=0; (3) (H) ⇔ b₀>0 or k(0⁺)>1; (4) z*(cF) = c z*(F) | (1), (2), (4) | (3); the annotation says it "has no declaration of its own" | ✓ / ✓ | **Leave**, and state (3) as a Lean corollary. It is (1) and (2) read against `def:standing-hypothesis` with no new mathematics, so a corollary is cheaper than a split. If Q-0139 makes splitting the rule, the child is (3) with `\uses{lem:zstar-log-growth, def:standing-hypothesis, lem:standing-levy-reading}`. The clause is a practical criterion readers will use (`rem:signaling-stability` reads the node). | High |
| `lem:local-moment-classification` (ch. 12) | (i) **exactly one** of m(z) = c′^z or m(z) = q₁^z Γ(a+z)/Γ(a); (ii) "that is, T₁ = 1/c′ a.s. or T₁ =ᵈ 1/(q₁γ_a)" | the disjunction of (i), without exclusivity | the exclusivity; (ii), the identification of the law, which needs determinacy of the law by its negative moments | ✓ / ✓ | **Leave** the exclusivity: the two forms cannot agree, since log Γ is strictly convex, and the claim is decorative. For (ii), **split or reword.** Either a child carrying the identification of the law, `\uses{lem:local-moment-classification, prop:laplace-uniqueness-causal}` (or Mellin injectivity, which is not in the development), or reword "that is" as "equivalently at the level of negative moments". The annotation already says moments are "the whole of what is reachable". | Medium: (ii) is an "that is" gloss, but it asserts a law |
| `lem:covariance-laplace` (ch. 6) | (1) ⇔ (2) ⇔ (3), and (6.1) under (A8) | (1)⇒(2), (1)⇒(3), (6.1) (`covariance_laplace`) | (2)⇒(1) is kind L (`isScaleCovariant_of_repr_map`); (3)⇒(2) has no declaration (the annotation says it "needs no further declaration") | ✓ / ✓ | **Leave**, widen `\lean{}` with `isScaleCovariant_of_repr_map`, and state (3)⇒(2) in Lean (Laplace injectivity plus injectivity of −log; a few lines). Every `\leanok` consumer (`lem:action-rigidity`, `prop:canonical-gauge`, `thm:main-analysis`, `cor:semigroup-case`) reads only (1)⇒ and (6.1). A split would orphan a two-line converse. | High |
| `cor:semigroup-case` (ch. 7) | F(s)=s^α, 0<α≤1; "i.e." the kernels are the extremal stable densities, with α=1 the pure delay μ₀,ₓ = δₓ | F(s)=s^α and α∈(0,1], plus G(x,s) = x s^α and S_σx = σ^α x | the kernel identification, in particular μ₀,ₓ = δₓ at α=1 | ✓ / ✓ | **Leave.** It is a naming gloss on F: the kernel is determined by F through `thm:main-characterization`, and δₓ is Laplace uniqueness at e^{−xs}. | Medium |
| `prop:main-uniqueness` (ch. 7) | χ = Id (on [0,∞)) and F′ = F | χ u = u for u>0; F′ = F on [0,∞) | χ(0) = 0 (the Lean monotonicity hypothesis is on (0,∞) only) | ✓ / ✓ | **Leave.** It follows in one line from the node's own hypotheses (nondecreasing, ≥ 0, χ(0⁺)=0). | High |
| `lem:memory-kernel-transform` (ch. 9) | κ⁽ˣ⁾ locally finite; ∂ₓF(xs) = sF′(xs) = s κ̂⁽ˣ⁾(s) | κ̂⁽ˣ⁾(s) = φₓ(s)/s, with φₓ(s) := sF′(xs) by definition (`symbol`) | the chain-rule equality ∂ₓF(xs) = sF′(xs); local finiteness of κ⁽ˣ⁾ | ✓ / ✓ | **Leave.** The chain rule on `lem:memory-kernel` is a motivating aside, and local finiteness is used, not claimed. | Medium |
| `lem:moment-recursion-quotient` (ch. 12) | γ₀=0; Q := −Σγ_{k+1}E_k(z+1) explicitly; P = zQ; Q(z) > 0 real, with m(z+1) = Q(z)m(z) on (0, z*−1) | ∃Q with P = zQ everywhere and positivity and recursion on the range | the explicit formula for Q; γ₀=0 is not stated, but it follows from P = zQ at z = 0, since E_j(0)=0 for j≥1 | ✓ / ✓ | **Leave.** γ₀=0 is a one-step instance, and the explicit Q is presentation (the annotation explains why no `Polynomial` is used). | High |
| `prop:admissibility-criterion` (ch. 8) | F(s) < ∞ for all s≥0; "consequently" F is of the form (7.1), and main-characterization applies | finiteness | the "consequently" sentence | ✓ / ✓ | **Leave.** The annotation already declares it "a consequence and not part of the statement". The construction is the structure literal (`gammaExponent` and `dickmanExponent` do it). | High |
| `lem:potential-kernel-scaling` (ch. 9) | ℓ⁽ˣ⁾ = x · (t↦xt)₊ℓ⁽¹⁾; "in density form ℓ⁽ˣ⁾(t) = ℓ⁽¹⁾(t/x)" | the measure identity | the density form (ℓ need not have a density) | ✓ / ✓ | **Leave.** It is a reading under an assumption the node does not make. | High |

## Flagged nodes: every clause stated in Lean, but not all by the declarations in `\lean{}` (kind L)

For all of these the recommendation is **leave, and widen `\lean{}`**. The clause is
machine-checked, and every declaration below is listed in `CIAxiomGuard.lean` except
`increment_density_nonneg`. Only the tag's list is short. All have `\leanok` on the statement and,
where there is a proof, on the proof.

| Node | Clause not covered by the named declarations | Where it is stated | Confidence |
|---|---|---|---|
| `lem:transform-tightness` (ch. 2) | "Consequently a family ... is tight" | `exists_tail_le_of_forall_laplace`, `isTightMeasureSet_of_forall_laplace` (named in the annotation) | High |
| `prop:canonical-gauge` (ch. 6) | c(σ)=S_σ1 is continuous; c(1)=1, i.e. χ(1)=1; F ∈ LE; F ≢ 0 | `action_rigidity`(3) at z=1; `gauge_one`; `exponent_hasLevyRep` at (0,1); `strict_monotonicity` / `exists_exponent_ne_zero`. The last two are "carried along" from other nodes, as the annotation says. | Medium: the node restates facts carried from its parents, and the reader may not count those as claims |
| `thm:main-characterization` (ch. 7) | (⇐) for an **arbitrary** increasing bijection χ; the bundle's (⇐) is the canonical gauge only | `CascadeFamily.reparam`, `cascadeFamily_reparam` (the annotation of `thm:main-construction`, finding R8). The bundle would need a fourth conjunct, or the node a second name. | Medium: "there exist χ and F" in an iff is read here as quantifying χ in the (⇐) direction |
| `lem:selfdecomposable-increment` (ch. 7) | G_{a,b} ∈ LE with density exactly (k(u/b)−k(u/a))/u, which needs that density ≥ 0 (`levyExponentD` truncates by `ofReal`) | `increment_density_nonneg` (**not** in `CIAxiomGuard.lean`) | High |
| `lem:dickman-superposition` (ch. 7) | (2) holds for **any** ρ with the tail property, not just for some | `exponent_eq_lintegral_ein` (the bundle states ∃ρ) | High |
| `prop:moments` (ch. 8) | E Tₓ = x F′(0⁺): the identification of the mean rate with the derivative at 0⁺ | `tendsto_ofReal_inv_mul_exponent` (difference quotients along decreasing sequences, in [0,∞]) | Medium: the Lean form is sequential and one-sided, which is the right reading of F′(0⁺) in [0,∞] |
| `lem:potential-kernel` (ch. 9) | φₓ is a nonzero Bernstein function, positive on (0,∞) | `exists_levyTriple_symbol`, `symbol_pos` (the annotation, finding R21). The clause is stated **only in BF**, with no LE reading beside it, which is the case `CLAUDE.md`'s two-vocabularies rule forbids for a tagged conclusion. | High |
| `thm:sonine-conservation` (ch. 9) | the identity as displayed, κ*ℓ = Leb_{[0,∞)} on ℝ; the tagged declaration is the restriction to [0,∞) | `sonine_conservation'` (the annotation, finding R23) | High, but minor: the two are equivalent for causal measures |
| `lem:mellin-data` (ch. 11) | the bound \|H̃(c+iτ)\| ≤ E[T₁^{−c}]\|Γ(c+iτ)\| | `norm_mellin_profile_le` (named in the annotation) | High |
| `lem:inversion-symbol` (ch. 11) | H̃ analytic on the strip; H̃ ≢ 0; the closed form B(−z)=z m(z+1)/m(z); poles only at the isolated zeros | `analyticAt_mellin_profile`, `mellin_profile_ofReal_ne_zero`, `eventually_mellin_profile_ne_zero`, `inversionSymbol_eq`, `analyticAt_inversionSymbol` (all named in the annotation). The tagged declaration covers only "B is meromorphic". | High |
| `lem:symbol-rigidity` (ch. 11) | pointwise agreement where both are continuous | `eq_of_continuousAt` (also `eqOn_of_ne_zero`, `eqOn`) | High |
| `lem:inversion-operator-action` (ch. 11) | Mellin(Ag)(z) = h̃(z−1) for every z; "in particular" = B(1−z)g̃(z−1) | `mellin_inversionOperator`, `mellin_inversionOperator_eq` (named in the annotation) | High |
| `lem:profile-eigenfunction` (ch. 11) | the domain clause: H(s·) is in the domain, with realising function s x H(sx) | `realisesSymbolAction_profile` (named in the annotation; already a conjunct of `signaling_form`) | High |
| `lem:delayed-average-mellin` (ch. 11) | the first display Φ₀,ₓf = E[f(·−xT₁)] a.e.; both sides absolutely convergent; the node's hypotheses (f ∈ L¹, Re z>1) in place of the Lean's `hpast` | `coeFn_Phi_zero`; `mellinConvergent_delayedField`; `integrableOn_pastIntegrand` (which discharges `hpast`) | High |
| `def:locality-pmp` (ch. 12) | the second definition, the positive maximum principle | `SatisfiesPMP` (named in the annotation) | High |
| `lem:local-polynomial-symbol` (ch. 12) | the coefficient form c_j(x) = γ_j x^{j−1}, and A = x⁻¹B(θ) | `exists_symbol_eq_of_isLocalOfOrder`, `coeff_eq_of_isLocalOfOrder`. The annotation says the tagged equivalence "says less than its halves". | High |
| `lem:symbol-vanishes-at-origin` (ch. 12) | m(z) → 1 as z↓0 | `tendsto_negMoment_nhdsGT_zero` (named in the annotation) | High |
| `lem:pmp-verification` (ch. 12) | the general first sentence: any order-≤2 expression with Re c₀ ≤ 0 and Re c₂ ≥ 0 satisfies the PMP. The tagged declaration is only the "in particular" symbol form, and it adds (H) and c < z*−1, which that sentence does not assume. | `satisfiesPMP_of_isLocalOfOrderCore` | High |

## Nodes examined and found complete (41)

Chapter 2: `lem:vanishing`\*, `def:levy-exponent`, `prop:laplace-uniqueness-causal`,
`prop:laplace-uniqueness-sigma-finite`, `lem:laplace-local-finiteness`,
`prop:laplace-continuity-causal`.
Chapter 3: `def:cascade-family`.
Chapter 4: `lem:convolution-representation`, `lem:transform-continuity`.
Chapter 5: `lem:additivity`, `thm:increments-bernstein`\*, `cor:strict-monotonicity`.
Chapter 6: `lem:action-rigidity` (clause (1), "S_σ is determined by (6.1)", is read off the
injectivity conjunct; medium confidence).
Chapter 7: `thm:main-construction`, `thm:main-analysis`, `lem:admissible-cone`.
Chapter 8: `prop:stable-family`, `prop:gamma-family`, `lem:criterion-converse`†,
`prop:gamma-kernels`, `prop:gamma-density`, `prop:gamma-moments`, `prop:stable-moments`.
Chapter 9: `lem:memory-kernel`, `prop:volterra`, `prop:volterra-uniqueness`,
`prop:sonine-pair-exists` (the ℓ of the ∃ is ℓ⁽ˣ⁾ because the identity fixes its transform).
Chapter 10: `lem:delay-core`, `def:phillips-generator`, `lem:generator-properties`.
Chapter 11: `def:standing-hypothesis`, `lem:symbol-uniqueness` (the two-operator form follows by
transitivity of the germ equality through A's own symbol), `thm:signaling-form` (clause (3)'s "in
particular" is read as the annotation reads it, as a remark and not a uniqueness claim over (2)),
`lem:mellin-vertical`, `lem:signaling-mellin-form`, `lem:fractional-integral-derivative`,
`lem:standing-kernel-readings`, `lem:standing-levy-reading`, `lem:mode-rigidity`.
Chapter 12: `lem:log-convexity`†, `lem:gamma-recursion-uniqueness`.

\* A vocabulary bridge, not a partial cover. `thm:increments-bernstein` gives the LE reading
beside the BF₀ one, as `CLAUDE.md` requires. **`lem:vanishing` is stated in BF₀ only**; the LE
reading is in its status note, not in the statement. That is the case `CLAUDE.md`'s
two-vocabularies rule says cannot carry `\lean`. The fix is to move the LE sentence into the
statement, not to split.
† Complete as to clauses, but see the hypothesis drift below.

Chapters 13 and 14 carry no `\lean{}` tags.

## A different defect: `\lean{}` names that are gone, and types that have drifted

**No name has gone.** `linkage check` resolves every `\lean{}` declaration, and a text search
found each one in `Formalization/Hemigroup/`.

**Hypothesis drift.** In these nodes, the tagged declaration assumes more than the node does, so
the node claims more than the Lean proves. None of them has a clause missing; the shortfall is in
the hypotheses.

- `lem:criterion-converse`. The node's point is that finiteness of the exponent **at the single
  point s=1** forces both integrability conditions. `integrableOn_of_ne_top` takes a whole
  `SelfDecomposableExponent`, whose `ne_top` field is finiteness at **every** s ≥ 0, and it also
  takes `k_zero`. The docstring says the proof uses only s=1, but the type does not show it.
  Recommendation: restate the Lean over (b₀, k) with a single-point hypothesis, as
  `levyExponentD_ne_top_of_integrableOn` already is for the forward direction, or soften the node.
  High confidence.
- `lem:log-convexity`. The node says log-convex on **(0,∞)**, with no hypothesis. The Lean is
  `ConvexOn` on `momentInterval` = (0, z*), under `lawT₁ {0} = 0`. The annotation explains why,
  and the unconditional [0,∞] form is `negMoment_le_rpow_mul_rpow`. Recommendation: put (0, z*)
  and the no-atom hypothesis into the statement, or add the [0,∞] declaration to `\lean{}`. High
  confidence.
- `lem:inversion-operator-action`. The node says "Fix c > 0" and assumes no (H).
  `inversionOperator_eq` requires `StandingHypothesis` and c < z*. Recommendation: state (H) and
  the strip in the node. High confidence.
- `lem:pmp-verification`. The tagged declaration requires (H) and c < z*−1 (see the table above);
  the general `satisfiesPMP_of_isLocalOfOrderCore` does not.
- `lem:zstar-log-growth` (1) and (4). These carry the no-atom hypothesis instead of the node's
  F ≢ 0. The two are bridged by `standing_levy_reading`(2) and `standing_kernel_readings`(1),
  both proved, as the annotation says. This is not a defect, only a chain a reader has to supply.
- `lem:delayed-average-mellin`. `hpast` is in place of "f ∈ L¹, Re z > 1"; the bridge is
  `integrableOn_pastIntegrand` (see the kind-L table).

## Counts

- 71 nodes examined; 41 complete.
- 12 with a clause no Lean declaration states (kind U). Of these, two have the defect of the
  `prop:pair-regularity` shape: `\leanok` on a node with a clause that rests on a ledger entry
  that is not a Lean axiom. They are `prop:pair-regularity` (A9) and `def:inversion-operator`
  (A12). One more has a claim-bearing clause with no Lean at all (`lem:zstar-log-growth`(3)).
  The other nine are glosses, asides or one-step consequences.
- 18 whose missing clauses are all machine-checked under a name not in `\lean{}` (kind L).
- 6 with hypothesis drift. Four of them (`lem:criterion-converse`, `lem:log-convexity`,
  `lem:inversion-operator-action`, `lem:delayed-average-mellin`) are otherwise complete or kind L;
  the other two (`lem:pmp-verification`, `lem:zstar-log-growth`) also appear above.
- 0 dangling `\lean{}` names.
