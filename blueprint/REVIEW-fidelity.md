# Fidelity review — cards and findings

Executes `PLAN-fidelity-review.md`. Cards follow the shape fixed there; the findings ledger is
at the top so that the state of the review is readable without the cards. Started 2026-08-15
with P0 (Tier 0 definitions) and P1 (the witnesses file).

Conventions. *Draft* = `draft/hemigroup-causal-scale-space-kernels.md` (the article, by its
numbering); *blueprint* = the node in `blueprint/src/parts/`; *Lean* = the declaration, unfolded
to Mathlib primitives. Failure-mode tags F1–F8 are the plan's. Severity: **claim-changing** (the
proved statement is not the article's), **statement-tightening** (the proved statement is the
article's but could be stated closer to it, or a bridge is missing), **note-only** (a deliberate,
recorded, faithful choice worth a sentence in the text of record).

## Findings ledger

| # | tag | severity | where | finding | resolution |
|---|---|---|---|---|---|
| R1 | F3 | statement-tightening | `main_analysis` (⇒), `MainAnalysis.lean:100` | Concludes in `(χ, b₀, k)` with `(levyExponentD b₀ k _).toReal`; asserts neither `levyExponentD b₀ k s ≠ ⊤` nor an `F : SelfDecomposableExponent` nor `Fam.repr x y = F.kernel (χ x) (χ y)`. Finiteness is forced (see card T1.1, P2) but derived by the reader; the article's sentence is "F of the form (7.1)". | open — P2 decision: round-trip corollary |
| R2 | F8/F3 | statement-tightening | `signaling_form` (2d), `SignalingForm.lean:80`; draft Thm 11.6(2) | Lean asserts the Mellin form off the zeros of `H̃(z−1)`; the draft asserts it on the strip and relegates the zero set to the proof. | open — P2 decision: which side moves |
| R3 | F8 | note-only → draft edit | draft Def. 12.1 (line 635) vs blueprint `def:locality-pmp` | Blueprint's definition tests locality on `C_c^∞((0,∞))` **and on the profiles**; the draft still says `C_c^∞` only. The widening is recorded and justified in the blueprint; the draft lags. | draft edit (P5, F8 sweep) |
| R4 | F5 | statement-tightening | `Nondegenerate` (`MemoryKernelTransform.lean:151`) vs `hF : ∃ s₀, 0 < s₀ ∧ F.exponent s₀ ≠ 0` | Two renderings of "F ≢ 0 / (ND)" for a `SelfDecomposableExponent` — chapter 9 uses the first, the headline theorems the second — with no bridge lemma. Equivalent (k antitone ⇒ `k t₀ > 0` gives positive measure to `{k > 0}`), so a lemma `nondegenerate_iff_exists_exponent_ne_zero` closes it. | open — cheap Lean lemma |
| R5 | F3 | note-only | `SatisfiesPMP` (`LocalOperator.lean:107`) | PMP rendered as `Re (Ag)(x₀) ≤ 0`; article says `(Ag)(x₀) ≤ 0` (a real number). Weaker as a *conclusion* (`lem:pmp-verification`), stronger-hypothesis-free as a *hypothesis*; blueprint annotation records the choice. Faithful once `A` preserves realness on real test functions — is that a lemma? | check in P4 |
| R6 | F4 | note-only | `HasCoreDeriv.causal_deriv` (`DelayCore.lean`) | `g` causal *pointwise* (`∀ r < 0, g r = 0`), where `X₀` is an a.e. condition. Harmless — every causal `L¹` class has such a representative and the theorems quantify over functions — but the card records it. | none |
| R7 | F4 | note-only | `semigroup_case` (`SemigroupCase.lean:233`) | The article's "after normalization `g_{0,1}(1) = 1`" is a *hypothesis* `hnorm : Fam.G 1 1 = 1`, not a reparametrisation performed. Faithful in content; the reparametrisation (rescale the scale axis) is a sentence in prose and is not in Lean. | none, or one-line blueprint note |
| R8 | F3 | statement-tightening | `main_characterization` (⇐), `cascadeFamily` (`Instance.lean`) | Theorem 7.3 (⇐) is stated for an *arbitrary* gauge `χ`: the family `Φ_{x,y} = μ_{χ(x),χ(y)} ∗ ·` satisfies the axioms. The Lean witness is the canonical gauge only (`S σ x = σ x`, kernels `F.kernel x y`). The general case is the canonical one reparametrised by `χ` — (A1)–(A7), (ND) transport trivially, (A8) with `S_σ = χ⁻¹(σ χ(·))`, and (A7) needs `χ` continuous, which an increasing bijection of `[0,∞)` is — but that reparametrisation lemma is not in Lean, and the article's own proof says "work in the canonical gauge" without stating it either. Surfaced by blind restatement A (§3, item 7). | P2: add `CascadeFamily.reparam` or record in the blueprint that (⇐) is proved in the canonical gauge and the general gauge is a reparametrisation |
| R9 | F3 | statement-tightening | `signaling_form` (1), `SignalingForm.lean:80` | Article's Thm 11.6(1) asserts two things: `H(s·)` *is in the domain of Def. 11.3* for every `c ∈ (0, z_*−1)`, and `A[H(s·)] = sH(s·)`. `A` being total in Lean, the domain claim is `RealisesSymbolAction c (H(s·)) (s·x·H(s·))`, proved as `realisesSymbolAction_profile` (`InversionOperator.lean:280`) but **not a conjunct of the assembled theorem**, which carries only the eigen-equation. Surfaced by blind restatement B (§11, items 3 and 5). | P2: add the conjunct |
| R10 | F4/F8 | claim-shaping (article side) | `signaling_form` (3), Lemma 11.4 vs `eventuallyEq_inversionSymbol_of_realisesAction` (`SymbolUniqueness.lean`) | The Lean hypothesises `RealisesAction c' B …` for **every** height `c'` in the range and concludes germ-agreement on the strip **without assuming `B` meromorphic**. The article fixes one `c`, says "of the form `x⁻¹B_i(θ)`" (implicitly: `B_i` meromorphic on the strip), and its proof reaches agreement on the *line* `Re z = c` and then says "on the strip outright" — the step from line to strip is the identity theorem and needs the meromorphy it never states. Two faithful statements exist: (a) `B` meromorphic + one height, or (b) every height, no meromorphy. Lean has (b); the article's *statement* is closer to (a) and its *proof* is a gap for (a). Blind restatement B found this independently (§11, item 4). | P2: decide; likeliest fix is the article's statement says "at every height" (matching the Lean, and matching how (1) is stated — "for every `c`"), and the proof drops "outright" |
| R11 | F3 | note-only | `signaling_form` (2c) | Article: "with `û(s,0+) = f̂(s)`". Lean has `û(s,x) = f̂(s) H(sx)` for `x > 0` and (2b) `Φ_{0,x} f → f` in `X`; the scalar limit follows (`H(sx) → H(0) = 1`, `profile` continuous) but is not a conjunct. | P2: add or note |
| R12 | F5 | note-only | `IsLocalOfOrder c n`, `SatisfiesPMP c` carry the height `c` | Def. 12.1 is stated `c`-free ("the inversion operator `A`"); Def. 11.3 fixes `c`. Lean is honest that `A = A_c`; no independence-of-`c` is claimed anywhere (article or Lean). Blind restatement C flagged three inequivalent readings (fixed / ∀ / ∃ `c`); Lean's is "fixed `c`, hypothesis on every theorem", the article's Def. 11.3 reading. | none; blueprint already carries `c` |

Ledger entries are added as cards are written; a resolved entry keeps its row with the commit.

---

## Tier 0 — definitions

### T0.1 `def:cascade-family` · Def. 3.1 · `CascadeCore`, `IsScaleCovariant`, `CascadeFamily` (`Family.lean`)

**Draft says.** Linear operators `Φ_{x,y} : X → X`, `0 ≤ x ≤ y < ∞`, with (A1) bounded; (A2)
`Φ τ_a = τ_a Φ`; (A3) `f = 0` a.e. on `(−∞,t₀)` ⇒ same for `Φf`; (A4) `Φ X₊ ⊆ X₊`; (A5)
`∫Φf = ∫f` on `X₊`; (A6) `Φ_{x,x} = Id`, `Φ_{y,z}Φ_{x,y} = Φ_{x,z}`; (A7) `(x,y) ↦ Φ_{x,y}f`
continuous `{0 ≤ x ≤ y} → X` for every `f`; (A8) a family `(S_σ)_{σ>0}` of increasing bijections
of `[0,∞)` with `D_σ Φ_{x,y} = Φ_{S_σx,S_σy} D_σ`; (ND) `Φ_{x,y} ≠ Id` for `x < y`.
Notation §2: `X = L¹(ℝ)`, `(τ_a f)(t) = f(t−a)`, `(D_σ f)(t) = σ⁻¹ f(t/σ)`.

**Blueprint says.** The same, verbatim, plus an annotation recording the split into
`CascadeCore` + `IsScaleCovariant` and the design choices below.

**Lean says (unfolded).** `X := ℝ →₁[volume] ℝ`. `CascadeCore` is a structure with
`Φ : ℝ → ℝ → (X →L[ℝ] X)` and fields, each guarded by `0 ≤ x → x ≤ y →`:
`translation` (∀ a f, `Φ x y (transL1 a f) = transL1 a (Φ x y f)`, where `transL1 a` is the
`L¹` class of `t ↦ f(t − a)`, `coeFn_transL1`); `causal` (`VanishesBefore t₀ f → VanishesBefore
t₀ (Φ x y f)`, `VanishesBefore t₀ f := ∀ᵐ t, t < t₀ → f t = 0`); `positive` (`IsNonneg f :=
0 ≤ᵐ f`); `unit_area` (`IsNonneg f → ∫ Φ x y f = ∫ f`); `refl` (`Φ x x = id`); `cascade`
(`(Φ y z).comp (Φ x y) = Φ x z` for `0 ≤ x ≤ y ≤ z`); `continuous` (∀ f, `ContinuousOn (fun p
=> Φ p.1 p.2 f) {p | 0 ≤ p.1 ∧ p.1 ≤ p.2}`); `nondegenerate` (`0 ≤ x → x < y → Φ x y ≠ id`).
`IsScaleCovariant Fam G S`: for `σ > 0`, `σ ∈ G`: `MapsTo (S σ) (Ici 0) (Ici 0)`, `StrictMonoOn
(S σ) (Ici 0)`, `SurjOn (S σ) (Ici 0) (Ici 0)`, and `(dilL1 hσ).comp (Φ x y) = (Φ (S σ x) (S σ
y)).comp (dilL1 hσ)` for `0 ≤ x ≤ y`, where `dilL1 hσ` is the class of `dilate σ f = fun t =>
σ⁻¹ * f (σ⁻¹ * t)`. `CascadeFamily := CascadeCore + S + IsScaleCovariant _ (Ioi 0) S`.

**Hypotheses/clauses.**
| article | Lean | class |
|---|---|---|
| (A1) bounded linear | type `X →L[ℝ] X` | same |
| (A2) | `translation`, `transL1 a` = `f(· − a)` | same (sign checked against §2) |
| (A3) a.e. ⇒ a.e. | a.e. ⇒ a.e. | same |
| (A4) | a.e. nonneg ⇒ a.e. nonneg | same |
| (A5) on `X₊` | on `IsNonneg` only | same (docstring: strengthening to all of `X` would *narrow* the structure) |
| (A6) two clauses | `refl`, `cascade` | same |
| (A7) | `ContinuousOn` on the closed wedge, into `X` (norm topology) | same |
| (A8) ∃ family of increasing bijections | `S` as data + `MapsTo/StrictMonoOn/SurjOn` on `Ici 0` + intertwining; `G = Ioi 0` | same — bundling ∃ as data is the standard rendering; "increasing bijection of `[0,∞)`" = strict-mono + onto + maps-to, exactly |
| (ND) | `nondegenerate` | same |
| index range `0 ≤ x ≤ y` | every field guarded; `Φ` total off the wedge, unconstrained there | same (off-wedge values are junk and no theorem reads them — checked: every consumer carries `0 ≤ x`, `x ≤ y`) |
| `D_σ` normalisation | `σ⁻¹ f(σ⁻¹ t)` | same as §2 |

**Junk-value audit.** `Φ x y` for `x > y` or `x < 0`: unconstrained data; every field and every
downstream statement guards the wedge. `dilL1 hσ` requires `0 < σ` as a proof argument, so no
`σ = 0` junk. `transL1` total. No partial functions in the structure.

**Witness.** `SelfDecomposableExponent.cascadeFamily hF` (`Instance.lean`), with `S σ x = σ * x`
(`Instance.lean:212`) — a model with (ND), so the structure is not only inhabited by trivial
families. P1 adds named witnesses.

**Blind restatement (agent A, draft only).** Produced a structure field-for-field identical
in content: guards on the wedge, (A3) a.e., (A4)/(A5) on the a.e. cone (it chose (A5) for all
`f`, "equivalent by linearity" — the Lean's cone-only reading is the weaker structure field,
which is the article's letter and the safer direction), (A7) as `ContinuousOn` on the closed
wedge in the norm topology (and flagged that operator-norm continuity would make (⇐) *false*
and separate continuity would be *weaker* — the Lean has the joint SOT reading ✓), (A8) with
`S` as data + `StrictMonoOn` + `BijOn (Ici 0) (Ici 0)` (Lean: `MapsTo`+`StrictMonoOn`+`SurjOn`,
the same), (ND) strict. Its one demand not already met: "exhibit an instance, else every (⇒)
is unverified against vacuity" — that is P1.

**Verdict.** **faithful.** The three deliberate choices (A5 on the cone, A3 a.e., S as data)
are the article's own reading and were reproduced blind; the split into core + covariance
predicate is invisible to `CascadeFamily`.

**Actions.** none.

---

### T0.2 The admissible exponents (7.1) · Lemma 7.1(3) / Thm 7.3's "F of the form (7.1), F ≢ 0" · `SelfDecomposableExponent`, `levyExponentD`, `exponent`, `increment`, `kernel` (`Construction.lean`, `SelfDecomposable.lean`)

**Draft says.** `F(s) = b₀ s + ∫₀^∞ (1 − e^{−st}) k(t)/t dt`, `b₀ ≥ 0`, `k : (0,∞) → [0,∞)`
nonincreasing, `∫₀¹ k < ∞`, `∫₁^∞ k(t)/t dt < ∞`; Theorem 7.3 adds `F ≢ 0`; kernels
`μ̂_{x,y}(s) = exp[−(F(χ(y)s) − F(χ(x)s))]`; canonical gauge `χ = id`.

**Blueprint says.** `def:levy-exponent` (the `LE` class, ch. 2) and (7.1) in ch. 7, with the
`k 0 = 0` normalisation and the `ne_top` field recorded in the annotation.

**Lean says (unfolded).** `levyJump k s := ∫⁻ t in Ioi 0, ofReal ((1 − e^{−st}) k t / t)`;
`levyExponentD b₀ k s := ofReal (b₀ s) + levyJump k s` (`ℝ≥0∞`). Structure fields: `b₀ : ℝ`,
`k : ℝ → ℝ`, `0 ≤ b₀`, `∀ t > 0, 0 ≤ k t`, `AntitoneOn k (Ioi 0)`, `k 0 = 0`, `∀ s ≥ 0,
levyExponentD b₀ k s ≠ ⊤`. `exponent s := levyExponentD b₀ k s`; `toRealExponent := (·).toReal`;
`increment a b s := levyExponentD (b₀(b−a)) (u ↦ k(u/b) − k(u/a)) s`, with
`exponent (a s) + increment a b s = exponent (b s)` (`exponent_add_increment`, `0 ≤ a ≤ b`,
`s ≥ 0`); `kernel a b := if 0 ≤ a ∧ a ≤ b then choose (A17-derived existence) else 0`, with
`kernel_spec`: probability, causal, `laplace (kernel a b) s = exp(−(increment a b s).toReal)`
for `s ≥ 0`, and `kernel_unique` (any causal finite measure with that transform *is* it).

**Hypotheses/clauses.**
| article | Lean | class |
|---|---|---|
| `b₀ ≥ 0`, `k ≥ 0` nonincreasing on `(0,∞)` | fields | same |
| `∫₀¹ k < ∞ ∧ ∫₁^∞ k/t < ∞` | `ne_top : ∀ s ≥ 0, F s ≠ ⊤` | **equivalent, and the equivalence is checked**: `Examples.lean` `levyExponentD_ne_top_of_integrableOn` gives (integrable ⇒ finite); the converse (finite at one `s > 0` ⇒ both integrals) is the docstring's concavity remark; see A17 card (T1.4) — *to confirm as a lemma or record as prose* |
| `k` defined on `(0,∞)` | `k : ℝ → ℝ` with `k 0 = 0` | **normalisation, not a constraint** — `k` on `(0,∞)` is what every field and every integral reads; `k 0` is read only by `increment_zero_left`, where it makes `a = 0` a case of the general formula. F4-none |
| `F ≢ 0` | `∃ s₀ > 0, exponent s₀ ≠ 0` | same (`F ≥ 0`, so `≢ 0` ⇔ nonzero somewhere on `(0,∞)`; `F(0) = 0` always) — but see **R4**: chapter 9's `Nondegenerate` is a second rendering |
| `μ̂_{x,y}(s) = e^{−(F(ys) − F(xs))}` | `laplace (kernel x y) s = exp(−(increment x y s).toReal)` + `exponent_add_increment` + `increment_ne_top` | same, once the two lemmas are read together; the statement is in "increment form" because `F(ys) − F(xs)` in `ℝ≥0∞` is not subtraction |
| `μ_{x,y}` a probability measure on `[0,∞)` | `IsProbabilityMeasure`, `IsCausal := μ (Iio 0) = 0` | same |

**Junk-value audit.** `k t / t` at `t = 0`: excluded by `Ioi 0`. `ofReal` of a negative: the
integrand is `≥ 0` on `Ioi 0` by `k_nonneg`. `(increment _ _ _).toReal`: protected by
`increment_ne_top` (`0 ≤ a ≤ b`, `s ≥ 0`). `kernel a b` off the wedge is `0` — a *finite*
measure by design so that `mconvL1 (kernel a b)` is total; no theorem reads it there.
`Classical.choose`: all properties flow through `kernel_spec`; `kernel_unique` shows the choice
is immaterial.

**Witness.** `gammaExponent γ`, `dickmanExponent τ`, `stableExponent α`, `leakyIntegrator`
(`Examples.lean`, `ClosedForms.lean`); pure drift — P1.

**Blind restatement (agent A).** Chose a real-valued `F : ℝ → ℝ` (Bochner) with the two
integrability conditions as *fields*, and warned that (i) dropping them makes a Bochner `F` junk,
(ii) an `ℝ≥0∞`-valued `F` "admits `F = ⊤`" and must be compensated by a finiteness clause — the
Lean does exactly that (`ne_top`), so the two designs are equivalent; (iii) `k` **must be
allowed unbounded near 0** (`k(t) ∼ t^{−α}` for the stable family) — Lean's `k : ℝ → ℝ` with
conditions on `Ioi 0` only ✓, and `stableExponent` is an instance; (iv) right-continuity must
*not* be imposed — Lean does not ✓; (v) `F ≢ 0` must be `∃ s > 0, F s ≠ 0`, never `F ≠ 0` as a
function on `ℝ` (junk on `s < 0`) — Lean ✓; (vi) uniqueness of `(χ, F)` as *functions on
`Ici 0`*, not as structures (`k` only a.e.) — Lean's `prop:main-uniqueness` concludes `∀ t ≥ 0,
F'.exponent t = F.exponent t` ✓; (vii) `μ (Iio 0) = 0`, not `Iic` — Lean ✓; (viii) the
increment lemma should include `a = 0` — Lean's `exponent_add_increment` takes `0 ≤ a` ✓.

**Verdict.** **faithful.** One hygiene finding (R4).

**Actions.** R4 (bridge lemma). Confirm on the A17 card that `ne_top ⇔ (∫₀¹ k < ∞ ∧ ∫₁^∞ k/t
< ∞)` is a lemma somewhere or state in the blueprint annotation that it is prose.

---

### T0.3 Transforms and exponents on the family side · §4–5 · `laplace`, `laplaceL`, `CascadeCore.repr`, `CascadeCore.exponent`, `G` (`Levy.lean`, `Representation.lean`, `TransformContinuity.lean`, `Additivity.lean`)

**Draft says.** `μ̂(s) = ∫_{[0,∞)} e^{−st} μ(dt)`, `s ≥ 0`, for finite positive `μ` on `[0,∞)`;
`g_{x,y} := −log μ̂_{x,y}`; `G(x,s) := g_{0,x}(s)`; Lemma 4.1: unique probability `μ_{x,y}` on
`[0,∞)` with `Φ_{x,y} f = μ_{x,y} ∗ f`.

**Lean says (unfolded).** `laplaceL μ s := ∫⁻ ofReal (e^{−st}) ∂μ` (`ℝ≥0∞`, unconditional);
`laplace μ s := ∫ e^{−st} ∂μ` (Bochner, junk `0` if not integrable — but for causal finite `μ`
and `s ≥ 0` the integrand is bounded by `1`, `laplaceL_le_mass`, so it is integrable and the two
agree, `laplace_eq_toReal_laplaceL`). `repr Fam x y := if 0 ≤ x ≤ y then choose (∃!
probability causal μ, Φ x y = mconvL1 μ) else dirac 0`; `existsUnique_repr` is the ∃! statement.
`exponent Fam x y s := −Real.log (laplace (repr x y) s)`; `G x s := exponent 0 x s`.

**Junk-value audit.** `Real.log 0 = 0`: `laplace (repr x y) s > 0` for causal probability
measures and `s ≥ 0` is `laplace_pos_of_prob` (`TransformContinuity.lean:119`; general finite
nonzero causal `μ`: `laplace_pos`, `Levy.lean:143`), so `−log` is the article's `g` on the whole
range, and the junk branch of `Real.log` is unreachable. `repr` off the wedge is `δ₀`, harmless
and unread. `laplace` at `s < 0`: not in any statement's range.

**Verdict.** **faithful.**

---

### T0.4 `def:standing-hypothesis` (Def. 11.1) and Lemma 11.2's objects · `lawT₁`, `profile`, `negMoment`, `zStar`, `StandingHypothesis` (`MellinData.lean`)

**Draft says.** (H): `F(∞) = ∞` (equivalently `b₀ > 0` or `∫₀^∞ k/t = ∞`; no atom at zero
delay), and `z_* := sup{ζ > 0 : E[T₁^{−ζ}] < ∞} > 1` (equivalently `∫₀^∞ e^{−F} < ∞`). `T₁` has
law `μ_{0,1}`, `E[e^{−sT₁}] = H(s) = e^{−F(s)}`.

**Lean says (unfolded).** `lawT₁ := kernel 0 1` (probability, causal); `profile s := laplace
lawT₁ s` (= `exp(−toRealExponent s)`, `profile_eq_exp_neg`, `s ≥ 0`); `negMoment ζ := ∫⁻ t in
Ioi 0, ofReal (t^{−ζ}) ∂lawT₁` (`ℝ≥0∞`); `zStar := sSup (ofReal '' {ζ | 0 < ζ ∧ negMoment ζ ≠
⊤}) : ℝ≥0∞`; `StandingHypothesis := Tendsto toRealExponent atTop atTop ∧ 1 < zStar`.

**Hypotheses/clauses.**
| article | Lean | class |
|---|---|---|
| `F(∞) = ∞` | `Tendsto toRealExponent atTop atTop` | same (`toReal` is faithful because `ne_top`) |
| "no atom at zero delay" | consequence: `lawT₁_singleton_zero` | same (proved, not assumed) |
| `E[T₁^{−ζ}]` | integral over `Ioi 0` against `lawT₁` — excludes `t = 0` | **same, by the draft's own words**: the proof of Lemma 11.2 (line 537) says "`E[T₁^{−c}]`, an integral over `(0,∞)`, does not see the atom" — so `Ioi 0` is the article's definition, not a Lean choice. |
| `z_* = sup{…}` in `(0,∞]` | `sSup` in `ℝ≥0∞`; empty set ⇒ `0` | same — the docstring's point about `Real.sSup` junk is correct and avoided |
| `z_* > 1` | `1 < zStar` | same |
| "equivalently `∫₀^∞ e^{−F} < ∞`" | not stated | not needed by any theorem; F7-none, note that the equivalence is unproved in Lean |

**Junk-value audit.** `t^{−ζ}` for `t ≤ 0`: excluded by `Ioi 0`. `sSup ∅ = 0` in `ℝ≥0∞`: then
`1 < zStar` fails and (H) is simply false, correct. `laplace lawT₁` Bochner: probability + causal
+ `s ≥ 0` ⇒ integrable.

**Witness.** none yet — P1 (pure drift `zStar = ⊤`; Gamma `zStar = γ`).

**Blind restatement (agent B).** Chose `zStar : ℝ≥0∞` as `⨆`/`sSup` of the image, for the
same reason the docstring gives (`Real.sSup` of an unbounded set is `0`, which would make (H)
false for drift/stable/Bessel — "exactly the headline cases"); `negMoment` as `∫⁻` (a Bochner
`< ∞` would be vacuous); `F(∞) = ∞` as a `Tendsto`, with the `b₀ > 0 ∨ ∫k/t = ∞` form as a
*lemma*; and demanded the downward-closure lemma "`ζ < zStar → negMoment ζ ≠ ⊤`" be present
before any strip statement is usable — it is, `negMoment_ne_top_of_lt_zStar`
(`MellinData.lean:375`) with its converse `le_zStar_of_negMoment_ne_top` ✓. It also flagged
that any `zStar.toReal` in a strip bound would empty the strip at `zStar = ⊤`; the Lean writes
every bound as `ofReal (Re z) < zStar` ✓ (and chapter 12's `ofReal c < zStar − 1`, ENNReal
subtraction, is safe because `zStar > 1` and `⊤ − 1 = ⊤`).

**Verdict.** **faithful.**

---

### T0.5 `def:inversion-operator` (Def. 11.3) · `inversionOperator`, `inversionSymbol`, `RealisesAction`, `verticalStrip` (`InversionOperator.lean`, `InversionSymbol.lean`)

**Draft says.** Fix `c ∈ (0, z_*−1)`. For `g` with `g̃` defined on `Re z = c` and `B(−z)g̃(z)`
absolutely integrable there, `(Ag)(x) := x⁻¹ (2πi)⁻¹ ∫_{(c)} x^{−z} B(−z) g̃(z) dz = (x⁻¹
B(θ)g)(x)`, the second equality asserting a realising `h` with `h̃ = B(−z)g̃` on the line and
`Ag = h/x`. `B(−z) := H̃(z+1)/H̃(z)` (Lemma 11.2).

**Lean says (unfolded).** `inversionSymbol z := mellin H (z+1) / mellin H z` — **this is the
article's `B(−z)`**, indexed by the Mellin variable; `inversionOperator c g x := x⁻¹ * mellinInv c
(fun z => inversionSymbol z * mellin g z) x`, total in `g`, `c`, `x`; Mathlib `mellinInv σ f x =
(2π)⁻¹ ∫ y, x^{−(σ+iy)} • f(σ+iy)`, which is `(2πi)⁻¹∫_{(c)} x^{−z} f(z) dz` after `dz = i dy` —
same normalisation. `RealisesAction c B g h`: `mellin h = B · mellin g` at every point of the
line where `mellin H ≠ 0`, `MellinConvergent h c`, `VerticalIntegrable (mellin h) c`.
`verticalStrip a b := {z | a < Re z ∧ ofReal (Re z) < b}` with `b : ℝ≥0∞`.

**Hypotheses/clauses.**
| article | Lean | class |
|---|---|---|
| `A` defined on a domain | `A` total; domain = hypotheses of the theorems that compute it (`RealisesAction`) | same in effect; the article's "domain of Def. 11.3" claim in Thm 11.6(1) must then appear as a `RealisesSymbolAction` conclusion somewhere — **check on T1.2** |
| `(2πi)⁻¹ ∫_{(c)} x^{−z}` | Mathlib `mellinInv c` | same |
| the realising `h` with `h̃ = B(−z)g̃` on the line | `mellin_eq` **off the zeros of `H̃`** | article says "at every point of the line where `H̃(z) ≠ 0`" (proof of 11.6(1)) — same; the docstring's argument that this is the unique composable choice is sound |
| `B(−z) = H̃(z+1)/H̃(z)` | `inversionSymbol z` | same up to the sign convention, which is documented in three places; **every statement using `B(1−z)` must read `inversionSymbol (z−1)`** — checked in `signaling_form` (2d): `inversionSymbol (z − 1)` ✓ |
| `c ∈ (0, z_*−1)` | `0 < c ∧ ofReal (c+1) < zStar` | same (`c + 1 < z_*` ⇔ `c < z_* − 1`, and `ofReal` is safe since `c+1 > 0`) |

**Junk-value audit.** `mellin H z` is a Bochner integral: on the strip `0 < Re z < z_*` it
converges (`lem:mellin-data`, `mellinConvergent_profile` or equivalent — cite on T1.2); off the
strip it is `0`, and `inversionSymbol` there is `0/0 = 0` — never evaluated there by any theorem
under (H) with `c` in range. `x⁻¹` at `x = 0`: theorems take `0 < x`. Division by `mellin H z = 0`
inside the strip: isolated zeros (`ae_mellin_profile_ne_zero`), null for the line integral.

**Witness.** the profiles themselves (`inversionOperator_profile`).

**Blind restatement (agent B).** Produced `Aop c g x := x⁻¹ * mellinInv c (Bsym * mellin g) x`
with `Bsym z := H̃(z+1)/H̃(z)` — the same object, the same normalisation ("no stray `i` or `2π`"),
the same indexing, and total with hypotheses on theorems. Three demands, each checked: (i) the
realising identity must be **a.e./off the zeros of `H̃`**, since an everywhere version is
unprovable for the profiles at a zero of `H̃` — Lean's `RealisesAction.mellin_eq` is exactly
"off the zeros" ✓; (ii) Theorem 11.6(1) must assert the *domain* claim separately from the
eigen-equation — it does not, **R9**; (iii) `c` is a parameter, universally quantified in
theorems, no independence-of-`c` claim — Lean ✓ (R12). It also listed the three renderings of
"`B(1−z)`" that would be transcription slips; the Lean's `inversionSymbol (z − 1)` in (2d) is the
correct one ✓.

**Verdict.** **faithful**, with the sign convention as the one place a reader must be told
(they are, in the blueprint annotation). R9 belongs to the theorem card, not this one.

---

### T0.6 `def:locality-pmp` (Def. 12.1) · `IsLocalOfOrderCore`, `IsLocalOfOrder`, `SatisfiesPMP`, `IsTestFunction` (`LocalOperator.lean`, `MellinEuler.lean`)

**Draft says.** `A` local of order `n` if it agrees on `C_c^∞((0,∞))` with `∑_{j≤n} c_j(x)∂_x^j`,
`c_j ∈ C((0,∞))`, `c_n ≢ 0`. PMP: `(Ag)(x₀) ≤ 0` whenever `g ∈ C_c^∞((0,∞))` attains a
nonnegative maximum at `x₀`.

**Blueprint says.** The same **plus "and on the profiles `H(s·)`, `s > 0`"**, with an italic
paragraph explaining the widening (needed for `lem:local-polynomial-symbol` (⇒)) and the
annotation on the three readings.

**Lean says (unfolded).** `IsTestFunction g`: `ContDiff ℝ ⊤ g`, `HasCompactSupport g`,
`tsupport g ⊆ Ioi 0` — i.e. `C_c^∞` with support inside `(0,∞)`, ✓ `C_c^∞((0,∞))`.
`IsLocalOfOrderCore c n`: data `coeff : ℕ → ℝ → ℂ`, `ContinuousOn (coeff j) (Ioi 0)`,
`∃ x₀ > 0, coeff n x₀ ≠ 0`, and `A g x = ∑_{j≤n} coeff j x · iteratedDeriv j g x` for test `g`,
`x > 0`. `IsLocalOfOrder` adds the same identity for `g = H(s·)`, `s > 0`. `SatisfiesPMP c`:
for real `g` with `IsTestFunction (g : ℂ)`, `x₀ > 0`, `0 ≤ g x₀`, `∀ x > 0, g x ≤ g x₀` ⇒
`Re (A g x₀) ≤ 0`.

**Hypotheses/clauses.**
| article | Lean | class |
|---|---|---|
| test class `C_c^∞((0,∞))` | `IsTestFunction` | same |
| `c_j ∈ C((0,∞))` | `ContinuousOn (coeff j) (Ioi 0)`, `ℂ`-valued | same (complex coefficients are the natural reading since `A` is `ℂ`-valued; the article's `c_j` are unspecified) |
| `c_n ≢ 0` | `∃ x₀ > 0, coeff n x₀ ≠ 0` | same |
| "agrees on `C_c^∞`" | + **on the profiles** | **divergent from the draft, faithful to the blueprint** (R3). The widening makes "local of order `n`" a *stronger* property, so `lem:local-polynomial-symbol` (⇒) has a stronger hypothesis than the draft's Lemma 12.2 (⇒), and (⇐) a stronger conclusion. Since the profiles are where `B` is controlled, and the draft's own (⇒) proof jumps from `C_c^∞` to the symbol without an approximation argument, the blueprint's version is the *correct* statement and the draft's is under-proved. |
| existential over the differential expression | data (`coeff`) | same in content; blueprint annotation explains `Nonempty` |
| PMP: `(Ag)(x₀) ≤ 0` | `Re (Ag)(x₀) ≤ 0` | **R5** — weaker as a conclusion unless `A` preserves realness |
| "attains a nonnegative maximum at `x₀`" | `0 ≤ g x₀ ∧ ∀ x > 0, g x ≤ g x₀` | same |

**Junk-value audit.** `iteratedDeriv j g` for smooth `g` — genuine. `A g x` total; on test
functions its Mellin data converge (`MellinEuler.lean`). No partial function reads a junk value
in the definition.

**Blind restatement (agent C).** Same test class (`ContDiff ⊤`, `HasCompactSupport`,
`tsupport ⊆ Ioi 0`); `c_n ≢ 0` as "not identically zero" (`∃ x > 0, …`), warning that "nowhere
zero" is a consequence, not the definition — Lean ✓; PMP with `x₀ > 0`, max over `(0,∞)`, `≥ 0`
— Lean ✓. Two substantive flags: (i) "`B` is a polynomial of degree `n`" must be stated **on the
whole strip, off the poles** (its preferred rendering: `∀ z ∈ strip, H̃(z) ≠ 0 → B(−z) = P(z)`),
never on one line — Lean's `nonempty_isLocalOfOrder_iff_symbol_eq` (`ProfileEuler.lean:669`)
is exactly that, with `γ n ≠ 0` for the degree ✓; (ii) Def. 12.1 "silently assumes `A` is
defined on all of `C_c^∞((0,∞))`", so a faithful formalisation must either prove test functions
lie in the domain or carry a domain hypothesis that could be hollow — Lean's `A` is total and
`MellinEuler.lean` proves the test-function Mellin data, so the identity in
`eq_sum_iteratedDeriv` is a genuine one ✓. It chose an *existential* for "local of order `n`"
and then needed a coefficient-uniqueness lemma; the Lean's data-carrying structure is the
blueprint's recorded alternative and avoids that lemma. It did **not** anticipate the profile
clause — which is the point: the widening (R3) is not derivable from the draft, and the
blueprint's paragraph justifying it is doing necessary work.

**Verdict.** **divergent-def w.r.t. the draft, faithful w.r.t. the blueprint** — R3, R5, R12.

**Actions.** R3: update draft Def. 12.1 and Lemma 12.2's statement (F8 sweep). R5: check
for a realness lemma; if present, strengthen `SatisfiesPMP` or note.

---

### T0.7 One-parameter families · Cor. 7.4 hypothesis · `IsOneParameter` (`SemigroupCase.lean`)

**Draft says.** "`Φ_{x,y}` depends only on `y − x`"; conclusion after normalisation
`g_{0,1}(1) = 1`: `F(s) = s^α`, `0 < α ≤ 1`.

**Lean says.** `IsOneParameter Fam := ∀ x r, 0 ≤ x → 0 ≤ r → Φ x (x+r) = Φ 0 r`. `semigroup_case
(hcov) (hone) (hnorm : G 1 1 = 1) : ∃ α, 0 < α ∧ α ≤ 1 ∧ (∀ s ≥ 0, G 1 s = s^α) ∧ (∀ x s ≥ 0, G x
s = x s^α) ∧ (∀ σ > 0, x ≥ 0, S σ x = σ^α x)`.

**Hypotheses/clauses.** "depends only on `y − x`" ⇔ `Φ x (x+r) = Φ 0 r` for all `x, r ≥ 0` —
same (the docstring's one-sided form is equivalent by transitivity). `G 1 s = s^α` is `F(s) =
s^α` in the canonical gauge (`G x s = x s^α` says the gauge *is* the identity here). `α ≤ 1`
included, `α = 1` allowed — matches "together with the boundary case". Extra conclusion `S σ x =
σ^α x`: stronger. **R7**: normalisation as a hypothesis.

**Junk-value audit.** `s ^ α` for `s ≥ 0`, `α > 0`: `Real.rpow`, `0^α = 0` — genuine.

**Blind restatement (agent A).** Two flags. (i) "One-parameter" must be imposed on the family
in its *given* parametrisation, not transported to the canonical gauge (where `χ(x) = x^{1/α}`
and the family is not one-parameter) — Lean's `IsOneParameter` is on `Fam.Φ` as given ✓, and
the conclusion `G x s = x s^α` is about the given parameter ✓. (ii) It suspected a clash between
"`g_{0,1}(1) = 1`" and Theorem 7.3's "`χ(1) = 1`". There is none: `g_{0,1}(s) = F(χ(1)s)`, so
`χ(1) = 1` gives `g_{0,1} = F` and the two normalisations are one; the Lean's `hnorm : G 1 1 = 1`
is that normalisation on `F` directly. A one-clause remark in the blueprint proof of
`cor:semigroup-case` would pre-empt the question — optional.

**Verdict.** **faithful** (R7 note-only).

---

### T0.8 Chapter 9/10 objects · Lemma 9.1, 9.4, Def. 10.2 · `toRealExponent`, `memoryKernel`, `symbol`, `Nondegenerate`, `existsUnique_potentialKernel`, `HasLevyTail`, `phillipsGenerator`, `HasCoreDeriv`/`MemCore` (`MemoryKernel.lean`, `MemoryKernelTransform.lean`, `PotentialKernel.lean`, `PhillipsGenerator.lean`, `DelayCore.lean`)

**Draft says.** `κ^{(x)} = b₀δ₀ + x⁻¹ k(t/x) dt`; `φ_x(s) = sF'(xs)`; `ℓ^{(x)}` = the unique
positive locally finite measure on `[0,∞)` with `ℓ̂ = 1/φ_x`; `ν₁ = −dk` (k right-continuous,
`k(∞)=0`), `ν_x` its dilation, `φ_x(∂_t)f = b₀f' + ∫(f − T_rf)ν_x(dr)`; `𝒟 = {f ∈ X₀ : f abs.
cont., f' ∈ X₀, f(0) = 0}`, `X₀ = L¹(ℝ₊)` as the causal elements of `X`.

**Lean says (unfolded).** `memoryKernel x := ofReal b₀ • dirac 0 + (volume|Ioi 0).withDensity
(t ↦ ofReal (k(t/x)/x))` ✓. `symbol x s := s * deriv toRealExponent (x s)`; `deriv` is genuine
for `xs > 0` by `hasDerivAt_toRealExponent` (`ExponentDerivative.lean:296`), so `F'` is the
honest derivative of the real-valued exponent on `(0,∞)`, and `lem:memory-kernel` proves it
equals `b₀ + ∫ e^{−st}k` ✓. `Nondegenerate := 0 < b₀ ∨ ∃ t > 0, 0 < k t` (R4).
`existsUnique_potentialKernel (hnd) (hx) : ∃! ℓ, IsCausal ℓ ∧ (∀ T, ℓ (Icc 0 T) ≠ ⊤) ∧ ∀ s > 0,
laplaceL ℓ s = ofReal (symbol x s)⁻¹` — the potential kernel is **specified** by the article's
three properties, and the subordinator construction lives inside the proof; the node's statement
is therefore the article's regardless of route (Route B is F7-none at the statement level) ✓.
`sonine_conservation`: `(memoryKernel x ∗ ℓ).restrict (Ici 0) = volume.restrict (Ici 0)` for any
s-finite causal `ℓ` with that transform — restriction to `Ici 0` on both sides; the article's
"`= Leb_{[0,∞)}`" as measures on `ℝ` also asserts no mass on `(−∞,0)`, which is `IsCausal.conv`
— **statement-tightening candidate, trivial** (add the unrestricted equality or note). `HasLevyTail
ν := IsCausal ν ∧ ∀ᵐ r ∂(volume|Ioi 0), ν (Ioi r) = ofReal (k r)` — the article's `ν₁((r,∞)) =
k(r)` with right-continuity replaced by an a.e. specification: same measure (a nonincreasing
`k` and its right-continuous version agree a.e.), so this is the article's `−dk` without the
normalisation ✓. `phillipsGenerator ν x A B := b₀ • B + ∫ r, (A − transL1 r A) ∂(dilatedTail ν
x)`, an `X`-valued Bochner integral, junk `0` off integrability — protected by
`lem:generator-properties`(1) (absolute convergence with the bound) ✓; takes `(A, B)` with
`HasCoreDerivL1 A B` because an `L¹` class has no derivative to read off — same content.
`HasCoreDeriv f g`: `Measurable g`, `Integrable g`, `∀ r < 0, g r = 0` (R6), `∀ r, f r = ∫_{Ioc 0
r} g`, `Integrable f`; `MemCore f := ∃ g, …`. Versus `𝒟`: absolute continuity + `f' ∈ X₀` +
`f(0) = 0` ⇔ `f = ∫₀^· g` with `g ∈ L¹` causal (Lebesgue FTC, one direction of which Mathlib
lacks — so the primitive is the *definition* and AC the consequence: same class), and `f ∈ X₀`
is `Integrable f` + causality (the latter free from the primitive) ✓; the `SignalingForm.lean`
docstring's point that `Integrable f` is a separate demand is right and the article's `f ∈ X₀`
imposes it.

**Junk-value audit.** `deriv toRealExponent` at `xs ≤ 0`: not in range (`x > 0`, `s > 0`).
`(symbol x s)⁻¹` at `symbol = 0`: `symbol_pos hnd hx hs`. `phillipsGenerator` integral: (1).
`memoryKernel` at `x = 0`: `k(t/0)/0 = k(0)·0 = 0` — junk but never read (`x > 0` everywhere).

**Blind restatement (agent C).** (i) Lemma 9.1's "`F'`" must be a `HasDerivAt` of the real
exponent, not merely a named closed form ("a Lean that only has the latter has renamed a
definition") — Lean has `hasDerivAt_toRealExponent` ✓ and `symbol` uses `deriv` of it ✓.
(ii) The potential kernel's *statement* must be the ∃! with the transform identity, and needs
`F ≠ 0` as a hypothesis or `1/φ_x` is junk — Lean: `existsUnique_potentialKernel (hnd :
Nondegenerate)` ✓; and it asked whether the subordinator-family construction is even
expressible with the interface — it is (`exists_subordinatorFamily`), and reaches only A17
(README, ch. 9 Route B). (iii) Sonine as a measure equality with the convolution as pushforward
of the product — Lean's `∗` ✓, restricted to `Ici 0` (the tightening noted above). (iv) Def.
10.2's Bochner integral: clause (1) **must be an `Integrable` statement, not only the norm
bound — "the bound is provable from junk"** — this is a check for the T2 card of
`lem:generator-properties`; the definitional file already carries
`integrable_sub_transL1`-style lemmas ✓. (v) `𝒟` must be the primitive form, since a
`deriv`-based predicate admits the Cantor function — Lean ✓. (vi) It would derive `k(∞) = 0`
rather than impose it — Lean: `tendsto_k_atTop_nhds_zero` ✓; and use an a.e. tail
specification for `−dk` — Lean's `HasLevyTail` ✓.

**Verdict.** **faithful**; one trivial tightening (Sonine restriction), R4, R6.

---

### T0.9 Primitives of chapter 2 · `def:levy-exponent` · `levyExponent`, `IsCausal`, `laplaceL`

`levyExponent b₀ ν s := ofReal (b₀ s) + ∫⁻ ofReal (1 − e^{−st}) ∂ν` (`ℝ≥0∞`); no killing term
(article: none, `F(0+) = 0`); `IsCausal μ := μ (Iio 0) = 0`. `levyExponentD_eq_levyExponent`
identifies the density form. Article's `∫(1∧t)ν(dt) < ∞` is again replaced by finiteness of the
exponent (see A17 card). **faithful.**

---

## Tier 1 — (P2/P3, not started)

## Witnesses (P1)

*(pending — agent report and `Formalization/Hemigroup/Witnesses.lean`)*
