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
| R1 | F3 | statement-tightening | `main_analysis` (⇒), `MainAnalysis.lean:100` | Concludes in `(χ, b₀, k)` with `(levyExponentD b₀ k _).toReal`; asserts neither `levyExponentD b₀ k s ≠ ⊤` nor an `F : SelfDecomposableExponent` nor `Fam.repr x y = F.kernel (χ x) (χ y)`. Finiteness is forced (see card T1.1, P2) but derived by the reader; the article's sentence is "F of the form (7.1)". | **resolved (P2)** — `main_analysis'` (`MainAnalysis.lean`): `∃ χ F, χ 0 = 0 ∧ χ 1 = 1 ∧ … ∧ ∀ x ≤ y, Fam.repr x y = F.kernel (χ x) (χ y) ∧ Fam.Φ x y = mconvL1 (…)`; `main_analysis` now also exports finiteness (from A18's own conclusion) and `χ 1 = 1`; the bundle's (⇒) is the round-trip form |
| R2 | F8/F3 | statement-tightening | `signaling_form` (2d), `SignalingForm.lean:80`; draft Thm 11.6(2) | Lean asserts the Mellin form off the zeros of `H̃(z−1)`; the draft asserts it on the strip and relegates the zero set to the proof. | **resolved (P2)** — blueprint `thm:signaling-form`(2) and draft Thm 11.6(2) state the Mellin form off the zeros of `H̃(z−1)`, with the meromorphic reading on the strip; Lean (2d) additionally asserts both `MellinConvergent`s |
| R3 | F8 | note-only → draft edit | draft Def. 12.1 (line 635) vs blueprint `def:locality-pmp` | Blueprint's definition tests locality on `C_c^∞((0,∞))` **and on the profiles**; the draft still says `C_c^∞` only. The widening is recorded and justified in the blueprint; the draft lags. | **resolved (P2)** — draft Def. 12.1 and Lemma 12.2's (⇒) proof aligned with the blueprint (`10551df`) |
| R4 | F5 | statement-tightening | `Nondegenerate` (`MemoryKernelTransform.lean:151`) vs `hF : ∃ s₀, 0 < s₀ ∧ F.exponent s₀ ≠ 0` | Two renderings of "F ≢ 0 / (ND)" for a `SelfDecomposableExponent` — chapter 9 uses the first, the headline theorems the second — with no bridge lemma. Equivalent (k antitone ⇒ `k t₀ > 0` gives positive measure to `{k > 0}`), so a lemma `nondegenerate_iff_exists_exponent_ne_zero` closes it. | **resolved (P2)** — `nondegenerate_iff_exists_exponent_ne_zero` (`MemoryKernelTransform.lean`), Lean core, with `strictMonoOn_toRealExponent` |
| R5 | F3 | note-only | `SatisfiesPMP` (`LocalOperator.lean:107`) | PMP rendered as `Re (Ag)(x₀) ≤ 0`; article says `(Ag)(x₀) ≤ 0` (a real number). Weaker as a *conclusion* (`lem:pmp-verification`), stronger-hypothesis-free as a *hypothesis*; blueprint annotation records the choice. Faithful once `A` preserves realness on real test functions — is that a lemma? | check in P4 |
| R6 | F4 | note-only | `HasCoreDeriv.causal_deriv` (`DelayCore.lean`) | `g` causal *pointwise* (`∀ r < 0, g r = 0`), where `X₀` is an a.e. condition. Harmless — every causal `L¹` class has such a representative and the theorems quantify over functions — but the card records it. | none |
| R7 | F4 | note-only | `semigroup_case` (`SemigroupCase.lean:233`) | The article's "after normalization `g_{0,1}(1) = 1`" is a *hypothesis* `hnorm : Fam.G 1 1 = 1`, not a reparametrisation performed. Faithful in content; the reparametrisation (rescale the scale axis) is a sentence in prose and is not in Lean. | none, or one-line blueprint note |
| R8 | F3 | statement-tightening | `main_characterization` (⇐), `cascadeFamily` (`Instance.lean`) | Theorem 7.3 (⇐) is stated for an *arbitrary* gauge `χ`: the family `Φ_{x,y} = μ_{χ(x),χ(y)} ∗ ·` satisfies the axioms. The Lean witness is the canonical gauge only (`S σ x = σ x`, kernels `F.kernel x y`). The general case is the canonical one reparametrised by `χ` — (A1)–(A7), (ND) transport trivially, (A8) with `S_σ = χ⁻¹(σ χ(·))`, and (A7) needs `χ` continuous, which an increasing bijection of `[0,∞)` is — but that reparametrisation lemma is not in Lean, and the article's own proof says "work in the canonical gauge" without stating it either. Surfaced by blind restatement A (§3, item 7). | **resolved (P2), in Lean** — `CascadeFamily.reparam` (`Reparam.lean`): any `χ` with `χ 0 = 0`, `StrictMonoOn (Ici 0)`, `SurjOn (Ici 0) (Ici 0)` (hence continuous, `continuousOn_of_strictMonoOn_surjOn`) reparametrises a family, `S' = χ⁻¹ ∘ S ∘ χ`; `cascadeFamily_reparam` is (⇐) in an arbitrary gauge, `rfl` |
| R9 | F3 | statement-tightening | `signaling_form` (1), `SignalingForm.lean:80` | Article's Thm 11.6(1) asserts two things: `H(s·)` *is in the domain of Def. 11.3* for every `c ∈ (0, z_*−1)`, and `A[H(s·)] = sH(s·)`. `A` being total in Lean, the domain claim is `RealisesSymbolAction c (H(s·)) (s·x·H(s·))`, proved as `realisesSymbolAction_profile` (`InversionOperator.lean:280`) but **not a conjunct of the assembled theorem**, which carries only the eigen-equation. Surfaced by blind restatement B (§11, items 3 and 5). | **resolved (P2)** — `signaling_form`(1) now `RealisesSymbolAction c (H(s·)) (s x H(sx)) ∧ A[H(s·)] = sH(s·)` |
| R10 | F4/F8 | claim-shaping (article side) | `signaling_form` (3), Lemma 11.4 vs `eventuallyEq_inversionSymbol_of_realisesAction` (`SymbolUniqueness.lean`) | The Lean hypothesises `RealisesAction c' B …` for **every** height `c'` in the range and concludes germ-agreement on the strip **without assuming `B` meromorphic**. The article fixes one `c`, says "of the form `x⁻¹B_i(θ)`" (implicitly: `B_i` meromorphic on the strip), and its proof reaches agreement on the *line* `Re z = c` and then says "on the strip outright" — the step from line to strip is the identity theorem and needs the meromorphy it never states. Two faithful statements exist: (a) `B` meromorphic + one height, or (b) every height, no meromorphy. Lean has (b); the article's *statement* is closer to (a) and its *proof* is a gap for (a). Blind restatement B found this independently (§11, item 4). | **resolved (P2)** — blueprint `lem:symbol-uniqueness` hypothesis "for some `s > 0`, at every height `c ∈ (0, z_*−1)`", proof rewritten (lines fill the strip; no identity theorem, no meromorphy); `thm:signaling-form`(3) "at every height"; draft Lemma 11.4 likewise (`10551df`) |
| R11 | F3 | note-only | `signaling_form` (2c) | Article: "with `û(s,0+) = f̂(s)`". Lean has `û(s,x) = f̂(s) H(sx)` for `x > 0` and (2b) `Φ_{0,x} f → f` in `X`; the scalar limit follows (`H(sx) → H(0) = 1`, `profile` continuous) but is not a conjunct. | **resolved (P2)** — `tendsto_laplaceFun_delayedField` (`SignalingForm.lean`), conjunct of (2c) |
| R12 | F5 | note-only | `IsLocalOfOrder c n`, `SatisfiesPMP c` carry the height `c` | Def. 12.1 is stated `c`-free ("the inversion operator `A`"); Def. 11.3 fixes `c`. Lean is honest that `A = A_c`; no independence-of-`c` is claimed anywhere (article or Lean). Blind restatement C flagged three inequivalent readings (fixed / ∀ / ∃ `c`); Lean's is "fixed `c`, hypothesis on every theorem", the article's Def. 11.3 reading. | none; blueprint already carries `c` |
| R13 | F3 | statement-tightening | `main_analysis` (⇒) | `χ 1 = 1` is not concluded, though true of `gauge S` (`gauge_orbit`, `S_one`); without it the (⇒) conjuncts pin `χ` only up to a positive scalar and the uniqueness clause's `χ(1) = 1` is not reachable from them. Vacuity pass, Theorem 2′. | **resolved (P2)** — `gauge_one` (`Gauge.lean`), exported by `similarity_form`, `main_analysis`, `main_analysis'` |
| R14 | robustness | note-only | witnesses of (⇒)'s hypotheses | Every Lean witness of a `CascadeCore` + `IsScaleCovariant` passes through `kernel`, hence A17; a pure-delay core `Φ x y := transL1 (y − x)`, `S σ x = σx`, would certify nonemptiness of the hypothesis class in Lean core. Vacuity pass, Theorem 2′. | optional (P5) |
| R15 | F3 | statement-tightening | `signaling_form` (2) | The theorem's "`u`" is two objects: (2a),(2c),(2d) are about `delayedField f`, (2b) about a free `q : X`; that `delayedField f · x` **is** `Φ_{0,x} f` (`coeFn_Phi_zero`, `MemoryFractional.lean:539`) and that `delayedField g` is its `X₀`-derivative (`delayedField_eq_setIntegral`, `:633`) are proved lemmas, not conjuncts — inside the theorem "`∂_t u`" is a comment. Vacuity pass, Theorem 4′. | **resolved (P2)** — conjuncts `Φ 0 x (toL1 f) =ᵐ delayedField f · x` (`coeFn_Phi_zero`) and `delayedField f t x = ∫_{Ioc 0 t} delayedField g` (`delayedField_eq_setIntegral'`, all `t`) |
| R16 | F3 | note-only | `signaling_form` (2d) | Lemma 11.5's "absolutely convergent" has no Lean clause: the two `mellin`s in (2d) are convergent inside the proof (`integrable_delayed`, `integrableOn_pastIntegrand_of_bounded`) but not asserted, so the honest form would carry `MellinConvergent` conjuncts. Not junk-true (both sides equal `H̃(z)(I^{z−1}f)(t) ≠ 0` generically). | **resolved (P2)** — `mellinConvergent_delayedField_pair`, conjunct of (2d) |
| R17 | F6 | note-only | A18 anchor (`AXIOMS.md`) | Independent as Lean axioms, A17 and A18 are entangled as *anchors*: reading A18's hypothesis as SSV Def. 5.14 passes through Thm 5.2's converse, which is A17's anchor. Not a strengthening (SSV's own proof does the same). | **resolved (P3)** — cross-reference paragraph added to A18's entry |
| R18 | F3 | note-only | `covariance_laplace` (`Covariance.lean:195`) vs Lemma 6.1 "is equivalent to" | Only (A8) ⇒ identities is under the tagged name; the converse is `dilL1_comp_mconvL1` + `mconvL1_congr`, used in `Instance.lean:221–225`. Elementary, available, not packaged. | open, optional: a converse lemma for literal iff-fidelity |
| R19 | cosmetic | note-only | `Covariance.lean` module docstring | Said clause (3) of `lem:action-rigidity` and `prop:canonical-gauge` were in `Skeleton/`; both proved. | **resolved (P3)** — docstring fixed |
| R20 | F8 | note-only | `lem:potential-kernel` annotation (`09-memory-kernels.tex`) | Said "Stated in Lean and decomposed, as `Skeleton.existsUnique_potentialKernel`… two sub-lemmas open"; the tag already pointed at the proved `Hemigroup` declaration. | **resolved (P4)** — annotation rewritten |
| R21 | F3 | note-only | `lem:potential-kernel` / `existsUnique_potentialKernel` | "`φ_x` is a nonzero Bernstein function, positive on `(0,∞)`" is not a conjunct of the `∃!`; carried by `exists_levyTriple_symbol`, `exists_subordinatorFamily`, `symbol_pos`. | **resolved (P4)** — said in the annotation |
| R22 | F3 | note-only | `lem:memory-kernel` first display | `∂_x F(xs) = sF'(xs)` has no standalone declaration; `symbol` defines the right side, chain rule inline where used. | accepted (note) |
| R23 | F3 | statement-tightening, trivial | `sonine_conservation` (`Sonine.lean:65`) | Restricted to `Ici 0` on both sides; unrestricted equality follows from causality of both factors. | **resolved (P4)** — `sonine_conservation'` |
| R5 | — | — | (update) | Checked in P4: no realness lemma for `A` on real test functions exists; the `Re` reading of `SatisfiesPMP` is a documented deliberate weakening. | **accepted with note** (T2.3f) |

Ledger entries are added as cards are written; a resolved entry keeps its row with the commit.

**State after P2 (2026-08-15).** All claim-shaping and statement-tightening findings on the two
headline theorems are resolved: Theorem 2′'s (⇒) concludes in `SelfDecomposableExponent` with
`χ 1 = 1` and identifies the kernels, (⇐) holds in an arbitrary gauge, and Theorem 4′ carries
its domain claim, its boundary value, the identification `u = Φ_{0,x}f`, the `X₀`-derivative,
and the convergence of its Mellin transforms as conjuncts; the two places where the article's
*statement* outran its proof (the Mellin form on the whole strip, the symbol uniqueness at one
height) are corrected in the text of record and the draft. Open: R14 (optional Lean-core
witness), R5 (P4 check), and the note-only rows. **Hub/paper action:** `linkage check` reports
two `[shared]` drift advisories — the paper's copies of `lem:symbol-uniqueness` and
`thm:signaling-form` must be re-synced to the blueprint by the paper-writing session.

**State after P3 (2026-08-15).** Tier 1 is complete: the chapter 4–6 supply chain (nine cards,
all faithful; one note-only, R18), the two ledger axioms (both faithful, axiom ≤ source on every
row against image-verified pages; R17 recorded), and Cor. 7.4 (faithful). No claim-changing
finding anywhere in Tier 1. P4 done — see below.

**State after P4 (2026-08-15).** Tier 2 complete: chapter 9 (seven cards), chapter 10 (three),
chapter 12 (eight) — every statement faithful; the one blind-restatement risk that mattered
(Lemma 10.3(1) as a norm bound only) does not arise, `Integrable` being an explicit conjunct.
Four note-only findings (R20–R23), two fixed in the text of record, one by a two-line Lean
strengthening; R5 accepted with note. Next: P5 (Tier 3, the F7 sweep, the draft↔blueprint
diff), then P6.

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

## Tier 1 — headline claims (P2)

### T1.1 `thm:main-characterization` · Theorem 7.3 = Theorem 2′ · `main_characterization` (`MainTheorem.lean`), through `cascadeFamily` (`Instance.lean`), `main_analysis` (`MainAnalysis.lean:100`), `gauge_and_exponent_unique` (`Uniqueness.lean`)

**Draft says.** A family satisfies (A1)–(A8), (ND) **iff** there exist an increasing bijection
`χ` of `[0,∞)` and `F` of the form (7.1), `F ≢ 0`, with `Φ_{x,y} f = μ_{x,y} ∗ f`,
`μ̂_{x,y}(s) = exp[−(F(χ(y)s) − F(χ(x)s))]`; in the canonical gauge the kernels are
`L⁻¹[e^{−F(xs)}]`; `(χ, F)` unique up to `χ(1) = 1`.

**Blueprint says.** The same at `thm:main-characterization` (a collation), split into
`thm:main-construction` (F ≢ 0 ⇒ the kernels *are* a `def:cascade-family` with `S_σ x = σx`),
`thm:main-analysis` (verbatim the draft's ⇒), and `prop:main-uniqueness` — already refined to
the Lean's shape: `F, F'` of the form (7.1), `F ≢ 0`, `χ` nondecreasing, positive on `(0,∞)`,
`χ(0+) = 0`, `χ(1) = 1`, `μ'_{χ(x),χ(y)} = μ_{x,y}` for `0 < x ≤ y` ⇒ `χ = Id`, `F' = F`.

**Lean says (unfolded, at `e3249b3`).**
* (⇐) `∀ F, hF → ∃ Fam : CascadeFamily, ∀ 0 ≤ x ≤ y, Fam.Φ x y = mconvL1 (F.kernel x y)`,
  witnessed by `F.cascadeFamily hF` whose `S σ x = σ * x` (`cascadeFamily_S`, `rfl`); `kernel x y`
  is the causal probability measure with `laplace = exp(−(increment x y s).toReal)`
  (`kernel_spec`) and `increment x y s + exponent (xs) = exponent (ys)` — i.e. the article's
  `μ_{x,y}` in the canonical gauge.
* (⇒) `∀ S Fam, IsScaleCovariant Fam (Ioi 0) S → ∃ χ b₀ k, χ 0 = 0 ∧ StrictMonoOn χ (Ici 0) ∧
  SurjOn χ (Ici 0) (Ici 0) ∧ (∀ σ > 0, x ≥ 0, χ (S σ x) = σ χ x) ∧ 0 ≤ b₀ ∧ AntitoneOn k (Ioi 0)
  ∧ (∀ t > 0, 0 ≤ k t) ∧ (∀ x ≤ y, Fam.Φ x y = mconvL1 (Fam.repr x y)) ∧ (∀ x ≤ y, s ≥ 0,
  laplace (Fam.repr x y) s = exp(−((levyExponentD b₀ k (χ y s)).toReal − (… (χ x s)).toReal)))
  ∧ ∃ s > 0, levyExponentD b₀ k s ≠ 0`. `Fam.repr x y` is *the* causal probability measure
  with `Φ x y = mconvL1 (repr x y)` (`existsUnique_repr`).
* (uniqueness) `∀ F F' χ, (χ > 0 on (0,∞)) → (χ monotone on (0,∞)) → (χ → 0 at 0+) →
  (∀ 0 < u ≤ v, F'.kernel (χ u) (χ v) = F.kernel u v) → χ 1 = 1 → hF → (∀ u > 0, χ u = u) ∧
  (∀ t ≥ 0, F'.exponent t = F.exponent t)`.

**Hypotheses/clauses.**
| article | Lean | class |
|---|---|---|
| (⇐) hypothesis: `F` of the form (7.1), `F ≢ 0` | `F : SelfDecomposableExponent`, `hF` | same (T0.2) |
| (⇐) hypothesis: *arbitrary* gauge `χ` | canonical gauge only | **weaker — R8** (the general gauge is a reparametrisation; not in Lean at `e3249b3`) |
| (⇐) conclusion: axioms hold, `S_σ x = σx` | `CascadeFamily` instance; `S = (σ, x) ↦ σx` | same, and stronger than "properties hold": the structure is inhabited |
| (⇒) hypothesis: (A1)–(A8), (ND) | `CascadeCore` + `IsScaleCovariant _ (Ioi 0) S` | same (T0.1) |
| (⇒) conclusion: `χ` increasing bijection of `[0,∞)` | `χ 0 = 0`, `StrictMonoOn (Ici 0)`, `SurjOn (Ici 0) (Ici 0)`; `MapsTo` follows from `χ 0 = 0` + strict mono | same; plus the extra `χ (S σ x) = σ χ x` (Prop. 6.3), stronger |
| (⇒) conclusion: `F` of the form (7.1) | `(b₀, k)` with sign/monotonicity; **finiteness not stated**; not packaged | **R1** — weaker in form; finiteness *is* forced (see junk audit) |
| (⇒) conclusion: `Φ_{x,y} f = μ_{x,y} ∗ f`, `μ̂ = e^{−(F(χ(y)s) − F(χ(x)s))}` | `Φ = mconvL1 (repr)`, transform identity in `toReal` form | same, given finiteness |
| (⇒) conclusion: `F ≢ 0` | `∃ s > 0, levyExponentD b₀ k s ≠ 0` | same, given finiteness (else `⊤ ≠ 0` would satisfy it vacuously — see audit) |
| "in particular … `L⁻¹[e^{−F(xs)}]`" | the measure `kernel 0 x` with transform `e^{−F(xs)}` | same in content; the article's density notation is loose (drift/delay kernels have no density) — note-only |
| uniqueness: `χ` increasing bijection, `χ(1) = 1`, same family | `χ` positive, monotone, `→ 0`, `χ 1 = 1`, equal *kernels* | **weaker hypotheses (stronger theorem)** on `χ`; "same family" ⇔ equal kernels by `mconvL1_injective` (`Representation.lean`) — the bridge exists |
| uniqueness conclusion: `χ = Id`, `F' = F` | `χ u = u` on `(0,∞)`; `F'.exponent = F.exponent` on `[0,∞)` | same (as functions, which is the right reading — data `(b₀,k)` are unique only a.e.) |
| trust boundary | (⇐), uniqueness: A17; (⇒): A18 | per-half `#print axioms` in `CIAxiomGuard.lean` |

**Junk-value audit.** (a) `(levyExponentD b₀ k u).toReal` with `u = χ y · s`: could `⊤` hide
here? If `levyExponentD b₀ k u = ⊤` for some `u > 0` then (monotone in `u`, and `SurjOn χ`) pick
`y` with `χ y = u/s`; the identity at `(0, y)` reads `laplace (repr 0 y) s = exp(−(⊤.toReal −
0)) = 1`, so `repr 0 y` is a causal probability measure with transform `1` at `s > 0`, hence
`δ₀`, hence `Φ 0 y = id`, contradicting `nondegenerate` (`y > 0` since `χ y > 0`). So finiteness
on `(0,∞)` is **forced by the conclusion + (ND)**, and at `u = 0` it is `0`. This is the reader's
derivation R1 asks to be replaced by a stated clause. (b) `∃ s, levyExponentD ≠ 0`: by (a) not
satisfied by `⊤`. (c) `Real.log`, `laplace` inside `repr`/`exponent`: T0.3. (d) `mconvL1 (kernel x
y)`: `IsFiniteMeasure` instance for all `x y` (junk `0` off the wedge, never read). (e)
`Classical.choose` in `kernel`, `repr`: all use through `_spec`/`existsUnique_repr`.

**Witness.** `witness_main_characterization_{drift,gamma,stable}` (P1): every hypothesis of
all three conjuncts, jointly.

**Blind restatement (agent A, §3 item 3).** Wrote (⇒) as `∃ γ E, F ≢ 0 ∧ ∀ x y, ∃ μ,
HasExponent μ (incr χ E x y) ∧ Φ x y = conv μ` — i.e. *packaged* in the exponent structure,
which is R1's point; (⇐) as a constructor `ofExponent (γ E hF)` for an **arbitrary** gauge
(R8); uniqueness as functions on `Ici 0` (✓); and warned against stating `E = E'` as structures
(the Lean does not) and against operator-norm continuity in (A7) (the Lean has SOT).

**Adversarial vacuity (agent, read-only, at `e3249b3`).** *No vacuous or junk attack.* Checked:
`dilL1` is a genuine isometry (`dilL1_dilL1_inv`, `dilL1_surjective`), `MapsTo` in
`IsScaleCovariant` is not redundant and is used (`S_zero`); (ND) real at drift; uniqueness's
`heq` cannot be met by junk since its RHS `F.kernel u v` is a probability measure (so `heq`
silently forces `0 ≤ χ u ≤ χ v`). Junk: finiteness of `levyExponentD b₀ k` is derivable as in
the audit above and, more to the point, is `htoReal` *inside* the proof (`MainAnalysis.lean:122`)
— available and not exported; `laplace` guarded by `integrable_exp_of_causal`; `Real.log` absent
from all three headline statements; `mconvL1` carries `IsFiniteMeasure` everywhere. Weakened
conclusion, new: **`χ 1 = 1` is not concluded (R13)**. Cosmetic: `MapsTo χ`, "repr is a causal
probability measure", the `μ̂` identity and `S = σ·` are def-level facts not in the bundle.
Strengthened hypotheses: none; uniqueness's are strictly weaker than the article's. Robustness:
every witness of the (⇒) hypotheses is A17-dependent (R14).

**Verdict (at `e3249b3`).** **faithful-with-tightenings (R1, R8, R13)**: the proved statement is the
article's; (⇒) should conclude in `SelfDecomposableExponent` and identify `repr` with `kernel`
(R1), and (⇐) is the canonical-gauge case (R8). Neither is claim-changing.

**Post-P2 verdict.** **faithful.** R1, R8, R13 resolved in Lean (`main_analysis'`,
`CascadeFamily.reparam`, `gauge_one`); the bundle's (⇒) is the round-trip form. Remaining:
R14 (optional).

---

### T1.2 `thm:signaling-form` · Theorem 11.6 = Theorem 4′ · `signaling_form` (`SignalingForm.lean:80`)

**Draft says.** Assume (H), canonical gauge. (1) for every `s > 0`, `H(s·)` is in the domain of
Def. 11.3 for every `c ∈ (0, z_*−1)` and `A[H(s·)](x) = sH(sx)`, `x > 0`. (2) for `f ∈ 𝒟`,
`u(·,x) = Φ_{0,x} f`: `u` causal in `t`; `u(·,x) → f` in `X₀` as `x ↓ 0`; Laplace form
`A[û(s,·)] = s û(s,·)` with `û(s,0+) = f̂(s)`; Mellin form for `t > 0`, `1 < Re z < z_*`:
`(∂_t u(t,·))~(z) = B(1−z) ũ(t,·)(z−1)`. (3) `A` is the unique operator in the covariant Mellin
class with property (1), hence with (2).

**Blueprint says.** Same statement; the annotation records that the Mellin form needs
`H̃(z−1) ≠ 0` (`rem:poles`) and that "of the form `x⁻¹B(θ)`" is the hypothesis that the
realising function exists.

**Lean says (unfolded, at `e3249b3`).** Hypotheses: `hH : StandingHypothesis` (T0.4), `hF`,
`0 < c`, `ofReal (c+1) < zStar`, `Measurable g`, `Integrable g`, `∀ r < 0, g r = 0`, `Measurable
f`, `Integrable f`, `∀ r, f r = ∫_{Ioc 0 r} g` — i.e. `HasCoreDeriv f g` unbundled (T0.8), the
article's `f ∈ 𝒟`. `delayedField f t x := ∫ τ, f (t − xτ) ∂lawT₁` = `E[f(t − xT₁)]` =
`(μ_{0,x} ∗ f)(t)` pointwise; `laplaceFun f s = ∫_{t>0} e^{−st} f t`. Conjuncts: (1) `∀ s > 0, x
> 0, inversionOperator c (H(s·)) x = s H(sx)`; (2a) `∀ x > 0, t < 0, delayedField f t x = 0`;
(2b) `∀ q : X, Φ 0 x q → q` as `x → 0⁺` in `X` (for the constructed family); (2c) `∀ s > 0, x
> 0, laplaceFun (delayedField f · x) s = H(sx) laplaceFun f s ∧ inversionOperator c (f̂(s) H(s·))
x = s (f̂(s) H(sx))`; (2d) `∀ z, 1 < Re z, ofReal (Re z) < zStar, t > 0, mellin H (z−1) ≠ 0 →
mellin (delayedField g t ·) z = inversionSymbol (z−1) · mellin (delayedField f t ·) (z−1)`; (3)
`∀ s > 0, B, (∀ c' ∈ (0, z_*−1), RealisesAction c' B (H(s·)) (s x H(sx))) → ∀ z ∈ strip(0,
z_*−1), inversionSymbol =ᶠ[𝓝[≠] z] B`.

**Hypotheses/clauses.**
| article | Lean | class |
|---|---|---|
| (H), canonical gauge | `hH`; the family is `F.cascadeFamily` | same |
| `f ∈ 𝒟` | `HasCoreDeriv f g` unbundled; `g` causal pointwise | same (R6 note) |
| `c ∈ (0, z_*−1)` | `0 < c`, `ofReal (c+1) < zStar` | same |
| (1) domain claim | **absent** (proved separately: `realisesSymbolAction_profile`) | **R9** |
| (1) eigen-equation | conjunct (1) | same |
| (2) `u = Φ_{0,x} f` | `delayedField f · x` — pointwise `E[f(t − xT₁)]`; its `L¹` class is `mconvL1 (kernel 0 x) f` — the identification lemma is named below (vacuity pass) | same if identified |
| (2) causal in `t` | (2a), pointwise for `t < 0` | same (stronger: pointwise) |
| (2) `u(·,x) → f` in `X₀` | (2b) for every `q : X`, in `X` | same (stronger: all of `X`; `X₀ ⊂ X` closed, so the same limit) |
| (2) Laplace form + `û(s,0+) = f̂(s)` | (2c) first half is `û(s,x) = f̂(s)H(sx)`, second is the eigen-equation for `f̂(s)H(s·)`; **the limit is absent** | **R11** (note-only; follows from `H(0)=1` and continuity) |
| (2) Mellin form on `1 < Re z < z_*` | (2d) **off the zeros of `H̃(z−1)`** | **R2**: article statement is stronger than provable pointwise (with `B(1−z)` a quotient) — the article's *own* proof and `rem:poles` say off the zeros; statement to be made explicit |
| (2) `∂_t u` = the `X₀`-derivative | `delayedField g t x`, i.e. `E[g(t − xT₁)]` with `g = f'` | same by definition of `𝒟`'s derivative |
| (3) uniqueness "in the covariant Mellin class with property (1)" | one `s`, every height, no meromorphy on `B`; germ agreement on the strip | **R10** — Lean is *stronger* than the draft's Lemma 11.4 (one `s` suffices) and *differently shaped* (every height instead of meromorphy + one height); article's proof has the line-to-strip gap |
| (3) "hence with property (2)" | absent | note-only: (2)'s Laplace form at one `f` with `f̂(s) ≠ 0` is (1) at that `s`; the Lean's (3) already needs only one `s` |

**Junk-value audit.** (a) `mellin` in (2d), both sides: convergent on the strip
(`lem:delayed-average-mellin`, `lem:memory-fractional-integrals` — `mellin_delayedField_deriv`,
`MemoryFractional.lean`); the identity is therefore not `0 = B·0`, though a `MellinConvergent`
conjunct would be the honest form (vacuity pass below). (b) `inversionSymbol (z−1)` at zeros of
`H̃(z−1)`: excluded by hypothesis. (c) `inversionOperator c g x`: `mellinInv` of a vertically
integrable function (`RealisesAction.verticalIntegrable`, `lem:mellin-vertical`) — genuine; and
(1)'s RHS `s H(sx) > 0` so no junk-truth. (d) `laplaceFun`: Bochner of `e^{−st} f` with `f ∈ L¹`,
`s ≥ 0` — integrable. (e) `zStar − 1` in `ℝ≥0∞`: `zStar > 1` under (H). (f) (3): the hypothesis
is satisfiable (by `inversionSymbol` itself, `realisesSymbolAction_profile`), so (3) is not
vacuous; and `inversionSymbol` is not `0` on any open subset of the strip (`inversionSymbol_eq`:
`z · m(z+1)/m(z)` with `m > 0` on the real axis and analytic) — so the conclusion is not trivial.

**Witness.** `witness_signaling_form_{drift,gamma}` (P1): all ten hypotheses jointly.

**Blind restatement (agent B, §11 item 5).** Same six-conjunct shape; demanded the domain
conjunct in (1) (R9), `MellinConvergent` conjuncts in (2d), the `H̃(z−1) ≠ 0` hypothesis in (2d)
("the whole-strip statement is false with junk division; the draft's *statement* is imprecise
here"), (2b) at `𝓝[>] 0` (✓), `f ∈ X₀` as a separate demand (✓), and read (3) as Lemma 11.4
instantiated (✓, modulo R10).

**Adversarial vacuity (agent, read-only, at `e3249b3`).** *No vacuous or junk attack.*
`zStar` is the article's `z_*` in both directions (`negMoment_ne_top_of_lt_zStar`,
`le_zStar_of_negMoment_ne_top`); the drift witness's `zStar = ⊤` is an honest
`zStar_eq_top_of_forall_negMoment_ne_top`, the Gamma witness's negative moments are computed
against Mathlib's `gammaMeasure`. (1)/(2c): `inversionOperator_eq` rewrites the integrand a.e. to
`mellin h` and applies Mathlib's `mellinInv_mellin_eq` with genuine `MellinConvergent` and
`VerticalIntegrable` (`realisesSymbolAction_profile`); RHS `> 0`. (2d): no `MellinConvergent …
delayedField` lemma exists, but the proof forces convergence (`mellin_delayed_average` via
`integral_integral_swap (integrable_delayed …)`; RHS via `integrableOn_pastIntegrand_of_bounded`)
— **R16**. (3): hypothesis satisfiable by `inversionSymbol` itself and, since only `mellin_eq`
depends on `B`, *equivalent* to "`B = inversionSymbol` off the zeros of `H̃` on the strip" — thin
by the article's own design (Lemma 11.4's "no injectivity needed"), not vacuous; `zStar − 1`
strip nonempty under (H) (`ofReal_lt_sub_one_iff`). Weakened conclusion, new: **the theorem's
`u` is two objects — `delayedField f` in (2a),(2c),(2d) and a free `q` in (2b) — and neither
`u = Φ_{0,x} f` (`coeFn_Phi_zero`) nor "`∂_t u` is the derivative" (`delayedField_eq_setIntegral`)
is a conjunct (R15)**; (2c-ii) is stated on `f̂(s)H(s·)` rather than on `û(s,·)` (coincide since
`mellin` reads `Ioi 0` — cosmetic). Redundant hypotheses: `hF` (implied by `hH.1`), `hfm`
(`hf` makes `f` continuous). Definitions: `inversionSymbol (z−1) = B(1−z)`, `inversionOperator`
= Def. 11.3, `profile`, `lawT₁ = μ_{0,1}`, `kernel_zero_eq_map_lawT₁` (canonical gauge),
`laplaceFun`, `mellin` — all ✓.

**Verdict (at `e3249b3`).** **faithful-with-tightenings (R2, R9, R10, R11, R15, R16)**: (2d) and (3) are the article's
claims *as the article's own proofs establish them*, and the article's statements should say so
(R2, R10 — text of record); (1) and (2c) each drop a conjunct that is proved elsewhere (R9, R11).
Nothing is vacuous and nothing proved is weaker than what the article's proofs prove.

**Post-P2 verdict.** **faithful.** R9, R11, R15, R16 resolved as conjuncts of `signaling_form`
(guard: A17 only, unchanged); R2, R10 resolved in the text of record and the draft. Remaining:
the paper's mirror of the two statements (hub/paper session).


### T1.3 The supply chain of `thm:main-analysis` — chapters 4–6 (P3)

Cards written by two read-only agents against the draft, the blueprint and the Lean, reviewed by
the integrator; each unfolds to primitives and audits junk values. Abbreviated where nothing
was found.

**T1.3a `lem:convolution-representation` (Lemma 4.1) · `CascadeCore.existsUnique_repr`
(`Representation.lean:937`), `mconvL1_satisfies_axioms` (`Family.lean:245`).** Lean: `∃ μ
[IsProbabilityMeasure μ], IsCausal μ ∧ Φ x y = mconvL1 μ ∧ ∀ ρ [IsProbabilityMeasure ρ], IsCausal ρ
→ Φ x y = mconvL1 ρ → ρ = μ` for `0 ≤ x ≤ y` — the `∃!` written out; the converse gives (A2)–(A5)
for `mconvL1 μ` from `IsProbabilityMeasure` + `IsCausal` and (A1) by the type. Stated over
`CascadeCore` (which carries (A6), (A7), (ND) too) but the proof reads only (A1)–(A5) — unread
fields, not a strengthening. `repr` off the wedge is `δ₀`, unread. **faithful.**

**T1.3b `lem:transform-continuity` (Lemma 4.2) · `CascadeCore.transform_continuity`
(`TransformContinuity.lean:196`).** Four conjuncts: `0 ≤ exponent x y s` for `s ≥ 0`; `exponent x
y 0 = 0` (exact, `laplace_zero_prob`, not a limit); `ContinuousOn (fun p => exponent p.1 p.2 s)
Index` with `Index = {0 ≤ p.1 ≤ p.2}`; `ContinuousOn (exponent x y) (Ici 0)`. `Real.log` guarded
by `laplace_pos_of_prob` (T0.3). **faithful.**

**T1.3c `lem:additivity` (Lemma 5.1) · `CascadeCore.additivity` (`Additivity.lean:153`).** Eight
conjuncts in the draft's order: `repr x z = repr x y ∗ repr y z` (draft writes `μ_{y,z} ∗ μ_{x,y}`
— commutative, the same measure); `exponent x z = exponent x y + exponent y z`; `exponent x x = 0`;
`exponent x y s = G y s − G x s`; `G 0 s = 0`; `MonotoneOn (G · s) (Ici 0)`; `ContinuousOn (G · s)
(Ici 0)`; `G x 0 = 0`. No partial functions. Lean core. **faithful.**

**T1.3d `thm:increments-bernstein` (Theorem 5.2) · `CascadeCore.exponent_hasLevyRep`
(`LevyTriple.lean:254`).** Draft: `g_{x,y} ∈ BF₀`. Blueprint: both readings, `BF₀` and — via
ledger A3 — `LE`, as CLAUDE.md requires. Lean: `∃ b₀ ≥ 0, ν, IsCausal ν ∧ ∀ s ≥ 0, ofReal
(exponent x y s) = levyExponent b₀ ν s` — the `LE` reading exactly; `ℝ≥0∞`-valued with no
`.toReal`, `ofReal` never truncates (`exponent_nonneg`). `IsCausal ν` allows an atom at `0`,
invisible to the integrand; the constructed `levyMeasure ρ` has none anyway
(`isCausal_levyMeasure`). **faithful-with-note** (the vocabulary crossing is done in the
statement, where it belongs).

**T1.3e `cor:strict-monotonicity` (Cor. 5.3) · `CascadeCore.strict_monotonicity`
(`LevyTriple.lean:310`).** `∀ 0 ≤ x < y, s > 0, G y s − G x s = exponent x y s ∧ 0 < exponent x y
s`. (ND) enters through `nondegenerate` → `exists_exponent_ne_zero` → `exponent_pos` with the
vanishing lemma — the blueprint's route. **faithful.**

**T1.3f `lem:covariance-laplace` (Lemma 6.1) · `CascadeCore.covariance_laplace`
(`Covariance.lean:195`).** Draft: under (A1)–(A5), (A8) **is equivalent to** `D_σ μ_{x,y} =
μ_{S_σx,S_σy}` ⟺ `g_{S_σx,S_σy}(s) = g_{x,y}(σs)`, in particular (6.1). Lean: from `hcov :
IsScaleCovariant Fam Gs S`, three identities — `(repr x y).map (σ·) = repr (Sσx) (Sσy)`, the
exponent identity, the `G` identity (6.1). **One direction only** ((A8) ⇒ identities); the
converse (identities ⇒ (A8)) is `dilL1_comp_mconvL1` + `mconvL1_congr` (`Family.lean:207,126`),
used as such in `Instance.lean:221–225` to prove (A8) for the constructed family, but not
packaged under the tagged name. **faithful-with-note (R18).**

**T1.3g `lem:action-rigidity` (Lemma 6.2) · `CascadeCore.action_rigidity`
(`Covariance.lean:338`).** All four clauses: `S_σ` unique given (6.1) (`eq_of_G_eq`, at `s > 0`);
group law + `S_1 = Id`; `σ ↦ S_σ x` continuous and strictly increasing for `x > 0`
(`continuousOn_S_apply`, `strictMonoOn_S_apply`); no fixed point in `(0,∞)`
(`eq_zero_of_fixed`). `Ioi 0` = the article's `σ > 0`. Proof route differs from the draft's
(uses `laplace_strictAnti`, no derivative) — F7, recorded in the blueprint. Stale file docstring
said clause (3) was in `Skeleton/` — fixed (R19). **faithful.**

**T1.3h `prop:canonical-gauge` (Prop. 6.3) · `CascadeCore.canonical_gauge` (`Gauge.lean:274`).**
Lean: `∃ χ, χ 0 = 0 ∧ StrictMonoOn χ (Ici 0) ∧ SurjOn χ (Ici 0) (Ici 0) ∧ (∀ σ x, χ (S σ x) = σ χ
x) ∧ (∀ x s, G x s = G 1 (χ x · s))`; `χ = gauge S := invFunOn (σ ↦ S σ 1) (Ioi 0)` extended by
`0` — **not** an `sSup`; junk-safe because `exists_orbit_eq` proves surjectivity first, so
`invFunOn`'s default branch is never taken for `y > 0`. Absent as conjuncts, deliberately and
recorded: `F ∈ BF₀`/`LE` and `F ≢ 0` (they are `thm:increments-bernstein` and
`cor:strict-monotonicity` at `F = G(1,·)`, nothing new). `gauge_one` (P2) adds `χ 1 = 1`.
**faithful.**

**T1.3i the machine-checked collation · `CascadeCore.similarity_form` (`MainAnalysis.lean:77`)**
— not a `\lean`-tagged node; the blueprint annotation of `thm:main-analysis` names it as
"everything but the last step". Conclusion: gauge (with `χ 1 = 1` since P2), `Φ x y = mconvL1
(repr x y)`, `laplace (repr x y) s = exp(−(G 1 (χ y s) − G 1 (χ x s)))`, **`∀ 0 < a ≤ b, ∃ b₀ ν,
IsCausal ν ∧ ofReal (G 1 (bs) − G 1 (as)) = levyExponent b₀ ν s`** (the `LE` reading of "every
increment `F(b·) − F(a·) ∈ BF₀`", quantified over arbitrary `0 < a ≤ b` via `SurjOn χ` — exactly
A18's `hincr`), and `∀ s > 0, G 1 s ≠ 0` (stronger in form than `F ≢ 0`, equivalent by
`cor:strict-monotonicity`). `ofReal` safe by monotonicity of `G` in the scale. **faithful.**

---

### T1.4 The trust boundary — ledger A17, A18 · `Interfaces.lean` (F6)

Source pages image-verified: Thm 5.2 p. 49 and the killing sentence p. 51 fetched today by the
librarian (`library page schilling2012bernstein --printed 49/51 --format image`, running header
"Chapter 5 A probabilistic intermezzo"); Def. 5.14 p. 55 and Prop. 5.17 p. 57 verbatim in
`AXIOMS.md` (image-verified 2026-08-10). Every row is judged "axiom ≤ source": the axiom's
hypothesis class lies inside the source's, its conclusion is implied by the source's.

**T1.4a A17 · `exists_isFiniteMeasure_laplace_eq_exp_neg_levyExponent` · SSV Thm 5.2 p. 49,
converse clause.**
| row | judgement |
|---|---|
| objects: `IsCausal ν`, `∀ s ≥ 0, levyExponent b₀ ν s ≠ ⊤` vs Lévy measure on `(0,∞)` with `∫(1∧t)dν < ∞` (Thm 3.2) | ≤ — the docstring's bound `1 − e^{−st} ≥ (1 − e^{−s}) min(1,t)` (`t ≥ 1`: monotone; `t < 1`: concavity above the chord) is checked, so finiteness at one `s > 0` gives `∫(1∧t)dν < ∞`; an atom of `ν` at `0` is invisible (`1 − e^{0} = 0`) |
| killing: `levyExponent` has no `a` | ≤ — the `a = 0` case; the probability upgrade is *proved* (`exists_isProbabilityMeasure_…`, `Interfaces.lean:90–101`, from `levyExponent_zero` at `s = 0`), consistent with p. 51 |
| asked for: one finite causal `μ` with `laplace μ s = exp(−(…).toReal)`, `s ≥ 0` | ≤ — the `t = 1` slice of the semigroup; `IsCausal μ` **is** in the conclusion, so `laplace` over `ℝ` equals the source's `∫_{[0,∞)}`; `.toReal` guarded by `hfin` |
| uniqueness | not asked; `laplace_injective` (`Injectivity.lean:198`), `kernel_unique` (`Construction.lean:286`) — proved |
| minimality | sole consumer `exists_kernel` (`Construction.lean:230–245`) instantiates exactly the axiom's shape |
| consistency | standard mathematics with the source's proof; hypothesis class non-empty (`Examples.lean`); no mis-transcription found |
**Verdict: faithful, axiom ≤ source.**

**T1.4b A18 · `exists_antitone_density_of_dilation_increments` · SSV Prop. 5.17 p. 57 (ii)⇒(i),
Def. 5.14 p. 55.**
| row | judgement |
|---|---|
| hypothesis `hincr`: `∀ 0 < a ≤ b, F(b·) − F(a·) = levyExponent c₀ ρ` (no killing) vs (ii) `g(λ)/g(cλ)` CM, `c ∈ (0,1)` | ≤ — ours ⇒ theirs by the cheap direction (`f ∈ BF ⇒ e^{−f} ∈ CM`, SSV's own p. 59 step); `c = a/b`, `λ = bs` a bijection; killing forced to `0` (Remark 3.3(iv)); "vanishing at `0+`" automatic |
| **anchor entanglement** | Prop. 5.17 is about `π` with `L(π) = e^{−f}`; our axiom is about `F`. The bridge "`F ∈ BF`, `F(0+) = 0` is the exponent of some `π`" is Thm 5.2's converse — A17's anchor. Independent as Lean axioms (guard prints each on its own consumers); entangled as anchors. Not a strengthening — SSV's proof performs the same bridge. **R17**, recorded in `AXIOMS.md` |
| conclusion `∃ c₀ k, 0 ≤ c₀ ∧ AntitoneOn k (Ioi 0) ∧ k ≥ 0 ∧ ofReal (F s) = levyExponentD c₀ k s` vs (i) Lévy measure has density `m` with `t·m(t)` nonincreasing, drift untouched | ≤ — the axiom allows a *different* drift `c₀`; the sole consumer `main_analysis` (`MainAnalysis.lean:112–145`) never compares `c₀` with `b₀`, so the weaker conclusion is exactly what is used; `k`'s integrability implied by `ofReal (F s) ≠ ⊤` |
| non-vacuity | `exists_levyExponent_dilation_increment` (`SelfDecomposable.lean:291`) shows genuine self-decomposable exponents satisfy `hincr`'s exact shape, without A18 |
| minimality | consumer supplies `hincr` verbatim from `similarity_form` |
**Verdict: faithful, axiom ≤ source; one note (R17).**

---

### T1.5 `cor:semigroup-case` · Cor. 7.4 · `CascadeCore.semigroup_case` (`SemigroupCase.lean:233`)

(Definition side and normalisation: T0.7.) Lean: `hcov`, `hone`, `hnorm : G 1 1 = 1` ⇒ `∃ α, 0 < α
∧ α ≤ 1 ∧ (∀ s ≥ 0, G 1 s = s^α) ∧ (∀ x s ≥ 0, G x s = x s^α) ∧ (∀ σ > 0, x ≥ 0, S σ x = σ^α x)`.
Both bounds are conclusions (`0 < α` from strict monotonicity of `S`, i.e. (ND); `α ≤ 1` from
`levyExponent_add_le` at `s = t = 1`, `2^α ≤ 2` — subadditivity, not full `BF₀`); `α = 1`
admitted, matching Remark 7.5; `S σ x = σ^α x` extra. `Real.rpow` at `s = 0` handled
(`Real.zero_rpow`). Witness: `witness_semigroup_case_drift` (`α = 1`); no `α < 1` witness, since
the canonical-gauge stable core is not one-parameter (the one-parameter stable semigroup is its
`reparam` by `x ↦ x^{1/α}`, now available — a witness through `CascadeFamily.reparam` is
possible, R14-adjacent, optional). **faithful.**

## Tier 2 — the "theorem content" the introduction promises (P4)

Three read-only card passes (one per chapter), reviewed by the integrator. Definitions were
audited at T0.6/T0.8; these are the statements. All abbreviated.

### T2.1 Chapter 9 — memory kernels, Sonine conservation, Volterra

**T2.1a `lem:memory-kernel` (Lemma 9.1, first display) · `hasDerivAt_toRealExponent`
(`ExponentDerivative.lean:296`).** `HasDerivAt toRealExponent (b₀ + ∫_{t>0} e^{−st} k t) s` for
`s > 0` — a `HasDerivAt`, not a `deriv` equation, so no off-differentiability junk; `F' = b₀ + ∫
e^{−st} k` exactly. The display's *first* equality `∂_x F(xs) = sF'(xs)` has no standalone
counterpart — `symbol x s := s · deriv toRealExponent (xs)` *defines* the right side, and the
chain rule is done inline where needed (`Volterra.lean:164–170`) — R22, note-only. **faithful.**

**T2.1b `lem:potential-kernel` (Lemma 9.4) · `existsUnique_potentialKernel`
(`PotentialKernel.lean:201`).** `Nondegenerate → 0 < x → ∃! ℓ, IsCausal ℓ ∧ (∀ T, ℓ (Icc 0 T) ≠
⊤) ∧ ∀ s > 0, laplaceL ℓ s = ofReal (symbol x s)⁻¹` — the article's specification, existence by
Route B inside the proof; A17 only. **No chosen potential-kernel object exists in `Hemigroup/`**:
every consumer quantifies over an `ℓ` meeting the spec, so there is no `Classical.choose` to
audit. `(symbol x s)⁻¹` guarded by `symbol_pos hnd`. The article's first sentence ("`φ_x` is a
nonzero Bernstein function, positive on `(0,∞)`") is carried by `exists_levyTriple_symbol`
(`:50`, the `LE` reading), `exists_subordinatorFamily` and `symbol_pos`, not by the `∃!`'s
conjuncts — R21, note-only, now said in the blueprint annotation. The annotation had gone stale
("Skeleton…, two sub-lemmas open") — R20, fixed. **faithful.**

**T2.1c `thm:sonine-conservation` (Thm 9.5) · `sonine_conservation` (`Sonine.lean:65`).**
`Nondegenerate → 0 < x → [SFinite ℓ] → IsCausal ℓ → (transform spec) → (memoryKernel x ∗
ℓ).restrict (Ici 0) = volume.restrict (Ici 0)`; Lean core (`laplaceL_injective_of_ne_top`). The
three hypotheses on `ℓ` are the article's `ℓ^{(x)}` unpacked, deliberately decoupled from
existence. Restricted on both sides — R23, trivial tightening (`sonine_conservation'`, P4).
**faithful-with-note.**

**T2.1d `prop:volterra`, `prop:volterra-uniqueness` (Prop. 9.8) · `volterra`, `volterra_unique`
(`Volterra.lean:149,205`).** `t μ_x(dt)` ↦ `(kernel 0 x).withDensity (t ↦ ofReal t)`; `θ_x` ↦
`volterraKernel x := ofReal x • memoryKernel x` (= `x·κ^{(x)}`, as the blueprint says);
`volterra : … = volterraKernel x ∗ kernel 0 x`; `volterra_unique : IsProbabilityMeasure ν →
IsCausal ν → (identity for ν) → ν = kernel 0 x` — the article's class exactly. No
`Classical.choose`, no `.toReal`. **faithful.**

**T2.1e `prop:sonine-pair-exists` · `exists_sonine_pair` (`PotentialKernel.lean:237`).**
Collation of b + c; inherits R23. **faithful.**

**T2.1f `lem:memory-kernel-transform` · `laplace_memoryKernel`
(`MemoryKernelTransform.lean:70`).** `laplace (memoryKernel x) s = symbol x s / s`, `x, s > 0` —
the display's second equality; `laplace` (Bochner) of a non-finite measure, integrability proved
piecewise (atom + density) inside; companion `laplaceL_memoryKernel_ne_top`. **faithful.**

**T2.1g `lem:potential-kernel-scaling` · `potential_kernel_scaling`
(`PotentialScaling.lean:77`).** For any `ℓ₁, ℓx` meeting the spec at scales `1`, `x`: `ℓx =
ofReal x • ℓ₁.map (x·)` — **the scalar `x` is there** (sup-normalisation), so in density form
`ℓ^{(x)}(t) = ℓ^{(1)}(t/x)` with no extra factor, as the draft's "Moreover" says. Quantified
over any two measures meeting the spec (uniqueness pins them). **faithful.**

`Skeleton.hasCMDensity_iff` (`Skeleton/Chapter9.lean:178`): `sorry`-marked, outside
`Hemigroup/`, uncited, not in the guard — nothing claimed.

### T2.2 Chapter 10 — the delay core and the generator

**T2.2a `lem:delay-core` (Lemma 10.1) · `delay_core` (`DelayCore.lean:773`).** `causalL1 ⊆
closure coreL1` (density in `X₀`, as a closure inclusion because `𝒟` is not dense in `X`) ∧
`T_r`-invariance ∧ **`mconvL1 μ`-invariance for every causal probability `μ`** (more general
than "every `Φ_{x,y}`"; the specific reading via `Φ x y = mconvL1 (repr x y)`) ∧ the difference
quotient `r⁻¹ • (transL1 r F − F) → −G` at `𝓝[>] 0` for `HasCoreDerivL1 F G` ∧ `‖transL1 r F −
F‖ ≤ min (2‖F‖) (r‖G‖)`. No partial functions. `memCore_iff_signaling_hypotheses` (`:377`) is an
*iff* between `HasCoreDeriv f g` and the six signal hypotheses of `signaling_form`. **faithful.**

**T2.2b `def:phillips-generator` (Def. 10.2).** Both displays: `phillipsGenerator` (`:427`) and
`phillipsGenerator_eq_smul_integral` (`:436`); tag correct. **faithful.**

**T2.2c `lem:generator-properties` (Lemma 10.3) · `generator_properties`
(`PhillipsGenerator.lean:901`).** Hypotheses `HasLevyTail ν`, `HasCoreDerivL1 A B`, `x > 0`.
**(1) is `Integrable (fun r => A − transL1 r A) (dilatedTail ν x) ∧ ‖…‖ ≤ b₀‖B‖ + x⁻¹ ∫ min (2‖A‖)
(x r ‖B‖) ∂ν`** — the `Integrable` conjunct is explicit and proved first
(`integrable_sub_transL1`, `:514–525`), so the blind-restatement worry (a norm bound provable
from junk `0`) does not arise. (2) `laplaceFun (…) s = symbol x s · laplaceFun A s`, `s > 0`,
`deriv` genuine (`hasDerivAt_toRealExponent`). (3) commutation with `mconvL1 μ` for causal
probability `μ` (the lemma beneath holds for any finite `μ`). (4) `ContinuousOn (fun y =>
phillipsGenerator ν y A B) (Ioi 0)` in `X`. (5) `mconv (memoryKernel x) f =ᵐ fun t => ∫_{Ioc 0 t}
phillipsGenerator …` (the lemma beneath is everywhere-equality). **faithful.**

### T2.3 Chapter 12 — the locality chain

**T2.3a `lem:local-polynomial-symbol` (Lemma 12.2) · `nonempty_isLocalOfOrder_iff_symbol_eq`
(`ProfileEuler.lean:669`), `exists_symbol_eq_of_isLocalOfOrder` (`:556`).** Symbol identity on
**the whole strip** `0 < Re z < z_*−1` off the zeros of `H̃`; degree = `γ n ≠ 0`; coefficients
`coeff j x = γ j x^{j−1}` in the separate declaration. **faithful** (to the blueprint; R3 for
the draft, resolved).

**T2.3b `lem:log-convexity` (Lemma 12.4) · `convexOn_log_negMoment` (`Locality.lean:100`).**
`ConvexOn ℝ momentInterval (ζ ↦ log (negMoment ζ).toReal)` on `(0, z_*)`, not `(0,∞)` — the
correct unconditional domain, equal to `Ioi 0` once A13 is spent (`momentInterval_eq_Ioi`);
`.toReal` guarded by `negMoment_ne_top_of_lt_zStar`, `log` by `negMoment_pos` under the no-atom
clause. **faithful.**

**T2.3c `lem:symbol-vanishes-at-origin` (draft 12.3(1)) · `tendsto_inversionSymbol_nhdsGT_zero`
(`Locality.lean:188`).** `B(0+) = 0` as a limit, with **no** polynomial hypothesis (inert in the
proof); `B(0) = 0` as a value follows for `B` continuous at `0`, in the caller. **faithful.**

**T2.3d `lem:gamma-recursion-uniqueness` · `eq_gamma_form_of_logConvex_of_recursion`
(`GammaRecursion.lean:175`).** Abstract: `m > 0`, `log ∘ m` convex on `Ioi 0`, `m(z+1) = c(z+a)
m(z)`, `m → 1` at `0+` ⇒ `m z = c^z Γ(a+z)/Γ(a)`. No project object; Lean core (Bohr–Mollerup);
A15 discharged in the linear-`Q` case. **faithful.**

**T2.3e `lem:moment-recursion-quotient` (draft 12.3(2)–(3)) · `exists_symbolQuotient_of_isLocalOfOrder`
(`MomentRecursion.lean:226`).** `∃ Q, (∀ z, symbol_poly z = z Q z) ∧ ∀ 0 < z < z_*−1, ∃ q > 0, Q z
= q ∧ m(z+1) = q m(z)` — **no `hA13`**, on exactly the range README claims. **faithful.**

**T2.3f `lem:pmp-verification` · `satisfiesPMP_of_symbol_eq`
(`PositiveMaximumPrinciple.lean:177`).** Concludes `Re (A g)(x₀) ≤ 0`; **no realness lemma
exists** for `A` on real test functions, so R5 does **not** close — the weaker reading is
deliberate and documented (`LocalOperator.lean:107`); as a *hypothesis* (A14's use in
`thm:locality`) it costs nothing. **faithful-with-note (R5, accepted).**

**T2.3g `lem:local-moment-classification` · `exists_moment_form_of_isLocalOfOrder`
(`LocalityClassification.lean:85`).** Hypotheses `hH`, `hA13 : AllNegMomentsFinite` (A13 as an
assignment), `0 < c`, `n ≤ 2` (A14's order bound as an assignment), `IsLocalOfOrder c n`;
conclusion the pure-power / shifted-Gamma dichotomy on `Ioi 0`; guard prints A17 only. **faithful.**

**T2.3h `thm:locality` (Thm 12.5).** No `\lean` tag (`[A]` on A14; A13 transitively; A15
discharged; A16 belongs to `prop:local-ladder`). Machine-checked beneath it: the four `[T]`
nodes above. **faithful as an `[A]` collation.**

## Witnesses (P1) — `Formalization/Hemigroup/Witnesses.lean`

Named theorems, `#print axioms`-guarded in `CIAxiomGuard.lean` (17 lines under
`### Witnesses (PLAN-fidelity-review P1)`), nothing importing the file. Every witness prints
Lean core, or Lean core + A17 where it quantifies over the constructed kernels; **none reaches
A18**. Verified 2026-08-15: `lake build` clean, guard exit code 0.

| target | model | hypotheses discharged | theorem |
|---|---|---|---|
| `main_characterization` (⇐) `hF` | drift `b₀ > 0`; Gamma `γ > 0`; stable all `α` | all | `witness_hF_{drift,gamma,stable}` |
| `main_characterization` (⇒) `IsScaleCovariant` | any `F` with `hF`, at `(F.cascadeFamily hF).toCascadeCore`, `S σ x = σ x` (`cascadeFamily_S`, `rfl`) | all | `witness_main_characterization_covariant` |
| `main_characterization` uniqueness | `χ = id`, `F' = F` | all six | `witness_main_characterization_uniqueness` |
| all three conjuncts jointly | drift / Gamma / stable | all | `witness_main_characterization_{drift,gamma,stable}` |
| `signaling_form` | drift (any `c > 0`, `z_* = ∞`); Gamma `γ > 1`, `c = (γ−1)/2` | **all ten**: (H), `hF`, `hc`, `hc'`, and the six signal clauses at the tent `f = ∫₀^· (box − box(·−1))` | `witness_signaling_form_{drift,gamma}` |
| `semigroup_case` | drift `b₀ = 1` | `IsScaleCovariant`, `IsOneParameter`, `G 1 1 = 1` | `witness_semigroup_case_drift` |
| `lem:local-polynomial-symbol` | drift (+ `AllNegMomentsFinite`); Gamma `γ > 1` | (H), `0 < c < z_* − 1` | `witness_local_polynomial_symbol_{drift,gamma}` |

New supporting facts proved on the way (all Lean core or A17): `driftExponent b₀` as a
`SelfDecomposableExponent` with `kernel a b = δ_{b₀(b−a)}`, `lawT₁ = δ_{b₀}`, all negative
moments finite; `gammaExponent γ` has `lawT₁ = gammaMeasure γ 1` and `negMoment ζ ≠ ⊤` for
`ζ < γ`, hence `StandingHypothesis` for `γ > 1`; `repr_cascadeFamily : repr = kernel`;
`hasCoreDeriv_tent : HasCoreDeriv tent tentDeriv`.

**Findings from P1.**
* **No hypothesis is unsatisfiable, and none needs a restriction the article does not state.**
  In particular the plan's worry that `hc'` might force `γ > 2` for Gamma does not arise:
  `hc' : c + 1 < z_*` leaves room for `c = (γ−1)/2` at every `γ > 1`, so (H)'s own boundary is
  the only one.
* The `f ∈ L¹` clause of `signaling_form` is a real constraint on the signal (the clipped ramp
  from `g = box` fails it; a `g` with `∫ g = 0` is needed) — as the `SignalingForm.lean`
  docstring says, and as the article's `f ∈ 𝒟 ⊆ X₀` imposes. Confirms T0.8's reading.
* Not shown: `StandingHypothesis` for the stable family (needs a negative moment of the positive
  stable law past the first; no closed form for its density in the development). Not a finding
  about the theorem — the drift and Gamma witnesses already show the hypotheses are jointly
  satisfiable — but a gap in the model coverage: the stable family is the article's Example 8.1
  and satisfies (H) with `z_* = ∞`; a witness would need `E[T₁^{−ζ}] < ∞` from the Laplace
  transform alone (`E[T^{−ζ}] = Γ(ζ)⁻¹ ∫ s^{ζ−1} e^{−s^α} ds`, which is Lemma 11.2's own
  computation run without (H) — a possible route, left open).
* `IsOneParameter` fails for Gamma and stable *in the canonical gauge*, correctly: the
  one-parameter stable semigroups with `α < 1` are those cores reparametrised by `x ↦ x^{1/α}`.
  That reparametrisation is exactly the lemma **R8** asks for, so R8 has a second consumer.
