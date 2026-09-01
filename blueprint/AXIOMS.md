# Axiom provenance ledger — hemigroup causal scale-space kernels

The project's **trust boundary**. Every `[A]` analytic-interface node in the blueprint is
grounded here, in a named theorem with a page anchor, resolved through the librarian.

Format contract (enforced by `linkage check`, fatal checks 2 and 6):

```
## A<N> — <one-line statement of what is taken on trust>
**Blueprint:** `<label>` · **Lean:** `<decl>`
**Cite:** @<citekey> — <page anchor>

- **Statement as used.** …
- **Primary — <the named theorem>.** …
```

A `[A]` node must also declare, in its status annotation, what the citation carries and what
it does not (`\textbf{Assignment.}`, fatal check 7). Widening this file widens the trust
base; it is a review decision, not a fix.

**Every anchor below was read out of a held scan** (librarian passes, 2026-08-07 and
2026-08-08), not quoted from memory. Where the verification changed what the entry says — Feller's
§XIII.1 splits four ways, Widder's attribution is not the one the draft's name suggests, Halgreen
has no numbered statements at all, Samko–Kilbas–Marichev turned out not to state the theorem the
draft cites it for — the entry records the discrepancy rather than papering over it.

**No exceptions: every entry is anchored on the source the draft names**, each read firsthand.
A15 was briefly the exception — @webster1997log resisted every automated route and the entry
stood on a corroborating monograph alone — until the author supplied the file on 2026-08-08. The
acquisition note in that entry is kept, because anyone re-verifying will hit the same wall.

**One entry supplies a citation the draft lacked**: A12. Mellin inversion is used three times in
§11 and was referenced nowhere; it is now Widder Theorem 9a, added to the draft at Definition
11.3 on 2026-08-08 together with the missing Lamperti, Krein and Thorin references. The draft's
own SSV and Samko–Kilbas–Marichev citations were checked and are correct as they stand.

**The `AXX` identifiers are opaque and stable** (policy revised 2026-08-09). They are assigned in
order of introduction, never reused, and **never renumbered** — including when a later entry
belongs, logically, beside an earlier one. Two reasons:

- They are *published names*. The manifest gives every node a `ledger` array and projects it to
  the hub, so renumbering silently changes what an existing hub note means, in a place no check
  can see. A stable identifier must not encode a fact that changes.
- The earlier rule — numbering in order of first use through the draft — required the ledger to
  be complete and correctly ordered before any proving began. That is only achievable from a
  finished dependency graph, and a draft is a proof sketch, not one. Formalisation routinely
  isolates an interface the draft had not, and under the old rule each such discovery forced a
  renumbering migration or an entry that lied about its position.

Order of first use is therefore a property of this index, not of the names:

| Serves | Entries |
|---|---|
| §2 — the Bernstein-function toolbox | A1–A6 |
| §8 — moments and the Bessel family | A7–A8 |
| §9 — memory kernels | A9–A10 |
| §10 — the scale Cauchy problem | A11 |
| §11 — the signaling form | A12 |
| §12 — locality | A13–A16 |
| §7 — the main theorem, **Lean route only** | A17 |

A17 is the first entry whose number sits outside that order, and it is exactly the case the
policy above was written for: it grounds no `[A]` node, because the blueprint's own proof of
`thm:main-characterization` does not use it — the Lean development reaches that theorem by a
different route.

Mnemonic identifiers would be better still, and `ledger_key` is per-article configurable, so this
repo could adopt them alone. It does not, because renaming sixteen published identifiers is the
very breakage the first bullet forbids; the case belongs in `article-kit` as guidance for
articles that have not yet pinned a ledger.

---

## A1 — Bernstein–Widder: completely monotone ⟺ the Laplace transform of a measure
**Blueprint:** `prop:bernstein-toolbox` (part 1) · **Lean:** *(not stated yet)*
**Cite:** @feller2009introduction — Vol. 2, §XIII.4, Theorem 1 and Theorem 1a, pp. 439–440

- **Statement as used.** Draft Proposition 2.3(1): `f` is the Laplace transform of a
  *probability* measure on `[0,∞)` iff `f` is completely monotone with `f(0+) = 1`. The
  blueprint node also carries the **general measure** form — `f` is CM iff
  `f(λ) = ∫ e^{−λx} F(dx)` for a not-necessarily-finite measure `F` — because §9 needs it
  (Lemma 9.4 inverts a Bernstein function to a locally finite potential kernel, which is not a
  probability measure).
- **Primary — Bernstein's theorem.** ✅ **[Feller] Vol. 2, §XIII.4 "Completely Monotone
  Functions", Theorem 1, p. 439**, with **Theorem 1a immediately below it on the same page**
  giving the measure-valued form; the proof runs onto p. 440. Verified against the held scan
  2026-08-07; the item is the **2nd edition (1971)** — the revision preface is dated January
  1970 — despite the citekey year and the filename's "1968". Chapter XIII begins p. 429.
- **Corroboration.** @schilling2012bernstein — **Theorem 1.4, p. 3** (2nd ed.), which states
  the same equivalence with **uniqueness** of the representing measure, and whose converse
  clause is phrased for any `μ` with finite transform on `(0,∞)` — i.e. it is already the
  locally-finite version. Cite this one where uniqueness is what is being used.
- **Agreement with the sibling.** `scale-space-foundations` pins its A5 at "§XIII.4, Theorem 1,
  pp. 439–440". **Confirmed correct**, same pages, same edition. The two ledgers agree.
- **Confidence.** ✅ well grounded — two independent primaries, both held as searchable scans,
  both page-verified.

## A2 — A Bernstein function is exactly one whose exponential is completely monotone
**Blueprint:** `prop:bernstein-toolbox` (part 2) · **Lean:** *(not stated yet)*
**Cite:** @schilling2012bernstein — Theorem 3.7, p. 27 (2nd ed.)

- **Statement as used.** Draft Proposition 2.3(2): `g ∈ BF` iff `e^{−τg}` is completely
  monotone for every `τ > 0`. This is what turns an exponent into a kernel: the whole
  construction of the kernel measures from `F` in Theorem 7.3(⇐) runs through it.
- **Primary — SSV Theorem 3.7.** ✅ **p. 27**, three equivalences: (i) `f ∈ BF`; (ii) `g ∘ f ∈ CM`
  for every `g ∈ CM`; (iii) **`e^{−uf} ∈ CM` for every `u > 0`**. Clause (iii) is the one used.
  Clause (ii) is used separately in §9 (Lemma 9.4, `CM ∘ BF` composition). Verified 2026-08-07.
- **Confidence.** ✅ well grounded.

## A3 — The Lévy–Khintchine representation of a Bernstein function, with a unique triple
**Blueprint:** `prop:bernstein-toolbox` (part 3) · **Lean:** *(not stated yet)*
**Cite:** @schilling2012bernstein — Theorem 3.2, pp. 21–22 (2nd ed.)

- **Statement as used.** Draft Proposition 2.3(3): every `g ∈ BF` is nonnegative,
  nondecreasing and concave, and has the representation
  `g(s) = a + b s + ∫ (1 − e^{−st}) ν(dt)` with `a, b ≥ 0` and `∫ (1 ∧ t) ν(dt) < ∞`,
  the triple `(a, b, ν)` being **unique**, and `g(0+) = a`.
- **Primary — SSV Theorem 3.2.** ✅ statement on **p. 21**, running to p. 22. Gives the
  representation and the uniqueness of `(a, b, μ)`. Verified 2026-08-07.
- **The cited theorem is an *iff*, and carries more than this entry uses** (recorded 2026-08-09).
  Its printed statement is *"A function `f : (0,∞) → ℝ` is a Bernstein function if, and only if,
  it admits the representation …"*, ending *"the triplet `(a, b, μ)` determines `f` uniquely and
  vice versa"*; the proof's converse paragraph (p. 22) closes with *"Therefore, `f` is a
  Bernstein function"*. The **statement as used** above is worded one-directionally because
  that is the direction draft Proposition 2.3(3) asserts. The converse leg — a triple with
  `∫ (1 ∧ t) ν(dt) < ∞` yields a Bernstein function — therefore needs **no new trust**: it is
  already inside this anchor, and [A17](#a17--existence-every-drift-plus-lévy-measure-pair-is-the-laplace-exponent-of-a-subordinator)
  relies on it rather than citing a second source for it.
- **Why uniqueness is load-bearing.** Lemma 7.1's equivalence (2) ⟺ (3) identifies the Lévy
  density of `B(s) = sF'(s)` with `k`; without uniqueness of the triple the identification is
  not available and the self-decomposability characterization does not close.
- **It is also the bridge between the project's two vocabularies** (recorded 2026-08-10). The
  paper argues in `BF₀`, defined by derivative signs; the Lean development argues in `LE`, the
  representation, and never defines complete monotonicity at all
  (`blueprint/DESIGN-formalization-strategy.md`). This part is what says the two classes are the
  same, and `def:levy-exponent` is the node that names the second one. Every Lean tag in
  chapters 5–7 crosses this edge exactly once, in a *statement* rather than inside a proof —
  which is the whole reason the `LE` readings of `thm:increments-bernstein` and
  `prop:canonical-gauge` are written out alongside the `BF₀` ones.
- **Confidence.** ✅ well grounded.

## A4 — Bernstein functions form a convex cone closed under pointwise limits and mixtures
**Blueprint:** `prop:bernstein-toolbox` (part 4) · **Lean:** *(not stated yet)*
**Cite:** @schilling2012bernstein — Corollary 3.8, pp. 28–29 (2nd ed.); closure under pointwise limits is part (ii), p. 28

- **Statement as used.** Draft Proposition 2.3(4): `BF` is a convex cone; if `g_n ∈ BF` and
  `g_n(s) → g(s) < ∞` pointwise on `(0,∞)` then `g ∈ BF`; consequently `BF` is closed under
  mixtures `s ↦ ∫ g_u(s) m(du)` whenever the integral is finite.
- **Primary — SSV Corollary 3.8.** ✅ **pp. 28–29**, with the **pointwise-limit clause as part
  (ii) on p. 28**. Parts (i) (convex cone), (iii) (composition) and (iv) (`f(λ)/λ ∈ CM`) sit on
  the same page. Verified 2026-08-07.
- **Why it is the workhorse.** This is the single external fact the article's key technical
  step rests on: Theorem 5.2 exhibits `g_{x,y}` as a **finite pointwise limit** of the
  elementary Bernstein functions `∫(1 − e^{−st}) Π_n(dt)` and concludes membership from
  closure alone. The null-array argument that produces the limit is ours and is `[T]`.
- **Confidence.** ✅ well grounded.

## A5 — Continuity theorem for Laplace transforms on the half-line
**Blueprint:** `prop:laplace-continuity` · **Lean:** `Hemigroup.tendsto_integral_of_tendsto_laplace` — a **theorem**, not an axiom; see below
**Cite:** @feller2009introduction — Vol. 2, §XIII.1, Theorem 2, p. 431 (probability distributions); Theorem 2a, p. 433 (arbitrary measures)

- **Statement as used.** Weak convergence of measures on `[0,∞)` is equivalent to pointwise
  convergence of their Laplace transforms. Used twice: in Theorem 7.3(⇐) to verify axiom (A7)
  from continuity of `F`, and in §9 to pass between the transform and measure forms of the
  scale evolution.
- **Primary — Feller's continuity theorem.** ✅ **Theorem 2, p. 431** for probability
  distributions: `F_n → F` iff `φ_n(λ) → φ(λ)`. ✅ **Theorem 2a, p. 433**, the *extended*
  continuity theorem, for arbitrary measures. Verified 2026-08-07.
- **⚠️ The blueprint statement is the probability case only (2026-08-16).** `prop:laplace-continuity`
  no longer states the arbitrary-measures clause. Theorem 2a is genuinely different in kind from
  Theorem 2, not just wider in scope: for infinite measures Feller proves convergence in *Feller's
  sense* (vaguely, or on bounded intervals), not weak convergence, so "the same equivalence …
  weakly" was imprecise, and no proof in this article spends the general-measure form — every use
  (`prop:laplace-continuity-causal`, `thm:main-characterization`) is the probability case. Theorem
  2a is kept above as the source of the "boundedness of `ω_n(a)`" hypothesis discussed below, which
  remains relevant context, not because the node's statement uses it.
- **The hypothesis that is easy to lose.** Theorem 2a's converse direction requires the
  sequence `{ω_n(a)}` to be **bounded**, and Feller gives the counterexample on the same page
  showing the hypothesis cannot be dropped. Any blueprint proof invoking the measure form must
  discharge boundedness explicitly; the probability form (Theorem 2) carries it for free, which
  is why Theorem 7.3(⇐) uses that one.
- **⚠️ Not in the Lean trust base — resolved 2026-08-09.** The development *proves* the form it
  needs instead of citing it: `Hemigroup.tendsto_integral_of_tendsto_laplace`, whose
  `#print axioms` reduces to Lean core alone. So A5 is **not** in `trust-boundary.txt`, and the
  boundary stays at one entry.
- **What is proved, exactly.** For **causal probability** measures on `ℝ`: convergence of the
  Laplace transforms together with tightness gives convergence of `∫ f dμₙ` for every bounded
  continuous `f` — i.e. weak convergence, in the transforms-to-measures direction. That is what
  `thm:main-characterization` (⇐) uses. The general **measure** form of Theorem 2a, with the
  boundedness hypothesis flagged above, is *not* formalised and would not be safe to assume from
  memory; the probability form carries that hypothesis for free, which is exactly why the Lean
  statement is restricted to it. Since 2026-08-10 that restricted form is a blueprint node of its
  own, `prop:laplace-continuity-causal`, `[T]` and Lean-tagged, sitting beneath this `[A]` one;
  the tightness half is `lem:transform-tightness`. The `[A]` node keeps the paper's statement.
- **Supporting pieces, all Lean core.** Tightness is ours as the **Assignment** clause always
  claimed, and now checked: `measureReal_Ioi_mul_le` (the Markov bound
  `μ(t>T)(1 - e^{-sT}) ≤ 1 - μ̂(s)`), `kernel_tail_le` (uniform over the family), and
  `exists_exponent_lt` (`F(0+) = 0`, which is what lets `s` be chosen small).
  `isTightMeasureSet_kernel` states the same thing in Mathlib's own vocabulary. Transform
  convergence is `tendsto_exponent` → `tendsto_increment_toReal` → `tendsto_laplace_kernel`.
- **Prokhorov was not needed.** The expected route — tight set, convergent subsequence,
  portmanteau, unique cluster point — is not the one taken. Pushing forward along `x = e^{-t}`
  lands the measures on the compact `[0,1]`, where Weierstrass does the work compactness would
  have done; the only price is a clamping estimate on the way back, paid by tightness. Mathlib's
  Prokhorov is never invoked.
- **Confidence.** ✅ well grounded, with the boundedness caveat recorded above.

## A6 — Uniqueness: a measure on the half-line is determined by its Laplace transform
**Blueprint:** `prop:laplace-uniqueness` · **Lean:** `Hemigroup.laplace_injective` — a **theorem**, not an axiom; see below
**Cite:** @feller2009introduction — Vol. 2, §XIII.1, Theorem 1, p. 430 (probability distributions); Theorem 1a, p. 432 (arbitrary measures)

- **Statement as used.** Distinct measures on `[0,∞)` have distinct Laplace transforms. This
  is what licenses every "and therefore the measures agree" step in the article — Lemma 4.1's
  uniqueness clause, Lemma 6.1, Proposition 9.2, Theorem 9.5, Lemma 10.3(5).
- **Primary — Feller's uniqueness theorem.** ✅ **Theorem 1, p. 430**: distinct probability
  distributions have distinct transforms. ✅ **Theorem 1a, p. 432**: a **measure** `U` is
  uniquely determined by its transform on an interval `a < λ < ∞`. Verified 2026-08-07.
  A corollary on p. 433 adds that a *continuous* function is determined by its ordinary
  transform.
- **Note on §XIII.1's structure.** The section carries four separate statements and the
  probability/measure pairs do **not** sit on adjacent pages: uniqueness is Theorem 1 (p. 430)
  and Theorem 1a (p. 432), continuity is Theorem 2 (p. 431) and Theorem 2a (p. 433). Citing
  "§XIII.1" alone is not an anchor; use the theorem numbers.
- **⚠️ Not in the Lean trust base** (2026-08-09). The development *proves* this instead of
  citing it: `Hemigroup.laplace_injective`, whose `#print axioms` reduces to Lean core alone. So
  A6 is **not** in `trust-boundary.txt` and nothing proved in Lean rests on it. The `**Lean:**`
  field above names a theorem, not an `axiom` — the cross-check in `linkage/trust.py` reads
  these segments only to confirm that a *declared* axiom was reviewed, never to authorise one,
  so naming a proved declaration here is safe and is the documented use.
- **⚠️ What Lean proves is weaker than what is stated.** `laplace_injective` assumes the
  transforms agree on all of `[0,∞)`; Feller's Theorem 1a gives the conclusion from agreement on
  a tail `(a,∞)`. The blueprint node states the tail form and therefore carries no Lean tag.
  The gap is genuine: the Lean proof substitutes `x = e^{-t}` and reads `μ̂(n)` as the `n`th moment
  of the transported measure, and moments from some `n_0` onwards do not pin down an atom at the
  origin — our measures have none, being carried by `(0,1]`, but that step is only available
  once `n = 0` is in hand. Anyone needing the tail form in Lean must supply it. Since 2026-08-10
  the full-half-line form is a blueprint node of its own, `prop:laplace-uniqueness-causal`, `[T]`
  and Lean-tagged, sitting beneath this `[A]` one; it is what the formalised arguments cite.
- **Confidence.** ✅ well grounded as a citation, and superseded in Lean for the case the
  development uses.

## A7 — Moment criterion for self-decomposable laws
**Blueprint:** `prop:moments` · **Lean:** *(not stated yet)*
**Cite:** @sato1999levy — Theorem 25.3, p. 159

- **Statement as used.** Draft Proposition 8.4: a submultiplicative `g`-moment of an infinitely
  divisible law is finite iff the corresponding integral against the Lévy measure over
  `{|t| > 1}` is finite. Specialized here to `g(t) = t^n`, giving
  `E T_x^n < ∞ ⟺ ∫_1^∞ t^{n−1} k(t) dt < ∞`.
- **Primary — Sato Theorem 25.3.** ✅ statement complete on **p. 159**; proof runs pp. 160–162.
  Verified 2026-08-07.
- **What this entry does not carry.** The first-moment identity `E T_x = x F'(0+) = x(b_0 + ∫k)`
  and the exact linearity of the influence curve are elementary consequences of the
  representation (7.1) and are held `[T]`, not on Sato.
- **Confidence.** ✅ well grounded. ⚠️ The held scan's OCR text layer is imperfect (e.g. "Lévy"
  renders as "Lary" in places); page numbers are reliable, but quote verbatim only from the
  image via `library page sato1999levy --printed N --format image`.

## A8 — The generalized inverse Gaussian laws are generalized Γ-convolutions, hence self-decomposable
**Blueprint:** `prop:bessel-family` · **Lean:** *(not stated yet)*
**Cite:** @halgreen1979self — §2 "The GIGDs are Generalized Γ-Convolutions", pp. 14–15; the generalized hyperbolic case is §3, pp. 15–17

- **Statement as used.** Draft Example 8.3: the scaled inverse-gamma law `T_1 =_d 1/(2γ_a)` is
  self-decomposable, hence the Bessel-K family is an admissible member of the class Theorem 7.3
  characterizes. This is not decoration — Theorem 5′ classifies that family as *the* order-2
  local case, so if it were not admissible the headline theorem would classify an empty set.
- **⚠️ The paper carries no numbered statements at all.** Verified: five pages of continuous
  prose, zero theorems, propositions or lemmas. The anchor is therefore **by section and page**,
  which is the honest form here and not a weakening. Announced on p. 13 (§1): *"it will,
  firstly, be shown that a GIGD is self-decomposable, or belongs to class L (Feller, 1971). In
  fact, any GIGD is a generalized Γ-convolution."* Proof in §2, concluding on **p. 15**:
  *"Comparing (5) and (2) we see, that the GIGDs with λ ≤ 0 are generalized Γ-convolutions"*,
  extended to all λ by the convolution identity on the same page. Verified 2026-08-08.
- **What is proved is stronger than what is used.** Halgreen proves **GIG ∈ GGC**; self-
  decomposability follows through `GGC ⊂ SD`, which is A16's second clause. A8 and A16 therefore
  rest on the same tower, and a reader checking one should check the other.
- **Confidence.** ✅ well grounded. ⚠️ The scan's OCR mangles Greek and formulae (λ, χ, ψ are
  unreliable in the text layer); page numbers and prose are sound, but quote from the image.

## A9 — Special Bernstein functions, the Stieltjes class, and complete Bernstein functions
**Blueprint:** `prop:pair-regularity` · **Lean:** *(not stated yet)*
**Cite:** @schilling2012bernstein — Theorem 11.3, pp. 160–161; Theorem 7.3, p. 93; Theorem 6.2, pp. 69–75; the Stieltjes class **S** is defined Ch. 2, p. 16 (all 2nd ed.)

- **Statement as used.** Draft Proposition 9.7(2),(3): the potential kernel `ℓ^{(x)}` is
  `cδ_0` plus a nonincreasing density iff `φ_x` is a *special* Bernstein function; and the
  memory kernel `κ^{(x)}` has a completely monotone density iff `k` is CM iff `F'` lies in the
  Stieltjes class, in which case `F ∈ CBF`.
- **Primary — SSV Theorem 11.3.** ✅ statement **p. 160**, proof from p. 161: `S` is a special
  subordinator iff its potential measure is `U(dt) = cδ_0(dt) + u(t)dt` with `u` nonincreasing.
  Ch. 11 (*Special Bernstein functions and potentials*) runs pp. 159–178. Verified 2026-08-07.
- **Primary — SSV Theorem 7.3.** ✅ **p. 93**: `f ∈ CBF ⟺ 1/f ∈ S`. This is the CBF/Stieltjes
  duality the draft's part (3) uses.
- **Supporting — SSV Theorem 6.2.** ✅ the characterization of CBF, statement opening **p. 69**,
  proof ending p. 75, with Corollary 6.3 following.
- **The draft's own citations here are correct**, and were checked: it cites `[SSV, Thm. 11.3]`
  for the special-subordinator theorem and `[SSV, Ch. 2]` for the Stieltjes class, which is
  where `S` is defined (p. 16). The two must not be merged into a single "Ch. 11" citation —
  an earlier draft of this entry did merge them, wrongly.
- **⚠️ Theorem 11.3 is 2nd-edition numbering and does not survive to the 1st.** The 2nd edition's
  preface (p. v) records that a new Chapter 10 (*transformations of Bernstein functions*) was
  **inserted**, so chapters 1–9 keep their numbers across editions but everything from 10 on
  shifts: this result is **Theorem 10.3 in the 1st edition**. Every SSV anchor in this ledger
  therefore says "2nd ed." — for A1–A4 (chapters 1 and 3) it is belt and braces, for A9 it is
  load-bearing. Inferred from the 2nd-edition preface; we hold no 1st edition to check against.
- **Confidence.** ✅ well grounded, with the edition caveat above.

## A10 — Nondegenerate self-decomposable laws are absolutely continuous
**Blueprint:** `prop:volterra` · **Lean:** *(not stated yet)*
**Cite:** @sato1999levy — Theorem 27.13, p. 181

- **Statement as used.** Draft Proposition 9.8: when `k ≢ 0` the kernel `μ_x` is absolutely
  continuous, so the measure-level Volterra identity (9.1) descends to the density equation
  (9.2) — which is what makes the equation usable as a forward numerical scheme.
- **Primary — Sato Theorem 27.13.** ✅ **p. 181**: "Any nondegenerate selfdecomposable
  distribution on `ℝ^d` is absolutely continuous." Statement and its short proof both on that
  page. Verified 2026-08-07.
- **Where nondegeneracy comes from.** `k ≢ 0` is exactly nondegeneracy here; the degenerate
  case `k ≡ 0` is the pure drift `F(s) = b_0 s`, whose kernel is the atom `δ_{b_0 x}` and is
  excluded by hypothesis, not by the citation. That exclusion is ours and is `[T]`.
- **Confidence.** ✅ well grounded.

## A11 — Subordination: the generator of the subordinate semigroup, and the core criterion
**Blueprint:** `prop:fixed-scale-semigroup` · **Lean:** *(not stated yet)*
**Cite:** @phillips1952generation — Theorem 4.3, pp. 362–363, whose hypotheses are equation (40), p. 362; and @engel2000one — Definition II.1.6 / Proposition II.1.7, pp. 52–53

- **Statement as used.** Draft Proposition 10.5: `−φ_x(∂_t)` on the core `D` is closable, its
  closure generates the `C_0` contraction semigroup subordinate to the delay semigroup via
  `φ_x`, and `D` is a core for that generator.
- **Primary — Phillips' subordination theorem.** ✅ **Theorem 4.3**, statement opening at the
  foot of **p. 362** and completing at the top of **p. 363**, giving the subordinate generator
  as `Bx = mAx + ∫_0^∞ [exp(−ω_0 ξ)T(ξ)x − x] dψ + ax` for `x ∈ D(A)`; proof runs to p. 364.
  The Lévy–Khintchine hypotheses on the subordinator live in **equation (40), p. 362**, and must
  be cited with the theorem — they are not restated in it. **Theorem 4.1, p. 361** supplies the
  prior half (the subordinate family is again a strongly continuous semigroup). Verified
  2026-08-08.
- **⚠️ Two things Phillips does not say.** First, he **never writes `−φ(−A)`**; that is modern
  notation, and his display becomes it only after setting `ω_0 = 0`, `a = 0`, `m = b`. The
  blueprint must state the correspondence rather than attribute the notation to him. Second, he
  asserts `D(B) ⊇ D(A)` — **not** that `D(A)` is a core for `B`. That gap is exactly why the
  second citation is here, and the two halves are genuinely complementary rather than redundant.
- **Secondary — the core criterion.** ✅ @engel2000one **Proposition II.1.7, p. 53**: a subspace
  of `D(A)` that is dense in `X` and invariant under the semigroup is always a core. The
  definition of *core* is Definition II.1.6 on the facing p. 52. Verified 2026-08-07.
- **What neither carries.** That `D` as defined in draft Lemma 10.1 is dense and semigroup-
  invariant is ours, proved there, and held **[T]**; the citation supplies only the implication
  from those properties to coreness.
- **Confidence.** ✅ well grounded, with the notation caveat recorded above.

## A12 — Mellin inversion on a vertical line of absolute convergence
**Blueprint:** `def:inversion-operator` · **Lean:** `Hemigroup.SelfDecomposableExponent.inversionOperator` (the operator; the one step the entry still carries is never invoked — see the sixth reading)
**Cite:** @widder1941laplace — Ch. VI, §9 "The Mellin Transform", Theorem 9a, pp. 246–247

- **Statement as used.** Draft Lemma 11.2 and Definition 11.3: if the Mellin transform
  converges absolutely on the line `Re z = c`, the inversion integral
  `(2πi)^{-1} ∫_{(c)} x^{−z} \tilde g(z) dz` recovers the function. Everything §11 builds — the
  inversion operator `A`, its symbol `B`, the eigenfunction relation of Theorem 4′ — rests on it.
- **Primary — Widder Theorem 9a.** ✅ statement opening at the foot of **p. 246** and completing
  on **p. 247**: *"If the integral (4) ∫_0^∞ u^{s−1}ψ(u)du converges **absolutely on the line
  σ = c**, and if ψ(t) is of bounded variation in a neighborhood of t = x (x > 0), then
  lim_{T→∞} (1/2πi)∫_{c−iT}^{c+iT} f(s)x^{−s}ds = [ψ(x+) + ψ(x−)]/2."* Widder derives it from
  Theorem 5a, p. 241, the bilateral-Laplace parent. Verified 2026-08-08.
- **Neighbouring statements, if §11 needs them.** Theorem 9b, p. 247 (Mellin–Stieltjes);
  Theorems 9c and 9d, p. 247 (the `L²` / Mellin–Plancherel version on a strip, should the
  inversion operator be wanted in the `L²` setting rather than pointwise); Theorem 6a, p. 243
  (uniqueness in a strip).
- **⚠️ What the gap actually was.** The draft cited nothing at all for Mellin inversion — it
  invokes the inversion integral in Definition 11.3 and again in the proofs of Lemma 11.4 and
  Theorem 11.6 without a reference. (Its one `[Samko–Kilbas–Marichev]` citation in §11 is for
  the Riemann–Liouville integral of complex order, which is correct and stays: SKM is strong
  there.) Samko–Kilbas–Marichev would *not* have served for the inversion theorem in any case —
  it gives it **only as a bare display, equation (1.113) on p. 25**, introduced with "and its
  inverse is given by the formula": no theorem number, no hypotheses, no convergence conditions.
  Widder was added to the draft at Definition 11.3 on 2026-08-08.
- **Confidence.** ✅ well grounded, and better grounded than the draft's own citation. Widder is
  already held and already this ledger's source for A13, so no new trust is introduced.
- **Mathlib check, 2026-08-11 — A12 is _not_ retired, and the reason is precise.** Mathlib has
  `Mathlib/Analysis/MellinInversion.lean`, whose `mellinInv_mellin_eq` reads

  ```
  (σ : ℝ) (f : ℝ → E) (hx : 0 < x)
  (hf  : MellinConvergent f σ)              -- forward transform absolutely convergent on Re z = σ
  (hFf : VerticalIntegrable (mellin f) σ)   -- the INVERSION integral absolutely convergent
  (hfx : ContinuousAt f x)
  → mellinInv σ (mellin f) x = f x
  ```

  This is **not** Widder Theorem 9a. Two differences, and the first is the one that matters:

  1. **Mathlib requires the inversion integral to converge absolutely**; Widder does not. Widder
     takes the symmetric limit `lim_{T→∞} ∫_{c−iT}^{c+iT}`, which is exactly the device that
     covers conditionally convergent inversion integrals. Mathlib's `mellinInv` is an ordinary
     integral over the line, not a principal value.
  2. Mathlib assumes `ContinuousAt f x` where Widder assumes bounded variation near `x` and
     concludes the midpoint `[ψ(x+) + ψ(x−)]/2`. For continuous `ψ` these agree, so this
     difference is harmless here.

  **Correction, same day, on the decisive point.** The paragraph first written here said (H)
  cannot supply vertical integrability and that retiring A12 would therefore cost a new
  hypothesis. The first half is true and irrelevant; the second half is wrong. **The article does
  not need (H) to supply it, because `def:inversion-operator` already assumes it**: the operator
  is defined "for `g` such that `g̃` is defined on the line `Re z = c` **and `B(−z) g̃(z)` is
  absolutely integrable there**". That is exactly `VerticalIntegrable`. The article never relies
  on Widder's conditional-convergence generality — it imposes the stronger hypothesis in the
  definition, and A12's Assignment clause says so in as many words: the entry carries "that
  absolute integrability on the line `Re z = c` is sufficient for the contour integral to recover
  `B(θ)g`".

  Two supporting facts, both already in `lem:mellin-data`: `H̃(z) = Γ(z) E[T_1^{−z}]` is
  absolutely integrable on every vertical line of the strip, because `|Γ(c+iτ)|` decays
  super-polynomially — so the *profile's* transform needs no extra assumption. The *symbol* `B`
  alone is not vertically integrable (`B(−z)` grows at least like `|z|`, being a ratio in which
  the Γ factors cancel), but `B` is never inverted alone: it always multiplies a transform that
  carries the Γ decay, and the product is `H̃(z+1)`, which decays again.

  **So A12 is retirable, at a formalisation cost rather than a mathematical one.** What remains
  between `mellinInv_mellin_eq` and this node: (i) matching the *operator* formulation — Mathlib
  states `mellinInv σ (mellin f) x = f x`, recovery of a function from its own transform, whereas
  the node needs the integral against `B(−z) g̃(z)` to agree with the functional-calculus reading,
  so one must exhibit the `h` whose Mellin transform is that product; and (ii) `ContinuousAt`,
  which Mathlib requires and Widder replaces with bounded variation. Neither is a change to the
  article's hypotheses. **This should be attempted before A12 is treated as permanent.**

  **Separately, `lem:symbol-uniqueness` may want Mellin _uniqueness_** (Widder Thm 6a, p. 243 —
  already listed above as a neighbouring statement). Mathlib gives injectivity only as a
  corollary of `mellinInv_mellin_eq`, i.e. under the same absolute-convergence hypotheses, so
  that node inherits the same question. *(Resolved 2026-08-12: it does not want it. Two operators
  agreeing on `H(s·)` share a realising function there, so their transforms agree at every point
  and the symbols come off by cancellation — no injectivity, and no second citation. See the
  seventh reading.)*

- **Third reading, 2026-08-11, from the Lean rather than from the library index — the obstacle is
  upstream.** `lem:mellin-data` is now proved
  (`Hemigroup.SelfDecomposableExponent.mellin_profile` and `norm_mellin_profile_le`), and proving
  it is what located the difficulty precisely. The correction above says the vertical
  integrability `mellinInv_mellin_eq` needs is *already supplied* by `lem:mellin-data`, because
  `H̃(z) = Γ(z)E[T₁^{−z}]` and `|Γ(c+iτ)|` decays super-polynomially. That is true of the
  mathematics and false of Mathlib: **there is no bound on `‖Complex.Gamma‖` along a vertical
  line anywhere in the library.** `Analysis/SpecialFunctions/Stirling.lean` is Stirling's formula
  for `n !` alone; the complex-plane asymptotic that gives `|Γ(c+iτ)| ∼ √(2π)|τ|^{c−1/2}
  e^{−π|τ|/2}` is absent, and so is any weaker decay estimate that would serve.

  So the vertical-integrability clause has been split out of `lem:mellin-data` as its own node,
  `lem:mellin-vertical` (11.13), which is where this entry's Blueprint line now points — that
  clause, and not the identity, is what A12's retirement turns on. It is stated in Lean as
  `Skeleton.verticalIntegrable_mellin_profile`, whose type is *verbatim*
  `Complex.VerticalIntegrable (mellin H) c`, the hypothesis `mellinInv_mellin_eq` asks for.
  Everything on this side of the Γ estimate is done.

  **What changes for the decision.** A12 is still retirable and is still not a question about the
  article's hypotheses — both earlier readings were wrong about *where* the cost sits, and this
  one moves it a third time. It is now a **queue item for Mathlib**, not a decision here: either
  the Γ decay arrives upstream, or it is proved in this repo as a piece of work in its own right
  (Stirling in the complex plane, or the reflection formula against `Gamma_mul_Gamma_one_sub`
  plus a bound on `|1/Γ|`, neither small). That is a different kind of obstacle from "a
  formalisation cost" and it should be recorded as such rather than left inside a correction that
  reads as though the remaining work were bookkeeping.

  **The general lesson, again and sharper.** The correction below already recorded that "does
  Mathlib retire this entry?" is not answered by comparing Mathlib to the *cited theorem*. It is
  not answered by comparing Mathlib to the article's *use* of it either — that gets the
  mathematical question right and can still miss a lemma the Lean proof needs and the paper takes
  for granted. The reliable move is to *write the statement in Lean and try*, which is what
  located the Γ gap here in an afternoon.

- **Fourth reading, 2026-08-11 — the estimate was not needed, and `lem:mellin-vertical` is
  proved.** The third reading said A12 was blocked upstream on the vertical decay of
  `|Γ(c+iτ)|`, which Mathlib does not carry. The first half of that is true; the second half was
  a claim about the classical *proof*, not about the *obligation*. The asymptotic
  `|Γ(c+iτ)| ∼ √(2π)|τ|^{c−1/2}e^{−π|τ|/2}` does need Stirling in the complex plane;
  **integrability needs only quadratic decay**, and that is the functional equation twice:

  - `|Γ(σ+iτ)| ≤ Γ(σ)` for `σ > 0`, since the imaginary part only rotates Euler's integrand;
  - `Γ(z+2) = (z+1)zΓ(z)` with `|z|, |z+1| ≥ |τ|`, both having imaginary part `τ`, so
    `|Γ(c+iτ)|τ² ≤ Γ(c+2)`.

  Adding them gives `|Γ(c+iτ)|(1+τ²) ≤ Γ(c) + Γ(c+2)`, and `(1+τ²)⁻¹` is integrable.
  `Hemigroup/MellinVertical.lean`; `lem:mellin-vertical` carries the tag and reduces to A17.

  **What remains of A12 is the operator formulation.** `mellinInv_mellin_eq` recovers a *function*
  from its own transform; `def:inversion-operator` needs the integral against `B(−z)g̃(z)` to agree
  with the functional-calculus reading, so one must exhibit the `h` whose Mellin transform is that
  product — plus `ContinuousAt`. Both are questions about this article, which is exactly where the
  correction of the same day said the cost would sit once the estimate was in hand.

- **Four assessments, and what each of the first three got wrong.** Worth keeping as a record of
  how a ledger entry should and should not be assessed.

  | | compared against | verdict | error |
  |---|---|---|---|
  | 1 | the **cited theorem** (Widder 9a) | not retirable; needs a new hypothesis | the article never uses Widder's generality |
  | 2 | the article's **use** of it | retirable at formalisation cost | right about the article, silent about Lean |
  | 3 | the **named lemma** the classical proof needs | blocked upstream on Γ decay | reasoned about the proof, not the obligation |
  | 4 | **the statement, by attempting it** | proved | — |
  | 5 | the **node**, by formalising it | narrowed to one step | (the narrowing *was* the finding) |
  | 6 | the article's **uses**, by proving them | the use is empty | — |
  | 7 | the **consumer** node, by proving it | it was outside the quantifier | read the hypothesis, not the proof |

  A survey answers "is this theory present?". Only attempting the proof answers "is this theorem
  reachable?", and here the two answers differed by two orders of magnitude of work.

- **Fifth reading, 2026-08-12 — the entry is narrowed, not retired, and now names one step.**
  `def:inversion-operator` is formalised: `Hemigroup.SelfDecomposableExponent.inversionOperator`
  with `inversionOperator_eq`, `mellin_inversionOperator` and `mellin_inversionOperator_eq`. The
  split those names record is the substance of this reading.

  The blueprint's definition sets `(Ag)(x)` to a contour integral and glosses it as
  `x^{-1}(B(θ)g)(x)`. Formalising it separates the two completely. **The operator needs no
  hypothesis at all** — `mellinInv` is an ordinary integral, so `A g` is total in `g`, and the
  parametrisation `z = c + iy` turns the blueprint's `dz/2πi` into Mathlib's `dy/2π` on the nose.
  **The gloss needs a referent.** `B(θ)g` is a functional calculus for an operator with poles, so
  the second display is not a rewriting of the first; it asserts that a certain function exists.
  That is the same gap the fourth reading saw from the Mathlib side — `mellinInv_mellin_eq`
  recovers a function from its *own* transform and says nothing about the integral of a product.

  So the Lean statement takes the referent as a hypothesis (`RealisesSymbolAction`: an `h` whose
  transform is `B(-z)g̃(z)` on the line, with the two convergence clauses) and proves everything
  downstream of it — `A g = x^{-1}h` at points of continuity, and `Ãg(z) = h̃(z-1)` at every `z`,
  with no strip condition, the weight `x^{-1}` being a Mellin shift. `#print axioms` on all four
  gives A17 and nothing else. That content is now the blueprint node `lem:inversion-operator-action`
  (11.16), `[T]` and `\leanok`; `def:inversion-operator` keeps its number and this entry.

  **What A12 is left carrying is one step: that absolute integrability of `B(-z)g̃(z)` on the line
  produces `h`.** Everything else that was ever assigned to it is proved.

  **And that is now a question about this article, not about the literature.** Every use of `A`
  applies it to a profile `H(s·)`, where `h(x) = s x H(sx)` is explicit and
  `h̃(z) = s^{-z}H̃(z+1)` is `lem:inversion-symbol`'s recursion with the denominator cleared. If
  each use supplies its own `h`, the entry retires with no citation spent. Checking that, node by
  node, is what `lem:symbol-uniqueness` and `thm:signaling-form` now consist of.

  **A finding that was not foreseen, and it is about the statement rather than the proof.** The
  realising identity can only be asked for *almost everywhere* on the line. `B` is a quotient with
  poles at the zeros of `H̃`; where `H̃` vanishes the product `B(-z)g̃(z)` vanishes with it — in
  Lean because `x/0 = 0`, in the prose because a meromorphic function has no value at a pole —
  while `h̃(z)` need not. A pointwise reading of the hypothesis would therefore be satisfied by no
  `g` at all. The zeros are isolated, so they meet the line in a null set and the inversion
  integral does not see them. This is the second time in chapter 11 that "equality on the strip"
  has had to say which equality it means; `lem:symbol-rigidity` was the first, and both times it
  was writing the statement, not reading it, that raised the question.

- **Sixth reading, 2026-08-12, same round — the article's use of A12 is empty.** The fifth reading
  ended by saying that whether A12 retires is now a question about this article: does every use of
  `A` exhibit its `h`? It does, and the check is machine-checked.

  `lem:profile-eigenfunction` (11.17), Lean
  `Hemigroup.SelfDecomposableExponent.inversionOperator_profile`: for the profile dilate
  `g = H(s·)` the realising function is `h(x) = s x H(sx)`, written down rather than inferred, and
  the instance `realisesSymbolAction_profile` is proved outright. `#print axioms` gives A17 and
  nothing else. The exhibition is free — `h̃(w) = s^{-w}H̃(w+1)` and `g̃(w) = s^{-w}H̃(w)` are one
  Mellin shift apart and their ratio is `B` by construction — and the conclusion `A g = x⁻¹h` reads
  `A[H(s·)](x) = s H(sx)`, which *is* `thm:signaling-form`(1). The instance and the eigenfunction
  relation are the same statement.

  That dilate is the only shape in which `A` is ever applied here: clause (2)'s Laplace form is
  clause (1) applied to `û(s,·) = f̂(s)H(s·)`. So the step A12 was left carrying is never invoked.

  **The entry stays.** Retiring it would be a claim about the *paper*, which cites Widder for the
  inversion integral and is entitled to. This is the A5/A6 situation of Chapter 2 exactly: the `[A]`
  tag records the paper's stance, and the `[T]` nodes underneath record what is machine-checked.
  What changes is that the record is now complete — nothing in the formal development reaches this
  citation, and `trust-boundary.txt` still holds two names.

  **One line of the draft's proof did not survive transcription.** It says of the product
  `B(-z)g̃(z)` that "no pole of `B` intervenes, the product containing no division". True of the
  *simplified* product `s^{-z}H̃(z+1)`; false of `B` read as a function, where the division is
  present and cancelling it needs `H̃(z) ≠ 0`. Hence the a.e. reading, and hence a small new lemma:
  the zeros of `H̃` on a vertical line are null, because isolated zeros form a discrete subset of
  the strip and `ℂ` is hereditarily Lindelöf, so the set is countable. The prose was doing algebra
  on symbols where the formalisation does it on functions, and that is where the gap between them
  sits.

- **Seventh reading, 2026-08-12 — `lem:symbol-uniqueness` was never waiting on this either.**
  Both halves of the node are now machine-checked
  (`sameSymbolAction_of_realisesAction`, `eventuallyEq_inversionSymbol_of_realisesAction`), and
  `#print axioms` gives A17 alone. The blueprint had recorded step 1 as carrying A12, on the
  reading that turning the operator relation into a transform relation requires
  `def:inversion-operator`'s identity and hence the *production* of `B(θ)g`.

  That was a misreading of the node's own hypothesis. It quantifies over operators "of the form
  `x⁻¹B(θ)`" — and an operator of that form is one whose `B(θ)g` is **given**. The class the
  statement ranges over is exactly the class in which the referent exists, so the step A12 carries
  is outside the quantifier, not inside it.

  Two further things fell out, both about what the proof does *not* need:

  - **No Mellin injectivity.** The bullet above anticipated wanting Widder Thm 6a here. It is not
    wanted: two operators that agree on `H(s·)` have the *same* realising function there, because
    `x⁻¹h₁ = x⁻¹h₂` on `(0,∞)` is `h₁ = h₂`; so their transforms agree at every point and the
    symbols are read off by cancelling `s^{-z}H̃(z)`. The realising function carries the
    information injectivity would have had to recover. One anticipated citation retired.
  - **One dilation suffices.** The blueprint quantifies the eigenfunction relation over all
    `s > 0`; the proof uses a single `s`, the dilate contributing only the nonvanishing factor
    `s^{-z}`.

  **And it corrected a design choice made one commit earlier.** `RealisesAction.mellin_eq` was
  first written as an `∀ᵐ` on the line — all `inversionOperator_eq` needs, since the zeros of `H̃`
  are null. That is too weak here: a uniqueness theorem must conclude an equality of symbols at
  *named* points, and an a.e. hypothesis concludes nothing at any of them. The right condition is
  the identity at every point of the line where `H̃` does not vanish — which is what the profile
  instance actually proves, and which makes `SameSymbolAction` hold on the whole strip (at a zero
  both sides vanish). Weakest hypothesis the consumer can use, strongest the producer can supply;
  they meet exactly, and it took writing the consumer to see it.

- **Eighth reading, 2026-08-29 — a second, cheaper use, in `cor:signaling-wellposed` (11.26).**
  Theorem 4′ was given a solution-uniqueness ending (`def:mellin-solution`, `lem:mode-rigidity`,
  `cor:signaling-wellposed`, `cor:signaling-classical`; blueprint `blueprint/src/parts/11-signaling.tex`,
  end of chapter 11): clause (3) of the theorem proves uniqueness of the *operator*, and the new
  corollary proves uniqueness of the *solution*, under a normalisation the field satisfies for
  free. Its proof identifies two continuous functions of `x` — a candidate solution's Laplace
  profile `x ↦ û(s,x)` and the field's own `x ↦ κ_s H(sx)` — from the fact that they share a Mellin
  transform, `κ_s` a constant determined by `lem:mode-rigidity`. That step is Widder Theorem 9a,
  applied **directly to two functions with a common transform**, not through the operator's
  functional-calculus reading (no symbol `B`, no realising function `h`): a second, and cheaper,
  use of the same citation. Were it formalised, it would go through Mathlib's
  `mellinInv_mellin_eq` applied to each function separately rather than through
  `RealisesAction` — the same pattern the sixth reading found for `lem:profile-eigenfunction`,
  where the article's use of `A`'s remaining step turned out to be empty because the referent is
  always exhibited. Not formalised here (`cor:signaling-wellposed` carries no `\lean` tag, on the
  pattern `def:covariant-mellin-class` set), so nothing about this reading is machine-checked yet
  — but the reuse is recorded because the assignment clause's accounting of what the entry
  carries should list every place the paper spends it, not only the first. **No new ledger name
  was created**; A12's `**Blueprint:**` header line stays `def:inversion-operator`, the ledger's
  format allowing one anchor label per entry, with this second use recorded here in prose instead.

## A13 — A Laplace transform with nonnegative integrand is singular at its abscissa of convergence
**Blueprint:** `lem:moment-recursion` · **Lean:** *(not stated yet)*
**Cite:** @widder1941laplace — Ch. II, §5, Theorem 5b, pp. 58–59

- **Statement as used.** Draft Lemma 12.3(2): if the inversion symbol `B` is a polynomial then
  `z_* = ∞`. The argument continues `m(z) = E[T_1^{−z}]` analytically through the real endpoint
  of its strip of convergence, which the cited theorem forbids unless the endpoint is at
  infinity.
- **Primary — Widder Theorem 5b.** ✅ **p. 58**, running head "[Ch. II": *"If `α(t)` is
  monotonic, then the real point of the axis of convergence of `f(s) = ∫_0^∞ e^{−st} dα(t)` is
  a singularity of `f(s)`."* Proof concludes p. 59. Widder motivates it on p. 58 with the
  counterexample showing a *general* Laplace integral need have no singularity on its axis of
  convergence — the monotonicity hypothesis is essential and is satisfied here because `T_1` is
  a positive random variable. Verified 2026-08-07.
- **⚠️ Attribution discrepancy, recorded not resolved.** The draft calls this the
  **Pringsheim–Landau** theorem. Widder's own footnote to Theorem 5b credits **H. Hamburger
  (1921), p. 306**. "Pringsheim–Landau" is the standard name for the Dirichlet-series and
  power-series forms of the same principle, so the draft's usage is the received one and not
  wrong — but the anchor is to **"Theorem 5b"**, and blueprint prose should say so rather than
  rely on the popular name matching the page.
- **Provenance of the copy.** Widder was **not** previously held. Acquired 2026-08-07 from
  archive.org item `dli.ernet.206074`, the **1946 Princeton reprint of the 1941 first edition**
  (Princeton Mathematical Series 6); x+406 printed pages match the 1941 collation exactly, so
  1941 page citations are valid against it.
- **Confidence.** ✅ well grounded, with the attribution note above.

---

## A14 — The positive maximum principle forces the integro-differential form; its local version forces order two
**Blueprint:** `thm:locality` · **Lean:** *(not stated yet)*
**Cite:** @courrege1966sur — Corollaire 2, p. 2-10 (the locality clause); Théorème 1.5, p. 2-09 and Corollaire 3, p. 2-10 (the general integro-differential form)

- **Statement as used.** Draft Definition 12.1 and Theorem 12.5: an operator satisfying the
  positive maximum principle has the Lévy–Khintchine-type integro-differential form, and one
  satisfying the *local* principle has no jump part — which is what caps the local class at
  order two and kills `n ≥ 3` in Remark 12.7.
- **Primary — the locality clause, and it is the load-bearing one.** ✅ **Corollaire 2,
  p. 2-10**: *"Toute application linéaire de `C_c^∞(Ω)` dans `B(Ω)` satisfaisant au principe du
  maximum positif **local** est un opérateur différentiel de diffusion."* Local PMP implies a
  pure second-order diffusion operator, no jump part. **Anchor Theorem 5′'s locality branch on
  Corollaire 2 specifically**, not on the structure theorem — it states exactly the needed
  implication and nothing more. Verified 2026-08-08.
- **Primary — the general form.** ✅ **Théorème 1.5, p. 2-09**: `A` is almost positive iff
  `A = P + S` with `P` a second-order diffusion operator with `P1 = 0` and `S` an almost-positive
  Lévy operator, the principal part of `P` and the singular kernel of `S` being **uniquely
  determined**; the final clause reads that `A` satisfies the PMP iff `S` does. ✅ **Corollaire 3,
  p. 2-10** gives the explicit form, formula (1.8), with condition **(1.13)** necessary and
  sufficient for the PMP. Definitions of (P), (PM), (PML) are on p. 2-04.
- **Pagination.** The NUMDAM scan paginates **by exposé**, not continuously: printed labels run
  `2-01`…`2-38`, and the cover sheet is pdf 1, so **printed 2-NN = pdf page NN+1**. A citation
  of the form "p. 10" is ambiguous here and must be written `p. 2-10`.
- **Confidence.** ✅ well grounded.

## A15 — Krull–Webster: a log-convex solution of `f(x+1) = g(x) f(x)` is unique up to normalization
**Blueprint:** `prop:local-ladder` · **Lean:** *(not stated yet)*
**Cite:** @webster1997log — §3 "Uniqueness Results", Theorem 3.1, p. 609; corroborated by @marichal2022generalization — Theorem 1.5, p. 3, at `p = 1`

- **Statement as used.** The moment recursion `m(z+1) = Q(z) m(z)` together with log-convexity of
  `m` (Lemma 12.4) determines `m` uniquely given its normalization. Proposition 12.6's ladder is
  what needs it: there `Q(z) = c' ∏(z + a_i)` has `n-1` roots.
- **⚠️ No longer used by `thm:locality`, and the reason is worth keeping.** Theorem 12.5 applies
  the recursion only in the **order-2** case, where `Q` is linear and the solution has a *single*
  Gamma factor. Krull–Webster restricted to that case **is Bohr–Mollerup**, which Mathlib carries
  as `Real.eq_Gamma_of_log_convex`, so the step is proved in-repo as
  `lem:gamma-recursion-uniqueness` / `Hemigroup.eq_gamma_form_of_logConvex_of_recursion` and
  Theorem 12.5 no longer cites this entry. The general entry is still live at Proposition 12.6,
  where `n-1 ≥ 2` Gamma factors put it out of Bohr–Mollerup's reach. Recorded 2026-08-12. The
  discharge is *longer* than the citation, unlike the other five substitutions this project has
  made — the gain is the trust base, not the exposition.
- **Primary — Webster Theorem 3.1.** ✅ **p. 609**, opening §3 *Uniqueness Results*: let
  `g : ℝ₊ → ℝ₊` have the property that `g(x+w)/g(x) → 1` as `x → ∞` for each `w > 0`; let
  `f : ℝ₊ → ℝ₊` be **eventually log-convex**, satisfying `f(x+1) = g(x) f(x)` for `x > 0` with
  `f(1) = 1`. Then `f` is uniquely determined by `g`, through an explicit limit formula given in
  the statement. Verified against the file 2026-08-08.
- **Two hypotheses the blueprint must discharge, not assume.** The **asymptotic condition**
  `g(x+w)/g(x) → 1` is a real hypothesis on `Q`, not a regularity afterthought; and the
  normalization `f(1) = 1` is what "unique" is relative to. Webster's own lead-in notes the
  theorem generalizes Bohr–Mollerup–Artin and needs only *eventual* log-convexity rather than
  log-convexity on all of `ℝ₊` — a genuine weakening, and the reason Lemma 12.4's log-convexity
  on `(0,∞)` is more than enough.
- **Also useful — Webster Theorem 5.1, p. 615.** Closure of the class `G` under products,
  quotients and shifts. Proposition 12.6's ladder has `Q(z) = c' ∏(z + a_i)`, a product, so this
  is what keeps the ladder inside the class; worth citing there rather than re-deriving.
  Existence is Theorem 4.1, p. 612.
- **Corroboration — Marichal & Zenaïdi (2022).** ✅ *A Generalization of Bohr-Mollerup's Theorem
  for Higher Order Convex Functions*, Springer, Developments in Mathematics 70, **CC BY 4.0**.
  **Theorem 1.5 (Uniqueness), p. 3** is the `p`-convex generalization, recovering Webster at
  `p = 1`; Bohr–Mollerup is their Theorem 1.1, p. 1. Their citation of *"Webster [98, Theorem
  3.1]"* independently confirms the theorem number. (Their [97] is a *different* 1997 Webster
  paper; the two must not be merged.)
- **Acquisition note.** The paper was long unobtainable through the library's routes —
  ScienceDirect bot-blocks every PDF endpoint for PII `S0022247X97953439` and there is no OA
  mirror — and this entry stood on Marichal–Zenaïdi alone until the author supplied the file on
  2026-08-08. Anyone re-verifying should expect the automated routes still to fail.
- **⚠️ Do not transcribe formulas from this file — the page image is corrupt too.** The text
  layer is poor in the ordinary way (parentheses render as `Z…s`, `ℝ₊` as `q`, Greek lost), but
  the damage is **not confined to extraction**: the embedded font substitutes glyphs, so the
  *rendered page* is wrong as well. In the displayed limit of Theorem 3.1 on p. 609 the italic
  superscript `x` is drawn as a numeral `2` — a reader zooming in to check the formula gets a
  confidently-rendered `g²(n)` where the mathematics requires `gˣ(n)`. Settled against two
  independent checks: @marichal2022generalization eq. (1.3), p. 2, whose additive form carries
  `x·Δg(n)`; and the classical specialization `g(x) = x`, which must reproduce Gauss's limit
  `Γ(x) = lim n! nˣ / (x(x+1)⋯(x+n))` and does not with `g²`. This is the publisher's own file of
  record, so there is no better-provenance scan to chase.
  **Statements, hypotheses, theorem numbers, section headings and page numbers are all sound** —
  every anchor in this entry is unaffected. But this entry deliberately does **not** reproduce
  the limit formula, and any blueprint node that wants it must take it from
  @marichal2022generalization, which is born-digital and clean.
- **Confidence.** ✅ well grounded — the draft's own named source, read firsthand, with an
  independent held corroboration.

## A16 — HCM is closed under products and reciprocals, and HCM ⊂ GGC ⊂ SD
**Blueprint:** `prop:local-ladder` · **Lean:** *(not stated yet)*
**Cite:** @bondesson1992generalized — Theorem 5.1.1, p. 69, with the property list p. 68 (closure); Theorem 4.3.1, p. 57, with its hypotheses (a)–(c) on p. 56 (HCM ⊂ GGC); §3.1, p. 30 (GGC ⊂ SD)

- **Statement as used.** Draft Proposition 12.6: the ladder law
  `T_1 =_d 1/(c' γ_{a_1} ⋯ γ_{a_{n−1}})` is admissible. The argument is HCM closure under
  products and reciprocals, then `HCM ⊂ GGC ⊂ SD` to land inside Theorem 7.3's class.
- **Closure.** ✅ **Theorem 5.1.1 (Multiplication theorem), p. 69**: *"If `X ∼ ℋ` and `Y ∼ ℋ` are
  independent r.v.'s, then `X·Y ∼ ℋ` and `X/Y ∼ ℋ`."* Reciprocal closure is stated on the same
  page (`X ∼ ℋ` iff `1/X ∼ ℋ`), from property (iv) of the list on **p. 68** with `q = −1`.
  Verified 2026-08-08.
- **⚠️ Guard-rail, same page.** `ℋ` is explicitly **not** closed under convolution — Bondesson
  gives the two-exponential counterexample on p. 69. Proposition 12.6's blueprint proof must not
  over-claim: only the *multiplicative* structure is available.
- **HCM ⊂ GGC.** ✅ **Theorem 4.3.1 (Main HCM-theorem), p. 57**, with the regularity hypotheses
  (a), (b), (c) stated on **p. 56** — those are hypotheses, not decoration, and the blueprint
  must discharge them. HCM is defined p. 55.
- **⚠️ GGC ⊂ SD is not a numbered theorem.** ✅ **§3.1, p. 30**: *"Since the Gamma distribution
  is ID and self-decomposable (SD), so is every GGC."* One sentence, restated in the summary on
  p. 2. It is load-bearing here and the entry records that its status in the source is an
  assertion rather than a displayed theorem. It is elementary and could be carried **[T]**
  instead if that is judged too thin.
- **Bonus anchor, recorded so it is not re-researched.** **Theorem 3.1.1, p. 30** characterizes
  GGC by the Lévy measure (`F` is a GGC iff ID with `y·ℓ(y)` completely monotone), and Bondesson
  **names `U` "the Thorin measure" on that page**; the GGC definition (3.1.1) on p. 29 is the
  Thorin representation. This is a second, independent, held anchor for the Thorin measure
  alongside the SSV one below.
- **Cross-check for A13.** On p. 57 Bondesson cites *"Widder (1946, p. 58)"* for the
  singularity-at-the-abscissa result — independently confirming both A13's page **and** that the
  1946 printing we hold carries 1941 pagination.
- **Confidence.** ✅ well grounded for the closure and the HCM ⊂ GGC step; ⚠️ the GGC ⊂ SD step
  rests on a one-sentence assertion, flagged above.

---

## A17 — Existence: every drift-plus-Lévy-measure pair is the Laplace exponent of a subordinator
**Blueprint:** *(none — Lean-side entry, see below)* · **Lean:** `Hemigroup.exists_isFiniteMeasure_laplace_eq_exp_neg_levyExponent`
**Cite:** @schilling2012bernstein — Theorem 5.2, p. 49, converse clause (Ch. 5, "A probabilistic
intermezzo"), 2nd ed.; the triple ⟹ `BF` leg is Theorem 3.2, p. 21, already A3's anchor

- **Statement as used.** Given `b₀ ≥ 0` and a causal measure `ν` whose exponent
  `g(s) = b₀ s + ∫ (1 − e^{−st}) ν(dt)` is finite for `s ≥ 0`, there exists a causal **finite**
  measure `μ` on `ℝ` with `μ̂(s) = e^{−g(s)}`. This is the **existence** half of the
  subordinator correspondence — the converse of A3, which carries the representation half.
- **The first Lean-side entry** (2026-08-09). It grounds no `[A]` node and no `\ledger{}`
  reference points at it, which `linkage check` permits: check 2 requires every reference to
  resolve to an entry, not every entry to be referenced. It exists because the **Lean route
  differs from the blueprint's**. The blueprint proves `thm:main-characterization` (⇐) through
  complete monotonicity — `prop:bernstein-toolbox`(2) then Bernstein–Widder, (1) — which is A1
  and A2. Lean never forms a completely monotone function: `lem:selfdecomposable-exponents`'
  Lean form hands over the Lévy triple explicitly, so what is needed is a *construction* from a
  triple, not a *representation theorem*. That is a strictly smaller interface, and it keeps
  `CompletelyMonotone` out of the development entirely
  (`blueprint/DESIGN-formalization-strategy.md`).
- **Primary — SSV Theorem 5.2, converse clause.** ✅ **p. 49**: *"Conversely, given `f ∈ BF`,
  there exists a unique convolution semigroup of sub-probability measures `(μ_t)_{t≥0}` on
  `[0,∞)` such that (5.1) holds true"*, where (5.1) is `𝓛μ_t = e^{−tf}`. Existence is an
  **explicit clause of its own**, not something read off a bijection, and it carries uniqueness
  of the semigroup. "Convolution semigroup" means *vaguely continuous* by Definition 5.1 and the
  standing convention on p. 48. Verified against the page image 2026-08-09.
- **The feeder leg needs no new trust.** `(0, b₀, ν) ⟹ g ∈ BF` is the converse direction of SSV
  Theorem 3.2, which is printed as an *iff*; see A3, whose note records this. So this entry
  cites a second theorem but adds only one new fact.
- **What this entry deliberately does NOT carry: the probability-measure refinement.**
  Theorem 5.2 yields **sub**-probability measures. That `g(0+) = 0` upgrades them to probability
  measures has *no numbered statement in SSV* — it is a line of the proof of 5.2
  (`μ_t[0,∞) = 𝓛(μ_t;0+) = e^{−t f(0+)}`) and a sentence of prose on **p. 51**. Rather than
  widen the citation to remark-grade material, the axiom claims only what Theorem 5.2 states and
  the refinement is proved: our `levyExponent` has no killing term by construction
  (`Hemigroup.levyExponent_zero`), so evaluating the transform at `s = 0`, where it is the total
  mass, gives `1`. That is `Hemigroup.exists_isProbabilityMeasure_laplace_eq_exp_neg_levyExponent`
  and it is **[T]**.
- **Nor uniqueness of `μ`.** Theorem 5.2 supplies it, but taking it here would cancel the M0
  remainder. It is `prop:laplace-uniqueness` on paper and is intended to become a proved lemma
  (Laplace injectivity), not a second axiom.
- **Hypothesis translation.** The Lean statement hypothesises finiteness of the exponent rather
  than the source's `∫ (1 ∧ t) ν(dt) < ∞`. Equivalent for causal `ν`, and in the safe direction:
  concavity of `t ↦ 1 − e^{−st}` on `[0,1]` gives `1 − e^{−st} ≥ (1 − e^{−s}) (1 ∧ t)` for
  `t ≥ 0`, so finiteness at a single `s > 0` already forces the integral condition. The axiom is
  therefore no stronger than the theorem it is anchored on. `IsCausal ν` also permits mass at
  `t = 0`, which SSV's `ν` on `(0,∞)` excludes; harmless, since the integrand vanishes there and
  the exponent does not see it.
- **Corroboration — Sato, assembled from three numbered statements.** ✅ **Theorem 8.1(iii),
  p. 38** (§8): *"Conversely, if `A` is a symmetric nonnegative-definite `d × d` matrix, `ν` is a
  measure satisfying (8.2), and `γ ∈ ℝ^d`, then there exists an infinitely divisible distribution
  `μ` whose characteristic function is given by (8.1)."* — existence as a labelled clause.
  ✅ **Corollary 11.6, p. 63** promotes it to a Lévy process, unique up to identity in law.
  ✅ **Theorem 21.5, p. 137** is the subordinator criterion, a test on an existing process rather
  than a construction. The half-line Laplace form is **Remark 21.6, formula (21.1), p. 138**,
  matching our sign convention with `b₀ = γ₀` — but it is a *remark* deferring to the proof of
  21.5, so Sato has no numbered theorem for it. That is why SSV stays primary. Verified against
  page images 2026-08-09.
- **Editions.** @schilling2012bernstein: held copy is the **2nd edition, © 2012 de Gruyter**
  (ISBN 978-3-11-025229-3) — citekey year correct, unlike the Feller case in A1. The 2nd-edition
  preface records new material added *within* Chapter 5, so this anchor is edition-specific and
  says so. @sato1999levy: held copy is the **1st English edition, Cambridge 1999** (ISBN
  0-521-55302-4, CSAM 68); a revised 2013 edition exists, so the anchor says "1999 ed.".
- **⚠️ Transcribe from page images for both sources.** SSV's text layer silently drops Greek and
  script letters (`μ`, `λ`, `𝓛`); Sato's OCR is poor throughout (cf. A7). Every quotation above
  was read off the rendered image, not the text layer.
- **Confidence.** ✅ well grounded: existence and semigroup uniqueness are an explicit clause of a
  numbered theorem, and the one part of the fact that the source states only as prose has been
  moved out of the trust base and proved.

---

**Reserved beyond this transcription's scope.** The **Thorin representation** — draft
Proposition 13.6, i.e. §13, which is not being transcribed — has a verified anchor already, and
it is recorded here so it is not re-researched later: @schilling2012bernstein — **Definition 8.1
and Theorem 8.2, pp. 109–110** (2nd ed.), Theorem 8.2(iii) giving
`f(λ) = a + bλ + ∫ log(1 + λ/t) σ(dt)` with `σ` **unique**. The draft names the Thorin
representation and the Thorin measure eleven times and cites only Bondesson at chapter level;
this is the statement-level anchor for it, in a source the article already trusts.

**On the Krein correspondence** (draft §§1 and 15, outside this scope): the librarian's
recommended primary is @kotani1982krein — Kotani & Watanabe, LNM 923, pp. 235–259 — over Krein's
own Doklady announcements, which are Russian and proofless. Decisively, it is the reference
**SSV itself** leans on in Ch. 15 (*Applications to generalized diffusions*), bibliography entry
[217], cited at pp. 270, 292 and 297 — so the article's Krein anchor stays inside a source it
already trusts. @dym1976gaussian is the book-length companion.

---

## A18 — Self-decomposability: an exponent whose dilation increments are Bernstein has a nonincreasing Levy density
**Blueprint:** `lem:selfdecomposable-derivative` (the direction (1) => (3)) · **Lean:** `Hemigroup.exists_antitone_density_of_dilation_increments`
**Cite:** @schilling2012bernstein — Proposition 5.17, p. 57, with Definition 5.14, p. 55 (2nd ed.); the `k(t)/t` normalisation is the source's own, from the proof on p. 59

- **Statement as used.** Let `F(s) = b0 s + INT_0^inf (1 - e^{-st}) nu(dt)` with `b0 >= 0` and
  `nu` a Levy measure on `(0,inf)` — so `F` is Bernstein with `F(0+) = 0`. If
  `F(b*) - F(a*)` is Bernstein and vanishes at `0+` for **every** `0 < a <= b`, then `nu` has a
  density `k(t)/t` with `k : (0,inf) -> [0,inf)` **nonincreasing**.
- **Primary — SSV Proposition 5.17.** OK **p. 57**, verified against the page image 2026-08-10:
  *"Let `f` in BF satisfy `L(pi) = e^{-f}` and let `mu` be the Levy measure of `f`. Then the
  following assertions are equivalent. (i) `mu` has a density `m(t)` such that `t -> t * m(t)` is
  non-increasing; (ii) `pi` is in SD."* Self-decomposability is **Definition 5.14, p. 55**: *"A
  completely monotone function `g` in CM with `g(0+) <= 1` is said to be self-decomposable, if
  `lambda -> g(lambda)/g(c*lambda) = g_c(lambda)` is completely monotone for all `c` in
  `(0,1)`."*
- **Printed as an iff; we use the hard half, (ii) => (i)**, proved pp. 57-59.
- **`k(t)/t` is the source's normalisation, not a reformulation.** The (ii) => (i) proof on p. 59
  builds `k(v) := l(e^{-v})`, records *"k is non-negative and non-increasing"*, derives
  `M(t) = INT_t^inf k(v)/v dv`, and closes *"the proof is finished by defining
  `m(t) := k(t)/t`."* That is exactly `levyExponentD`'s shape.
- **The hypothesis bridge, and what it costs.** Our hypothesis is *the increment is Bernstein*;
  Definition 5.14's is *the ratio is completely monotone*. The direction we need — ours implies
  his — is the cheap one, and SSV performs it inside the same proof on p. 59:
  *"`g_c(lambda) = g(lambda)/g(c*lambda) = e^{-f(lambda)}/e^{-f(c*lambda)} = e^{-f_c(lambda)}`,
  proving that `g` is completely monotone."* It uses `f` Bernstein implies `e^{-f}` completely
  monotone, which is **A2**. So the anchor route for this entry runs through A2 and Proposition
  5.17 — *not* through A4 and A3, which is how the blueprint's own proof of
  `lem:selfdecomposable-derivative` gets there. Both are valid; the routes are independent, and
  this entry is anchored on the first.
- **The anchors interlock; the axioms do not** (fidelity review 2026-08-15, R17). Proposition
  5.17 is a statement about a sub-probability measure `pi` with `L(pi) = e^{-f}`; our axiom is a
  statement about the function `F`. Reading our hypothesis as Definition 5.14's therefore
  passes through "an `F` in BF with `F(0+) = 0` is the exponent of some `pi`" — Theorem 5.2's
  converse clause, which is A17's anchor. So a reader auditing whether A18 is anchored
  independently of A17 should know: as *Lean axioms* the two are independent postulates
  (`CIAxiomGuard.lean` prints each on its own consumers); as *anchors* they share Theorem 5.2.
  This does not make A18 stronger than its source — SSV's own proof performs the same bridge.
- **Quantifier shape.** Our `for all 0 < a <= b` and the printed `for all c in (0,1)` are the
  same condition: take `c = a/b` and substitute `lambda = b*s`, a bijection of `(0,inf)`;
  `a = b` gives the trivial `0` in BF. This is why the Lean statement quantifies over pairs.
- **The source is more general than we are.** SSV allows a killing term (`g(0+) <= 1`, so
  sub-probability, `a > 0` in the triplet); our `levyExponent` has none by construction, forcing
  `a = 0` (Remark 3.3(iv), p. 23: `a = f(0+)`). Our hypothesis is a special case — the safe
  direction. The clause "increment vanishing at `0+`" is likewise **automatic**, not an extra
  assumption: `f_c(0+) = F(0+) - F(0+) = 0`.
- **Right-continuity of `k` is available but not assumed.** **Remark 5.18, p. 59**: *"In the
  proof one can choose `m(t)` so that `t * m(t)` is right-continuous. Hence, Proposition 5.17 can
  be stated as `pi` in SD if, and only if, `t*m(t)` is 1-monotone"* — and *1-monotone* is
  nonnegative, nonincreasing **and right-continuous** (Definition 1.10, p. 8). Our Lean statement
  asks only `AntitoneOn` and nonnegativity, i.e. strictly less than is available.
- **Uniqueness of `k` is NOT claimed, and should not be.** `nu` is unique (Theorem 3.2,
  pp. 21-22, is one-to-one on triplets), so `k` is unique Lebesgue-a.e.; two nonincreasing
  right-continuous functions agreeing a.e. agree everywhere, so the 1-monotone version is
  genuinely unique. **That last step is an inference, printed in neither SSV nor Sato.** Our
  interface existentially quantifies `k` and asserts no uniqueness, so it stays strictly inside
  the citation.
- **The two integrability conditions of (7.1) are consequences, not dropped assumptions.** This
  was flagged as a check to run and is now discharged on paper: Theorem 3.2's Levy measure
  satisfies `INT (1 ^ t) nu(dt) < inf`, and with `nu(dt) = k(t)/t dt` that reads
  `INT_0^1 t * k(t)/t dt = INT_0^1 k(t) dt < inf` and `INT_1^inf k(t)/t dt < inf` — exactly the
  blueprint's pair.
- **Non-vacuity, checked in Lean.** An axiom whose hypothesis is unsatisfiable proves everything
  about nothing. `Hemigroup.exists_levyExponent_dilation_increment` shows the exponents A18
  concludes *about* satisfy the hypothesis it assumes — it is `levyExponentD_increment` restated
  in A18's shape, and it does not use A18. This was the second outstanding check and it is now
  run.
- **The intermediate form `B(s) = s F'(s)` Bernstein has no numbered source.** Searched in both
  books (2026-08-10): SSV's idiom is uniformly `t*m(t)`, and Sato's is the `k`-function. What
  underwrites the derivative form is equation (3.3) in Remark 3.3(ii), **p. 23** —
  `f(lambda) = a + b*lambda + lambda INT_0^inf e^{-lambda*s} M(s) ds` with `M(s) = nu(s,inf)`
  nonincreasing and right-continuous — combined with the derivative identity in the proof of
  Theorem 3.2, p. 21. So Lemma 7.1's clause (2) is a **derivation**, and anyone tempted to cite a
  source for it will not find one. The Lean development never forms it, which is the other reason
  it does not matter here.
- **Why not Sato.** OK **Theorem 15.10, p. 95** verified: it is `R^d` with polar decomposition,
  `nu(B) = INT_S lambda(dxi) INT_0^inf 1_B(r*xi) k_xi(r) dr/r`. **Corollary 15.11, p. 95** is the
  `R^1` case but on the *whole line* and in characteristic-function form. There is **no numbered
  half-line or subordinator specialisation** — Sato uses "selfdecomposable subordinator" only in
  Remarks 53.11 (p. 415) and 54.6 (p. 418), both referring back to Corollary 15.11. Getting from
  there to `F` means specialising `k = 0` on `(-inf,0)`, `A = 0`, and re-deriving the drift from
  Sato's `1_{[-1,1]}` cutoff — real work that a citation would hide. SSV is anchored in the right
  vocabulary and is used instead. Historically the two agree: SSV's Chapter 5 notes, **p. 67**,
  credit the proof to Levy and say it is *"adapted from Sato [314, p. 95]"* — the page verified
  above.
- **A convention worth recording if Sato is ever cited alongside.** Sato's *Remarks on notation*,
  **p. xi**: *"decreasing means `f(s) >= f(t)` for `s < t`"* — so Sato's "decreasing" is our
  "nonincreasing", not strict. And Sato normalises the `k`-function **left**-continuous on
  `(0,inf)` (p. 403) where SSV normalises **right**-continuous. Harmless — they agree a.e. — but
  do not mix the two.
- **Retirability: worse than A17, and this should be said plainly.** A17 was phrased so it could
  be demoted once the compound-Poisson construction is carried out, which Mathlib's Prokhorov
  puts within reach. A18 has no comparable path. Its `(2) => (3)` leg is arguably reachable —
  `Hemigroup.laplace_injective` already gives the uniqueness it needs — but `(1) => (2)` requires
  differentiability of Bernstein functions, precisely the vocabulary this development excludes.
  Treat this entry as permanent.
- **Confidence.** OK well grounded. The anchor is image-verified, the hypotheses match or are
  weaker than printed, both outstanding checks are discharged, and the two places where we go
  beyond the printed text — the A2 bridge and the uniqueness inference — are recorded above and
  neither is needed by the Lean statement.

## A19 — Variation diminution and total positivity coincide for translation kernels
**Blueprint:** `prop:gamma-regularity` (also consumed by `prop:vd-impossibility`) · **Lean:** *(none — the VD/TP vocabulary is outside the development by design)*
**Cite:** @karlin1968total — Ch. 5, Theorem 3.1(i), p. 233, and Theorem 4.2, pp. 242–243

- **Statement as used.** Convolution with a density kernel is variation-diminishing —
  `S^-(k * g) <= S^-(g)`, sign changes counted in the essential sense — **iff** the
  translation kernel `k(u - v)` is totally positive; for a kernel supported on `[0,inf)`
  that is the one-sided Pólya frequency property. Both directions are consumed:
  sufficiency by `prop:gamma-regularity`(1) (a PF kernel diminishes the counts of the
  field), necessity by `prop:vd-impossibility` Step 1 (a variation-diminishing increment
  has a PF density after smoothing).
- **Primary — Theorem 3.1(i), p. 233 (sufficiency).** If `K(x,y)` is `SR_r` (`r >= 2`) and
  `f` has `n <= r - 1` relevant sign changes with respect to `mu`, then
  `S^-[g] <= S_mu[f]` for the transform `g(x) = INT K(x,y) f(y) dmu(y)` — display (3.5).
  Printed hypotheses: `f` bounded Borel-measurable (the section's standing convention,
  stated at the top of p. 233), the integral finite. A `TP_inf` translation kernel gives
  the bound for every `n`. The extension from bounded to integrable arguments used by the
  node is the standard truncation and is **taken with the citation**, recorded in the
  node's Assignment.
- **Primary — Theorem 4.2, pp. 242–243 (necessity).** Let `k(u)` be a density on
  `(-inf,inf)`. If the transformation (4.4) enjoys property (4.6) — `S^-(g) <= S_mu(f)`
  for all bounded Borel `f` with `S_mu(f) <= r - 1`, `mu` Lebesgue measure — then
  `k(u - v)` is `TP_r` a.e. Built on Theorem 4.1 (p. 242), which delivers `SR_r`, and the
  sign-pinning argument on p. 243.
- **Counting convention.** Karlin's *relevant sign changes with respect to `mu`* with `mu`
  Lebesgue measure is exactly the blueprint's essential (almost-everywhere) counting; the
  nodes state their counts in that sense, so hypotheses and conclusion match the printed
  form with no translation beyond vocabulary.
- **Provenance.** Added 2026-09-01, promoting the external-review results (the repaired
  Pólya-frequency proposition and the impossibility theorem) from the paper on the
  author's instruction. All three page anchors read from the held scan in the same pass.
- **Confidence.** OK. The anchors are image-verified; the one step beyond the printed text
  — bounded to integrable arguments in the sufficiency leg — is named here and in the
  consuming node's Assignment, not silently absorbed.

## A20 — Schoenberg's representation of one-sided Pólya frequency densities
**Blueprint:** `prop:vd-impossibility` (also consumed by `prop:gamma-regularity`) · **Lean:** *(none — the VD/TP vocabulary is outside the development by design)*
**Cite:** @karlin1968total — Ch. 7, Theorem 3.2(b), p. 345, and Remark 3.1, p. 346

- **Statement as used.** A density supported on `[0,inf)` is a one-sided Pólya frequency
  density **iff** the reciprocal of its Laplace transform is an entire function of the
  form `C e^{delta s} PROD_i (1 + lambda_i s)` with `C > 0`, `delta >= 0`,
  `lambda_i >= 0`, `SUM_i lambda_i < inf`. Necessity is what `prop:vd-impossibility`
  spends (the product form of `e^g (1 + eps s)^2`); sufficiency is what
  `prop:gamma-regularity` spends (reading `(1 + xs)^gamma` and the Thorin-atom form
  against it), together with the branch-point exclusion for non-integer `gamma`.
- **Primary — Theorem 3.2(b), p. 345.** "A necessary and sufficient condition that a
  density function `f(u)`, for which `f(u) = 0` (`u < 0`), be PF is that the reciprocal of
  its Laplace transform be an entire function of class `E_1^*` with `SUM lambda_i > 0`."
  Assembled on the page from Theorems 2.1, 2.2, 3.1 and Remark 2.1.
- **Primary — Remark 3.1, p. 346.** Drops integrability and displays the one-sided form
  explicitly: `f` PF with `f(u) = 0` for `u < 0` iff the transform exists and equals
  `e^{-delta s} (s^r PROD_i (1 + lambda_i s))^{-1}`, `delta >= 0`, `lambda_i >= 0`,
  `0 < SUM lambda_i < inf`, `r` a nonnegative integer; a *density* is the case `r = 0`,
  with the reciprocal `C e^{delta s} PROD (1 + lambda_i s)` — the form as used above. The
  degenerate case `SUM lambda_i = 0` (a pure shift) is excluded by the printed
  `SUM lambda_i > 0`; the nodes' pure-delay member enters as the *kernel* `delta_{b_0 x}`,
  not as a PF density, and no claim about it rides on this entry.
- **Provenance.** Added 2026-09-01 together with A19, same pass, both page anchors read
  from the held scan.
- **Confidence.** OK. Both anchors image-verified; the statement as used is the printed
  one specialised to densities (`r = 0`), with the sign convention reconciled — Karlin's
  one-sided display on p. 346 is in the `(1 + lambda_i s)` form, matching the nodes
  verbatim.

## Notes on the sources

- **@feller2009introduction** — the citekey year is wrong (the item is the 2nd edition, 1971)
  but it is **canonical across the constellation** and must not be repinned.
- **@lindebergGeneralizedGaussianScaleSpace2010** — likewise says 2010 for a 2011 paper;
  canonical, not repinned. Metadata was corrected in place.
- **@fagerstrom2005temporal** — full bibliographic data now pinned: *Int. J. Computer Vision*
  **64**(2–3), September 2005, pp. 97–106, doi 10.1007/s11263-005-1837-8. The draft's reference
  list carried no volume or pages for the article it cites 24 times.
- Five citekeys were **repinned** in this pass (`sato1999levy`, `clement1981asymptotic`,
  `koenderink1988scale`, `steutel2004infinite`, `devries1992gamma`); none of the old keys was
  referenced anywhere in this repo, the hub vault, or `scale-space-foundations`.
- **@iijima1962basic** is metadata only and effectively unobtainable outside Japan. It is cited
  for provenance in the introduction and **must never carry a page anchor**.
