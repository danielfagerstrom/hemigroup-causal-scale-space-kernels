# Exposition notes for the article

Written 2026-08-12, after chapter 11 closed and both headline theorems went `\leanok`. Input to
the article-writing pass, in three parts: what the draft now says differently and what still
should; whether the `CM`/`BF` vocabulary needs reformulating; and a reader-facing account of what
is machine-checked against what is cited.

Companion to `DESIGN-formalization-strategy.md`, which predicted much of Part 2 before the work
started and can now be scored against it.

---

# Part 1 — Exposition consequences of the corrections

## Already in the draft

Six corrections landed in `draft/` and `blueprint/src/parts/11-signaling.tex` this session. All are
in §11, and none changes a result — each changes what a statement *says* or what a proof *spends*.

1. **Lemma 11.2's proof.** Three separate repairs. The Tonelli exchange is licensed by the strip
   condition *and by nothing else* — run on absolute values it is finite **iff** `c < z_*`, so the
   condition is characteristic rather than merely sufficient. (H)'s first clause `F(∞) = ∞` is used
   exactly once, to give `T₁ > 0` a.s., and without it the identity is **false**, not merely
   unproved: at an atom `t = 0` the inner integral diverges while `E[T₁^{-c}]` does not see the
   atom. And vertical integrability needs only *quadratic* decay of `|Γ(c+iτ)|` — two lines of the
   functional equation — where the proof had appealed to the super-polynomial asymptotic.

2. **Definition 11.3.** The second display is an assertion, not a rewriting: `B(θ)` is a functional
   calculus for a symbol with poles, so `(Ag)(x) = x⁻¹(B(θ)g)(x)` says that a function `h` with
   `h̃ = B(-z)g̃` on the line *exists* and that the contour integral computes it. Every application
   in the article exhibits its `h` outright, so Widder Thm 9a is available but never spent.

3. **Lemma 11.4.** Now says *which* equality: for meromorphic symbols, agreement on a punctured
   neighbourhood of every point, pointwise where both are continuous. Its proof is replaced by the
   direct route, which needs strictly less — no injectivity of the inverse Mellin transform (two
   operators agreeing on `H(s·)` share a realising function), and a single dilation rather than all
   `s > 0`.

4. **Theorem 11.6(1).** "No pole of `B` intervenes, the product containing no division" is true of
   the *simplified* product and false of `B` as a function. The proof now exhibits `h(x) = s·x·H(sx)`
   and notes that clearing the division costs an exceptional set, isolated hence null.

5. **Lemma 11.5's range.** The lemma states `1 < Re z < z_*`; Theorem 11.6(2) states the same range
   while applying the lemma **at `z-1`**, which that range does not cover. The chain closes because
   `f ∈ 𝒟` is bounded, which moves the lower endpoint to `0`. Nothing about the result changes;
   what changes is what the lemma says. Both documents now say it.

6. **Lemma 11.5's derivative clause.** `∂_t u` had to name its reading. Pointwise it is **false**:
   `f ∈ 𝒟` is absolutely continuous so `f'` exists only a.e., and the field is a convolution of two
   `L¹` functions, hence `L¹` and not continuous. The article means the `X₀` derivative of §10, and
   what §10's `Φ`-invariance argument establishes is `μ * f = 1_{[0,∞)} * (μ * f')` — the field of
   `f` is the *primitive* of the field of `f'`. Also: `Iᶻf' = I^{z-1}f` follows from Fubini over a
   triangle without the semigroup identity `I^{z-1}I¹ = Iᶻ` the draft invoked.

## Identified and not yet written

Four items, in rough order of value.

7. **Remark 7.6 and hypothesis (H) are the same fact, stated 200 lines apart.** Remark 7.6 closes
   with "every extreme ray has `F(s) ∼ log s` and hence `z_* = 1`: the extreme boundary of the cone
   lies exactly on the boundary of hypothesis (H)". §11 then needs `z_* > 1` and never refers back.
   The formalisation makes the connection sharp, because `Re z > 1` arrives **three independent
   times** in chapter 11 — the delayed average's inner integrability, the application of 11.5 at
   `z-1`, and the convergence of `∫_ρ^t (t-r)^{z-2}dr`. Three different obligations, one endpoint.
   That is worth a forward reference in 7.6 and a sentence in §11 saying the endpoint is
   characteristic rather than an artefact of one argument.

8. **What `f ∈ 𝒟` is actually for.** Lemmas 11.5 and 11.6 cite `𝒟` wholesale. Exactly three of its
   features are used: *boundedness* (widens 11.5's strip, item 5 above), *being a primitive* (gives
   the derivative clause its meaning), and *integrability* (the Laplace form — and note that
   "primitive of an `L¹` function" does **not** imply `L¹`, since the primitive tends to `∫₀^∞ f'`;
   `𝒟` asks for `f ∈ X₀` *and* `f' ∈ X₀` and thereby imposes it). Density, `T_r`-invariance and
   `Φ`-invariance — the substance of Lemma 10.1, which the proof cites — are used nowhere. Saying so
   would let §11 stand on a hypothesis it names, rather than on §10.

9. **The article's stance on Mellin inversion (A12).** The paper cites Widder Thm 9a for
   Definition 11.3 and is entitled to. The formalisation never reaches it, because every use
   exhibits its referent. Editorial choice: keep the citation as the paper's own route (my
   preference — it is the honest description of the argument as written), and add one clause to
   Definition 11.3 noting that each application below exhibits `B(θ)g` explicitly, so the reader
   who wants to avoid the citation can. Item 2 already does half of this.

10. **Remark 11.8's regularity claim.** "The identity is nevertheless regular, the factor
    `H̃(z-1)` cancelling every denominator" is true of the product as a *meromorphic function* and
    not of `B` evaluated at a point. The remark is not wrong, but it is the third place in §11
    where a symbolic cancellation has to become a pointwise one, and one sentence distinguishing
    the two readings would close the pattern the other two now name.

---

# Part 2 — `CM` and `BF`: does the prose need reformulating?

## The short answer

**No — but five proofs should change, and for the article's own sake rather than Lean's.**

The `CM`/`BF` prose is accurate. Nothing found in this project contradicts a `CM` or `BF`
statement in the draft, and the classical arguments are correct as written. The question is not
correctness but *economy*: in five places the classical route asks for strictly more than the
statement needs, and the elementary route is shorter, spends less, and reads no worse.

## Where the classical route costs more than it must

Each row is a place the draft invokes a named classical theorem and the development instead uses
an elementary argument. **None of these is a formalisation artefact** — each is a shorter proof of
the same statement, available on paper.

| draft proof | what it spends | the shorter route |
|---|---|---|
| Thm 5.2, increments are Bernstein | **A4** — `BF` closed under pointwise limits, applied to a cone-closure | the Lévy representation comes straight off the weak limit; no closure theorem |
| Lemma 9.4/9.5, the potential kernel | **A1** (Bernstein–Widder) + **A2** (`CM ∘ BF ⊆ CM`) | the subordinator's potential measure `U = ∫₀^∞ μ_t dt`, *constructed*, never represented |
| Lemma 11.2, vertical integrability | super-polynomial `Γ` decay, i.e. Stirling in the complex plane | `\|Γ(σ+iτ)\| ≤ Γ(σ)` and `Γ(z+2) = (z+1)zΓ(z)`: quadratic decay, which is all integrability needs |
| Lemma 11.5, derivative clause | the Riemann–Liouville semigroup `I^{z-1}I¹ = Iᶻ` | Fubini over `0 < ρ ≤ r ≤ t`, leaving `∫_ρ^t (t-r)^{z-2}dr` |
| Lemma 11.4, uniqueness of the symbol | Mellin injectivity (anticipated; Widder Thm 6a) | two operators agreeing on `H(s·)` share a realising function, so their transforms agree at every point |

The pattern is one thing said five times: **the paper reaches for a named theorem about a class
where an elementary argument about the object suffices.** Acting on it shortens the article's own
trust base — the reader who does not want Bernstein–Widder is currently told they need it, and they
do not.

## Where `CM`/`BF` is irreducible and should stay

Three places, and they are different in kind from the five above.

- **Lemma 7.1, (1) ⇒ (2) ⇒ (3).** `B(s) := sF'(s)` has no meaning in the representation vocabulary
  until the representation is in hand. This is genuinely derivative-sign mathematics; it is why
  ledger **A18** is expected to be permanent where **A17** is not. The asymmetry of Lemma 7.1 —
  (3) ⇒ (1) elementary and machine-checked, the other two legs not even *statable* without `CM` —
  is real mathematics and is worth saying in the text, because it explains why the constructive
  direction of the main theorem is cheap and the analytic one is not.
- **Proposition 9.7(3) and Proposition 13.6.** Statements *about* the `CM` class — the classical
  Sonine case, the Thorin subclass. Here `CM` is the subject, not a tool, and removing it would
  remove the content.
- **Proposition 2.3, the toolbox.** The article's bridge, and it should stay exactly as it is: one
  place where the two vocabularies are identified, cited, and never re-derived.

## A larger editorial question

§2 currently opens with Definition 2.1 (`CM`) and Definition 2.2 (`BF`), presenting them as the
foundation. The development shows that the **Lévy representation is the load-bearing notion** and
`CM`/`BF` is a characterisation invoked at three specific places. One could reorder §2 so the
representation (7.1) comes first, with `CM`/`BF` as the classical equivalent in Proposition 2.3.

Arguments for: it matches how the mathematics actually flows; it makes the trust base visible in
the order of presentation; it is what a reader reconstructing the proofs would want.

Arguments against: `CM`/`BF` is the field's vocabulary, the results are stated for readers who know
it, and Bernstein-function language is how this material is indexed and found.

**Recommendation: keep the vocabulary, change the five proofs, and add one paragraph** — in §2
after Proposition 2.3, or in §15 — saying plainly that the representation form is what the
arguments use, that `CM`/`BF` enters at three named places, and that Proposition 2.3 is the bridge.
That gets the honesty of the reordering without the cost.

## Scoring `DESIGN-formalization-strategy.md`

That document predicted, before any Lean was written, that the draft "can be made
Bernstein–Widder-free" and that representation-first definitions would "probably halve the
project". The prediction held, and held further than stated: the trust base is **two** entries, and
Bernstein–Widder (A1) is not among them. It was also right about the specific mechanisms — the
weak-limit route for Thm 5.2, Laplace injectivity from Stone–Weierstrass, Prokhorov for tightness.

What it got wrong is worth recording too. It listed the Mellin transform "with an inversion
theorem" as a gift making §11 "less hopeless than one would guess" — correct — but the inversion
theorem turned out to be the one piece of §11 that was *never used*, because every application
exhibits its own referent. And it expected `StieltjesFunction` to carry the Lévy measure `-dk`;
that failed, because Mathlib's Stieltjes measures are finite on bounded intervals and a Lévy
measure need not be. The quantile transform replaced it.

---

# Part 3 — Machine-checked versus cited: a reader-facing summary

## The numbers

| | |
|---|---|
| Blueprint statement nodes | 76 |
| With machine-checked proofs | 44 |
| Trust base (axioms the proofs rest on) | **2** |
| Ledger entries (cited analytic interfaces) | 18 |
| `sorry` in the development | 1, at Prop 9.7(2), ledger A9 by design |
| Headline theorems machine-checked | both — Thm 7.3 (2′) and Thm 11.6 (4′) |

## What the two axioms are

- **A17** — every drift-plus-Lévy-measure pair is the Laplace exponent of a subordinator. The
  *existence* half of the subordinator correspondence, and the only thing the constructive
  direction of the main theorem needs that is not proved here. Phrased in the development's own
  vocabulary, so that the day the compound-Poisson construction is carried out it becomes a lemma.
- **A18** — an exponent whose dilation increments are Lévy exponents has a Lévy measure with
  nonincreasing density `k(t)/t`. Self-decomposability in the direction the *analysis* needs.
  Expected to be permanent, for the reason in Part 2: its other leg needs the derivative-sign
  vocabulary the development excludes.

Note the separation, which is checked rather than asserted: `(⇐)` and the uniqueness clause of the
main theorem rest on A17, `(⇒)` on A18, and **neither borrows the other's**.

## The eighteen ledger entries, sorted by what actually happens to them

| | entries | what it means |
|---|---|---|
| **Spent** — reached by a machine-checked proof | A17, A18 | the trust base, 2 of 18 |
| **Cited by proved results whose proofs avoid them** | A3, A4, A5, A6, A9, A12 | the paper spends them; the formalisation does not |
| **Under nodes not formalised** | A1, A2, A7, A8, A10, A11, A13, A14, A15, A16 | chapters 8, 10, 12 and the toolbox |

The middle row is the interesting one and is the honest headline: **six of the interfaces the
article leans on are cited by results that are machine-checked without them.** A12 is the sharpest
case — nine nodes cite it, all nine are proved, and none spends it. A4 and A3 are the next: Theorem
5.2 spends them on paper and its Lean proof reduces to Lean core.

## Suggested placement in the article

A short subsection — §1.4 or an appendix "What is machine-checked" — with:

1. the numbers table above;
2. the two axioms, stated in one sentence each, with their page anchors;
3. the sorted ledger table;
4. one paragraph on the separation A17/A18 and why it is checked rather than claimed;
5. a pointer to the repository, the blueprint's dependency graph, and `CIAxiomGuard.lean`.

What to claim, precisely: *the construction of the kernel families, the main characterization, and
the signaling form are machine-checked from the axioms (A1)–(A8) with two analytic interfaces taken
on trust, both stated with page-verified citations.* Not "the paper is formalised" — chapters 10 and
12 are not, and the summary should say which chapters are and which are not.

## What is not formalised, and why

Worth one honest paragraph, because the reasons differ and a reader can check them:

- **Chapter 10** (the scale-Cauchy problem) and **chapter 12** (locality) need C₀-semigroup and
  closed-operator theory, and Bessel `K` — absent from Mathlib. Not a design choice.
- **Prop 9.2 and Cor 9.10** need a locally integrable function read as a distribution and a
  distribution convolved with a measure; `Analysis/Distribution/` does not yet have them.
- **Prop 9.7(2)** is ledger A9 by design: it is a statement about the `CM` class, which the
  development deliberately does not define.
- **Lemma 10.1** is not blocked and is not needed by anything now that chapter 11 is closed; it is
  simply optional.
