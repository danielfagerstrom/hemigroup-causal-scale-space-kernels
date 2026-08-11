/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
-- `Hemigroup.Sonine` rather than `MemoryKernelTransform`: Route B's main argument below uses
-- `laplaceL_volume_Ici`, which is where `thm:sonine-conservation` needed it too.
import Hemigroup.Subordinator

/-!
# The target types of chapter 9

**This file carries `sorry`s and is not part of the `Hemigroup` library.** Phase 2 of
`blueprint/PLAN-chapters-8-12.md`: state the chapter before proving it, so that the design
decisions are taken once, visibly, and the remaining work becomes countable rather than
estimated.

Writing these down has already earned its keep — three findings that a proof-first order would
have hit one at a time, halfway through:

**1. The vocabulary question is settled, and the design does not bend.** `HasCMRep` and
`HasStieltjesRep` in `Hemigroup/MemoryKernel.lean` state complete monotonicity and the Stieltjes
class as *representations*. `prop:pair-regularity`(2) is expressible with no new predicate. See
that file's docstring.

**2. Two statements here needed something the development did not have** — Laplace injectivity
for measures that are not finite, since `κ^{(x)}`, `ℓ^{(x)}` and Lebesgue measure are none of
them finite and `sonine_conservation` compares them. **Discharged 2026-08-11** as
`Hemigroup.laplaceL_injective_of_ne_top`, so ledger A6 stays off the trust boundary in its
general form too. Writing these statements is what showed it was a prerequisite rather than a
detail; the sharpening it produced — that the real hypothesis is convergence of the transform at
one point, not local finiteness — came out of trying to prove it.

**3. `lem:potential-kernel` is where a third trust-boundary entry would enter.** It asserts a
measure with a prescribed Laplace transform, which is Bernstein–Widder in its general
(locally finite) form — ledger A1. Unlike A17 and A18 this one is *not* forced yet: the function
whose transform is prescribed is `1/φ_x`, and the development might reach it through the
subordinator correspondence it already trusts. Deciding that is Phase 5 work, and the statement
below is deliberately written so either route can discharge it.
-/

namespace Skeleton

open MeasureTheory Set
open scoped ENNReal

open Hemigroup Hemigroup.SelfDecomposableExponent

variable (F : Hemigroup.SelfDecomposableExponent)

/-! ## `lem:memory-kernel` — **discharged 2026-08-11**

The derivative formula `F'(s) = b₀ + ∫₀^∞ e^{-st} k(t) dt` has moved into the library as
`Hemigroup.SelfDecomposableExponent.hasDerivAt_toRealExponent`, and its node is `\leanok`.

What it cost, against what was expected: the differentiation itself is Mathlib's, and every side
condition turned out to be free. The dominating function `e^{-(s/2)t} k(t)` is integrable because
`lem:criterion-converse` extracts both integrability facts from class membership, so no
hypothesis on `k` beyond the structure's own fields is needed. The chapter was written as though
`∫₀¹ k < ∞` were a condition to check per family; it is not.

What remains of the draft's Lemma 9.1 is its second clause, the memory kernel's transform, split
off as node 9.15 and stated below — the two clauses cost differently, and a node reporting the
maximum cost of its clauses misreports its cheap ones.
-/

/-! ## `lem:memory-kernel-transform` — **discharged 2026-08-11**

`laplace (F.memoryKernel x) s = F.symbol x s / s` has moved into the library as
`Hemigroup.SelfDecomposableExponent.laplace_memoryKernel`, and its node is `\leanok`.

The mathematical content is one substitution, `τ = t/x`. What it cost is measure-theoretic
bookkeeping: `κ^{(x)}` is the first object here that is neither finite nor a probability measure,
`laplace` is a Bochner integral, and the measure is a sum of an atom and a density — so the
integrability of the exponential has to be established separately against each piece, and the
density is only a.e. measurable because `k` is.
-/

/-! ## `lem:potential-kernel`

Existence *and* uniqueness of `ℓ^{(x)}`. Uniqueness is Laplace injectivity for locally finite
measures (see the module docstring); existence was the open question of the chapter.

**Route B chosen 2026-08-11.** Deferring it was the right order — `sonine_conservation` is stated
against an arbitrary `ℓ` meeting the specification, so the chapter's headline turned out not to
depend on this at all and is now proved interface-free. Only `prop:sonine-pair-exists` (9.12)
needs existence.

*The route not taken.* (A) is the blueprint's own proof: `1/u` is completely monotone,
`CM ∘ BF ⊆ CM` (ledger A2), and Bernstein–Widder for general measures (ledger A1) produces the
measure. Short and faithful to the text, but A1 is precisely the entry
`DESIGN-formalization-strategy.md`'s representation-first choice exists to keep off the critical
path; taking it would falsify a design claim the article makes about its own trust base.

*The route taken.* (B) constructs the measure instead of representing it, and **never mentions
complete monotonicity** — not even as a consequence. `ℓ^{(x)}` is the subordinator's potential
measure `U = ∫₀^∞ μ_t dt`, where `μ_t` is the law A17 already supplies; its transform is
`∫₀^∞ e^{-tφ_x(s)} dt = 1/φ_x(s)` by Tonelli. The trust boundary stays at two entries.

**Route B, decomposed 2026-08-11.** The main argument below is now `sorry`-free and rests on two
explicitly named sub-lemmas, which is article-kit's decomposition gate. Writing the decomposition
down before proving any of it earned its keep again, and this time the finding is in a step the
work order called routine.

1. `exists_levyTriple_symbol` — `φ_x ∈ LE` with its triple *exhibited*. A theorem to prove, not a
   hypothesis and not an axiom. Integrating `∫₀^∞ s e^{-su} h(u) du` by parts, with
   `h(u) = k(u/x)/x`, turns it into `∫₀^∞ (1 - e^{-su}) ν(du)` with `ν = -dh`, so the triple is
   drift `b₀` and Lévy measure `-dh`. The Stieltjes measure `-dh` is the real cost: `k` is only
   `AntitoneOn`, so it needs a right-continuous modification first, and Mathlib's
   `StieltjesFunction` then produces the measure. (That name is flagged in
   `PLAN-chapters-8-12.md` as a false friend for the Stieltjes *class*; for this, the other
   meaning, it is exactly the right tool.)

2. `exists_subordinatorFamily` — the laws `μ_t`, with transform `e^{-tφ_x(s)}`, **as a measurable
   family**.

3. The rest is proved below: `U := ∫₀^∞ μ_t dt` is `Measure.bind`, its transform is Tonelli plus
   `∫₀^∞ e^{-tφ} dt = 1/φ`, local finiteness is `measure_Icc_ne_top_of_laplaceL_ne_top`, and
   uniqueness is `laplaceL_injective_of_ne_top`.

**The finding: `Measurable μ` is a hypothesis with content, and the work order omitted it.**
Step 3 was written as "`U := ∫₀^∞ μ_t dt` as a measure, and Tonelli for its transform", as though
forming `U` were bookkeeping. It is not. A17 supplies `μ_t` for each `t` **by choice,
independently**, so nothing connects the choices across `t` and `∫₀^∞ μ_t dt` is not a measure at
all — `Measure.bind` will not even typecheck without `Measurable μ`. This is the same shape as the
`IsCausal ℓ` omission that writing `sonine_conservation` found: a clause that reads as a
formality and is in fact the whole reachability of the statement.

It is not an obstacle, and the route to it is worth recording because it is where the
*subordinator* structure finally gets used rather than merely named:

* `μ_{t+t'} = μ_t ∗ μ_{t'}`, from the transform and `laplace_injective`;
* hence `t ↦ μ_t (Iic r)` is **antitone** — `μ_{t+t'}(Iic r) = ∫ μ_t(Iic (r-u)) dμ_{t'}(u) ≤
  μ_t(Iic r)`, because `μ_{t'}` is causal so `u ≥ 0` a.e. — and an antitone function is
  measurable;
* `{Iic r}` is a π-system generating the Borel σ-algebra and the `μ_t` are finite, so the sets
  where `t ↦ μ_t A` is measurable form a λ-system: Dynkin gives every Borel `A`;
* `Measure.measurable_of_measurable_coe` assembles it.

So the increasing paths of the subordinator, which Route B's prose treats as intuition, are
exactly what makes the potential measure *exist*. Nothing here needs complete monotonicity, and
the trust boundary stays at two entries.
-/

/-- **Route B, step 1.** The symbol is a Lévy exponent with an exhibited triple: drift `b₀` and
Lévy measure the Stieltjes measure of the nonincreasing dilate `u ↦ k(u/x)/x`. -/
theorem exists_levyTriple_symbol (hnd : F.Nondegenerate) {x : ℝ} (hx : 0 < x) :
    ∃ ν : Measure ℝ, IsCausal ν ∧ (∀ s, 0 ≤ s → levyExponent F.b₀ ν s ≠ ⊤) ∧
      ∀ s, 0 < s → ENNReal.ofReal (F.symbol x s) = levyExponent F.b₀ ν s := by
  sorry

/-- **Route B, step 2 — proved 2026-08-11.** The subordinator's laws, as a *measurable* family.

Everything but the triple: A17 applied to the scaled triple `(t b₀, tν)` at each `t ≥ 0` (the
scaling is `levyExponent_smul`), the family extended by `δ₀` below the origin, the semigroup law
`μ_{t+t'} = μ_t ∗ μ_{t'}` from the transform and `laplace_injective`, and then the measurability
that the work order omitted: `conv_Iic_le` makes `t ↦ μ_t(Iic r)` antitone, hence measurable, and
`measurable_of_antitone_measure_Iic` lifts that to every Borel set by Dynkin. -/
theorem exists_subordinatorFamily (hnd : F.Nondegenerate) {x : ℝ} (hx : 0 < x) :
    ∃ μ : ℝ → Measure ℝ, Measurable μ ∧ (∀ t, IsProbabilityMeasure (μ t)) ∧
      (∀ t, IsCausal (μ t)) ∧
      ∀ t, 0 ≤ t → ∀ s, 0 < s →
        laplaceL (μ t) s = ENNReal.ofReal (Real.exp (-(t * F.symbol x s))) := by
  classical
  obtain ⟨ν, hνc, hνfin, hνφ⟩ := exists_levyTriple_symbol F hnd hx
  -- A17 on the scaled triple `(t b₀, t ν)`, for each `t ≥ 0`.
  have key : ∀ t : ℝ, 0 ≤ t → ∃ m : Measure ℝ, IsProbabilityMeasure m ∧ IsCausal m ∧
      ∀ s, 0 ≤ s → laplace m s = Real.exp (-(t * F.symbol x s)) := by
    intro t ht
    have hscale : ∀ s, levyExponent (t * F.b₀) (ENNReal.ofReal t • ν) s
        = ENNReal.ofReal t * levyExponent F.b₀ ν s := fun s => levyExponent_smul ν ht s
    obtain ⟨m, hprob, hcaus, htr⟩ :=
      exists_isProbabilityMeasure_laplace_eq_exp_neg_levyExponent
        (mul_nonneg ht F.b₀_nonneg) (hνc.smul _)
        (fun s hs => by
          rw [hscale s]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hνfin s hs))
    refine ⟨m, hprob, hcaus, fun s hs => ?_⟩
    rw [htr s hs, hscale s]
    congr 2
    rcases hs.eq_or_lt with rfl | hs'
    · simp [symbol]
    · rw [← hνφ s hs', ← ENNReal.ofReal_mul ht,
        ENNReal.toReal_ofReal (mul_nonneg ht (F.symbol_pos hnd hx hs').le)]
  -- Choose the family, extended by `δ₀` below the origin.
  have hfam : ∃ μ : ℝ → Measure ℝ, (∀ t, IsProbabilityMeasure (μ t)) ∧ (∀ t, IsCausal (μ t)) ∧
      (∀ t, t < 0 → μ t = Measure.dirac 0) ∧
      ∀ t, 0 ≤ t → ∀ s, 0 ≤ s → laplace (μ t) s = Real.exp (-(t * F.symbol x s)) := by
    refine ⟨fun t => if ht : 0 ≤ t then (key t ht).choose else Measure.dirac 0, ?_, ?_, ?_, ?_⟩
    · intro t
      dsimp only
      by_cases ht : 0 ≤ t
      · rw [dif_pos ht]; exact (key t ht).choose_spec.1
      · rw [dif_neg ht]; infer_instance
    · intro t
      dsimp only
      by_cases ht : 0 ≤ t
      · rw [dif_pos ht]; exact (key t ht).choose_spec.2.1
      · rw [dif_neg ht]; exact isCausal_dirac le_rfl
    · intro t ht
      dsimp only
      rw [dif_neg (not_le.mpr ht)]
    · intro t ht s hs
      dsimp only
      rw [dif_pos ht]; exact (key t ht).choose_spec.2.2 s hs
  obtain ⟨μ, hprob, hcaus, hneg, htr⟩ := hfam
  haveI : ∀ t, IsProbabilityMeasure (μ t) := hprob
  -- `μ 0 = δ₀`, and the semigroup law.
  have hzero : μ 0 = Measure.dirac 0 := by
    refine laplace_injective (hcaus 0) (isCausal_dirac le_rfl) fun s hs => ?_
    rw [htr 0 le_rfl s hs, laplace, integral_dirac]
    simp
  have hsemi : ∀ t t', 0 ≤ t → 0 ≤ t' → μ (t + t') = μ t ∗ μ t' := by
    intro t t' ht ht'
    haveI : IsFiniteMeasure (μ t ∗ μ t') := by
      haveI : IsProbabilityMeasure (μ t ∗ μ t') := inferInstance
      infer_instance
    refine laplace_injective (hcaus (t + t')) ((hcaus t).conv (hcaus t')) fun s hs => ?_
    rw [laplace_conv, htr (t + t') (by linarith) s hs, htr t ht s hs, htr t' ht' s hs,
      ← Real.exp_add]
    ring_nf
  -- Antitone cumulative distributions, hence measurability.
  have hanti : ∀ r : ℝ, Antitone fun t => μ t (Iic r) := by
    intro r t₁ t₂ h12
    dsimp only
    have hstep : ∀ a b : ℝ, 0 ≤ a → a ≤ b → μ b (Iic r) ≤ μ a (Iic r) := by
      intro a b ha hab
      have hb : μ b = μ a ∗ μ (b - a) := by
        rw [← hsemi a (b - a) ha (by linarith)]; ring_nf
      rw [hb]
      exact conv_Iic_le (hcaus _) r
    rcases lt_or_ge t₁ 0 with h1 | h1
    · rcases lt_or_ge t₂ 0 with h2 | h2
      · rw [hneg t₁ h1, hneg t₂ h2]
      · calc μ t₂ (Iic r) ≤ μ 0 (Iic r) := hstep 0 t₂ le_rfl h2
          _ = μ t₁ (Iic r) := by rw [hzero, hneg t₁ h1]
    · exact hstep t₁ t₂ h1 h12
  refine ⟨μ, measurable_of_antitone_measure_Iic hprob hanti, hprob, hcaus, fun t ht s hs => ?_⟩
  rw [← htr t ht s hs.le, laplace_eq_toReal_laplaceL,
    ENNReal.ofReal_toReal (laplaceL_ne_top_of_causal (hcaus t) hs.le)]

/-- **`lem:potential-kernel`.** The potential kernel exists and is unique.

Route B's main argument, `sorry`-free: the mixture `∫₀^∞ μ_t dt` of the subordinator's laws is
causal because every `μ_t` is, its transform is `∫₀^∞ e^{-tφ_x(s)} dt = 1/φ_x(s)` by Tonelli,
local finiteness follows from convergence of that transform at a single point, and uniqueness is
Laplace injectivity for measures that are not finite. Only the two sub-lemmas above are open. -/
theorem existsUnique_potentialKernel (hnd : F.Nondegenerate) {x : ℝ} (hx : 0 < x) :
    ∃! ℓ : Measure ℝ, IsCausal ℓ ∧ (∀ T : ℝ, ℓ (Icc 0 T) ≠ ⊤) ∧
      ∀ s : ℝ, 0 < s → laplaceL ℓ s = ENNReal.ofReal (F.symbol x s)⁻¹ := by
  obtain ⟨μ, hmeas, hprob, hcaus, htrans⟩ := exists_subordinatorFamily F hnd hx
  set ℓ := (volume.restrict (Ioi 0)).bind μ with hℓdef
  have hcausal : IsCausal ℓ := by
    have hz : ∀ t, μ t (Iio 0) = 0 := fun t => hcaus t
    rw [IsCausal, hℓdef, Measure.bind_apply measurableSet_Iio hmeas.aemeasurable]
    simp only [hz, lintegral_zero]
  have htr : ∀ s : ℝ, 0 < s → laplaceL ℓ s = ENNReal.ofReal (F.symbol x s)⁻¹ := by
    intro s hs
    have hφ : 0 < F.symbol x s := F.symbol_pos hnd hx hs
    rw [hℓdef, laplaceL, Measure.lintegral_bind hmeas.aemeasurable (by fun_prop)]
    have hcongr : ∀ t ∈ Ioi (0 : ℝ), (∫⁻ u, ENNReal.ofReal (Real.exp (-(s * u))) ∂(μ t))
        = ENNReal.ofReal (Real.exp (-(F.symbol x s * t))) := by
      intro t ht
      rw [show (∫⁻ u, ENNReal.ofReal (Real.exp (-(s * u))) ∂(μ t)) = laplaceL (μ t) s from rfl,
        htrans t (le_of_lt ht) s hs, mul_comm t (F.symbol x s)]
    rw [setLIntegral_congr_fun measurableSet_Ioi hcongr,
      show (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(F.symbol x s * t))))
        = laplaceL (volume.restrict (Ioi (0 : ℝ))) (F.symbol x s) from rfl,
      show volume.restrict (Ioi (0 : ℝ)) = volume.restrict (Ici (0 : ℝ)) from
        Measure.restrict_congr_set Ioi_ae_eq_Ici,
      laplaceL_volume_Ici hφ, one_div]
  have hfin : laplaceL ℓ 1 ≠ ⊤ := by
    rw [htr 1 zero_lt_one]; exact ENNReal.ofReal_ne_top
  refine ⟨ℓ, ⟨hcausal, fun T => measure_Icc_ne_top_of_laplaceL_ne_top hcausal zero_lt_one hfin T,
    htr⟩, ?_⟩
  rintro ρ ⟨hρcaus, -, hρtr⟩
  exact laplaceL_injective_of_ne_top hρcaus hcausal
    (by rw [hρtr 1 zero_lt_one]; exact ENNReal.ofReal_ne_top)
    fun s hs => by rw [hρtr s (by linarith), htr s (by linarith)]

/-! ## `thm:sonine-conservation` and its corollary -/

/-! ## `thm:sonine-conservation` — **discharged 2026-08-11**

Proved as `Hemigroup.SelfDecomposableExponent.sonine_conservation`, with all three of the
hypotheses below added. The note is kept because the record of what the statement was missing is
worth more than the statement was.

`κ^{(x)} ∗ ℓ^{(x)} = Leb` on `[0,∞)`.

Stated against an arbitrary `ℓ` satisfying the potential-kernel specification rather than
against a chosen one, so that it does not depend on how `existsUnique_potentialKernel` is
discharged.

**`IsCausal ℓ` added 2026-08-11**, and it is not a formality. Without it the statement is not
reachable by the only available route and is very likely false: the proof compares transforms
and concludes with `laplaceL_injective_of_ne_top`, which needs both measures carried by
`[0,∞)`, and `IsCausal (μ ∗ ν)` needs it of both factors too. The specification as first written
pinned `ℓ` only through its transform on `(0,∞)`, which does not confine a measure to the
half-line. `lem:potential-kernel` asserts causality of `ℓ^{(x)}` and always did — the omission
was in this statement, not in the mathematics, and writing the proof is what found it.

**Two further gaps, found the same way.**

*The specification must be stated in `laplaceL`, not `laplace`* — fixed above. `laplace` is a
Bochner integral and is `0` by convention when the integrand is not integrable, so
`laplace ℓ s = (φ_x s)⁻¹` does **not** give `laplaceL ℓ s = ofReal (φ_x s)⁻¹`: the transform
could be `⊤` while the Bochner integral reads `0`. Since the proof multiplies transforms
(`laplaceL_conv`), the `ℝ≥0∞` reading is the one that has to appear. This is the same reason
`levyExponent` is `ℝ≥0∞`-valued throughout — the development made this choice once already, and
the skeleton statement quietly departed from it.

*Nondegeneracy was missing; `hnd : F.Nondegenerate` added.* The proof needs `φ_x s > 0`, without
which
`ofReal (φ_x s) * ofReal (φ_x s)⁻¹ ≠ 1`. And `φ_x s = s F'(xs)` genuinely can vanish: with
`b₀ = 0` and `k ≡ 0` we get `F ≡ 0`, `κ^{(x)} = 0`, and the identity is **false**, not merely
unprovable. So this needs the hypothesis the article carries everywhere and this statement
dropped. It is `Hemigroup.SelfDecomposableExponent.Nondegenerate`, and `symbol_pos` is the
consequence the proofs consume. The blueprint's `thm:sonine-conservation` inherits it by taking
`(Φ_{x,y})` from `thm:main-characterization`, which is where it hides; a standalone Lean
statement has to say it, and adding it is the next step here.
-/

/-- **`prop:sonine-pair-exists`**, the node split out in Phase 0: at the level of measures the
pair is unconditional. A collation of the three results above, and the reason it is worth
stating separately is that it needs no ledger entry, where the regularity clauses do. -/
theorem exists_sonine_pair (hnd : F.Nondegenerate) {x : ℝ} (hx : 0 < x) :
    ∃ ℓ : Measure ℝ, IsCausal ℓ ∧ (∀ T : ℝ, ℓ (Icc 0 T) ≠ ⊤) ∧
      ∃ _ : SFinite ℓ, (F.memoryKernel x ∗ ℓ).restrict (Ici 0) = volume.restrict (Ici 0) := by
  sorry

/-! ## `prop:pair-regularity`(2), the Phase 1 decision made concrete

The statement that forced the vocabulary question. Note that no predicate `CompletelyMonotone`
appears: `HasCMRep` and `HasStieltjesRep` are representations, and the equivalence below is
therefore statable in the development's existing idiom.

Crossing to the blueprint's derivative-sign reading of the same classes costs ledger **A1**,
once, in the statement — never inside a proof. That is the discipline `prop:bernstein-toolbox`(3)
already documents for `BF₀` against `LE`.
-/

/-- **`prop:pair-regularity`(2).** `κ^{(x)}` has a completely monotone density iff `k` does,
iff `F'` is Stieltjes. -/
theorem hasCMDensity_iff {x : ℝ} (hx : 0 < x) :
    (HasCMDensity (F.memoryKernel x) ↔ HasCMRep F.k) ∧
      (HasCMRep F.k ↔ HasStieltjesRep (deriv F.toRealExponent)) := by
  sorry

end Skeleton
