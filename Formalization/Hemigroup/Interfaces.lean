/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.Levy

/-!
# The analytic interfaces

**Every `axiom` in this development lives in this file.** `blueprint/trust-boundary.txt` names
them, `blueprint/AXIOMS.md` reviews them against a page anchor, and `linkage axioms --check`
holds the two together. Nothing else in `Hemigroup/` may declare an axiom.

## Why these are stated in the development's own vocabulary

Each interface below is phrased in terms this development already defines — `levyExponent`,
`laplace`, `IsCausal` — and *not* in the classical vocabulary of the blueprint node it stands
for. That is deliberate, and it is the reason the file exists separately.

The blueprint reaches the existence of the kernel measures through complete monotonicity:
`prop:bernstein-toolbox`(2) makes `e^{-g}` completely monotone, then (1) — Bernstein–Widder —
turns a completely monotone function into a measure. Taking *that* route in Lean would mean
defining `CompletelyMonotone`, which is precisely the derivative-sign vocabulary
`blueprint/DESIGN-formalization-strategy.md` exists to keep out of the development.

Representation-first, the function whose measure we want is never anonymous: `lem:vanishing`'s
and `lem:selfdecomposable-exponents`' Lean forms hand over the Lévy triple explicitly (see
`SelfDecomposable.levyExponentD_increment`). So the interface needed is not a representation
theorem but a *construction* — from a triple, a measure — and it can be stated without the
classical predicates.

The practical consequence: an interface phrased this way can later be **demoted to a lemma
without touching a single downstream statement**. If the compound-Poisson construction is ever
carried out — explicit `e^{-‖ν‖} Σ ν^{*n}/n!`, truncate `ν` to `(ε,∞)`, pass to the weak limit
with Prokhorov, which Mathlib has — the `axiom` below becomes a `theorem` and the trust boundary
returns to empty, silently. An interface phrased in terms of `CompletelyMonotone` could not be
retired that way, because the predicate would be woven through everything that mentions it.
-/

namespace Hemigroup

open MeasureTheory Set
open scoped ENNReal

/-- **The subordinator correspondence** — the existence half, ledger A17.

Given a drift `b₀ ≥ 0` and a causal Lévy measure `ν` whose exponent is finite, there is a causal
**finite** measure whose Laplace transform is `exp (-(b₀ s + ∫ (1 - e^{-st}) ν(dt)))`.

This is what `thm:main-characterization` (⇐) needs in order to build the kernels `μ_{x,y}` from
`F`, and it is the *only* thing it needs that is not proved here. It is strictly weaker than
Bernstein–Widder: the triple is given, so no representation theorem is involved — only the
construction of an infinitely divisible law from its triple.

**Finite, not probability — deliberately.** Schilling–Song–Vondraček Theorem 5.2 delivers a
convolution semigroup of *sub*-probability measures, and that is all this axiom claims. The
upgrade to a probability measure has no numbered statement in the source; it is a line of the
proof and a sentence of prose on p. 51. It does not need to be trusted, because our
`levyExponent` carries no killing term by construction (`levyExponent_zero`), so the mass falls
out of the transform at `s = 0`. That derivation is
`exists_isProbabilityMeasure_laplace_eq_exp_neg_levyExponent` below, and it is `[T]`.

Uniqueness is likewise **not** part of this interface. It follows from injectivity of the
Laplace transform, which is `prop:laplace-uniqueness` on paper and is intended to become a
proved lemma here (the M0 remainder), not a second axiom.

The finiteness hypothesis is stated as finiteness of the exponent rather than as the source's
`∫ (1 ∧ t) ν(dt) < ∞`. The two are equivalent for causal `ν`: concavity of `t ↦ 1 - e^{-st}`
gives `1 - e^{-st} ≥ (1 - e^{-s}) min (1, t)` for `t ≥ 0`, so finiteness at a single `s > 0`
already forces the integral condition. The axiom is therefore no stronger than the theorem it
is anchored on. -/
axiom exists_isFiniteMeasure_laplace_eq_exp_neg_levyExponent {b₀ : ℝ} (hb₀ : 0 ≤ b₀)
    {ν : Measure ℝ} (hν : IsCausal ν) (hfin : ∀ s, 0 ≤ s → levyExponent b₀ ν s ≠ ⊤) :
    ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧ IsCausal μ ∧
      ∀ s, 0 ≤ s → laplace μ s = Real.exp (-(levyExponent b₀ ν s).toReal)

/-- The measure supplied by A17 is a **probability** measure.

This is the step the source states only as prose (SSV p. 51: `a = f(0+) > 0` iff
`μ_t[0,∞) < 1`). It is not taken on trust: `levyExponent` has no killing term, so
`levyExponent b₀ ν 0 = 0`, and evaluating the transform at `s = 0` — where it is the total mass
— gives `exp 0 = 1` directly. -/
theorem exists_isProbabilityMeasure_laplace_eq_exp_neg_levyExponent {b₀ : ℝ} (hb₀ : 0 ≤ b₀)
    {ν : Measure ℝ} (hν : IsCausal ν) (hfin : ∀ s, 0 ≤ s → levyExponent b₀ ν s ≠ ⊤) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ IsCausal μ ∧
      ∀ s, 0 ≤ s → laplace μ s = Real.exp (-(levyExponent b₀ ν s).toReal) := by
  obtain ⟨μ, hfinite, hcausal, htrans⟩ :=
    exists_isFiniteMeasure_laplace_eq_exp_neg_levyExponent hb₀ hν hfin
  refine ⟨μ, ⟨?_⟩, hcausal, htrans⟩
  -- At `s = 0` the transform is the total mass, and the exponent vanishes.
  have h0 := htrans 0 le_rfl
  rw [levyExponent_zero, ENNReal.toReal_zero, neg_zero, Real.exp_zero,
    laplace_eq_toReal_laplaceL, laplaceL_zero] at h0
  exact (ENNReal.toReal_eq_one_iff _).mp h0

end Hemigroup
