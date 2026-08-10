/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.Construction
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Chapter 9's objects: the memory kernel, and complete monotonicity without the predicate

Blueprint: `blueprint/src/parts/09-memory-kernels.tex`.

Definitions only. The statements about them are stated-but-unproved in
`Formalization/Skeleton/Chapter9.lean` until they are proved; nothing here carries a proof
obligation, which is why it belongs in the library rather than in the skeleton.

(The word the skeleton library is marked with is deliberately not written in this file: CI's
guard scans `Formalization/Hemigroup` for it as plain text, so a docstring mentioning it would
fail the build as surely as a real one.)

## The vocabulary decision, made concrete

`blueprint/PLAN-chapters-8-12.md` Phase 1 asks whether chapter 9 forces the development to define
`CompletelyMonotone`, reversing `DESIGN-formalization-strategy.md`. It does not, and this file is
where that is settled rather than asserted.

`prop:pair-regularity`(2) says: *`κ` has a completely monotone density iff `k` is completely
monotone iff `F'` lies in the Stieltjes class.* Both classes are named there by derivative signs,
but both are *equivalently* named by a representation — and the blueprint already writes the
Stieltjes one that way. So:

* `HasCMRep k` — `k(t) = ∫ e^{-τt} σ(dτ)` for a causal `σ`. By Bernstein–Widder this is complete
  monotonicity, but it is stated as what it is: a representation.
* `HasStieltjesRep h` — `h(s) = a/s + b + ∫ (s+τ)^{-1} σ(dτ)`, which is the blueprint's own
  display of the class `S`.

This is the same move that made `BF₀` into `LE` for chapters 5–7, and it has the same
consequence: crossing between the two readings costs ledger A1, once, in a *statement* — never
inside a proof. A node whose conclusion is stated with a representation carries a Lean tag for
free; one stated by derivative signs cannot carry one at all.

The Mathlib survey of 2026-08-11 makes this forced rather than merely preferred: Mathlib has no
completely monotone, Bernstein or Stieltjes machinery of any kind, and no Bernstein–Widder. (It
does have `MeasureTheory.Measure.Stieltjes.StieltjesFunction` — a monotone right-continuous
function used to *build* a measure, entirely unrelated to the class `S`. Do not be misled by the
name.)
-/

namespace Hemigroup

open MeasureTheory Set
open scoped ENNReal

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent)

/-! ## The exponent as a real-valued function

`exponent` is `ℝ≥0∞`-valued so that no integrability hypothesis is needed anywhere. Chapter 9
differentiates it, so it needs a real-valued reading; `ne_top` is exactly what makes the two
agree on `[0,∞)`.
-/

/-- `F(s)`, as a real number. -/
noncomputable def toRealExponent (s : ℝ) : ℝ := (F.exponent s).toReal

/-! ## The memory kernel and the potential kernel -/

/-- **`κ^{(x)}`**, the memory kernel of the scale flow: the drift atom together with the Lévy
density dilated to scale `x` with `L¹` normalisation.

The blueprint writes it `b₀ δ₀(dt) + (1/x) k(t/x) dt`. -/
noncomputable def memoryKernel (x : ℝ) : Measure ℝ :=
  ENNReal.ofReal F.b₀ • Measure.dirac 0
    + (volume.restrict (Ioi 0)).withDensity fun t => ENNReal.ofReal (F.k (t / x) / x)

/-- **`φ_x(s) = s F'(xs)`**, the per-scale symbol. Its reciprocal is the transform of the
potential kernel. -/
noncomputable def symbol (x s : ℝ) : ℝ := s * deriv F.toRealExponent (x * s)

/-! ## Complete monotonicity and the Stieltjes class, as representations

Neither predicate is defined by derivative signs; see the module docstring.
-/

/-- **`k` is completely monotone**, stated as the representation Bernstein–Widder gives it:
`k(t) = ∫ e^{-τt} σ(dτ)` for a positive measure `σ` on `[0,∞)`. -/
def HasCMRep (k : ℝ → ℝ) : Prop :=
  ∃ σ : Measure ℝ, IsCausal σ ∧ ∀ t : ℝ, 0 < t → k t = ∫ τ, Real.exp (-(τ * t)) ∂σ

/-- **`h` lies in the Stieltjes class `S`**, in the form the blueprint displays it:
`h(s) = a/s + b + ∫ (s+τ)^{-1} σ(dτ)`. -/
def HasStieltjesRep (h : ℝ → ℝ) : Prop :=
  ∃ (a b : ℝ) (σ : Measure ℝ), 0 ≤ a ∧ 0 ≤ b ∧ IsCausal σ ∧
    ∀ s : ℝ, 0 < s → h s = a / s + b + ∫ τ, (s + τ)⁻¹ ∂σ

/-- **A measure has a completely monotone density on `(0,∞)`.** The form
`prop:pair-regularity` asks about, drift atom excluded — which is what its opening clause
about the atoms `b₀δ₀` is there to say. -/
def HasCMDensity (μ : Measure ℝ) : Prop :=
  ∃ m : ℝ → ℝ, HasCMRep m ∧
    μ.restrict (Ioi 0) = (volume.restrict (Ioi 0)).withDensity fun t => ENNReal.ofReal (m t)

end SelfDecomposableExponent

end Hemigroup
