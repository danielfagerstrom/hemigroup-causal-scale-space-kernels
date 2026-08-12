/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# The Mellin symbol of the Euler operator

Blueprint: the analytic engine of `lem:local-polynomial-symbol` (12.2).

The chapter's whole (⇐) direction rests on one identity, and Mathlib has no part of it:
`MellinTransform.lean` and `MellinInversion.lean` between them prove nothing relating the Mellin
transform to a derivative. What is proved here is

  `M[x ↦ xʲ g⁽ʲ⁾(x)](z) = (∏_{i<j} (-z-i)) · M[g](z)`

for `g` smooth and compactly supported **inside** `(0,∞)` --- that is, `θ = x∂ₓ` has Mellin symbol
`-z`, applied `j` times.

## Where the hypotheses are spent

`tsupport g ⊆ Ioi 0` is not a convenience. Mathlib's integration by parts on the whole line,
`MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable`, asks for the differentiability of
each factor only on the *support of the other*, which is exactly what makes this route work: the
weight `x ↦ xʷ` is differentiable away from the origin and nowhere near it, and `tsupport g ⊆
Ioi 0` is precisely the statement that the origin is not in the region where its derivative is
needed. Compact support alone would leave the boundary term at `0`, where the weight is singular,
and the identity would be false as stated.

The other place the hypothesis is spent is integrability: `x ↦ xʷ g(x)` is continuous *because* `g`
vanishes on a neighbourhood of the origin, so the singular weight never meets a nonzero value.

## The induction

Peeling one derivative at a time, and moving the shift into the exponent rather than into the
function, gives a clean recursion:

  `∫ x^{z-1+(j+1)} g^{(j+1)} = ∫ x^{(z+1)-1+j} (g')^{(j)}`

which is the induction hypothesis at `z+1` for `g'`, followed by one integration by parts. The
constant then satisfies `E_{j+1}(z) = -z · E_j(z+1)`, which is `Finset.prod_range_succ'` --- the
version that peels the *first* factor, not the last.
-/

namespace Hemigroup

open MeasureTheory Set Filter
open scoped Topology

/-! ## The test class -/

/-- The test class of `def:locality-pmp`: smooth, compactly supported, and supported **inside**
`(0,∞)`. The last clause is what makes the integrations by parts below have no boundary term. -/
structure IsTestFunction (g : ℝ → ℂ) : Prop where
  /-- Smooth on all of `ℝ`. -/
  contDiff : ContDiff ℝ (⊤ : ℕ∞) g
  /-- Compactly supported. -/
  hasCompactSupport : HasCompactSupport g
  /-- Supported away from the origin, which is what makes the boundary terms vanish. -/
  tsupport_subset : tsupport g ⊆ Ioi (0 : ℝ)

namespace IsTestFunction

variable {g : ℝ → ℂ}

/-- A test function vanishes at and below the origin. -/
theorem eq_zero_of_nonpos (hg : IsTestFunction g) {x : ℝ} (hx : x ≤ 0) : g x = 0 := by
  refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
  exact absurd (hg.tsupport_subset hmem) (by simpa using hx)

/-- The derivative of a test function is a test function: this is what lets the identity below be
proved by induction rather than by a single `j`-fold argument. -/
theorem deriv (hg : IsTestFunction g) : IsTestFunction (_root_.deriv g) where
  contDiff := by
    have h : ContDiff ℝ ((⊤ : ℕ∞) + 1) g := by simpa using hg.contDiff
    simpa using h.deriv'
  hasCompactSupport := hg.hasCompactSupport.deriv
  tsupport_subset := tsupport_deriv_subset.trans hg.tsupport_subset

/-- Every iterated derivative is again a test function. -/
theorem iteratedDeriv (hg : IsTestFunction g) (j : ℕ) :
    IsTestFunction (_root_.iteratedDeriv j g) := by
  induction j generalizing g with
  | zero => simpa [iteratedDeriv_zero] using hg
  | succ k ih =>
      have := ih hg.deriv
      simpa [iteratedDeriv_succ'] using this

end IsTestFunction

/-! ## The weight -/

/-- `x ↦ xʷ` is differentiable away from the origin, at every complex exponent.

Mathlib's `hasDerivAt_ofReal_cpow_const` excludes `w = 0`; there the function is constant `1` and
the stated derivative `0 · x⁻¹` is `0`, so the formula holds anyway and is worth having uniformly:
the induction below runs over all `w` and a side condition at one of them would propagate. -/
theorem hasDerivAt_ofReal_cpow {x : ℝ} (hx : x ≠ 0) (w : ℂ) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ w) (w * (x : ℂ) ^ (w - 1)) x := by
  rcases eq_or_ne w 0 with rfl | hw
  · simpa using hasDerivAt_const x (1 : ℂ)
  · exact hasDerivAt_ofReal_cpow_const hx hw

/-- The weighted test function is continuous: away from the origin because both factors are, and
at the origin because `g` vanishes on a neighbourhood of it. -/
theorem continuous_cpow_mul_of_isTestFunction {g : ℝ → ℂ} (hg : IsTestFunction g) (w : ℂ) :
    Continuous fun x : ℝ => (x : ℂ) ^ w * g x := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  rcases eq_or_ne x 0 with rfl | hx
  · -- `g` vanishes on `Iio 0`'s neighbourhood side too, so the product is locally `0`
    have hzero : (fun y : ℝ => (y : ℂ) ^ w * g y) =ᶠ[𝓝 (0 : ℝ)] fun _ => (0 : ℂ) := by
      have hopen : IsOpen (tsupport g)ᶜ := (isClosed_tsupport g).isOpen_compl
      have hmem : (0 : ℝ) ∈ (tsupport g)ᶜ := fun h => by simpa using hg.tsupport_subset h
      filter_upwards [hopen.mem_nhds hmem] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]
    exact continuousAt_const.congr hzero.symm
  · have h₁ : ContinuousAt (fun y : ℝ => (y : ℂ) ^ w) x :=
      (hasDerivAt_ofReal_cpow hx w).continuousAt
    exact h₁.mul (hg.contDiff.continuous.continuousAt)

/-- …and compactly supported, hence integrable. -/
theorem integrable_cpow_mul_of_isTestFunction {g : ℝ → ℂ} (hg : IsTestFunction g) (w : ℂ) :
    Integrable fun x : ℝ => (x : ℂ) ^ w * g x := by
  refine (continuous_cpow_mul_of_isTestFunction hg w).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro hg.hasCompactSupport.isCompact fun x hx => ?_
  rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

/-! ## Integration by parts -/

/-- **One integration by parts against the weight `xʷ`.**

The boundary terms vanish because `g` is compactly supported inside `(0,∞)`; Mathlib's
whole-line statement asks for differentiability of each factor only on the other's support, which
is exactly the shape in which the origin never has to be differentiated at. -/
theorem integral_cpow_mul_deriv {g : ℝ → ℂ} (hg : IsTestFunction g) (w : ℂ) :
    ∫ x : ℝ, (x : ℂ) ^ w * deriv g x = -w * ∫ x : ℝ, (x : ℂ) ^ (w - 1) * g x := by
  have hu : ∀ x ∈ tsupport g, HasDerivAt (fun y : ℝ => (y : ℂ) ^ w)
      ((fun y : ℝ => w * (y : ℂ) ^ (w - 1)) x) x := by
    intro x hx
    exact hasDerivAt_ofReal_cpow (ne_of_gt (hg.tsupport_subset hx)) w
  have hv : ∀ x ∈ tsupport (fun y : ℝ => (y : ℂ) ^ w), HasDerivAt g (deriv g x) x := by
    intro x _
    exact (hg.contDiff.differentiable (by simp)).differentiableAt.hasDerivAt
  have h₁ : Integrable fun x : ℝ => (x : ℂ) ^ w * deriv g x :=
    integrable_cpow_mul_of_isTestFunction hg.deriv w
  have h₂ : Integrable fun x : ℝ => w * (x : ℂ) ^ (w - 1) * g x := by
    have := (integrable_cpow_mul_of_isTestFunction hg (w - 1)).const_mul w
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    ring
  have h₃ : Integrable fun x : ℝ => (x : ℂ) ^ w * g x :=
    integrable_cpow_mul_of_isTestFunction hg w
  have key := MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun y : ℝ => (y : ℂ) ^ w) (u' := fun y : ℝ => w * (y : ℂ) ^ (w - 1))
    (v := g) (v' := deriv g) hu hv h₁ h₂ h₃
  rw [key, neg_mul, ← integral_const_mul]
  congr 1
  simp [mul_assoc]

/-! ## The symbol -/

/-- The Mellin symbol of the `j`-th Euler factor: `θ(θ-1)⋯(θ-j+1)` has symbol
`(-z)(-z-1)⋯(-z-j+1)`, because `θ = x∂ₓ` has symbol `-z`.

Isolated rather than inlined because the sign convention is where this chapter's bookkeeping
errors would live: `SelfDecomposableExponent.inversionSymbol z` is the blueprint's `B(-z)`. -/
noncomputable def mellinEulerFactor (j : ℕ) (z : ℂ) : ℂ := ∏ i ∈ Finset.range j, (-z - (i : ℂ))

@[simp] theorem mellinEulerFactor_zero (z : ℂ) : mellinEulerFactor 0 z = 1 := by
  simp [mellinEulerFactor]

/-- The recursion the induction runs on: peel the *first* factor, not the last. -/
theorem mellinEulerFactor_succ (j : ℕ) (z : ℂ) :
    mellinEulerFactor (j + 1) z = -z * mellinEulerFactor j (z + 1) := by
  rw [mellinEulerFactor, Finset.prod_range_succ', mellinEulerFactor]
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_zero]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  ring

/-- **The engine, in integral form.** `j` integrations by parts, the shift living in the exponent
rather than in the function. -/
theorem integral_cpow_mul_iteratedDeriv {g : ℝ → ℂ} (hg : IsTestFunction g) (j : ℕ) (z : ℂ) :
    ∫ x : ℝ, (x : ℂ) ^ (z - 1 + j) * iteratedDeriv j g x
      = mellinEulerFactor j z * ∫ x : ℝ, (x : ℂ) ^ (z - 1) * g x := by
  induction j generalizing g z with
  | zero => simp [iteratedDeriv_zero]
  | succ k ih =>
      have hstep : ∫ x : ℝ, (x : ℂ) ^ (z - 1 + (k + 1 : ℕ)) * iteratedDeriv (k + 1) g x
          = ∫ x : ℝ, (x : ℂ) ^ ((z + 1) - 1 + k) * iteratedDeriv k (deriv g) x := by
        rw [iteratedDeriv_succ']
        congr 1
        funext x
        push_cast
        ring_nf
      rw [hstep, ih hg.deriv (z + 1), mellinEulerFactor_succ]
      have : ∫ x : ℝ, (x : ℂ) ^ ((z + 1) - 1) * deriv g x
          = -z * ∫ x : ℝ, (x : ℂ) ^ (z - 1) * g x := by
        have h := integral_cpow_mul_deriv hg z
        simpa using h
      rw [this]
      ring

/-- **`lem:local-polynomial-symbol`'s engine.** The Mellin transform turns the Euler operator into
multiplication by its symbol. -/
theorem mellin_pow_mul_iteratedDeriv {g : ℝ → ℂ} (hg : IsTestFunction g) (j : ℕ) (z : ℂ) :
    mellin (fun x => (x : ℂ) ^ j * iteratedDeriv j g x) z
      = mellinEulerFactor j z * mellin g z := by
  have hIoi : ∀ (h : ℝ → ℂ), IsTestFunction h → ∀ w : ℂ,
      ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ w * h x = ∫ x : ℝ, (x : ℂ) ^ w * h x := by
    intro h hh w
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    rw [hh.eq_zero_of_nonpos (not_lt.mp hx), mul_zero]
  have hleft : mellin (fun x => (x : ℂ) ^ j * iteratedDeriv j g x) z
      = ∫ x : ℝ, (x : ℂ) ^ (z - 1 + j) * iteratedDeriv j g x := by
    rw [mellin]
    rw [← hIoi (fun x => iteratedDeriv j g x) (hg.iteratedDeriv j) (z - 1 + j)]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (0 : ℝ) < x := hx
    have hxne : (x : ℂ) ≠ 0 := by
      simpa using ne_of_gt hx0
    rw [smul_eq_mul, ← mul_assoc]
    congr 1
    rw [Complex.cpow_add _ _ hxne, Complex.cpow_natCast]
  rw [hleft, integral_cpow_mul_iteratedDeriv hg j z, mellin]
  congr 1
  rw [← hIoi g hg (z - 1)]
  exact (setIntegral_congr_fun measurableSet_Ioi fun x _ => by rw [smul_eq_mul]).symm

end Hemigroup
