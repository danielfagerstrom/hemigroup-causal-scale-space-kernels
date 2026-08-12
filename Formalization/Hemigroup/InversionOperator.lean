/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.InversionSymbol
import Hemigroup.MellinVertical

/-!
# The inversion operator

Blueprint: `def:inversion-operator` (Definition 11.3), ledger **A12**.

The operator is
`(A g)(x) = x⁻¹ · (2πi)⁻¹ ∫_{(c)} x^{-z} B(-z) g̃(z) dz`, and the blueprint's second reading of it
is the functional calculus `x ↦ x⁻¹ (B(θ)g)(x)`, `θ` the Euler operator. What ledger A12 carries
is exactly the step from the first reading to the second: that absolute convergence on the line is
enough for the contour integral to compute `B(θ)g`.

## What had to be exhibited

Mathlib's `mellinInv_mellin_eq` recovers a function from *its own* transform; it says nothing
about the integral of a product. So the second reading has to be given a referent: `B(θ)g` names a
function, and what makes the display a definition of an *operator* is that the function exists.
`RealisesSymbolAction` is that hypothesis — `h` realises the symbol's action on `g` at height `c`
— and `inversionOperator_eq` is then Mathlib's theorem applied to `h`.

This is a stronger hypothesis than absolute integrability of `B(-z)g̃(z)`, and deliberately so.
Every use the article makes of `A` exhibits `h` explicitly; the eigenfunction relation of
Theorem 4′ is the case `g = H(s·)`, `h = s x H(sx)`, where the identity `h̃(z) = s^{-z}H̃(z+1)` is
the recursion `B(-z) = H̃(z+1)/H̃(z)` with the denominators cleared.

## The identity on the line is almost-everywhere, and cannot be more

`B` is a quotient with poles at the zeros of `H̃`. Where `H̃` vanishes, Lean's `x / 0 = 0` makes
`B(-z) g̃(z)` vanish too, while `h̃(z)` need not: at such a point the product identity fails for a
reason about notation rather than about the operator. Those points are isolated
(`eventually_mellin_profile_ne_zero`), so they meet the line in a null set and the inversion
integral does not see them — but a pointwise reading of the blueprint's display would be false as
stated, so `RealisesSymbolAction.mellin_eq` is an `∀ᵐ`.

That is why `mellin_inversionOperator` concludes `Ãg(z) = h̃(z-1)` rather than the display
`B(1-z)g̃(z-1)`: the two agree at every point where the product identity holds pointwise, which is
`mellin_inversionOperator_eq`. The same question — which equality does "equal on the strip" mean —
was answered the same way in `SymbolUniqueness.lean`, and both times writing the statement is what
raised it.

## The shift costs nothing

`mellin (A g) z = mellin h (z - 1)` holds at *every* `z`, with no strip condition: once
`A g = x⁻¹ h` is known on `(0,∞)`, the rest is `mellin_cpow_smul` at exponent `-1`. The strip
enters only in identifying `h̃(z-1)` with the product, i.e. in the hypothesis of
`RealisesSymbolAction`.
-/

namespace Hemigroup

open MeasureTheory Set Filter

open scoped Topology

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent)

/-- **`def:inversion-operator`.** The inversion operator at height `c`,
`(A g)(x) = x⁻¹ (2πi)⁻¹ ∫_{(c)} x^{-z} B(-z) g̃(z) dz`.

Mathlib's `mellinInv` *is* the contour integral of the blueprint: parametrising the line by
`z = c + iy` turns `dz` into `i dy`, which cancels the `i`, leaving `(2π)⁻¹ ∫ x^{-z} … dy`. The
symbol appears as `F.inversionSymbol z` and not as `B (-z)` because `inversionSymbol` is already
indexed by the Mellin variable of the Euler operator; see its docstring.

`A g` is total in `g`: `mellinInv` is an ordinary integral, so restricting the definition to an
admissible class would put a proof obligation in every downstream statement to no purpose. What
the blueprint writes as a restriction on the domain of `A` is here a hypothesis of the theorems
that compute it. -/
noncomputable def inversionOperator (c : ℝ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  x⁻¹ * mellinInv c (fun z => F.inversionSymbol z * mellin g z) x

/-- `h` **realises the symbol's action** on `g` at height `c`: it is the function that the
functional-calculus reading of `def:inversion-operator` calls `B(θ)g`.

The first field is almost-everywhere equality on the line, not pointwise — see the module
docstring. The last two are verbatim the hypotheses of Mathlib's `mellinInv_mellin_eq`, and for
the profiles the second of them is `lem:mellin-vertical`. -/
structure RealisesSymbolAction (c : ℝ) (g h : ℝ → ℂ) : Prop where
  /-- The transform of `h` is the product `B(-z) g̃(z)` almost everywhere on the line. -/
  mellin_eq : ∀ᵐ y : ℝ, mellin h (c + y * Complex.I)
    = F.inversionSymbol (c + y * Complex.I) * mellin g (c + y * Complex.I)
  /-- The forward Mellin integral of `h` converges on the line. -/
  convergent : MellinConvergent h c
  /-- The inversion integral converges absolutely on the line — the hypothesis
  `def:inversion-operator` imposes, and the one `lem:mellin-vertical` supplies for profiles. -/
  verticalIntegrable : Complex.VerticalIntegrable (mellin h) c

/-- **`def:inversion-operator`**, the functional-calculus reading: where the symbol's action on `g`
is realised by `h`, the contour integral computes `x⁻¹ h x`.

This is the step ledger A12 carries, and it is Mathlib's `mellinInv_mellin_eq` once the integrand
has been recognised as `mellin h`. Recognising it is the whole of the proof, and the null set
where the recognition fails is discarded by `integral_congr_ae` — which is available precisely
because `mellinInv` integrates over the line rather than evaluating on it. -/
theorem inversionOperator_eq {c : ℝ} {g h : ℝ → ℂ} (hrep : F.RealisesSymbolAction c g h) {x : ℝ}
    (hx : 0 < x) (hcont : ContinuousAt h x) :
    F.inversionOperator c g x = x⁻¹ * h x := by
  have hint : mellinInv c (fun z => F.inversionSymbol z * mellin g z) x
      = mellinInv c (mellin h) x := by
    rw [mellinInv, mellinInv]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hrep.mellin_eq] with y hy
    rw [hy]
  rw [inversionOperator, hint,
    mellinInv_mellin_eq c h hx hrep.convergent hrep.verticalIntegrable hcont]

/-- **`def:inversion-operator`**, the transform-level identity, against the realising function:
`Ãg(z) = h̃(z-1)`.

No strip condition. Once the pointwise formula is known on `(0,∞)`, the weight `x⁻¹` is
`mellin_cpow_smul` at exponent `-1`, which shifts the argument and is available at every `z`. -/
theorem mellin_inversionOperator {c : ℝ} {g h : ℝ → ℂ} (hrep : F.RealisesSymbolAction c g h)
    (hcont : ContinuousOn h (Ioi 0)) (z : ℂ) :
    mellin (F.inversionOperator c g) z = mellin h (z - 1) := by
  have hpt : ∀ t ∈ Ioi (0 : ℝ),
      F.inversionOperator c g t = (t : ℂ) ^ (-1 : ℂ) • h t := by
    intro t ht
    rw [F.inversionOperator_eq hrep (mem_Ioi.mp ht)
      (hcont.continuousAt (isOpen_Ioi.mem_nhds ht)), Complex.cpow_neg_one]
    simp
  calc mellin (F.inversionOperator c g) z
      = mellin (fun t => (t : ℂ) ^ (-1 : ℂ) • h t) z := by
        rw [mellin, mellin]
        exact setIntegral_congr_fun measurableSet_Ioi fun t ht => by rw [hpt t ht]
    _ = mellin h (z + -1) := mellin_cpow_smul h z (-1)
    _ = mellin h (z - 1) := by rw [← sub_eq_add_neg]

/-- **`def:inversion-operator`**, the blueprint's display `Ãg(z) = B(1-z) g̃(z-1)`, at any point
where the product identity holds pointwise — which, by `lem:inversion-symbol`, is every point of
the strip off the isolated zeros of `H̃`. -/
theorem mellin_inversionOperator_eq {c : ℝ} {g h : ℝ → ℂ} (hrep : F.RealisesSymbolAction c g h)
    (hcont : ContinuousOn h (Ioi 0)) {z : ℂ}
    (hz : mellin h (z - 1) = F.inversionSymbol (z - 1) * mellin g (z - 1)) :
    mellin (F.inversionOperator c g) z = F.inversionSymbol (z - 1) * mellin g (z - 1) := by
  rw [F.mellin_inversionOperator hrep hcont z, hz]

end SelfDecomposableExponent

end Hemigroup
