/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.MellinVertical
import Hemigroup.InversionSymbol

/-!
# The target types of chapter 11

`thm:signaling-form` is Theorem 4′, and by the author's account the formulation the article exists
for. This file holds chapter 11's target types while they are being proved; a declaration moves
into `Hemigroup/` when it is proved, and its node goes `\leanok`.

## What has already moved

| node | declaration | file (under `Hemigroup/`) |
|---|---|---|
| `lem:mellin-data` (11.2) | `mellin_profile`, `norm_mellin_profile_le` | `MellinData.lean` |
| `lem:inversion-symbol` (11.14) | `meromorphicOn_inversionSymbol` + 5 | `InversionSymbol.lean` |
| `lem:symbol-rigidity` (11.15) | `SameSymbolAction.eventuallyEq` | `SymbolUniqueness.lean` |
| `lem:mellin-vertical` (11.13) | `verticalIntegrable_mellin_profile` | `MellinVertical.lean` |

All of it reduces to ledger **A17** and nothing else.

`lem:mellin-vertical` is the one worth reading about: it was recorded, twice, as blocked on
Mathlib, because the bound of `lem:mellin-data` reduces vertical integrability to the decay of
`|Γ(c+iτ)|` and Mathlib has no such estimate. That was true about Mathlib and false about the
obligation — the classical asymptotic needs Stirling in the complex plane, but *integrability
needs only quadratic decay*, and quadratic decay is the functional equation twice. See
`Hemigroup/MellinVertical.lean`.

## What is stated here: `def:inversion-operator`

Ledger **A12**. What remains of that entry, after the Γ estimate, is the *operator* formulation:
Mathlib's `mellinInv_mellin_eq` recovers a function from its own transform, whereas the node needs
the contour integral against `B(-z) g̃(z)` to agree with the functional-calculus reading
`x ↦ x⁻¹ (B(θ)g)(x)`. So one must **exhibit** the `h` that `B(θ)g` names.

That is what `RealisesSymbolAction` is: `h` realises the symbol's action on `g` at height `c` when
its Mellin transform is the product on the line, and it meets Mathlib's inversion hypotheses
there. The operator is then defined unconditionally by the contour integral, and the content is
that it computes `x⁻¹ h x` whenever such an `h` exists.

Three design decisions were taken in writing this down.

**1. The transform identity is stated against `h`, not against the product.** Blueprint:
`Ãg(z) = B(1-z) g̃(z-1)`. What `mellin_inversionOperator` concludes is `mellin (A g) z =
mellin h (z-1)`, from which the display follows *wherever the product identity holds pointwise*
(`mellin_inversionOperator_eq`). The split is forced, and by the same feature of `B` that
`inversionSymbol_eq`'s docstring records: `B` is a quotient, so at a zero of `H̃` Lean's `x/0 = 0`
makes the product vanish where `mellin h` need not.

**2. Hence the realising condition is stated almost everywhere on the line.** The zeros of `H̃` are
isolated (`eventually_mellin_profile_ne_zero`), so they meet the line in a null set, and the
inversion integral does not see them. Demanding the identity at *every* point of the line would be
a hypothesis no profile satisfies; demanding it almost everywhere is exactly what the integral
uses. This is the second time in the chapter that "equality on the strip" has had to say which
equality it means — the first was `lem:symbol-rigidity`.

**3. `A` is defined for every `g`, and the hypotheses live on the theorems.** `mellinInv` is an
ordinary integral, so `A g` is a total function whatever `g` is; making the definition partial
would put a proof obligation in every downstream statement to no purpose. What the blueprint
states as a restriction on the domain of `A` is here a hypothesis of the theorems that compute it.
-/

namespace Skeleton

open MeasureTheory Set Filter Hemigroup

open scoped Topology

variable (F : Hemigroup.SelfDecomposableExponent)

/-! ## `def:inversion-operator` -/

/-- **`def:inversion-operator`.** The inversion operator at height `c`,
`(A g)(x) = x⁻¹ (2πi)⁻¹ ∫_{(c)} x^{-z} B(-z) g̃(z) dz`.

Mathlib's `mellinInv` is exactly the contour integral of the blueprint: parametrising the line by
`z = c + iy` turns `dz` into `i dy` and cancels the `i`, leaving `(2π)⁻¹ ∫ x^{-z} …dy`. The symbol
appears as `F.inversionSymbol z` rather than as `B(-z)` because `inversionSymbol` is already
indexed by the Mellin variable of the Euler operator; see its docstring. -/
noncomputable def inversionOperator (c : ℝ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  x⁻¹ * mellinInv c (fun z => F.inversionSymbol z * mellin g z) x

/-- `h` **realises the symbol's action** on `g` at height `c`: it is the function the
functional-calculus reading of `def:inversion-operator` calls `B(θ)g`.

The first field is almost-everywhere equality on the line, not pointwise: `B` is a quotient, so at
a zero of `H̃` the product vanishes for Lean's reason rather than for a mathematical one, and the
zeros are isolated. The last two fields are verbatim the hypotheses of `mellinInv_mellin_eq`. -/
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

This is the step ledger A12 carries. Everything in it is Mathlib's `mellinInv_mellin_eq` once the
integrand has been recognised as `mellin h`. -/
theorem inversionOperator_eq {c : ℝ} {g h : ℝ → ℂ} (hrep : RealisesSymbolAction F c g h) {x : ℝ}
    (hx : 0 < x) (hcont : ContinuousAt h x) :
    inversionOperator F c g x = x⁻¹ * h x := by
  sorry

/-- **`def:inversion-operator`**, the transform-level identity, stated against the realising
function: `Ãg(z) = h̃(z-1)`.

No strip condition: the shift is `mellin_cpow_smul` at exponent `-1` and holds at every `z` once
the pointwise formula above is known on `(0,∞)`. -/
theorem mellin_inversionOperator {c : ℝ} {g h : ℝ → ℂ} (hrep : RealisesSymbolAction F c g h)
    (hcont : ContinuousOn h (Ioi 0)) (z : ℂ) :
    mellin (inversionOperator F c g) z = mellin h (z - 1) := by
  sorry

/-- **`def:inversion-operator`**, the blueprint's display `Ãg(z) = B(1-z) g̃(z-1)`, at any point
where the product identity holds pointwise. -/
theorem mellin_inversionOperator_eq {c : ℝ} {g h : ℝ → ℂ} (hrep : RealisesSymbolAction F c g h)
    (hcont : ContinuousOn h (Ioi 0)) {z : ℂ}
    (hz : mellin h (z - 1) = F.inversionSymbol (z - 1) * mellin g (z - 1)) :
    mellin (inversionOperator F c g) z = F.inversionSymbol (z - 1) * mellin g (z - 1) := by
  sorry

end Skeleton
