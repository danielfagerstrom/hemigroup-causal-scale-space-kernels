/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Hemigroup.InversionSymbol
import Hemigroup.MellinVertical
-- For `continuousOn_laplace`: the profile instance below needs `H` continuous at a point, which is
-- the standing continuity of a causal finite measure's transform on `[0,∞)`.
import Hemigroup.TransformContinuity

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

## The identity on the line holds exactly off the zeros of `H̃`

`B` is a quotient with poles at the zeros of `H̃`. Where `H̃` vanishes, Lean's `x / 0 = 0` makes
`B(-z) g̃(z)` vanish too, while `h̃(z)` need not: at such a point the product identity fails for a
reason about notation rather than about the operator. So a pointwise reading of the blueprint's
display, valid at every point of the line, would be false as stated.

There are two candidate weakenings, and they are not interchangeable. *Almost everywhere* is all
`inversionOperator_eq` needs — the zeros are isolated, hence null on the line, and
`integral_congr_ae` discards them. *Off the zeros of `H̃`* is what the profiles actually supply,
and it is what `lem:symbol-uniqueness` consumes, since that theorem has to conclude an equality of
symbols at named points and an a.e. hypothesis concludes nothing at any of them.
`RealisesAction.mellin_eq` is therefore the second, with the first derived from it as
`mellin_eq_ae`. Choosing the weaker one first and discovering the gap at the uniqueness theorem is
what the statement-first order is for.

That is also why `mellin_inversionOperator` concludes `Ãg(z) = h̃(z-1)` rather than the display
`B(1-z)g̃(z-1)`: the two agree wherever the product identity holds, which is
`mellin_inversionOperator_eq`. The same question — which equality does "equal on the strip" mean —
was answered differently in `SymbolUniqueness.lean` (a punctured neighbourhood, the meromorphic
reading), and each time writing the statement is what raised it.

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

/-- `h` **realises the action of the symbol `B`** on `g` at height `c`: it is the function that
the functional-calculus reading of `def:inversion-operator` calls `B(θ)g`.

The symbol is a parameter rather than `F.inversionSymbol`, because `lem:symbol-uniqueness`
quantifies over candidate symbols; `RealisesSymbolAction` below is the case that matters.

**The transform identity is asked for exactly off the zeros of `H̃`, and that set is not
arbitrary.** It cannot be asked for everywhere: `F.inversionSymbol` is a quotient with denominator
`H̃`, so where `H̃` vanishes the product vanishes for a reason about notation and `h̃` need not.
It could be asked for only almost everywhere — which is all `inversionOperator_eq` uses, the zeros
being null — but that is *weaker than what the profiles supply* and too weak for
`lem:symbol-uniqueness`, which needs the symbols to agree at named points. Conditioning on
`H̃(w) ≠ 0` is the unique choice that the instance proves and the uniqueness theorem consumes.

The last two fields are verbatim the hypotheses of Mathlib's `mellinInv_mellin_eq`; for the
profiles the second of them is `lem:mellin-vertical`. -/
structure RealisesAction (c : ℝ) (B : ℂ → ℂ) (g h : ℝ → ℂ) : Prop where
  /-- The transform of `h` is the product `B(-z) g̃(z)` at every point of the line where the
  profile's own transform does not vanish. -/
  mellin_eq : ∀ y : ℝ, mellin (fun u => (F.profile u : ℂ)) (c + y * Complex.I) ≠ 0 →
    mellin h (c + y * Complex.I) = B (c + y * Complex.I) * mellin g (c + y * Complex.I)
  /-- The forward Mellin integral of `h` converges on the line. -/
  convergent : MellinConvergent h c
  /-- The inversion integral converges absolutely on the line — the hypothesis
  `def:inversion-operator` imposes, and the one `lem:mellin-vertical` supplies for profiles. -/
  verticalIntegrable : Complex.VerticalIntegrable (mellin h) c

/-- `h` realises the action of *the* inversion symbol on `g` at height `c`. -/
abbrev RealisesSymbolAction (c : ℝ) (g h : ℝ → ℂ) : Prop :=
  F.RealisesAction c F.inversionSymbol g h

/-- The almost-everywhere reading of the transform identity, which is what the inversion integral
uses: the zeros of `H̃` on the line are null (`ae_mellin_profile_ne_zero`). -/
theorem RealisesAction.mellin_eq_ae {F : SelfDecomposableExponent} (hH : F.StandingHypothesis)
    {c : ℝ} (hc : 0 < c)
    (hc' : ENNReal.ofReal c < F.zStar) {B : ℂ → ℂ} {g h : ℝ → ℂ} (hrep : F.RealisesAction c B g h) :
    ∀ᵐ y : ℝ, mellin h ((c : ℂ) + y * Complex.I)
      = B ((c : ℂ) + y * Complex.I) * mellin g ((c : ℂ) + y * Complex.I) := by
  filter_upwards [F.ae_mellin_profile_ne_zero hH hc hc'] with y hy using hrep.mellin_eq y hy

/-- **`def:inversion-operator`**, the functional-calculus reading: where the symbol's action on `g`
is realised by `h`, the contour integral computes `x⁻¹ h x`.

This is the step ledger A12 carries, and it is Mathlib's `mellinInv_mellin_eq` once the integrand
has been recognised as `mellin h`. Recognising it is the whole of the proof, and the null set
where the recognition fails is discarded by `integral_congr_ae` — which is available precisely
because `mellinInv` integrates over the line rather than evaluating on it. -/
theorem inversionOperator_eq (hH : F.StandingHypothesis) {c : ℝ} (hc : 0 < c) (hc' : ENNReal.ofReal c < F.zStar)
    {g h : ℝ → ℂ} (hrep : F.RealisesSymbolAction c g h) {x : ℝ}
    (hx : 0 < x) (hcont : ContinuousAt h x) :
    F.inversionOperator c g x = x⁻¹ * h x := by
  have hint : mellinInv c (fun z => F.inversionSymbol z * mellin g z) x
      = mellinInv c (mellin h) x := by
    rw [mellinInv, mellinInv]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hrep.mellin_eq_ae hH hc hc'] with y hy
    rw [hy]
  rw [inversionOperator, hint,
    mellinInv_mellin_eq c h hx hrep.convergent hrep.verticalIntegrable hcont]

/-- **`def:inversion-operator`**, the transform-level identity, against the realising function:
`Ãg(z) = h̃(z-1)`.

No strip condition. Once the pointwise formula is known on `(0,∞)`, the weight `x⁻¹` is
`mellin_cpow_smul` at exponent `-1`, which shifts the argument and is available at every `z`. -/
theorem mellin_inversionOperator (hH : F.StandingHypothesis) {c : ℝ} (hc : 0 < c)
    (hc' : ENNReal.ofReal c < F.zStar) {g h : ℝ → ℂ} (hrep : F.RealisesSymbolAction c g h)
    (hcont : ContinuousOn h (Ioi 0)) (z : ℂ) :
    mellin (F.inversionOperator c g) z = mellin h (z - 1) := by
  have hpt : ∀ t ∈ Ioi (0 : ℝ),
      F.inversionOperator c g t = (t : ℂ) ^ (-1 : ℂ) • h t := by
    intro t ht
    rw [F.inversionOperator_eq hH hc hc' hrep (mem_Ioi.mp ht)
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
theorem mellin_inversionOperator_eq (hH : F.StandingHypothesis) {c : ℝ} (hc : 0 < c)
    (hc' : ENNReal.ofReal c < F.zStar) {g h : ℝ → ℂ} (hrep : F.RealisesSymbolAction c g h)
    (hcont : ContinuousOn h (Ioi 0)) {z : ℂ}
    (hz : mellin h (z - 1) = F.inversionSymbol (z - 1) * mellin g (z - 1)) :
    mellin (F.inversionOperator c g) z = F.inversionSymbol (z - 1) * mellin g (z - 1) := by
  rw [F.mellin_inversionOperator hH hc hc' hrep hcont z, hz]

/-! ## The profile instance, and the eigenfunction relation

The case the article actually uses, and the one that decides ledger A12: `g = H(s·)`, the dilate of
the profile, with the referent `h(x) = s x H(sx)` exhibited outright. Nothing here is a hypothesis
about `g` — the realising function is produced, so this is the check that A12's remaining step is
never called upon.

The two transforms are one Mellin shift apart, `h̃(w) = s^{-w} H̃(w+1)` against
`g̃(w) = s^{-w} H̃(w)`, and their ratio is `inversionSymbol` by definition. So the realising
identity is not a computation at all: it is `B` written out, with the denominator cleared — which
is why it needs `H̃(w) ≠ 0`, and why it can only be asked for almost everywhere. The blueprint's
proof says "no pole of `B` intervenes, the product containing no division", and that is true of
the *simplified* product; `B` here is a function, so the division is present and has to be
cancelled, which costs `ae_mellin_profile_ne_zero`.

And then `A g = x⁻¹ h` reads `(A[H(s·)])(x) = s H(sx)`, which is Theorem 4′'s eigenfunction
relation. The instance and the eigenfunction relation are the same statement. -/

/-- The Mellin transform of a dilate: `g̃(w) = s^{-w} H̃(w)`. -/
theorem mellin_profile_comp_mul {s : ℝ} (hs : 0 < s) (w : ℂ) :
    mellin (fun x : ℝ => (F.profile (s * x) : ℂ)) w
      = (s : ℂ) ^ (-w) * mellin (fun u => (F.profile u : ℂ)) w := by
  rw [mellin_comp_mul_left (fun u : ℝ => ((F.profile u : ℝ) : ℂ)) w hs, smul_eq_mul]

/-- The Mellin transform of the realising function: `h̃(w) = s^{-w} H̃(w+1)`.

`h(x) = s·x·H(sx)` is `s • (x^1 • g(x))`, so the weight `x` is a Mellin shift by one and the
constant comes out; the two powers of `s` then combine as `s^1 · s^{-(w+1)} = s^{-w}`. -/
theorem mellin_profile_comp_mul_weight {s : ℝ} (hs : 0 < s) (w : ℂ) :
    mellin (fun x : ℝ => (s : ℂ) * (x : ℂ) * (F.profile (s * x) : ℂ)) w
      = (s : ℂ) ^ (-w) * mellin (fun u => (F.profile u : ℂ)) (w + 1) := by
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hfun : (fun x : ℝ => (s : ℂ) * (x : ℂ) * (F.profile (s * x) : ℂ))
      = fun x : ℝ => (s : ℂ) • ((x : ℂ) ^ (1 : ℂ) • ((F.profile (s * x) : ℝ) : ℂ)) := by
    funext x
    simp [Complex.cpow_one, smul_eq_mul, mul_assoc]
  rw [hfun, mellin_const_smul, mellin_cpow_smul, smul_eq_mul,
    mellin_comp_mul_left (fun u : ℝ => ((F.profile u : ℝ) : ℂ)) (w + 1) hs, smul_eq_mul,
    ← mul_assoc]
  congr 1
  rw [show (-w : ℂ) = 1 + -(w + 1) from by ring, Complex.cpow_add _ _ hs0, Complex.cpow_one]

/-- `MellinConvergent` for the realising function, from the profile's own convergence one step
higher in the strip: the weight `x` and the dilation are both Mellin-transparent. -/
theorem mellinConvergent_profile_comp_mul_weight (hH : F.StandingHypothesis) {c s : ℝ}
    (hc : 0 < c) (hc' : ENNReal.ofReal (c + 1) < F.zStar) (hs : 0 < s) :
    MellinConvergent (fun x : ℝ => (s : ℂ) * (x : ℂ) * (F.profile (s * x) : ℂ)) c := by
  have hbase : MellinConvergent (fun u : ℝ => ((F.profile u : ℝ) : ℂ)) ((c : ℂ) + 1) :=
    F.mellinConvergent_profile hH (z := (c : ℂ) + 1) (by simp; linarith) (by simpa using hc')
  have hdil : MellinConvergent (fun x : ℝ => ((F.profile (s * x) : ℝ) : ℂ)) ((c : ℂ) + 1) :=
    (MellinConvergent.comp_mul_left hs).mpr hbase
  have hweight : MellinConvergent
      (fun x : ℝ => (x : ℂ) ^ (1 : ℂ) • ((F.profile (s * x) : ℝ) : ℂ)) (c : ℂ) :=
    MellinConvergent.cpow_smul.mpr hdil
  have hfun : (fun x : ℝ => (s : ℂ) * (x : ℂ) * (F.profile (s * x) : ℂ))
      = fun x : ℝ => (s : ℂ) • ((x : ℂ) ^ (1 : ℂ) • ((F.profile (s * x) : ℝ) : ℂ)) := by
    funext x
    simp [Complex.cpow_one, smul_eq_mul, mul_assoc]
  rw [hfun]
  exact hweight.const_smul _

/-- Vertical integrability for the realising function: `lem:mellin-vertical` at height `c+1`,
carried across by a multiplier of constant modulus `s^{-c}`. -/
theorem verticalIntegrable_mellin_profile_comp_mul_weight (hH : F.StandingHypothesis) {c s : ℝ}
    (hc : 0 < c) (hc' : ENNReal.ofReal (c + 1) < F.zStar) (hs : 0 < s) :
    Complex.VerticalIntegrable
      (mellin fun x : ℝ => (s : ℂ) * (x : ℂ) * (F.profile (s * x) : ℂ)) c := by
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have harg : ∀ y : ℝ, (((c + 1 : ℝ) : ℂ) + y * Complex.I) = ((c : ℂ) + y * Complex.I) + 1 := by
    intro y
    push_cast
    ring
  have hbase : Integrable fun y : ℝ =>
      mellin (fun u : ℝ => ((F.profile u : ℝ) : ℂ)) (((c + 1 : ℝ) : ℂ) + y * Complex.I) :=
    F.verticalIntegrable_mellin_profile hH (c := c + 1) (by linarith) hc'
  have hshift : Integrable fun y : ℝ =>
      mellin (fun u : ℝ => ((F.profile u : ℝ) : ℂ)) (((c : ℂ) + y * Complex.I) + 1) := by
    simpa only [harg] using hbase
  have hmeas : AEStronglyMeasurable
      (fun y : ℝ => (s : ℂ) ^ (-((c : ℂ) + y * Complex.I))) volume := by
    refine Continuous.aestronglyMeasurable (continuous_iff_continuousAt.mpr fun y => ?_)
    exact ContinuousAt.const_cpow (by fun_prop) (Or.inl hs0)
  have hbound : ∀ᵐ y : ℝ, ‖(s : ℂ) ^ (-((c : ℂ) + y * Complex.I))‖ ≤ s ^ (-c) := by
    refine .of_forall fun y => ?_
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hs]
    simp
  have := hshift.bdd_mul hmeas hbound
  refine this.congr (.of_forall fun y => ?_)
  exact (F.mellin_profile_comp_mul_weight hs _).symm

/-- **The profile realises the symbol's action on its own dilate.**

Ledger A12's remaining step is never called upon in this article, because this is the only shape in
which `A` is ever applied and the referent is exhibited rather than asserted. The realising
identity is `inversionSymbol` written out with its denominator cleared, so it holds exactly where
`H̃` does not vanish — a set of full measure on the line by `ae_mellin_profile_ne_zero`. -/
theorem realisesSymbolAction_profile (hH : F.StandingHypothesis) {c s : ℝ} (hc : 0 < c)
    (hc' : ENNReal.ofReal (c + 1) < F.zStar) (hs : 0 < s) :
    F.RealisesSymbolAction c (fun x : ℝ => (F.profile (s * x) : ℂ))
      (fun x : ℝ => (s : ℂ) * (x : ℂ) * (F.profile (s * x) : ℂ)) where
  mellin_eq := by
    intro y hy
    rw [F.mellin_profile_comp_mul_weight hs, F.mellin_profile_comp_mul hs, inversionSymbol]
    field_simp
  convergent := F.mellinConvergent_profile_comp_mul_weight hH hc hc' hs
  verticalIntegrable := F.verticalIntegrable_mellin_profile_comp_mul_weight hH hc hc' hs

/-- **The eigenfunction relation**, `A[H(s·)] = s·H(s·)`: the clause `thm:signaling-form` is built
on, and the same statement as the instance above.

`A g = x⁻¹ h` with `h(x) = s x H(sx)` is `s H(sx)` on the nose — the weight `x⁻¹` in
`def:inversion-operator` is exactly what cancels the weight `x` that shifts the transform. -/
theorem inversionOperator_profile (hH : F.StandingHypothesis) {c s : ℝ} (hc : 0 < c)
    (hc' : ENNReal.ofReal (c + 1) < F.zStar) (hs : 0 < s) {x : ℝ} (hx : 0 < x) :
    F.inversionOperator c (fun u : ℝ => (F.profile (s * u) : ℂ)) x
      = (s : ℂ) * (F.profile (s * x) : ℂ) := by
  have hprof : ContinuousAt (fun u : ℝ => ((F.profile u : ℝ) : ℂ)) (s * x) := by
    have hcont := continuousOn_laplace (μ := F.lawT₁) F.isCausal_lawT₁
    have hat : ContinuousAt (fun u : ℝ => laplace F.lawT₁ u) (s * x) :=
      hcont.continuousAt (Ici_mem_nhds (mul_pos hs hx))
    exact Complex.continuous_ofReal.continuousAt.comp hat
  have hcont : ContinuousAt
      (fun u : ℝ => (s : ℂ) * (u : ℂ) * (F.profile (s * u) : ℂ)) x := by
    exact ((continuousAt_const.mul (Complex.continuous_ofReal.continuousAt)).mul
      (hprof.comp (by fun_prop)))
  rw [F.inversionOperator_eq hH hc (F.ofReal_lt_zStar_of_le (by linarith) hc')
    (F.realisesSymbolAction_profile hH hc hc' hs)
    hx hcont]
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [show (s : ℂ) * (x : ℂ) * (F.profile (s * x) : ℂ)
      = (x : ℂ) * ((s : ℂ) * (F.profile (s * x) : ℂ)) from by ring,
    ← mul_assoc, Complex.ofReal_inv, inv_mul_cancel₀ hx0, one_mul]


/-- `mellinInv` is linear in the transform, which is all the Laplace form of
`thm:signaling-form`(2) needs beyond the eigenfunction relation. -/
theorem mellinInv_const_mul (sigma : ℝ) (a : ℂ) (G : ℂ → ℂ) (x : ℝ) :
    mellinInv sigma (fun z => a * G z) x = a * mellinInv sigma G x := by
  simp only [mellinInv, Complex.real_smul, smul_eq_mul]
  rw [show (∫ y : ℝ, (x : ℂ) ^ (-((sigma : ℂ) + y * Complex.I))
        * (a * G ((sigma : ℂ) + y * Complex.I)))
      = a * ∫ y : ℝ, (x : ℂ) ^ (-((sigma : ℂ) + y * Complex.I))
        * G ((sigma : ℂ) + y * Complex.I) from by
    rw [← integral_const_mul]
    exact integral_congr_ae (.of_forall fun y => by ring)]
  ring

/-- **The inversion operator is homogeneous.** -/
theorem inversionOperator_const_mul (c : ℝ) (a : ℂ) (g : ℝ → ℂ) (x : ℝ) :
    F.inversionOperator c (fun u => a * g u) x = a * F.inversionOperator c g x := by
  have hm : ∀ z : ℂ, mellin (fun u : ℝ => a * g u) z = a * mellin g z := fun z => by
    simpa [smul_eq_mul] using mellin_const_smul g z a
  rw [inversionOperator, inversionOperator,
    show (fun z => F.inversionSymbol z * mellin (fun u : ℝ => a * g u) z)
      = fun z => a * (F.inversionSymbol z * mellin g z) from by
      funext z; rw [hm z]; ring,
    mellinInv_const_mul]
  ring

/-- **`thm:signaling-form`(2), the Laplace form**: every constant multiple of a profile dilate is
an eigenfunction of `A` with eigenvalue `s`.

The field's Laplace profile is `û(s,·) = f̂(s)·H(s·)`, so this *is* the Laplace form once that
identification is made (`laplaceFun_delayedField`). Homogeneity plus
`lem:profile-eigenfunction`. -/
theorem inversionOperator_const_mul_profile (hH : F.StandingHypothesis) {c s : ℝ} (hc : 0 < c)
    (hc' : ENNReal.ofReal (c + 1) < F.zStar) (hs : 0 < s) (a : ℂ) {x : ℝ} (hx : 0 < x) :
    F.inversionOperator c (fun u : ℝ => a * (F.profile (s * u) : ℂ)) x
      = (s : ℂ) * (a * (F.profile (s * x) : ℂ)) := by
  rw [F.inversionOperator_const_mul c a _ x, F.inversionOperator_profile hH hc hc' hs hx]
  ring

end SelfDecomposableExponent

end Hemigroup
