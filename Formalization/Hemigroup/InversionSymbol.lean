/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.MellinData
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The inversion symbol

Blueprint: `lem:inversion-symbol` (11.14), the clause of the draft's Lemma 11.2 that every later
node of chapter 11 actually consumes — `def:inversion-operator` needs `B` and its strip,
`lem:symbol-uniqueness` needs the isolated zeros of `H̃`, `rem:poles` needs the poles.

`lem:mellin-data` supplies the identity `H̃(z) = Γ(z) m(z)` with `m(z) = E[T₁^{-z}]`. This file
turns it into the complex-analytic statement the chapter runs on:

* `analyticAt_mellin_profile` — `H̃` is analytic on `0 < Re z < z_*`;
* `mellin_profile_ofReal_ne_zero` — `H̃` does not vanish at the real points of the strip, so it is
  not identically zero;
* `eventually_mellin_profile_ne_zero` — hence its zeros are isolated;
* `inversionSymbol_eq` — `B(-z) = z · m(z+1) / m(z)`;
* `analyticAt_inversionSymbol` — `B` is analytic wherever `H̃` does not vanish;
* `meromorphicOn_inversionSymbol` — and meromorphic on `0 < Re z < z_* - 1` throughout.

## Where the analyticity comes from: `m` is a complex MGF

The obvious route is Mathlib's `mellin_differentiableAt_of_isBigO_rpow`, which would need `H` to
be `O(s^{-a})` at infinity for every `a < z_*`. That is true — `H` is antitone, so
`H(s)·s^a/a ≤ ∫₀^s u^{a-1}H(u) du ≤ Γ(a)E[T₁^{-a}]` — but it is work, and it re-derives from the
Mellin integral what the identity already says.

The identity gives a shorter route, and a more informative one. `m(z) = E[T₁^{-z}] =
E[e^{-z log T₁}]` is exactly `ProbabilityTheory.complexMGF` of the random variable `-log T₁`, and
Mathlib's `analyticAt_complexMGF` gives analyticity on the interior of the set where the
corresponding real exponential is integrable. Here that set contains `(0, z_*)` — which is open,
so no boundary case has to be argued — and membership is `negMoment_ne_top_of_lt_zStar`, already
proved. So the strip of analyticity and the strip of the identity are *the same strip*, for the
same reason, rather than two conditions that happen to coincide: `Re z < z_*` is finiteness of the
`Re z`-th negative moment on both sides. `Γ` contributes the rest, being analytic on `Re z > 0`.

## What the symbol costs, and what it does not

`inversionSymbol_eq` is the recursion `Γ(z+1) = z Γ(z)` and nothing else — the `Γ` factors cancel
in the ratio, which is exactly why `B` alone grows along vertical lines where `H̃` decays, the
point `blueprint/AXIOMS.md` A12 turns on. Note the identity holds with no hypothesis on `m(z)`:
Lean's `x / 0 = 0` makes both sides vanish together when `H̃(z) = 0`, so the statement needs no
non-vanishing side condition and the reader is not misled into thinking one was checked.
-/

namespace Hemigroup

open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal Topology

/-! ## Vertical strips -/

/-- The open vertical strip `a < Re z < b`. -/
def verticalStrip (a b : ℝ) : Set ℂ := {z : ℂ | a < z.re ∧ z.re < b}

lemma mem_verticalStrip {a b : ℝ} {z : ℂ} : z ∈ verticalStrip a b ↔ a < z.re ∧ z.re < b := Iff.rfl

lemma isOpen_verticalStrip (a b : ℝ) : IsOpen (verticalStrip a b) :=
  (isOpen_Ioo (a := a) (b := b)).preimage Complex.continuous_re

lemma convex_verticalStrip (a b : ℝ) : Convex ℝ (verticalStrip a b) :=
  (convex_Ioo a b).linear_preimage Complex.reLm

/-- `Γ` is analytic on the right half-plane. Mathlib carries differentiability; the half-plane is
open, so Goursat upgrades it. -/
theorem analyticAt_Gamma {z : ℂ} (hz : 0 < z.re) : AnalyticAt ℂ Complex.Gamma z := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ Complex.Gamma {w : ℂ | 0 < w.re} := by
    intro w hw
    refine (Complex.differentiableAt_Gamma w fun m => ?_).differentiableWithinAt
    intro h
    rw [h] at hw
    simp only [mem_setOf_eq, Complex.neg_re, Complex.natCast_re] at hw
    linarith [Nat.cast_nonneg (α := ℝ) m]
  exact hdiff.analyticOnNhd hopen z hz

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent)

/-! ## `m(z) = E[T₁^{-z}]` as a complex MGF -/

/-- **The negative-moment function** `m(z) = E[T₁^{-z}]`, complex-valued. This is the factor
`mellin_profile` pairs with `Γ`; it is finite on the strip because `Re z < z_*`. -/
noncomputable def negMomentC (z : ℂ) : ℂ := ∫ t, (t : ℂ) ^ (-z) ∂F.lawT₁

/-- `m` is the complex moment-generating function of `-log T₁`. Since `T₁ > 0` almost surely,
`T₁^{-z} = e^{-z log T₁}` pointwise, and the two integrals agree. -/
theorem negMomentC_eq_complexMGF (h0 : F.lawT₁ {(0 : ℝ)} = 0) (z : ℂ) :
    F.negMomentC z = complexMGF (fun t : ℝ => -Real.log t) F.lawT₁ z := by
  rw [negMomentC, complexMGF]
  refine integral_congr_ae ?_
  filter_upwards [F.ae_mem_Ioi_lawT₁ h0] with t ht
  have ht' : (0 : ℝ) < t := mem_Ioi.mp ht
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ht'.ne'), ← Complex.ofReal_log ht'.le]
  congr 1
  push_cast
  ring

/-- The strip is inside the exponential-integrability set of `-log T₁`, membership being exactly
`negMoment_ne_top_of_lt_zStar`. Stated for the *open* interval, which is what makes the interior
step below free. -/
theorem Ioo_subset_integrableExpSet (h0 : F.lawT₁ {(0 : ℝ)} = 0) :
    Ioo (0 : ℝ) F.zStar ⊆ integrableExpSet (fun t : ℝ => -Real.log t) F.lawT₁ := by
  rintro c ⟨hc0, hcz⟩
  have hae := F.ae_mem_Ioi_lawT₁ h0
  have heq : (fun t : ℝ => Real.exp (c * -Real.log t)) =ᵐ[F.lawT₁] fun t : ℝ => t ^ (-c) := by
    filter_upwards [hae] with t ht
    rw [Real.rpow_def_of_pos (mem_Ioi.mp ht)]
    ring_nf
  refine Integrable.congr ?_ heq.symm
  refine ⟨(by fun_prop), ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hcalc : ∫⁻ t, ‖t ^ (-c)‖ₑ ∂F.lawT₁ = F.negMoment c := by
    rw [negMoment, Measure.restrict_eq_self_of_ae_mem hae]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with t ht
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (mem_Ioi.mp ht).le _)]
  rw [hcalc]
  exact lt_top_iff_ne_top.mpr (F.negMoment_ne_top_of_lt_zStar hc0 hcz)

/-- `m` is analytic on the strip. -/
theorem analyticAt_negMomentC (h0 : F.lawT₁ {(0 : ℝ)} = 0) {z : ℂ}
    (hz : z ∈ verticalStrip 0 F.zStar) : AnalyticAt ℂ F.negMomentC z := by
  have hmem : z.re ∈ interior (integrableExpSet (fun t : ℝ => -Real.log t) F.lawT₁) :=
    interior_maximal (F.Ioo_subset_integrableExpSet h0) isOpen_Ioo ⟨hz.1, hz.2⟩
  refine (analyticAt_complexMGF hmem).congr ?_
  exact Filter.Eventually.of_forall fun w => (F.negMomentC_eq_complexMGF h0 w).symm

/-! ## `lem:inversion-symbol`: `H̃` is analytic and does not vanish identically -/

/-- **`lem:inversion-symbol`**, analyticity: `H̃` is analytic on `0 < Re z < z_*`.

`Γ` is analytic on the half-plane and `m` on the strip; `mellin_profile` identifies the product
with `H̃` *throughout* the strip, which is open, so the identification holds on a neighbourhood
and transfers analyticity. -/
theorem analyticAt_mellin_profile (hH : F.StandingHypothesis) {z : ℂ}
    (hz : z ∈ verticalStrip 0 F.zStar) :
    AnalyticAt ℂ (mellin fun s => (F.profile s : ℂ)) z := by
  have h0 := F.lawT₁_singleton_zero hH.1
  refine ((analyticAt_Gamma hz.1).mul (F.analyticAt_negMomentC h0 hz)).congr ?_
  filter_upwards [(isOpen_verticalStrip 0 F.zStar).mem_nhds hz] with w hw
  exact (F.mellin_profile hH hw.1 hw.2).symm

/-- The shifted transform `w ↦ H̃(w+1)`, analytic one step lower in the strip: the numerator of
the inversion symbol. -/
theorem analyticAt_mellin_profile_shift (hH : F.StandingHypothesis) {z : ℂ}
    (hz : z ∈ verticalStrip 0 (F.zStar - 1)) :
    AnalyticAt ℂ (fun w : ℂ => mellin (fun s => (F.profile s : ℂ)) (w + 1)) z := by
  obtain ⟨hz0, hz1⟩ := hz
  have hshift : AnalyticAt ℂ (fun w : ℂ => w + 1) z := analyticAt_id.add analyticAt_const
  have hmem : z + 1 ∈ verticalStrip 0 F.zStar := by
    constructor <;> simp <;> linarith
  have hcomp := AnalyticAt.comp (g := mellin fun s => (F.profile s : ℂ))
    (f := fun w : ℂ => w + 1) (x := z) (F.analyticAt_mellin_profile hH hmem) hshift
  simpa [Function.comp_def] using hcomp

/-- The negative moments are strictly positive: `T₁ > 0` almost surely and carries unit mass. -/
theorem negMoment_ne_zero (h0 : F.lawT₁ {(0 : ℝ)} = 0) (c : ℝ) : F.negMoment c ≠ 0 := by
  have hae := F.ae_mem_Ioi_lawT₁ h0
  rw [negMoment, Measure.restrict_eq_self_of_ae_mem hae]
  intro hzero
  rw [lintegral_eq_zero_iff' (by fun_prop)] at hzero
  have hpos : ∀ᵐ t ∂F.lawT₁, ENNReal.ofReal (t ^ (-c)) ≠ 0 := by
    filter_upwards [hae] with t ht
    simp [ENNReal.ofReal_eq_zero, not_le, Real.rpow_pos_of_pos (mem_Ioi.mp ht)]
  obtain ⟨t, h1, h2⟩ := (hzero.and hpos).exists
  exact h2 h1

/-- At a real point of the strip, `m` is the real negative moment. -/
theorem negMomentC_ofReal (h0 : F.lawT₁ {(0 : ℝ)} = 0) (c : ℝ) :
    F.negMomentC (c : ℂ) = ((F.negMoment c).toReal : ℂ) := by
  have hof : ((∫ t, t ^ (-c) ∂F.lawT₁ : ℝ) : ℂ) = ∫ t, ((t ^ (-c) : ℝ) : ℂ) ∂F.lawT₁ :=
    (integral_ofReal (𝕜 := ℂ)).symm
  rw [← F.integral_rpow_neg_eq_negMoment h0, hof, negMomentC]
  refine integral_congr_ae ?_
  filter_upwards [F.ae_mem_Ioi_lawT₁ h0] with t ht
  rw [Complex.ofReal_cpow (mem_Ioi.mp ht).le]
  norm_cast

/-- **`lem:inversion-symbol`**, non-vanishing: `H̃ ≠ 0` at every real point of the strip.

Both factors of `Γ(c)E[T₁^{-c}]` are strictly positive there. This is what makes `H̃ ≢ 0`, and so
what makes its zeros isolated. -/
theorem mellin_profile_ofReal_ne_zero (hH : F.StandingHypothesis) {c : ℝ} (hc : 0 < c)
    (hc' : c < F.zStar) : mellin (fun s => (F.profile s : ℂ)) (c : ℂ) ≠ 0 := by
  have h0 := F.lawT₁_singleton_zero hH.1
  have hre : ((c : ℂ)).re = c := Complex.ofReal_re c
  rw [F.mellin_profile hH (by rw [hre]; exact hc) (by rw [hre]; exact hc')]
  refine mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos (by rw [hre]; exact hc)) ?_
  rw [show (∫ t, (t : ℂ) ^ (-(c : ℂ)) ∂F.lawT₁) = F.negMomentC (c : ℂ) from rfl,
    F.negMomentC_ofReal h0]
  simp only [ne_eq, Complex.ofReal_eq_zero, ENNReal.toReal_eq_zero_iff, not_or]
  exact ⟨F.negMoment_ne_zero h0 c, F.negMoment_ne_top_of_lt_zStar hc hc'⟩

/-- **`lem:inversion-symbol`**, isolated zeros: `H̃` is nonzero on a punctured neighbourhood of
every point of the strip.

The identity theorem on the strip, which is convex and so preconnected: were `H̃` to vanish near
one point it would vanish at every point, and it does not vanish at the real ones. This is the
clause `lem:symbol-uniqueness` consumes — it is what lets an identity that holds off an isolated
set be promoted to the whole strip. -/
theorem eventually_mellin_profile_ne_zero (hH : F.StandingHypothesis) {z : ℂ}
    (hz : z ∈ verticalStrip 0 F.zStar) :
    ∀ᶠ w in 𝓝[≠] z, mellin (fun s => (F.profile s : ℂ)) w ≠ 0 := by
  have hanal : AnalyticOnNhd ℂ (mellin fun s => (F.profile s : ℂ)) (verticalStrip 0 F.zStar) :=
    fun w hw => F.analyticAt_mellin_profile hH hw
  rcases (hanal z hz).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    have hzero := hanal.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_verticalStrip 0 F.zStar).isPreconnected hz h
    have hmem : ((z.re : ℝ) : ℂ) ∈ verticalStrip 0 F.zStar := by
      simpa [mem_verticalStrip] using hz
    exact F.mellin_profile_ofReal_ne_zero hH hz.1 hz.2 (hzero hmem)
  · exact h

/-! ## The symbol -/

/-- **The inversion symbol**, the blueprint's `B(-z) = H̃(z+1)/H̃(z)`.

Indexed by `z`, not by `-z`: the article writes the symbol of the Euler operator, whose Mellin
symbol is `-z`, and carrying the sign in the definition would put it in every statement below. -/
noncomputable def inversionSymbol (z : ℂ) : ℂ :=
  mellin (fun s => (F.profile s : ℂ)) (z + 1) / mellin (fun s => (F.profile s : ℂ)) z

/-- **`lem:inversion-symbol`**, the closed form: `B(-z) = z · E[T₁^{-z-1}] / E[T₁^{-z}]`.

The `Γ` factors cancel by `Γ(z+1) = zΓ(z)`, and that cancellation is the whole content. It is also
why `B` alone is not vertically integrable where `H̃` is — the decay leaves with the `Γ`s. -/
theorem inversionSymbol_eq (hH : F.StandingHypothesis) {z : ℂ}
    (hz : z ∈ verticalStrip 0 (F.zStar - 1)) :
    F.inversionSymbol z = z * F.negMomentC (z + 1) / F.negMomentC z := by
  obtain ⟨hz0, hz1⟩ := hz
  have hre1 : (z + 1).re = z.re + 1 := by simp
  have h1 := F.mellin_profile hH (z := z + 1) (by rw [hre1]; linarith) (by rw [hre1]; linarith)
  have h2 := F.mellin_profile hH (z := z) hz0 (by linarith)
  have hz0' : z ≠ 0 := fun h => by rw [h] at hz0; simp at hz0
  have hΓ : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz0
  rw [inversionSymbol, h1, h2, Complex.Gamma_add_one z hz0']
  rw [show (∫ t, (t : ℂ) ^ (-(z + 1)) ∂F.lawT₁) = F.negMomentC (z + 1) from rfl,
    show (∫ t, (t : ℂ) ^ (-z) ∂F.lawT₁) = F.negMomentC z from rfl,
    show z * Complex.Gamma z * F.negMomentC (z + 1)
      = Complex.Gamma z * (z * F.negMomentC (z + 1)) from by ring]
  exact mul_div_mul_left _ _ hΓ

/-- **`lem:inversion-symbol`**, poles only at the zeros of `H̃`: `B` is analytic at every point of
its strip where the denominator does not vanish. -/
theorem analyticAt_inversionSymbol (hH : F.StandingHypothesis) {z : ℂ}
    (hz : z ∈ verticalStrip 0 (F.zStar - 1))
    (hne : mellin (fun s => (F.profile s : ℂ)) z ≠ 0) :
    AnalyticAt ℂ F.inversionSymbol z := by
  obtain ⟨hz0, hz1⟩ := hz
  have hnum : AnalyticAt ℂ (fun w : ℂ => mellin (fun s => (F.profile s : ℂ)) (w + 1)) z :=
    F.analyticAt_mellin_profile_shift hH ⟨hz0, hz1⟩
  exact hnum.div (F.analyticAt_mellin_profile hH ⟨hz0, by linarith⟩) hne

/-- **`lem:inversion-symbol`**, meromorphy: `B` is meromorphic on `0 < Re z < z_* - 1`. -/
theorem meromorphicOn_inversionSymbol (hH : F.StandingHypothesis) :
    MeromorphicOn F.inversionSymbol (verticalStrip 0 (F.zStar - 1)) := by
  intro z hz
  obtain ⟨hz0, hz1⟩ := hz
  have hnum : AnalyticAt ℂ (fun w : ℂ => mellin (fun s => (F.profile s : ℂ)) (w + 1)) z :=
    F.analyticAt_mellin_profile_shift hH ⟨hz0, hz1⟩
  have hden : AnalyticAt ℂ (mellin fun s => (F.profile s : ℂ)) z :=
    F.analyticAt_mellin_profile hH ⟨hz0, by linarith⟩
  exact hnum.meromorphicAt.div hden.meromorphicAt

end SelfDecomposableExponent

end Hemigroup
