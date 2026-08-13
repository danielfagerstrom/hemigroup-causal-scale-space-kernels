/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.LocalOperator
import Hemigroup.ProfileDeriv
import Hemigroup.SymbolUniqueness

/-!
# The Euler engine on the profile class, and the (⇒) direction of `lem:local-polynomial-symbol`

Blueprint: the second half of `lem:local-polynomial-symbol` (12.2).

`MellinEuler.lean` proves `M[xʲ g⁽ʲ⁾](w) = E_j(w)·M[g](w)` for *test functions*, by `j`
integrations by parts. The profiles `H(s·)` are not test functions, and the same identity on them
needs no integration by parts at all: `ProfileDeriv.lean` has already turned the derivative into
an integral,

  `∂ₓʲ H(sx) = (-s)ʲ ∫ tʲ e^{-sxt} dμ(t)`,

and what is left is a computation in three moves, none of which is an estimate.

1. **The weight is a Mellin shift.** `mellin_cpow_smul` turns `M[xʲ f](w)` into `M[f](w+j)`, so
   the `xʲ` disappears into the argument and never has to be carried through a Fubini.
2. **The dilation is a factor**, `mellin_comp_mul_left`.
3. **What is left is chapter 11's own hinge.** `x ↦ ∫ tʲ e^{-xt} dμ(t)` is the Laplace transform
   of the *weighted* measure `tʲ μ(dt)`, so `lem:mellin-data` applies to it verbatim --- which is
   why `MellinData.lean` now states its three steps for a measure carried by `(0,∞)` rather than
   for `lawT₁`. Nothing there was restated; the generality was already in the proof.

`E_j(w) = (-1)ʲ Γ(w+j)/Γ(w)` then matches `mellinEulerFactor` by `Gamma_add_one` `j` times.

## What the identity is spent on, and the one thing it does not buy

With the engine in hand the profile clause of `def:locality-pmp` has two readings of `A[H(s·)]`
--- the differential expression, and the eigenfunction relation `A[H(s·)] = s H(s·)` of
`lem:profile-eigenfunction` --- and equating them gives, on `(0,∞)`,

  `s·x·H(sx) = ∑_j γ_j xʲ ∂ₓʲ H(sx)`.

Mellin-transforming term by term turns that into `h̃(w) = P(w)·g̃(w)` for the profile dilate and
its realising function, which is exactly `RealisesAction` with `P` in the place of the symbol. So
`lem:symbol-uniqueness` applies and `B` and `P` are the same meromorphic function.

**The conclusion is conditioned on `H̃(z) ≠ 0`, and that is forced rather than chosen.** What the
argument delivers, at every point of the strip and with no side condition, is the *recursion*
`H̃(z+1) = P(z)·H̃(z)` (`mellin_profile_shift_eq`). Dividing by `H̃(z)` to read off the symbol is
legitimate exactly where the denominator does not vanish; and where it does, `inversionSymbol z`
is `H̃(z+1)/0`, whose value in Lean is `0`, while `P(z)` is a polynomial and need not vanish
there. So the unconditional pointwise statement is *false* as stated, for the same reason the
identity of `def:inversion-operator` had to be conditioned on `H̃(w) ≠ 0` rather than asserted on
the whole line, and the same reason `lem:symbol-rigidity` concludes an `EventuallyEq` on a
punctured neighbourhood rather than an equality of functions. Both forms are proved below.

Nothing rules the zeros out. `H̃(z) = Γ(z)·E[T₁^{-z}]` has no zeros at the *real* points of the
strip (`mellin_profile_ofReal_ne_zero`), which is all chapter 11 needed and all that is available:
a Mellin transform of a positive random variable may certainly vanish off the real axis, and
excluding it here would be a theorem about self-decomposable laws that the article does not have.
The recursion is in any case the form the chapter consumes --- `lem:moment-recursion`(2) argues
from `H̃(z+1) = B(-z)H̃(z)` *as an identity between analytic functions*, not from a pointwise
value of `B`.
-/

namespace Hemigroup

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

/-! ## Two identities about `Γ` and the Euler factor

`E_j(z) = (-1)ʲ Γ(z+j)/Γ(z)` is the whole of the bookkeeping, and it is cleanest as two
statements that never divide. -/

/-- `Γ(z+j) = (z)(z+1)⋯(z+j-1)·Γ(z)`: the functional equation `j` times. The hypothesis
`0 < Re z` is what keeps every intermediate argument away from the pole. -/
theorem Gamma_add_natCast {z : ℂ} (hz : 0 < z.re) (j : ℕ) :
    Complex.Gamma (z + j) = (∏ i ∈ Finset.range j, (z + (i : ℂ))) * Complex.Gamma z := by
  induction j with
  | zero => simp
  | succ k ih =>
      have hne : z + (k : ℂ) ≠ 0 := by
        intro h
        have hre : (z + (k : ℂ)).re = 0 := by rw [h]; simp
        rw [Complex.add_re, Complex.natCast_re] at hre
        have := Nat.cast_nonneg (α := ℝ) k
        linarith
      rw [show z + ((k + 1 : ℕ) : ℂ) = (z + (k : ℂ)) + 1 by push_cast; ring,
        Complex.Gamma_add_one _ hne, ih, Finset.prod_range_succ]
      ring

/-- The Euler factor with its sign pulled out: `E_j(z) = (-1)ʲ (z)(z+1)⋯(z+j-1)`. -/
theorem mellinEulerFactor_eq_neg_one_pow_mul_prod (j : ℕ) (z : ℂ) :
    mellinEulerFactor j z = (-1) ^ j * ∏ i ∈ Finset.range j, (z + (i : ℂ)) := by
  have h : ∀ i ∈ Finset.range j, -z - (i : ℂ) = (-1) * (z + (i : ℂ)) := fun i _ => by ring
  rw [mellinEulerFactor, Finset.prod_congr rfl h, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_range]

/-- The Mellin transform of a finite sum, given that each summand converges. -/
theorem mellin_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ) (z : ℂ)
    (hf : ∀ i ∈ s, MellinConvergent (f i) z) :
    mellin (fun x => ∑ i ∈ s, f i x) z = ∑ i ∈ s, mellin (f i) z := by
  simp only [mellin]
  rw [← integral_finsetSum s fun i hi => hf i hi]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  simp only [smul_eq_mul]
  exact Finset.mul_sum _ _ _

theorem measurable_toNNReal_pow (j : ℕ) : Measurable fun t : ℝ => Real.toNNReal (t ^ j) :=
  Measurable.real_toNNReal (by fun_prop)

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent)

/-! ## The weighted law, and `lem:mellin-data` on it

`∂ₓʲ H(sx)` is, up to the constant `(-s)ʲ`, the Laplace transform of `tʲ μ(dt)`. Writing that
measure down is all it takes to reuse chapter 11's Gamma-integral hinge, now that the hinge is
stated for a measure rather than for `T₁`. -/

/-- The law of `T₁` weighted by `tʲ`.

The density is written through `Real.toNNReal` rather than as `ENNReal.ofReal` --- the same term,
unfolded one step --- because that is the shape `integral_withDensity_eq_integral_smul` matches
against. -/
noncomputable def weightedLawT₁ (j : ℕ) : Measure ℝ :=
  F.lawT₁.withDensity fun t => ((Real.toNNReal (t ^ j) : ℝ≥0) : ℝ≥0∞)

theorem coe_toNNReal_pow (t : ℝ) (j : ℕ) :
    ((Real.toNNReal (t ^ j) : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (t ^ j) := rfl

instance instSFiniteWeightedLawT₁ (j : ℕ) : SFinite (F.weightedLawT₁ j) := by
  rw [weightedLawT₁]; infer_instance

/-- **`E[T₁ʲ e^{-xT₁}]`**, the integral `ProfileDeriv.lean` leaves the `j`-th derivative of the
profile as. It is the Laplace transform of `weightedLawT₁ j`, which is the point of naming it. -/
noncomputable def weightedProfile (j : ℕ) (x : ℝ) : ℝ :=
  ∫ t, t ^ j * Real.exp (-(x * t)) ∂F.lawT₁

theorem ae_mem_Ioi_weightedLawT₁ (h0 : F.lawT₁ {(0 : ℝ)} = 0) (j : ℕ) :
    ∀ᵐ t ∂F.weightedLawT₁ j, t ∈ Ioi (0 : ℝ) := by
  rw [weightedLawT₁]
  exact (withDensity_absolutelyContinuous _ _).ae_le (F.ae_mem_Ioi_lawT₁ h0)

theorem laplace_weightedLawT₁ (h0 : F.lawT₁ {(0 : ℝ)} = 0) (j : ℕ) (x : ℝ) :
    laplace (F.weightedLawT₁ j) x = F.weightedProfile j x := by
  rw [laplace, weightedLawT₁,
    integral_withDensity_eq_integral_smul (measurable_toNNReal_pow j), weightedProfile]
  refine integral_congr_ae ?_
  filter_upwards [F.ae_mem_Ioi_lawT₁ h0] with t ht
  have ht' : (0 : ℝ) < t := ht
  rw [NNReal.smul_def, Real.coe_toNNReal (t ^ j) (by positivity), smul_eq_mul]

theorem lintegral_rpow_neg_weightedLawT₁ (h0 : F.lawT₁ {(0 : ℝ)} = 0) (j : ℕ) (c : ℝ) :
    ∫⁻ t, ENNReal.ofReal (t ^ (-c)) ∂F.weightedLawT₁ j = F.negMoment (c - j) := by
  rw [weightedLawT₁, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop),
    F.negMoment_eq_lintegral h0]
  refine lintegral_congr_ae ?_
  filter_upwards [F.ae_mem_Ioi_lawT₁ h0] with t ht
  have ht' : (0 : ℝ) < t := ht
  rw [Pi.mul_apply, coe_toNNReal_pow, ← ENNReal.ofReal_mul (by positivity),
    ← Real.rpow_natCast t j, ← Real.rpow_add ht']
  congr 1
  ring_nf

theorem integral_cpow_neg_weightedLawT₁ (h0 : F.lawT₁ {(0 : ℝ)} = 0) (j : ℕ) (z : ℂ) :
    ∫ t, (t : ℂ) ^ (-z) ∂F.weightedLawT₁ j = ∫ t, (t : ℂ) ^ ((j : ℂ) - z) ∂F.lawT₁ := by
  rw [weightedLawT₁, integral_withDensity_eq_integral_smul (measurable_toNNReal_pow j)]
  refine integral_congr_ae ?_
  filter_upwards [F.ae_mem_Ioi_lawT₁ h0] with t ht
  have ht' : (0 : ℝ) < t := ht
  have htne : (t : ℂ) ≠ 0 := by exact_mod_cast ht'.ne'
  rw [NNReal.smul_def, Real.coe_toNNReal (t ^ j) (by positivity), Complex.real_smul,
    show ((j : ℂ) - z) = (j : ℂ) + -z from by ring, Complex.cpow_add _ _ htne,
    Complex.cpow_natCast]
  push_cast
  ring

/-- **`lem:mellin-data` on the weighted law**: `M[x ↦ ∫ tʲ e^{-xt} dμ(t)](z) = Γ(z)·∫ t^{j-z} dμ`.

The strip has moved by `j`, as it must: the weight makes the integrand larger at infinity and
the moment that has to converge is `E[T₁^{j-Re z}]`. -/
theorem mellin_weightedProfile (hH : F.StandingHypothesis) (j : ℕ) {z : ℂ}
    (hz : 0 < z.re - j) (hz' : z.re - j < F.zStar) :
    mellin (fun x : ℝ => (F.weightedProfile j x : ℂ)) z
      = Complex.Gamma z * ∫ t, (t : ℂ) ^ ((j : ℂ) - z) ∂F.lawT₁ := by
  have h0 := F.lawT₁_singleton_zero hH.1
  have hzre : 0 < z.re := by have := Nat.cast_nonneg (α := ℝ) j; linarith
  have hfin : ∫⁻ t, ENNReal.ofReal (t ^ (-z.re)) ∂F.weightedLawT₁ j ≠ ⊤ := by
    rw [F.lintegral_rpow_neg_weightedLawT₁ h0]
    exact F.negMoment_ne_top_of_lt_zStar hz hz'
  rw [show (fun x : ℝ => ((F.weightedProfile j x : ℝ) : ℂ))
      = fun x : ℝ => ((laplace (F.weightedLawT₁ j) x : ℝ) : ℂ) from
    funext fun x => by rw [F.laplace_weightedLawT₁ h0],
    mellin_laplace_of_ae_mem_Ioi (F.ae_mem_Ioi_weightedLawT₁ h0 j) hzre hfin,
    F.integral_cpow_neg_weightedLawT₁ h0]

theorem mellinConvergent_weightedProfile (hH : F.StandingHypothesis) (j : ℕ) {z : ℂ}
    (hz : 0 < z.re - j) (hz' : z.re - j < F.zStar) :
    MellinConvergent (fun x : ℝ => (F.weightedProfile j x : ℂ)) z := by
  have h0 := F.lawT₁_singleton_zero hH.1
  have hzre : 0 < z.re := by have := Nat.cast_nonneg (α := ℝ) j; linarith
  have hfin : ∫⁻ t, ENNReal.ofReal (t ^ (-z.re)) ∂F.weightedLawT₁ j ≠ ⊤ := by
    rw [F.lintegral_rpow_neg_weightedLawT₁ h0]
    exact F.negMoment_ne_top_of_lt_zStar hz hz'
  rw [show (fun x : ℝ => ((F.weightedProfile j x : ℝ) : ℂ))
      = fun x : ℝ => ((laplace (F.weightedLawT₁ j) x : ℝ) : ℂ) from
    funext fun x => by rw [F.laplace_weightedLawT₁ h0]]
  exact mellinConvergent_laplace_of_ae_mem_Ioi (F.ae_mem_Ioi_weightedLawT₁ h0 j) hzre hfin

/-! ## The engine -/

/-- The derivative side of the profile clause, with the constant and the dilation displayed:
on `(0,∞)`, `∂ᵥʲ H(sv)|_{v=x} = (-s)ʲ · (weighted profile at `sx`)`. -/
theorem iteratedDeriv_profileC_eq_weightedProfile {s : ℝ} (hs : 0 < s) (j : ℕ) {x : ℝ}
    (hx : 0 < x) :
    iteratedDeriv j (fun v : ℝ => (F.profile (s * v) : ℂ)) x
      = ((((-s) ^ j : ℝ)) : ℂ) * ((F.weightedProfile j (s * x) : ℝ) : ℂ) := by
  rw [F.iteratedDeriv_profileC_comp_mul hs j hx, Complex.ofReal_mul, weightedProfile]

/-- **`lem:local-polynomial-symbol`'s engine, on the profile class.**
`M[x ↦ xʲ ∂ₓʲ H(sx)](w) = E_j(w) · M[H(s·)](w)`.

No integration by parts: the derivative is already an integral, the weight `xʲ` is a Mellin
shift, and the dilation is a factor. What is left is `lem:mellin-data` on `tʲ μ(dt)` and the
functional equation of `Γ`. -/
theorem mellin_pow_mul_iteratedDeriv_profile (hH : F.StandingHypothesis) {s : ℝ} (hs : 0 < s)
    (j : ℕ) {w : ℂ} (hw : 0 < w.re) (hw' : w.re < F.zStar) :
    mellin (fun x : ℝ => (x : ℂ) ^ j *
        iteratedDeriv j (fun v : ℝ => (F.profile (s * v) : ℂ)) x) w
      = mellinEulerFactor j w * mellin (fun u : ℝ => (F.profile (s * u) : ℂ)) w := by
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hshift : (w + (j : ℂ)).re - j = w.re := by simp
  -- the integrand, rewritten so that the weight and the dilation are visible
  have hstep : mellin (fun x : ℝ => (x : ℂ) ^ j *
        iteratedDeriv j (fun v : ℝ => (F.profile (s * v) : ℂ)) x) w
      = mellin (fun x : ℝ => (x : ℂ) ^ (j : ℂ) •
          (((((-s) ^ j : ℝ)) : ℂ) • ((F.weightedProfile j (s * x) : ℝ) : ℂ))) w := by
    rw [mellin, mellin]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    rw [F.iteratedDeriv_profileC_eq_weightedProfile hs j (mem_Ioi.mp hx)]
    simp only [smul_eq_mul, Complex.cpow_natCast]
  rw [hstep, mellin_cpow_smul, mellin_const_smul,
    mellin_comp_mul_left (fun y : ℝ => ((F.weightedProfile j y : ℝ) : ℂ)) (w + (j : ℂ)) hs,
    F.mellin_weightedProfile hH j (by rw [hshift]; exact hw) (by rw [hshift]; exact hw'),
    F.mellin_profile_comp_mul hs w, F.mellin_profile hH hw hw',
    mellinEulerFactor_eq_neg_one_pow_mul_prod, Gamma_add_natCast hw j]
  have hcombine : ((((-s) ^ j : ℝ)) : ℂ) * (s : ℂ) ^ (-(w + (j : ℂ)))
      = (-1) ^ j * (s : ℂ) ^ (-w) := by
    have hsj : ((((-s) ^ j : ℝ)) : ℂ) = (-1) ^ j * (s : ℂ) ^ (j : ℂ) := by
      rw [Complex.cpow_natCast]
      push_cast
      ring
    rw [hsj, mul_assoc, ← Complex.cpow_add _ _ hs0,
      show (j : ℂ) + -(w + (j : ℂ)) = -w from by ring]
  have hcast : ((j : ℂ)) - (w + (j : ℂ)) = -w := by ring
  rw [hcast, smul_eq_mul, smul_eq_mul, ← mul_assoc, hcombine]
  ring

/-- Each term of the differential expression has a convergent Mellin integral on the strip, which
is what lets the transform be taken term by term. -/
theorem mellinConvergent_pow_mul_iteratedDeriv_profile (hH : F.StandingHypothesis) {s : ℝ}
    (hs : 0 < s) (j : ℕ) {w : ℂ} (hw : 0 < w.re) (hw' : w.re < F.zStar) :
    MellinConvergent (fun x : ℝ => (x : ℂ) ^ j *
      iteratedDeriv j (fun v : ℝ => (F.profile (s * v) : ℂ)) x) w := by
  have hshift : (w + (j : ℂ)).re - j = w.re := by simp
  have hbase : MellinConvergent
      (fun x : ℝ => ((F.weightedProfile j (s * x) : ℝ) : ℂ)) (w + (j : ℂ)) :=
    (MellinConvergent.comp_mul_left hs).mpr
      (F.mellinConvergent_weightedProfile hH j (by rw [hshift]; exact hw)
        (by rw [hshift]; exact hw'))
  have hsmul : MellinConvergent (fun x : ℝ => (x : ℂ) ^ (j : ℂ) •
      (((((-s) ^ j : ℝ)) : ℂ) • ((F.weightedProfile j (s * x) : ℝ) : ℂ))) w :=
    MellinConvergent.cpow_smul.mpr (hbase.const_smul _)
  refine hsmul.congr_fun (fun x hx => ?_) measurableSet_Ioi
  dsimp only
  rw [F.iteratedDeriv_profileC_eq_weightedProfile hs j (mem_Ioi.mp hx)]
  simp only [smul_eq_mul, Complex.cpow_natCast]

/-! ## From locality to the symbol

The profile clause of `def:locality-pmp` gives one reading of `A[H(s·)]` and
`lem:profile-eigenfunction` gives another. Equating them is a pointwise identity on `(0,∞)`, in
which the height `c` of the contour no longer appears --- which is why locality tested at a
*single* height settles the symbol on the whole strip. -/

/-- **The two readings of `A[H(s·)]`, equated.** On `(0,∞)`,
`s·x·H(sx) = ∑_j γ_j xʲ ∂ₓʲ H(sx)`, with `γ_j = c_j(1)`.

The weight `x` is what turns `c_j(x) = γ_j x^{j-1}` into the Euler form `γ_j xʲ`; it is the same
`x⁻¹` of `def:inversion-operator`, cleared. -/
theorem mul_profile_eq_sum_of_isLocalOfOrder (hH : F.StandingHypothesis) {c : ℝ} (hc : 0 < c)
    (hc' : c < F.zStar - 1) {n : ℕ} (hL : F.IsLocalOfOrder c n) {s : ℝ} (hs : 0 < s) {x : ℝ}
    (hx : 0 < x) :
    (s : ℂ) * (x : ℂ) * (F.profile (s * x) : ℂ)
      = ∑ j ∈ Finset.range (n + 1), hL.coeff j 1 *
          ((x : ℂ) ^ j * iteratedDeriv j (fun v : ℝ => (F.profile (s * v) : ℂ)) x) := by
  have hxne : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have key : (s : ℂ) * (F.profile (s * x) : ℂ)
      = ∑ j ∈ Finset.range (n + 1), hL.coeff j x *
          iteratedDeriv j (fun u : ℝ => (F.profile (s * u) : ℂ)) x :=
    (F.inversionOperator_profile hH hc (by linarith) hs hx).symm.trans
      (hL.eq_sum_iteratedDeriv_profile hs hx)
  calc (s : ℂ) * (x : ℂ) * (F.profile (s * x) : ℂ)
      = (x : ℂ) * ((s : ℂ) * (F.profile (s * x) : ℂ)) := by ring
    _ = (x : ℂ) * ∑ j ∈ Finset.range (n + 1), hL.coeff j x *
          iteratedDeriv j (fun u : ℝ => (F.profile (s * u) : ℂ)) x := by rw [key]
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [F.coeff_eq_of_isLocalOfOrder hL.toIsLocalOfOrderCore
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hx, zpow_sub₀ hxne, zpow_natCast, zpow_one]
        field_simp

/-- **The transform-level identity.** `h̃(w) = P(w)·g̃(w)` on the strip, for the profile dilate
`g = H(s·)` and its realising function `h(x) = s x H(sx)`.

The engine term by term, with `mellin_finset_sum` splitting the sum --- which is licensed by the
convergence of each term and not by any estimate on the whole. -/
theorem mellin_profile_weight_eq_of_isLocalOfOrder (hH : F.StandingHypothesis) {c : ℝ}
    (hc : 0 < c) (hc' : c < F.zStar - 1) {n : ℕ} (hL : F.IsLocalOfOrder c n) {s : ℝ} (hs : 0 < s)
    {w : ℂ} (hw : 0 < w.re) (hw' : w.re < F.zStar) :
    mellin (fun x : ℝ => (s : ℂ) * (x : ℂ) * (F.profile (s * x) : ℂ)) w
      = (∑ j ∈ Finset.range (n + 1), hL.coeff j 1 * mellinEulerFactor j w) *
        mellin (fun u : ℝ => (F.profile (s * u) : ℂ)) w := by
  have hcongr : mellin (fun x : ℝ => (s : ℂ) * (x : ℂ) * (F.profile (s * x) : ℂ)) w
      = mellin (fun x : ℝ => ∑ j ∈ Finset.range (n + 1), hL.coeff j 1 *
          ((x : ℂ) ^ j * iteratedDeriv j (fun v : ℝ => (F.profile (s * v) : ℂ)) x)) w := by
    rw [mellin, mellin]
    exact setIntegral_congr_fun measurableSet_Ioi fun x hx => by
      rw [F.mul_profile_eq_sum_of_isLocalOfOrder hH hc hc' hL hs (mem_Ioi.mp hx)]
  have hconv : ∀ j ∈ Finset.range (n + 1), MellinConvergent (fun x : ℝ => hL.coeff j 1 *
      ((x : ℂ) ^ j * iteratedDeriv j (fun v : ℝ => (F.profile (s * v) : ℂ)) x)) w := by
    intro j _
    simpa only [smul_eq_mul] using
      (F.mellinConvergent_pow_mul_iteratedDeriv_profile hH hs j hw hw').const_smul
        (hL.coeff j 1)
  rw [hcongr, mellin_finset_sum _ _ _ hconv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hterm : mellin (fun x : ℝ => hL.coeff j 1 *
      ((x : ℂ) ^ j * iteratedDeriv j (fun v : ℝ => (F.profile (s * v) : ℂ)) x)) w
      = hL.coeff j 1 * mellin (fun x : ℝ => (x : ℂ) ^ j *
          iteratedDeriv j (fun v : ℝ => (F.profile (s * v) : ℂ)) x) w := by
    simpa only [smul_eq_mul] using
      mellin_const_smul (fun x : ℝ => (x : ℂ) ^ j *
        iteratedDeriv j (fun v : ℝ => (F.profile (s * v) : ℂ)) x) w (hL.coeff j 1)
  rw [hterm, F.mellin_pow_mul_iteratedDeriv_profile hH hs j hw hw']
  ring

/-- **The recursion `H̃(z+1) = P(z)·H̃(z)`, at every point of the strip and with no side
condition.**

This is the honest form of "the symbol is the polynomial `P`", and it is the form
`lem:moment-recursion` consumes: that lemma's clause (2) argues from the recursion *as an identity
between analytic functions*, never from a value of `B` at a point. Reading `B = P` off it requires
dividing by `H̃(z)`, which is legitimate exactly where the denominator does not vanish. -/
theorem mellin_profile_shift_eq_of_isLocalOfOrder (hH : F.StandingHypothesis) {c : ℝ}
    (hc : 0 < c) (hc' : c < F.zStar - 1) {n : ℕ} (hL : F.IsLocalOfOrder c n) {z : ℂ}
    (hz : 0 < z.re) (hz' : z.re < F.zStar - 1) :
    mellin (fun u : ℝ => (F.profile u : ℂ)) (z + 1)
      = (∑ j ∈ Finset.range (n + 1), hL.coeff j 1 * mellinEulerFactor j z) *
        mellin (fun u : ℝ => (F.profile u : ℂ)) z := by
  have key := F.mellin_profile_weight_eq_of_isLocalOfOrder hH hc hc' hL one_pos hz (by linarith)
  rw [F.mellin_profile_comp_mul_weight one_pos z, F.mellin_profile_comp_mul one_pos z] at key
  simpa only [Complex.ofReal_one, Complex.one_cpow, one_mul] using key

/-- The polynomial symbol realises the action on the profile dilate, at every admissible height.

`RealisesAction`'s two analytic fields are the profile instance's own --- the realising function
is the same one --- so what has to be supplied is only the transform identity, which is the
display above. -/
theorem realisesAction_sum_mellinEulerFactor (hH : F.StandingHypothesis) {c : ℝ} (hc : 0 < c)
    (hc' : c < F.zStar - 1) {n : ℕ} (hL : F.IsLocalOfOrder c n) {s : ℝ} (hs : 0 < s) {c' : ℝ}
    (hc0 : 0 < c') (hc1 : c' + 1 < F.zStar) :
    F.RealisesAction c'
      (fun z => ∑ j ∈ Finset.range (n + 1), hL.coeff j 1 * mellinEulerFactor j z)
      (fun u : ℝ => (F.profile (s * u) : ℂ))
      (fun x : ℝ => (s : ℂ) * (x : ℂ) * (F.profile (s * x) : ℂ)) where
  mellin_eq := by
    intro y _
    have hre : ((c' : ℂ) + y * Complex.I).re = c' := by simp
    exact F.mellin_profile_weight_eq_of_isLocalOfOrder hH hc hc' hL hs
      (by rw [hre]; exact hc0) (by rw [hre]; linarith)
  convergent := F.mellinConvergent_profile_comp_mul_weight hH hc0 hc1 hs
  verticalIntegrable := F.verticalIntegrable_mellin_profile_comp_mul_weight hH hc0 hc1 hs

/-- The symbol and the polynomial act identically on the profile: `lem:symbol-uniqueness`'s
hypothesis, supplied by locality. -/
theorem sameSymbolAction_of_isLocalOfOrder (hH : F.StandingHypothesis) {c : ℝ} (hc : 0 < c)
    (hc' : c < F.zStar - 1) {n : ℕ} (hL : F.IsLocalOfOrder c n) :
    F.SameSymbolAction F.inversionSymbol
      (fun z => ∑ j ∈ Finset.range (n + 1), hL.coeff j 1 * mellinEulerFactor j z) :=
  F.sameSymbolAction_of_realisesAction one_pos
    (fun _ hc₀ hc₁ => F.realisesSymbolAction_profile hH hc₀ hc₁ one_pos)
    (fun _ hc₀ hc₁ => F.realisesAction_sum_mellinEulerFactor hH hc hc' hL one_pos hc₀ hc₁)

/-- **`lem:local-polynomial-symbol`, the (⇒) direction, as a meromorphic identity.** `B` and `P`
agree near every point of the strip, the point itself excepted --- `lem:symbol-rigidity`'s reading
of "equal on the strip", and the unconditional one. -/
theorem eventuallyEq_inversionSymbol_of_isLocalOfOrder (hH : F.StandingHypothesis) {c : ℝ}
    (hc : 0 < c) (hc' : c < F.zStar - 1) {n : ℕ} (hL : F.IsLocalOfOrder c n) {z : ℂ}
    (hz : z ∈ verticalStrip 0 (F.zStar - 1)) :
    F.inversionSymbol
      =ᶠ[𝓝[≠] z] fun w => ∑ j ∈ Finset.range (n + 1), hL.coeff j 1 * mellinEulerFactor j w :=
  (F.sameSymbolAction_of_isLocalOfOrder hH hc hc' hL).eventuallyEq hH hz

/-- **`lem:local-polynomial-symbol`, the (⇒) direction.** Locality forces the symbol to be a
polynomial, and covariance forces the coefficients to be `γ_j x^{j-1}`.

Unlike the (⇐) direction this one is stated under (H), because the covariance argument runs
through `lem:mellin-data`, which needs it.

**The symbol clause carries `H̃(z) ≠ 0`, and it has to.** What the argument delivers everywhere is
the recursion `H̃(z+1) = P(z)H̃(z)` (`mellin_profile_shift_eq_of_isLocalOfOrder`); `B` is that
recursion divided by `H̃(z)`, and at a zero of `H̃` the quotient `H̃(z+1)/0` is Lean's `0` while
`P(z)` is a polynomial value. The zeros are isolated but nothing available rules them out --- `H̃`
is known nonzero only at the *real* points of the strip. The meromorphic reading, which needs no
side condition, is `eventuallyEq_inversionSymbol_of_isLocalOfOrder`. -/
theorem exists_symbol_eq_of_isLocalOfOrder (hH : F.StandingHypothesis) {c : ℝ} (hc : 0 < c)
    (hc' : c < F.zStar - 1) {n : ℕ} (hL : F.IsLocalOfOrder c n) :
    ∃ γ : ℕ → ℂ, γ n ≠ 0 ∧
      (∀ j ∈ Finset.range (n + 1), ∀ x : ℝ, 0 < x →
        hL.coeff j x = γ j * (x : ℂ) ^ ((j : ℤ) - 1)) ∧
      (∀ z : ℂ, 0 < z.re → z.re < F.zStar - 1 →
        mellin (fun s => (F.profile s : ℂ)) z ≠ 0 →
        F.inversionSymbol z = ∑ j ∈ Finset.range (n + 1), γ j * mellinEulerFactor j z) := by
  refine ⟨fun j => hL.coeff j 1, ?_, ?_, ?_⟩
  · -- the leading coefficient is nonzero at `1` because it is nonzero somewhere
    obtain ⟨x₀, hx₀, hne⟩ := hL.leading_ne_zero
    intro h
    refine hne ?_
    rw [F.coeff_eq_of_isLocalOfOrder hL.toIsLocalOfOrderCore le_rfl hx₀,
      show hL.coeff n 1 = 0 from h, zero_mul]
  · -- covariance, which is `coeff_eq_of_isLocalOfOrder`
    intro j hj x hx
    exact F.coeff_eq_of_isLocalOfOrder hL.toIsLocalOfOrderCore
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hx
  · -- the symbol identity, off the zeros of `H̃`
    intro z hz hz' hne
    exact (F.sameSymbolAction_of_isLocalOfOrder hH hc hc' hL).eqOn_of_ne_zero ⟨⟨hz, hz'⟩, hne⟩

end SelfDecomposableExponent

end Hemigroup
