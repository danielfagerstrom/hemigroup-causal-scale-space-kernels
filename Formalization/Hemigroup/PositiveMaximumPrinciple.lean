/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.LocalOperator
import Hemigroup.ProfileDeriv

/-!
# The positive maximum principle, verified

Blueprint: the PMP step of `thm:locality`'s (⇐) direction (12.5), which that node's Assignment
calls "two lines of calculus".

## Which step this is, and which it is not

`thm:locality` uses the maximum principle twice, in opposite directions and at opposite costs.

* **(⇒), the order bound.** That a local operator satisfying the PMP is a pure second-order
  diffusion --- `deg B ≤ 2`, no jump part --- is Courrège's classification, ledger **A14**. It is
  cited and stays cited; nothing here touches it.
* **(⇐), the verification.** That the operators the theorem exhibits *do* satisfy the PMP is
  elementary, and is what is proved here: at an interior nonnegative maximum the first derivative
  vanishes and the second is nonpositive, so a differential expression of order at most two with
  no killing term and a nonnegative leading coefficient takes a nonpositive value there.

The two are not the same statement and do not cost the same, which is why the ledger entry sits
on one of them alone.

## What Mathlib does not have

`IsLocalMax.deriv_eq_zero` is Mathlib's; the **second**-derivative half is not, and neither is any
second-derivative test at a local extremum. `deriv_deriv_nonpos_of_isLocalMax` below is written
from scratch, and the argument is the classical one: if `f''(a) > 0` then the slope of `f'` at `a`
is eventually positive, so `f' > 0` just to the right of `a`, so `f` is strictly increasing there
--- contradicting the maximum. It is stated for a general real function rather than for a test
function, mentions nothing of this development, and should reduce to Lean core.

## Where the real-valued reading is paid for

`def:locality-pmp`'s Lean form quantifies over real-valued test functions and asserts
`Re (Ag)(x₀) ≤ 0`, the operator being `ℂ`-valued. So the differential expression has to be pushed
through `Complex.re`, and the derivatives of `x ↦ (g x : ℂ)` identified with those of `g`. That is
`iteratedDeriv_ofReal_comp`, already proved for the profile, applied on `univ` where a test
function is smooth --- the one place this file leaves the two-line argument.
-/

namespace Hemigroup

open MeasureTheory Set Filter
open scoped Topology

/-! ## The second-derivative test at a local maximum -/

/-- **At a local maximum the second derivative is nonpositive.**

Mathlib carries `IsLocalMax.deriv_eq_zero` and nothing for the second derivative. The proof is the
classical one: were `f''(a)` positive, the slope of `f'` at `a` would be eventually positive, hence
`f' > 0` on an interval to the right of `a`, hence `f` strictly increasing there --- and `a` is a
maximum. -/
theorem deriv_deriv_nonpos_of_isLocalMax {f : ℝ → ℝ} {a : ℝ} (hmax : IsLocalMax f a)
    (hf : Differentiable ℝ f) (hf' : DifferentiableAt ℝ (deriv f) a) :
    deriv (deriv f) a ≤ 0 := by
  by_contra hcon
  push_neg at hcon
  have hd0 : deriv f a = 0 := hmax.deriv_eq_zero
  -- the slope of `f'` at `a` is eventually positive
  have hslope : Tendsto (slope (deriv f) a) (𝓝[≠] a) (𝓝 (deriv (deriv f) a)) :=
    hasDerivAt_iff_tendsto_slope.mp hf'.hasDerivAt
  have hne : ∀ᶠ y in 𝓝[>] a, 0 < slope (deriv f) a y := by
    have hmem : ∀ᶠ y in 𝓝[≠] a, 0 < slope (deriv f) a y :=
      hslope.eventually (eventually_gt_nhds hcon)
    exact hmem.filter_mono (nhdsWithin_mono a fun y hy => ne_of_gt hy)
  -- so `f'` itself is eventually positive to the right of `a`
  have hpos : ∀ᶠ y in 𝓝[>] a, 0 < deriv f y := by
    filter_upwards [hne, self_mem_nhdsWithin] with y hy hy0
    have hya : 0 < y - a := sub_pos.mpr hy0
    rw [slope_def_field, hd0, sub_zero, lt_div_iff₀ hya, zero_mul] at hy
    exact hy
  -- and `f` is dominated by `f a` there
  have hle : ∀ᶠ y in 𝓝[>] a, f y ≤ f a := hmax.filter_mono nhdsWithin_le_nhds
  obtain ⟨b, hab, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hpos.and hle)
  have hab' : a < b := hab
  set y₁ : ℝ := (a + b) / 2 with hy₁
  have hmem : y₁ ∈ Ioo a b := by
    constructor <;> rw [hy₁] <;> linarith [hab']
  have hstrict : StrictMonoOn f (Icc a y₁) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc a y₁) hf.continuous.continuousOn fun x hx => ?_
    rw [interior_Icc] at hx
    exact (hsub ⟨hx.1, lt_trans hx.2 hmem.2⟩).1
  have hlt : f a < f y₁ :=
    hstrict (left_mem_Icc.mpr hmem.1.le) (right_mem_Icc.mpr hmem.1.le) hmem.1
  exact absurd (hsub hmem).2 (not_le.mpr hlt)

/-- A real-valued test function is smooth as a real function: the complex one is, and `Complex.re`
is a continuous linear map. -/
theorem contDiff_of_isTestFunction_ofReal {g : ℝ → ℝ}
    (hg : IsTestFunction fun x => (g x : ℂ)) : ContDiff ℝ (⊤ : ℕ∞) g := by
  have hcomp : ContDiff ℝ (⊤ : ℕ∞) fun x : ℝ => ((g x : ℂ)).re :=
    Complex.reCLM.contDiff.comp hg.contDiff
  simpa using hcomp

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent)

/-! ## The verification -/

/-- **`thm:locality`(⇐), the PMP verification.**

A differential expression of order at most two satisfies the positive maximum principle as soon as
its killing coefficient has nonpositive real part and its leading one nonnegative. The first-order
coefficient is unconstrained, and that is the whole content of "at an interior maximum the first
derivative vanishes".

Ledger A14 --- Courrège --- is the *converse* direction, that the PMP forces order two, and is not
used here. -/
theorem satisfiesPMP_of_isLocalOfOrderCore {c : ℝ} {n : ℕ} (hL : F.IsLocalOfOrderCore c n)
    (hn : n ≤ 2) (h0 : ∀ x : ℝ, 0 < x → (hL.coeff 0 x).re ≤ 0)
    (h2 : 2 ≤ n → ∀ x : ℝ, 0 < x → 0 ≤ (hL.coeff 2 x).re) :
    F.SatisfiesPMP c := by
  intro g hg x₀ hx₀ hg0 hmaxOn
  have hgr : ContDiff ℝ (⊤ : ℕ∞) g := contDiff_of_isTestFunction_ofReal hg
  have hdiff : ∀ k : ℕ, Differentiable ℝ (iteratedDeriv k g) := fun k =>
    hgr.differentiable_iteratedDeriv k (by exact_mod_cast (by simp : (k : ℕ∞) < ⊤))
  -- the complex derivatives are the real ones
  have hcast : ∀ j : ℕ, iteratedDeriv j (fun x : ℝ => (g x : ℂ)) x₀
      = ((iteratedDeriv j g x₀ : ℝ) : ℂ) :=
    fun j => iteratedDeriv_ofReal_comp (f := g) isOpen_univ
      (fun k y _ => (hdiff k) y) j (mem_univ x₀)
  -- the jet of `g` at an interior nonnegative maximum
  have hmax : IsLocalMax g x₀ := by
    filter_upwards [isOpen_Ioi.mem_nhds (mem_Ioi.mpr hx₀)] with y hy
    exact hmaxOn y hy
  have hjet1 : iteratedDeriv 1 g x₀ = 0 := by
    rw [iteratedDeriv_one]
    exact hmax.deriv_eq_zero
  have hjet2 : iteratedDeriv 2 g x₀ ≤ 0 := by
    have hrw : iteratedDeriv 2 g = deriv (deriv g) := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
    have hg1 : Differentiable ℝ g := by simpa [iteratedDeriv_zero] using hdiff 0
    have hg2 : DifferentiableAt ℝ (deriv g) x₀ := by
      simpa [iteratedDeriv_one] using (hdiff 1) x₀
    rw [hrw]
    exact deriv_deriv_nonpos_of_isLocalMax hmax hg1 hg2
  -- the differential expression, in real parts
  rw [hL.eq_sum_iteratedDeriv hg hx₀, Complex.re_sum]
  have hterm : ∀ j : ℕ, (hL.coeff j x₀ * iteratedDeriv j (fun x : ℝ => (g x : ℂ)) x₀).re
      = (hL.coeff j x₀).re * iteratedDeriv j g x₀ := by
    intro j
    rw [hcast j]
    simp [Complex.mul_re]
  simp only [hterm]
  have hzero : iteratedDeriv 0 g x₀ = g x₀ := by rw [iteratedDeriv_zero]
  interval_cases n
  · rw [Finset.sum_range_one, hzero]
    exact mul_nonpos_of_nonpos_of_nonneg (h0 x₀ hx₀) hg0
  · rw [Finset.sum_range_succ, Finset.sum_range_one, hzero, hjet1, mul_zero, add_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (h0 x₀ hx₀) hg0
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, hzero, hjet1,
      mul_zero, add_zero]
    have hlead : (hL.coeff 2 x₀).re * iteratedDeriv 2 g x₀ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (h2 le_rfl x₀ hx₀) hjet2
    have hkill : (hL.coeff 0 x₀).re * g x₀ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (h0 x₀ hx₀) hg0
    linarith

/-- **`thm:locality`(⇐), the PMP verification, from the symbol.**

The form the theorem's two cases arrive in: a polynomial symbol `∑_{j≤n} γ_j E_j` of degree at
most two with no constant term --- `γ_0 = 0` is `lem:moment-recursion`(1), the absence of killing
--- and leading coefficient of nonnegative real part.

Case (1) of `thm:locality` is `n = 1`, where the leading hypothesis is vacuous: a first-order
operator satisfies the PMP for the single reason that `g'(x₀) = 0`. Case (2) is `n = 2` with
`γ_2 = 2 > 0`. -/
theorem satisfiesPMP_of_symbol_eq (hH : F.StandingHypothesis) {c : ℝ} (hc : 0 < c)
    (hc' : c < F.zStar - 1) {n : ℕ} (γ : ℕ → ℂ) (hγ : γ n ≠ 0)
    (hsymbol : ∀ z : ℂ, 0 < z.re → z.re < F.zStar - 1 →
      mellin (fun s => (F.profile s : ℂ)) z ≠ 0 →
      F.inversionSymbol z = ∑ j ∈ Finset.range (n + 1), γ j * mellinEulerFactor j z)
    (hn : n ≤ 2) (h0 : γ 0 = 0) (h2 : 2 ≤ n → 0 ≤ (γ 2).re) :
    F.SatisfiesPMP c := by
  refine F.satisfiesPMP_of_isLocalOfOrderCore
    (F.isLocalOfOrderCoreOfSymbolEq hH hc hc' γ hγ hsymbol) hn (fun x _ => ?_) (fun hn2 x hx => ?_)
  · rw [coeff_isLocalOfOrderCoreOfSymbolEq, h0, zero_mul, Complex.zero_re]
  · have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    rw [coeff_isLocalOfOrderCoreOfSymbolEq,
      show ((2 : ℕ) : ℤ) - 1 = 1 from by norm_num, zpow_one]
    have hre : (γ 2 * (x : ℂ)).re = (γ 2).re * x := by simp [Complex.mul_re]
    rw [hre]
    exact mul_nonneg (h2 hn2) hx.le

end SelfDecomposableExponent

end Hemigroup
