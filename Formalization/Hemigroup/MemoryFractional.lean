/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.MellinData
import Hemigroup.InversionSymbol
import Hemigroup.Instance
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The memory line stores fractional integrals

Blueprint: `lem:memory-fractional-integrals` (Lemma 11.5), the analytic core.

The claim is that the Mellin transform in `x` of the field `u(t,x)` is `H̃(z)` times the
Riemann–Liouville integral of order `z` of the past signal — so the memory line, read through the
Mellin transform at a fixed time, holds the whole analytic family `{(Iᶻf)(t)}` weighted by the
negative delay-moments.

## Two things the statement had to settle

**Mathlib has no fractional integral of any order.** `Analysis/` carries Mellin, Fourier,
convolution and distributions, and nothing fractional, so `riemannLiouville` is defined here. That
is a definition and not an interface: the article cites Samko–Kilbas–Marichev for the notation and
theory of `Iᶻ`, and chapter 11 uses no more of that theory than the definition itself.

**The field is `L¹`-valued and this lemma is pointwise in `t`.** `Φ_{x,y}` maps `X →L[ℝ] X` with
`X` an `L¹` space, and an `L¹` class has no value at a point. What is proved here is therefore the
*analytic core*: the integrand is written as `E[f(t - x T₁)]` for a genuine function `f`, and the
identification of that with `Φ_{0,x}f` — an a.e.-in-`t` statement, per the decision recorded in
`PLAN-chapters-8-12.md` — is separate. The core is what both readings of that decision need.

## Everything factors through one integral

`pastIntegral z f t = ∫₀^∞ y^{z-1} f(t-y) dy` is the object both sides go through, and once it is
named the lemma is two independent facts about it:

* `mul_riemannLiouville` — it *is* `Γ(z)(Iᶻf)(t)`, by reflecting `y ↦ t - y`. Causality is what
  makes the two integrals have the same domain: `f(t-y)` vanishes for `y > t`, so the integral over
  `(0,∞)` is already an integral over `(0,t]`.
* `mellin_delayed_average` — and it is the inner integral of the Fubini exchange, the dilation
  `x ↦ τx` contributing exactly the factor `τ^{-z}` whose expectation is `E[T₁^{-z}]`.

## Why `Re z > 1` here and `Re z > 0` in `lem:mellin-data`

The side condition is `∫₀^t y^{c-1}|f(t-y)|dy < ∞`, and for `c > 1` it is free: `y^{c-1} ≤ t^{c-1}`
on `(0,t]`, so the integral is at most `t^{c-1}‖f‖₁` with no hypothesis on `f` beyond `L¹`. At
`c ≤ 1` the weight blows up at the origin and integrability becomes a condition on `f` near `t`.
That gap is exactly why (H)'s second clause asks for `z_* > 1` rather than `z_* > 0`: below `1`
there is no strip for this lemma to live in, and Theorem 4′(2) would have nothing to say.
-/

namespace Hemigroup

open MeasureTheory Set Filter

open scoped Topology ENNReal

/-- The **Riemann–Liouville integral of complex order** `z`,
`(Iᶻf)(t) = Γ(z)⁻¹ ∫₀ᵗ (t-r)^{z-1} f(r) dr`.

Total in `z` and `t`: `Complex.Gamma` and `cpow` are total, so no side condition is carried in the
definition and the hypotheses live on the theorems — the convention `inversionOperator` also
follows. -/
noncomputable def riemannLiouville (z : ℂ) (f : ℝ → ℝ) (t : ℝ) : ℂ :=
  (Complex.Gamma z)⁻¹ * ∫ r in Ioc (0 : ℝ) t, ((t - r : ℝ) : ℂ) ^ (z - 1) * (f r : ℂ)

/-- The **past integral** `∫₀^∞ y^{z-1} f(t-y) dy`: the signal seen from `t`, weighted by the
Mellin character. Both sides of `lem:memory-fractional-integrals` factor through it. -/
noncomputable def pastIntegral (z : ℂ) (f : ℝ → ℝ) (t : ℝ) : ℂ :=
  ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (z - 1) * (f (t - y) : ℂ)

section PastIntegral

variable {f : ℝ → ℝ} {t : ℝ} {z : ℂ}

/-- Causality puts the past integral on a bounded interval: `f(t-y) = 0` once `y > t`. -/
theorem pastIntegrand_eq_zero (hcausal : ∀ r : ℝ, r < 0 → f r = 0) {y : ℝ} (hy : t < y) :
    (y : ℂ) ^ (z - 1) * (f (t - y) : ℂ) = 0 := by
  rw [hcausal (t - y) (by linarith), Complex.ofReal_zero, mul_zero]

/-- The past integrand is integrable on `(0,∞)` when `Re z > 1`.

Two pieces, and both are the reason the strip starts at `1`: beyond `t` the integrand vanishes by
causality, and on `(0,t]` the weight `y^{c-1}` is bounded by `t^{c-1}` because `c > 1`, so `f`
needs nothing beyond `L¹`. -/
theorem integrableOn_pastIntegrand (hz : 1 < z.re) (hf : Integrable f)
    (hcausal : ∀ r : ℝ, r < 0 → f r = 0) (ht : 0 < t) :
    IntegrableOn (fun y : ℝ => (y : ℂ) ^ (z - 1) * (f (t - y) : ℂ)) (Ioi 0) := by
  have hrefl : Integrable fun y : ℝ => f (t - y) := hf.comp_sub_left t
  have hIoc : IntegrableOn (fun y : ℝ => (y : ℂ) ^ (z - 1) * (f (t - y) : ℂ)) (Ioc 0 t) := by
    have hw : Measurable fun y : ℝ => (y : ℂ) ^ (z - 1) := by fun_prop
    have hmeas : AEStronglyMeasurable
        (fun y : ℝ => (y : ℂ) ^ (z - 1) * (f (t - y) : ℂ)) volume :=
      hw.aestronglyMeasurable.mul
        (Complex.continuous_ofReal.comp_aestronglyMeasurable hrefl.aestronglyMeasurable)
    refine Integrable.mono' (hrefl.norm.const_mul (t ^ (z.re - 1))).integrableOn hmeas.restrict ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (.of_forall fun y hy => ?_)
    obtain ⟨hy0, hyt⟩ := hy
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy0, Complex.norm_real]
    simp only [Complex.sub_re, Complex.one_re]
    gcongr
  have hIoi : IntegrableOn (fun y : ℝ => (y : ℂ) ^ (z - 1) * (f (t - y) : ℂ)) (Ioi t) := by
    refine (integrable_zero ℝ ℂ _).congr ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun y hy => ?_)
    exact (pastIntegrand_eq_zero hcausal (mem_Ioi.mp hy)).symm
  rw [← Ioc_union_Ioi_eq_Ioi ht.le]
  exact hIoc.union hIoi

/-- **Bounded `f` extends the strip down to `Re z > 0`.**

This is what `f ∈ 𝒟` supplies — absolutely continuous with `f' ∈ L¹` and `f(0) = 0` forces
`‖f‖_∞ ≤ ‖f'‖₁` — and it is what `thm:signaling-form`(2) needs, because that node applies
`lem:memory-fractional-integrals` at `z-1`. With `f` merely `L¹` the weight `y^{c-1}` has to be
absorbed by `t^{c-1}`, which needs `c > 1`; with `f` bounded the weight is integrable at the origin
on its own for every `c > 0`.

**The gap this closes is in the draft.** `lem:memory-fractional-integrals` states the range
`1 < Re z < z_*`, and `thm:signaling-form`(2) states the same range while applying that lemma at
`z-1` — which its stated range does not cover. The repair is not a change of result: (2)
hypothesises `f ∈ 𝒟`, which is bounded, so the lemma holds there for `0 < Re z < z_*` and the chain
closes. It is a gap in what the lemma *says*, not in what is true, and chaining the two surfaced
it. -/
theorem integrableOn_pastIntegrand_of_bounded (hz : 0 < z.re) {C : ℝ} (hfm : Measurable f)
    (hbdd : ∀ y : ℝ, |f y| ≤ C) (hcausal : ∀ r : ℝ, r < 0 → f r = 0) (ht : 0 < t) :
    IntegrableOn (fun y : ℝ => (y : ℂ) ^ (z - 1) * (f (t - y) : ℂ)) (Ioi 0) := by
  have hIoc : IntegrableOn (fun y : ℝ => (y : ℂ) ^ (z - 1) * (f (t - y) : ℂ)) (Ioc 0 t) := by
    have hw : IntegrableOn (fun y : ℝ => y ^ (z.re - 1) * C) (Ioc 0 t) := by
      have hr := intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := t)
        (r := z.re - 1) (by linarith)
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le] at hr
      exact hr.mul_const C
    have hmeas : AEStronglyMeasurable
        (fun y : ℝ => (y : ℂ) ^ (z - 1) * (f (t - y) : ℂ)) volume := by
      have h1 : Measurable fun y : ℝ => (y : ℂ) ^ (z - 1) := by fun_prop
      exact (h1.mul (Complex.measurable_ofReal.comp
        (hfm.comp (measurable_const_sub t)))).aestronglyMeasurable
    refine Integrable.mono' hw hmeas.restrict ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (.of_forall fun y hy => ?_)
    obtain ⟨hy0, hyt⟩ := hy
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy0, Complex.norm_real, Real.norm_eq_abs]
    simp only [Complex.sub_re, Complex.one_re]
    gcongr
    exact hbdd _
  have hIoi : IntegrableOn (fun y : ℝ => (y : ℂ) ^ (z - 1) * (f (t - y) : ℂ)) (Ioi t) := by
    refine (integrable_zero ℝ ℂ _).congr ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun y hy => ?_)
    exact (pastIntegrand_eq_zero hcausal (mem_Ioi.mp hy)).symm
  rw [← Ioc_union_Ioi_eq_Ioi ht.le]
  exact hIoc.union hIoi

/-- **The past integral is `Γ(z)` times the Riemann–Liouville integral.**

The reflection `y ↦ t - y`, and causality is what makes the domains match: the past integral over
`(0,∞)` is already an integral over `(0,t]`, which the reflection carries onto `(0,t]` again. -/
theorem mul_riemannLiouville (hz : 0 < z.re) (hcausal : ∀ r : ℝ, r < 0 → f r = 0) (ht : 0 < t)
    (hint : IntegrableOn (fun y : ℝ => (y : ℂ) ^ (z - 1) * (f (t - y) : ℂ)) (Ioi 0)) :
    Complex.Gamma z * riemannLiouville z f t = pastIntegral z f t := by
  have hsplit : pastIntegral z f t
      = ∫ y in Ioc (0 : ℝ) t, (y : ℂ) ^ (z - 1) * (f (t - y) : ℂ) := by
    rw [pastIntegral, ← Ioc_union_Ioi_eq_Ioi ht.le,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hint.mono_set (by rw [← Ioc_union_Ioi_eq_Ioi ht.le]; exact subset_union_left))
        (hint.mono_set (by rw [← Ioc_union_Ioi_eq_Ioi ht.le]; exact subset_union_right))]
    have hzero : ∫ y in Ioi t, (y : ℂ) ^ (z - 1) * (f (t - y) : ℂ) = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
      exact pastIntegrand_eq_zero hcausal (mem_Ioi.mp hy)
    rw [hzero, add_zero]
  have hrefl : ∫ y in Ioc (0 : ℝ) t, (y : ℂ) ^ (z - 1) * (f (t - y) : ℂ)
      = ∫ r in Ioc (0 : ℝ) t, ((t - r : ℝ) : ℂ) ^ (z - 1) * (f r : ℂ) := by
    rw [← intervalIntegral.integral_of_le ht.le, ← intervalIntegral.integral_of_le ht.le]
    have := intervalIntegral.integral_comp_sub_left
      (a := 0) (b := t) (fun r : ℝ => ((t - r : ℝ) : ℂ) ^ (z - 1) * (f r : ℂ)) t
    simpa using this
  rw [hsplit, hrefl, riemannLiouville, ← mul_assoc,
    mul_inv_cancel₀ (Complex.Gamma_ne_zero_of_re_pos hz), one_mul]

/-- The past integrand's norm, as a real function: `y^{c-1}|f(t-y)|`. -/
theorem integrableOn_pastNorm
    (hpast : IntegrableOn (fun y : ℝ => (y : ℂ) ^ (z - 1) * (f (t - y) : ℂ)) (Ioi 0)) :
    IntegrableOn (fun y : ℝ => y ^ (z.re - 1) * |f (t - y)|) (Ioi 0) := by
  have hn : IntegrableOn (fun y : ℝ => ‖(y : ℂ) ^ (z - 1) * (f (t - y) : ℂ)‖) (Ioi 0) :=
    hpast.norm
  refine hn.congr_fun (fun y hy => ?_) measurableSet_Ioi
  dsimp only
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (mem_Ioi.mp hy), Complex.norm_real,
    Real.norm_eq_abs]
  simp only [Complex.sub_re, Complex.one_re]

/-- **The dilation contributes exactly `τ^{-c}`.** The substitution `y = τ x`, on the norms, which
is the side condition of the Fubini exchange below. -/
theorem integral_pastNorm_comp_mul (c : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (∫ x in Ioi (0 : ℝ), x ^ (c - 1) * |f (t - x * τ)|)
      = τ ^ (-c) * ∫ y in Ioi (0 : ℝ), y ^ (c - 1) * |f (t - y)| := by
  have hsub := integral_comp_mul_left_Ioi (fun y : ℝ => y ^ (c - 1) * |f (t - y)|) 0 hτ
  rw [mul_zero] at hsub
  have hpt : ∀ x ∈ Ioi (0 : ℝ),
      (fun y : ℝ => y ^ (c - 1) * |f (t - y)|) (τ * x)
        = τ ^ (c - 1) * (x ^ (c - 1) * |f (t - x * τ)|) := by
    intro x hx
    dsimp only
    rw [Real.mul_rpow hτ.le (mem_Ioi.mp hx).le, mul_comm τ x, mul_assoc]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, smul_eq_mul] at hsub
  have hτ0 : (0 : ℝ) < τ ^ (c - 1) := Real.rpow_pos_of_pos hτ _
  have hinv : τ⁻¹ = τ ^ (-1 : ℝ) := by rw [Real.rpow_neg hτ.le, Real.rpow_one]
  have hpow : (τ ^ (c - 1))⁻¹ * τ⁻¹ = τ ^ (-c) := by
    rw [← Real.rpow_neg hτ.le, hinv, ← Real.rpow_add hτ]
    congr 1
    ring
  calc (∫ x in Ioi (0 : ℝ), x ^ (c - 1) * |f (t - x * τ)|)
      = (τ ^ (c - 1))⁻¹ * (τ ^ (c - 1) * ∫ x in Ioi (0 : ℝ), x ^ (c - 1) * |f (t - x * τ)|) := by
        rw [← mul_assoc, inv_mul_cancel₀ hτ0.ne', one_mul]
    _ = (τ ^ (c - 1))⁻¹ * (τ⁻¹ * ∫ y in Ioi (0 : ℝ), y ^ (c - 1) * |f (t - y)|) := by
        rw [hsub]
    _ = τ ^ (-c) * ∫ y in Ioi (0 : ℝ), y ^ (c - 1) * |f (t - y)| := by
        rw [← mul_assoc, hpow]

end PastIntegral

section Core

variable (F : SelfDecomposableExponent)

variable {F}

/-- **The Fubini side condition**: the delayed integrand is jointly integrable for
`volume|_(0,∞) ⊗ lawT₁`.

Both factors are in hand and the dilation is what couples them. Inside, the dilate of the past
integrand is integrable because `Re z > 1` (`integrableOn_pastIntegrand`); outside, the dilation
leaves exactly `τ^{-c}`, whose `lawT₁`-integral is `E[T₁^{-c}]`, finite because `Re z < z_*`. So
the exchange is licensed by the *two* ends of the strip at once, one apiece — the same shape as
`lem:mellin-data`'s hinge, with the lower end there being `0` rather than `1`.

`f` is asked to be measurable, not merely a.e.-measurable: the integrand composes `f` with
`(x,τ) ↦ t - xτ`, and a null set for `volume` need not pull back to one for the product measure —
`lawT₁` may have atoms. Choosing a measurable representative is free for an `L¹` class, so this
costs the article nothing. -/
theorem integrable_delayed (hH : F.StandingHypothesis) {z : ℂ} (hz : 0 < z.re)
    (hz' : ENNReal.ofReal z.re < F.zStar) {f : ℝ → ℝ} (hfm : Measurable f) {t : ℝ}
    (hpast : IntegrableOn (fun y : ℝ => (y : ℂ) ^ (z - 1) * (f (t - y) : ℂ)) (Ioi 0)) :
    Integrable (Function.uncurry fun x τ : ℝ => (x : ℂ) ^ (z - 1) * (f (t - x * τ) : ℂ))
      ((volume.restrict (Ioi 0)).prod F.lawT₁) := by
  have h0 := F.lawT₁_singleton_zero hH.1
  have hae := F.ae_mem_Ioi_lawT₁ h0
  have hmeas : Measurable
      (Function.uncurry fun x τ : ℝ => (x : ℂ) ^ (z - 1) * (f (t - x * τ) : ℂ)) := by
    unfold Function.uncurry
    fun_prop
  refine (integrable_prod_iff' hmeas.aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · filter_upwards [hae] with τ hτ
    have hbase : MellinConvergent (fun y : ℝ => ((f (t - y) : ℝ) : ℂ)) z := by
      simpa only [MellinConvergent, smul_eq_mul] using hpast
    have hdil := (MellinConvergent.comp_mul_left (f := fun y : ℝ => ((f (t - y) : ℝ) : ℂ))
      (s := z) (mem_Ioi.mp hτ)).mpr hbase
    have hdil' : IntegrableOn
        (fun x : ℝ => (x : ℂ) ^ (z - 1) * ((f (t - τ * x) : ℝ) : ℂ)) (Ioi 0) := by
      simpa only [MellinConvergent, smul_eq_mul] using hdil
    refine hdil'.congr_fun (fun x hx => ?_) measurableSet_Ioi
    dsimp only [Function.uncurry]
    rw [mul_comm τ x]
  · have heq : (fun τ : ℝ => ∫ x in Ioi (0 : ℝ),
          ‖Function.uncurry (fun x τ : ℝ => (x : ℂ) ^ (z - 1) * (f (t - x * τ) : ℂ)) (x, τ)‖)
        =ᵐ[F.lawT₁] fun τ : ℝ =>
          τ ^ (-z.re) * ∫ y in Ioi (0 : ℝ), y ^ (z.re - 1) * |f (t - y)| := by
      filter_upwards [hae] with τ hτ
      rw [← integral_pastNorm_comp_mul (f := f) (t := t) z.re (mem_Ioi.mp hτ)]
      refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
      rw [Function.uncurry_apply_pair, norm_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos (mem_Ioi.mp hx), Complex.norm_real, Real.norm_eq_abs]
      simp only [Complex.sub_re, Complex.one_re]
    refine Integrable.congr ?_ heq.symm
    exact (integrable_rpow_neg F hH (by linarith) hz').mul_const _

/-- **`lem:memory-fractional-integrals`**, the analytic core: the Mellin transform in `x` of the
delayed average `x ↦ E[f(t - xT₁)]` is `H̃(z)` times the Riemann–Liouville integral of order `z`.

Everything goes through `pastIntegral`. Fubini exchanges the two integrals; the inner one is then
a dilate, contributing `τ^{-z}` times the past integral, and the outer integral of `τ^{-z}` is
`E[T₁^{-z}]`. `lem:mellin-data` turns `Γ(z)E[T₁^{-z}]` into `H̃(z)` and `mul_riemannLiouville`
turns the past integral into `Γ(z)(Iᶻf)(t)`; the two `Γ`s cancel, which is why the statement has
no `Γ` in it. -/
theorem mellin_delayed_average (hH : F.StandingHypothesis) {z : ℂ} (hz : 0 < z.re)
    (hz' : ENNReal.ofReal z.re < F.zStar) {f : ℝ → ℝ} (hfm : Measurable f)
    (hcausal : ∀ r : ℝ, r < 0 → f r = 0) {t : ℝ} (ht : 0 < t)
    (hpast : IntegrableOn (fun y : ℝ => (y : ℂ) ^ (z - 1) * (f (t - y) : ℂ)) (Ioi 0)) :
    mellin (fun x : ℝ => ∫ τ, (f (t - x * τ) : ℂ) ∂F.lawT₁) z
      = mellin (fun s => (F.profile s : ℂ)) z * riemannLiouville z f t := by
  have h0 := F.lawT₁_singleton_zero hH.1
  have hae := F.ae_mem_Ioi_lawT₁ h0
  have hzpos : 0 < z.re := hz
  have hinner : ∀ x : ℝ, (x : ℂ) ^ (z - 1) • (∫ τ, (f (t - x * τ) : ℂ) ∂F.lawT₁)
      = ∫ τ, (x : ℂ) ^ (z - 1) * (f (t - x * τ) : ℂ) ∂F.lawT₁ := by
    intro x
    rw [integral_const_mul, smul_eq_mul]
  have hdil : ∀ τ : ℝ, 0 < τ →
      (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (z - 1) * (f (t - x * τ) : ℂ))
        = (τ : ℂ) ^ (-z) * pastIntegral z f t := by
    intro τ hτ
    have hmc := mellin_comp_mul_left (fun y : ℝ => ((f (t - y) : ℝ) : ℂ)) z hτ
    rw [smul_eq_mul] at hmc
    have hL : (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (z - 1) * (f (t - x * τ) : ℂ))
        = mellin (fun x : ℝ => ((f (t - τ * x) : ℝ) : ℂ)) z := by
      rw [mellin]
      refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
      rw [smul_eq_mul, mul_comm τ x]
    rw [hL, hmc, pastIntegral, mellin]
    simp only [smul_eq_mul]
  calc mellin (fun x : ℝ => ∫ τ, (f (t - x * τ) : ℂ) ∂F.lawT₁) z
      = ∫ x in Ioi (0 : ℝ), ∫ τ, (x : ℂ) ^ (z - 1) * (f (t - x * τ) : ℂ) ∂F.lawT₁ := by
        rw [mellin]
        exact setIntegral_congr_fun measurableSet_Ioi (fun x _ => hinner x)
    _ = ∫ τ, (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (z - 1) * (f (t - x * τ) : ℂ)) ∂F.lawT₁ :=
        integral_integral_swap (integrable_delayed hH hz hz' hfm hpast)
    _ = ∫ τ, (τ : ℂ) ^ (-z) * pastIntegral z f t ∂F.lawT₁ := by
        refine integral_congr_ae ?_
        filter_upwards [hae] with τ hτ using hdil τ (mem_Ioi.mp hτ)
    _ = (∫ τ, (τ : ℂ) ^ (-z) ∂F.lawT₁) * pastIntegral z f t := integral_mul_const _ _
    _ = mellin (fun s => (F.profile s : ℂ)) z * riemannLiouville z f t := by
        rw [F.mellin_profile hH hzpos hz', ← mul_riemannLiouville hzpos hcausal ht hpast]
        ring

end Core


/-! ## The fractional-integral identity `Iᶻf' = I^{z-1}f`

`lem:memory-fractional-integrals`' derivative clause, transform half. The draft derives it from
the semigroup property `Iᶻ I¹ = I^{z+1}`; that property is not needed, and not having it is
cheaper. Writing `f` as the integral of `g` and exchanging the order of integration over the
triangle `0 < ρ ≤ r ≤ t` leaves an inner integral in `r` alone, which is elementary.
-/

/-- The inner integral of the exchange: `∫_ρ^t (t-r)^{z-2}dr = (t-ρ)^{z-1}/(z-1)`.

`Re z > 1` is exactly the convergence condition — the same endpoint the rest of the chapter turns
on — and it is Mathlib's `integral_cpow` hypothesis `-1 < Re r` after the substitution
`w = t - r`. -/
theorem integral_cpow_sub_left {z : ℂ} (hz : 1 < z.re) {ρ t : ℝ} (hρt : ρ ≤ t) :
    (∫ r in Ioc ρ t, ((t - r : ℝ) : ℂ) ^ (z - 2)) = ((t - ρ : ℝ) : ℂ) ^ (z - 1) / (z - 1) := by
  have hz1 : z - 1 ≠ 0 := fun h => by
    rw [sub_eq_zero] at h; rw [h] at hz; simp at hz
  have hre : -1 < (z - 2).re := by simp only [Complex.sub_re, Complex.re_ofNat]; linarith
  rw [← intervalIntegral.integral_of_le hρt]
  have hsub := intervalIntegral.integral_comp_sub_left
    (a := ρ) (b := t) (fun w : ℝ => ((w : ℝ) : ℂ) ^ (z - 2)) t
  simp only [sub_self] at hsub
  rw [hsub, integral_cpow (Or.inl hre)]
  have h0 : ((0 : ℝ) : ℂ) ^ (z - 2 + 1) = 0 := by
    rw [Complex.ofReal_zero, Complex.zero_cpow (by rw [show z - 2 + 1 = z - 1 by ring]; exact hz1)]
  rw [h0, sub_zero]
  congr 2 <;> ring


/-- **`Iᶻf' = I^{z-1}f`** when `f` is the integral of `g`, i.e. absolutely continuous with
`f(0) = 0`.

Fubini over the triangle `0 < ρ ≤ r ≤ t`: the inner integral in `r` is
`integral_cpow_sub_left`, and `Γ(z) = (z-1)Γ(z-1)` absorbs the factor it produces. No semigroup
property of the Riemann–Liouville family is needed, which is what the draft's derivation
`Iᶻf' = I^{z-1}I¹f'` goes through. -/
theorem riemannLiouville_integral {z : ℂ} (hz : 1 < z.re) {g : ℝ → ℝ} (hgm : Measurable g)
    {t : ℝ} (hg : IntegrableOn g (Ioc 0 t)) (ht : 0 < t) :
    riemannLiouville (z - 1) (fun r => ∫ ρ in Ioc (0 : ℝ) r, g ρ) t
      = riemannLiouville z g t := by
  have hz1 : z - 1 ≠ 0 := fun h => by rw [sub_eq_zero] at h; rw [h] at hz; simp at hz
  have hre : -1 < (z - 2).re := by simp only [Complex.sub_re, Complex.re_ofNat]; linarith
  have hw : ∀ ρ : ℝ, ρ ≤ t →
      IntegrableOn (fun r : ℝ => ((t - r : ℝ) : ℂ) ^ (z - 2)) (Ioc ρ t) := by
    intro ρ hρ
    have h1 : IntervalIntegrable (fun w : ℝ => ((w : ℝ) : ℂ) ^ (z - 2)) volume 0 (t - ρ) :=
      intervalIntegral.intervalIntegrable_cpow' hre
    have h2 := (h1.comp_sub_left t).symm
    simp only [sub_sub_cancel, sub_zero] at h2
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hρ).mp h2
  set Ψ : ℝ → ℝ → ℂ := fun r ρ =>
    Set.indicator (Iic r) (fun ρ => ((t - r : ℝ) : ℂ) ^ (z - 2) * (g ρ : ℂ)) ρ with hΨdef
  have hcolfun : ∀ ρ r : ℝ, Ψ r ρ
      = Set.indicator (Ici ρ) (fun r => ((t - r : ℝ) : ℂ) ^ (z - 2) * (g ρ : ℂ)) r := by
    intro ρ r
    by_cases h : ρ ≤ r
    · simp only [hΨdef, Set.indicator_of_mem, mem_Iic.mpr h, mem_Ici.mpr h]
    · rw [hΨdef]
      simp only [Set.indicator_apply, mem_Iic, mem_Ici, if_neg h]
  have hIcc : ∀ ρ : ℝ, 0 < ρ → Ioc (0 : ℝ) t ∩ Ici ρ = Icc ρ t := by
    intro ρ hρ
    ext u
    simp only [mem_inter_iff, mem_Ioc, mem_Icc, mem_Ici]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨lt_of_lt_of_le hρ h.1, h.2⟩, h.1⟩⟩
  have hmeas : Measurable (Function.uncurry Ψ) := by
    have hset : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} :=
      measurableSet_le measurable_snd measurable_fst
    have heq : Function.uncurry Ψ = fun p : ℝ × ℝ =>
        Set.indicator {q : ℝ × ℝ | q.2 ≤ q.1}
          (fun q => ((t - q.1 : ℝ) : ℂ) ^ (z - 2) * (g q.2 : ℂ)) p := by
      funext p
      by_cases h : p.2 ≤ p.1
      · simp only [Function.uncurry, hΨdef, Set.indicator_of_mem, mem_Iic.mpr h,
          Set.mem_setOf_eq, h]
      · simp only [Function.uncurry, hΨdef, Set.indicator_apply, mem_Iic, Set.mem_setOf_eq,
          if_neg h]
    rw [heq]
    exact (by fun_prop : Measurable fun q : ℝ × ℝ =>
      ((t - q.1 : ℝ) : ℂ) ^ (z - 2) * (g q.2 : ℂ)).indicator hset
  have hrow : ∀ r ∈ Ioc (0 : ℝ) t, (∫ ρ in Ioc (0 : ℝ) t, Ψ r ρ)
      = ((t - r : ℝ) : ℂ) ^ (z - 2) * ((∫ ρ in Ioc (0 : ℝ) r, g ρ : ℝ) : ℂ) := by
    intro r hr
    have hsub : Ioc (0 : ℝ) t ∩ Iic r = Ioc (0 : ℝ) r := by
      ext u
      simp only [mem_inter_iff, mem_Ioc, mem_Iic]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.trans hr.2⟩, h.2⟩⟩
    rw [hΨdef, setIntegral_indicator measurableSet_Iic, hsub, integral_const_mul]
    congr 1
    exact integral_ofReal (𝕜 := ℂ)
  have hcol : ∀ ρ ∈ Ioc (0 : ℝ) t, (∫ r in Ioc (0 : ℝ) t, Ψ r ρ)
      = (g ρ : ℂ) * (((t - ρ : ℝ) : ℂ) ^ (z - 1) / (z - 1)) := by
    intro ρ hρ
    simp only [hcolfun ρ]
    rw [setIntegral_indicator measurableSet_Ici, hIcc ρ hρ.1,
      setIntegral_congr_set (Ioc_ae_eq_Icc (a := ρ) (b := t)).symm, integral_mul_const,
      integral_cpow_sub_left hz hρ.2]
    ring
  have hint : Integrable (Function.uncurry Ψ)
      ((volume.restrict (Ioc (0 : ℝ) t)).prod (volume.restrict (Ioc (0 : ℝ) t))) := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_prod_symm _ hmeas.enorm.aemeasurable]
    have hpt : ∀ ρ r : ℝ, ‖Function.uncurry Ψ (r, ρ)‖ₑ
        ≤ ‖((t - r : ℝ) : ℂ) ^ (z - 2)‖ₑ * ‖(g ρ : ℂ)‖ₑ := by
      intro ρ r
      by_cases h : ρ ≤ r
      · simp only [Function.uncurry, hΨdef, Set.indicator_of_mem, mem_Iic.mpr h]
        rw [enorm_mul]
      · simp only [Function.uncurry, hΨdef, Set.indicator_apply, mem_Iic, if_neg h]
        simp
    have hA : ∫⁻ r in Ioc (0 : ℝ) t, ‖((t - r : ℝ) : ℂ) ^ (z - 2)‖ₑ ≠ ⊤ :=
      ((hw 0 ht.le).2).ne
    have hB : ∫⁻ ρ in Ioc (0 : ℝ) t, ‖(g ρ : ℂ)‖ₑ ≠ ⊤ := by
      have := hg.2
      rw [hasFiniteIntegral_iff_enorm] at this
      refine ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) this)
      refine lintegral_congr fun ρ => ?_
      rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real]
    calc ∫⁻ ρ, ∫⁻ r, ‖Function.uncurry Ψ (r, ρ)‖ₑ ∂(volume.restrict (Ioc (0 : ℝ) t))
            ∂(volume.restrict (Ioc (0 : ℝ) t))
        ≤ ∫⁻ ρ in Ioc (0 : ℝ) t, ∫⁻ r in Ioc (0 : ℝ) t,
            ‖((t - r : ℝ) : ℂ) ^ (z - 2)‖ₑ * ‖(g ρ : ℂ)‖ₑ :=
          lintegral_mono fun ρ => lintegral_mono fun r => hpt ρ r
      _ = (∫⁻ ρ in Ioc (0 : ℝ) t, ‖(g ρ : ℂ)‖ₑ)
            * ∫⁻ r in Ioc (0 : ℝ) t, ‖((t - r : ℝ) : ℂ) ^ (z - 2)‖ₑ := by
          rw [← lintegral_mul_const' _ _ hA]
          refine lintegral_congr fun ρ => ?_
          rw [lintegral_mul_const' _ _ (by simp), mul_comm]
      _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hB) (lt_top_iff_ne_top.mpr hA)
  have hexp : z - 1 - 1 = z - 2 := by ring
  calc riemannLiouville (z - 1) (fun r => ∫ ρ in Ioc (0 : ℝ) r, g ρ) t
      = (Complex.Gamma (z - 1))⁻¹ * ∫ r in Ioc (0 : ℝ) t, ∫ ρ in Ioc (0 : ℝ) t, Ψ r ρ := by
        rw [riemannLiouville, hexp]
        congr 1
        exact (setIntegral_congr_fun measurableSet_Ioc (fun r hr => hrow r hr)).symm
    _ = (Complex.Gamma (z - 1))⁻¹ * ∫ ρ in Ioc (0 : ℝ) t, ∫ r in Ioc (0 : ℝ) t, Ψ r ρ := by
        rw [integral_integral_swap hint]
    _ = riemannLiouville z g t := by
        rw [riemannLiouville, setIntegral_congr_fun measurableSet_Ioc hcol,
          show (fun ρ : ℝ => (g ρ : ℂ) * (((t - ρ : ℝ) : ℂ) ^ (z - 1) / (z - 1)))
            = fun ρ : ℝ => (z - 1)⁻¹ * (((t - ρ : ℝ) : ℂ) ^ (z - 1) * (g ρ : ℂ)) from by
              funext ρ; field_simp,
          integral_const_mul, ← mul_assoc]
        congr 1
        have hGam : Complex.Gamma z = (z - 1) * Complex.Gamma (z - 1) := by
          have h := Complex.Gamma_add_one (z - 1) hz1
          rwa [sub_add_cancel] at h
        rw [hGam, mul_inv]
        exact mul_comm _ _

/-! ## The canonical gauge at the level of measures, and the field

`lem:memory-fractional-integrals` is about the field `u(t,x) = (Φ_{0,x}f)(t)`, and `Φ` is
`L¹`-valued. The decision recorded in `PLAN-chapters-8-12.md` was to read the identification
almost everywhere in `t` rather than build a pointwise model of the field.

**What that decision does not avoid, and this is worth naming.** "For each `x`, for a.e. `t`" does
*not* give "for a.e. `t`, for every `x`": the null set depends on `x`. So a Mellin transform in `x`
at a fixed `t` cannot be taken of `(Φ_{0,x}f)(t)` as it stands, whichever way the identification is
read — a representative has to be chosen. What (a) buys is that the choice is *local*: it is the
one function `delayedField`, defined outright, with a bridge saying it represents `Φ_{0,x}f` for
each `x`. What (b) would have bought is the same choice made once, globally, under all of
chapters 10–12.
-/

/-- Dilating a measure dilates the Laplace variable. -/
theorem laplace_map_mul (μ : Measure ℝ) (x s : ℝ) :
    laplace (μ.map (fun t : ℝ => x * t)) s = laplace μ (x * s) := by
  rw [laplace, laplace, integral_map (by fun_prop) (by fun_prop)]
  refine integral_congr_ae (.of_forall fun t => ?_)
  ring_nf

/-- A positive dilation preserves causality. -/
theorem isCausal_map_mul {μ : Measure ℝ} (hμ : IsCausal μ) {x : ℝ} (hx : 0 < x) :
    IsCausal (μ.map (fun t : ℝ => x * t)) := by
  rw [IsCausal, Measure.map_apply (by fun_prop) measurableSet_Iio]
  have hpre : (fun t : ℝ => x * t) ⁻¹' Iio 0 = Iio 0 := by
    ext t
    simp [mem_Iio, hx]
  rw [hpre]
  exact hμ

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent)

/-- **The canonical gauge, at the level of measures**: `μ_{0,x}` is the law of `x·T₁`.

The article works in the canonical gauge throughout Chapter 11 and reads this off the notation;
in Lean the kernels are produced by `kernel_spec` from their transforms, so it is a lemma. Both
sides are causal with transform `e^{-F(xs)}`, and `kernel_unique` is Laplace injectivity. -/
theorem kernel_zero_eq_map_lawT₁ {x : ℝ} (hx : 0 < x) :
    F.kernel 0 x = F.lawT₁.map (fun t : ℝ => x * t) := by
  haveI : IsProbabilityMeasure F.lawT₁ := F.isProbabilityMeasure_lawT₁
  haveI : IsProbabilityMeasure (F.lawT₁.map (fun t : ℝ => x * t)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  refine (kernel_unique (isCausal_map_mul F.isCausal_lawT₁ hx) le_rfl hx.le fun s hs => ?_).symm
  rw [laplace_map_mul, show laplace F.lawT₁ (x * s) = F.profile (x * s) from rfl,
    F.profile_eq_exp_neg (mul_nonneg hx.le hs), increment_zero_left hx.le, toRealExponent]

/-! ## `lem:standing-kernel-readings` (11.21), assembled

`MellinData.lean` carries everything about the first clause of `def:standing-hypothesis` that is
stateable in terms of `F.lawT₁` alone; this is the one clause that needs comparing `F.kernel 0 x`
across every `x > 0`, which needs `kernel_zero_eq_map_lawT₁` just proved, and so has to live here,
downstream of it. -/

/-- The general kernel `μ_{0,x}` has no atom at zero delay exactly when `T₁` does not, for any
`x > 0`: `μ_{0,x}` is the law of `x T₁` (`kernel_zero_eq_map_lawT₁`), and multiplication by a
nonzero `x` carries `{0}` to `{0}` and nothing else there. -/
theorem kernel_zero_singleton_zero_eq {x : ℝ} (hx : 0 < x) :
    F.kernel 0 x {(0 : ℝ)} = F.lawT₁ {(0 : ℝ)} := by
  rw [F.kernel_zero_eq_map_lawT₁ hx,
    Measure.map_apply (by fun_prop) (measurableSet_singleton (0 : ℝ))]
  congr 1
  ext t
  simp [hx.ne']

/-- **`lem:standing-kernel-readings`(1)**: `F(∞) = ∞` iff none of the kernels `μ_{0,x}`, `x > 0`,
has an atom at zero delay. -/
theorem tendsto_toRealExponent_atTop_iff :
    Tendsto F.toRealExponent atTop atTop ↔ ∀ x : ℝ, 0 < x → F.kernel 0 x {(0 : ℝ)} = 0 :=
  ⟨fun h _x hx => (F.kernel_zero_singleton_zero_eq hx).trans (F.lawT₁_singleton_zero h),
    fun h => F.tendsto_toRealExponent_atTop_of_lawT₁_singleton_zero
      (show F.kernel 0 1 {(0 : ℝ)} = 0 from h 1 one_pos)⟩

/-- **`lem:standing-kernel-readings`**, assembled: both clauses of `def:standing-hypothesis`
that used to be asserted in passing, now proved. `#print axioms` on this bundle is the
load-bearing check for the node: the two moment-side conjuncts are unconditional (Lean core plus
nothing), and the atom-side conjuncts and the identity rest on `A17`, through the constructed
family, exactly as `lem:mellin-data` does. -/
theorem standing_kernel_readings :
    (Tendsto F.toRealExponent atTop atTop ↔ ∀ x : ℝ, 0 < x → F.kernel 0 x {(0 : ℝ)} = 0) ∧
    (F.lawT₁ {(0 : ℝ)} = 0 → ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (F.profile s) = F.negMoment 1) ∧
    (1 < F.zStar → F.negMoment 1 ≠ ⊤) ∧ (F.negMoment 1 ≠ ⊤ → (1 : ℝ≥0∞) ≤ F.zStar) :=
  ⟨F.tendsto_toRealExponent_atTop_iff, F.lintegral_profile_eq_negMoment_one,
    F.negMoment_one_ne_top_of_one_lt_zStar, F.one_le_zStar_of_negMoment_one_ne_top⟩

/-- **The field, as a genuine function of `(t,x)`**: `u(t,x) = E[f(t - x T₁)]`.

The representative the article's `Φ_{0,x}f` is read through. Choosing it is what makes a Mellin
transform in `x` at a fixed `t` meaningful; see the section docstring for why no reading of the
identification avoids the choice. -/
noncomputable def delayedField (f : ℝ → ℝ) (t x : ℝ) : ℝ := ∫ τ, f (t - x * τ) ∂F.lawT₁

/-- **The bridge**: at each scale `x`, the chosen representative *is* `Φ_{0,x}f`, almost
everywhere in `t`.

`Φ` is convolution with `μ_{0,x}` at the level of `L¹` classes (`coeFn_mconvL1`), and `μ_{0,x}` is
the law of `x·T₁`; pushing the dilation through the convolution integral gives the delayed
average. -/
theorem coeFn_Phi_zero (hF : ∃ s₀, 0 < s₀ ∧ F.exponent s₀ ≠ 0) {x : ℝ} (hx : 0 < x)
    {f : ℝ → ℝ} (hfm : Measurable f) (hf : Integrable f) :
    ⇑((F.cascadeFamily hF).Φ 0 x (hf.toL1 f)) =ᵐ[volume] fun t => F.delayedField f t x := by
  haveI := isProbabilityMeasure_kernel (F := F) (le_refl (0 : ℝ)) hx.le
  refine (coeFn_mconvL1 (F.kernel 0 x) (hf.toL1 f)).trans ?_
  refine (mconv_congr_ae (F.kernel 0 x) hf.coeFn_toL1).trans (.of_forall fun t => ?_)
  have hmap : ∫ r, f (t - r) ∂(F.lawT₁.map fun u : ℝ => x * u)
      = ∫ τ, f (t - x * τ) ∂F.lawT₁ :=
    integral_map (by fun_prop) (hfm.comp (measurable_const_sub t)).aestronglyMeasurable
  rw [mconv_apply, F.kernel_zero_eq_map_lawT₁ hx, hmap]
  rfl


/-- **`lem:memory-fractional-integrals`**, first clause: at each time `t > 0`, the Mellin
transform in `x` of the field is `H̃(z)` times the Riemann–Liouville integral of order `z` of the
past signal.

The field is read through `delayedField`, which `coeFn_Phi_zero` shows represents `Φ_{0,x}f` at
every scale `x > 0`. So the memory line at time `t`, seen through the Mellin transform, holds the
whole analytic family `{(Iᶻf)(t)}` weighted by the negative delay-moments — which is what the
article's Remark 11.7 reads as the observer's embodiment of its past. -/
theorem mellin_delayedField (hH : F.StandingHypothesis) {z : ℂ} (hz : 0 < z.re)
    (hz' : ENNReal.ofReal z.re < F.zStar) {f : ℝ → ℝ} (hfm : Measurable f)
    (hcausal : ∀ r : ℝ, r < 0 → f r = 0) {t : ℝ} (ht : 0 < t)
    (hpast : IntegrableOn (fun y : ℝ => (y : ℂ) ^ (z - 1) * (f (t - y) : ℂ)) (Ioi 0)) :
    mellin (fun x : ℝ => (F.delayedField f t x : ℂ)) z
      = mellin (fun s => (F.profile s : ℂ)) z * riemannLiouville z f t := by
  rw [← mellin_delayed_average hH hz hz' hfm hcausal ht hpast]
  congr 1
  funext x
  exact (integral_ofReal (𝕜 := ℂ)).symm


/-- **`thm:signaling-form`(2), the Mellin form**, up to its derivative clause:
`B(1-z)·ũ(t,·)(z-1) = H̃(z)·(I^{z-1}f)(t)`.

The draft's displayed computation, exactly: the symbol is `H̃(z)/H̃(z-1)`, the transform of the
field at `z-1` is `H̃(z-1)(I^{z-1}f)(t)`, and the `H̃(z-1)` cancels. What remains to reach
`∂̃_t u(t,·)(z)` is the derivative clause of `lem:memory-fractional-integrals`, which needs
`∂_t u` and hence `lem:delay-core`.

Two hypotheses are worth reading. `Re z > 1` is used at `z-1`, which is where the strip has to
start at `0` rather than `1` — hence the boundedness of `f`, supplied by `f ∈ 𝒟`. And `H̃(z-1) ≠ 0`
is not a side condition the article states: its `rem:poles` says the identity "is nevertheless
regular, the factor `H̃(z-1)` cancelling every denominator", which is true of the product as a
*meromorphic function* and not of `B` as a function, where the division is present and has to be
cancelled at the point. That is the third time in this chapter the same distinction has had to be
drawn. -/
theorem inversionSymbol_mul_mellin_delayedField (hH : F.StandingHypothesis) {z : ℂ}
    (hz : 1 < z.re) (hz' : ENNReal.ofReal z.re < F.zStar) {f : ℝ → ℝ} {C : ℝ} (hfm : Measurable f)
    (hbdd : ∀ y : ℝ, |f y| ≤ C) (hcausal : ∀ r : ℝ, r < 0 → f r = 0) {t : ℝ} (ht : 0 < t)
    (hne : mellin (fun s => (F.profile s : ℂ)) (z - 1) ≠ 0) :
    F.inversionSymbol (z - 1) * mellin (fun x : ℝ => (F.delayedField f t x : ℂ)) (z - 1)
      = mellin (fun s => (F.profile s : ℂ)) z * riemannLiouville (z - 1) f t := by
  have hre : (z - 1).re = z.re - 1 := by simp
  have hz1 : 0 < (z - 1).re := by rw [hre]; linarith
  have hz1' : ENNReal.ofReal (z - 1).re < F.zStar := by
    rw [hre]; exact F.ofReal_lt_zStar_of_le (by linarith) hz'
  have hpast := integrableOn_pastIntegrand_of_bounded (z := z - 1) hz1 hfm hbdd hcausal ht
  rw [F.mellin_delayedField hH hz1 hz1' hfm hcausal ht hpast, inversionSymbol,
    sub_add_cancel]
  field_simp

end SelfDecomposableExponent


/-! ## The derivative clause, field half

`lem:memory-fractional-integrals`' second clause says `∂_t u(t,x) = E[f'(t - xT₁)]` for `f ∈ 𝒟`.
Stating that as a pointwise derivative — `HasDerivAt` at every `t` — **is false**, and it is worth
being exact about why, because the repair is not a technicality.

`f ∈ 𝒟` is absolutely continuous, so `f' = g` only almost everywhere. The field is
`E[f(t - xT₁)] = (f ⋆ ν_x)(t)` for `ν_x` the law of `xT₁`, and a convolution of two `L¹` functions
is `L¹`, not continuous; so `E[g(t - xT₁)]` has no pointwise values to be a derivative *at*. One
could buy continuity by using absolute continuity of `T₁`'s law — but that is `Sato, Thm 27.13`,
an interface, spent for nothing.

The article never meant the pointwise reading. `∂_t` in Chapter 10 is the `X₀ = L¹` derivative of
`lem:delay-core`, and what that lemma's `Φ`-invariance argument actually establishes is
`μ * f = 1_{[0,∞)} * (μ * f')` — the field of `f` is the **primitive** of the field of `f'`. That
is the statement below: an identity between two genuine functions of `t`, needing no interface and
no representative-choosing, and it is the form the Mellin computation consumes.
-/

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent)

/-- **The field of `f` is the primitive of the field of `f'`.**

The derivative clause of `lem:memory-fractional-integrals`, in the only form in which it is true
without an interface. Fubini plus a translation, and causality of `g` is what makes the inner
integral land on `(0, t - xτ]` rather than `(-xτ, t - xτ]`. -/
theorem delayedField_eq_setIntegral {g f : ℝ → ℝ} (hgm : Measurable g) (hg : Integrable g)
    (hgc : ∀ r : ℝ, r < 0 → g r = 0) (hf : ∀ r : ℝ, f r = ∫ ρ in Ioc (0 : ℝ) r, g ρ)
    (hH : F.StandingHypothesis) {x : ℝ} (hx : 0 < x) {t : ℝ} (ht : 0 ≤ t) :
    F.delayedField f t x = ∫ s in Ioc (0 : ℝ) t, F.delayedField g s x := by
  have h0 := F.lawT₁_singleton_zero hH.1
  have hae := F.ae_mem_Ioi_lawT₁ h0
  -- `g` integrates to zero over any interval to the left of the origin
  have hne : ∀ᵐ w : ℝ, w ≠ 0 := by
    rw [ae_iff]
    simp
  have hzero : ∀ a b : ℝ, b ≤ 0 → (∫ w in Ioc a b, g w) = 0 := by
    intro a b hb
    refine integral_eq_zero_of_ae ((ae_restrict_iff' measurableSet_Ioc).mpr ?_)
    filter_upwards [hne] with w hw hwmem
    exact hgc w (lt_of_le_of_ne (hwmem.2.trans hb) hw)
  have htrim : ∀ a b : ℝ, a ≤ 0 → (∫ w in Ioc a b, g w) = ∫ w in Ioc (0 : ℝ) b, g w := by
    intro a b ha
    rcases lt_or_ge 0 b with hb | hb
    · have hsplit : Ioc a b = Ioc a 0 ∪ Ioc (0 : ℝ) b := (Ioc_union_Ioc_eq_Ioc ha hb.le).symm
      have hdisj : Disjoint (Ioc a (0 : ℝ)) (Ioc (0 : ℝ) b) := by
        rw [Set.disjoint_left]
        rintro w ⟨-, hw2⟩ ⟨hw3, -⟩
        exact absurd hw3 (not_lt.mpr hw2)
      rw [hsplit, setIntegral_union hdisj measurableSet_Ioc hg.integrableOn hg.integrableOn,
        hzero a 0 le_rfl, zero_add]
    · rw [hzero a b hb, Ioc_eq_empty (not_lt.mpr hb), Measure.restrict_empty, integral_zero_measure]
  -- the inner integral, at a fixed delay
  have hinner : ∀ τ : ℝ, 0 ≤ τ →
      (∫ s in Ioc (0 : ℝ) t, g (s - x * τ)) = f (t - x * τ) := by
    intro τ hτ
    have hsub : (∫ s in Ioc (0 : ℝ) t, g (s - x * τ))
        = ∫ w in Ioc (0 - x * τ) (t - x * τ), g w := by
      rw [← intervalIntegral.integral_of_le ht, ← intervalIntegral.integral_of_le (by linarith)]
      exact intervalIntegral.integral_comp_sub_right (fun w => g w) (x * τ)
    rw [hsub, htrim _ _ (by simpa using mul_nonneg hx.le hτ), hf]
  -- the exchange
  have hint : Integrable (Function.uncurry fun (s τ : ℝ) => g (s - x * τ))
      ((volume.restrict (Ioc (0 : ℝ) t)).prod F.lawT₁) := by
    have hmeas : Measurable (Function.uncurry fun (s τ : ℝ) => g (s - x * τ)) := by
      unfold Function.uncurry
      fun_prop
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_prod_symm _ hmeas.enorm.aemeasurable]
    have hC : ∫⁻ w, ‖g w‖ₑ ≠ ⊤ := by
      have := hg.2
      rw [hasFiniteIntegral_iff_enorm] at this
      exact this.ne
    have hbnd : ∀ τ : ℝ,
        (∫⁻ s in Ioc (0 : ℝ) t, ‖Function.uncurry (fun (s τ : ℝ) => g (s - x * τ)) (s, τ)‖ₑ)
          ≤ ∫⁻ w, ‖g w‖ₑ := by
      intro τ
      calc (∫⁻ s in Ioc (0 : ℝ) t, ‖g (s - x * τ)‖ₑ)
          ≤ ∫⁻ s, ‖g (s - x * τ)‖ₑ := setLIntegral_le_lintegral _ _
        _ = ∫⁻ w, ‖g w‖ₑ := lintegral_sub_right_eq_self (fun w => ‖g w‖ₑ) (x * τ)
    calc ∫⁻ τ, (∫⁻ s in Ioc (0 : ℝ) t,
            ‖Function.uncurry (fun (s τ : ℝ) => g (s - x * τ)) (s, τ)‖ₑ) ∂F.lawT₁
        ≤ ∫⁻ _τ, (∫⁻ w, ‖g w‖ₑ) ∂F.lawT₁ := lintegral_mono hbnd
      _ = ∫⁻ w, ‖g w‖ₑ := by rw [lintegral_const, measure_univ, mul_one]
      _ < ⊤ := lt_top_iff_ne_top.mpr hC
  calc F.delayedField f t x
      = ∫ τ, f (t - x * τ) ∂F.lawT₁ := rfl
    _ = ∫ τ, (∫ s in Ioc (0 : ℝ) t, g (s - x * τ)) ∂F.lawT₁ := by
        refine (integral_congr_ae ?_).symm
        filter_upwards [hae] with τ hτ using hinner τ (mem_Ioi.mp hτ).le
    _ = ∫ s in Ioc (0 : ℝ) t, ∫ τ, g (s - x * τ) ∂F.lawT₁ := (integral_integral_swap hint).symm
    _ = ∫ s in Ioc (0 : ℝ) t, F.delayedField g s x := rfl


/-- The primitive of an `L¹` function is bounded by its norm — the concrete content of "`f ∈ 𝒟` is
bounded", which is what widens the strip in `lem:memory-fractional-integrals`. -/
theorem abs_primitive_le {g : ℝ → ℝ} (hg : Integrable g) (r : ℝ) :
    |∫ ρ in Ioc (0 : ℝ) r, g ρ| ≤ ∫ w, |g w| := by
  refine le_trans abs_integral_le_integral_abs ?_
  exact setIntegral_le_integral hg.abs (.of_forall fun w => abs_nonneg _)

/-- **`lem:memory-fractional-integrals`, derivative clause, transformed**:
`∂̃_t u(t,·)(z) = H̃(z)(I^{z-1}f)(t)`.

The field of `f'` transformed by `lem:delayed-average-mellin`, then
`lem:fractional-integral-derivative` to turn `Iᶻf'` into `I^{z-1}f`. -/
theorem mellin_delayedField_deriv (hH : F.StandingHypothesis) {z : ℂ} (hz : 1 < z.re)
    (hz' : ENNReal.ofReal z.re < F.zStar) {g f : ℝ → ℝ} (hgm : Measurable g) (hg : Integrable g)
    (hgc : ∀ r : ℝ, r < 0 → g r = 0) (hf : ∀ r : ℝ, f r = ∫ ρ in Ioc (0 : ℝ) r, g ρ)
    {t : ℝ} (ht : 0 < t) :
    mellin (fun x : ℝ => (F.delayedField g t x : ℂ)) z
      = mellin (fun s => (F.profile s : ℂ)) z * riemannLiouville (z - 1) f t := by
  have hpast := integrableOn_pastIntegrand (z := z) hz hg hgc ht
  rw [F.mellin_delayedField hH (by linarith) hz' hgm hgc ht hpast,
    ← riemannLiouville_integral hz hgm hg.integrableOn ht]
  congr 1
  rw [riemannLiouville, riemannLiouville]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun r _ => ?_
  rw [hf r]

/-- **`thm:signaling-form`(2), the Mellin form**, entire:
`∂̃_t u(t,·)(z) = B(1-z)·ũ(t,·)(z-1)`.

Both sides equal `H̃(z)(I^{z-1}f)(t)`; the left by `mellin_delayedField_deriv`, the right by
`inversionSymbol_mul_mellin_delayedField`. The boundedness of `f` that the right-hand side needs
— because it applies `lem:delayed-average-mellin` at `z-1`, below the strip an `L¹` hypothesis
would give — is `abs_primitive_le`, i.e. exactly the part of `f ∈ 𝒟` that is load-bearing. -/
theorem mellin_signaling_form (hH : F.StandingHypothesis) {z : ℂ} (hz : 1 < z.re)
    (hz' : ENNReal.ofReal z.re < F.zStar) {g f : ℝ → ℝ} (hgm : Measurable g) (hg : Integrable g)
    (hgc : ∀ r : ℝ, r < 0 → g r = 0) (hfm : Measurable f)
    (hf : ∀ r : ℝ, f r = ∫ ρ in Ioc (0 : ℝ) r, g ρ) {t : ℝ} (ht : 0 < t)
    (hne : mellin (fun s => (F.profile s : ℂ)) (z - 1) ≠ 0) :
    mellin (fun x : ℝ => (F.delayedField g t x : ℂ)) z
      = F.inversionSymbol (z - 1) * mellin (fun x : ℝ => (F.delayedField f t x : ℂ)) (z - 1) := by
  have hfc : ∀ r : ℝ, r < 0 → f r = 0 := by
    intro r hr
    rw [hf r, Ioc_eq_empty (not_lt.mpr hr.le), Measure.restrict_empty, integral_zero_measure]
  have hbdd : ∀ y : ℝ, |f y| ≤ ∫ w, |g w| := fun y => by rw [hf y]; exact abs_primitive_le hg y
  rw [F.inversionSymbol_mul_mellin_delayedField hH hz hz' hfm hbdd hfc ht hne]
  exact F.mellin_delayedField_deriv hH hz hz' hgm hg hgc hf ht

end SelfDecomposableExponent


/-! ## The remaining clauses of `thm:signaling-form`(2)

Causality in `t`, boundary attainment as `x ↓ 0`, and the identification
`û(s,x) = f̂(s)H(sx)` that turns `inversionOperator_const_mul_profile` into the Laplace form.
-/

/-- The causal Laplace transform of a function on the half-line. -/
noncomputable def laplaceFun (f : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), Real.exp (-(s * t)) * f t

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent)

/-- **`thm:signaling-form`(2), causality**: the field vanishes before the signal does.

Pointwise and immediate — `f(t - xτ) = 0` for `t < 0` because `τ ≥ 0` almost surely. -/
theorem delayedField_eq_zero (hH : F.StandingHypothesis) {f : ℝ → ℝ}
    (hfc : ∀ r : ℝ, r < 0 → f r = 0) {x t : ℝ} (hx : 0 < x) (ht : t < 0) :
    F.delayedField f t x = 0 := by
  have hae := F.ae_mem_Ioi_lawT₁ (F.lawT₁_singleton_zero hH.1)
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hae] with τ hτ
  exact hfc _ (by nlinarith [mem_Ioi.mp hτ])

/-- **`thm:signaling-form`(2), boundary attainment**: `Φ_{0,x} f → f` in `X₀` as `x ↓ 0`.

(A7) with (A6): the parameter map is continuous on `{0 ≤ a ≤ b}` and the diagonal is the
identity. -/
theorem tendsto_Phi_zero (hF : ∃ s₀, 0 < s₀ ∧ F.exponent s₀ ≠ 0) (f : X) :
    Filter.Tendsto (fun x : ℝ => (F.cascadeFamily hF).Φ 0 x f) (𝓝[≥] (0 : ℝ)) (𝓝 f) := by
  have hmem : ((0 : ℝ), (0 : ℝ)) ∈ {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2} := ⟨le_rfl, le_rfl⟩
  have hcont := ((F.cascadeFamily hF).continuous f _ hmem).tendsto
  have hmap : Filter.Tendsto (fun x : ℝ => ((0 : ℝ), x)) (𝓝[≥] (0 : ℝ))
      (𝓝[{p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2}] ((0 : ℝ), (0 : ℝ))) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact ((continuous_const.prodMk continuous_id).tendsto 0).mono_left nhdsWithin_le_nhds
    · exact Filter.Eventually.mono self_mem_nhdsWithin fun x hx => ⟨le_rfl, hx⟩
  have := hcont.comp hmap
  simpa [Function.comp_def, (F.cascadeFamily hF).refl 0 le_rfl] using this

/-- **`thm:signaling-form`(2), the Laplace profile of the field**: `û(s,x) = f̂(s)·H(sx)`.

Fubini and a translation. With this, `inversionOperator_const_mul_profile` *is* the Laplace form
`A[û(s,·)] = s·û(s,·)`. -/
theorem laplaceFun_delayedField (hH : F.StandingHypothesis) {f : ℝ → ℝ} (hfm : Measurable f)
    (hf : Integrable f) (hfc : ∀ r : ℝ, r < 0 → f r = 0) {s x : ℝ} (hs : 0 ≤ s) (hx : 0 < x) :
    laplaceFun (fun t => F.delayedField f t x) s = F.profile (s * x) * laplaceFun f s := by
  have hae := F.ae_mem_Ioi_lawT₁ (F.lawT₁_singleton_zero hH.1)
  have hne : ∀ᵐ w : ℝ, w ≠ 0 := by
    rw [ae_iff]; simp
  have hzero : ∀ a : ℝ, (∫ w in Ioc a (0 : ℝ), Real.exp (-(s * w)) * f w) = 0 := by
    intro a
    refine integral_eq_zero_of_ae ((ae_restrict_iff' measurableSet_Ioc).mpr ?_)
    filter_upwards [hne] with w hw hwmem
    rw [hfc w (lt_of_le_of_ne hwmem.2 hw), mul_zero]
    rfl
  have htrim : ∀ a : ℝ, a ≤ 0 →
      (∫ w in Ioi a, Real.exp (-(s * w)) * f w) = laplaceFun f s := by
    intro a ha
    have hsplit : Ioi a = Ioc a 0 ∪ Ioi (0 : ℝ) := (Ioc_union_Ioi_eq_Ioi ha).symm
    have hdisj : Disjoint (Ioc a (0 : ℝ)) (Ioi (0 : ℝ)) := by
      rw [Set.disjoint_left]
      rintro w ⟨-, hw2⟩ hw3
      exact absurd hw3 (not_lt.mpr hw2)
    have hint : IntegrableOn (fun w : ℝ => Real.exp (-(s * w)) * f w) (Ioi a) := by
      refine Integrable.mono' hf.norm.integrableOn ((by fun_prop : Measurable fun w : ℝ =>
        Real.exp (-(s * w)) * f w).aestronglyMeasurable.restrict) ?_
      refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
      filter_upwards [hne] with w hw _
      rcases lt_or_ge 0 w with hpos | hnonpos
      · rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        refine mul_le_of_le_one_left (norm_nonneg _) ?_
        exact Real.exp_le_one_iff.mpr (by nlinarith)
      · rw [hfc w (lt_of_le_of_ne hnonpos hw), mul_zero, norm_zero]
    rw [laplaceFun, hsplit, setIntegral_union hdisj measurableSet_Ioi
      (hint.mono_set (by rw [hsplit]; exact subset_union_left))
      (hint.mono_set (by rw [hsplit]; exact subset_union_right)), hzero a, zero_add]
  have hinner : ∀ τ : ℝ, 0 < τ →
      (∫ t in Ioi (0 : ℝ), Real.exp (-(s * t)) * f (t - x * τ))
        = Real.exp (-(s * x * τ)) * laplaceFun f s := by
    intro τ hτ
    have hmp : MeasurePreserving (fun w : ℝ => w + x * τ) volume volume :=
      measurePreserving_add_right volume (x * τ)
    have hemb : MeasurableEmbedding (fun w : ℝ => w + x * τ) :=
      (Homeomorph.addRight (x * τ)).measurableEmbedding
    have hpre := hmp.setIntegral_preimage_emb hemb
      (fun t : ℝ => Real.exp (-(s * t)) * f (t - x * τ)) (Ioi 0)
    have hset : (fun w : ℝ => w + x * τ) ⁻¹' Ioi 0 = Ioi (-(x * τ)) := by
      ext w; simp [mem_Ioi, neg_lt_iff_pos_add]
    rw [hset] at hpre
    rw [← hpre]
    have hcongr : ∀ w : ℝ, Real.exp (-(s * (w + x * τ))) * f (w + x * τ - x * τ)
        = Real.exp (-(s * x * τ)) * (Real.exp (-(s * w)) * f w) := by
      intro w
      rw [add_sub_cancel_right, show -(s * (w + x * τ)) = -(s * x * τ) + -(s * w) from by ring,
        Real.exp_add]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi (fun w _ => hcongr w), integral_const_mul,
      htrim _ (by simpa using (mul_pos hx hτ).le)]
  have hmeas : Measurable (Function.uncurry fun (t τ : ℝ) =>
      Real.exp (-(s * t)) * f (t - x * τ)) := by
    unfold Function.uncurry
    fun_prop
  have hswap : Integrable (Function.uncurry fun (t τ : ℝ) => Real.exp (-(s * t)) * f (t - x * τ))
      ((volume.restrict (Ioi (0 : ℝ))).prod F.lawT₁) := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_prod_symm _ hmeas.enorm.aemeasurable]
    have hC : ∫⁻ w, ‖f w‖ₑ ≠ ⊤ := by
      have h := hf.2
      rw [hasFiniteIntegral_iff_enorm] at h
      exact h.ne
    have hbnd : ∀ τ : ℝ, (∫⁻ t in Ioi (0 : ℝ),
        ‖Function.uncurry (fun (t τ : ℝ) => Real.exp (-(s * t)) * f (t - x * τ)) (t, τ)‖ₑ)
          ≤ ∫⁻ w, ‖f w‖ₑ := by
      intro τ
      calc (∫⁻ t in Ioi (0 : ℝ), ‖Real.exp (-(s * t)) * f (t - x * τ)‖ₑ)
          ≤ ∫⁻ t in Ioi (0 : ℝ), ‖f (t - x * τ)‖ₑ := by
            refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
            rw [enorm_mul]
            refine mul_le_of_le_one_left' ?_
            rw [← ofReal_norm, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
            exact ENNReal.ofReal_le_one.mpr
              (Real.exp_le_one_iff.mpr (by nlinarith [mem_Ioi.mp ht]))
        _ ≤ ∫⁻ t, ‖f (t - x * τ)‖ₑ := setLIntegral_le_lintegral _ _
        _ = ∫⁻ w, ‖f w‖ₑ := lintegral_sub_right_eq_self (fun w => ‖f w‖ₑ) (x * τ)
    calc ∫⁻ τ, (∫⁻ t in Ioi (0 : ℝ),
            ‖Function.uncurry (fun (t τ : ℝ) => Real.exp (-(s * t)) * f (t - x * τ)) (t, τ)‖ₑ)
              ∂F.lawT₁
        ≤ ∫⁻ _τ, (∫⁻ w, ‖f w‖ₑ) ∂F.lawT₁ := lintegral_mono hbnd
      _ = ∫⁻ w, ‖f w‖ₑ := by rw [lintegral_const, measure_univ, mul_one]
      _ < ⊤ := lt_top_iff_ne_top.mpr hC
  calc laplaceFun (fun t => F.delayedField f t x) s
      = ∫ t in Ioi (0 : ℝ), ∫ τ, Real.exp (-(s * t)) * f (t - x * τ) ∂F.lawT₁ := by
        rw [laplaceFun]
        refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
        rw [delayedField, ← integral_const_mul]
    _ = ∫ τ, (∫ t in Ioi (0 : ℝ), Real.exp (-(s * t)) * f (t - x * τ)) ∂F.lawT₁ :=
        integral_integral_swap hswap
    _ = ∫ τ, Real.exp (-(s * x * τ)) * laplaceFun f s ∂F.lawT₁ := by
        refine integral_congr_ae ?_
        filter_upwards [hae] with τ hτ using hinner τ (mem_Ioi.mp hτ)
    _ = F.profile (s * x) * laplaceFun f s := by
        rw [integral_mul_const, profile, laplace]

/-! ### Two conjuncts the fidelity review added to `thm:signaling-form`

Each is a consequence of a lemma above, stated in the form the theorem needs (the
adversarial-vacuity pass, `PLAN-fidelity-review.md` P2). The third addition, the boundary value
`û(s,0+) = f̂(s)` (finding R11), lives in `SignalingForm.lean`, which has the transform's
continuity in scope. -/

/-- **`thm:signaling-form`(2), the time derivative**: at every scale `x > 0` and every time `t`,
the field of `f ∈ 𝒟` is the primitive of the field of `f'`. `delayedField_eq_setIntegral` for
`t ≥ 0`; for `t < 0` both sides vanish, by causality on the left and by the empty interval on the
right. This is the `X₀`-reading of `∂_t u` under which the Mellin form (2d) is stated. -/
theorem delayedField_eq_setIntegral' {g f : ℝ → ℝ} (hgm : Measurable g) (hg : Integrable g)
    (hgc : ∀ r : ℝ, r < 0 → g r = 0) (hf : ∀ r : ℝ, f r = ∫ ρ in Ioc (0 : ℝ) r, g ρ)
    (hH : F.StandingHypothesis) {x : ℝ} (hx : 0 < x) (t : ℝ) :
    F.delayedField f t x = ∫ s in Ioc (0 : ℝ) t, F.delayedField g s x := by
  rcases le_or_gt 0 t with ht | ht
  · exact F.delayedField_eq_setIntegral hgm hg hgc hf hH hx ht
  · have hfc : ∀ r : ℝ, r < 0 → f r = 0 := fun r hr => by
      rw [hf r, Ioc_eq_empty (not_lt.mpr hr.le), Measure.restrict_empty, integral_zero_measure]
    rw [F.delayedField_eq_zero hH hfc hx ht, Ioc_eq_empty (not_lt.mpr ht.le),
      Measure.restrict_empty, integral_zero_measure]

/-- **The Mellin transform of the field converges** wherever `lem:memory-fractional-integrals`
computes it: the joint integrability `integrable_delayed` gives, by Fubini, integrability of the
`x`-marginal, which is `MellinConvergent` for the field. This is what makes the identity in
`thm:signaling-form`(2d) an identity between convergent transforms rather than between Mathlib's
junk value `0` on both sides. -/
theorem mellinConvergent_delayedField (hH : F.StandingHypothesis) {z : ℂ} (hz : 0 < z.re)
    (hz' : ENNReal.ofReal z.re < F.zStar) {f : ℝ → ℝ} (hfm : Measurable f) {t : ℝ}
    (hpast : IntegrableOn (fun y : ℝ => (y : ℂ) ^ (z - 1) * (f (t - y) : ℂ)) (Ioi 0)) :
    MellinConvergent (fun x : ℝ => (F.delayedField f t x : ℂ)) z := by
  have h := (integrable_delayed hH hz hz' hfm hpast).integral_prod_left
  simp only [MellinConvergent, smul_eq_mul]
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [delayedField, Function.uncurry_apply_pair, integral_const_mul]
  congr 1
  exact integral_ofReal (𝕜 := ℂ)

/-- The two convergence clauses `thm:signaling-form`(2d) carries: the field of `f'` at `z`, and
the field of `f` at `z - 1`, on the strip `1 < Re z < z_*`. -/
theorem mellinConvergent_delayedField_pair (hH : F.StandingHypothesis) {z : ℂ} (hz : 1 < z.re)
    (hz' : ENNReal.ofReal z.re < F.zStar) {g f : ℝ → ℝ} (hgm : Measurable g) (hg : Integrable g)
    (hgc : ∀ r : ℝ, r < 0 → g r = 0) (hfm : Measurable f)
    (hf : ∀ r : ℝ, f r = ∫ ρ in Ioc (0 : ℝ) r, g ρ) {t : ℝ} (ht : 0 < t) :
    MellinConvergent (fun x : ℝ => (F.delayedField g t x : ℂ)) z ∧
      MellinConvergent (fun x : ℝ => (F.delayedField f t x : ℂ)) (z - 1) := by
  have hfc : ∀ r : ℝ, r < 0 → f r = 0 := fun r hr => by
    rw [hf r, Ioc_eq_empty (not_lt.mpr hr.le), Measure.restrict_empty, integral_zero_measure]
  have hbdd : ∀ y : ℝ, |f y| ≤ ∫ w, |g w| := fun y => by rw [hf y]; exact abs_primitive_le hg y
  have hre : (z - 1).re = z.re - 1 := by simp
  have hz1 : 0 < (z - 1).re := by rw [hre]; linarith
  have hz1' : ENNReal.ofReal (z - 1).re < F.zStar := by
    rw [hre]; exact F.ofReal_lt_zStar_of_le (by linarith) hz'
  exact ⟨F.mellinConvergent_delayedField hH (by linarith) hz' hgm
      (integrableOn_pastIntegrand (z := z) hz hg hgc ht),
    F.mellinConvergent_delayedField hH hz1 hz1' hfm
      (integrableOn_pastIntegrand_of_bounded (z := z - 1) hz1 hfm hbdd hfc ht)⟩

end SelfDecomposableExponent

end Hemigroup
