/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.MellinData
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

open scoped Topology

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
theorem integrableOn_pastNorm (hz : 1 < z.re) (hf : Integrable f)
    (hcausal : ∀ r : ℝ, r < 0 → f r = 0) (ht : 0 < t) :
    IntegrableOn (fun y : ℝ => y ^ (z.re - 1) * |f (t - y)|) (Ioi 0) := by
  have hn : IntegrableOn (fun y : ℝ => ‖(y : ℂ) ^ (z - 1) * (f (t - y) : ℂ)‖) (Ioi 0) :=
    (integrableOn_pastIntegrand hz hf hcausal ht).norm
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

/-- `E[T₁^{-c}]` as a Bochner-integrable function: the outer factor of the Fubini side condition. -/
theorem integrable_rpow_neg (hH : F.StandingHypothesis) {c : ℝ} (hc : 0 < c)
    (hc' : c < F.zStar) : Integrable (fun τ : ℝ => τ ^ (-c)) F.lawT₁ := by
  have h0 := F.lawT₁_singleton_zero hH.1
  have hae := F.ae_mem_Ioi_lawT₁ h0
  refine ⟨by fun_prop, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hcalc : ∫⁻ τ, ‖τ ^ (-c)‖ₑ ∂F.lawT₁ = F.negMoment c := by
    rw [SelfDecomposableExponent.negMoment, Measure.restrict_eq_self_of_ae_mem hae]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with τ hτ
    rw [← ofReal_norm, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (mem_Ioi.mp hτ).le _)]
  rw [hcalc]
  exact lt_top_iff_ne_top.mpr (F.negMoment_ne_top_of_lt_zStar hc hc')

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
theorem integrable_delayed (hH : F.StandingHypothesis) {z : ℂ} (hz : 1 < z.re)
    (hz' : z.re < F.zStar) {f : ℝ → ℝ} (hfm : Measurable f) (hf : Integrable f)
    (hcausal : ∀ r : ℝ, r < 0 → f r = 0) {t : ℝ} (ht : 0 < t) :
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
      simpa only [MellinConvergent, smul_eq_mul] using integrableOn_pastIntegrand hz hf hcausal ht
    have hdil := (MellinConvergent.comp_mul_left (f := fun y : ℝ => ((f (t - y) : ℝ) : ℂ))
      (s := z) (mem_Ioi.mp hτ)).mpr hbase
    have hdil' : IntegrableOn
        (fun x : ℝ => (x : ℂ) ^ (z - 1) * ((f (t - τ * x) : ℝ) : ℂ)) (Ioi 0) := by
      simpa only [MellinConvergent, smul_eq_mul] using hdil
    refine hdil'.congr_fun (fun x hx => ?_) measurableSet_Ioi
    dsimp only [Function.uncurry]
    rw [mul_comm τ x]
  · have hC := integrableOn_pastNorm hz hf hcausal ht
    have heq : (fun τ : ℝ => ∫ x in Ioi (0 : ℝ),
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
theorem mellin_delayed_average (hH : F.StandingHypothesis) {z : ℂ} (hz : 1 < z.re)
    (hz' : z.re < F.zStar) {f : ℝ → ℝ} (hfm : Measurable f) (hf : Integrable f)
    (hcausal : ∀ r : ℝ, r < 0 → f r = 0) {t : ℝ} (ht : 0 < t) :
    mellin (fun x : ℝ => ∫ τ, (f (t - x * τ) : ℂ) ∂F.lawT₁) z
      = mellin (fun s => (F.profile s : ℂ)) z * riemannLiouville z f t := by
  have h0 := F.lawT₁_singleton_zero hH.1
  have hae := F.ae_mem_Ioi_lawT₁ h0
  have hzpos : 0 < z.re := by linarith
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
        integral_integral_swap (integrable_delayed hH hz hz' hfm hf hcausal ht)
    _ = ∫ τ, (τ : ℂ) ^ (-z) * pastIntegral z f t ∂F.lawT₁ := by
        refine integral_congr_ae ?_
        filter_upwards [hae] with τ hτ using hdil τ (mem_Ioi.mp hτ)
    _ = (∫ τ, (τ : ℂ) ^ (-z) ∂F.lawT₁) * pastIntegral z f t := integral_mul_const _ _
    _ = mellin (fun s => (F.profile s : ℂ)) z * riemannLiouville z f t := by
        rw [F.mellin_profile hH hzpos hz',
          ← mul_riemannLiouville hzpos hcausal ht (integrableOn_pastIntegrand hz hf hcausal ht)]
        ring

end Core

end Hemigroup
