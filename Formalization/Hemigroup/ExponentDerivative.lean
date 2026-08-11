/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.Examples
import Hemigroup.MemoryKernel
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# `F' (s) = b₀ + ∫₀^∞ e^{-st} k(t) dt`

Blueprint: `lem:memory-kernel` (Lemma 9.1), and the tool chapter 8's closed forms are computed
with. Differentiation under the integral sign, which Mathlib has; the work is entirely in the
integrability side conditions, and those are worth stating separately because they are the
converse of chapter 8's admissibility criterion.

## The criterion runs both ways

`Examples.lean` proves that `k` integrable at the origin and `k t / t` integrable at infinity
make the exponent converge. Here the implication is reversed: the structure field `ne_top` — one
instance of it, at `s = 1` — *forces* both integrals to converge. So the criterion is not merely
sufficient but characteristic, and every `SelfDecomposableExponent` carries the integrability its
own analysis needs without a further hypothesis.

The reversal costs one inequality in the other direction, `1 - e^{-u} ≥ u/(1+u)`, which is
`e^u ≥ 1 + u` read as a bound on `e^{-u}`. Together with `one_sub_exp_neg_le` it pins
`1 - e^{-u}` between `u/(1+u)` and `u`, and every estimate in this file is one of those two.
-/

namespace Hemigroup

open MeasureTheory Set Filter
open scoped ENNReal Topology

variable {k : ℝ → ℝ} {s : ℝ}

/-! ## The lower estimate, and two conversions -/

/-- `u/(1+u) ≤ 1 - e^{-u}` for `u ≥ 0`: the converse of `one_sub_exp_neg_le`, and what makes the
admissibility criterion characteristic rather than merely sufficient. -/
theorem le_one_sub_exp_neg {u : ℝ} (hu : 0 ≤ u) : u / (1 + u) ≤ 1 - Real.exp (-u) := by
  have h1 : (0 : ℝ) < 1 + u := by linarith
  have h2 : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  have h3 : 1 + u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  rw [div_le_iff₀ h1]
  nlinarith [Real.exp_pos (-u), Real.exp_pos u]

/-- A nonnegative function with a finite `lintegral` of its `ofReal` is integrable. -/
theorem integrableOn_of_lintegral_ofReal_ne_top {f : ℝ → ℝ} {S : Set ℝ}
    (hmeas : AEStronglyMeasurable f (volume.restrict S))
    (h : (∫⁻ t in S, ENNReal.ofReal (f t)) ≠ ⊤) (hnn : ∀ᵐ t ∂(volume.restrict S), 0 ≤ f t) :
    IntegrableOn f S := by
  refine ⟨hmeas, ?_⟩
  refine lt_of_le_of_lt (lintegral_mono_ae ?_) (lt_top_iff_ne_top.mpr h)
  filter_upwards [hnn] with t ht
  rw [Real.enorm_eq_ofReal ht]

/-! ## Every exponent is integrable where its own analysis needs it -/

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent)

lemma aemeasurable_k {S : Set ℝ} (hS : S ⊆ Ioi 0) :
    AEMeasurable F.k (volume.restrict S) :=
  (aemeasurable_of_antitoneOn F.k_antitone).mono_measure (Measure.restrict_mono hS le_rfl)

lemma levyJump_one_ne_top : levyJump F.k 1 ≠ ⊤ :=
  (ENNReal.add_ne_top.mp (F.ne_top 1 zero_le_one)).2

/-- **`k` is integrable at the origin**, forced by `ne_top` rather than assumed. -/
theorem integrableOn_k : IntegrableOn F.k (Ioc 0 1) := by
  refine integrableOn_of_lintegral_ofReal_ne_top
    ((F.aemeasurable_k Ioc_subset_Ioi_self).aestronglyMeasurable) ?_
    ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall
      (fun t ht => F.k_nonneg t (mem_Ioi.mpr ht.1))))
  -- `(1 - e^{-t}) k t / t ≥ k t / 2` on `(0,1]`
  have hle : (∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (F.k t))
      ≤ 2 * ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.exp (-(1 * t))) * F.k t / t) := by
    rw [← lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
    refine le_trans (lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioc).mpr ?_))
      (lintegral_mono_set Ioc_subset_Ioi_self)
    filter_upwards with t ht
    have htpos : (0 : ℝ) < t := ht.1
    have hkt : 0 ≤ F.k t := F.k_nonneg t (mem_Ioi.mpr htpos)
    have hlow : t / (1 + t) ≤ 1 - Real.exp (-(1 * t)) := by
      rw [one_mul]; exact le_one_sub_exp_neg htpos.le
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    -- on `(0,1]` the lower estimate gives `1 - e^{-t} ≥ t/(1+t) ≥ t/2`
    have h1t : (0 : ℝ) < 1 + t := by linarith
    have hnn : 0 ≤ 1 - Real.exp (-(1 * t)) := le_trans (div_nonneg htpos.le h1t.le) hlow
    rw [div_le_iff₀ h1t] at hlow
    rw [← mul_div_assoc, le_div_iff₀ htpos]
    nlinarith [mul_nonneg hkt
      (by nlinarith [hlow, hnn, ht.2] : (0 : ℝ) ≤ 2 * (1 - Real.exp (-(1 * t))) - t)]
  exact ne_of_lt (lt_of_le_of_lt hle
    (ENNReal.mul_lt_top (by norm_num) (lt_top_iff_ne_top.mpr F.levyJump_one_ne_top)))

/-- **`k t / t` is integrable at infinity**, likewise forced. -/
theorem integrableOn_k_div : IntegrableOn (fun t => F.k t / t) (Ioi 1) := by
  refine integrableOn_of_lintegral_ofReal_ne_top
    (((F.aemeasurable_k (fun t ht => lt_trans zero_lt_one (mem_Ioi.mp ht))).div
      aemeasurable_id).aestronglyMeasurable) ?_
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun t ht =>
      div_nonneg (F.k_nonneg t (mem_Ioi.mpr (lt_trans zero_lt_one (mem_Ioi.mp ht))))
        (le_of_lt (lt_trans zero_lt_one (mem_Ioi.mp ht))))))
  have hle : (∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (F.k t / t))
      ≤ 2 * ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.exp (-(1 * t))) * F.k t / t) := by
    rw [← lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
    refine le_trans (lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).mpr ?_))
      (lintegral_mono_set (fun t ht => lt_trans zero_lt_one (mem_Ioi.mp ht)))
    filter_upwards with t ht
    have ht1 : (1 : ℝ) < t := mem_Ioi.mp ht
    have htpos : (0 : ℝ) < t := lt_trans zero_lt_one ht1
    have hkt : 0 ≤ F.k t := F.k_nonneg t (mem_Ioi.mpr htpos)
    have hlow : t / (1 + t) ≤ 1 - Real.exp (-(1 * t)) := by
      rw [one_mul]; exact le_one_sub_exp_neg htpos.le
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    -- past `1` the same estimate gives `1 - e^{-t} ≥ t/(1+t) ≥ 1/2`
    have h1t : (0 : ℝ) < 1 + t := by linarith
    have hnn : 0 ≤ 1 - Real.exp (-(1 * t)) := le_trans (div_nonneg htpos.le h1t.le) hlow
    rw [div_le_iff₀ h1t] at hlow
    rw [← mul_div_assoc, div_le_div_iff_of_pos_right htpos]
    nlinarith [mul_nonneg hkt
      (by nlinarith [hlow, hnn, ht1] : (0 : ℝ) ≤ 2 * (1 - Real.exp (-(1 * t))) - 1)]
  exact ne_of_lt (lt_of_le_of_lt hle
    (ENNReal.mul_lt_top (by norm_num) (lt_top_iff_ne_top.mpr F.levyJump_one_ne_top)))

/-- **The criterion is characteristic.** Both halves of `prop:admissibility-criterion` are not
merely sufficient for convergence but forced by it — a single instance of `ne_top`, at `s = 1`,
implies them. Collated so that the blueprint node covering both can carry one Lean tag. -/
theorem integrableOn_of_ne_top :
    IntegrableOn F.k (Ioc 0 1) ∧ IntegrableOn (fun t => F.k t / t) (Ioi 1) :=
  ⟨F.integrableOn_k, F.integrableOn_k_div⟩

/-- `k` is bounded past the origin, being nonincreasing. -/
lemma k_le_of_one_le {t : ℝ} (ht : 1 ≤ t) : F.k t ≤ F.k 1 :=
  F.k_antitone (mem_Ioi.mpr zero_lt_one) (mem_Ioi.mpr (lt_of_lt_of_le zero_lt_one ht)) ht

/-- **The dominating function of the differentiation**: `e^{-st} k(t)` is integrable on `(0,∞)`
for every `s > 0`. Integrable at the origin because `k` is, by `integrableOn_k`, the exponential
being bounded there; at infinity because `k` is bounded, being nonincreasing, and the exponential
decays. -/
theorem integrableOn_exp_mul_k (hs : 0 < s) :
    IntegrableOn (fun t => Real.exp (-(s * t)) * F.k t) (Ioi 0) := by
  rw [show Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 from (Ioc_union_Ioi_eq_Ioi zero_le_one).symm]
  refine IntegrableOn.union ?_ ?_
  · refine Integrable.mono' F.integrableOn_k
      (((Real.continuous_exp.comp (by fun_prop)).aestronglyMeasurable).mul
        (F.aemeasurable_k Ioc_subset_Ioi_self).aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    have hkt : 0 ≤ F.k t := F.k_nonneg t (mem_Ioi.mpr ht.1)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hkt)]
    nlinarith [Real.exp_le_one_iff.mpr (by nlinarith [ht.1] : -(s * t) ≤ 0), Real.exp_pos (-(s*t))]
  · refine Integrable.mono' (((exp_neg_integrableOn_Ioi (1 : ℝ) hs).const_mul (F.k 1)))
      (((Real.continuous_exp.comp (by fun_prop)).aestronglyMeasurable).mul
        (F.aemeasurable_k (fun t ht => lt_trans zero_lt_one (mem_Ioi.mp ht))).aestronglyMeasurable)
      ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    have ht1 : (1 : ℝ) ≤ t := le_of_lt (mem_Ioi.mp ht)
    have hkt : 0 ≤ F.k t := F.k_nonneg t (mem_Ioi.mpr (lt_of_lt_of_le zero_lt_one ht1))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hkt), ← neg_mul,
      mul_comm (F.k 1)]
    exact mul_le_mul_of_nonneg_left (F.k_le_of_one_le ht1) (Real.exp_pos _).le

/-! ## Measurability, once

`k` is only nonincreasing on `(0,∞)`, so it is a.e. measurable for the restricted measure and
nothing more; every measurability side condition below routes through `aemeasurable_k`. -/

lemma aestronglyMeasurable_integrand (x : ℝ) {S : Set ℝ} (hS : S ⊆ Ioi 0) :
    AEStronglyMeasurable (fun t => (1 - Real.exp (-(x * t))) * F.k t / t)
      (volume.restrict S) := by
  have hcont : Continuous fun t : ℝ => 1 - Real.exp (-(x * t)) := by fun_prop
  exact ((hcont.measurable.aemeasurable.mul (F.aemeasurable_k hS)).div
    aemeasurable_id).aestronglyMeasurable

lemma aestronglyMeasurable_deriv (x : ℝ) {S : Set ℝ} (hS : S ⊆ Ioi 0) :
    AEStronglyMeasurable (fun t => Real.exp (-(x * t)) * F.k t) (volume.restrict S) := by
  have hcont : Continuous fun t : ℝ => Real.exp (-(x * t)) := by fun_prop
  exact (hcont.measurable.aemeasurable.mul (F.aemeasurable_k hS)).aestronglyMeasurable

/-- The integrand of the exponent itself is integrable: bounded by `s k(t)` at the origin and by
`k(t)/t` at infinity, which are the two halves of the criterion. -/
theorem integrableOn_exponent_integrand (hs : 0 ≤ s) :
    IntegrableOn (fun t => (1 - Real.exp (-(s * t))) * F.k t / t) (Ioi 0) := by
  rw [show Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 from (Ioc_union_Ioi_eq_Ioi zero_le_one).symm]
  have hmeas : ∀ S : Set ℝ, S ⊆ Ioi 0 →
      AEStronglyMeasurable (fun t => (1 - Real.exp (-(s * t))) * F.k t / t)
        (volume.restrict S) := fun S hS => F.aestronglyMeasurable_integrand s hS
  refine IntegrableOn.union ?_ ?_
  · refine Integrable.mono' (F.integrableOn_k.const_mul s) (hmeas _ Ioc_subset_Ioi_self) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    have htpos : (0 : ℝ) < t := ht.1
    have hkt : 0 ≤ F.k t := F.k_nonneg t (mem_Ioi.mpr htpos)
    have hnn : 0 ≤ 1 - Real.exp (-(s * t)) := by
      have : Real.exp (-(s * t)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith : -(s * t) ≤ 0)
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (mul_nonneg hnn hkt) htpos.le),
      div_le_iff₀ htpos]
    nlinarith [mul_le_mul_of_nonneg_right (one_sub_exp_neg_le (s * t)) hkt]
  · refine Integrable.mono' F.integrableOn_k_div
      (hmeas _ (fun t ht => lt_trans zero_lt_one (mem_Ioi.mp ht))) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    have htpos : (0 : ℝ) < t := lt_trans zero_lt_one (mem_Ioi.mp ht)
    have hkt : 0 ≤ F.k t := F.k_nonneg t (mem_Ioi.mpr htpos)
    have hnn : 0 ≤ 1 - Real.exp (-(s * t)) := by
      have : Real.exp (-(s * t)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith : -(s * t) ≤ 0)
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (mul_nonneg hnn hkt) htpos.le)]
    gcongr
    nlinarith [Real.exp_pos (-(s * t))]

/-! ## The exponent as a real integral, and its derivative -/

/-- The exponent read as a Bochner integral. `ne_top` is what makes the `ℝ≥0∞` and `ℝ` readings
agree, and it is a field of the structure, so no hypothesis beyond `s ≥ 0` is needed. -/
theorem toRealExponent_eq (hs : 0 ≤ s) :
    F.toRealExponent s
      = F.b₀ * s + ∫ t in Ioi (0 : ℝ), (1 - Real.exp (-(s * t))) * F.k t / t := by
  have hjump : levyJump F.k s ≠ ⊤ := (ENNReal.add_ne_top.mp (F.ne_top s hs)).2
  simp only [toRealExponent, exponent, levyExponentD]
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top hjump,
    ENNReal.toReal_ofReal (mul_nonneg F.b₀_nonneg hs)]
  congr 1
  refine (integral_eq_lintegral_of_nonneg_ae ?_
    (F.aestronglyMeasurable_integrand s subset_rfl)).symm
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
  have htpos : (0 : ℝ) < t := mem_Ioi.mp ht
  have hkt : 0 ≤ F.k t := F.k_nonneg t ht
  have hnn : 0 ≤ 1 - Real.exp (-(s * t)) := by
    have : Real.exp (-(s * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    linarith
  exact div_nonneg (mul_nonneg hnn hkt) htpos.le

/-- **`lem:memory-kernel`** (Lemma 9.1): `F'(s) = b₀ + ∫₀^∞ e^{-st} k(t) dt`.

Differentiation under the integral sign. The dominating function is `e^{-(s/2)t} k(t)`, valid on
the neighbourhood `(s/2, ∞)` of `s`, and it is integrable by `integrableOn_exp_mul_k` — which
needs no hypothesis, because `lem:criterion-converse` extracts the integrability from the
structure itself. -/
theorem hasDerivAt_toRealExponent (hs : 0 < s) :
    HasDerivAt F.toRealExponent
      (F.b₀ + ∫ t in Ioi (0 : ℝ), Real.exp (-(s * t)) * F.k t) s := by
  have hhalf : (0 : ℝ) < s / 2 := by linarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Ioi (0 : ℝ)))
      (F := fun x t => (1 - Real.exp (-(x * t))) * F.k t / t)
      (F' := fun x t => Real.exp (-(x * t)) * F.k t)
      (bound := fun t => Real.exp (-(s / 2 * t)) * F.k t)
      (x₀ := s) (s := Ioi (s / 2))
      (Ioi_mem_nhds (by linarith))
      (Filter.Eventually.of_forall fun x => F.aestronglyMeasurable_integrand x subset_rfl)
      (F.integrableOn_exponent_integrand hs.le)
      (F.aestronglyMeasurable_deriv s subset_rfl)
      ?bound (F.integrableOn_exp_mul_k hhalf) ?diff
  case bound =>
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht x hx => ?_)
    have htpos : (0 : ℝ) < t := mem_Ioi.mp ht
    have hkt : 0 ≤ F.k t := F.k_nonneg t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hkt)]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) hkt
    have : s / 2 ≤ x := le_of_lt (mem_Ioi.mp hx)
    nlinarith
  case diff =>
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht x _ => ?_)
    have htpos : (0 : ℝ) < t := mem_Ioi.mp ht
    have ht0 : t ≠ 0 := ne_of_gt htpos
    have hb0 : HasDerivAt (fun y : ℝ => y * t) t x := by
      simpa using (hasDerivAt_id x).mul_const t
    have hb : HasDerivAt (fun y : ℝ => -(y * t)) (-t) x := hb0.neg
    have h2 : HasDerivAt (fun y : ℝ => (1 - Real.exp (-(y * t))) * F.k t / t)
        (-(Real.exp (-(x * t)) * -t) * F.k t / t) x :=
      (((hb.exp).const_sub 1).mul_const (F.k t)).div_const t
    have heq : -(Real.exp (-(x * t)) * -t) * F.k t / t = Real.exp (-(x * t)) * F.k t := by
      rw [div_eq_iff ht0]; ring
    rwa [heq] at h2
  -- the drift term differentiates to `b₀`
  have hdrift : HasDerivAt (fun x : ℝ => F.b₀ * x) F.b₀ s := by
    simpa using (hasDerivAt_id s).const_mul F.b₀
  refine (hdrift.add key.2).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hs] with x hx
  exact F.toRealExponent_eq (le_of_lt (mem_Ioi.mp hx))

end SelfDecomposableExponent

end Hemigroup
