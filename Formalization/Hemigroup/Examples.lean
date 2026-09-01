/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Hemigroup.Construction
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# Chapter 8's exponents, as instances

Blueprint: `blueprint/src/parts/08-examples-moments.tex`.

Chapter 7 says which `F` are admissible; chapter 8 exhibits some. Exhibiting one means building a
`SelfDecomposableExponent`, and five of its six fields are immediate for any concrete `k`. The
sixth, `ne_top`, is the only one with content, and it is the same content every time: the
exponent converges iff `k` is integrable at the origin and `k t / t` is integrable at infinity.

`levyExponentD_ne_top_of_integrableOn` below is that criterion, stated once. The two-sided split
is forced by the shape of the integrand and not by convenience: `1 - e^{-st}` is comparable to
`st` near the origin, which cancels the `1/t` and leaves `k` itself, and is bounded by `1` at
infinity, which leaves `k t / t`. So the two halves genuinely test different things — the stable
family's `k` is *unbounded* at the origin and still integrable there, while the Dickman ray's `k`
has compact support and so is trivially integrable at infinity.

## The normalisation `k 0 = 0` is not free

`SelfDecomposableExponent` fixes `k 0 = 0` so that the family's lower endpoint `x = 0` is a case
of the general formula rather than a separate definition (see `Construction.lean`). Every kernel
in this chapter is therefore written with an `if 0 < t` guard: `e^{-t}` and the constant `1` are
both nonzero at the origin, and dropping the guard would make `k_zero` unprovable rather than
merely inelegant. The guard costs nothing downstream, `{0}` being null for every integral here.
-/

namespace Hemigroup

open MeasureTheory Set
open scoped ENNReal

variable {k : ℝ → ℝ} {s t : ℝ}

/-! ## A finiteness criterion -/

/-- Turning an `IntegrableOn` hypothesis into the `≠ ⊤` form the exponent is stated in. -/
lemma lintegral_ofReal_ne_top_of_integrableOn {f : ℝ → ℝ} {S : Set ℝ} (hf : IntegrableOn f S) :
    (∫⁻ t in S, ENNReal.ofReal (f t)) ≠ ⊤ := by
  refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun t => ?_) hf.hasFiniteIntegral)
  rw [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal (le_abs_self _)

/-- **The criterion.** The Lévy exponent of a density `k` converges at every `s ≥ 0` as soon as
`k` is integrable on `(0,1]` and `k t / t` is integrable on `(1,∞)`.

This is the only nontrivial obligation in exhibiting a concrete admissible exponent, and it is
discharged here once for all of chapter 8. -/
lemma levyJump_ne_top_of_integrableOn (hk : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ k t) (hs : 0 ≤ s)
    (h0 : (∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (k t)) ≠ ⊤)
    (h1 : (∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (k t / t)) ≠ ⊤) :
    levyJump k s ≠ ⊤ := by
  have hsplit : volume.restrict (Ioi (0 : ℝ))
      = volume.restrict (Ioc (0 : ℝ) 1) + volume.restrict (Ioi (1 : ℝ)) := by
    rw [← Measure.restrict_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi,
      Ioc_union_Ioi_eq_Ioi zero_le_one]
  rw [levyJump, hsplit, lintegral_add_measure]
  refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
  · -- near the origin: `(1 - e^{-st}) k t / t ≤ s * k t`
    have hmono : (∫⁻ t in Ioc (0 : ℝ) 1,
          ENNReal.ofReal ((1 - Real.exp (-(s * t))) * k t / t))
        ≤ ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal s * ENNReal.ofReal (k t) := by
      refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioc).mpr ?_)
      filter_upwards with t ht
      have htpos : (0 : ℝ) < t := ht.1
      have hkt : 0 ≤ k t := hk t (mem_Ioi.mpr htpos)
      rw [← ENNReal.ofReal_mul hs]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [div_le_iff₀ htpos]
      have : (1 - Real.exp (-(s * t))) * k t ≤ (s * t) * k t :=
        mul_le_mul_of_nonneg_right (one_sub_exp_neg_le (s * t)) hkt
      nlinarith [this]
    refine ne_of_lt (lt_of_le_of_lt hmono ?_)
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr h0)
  · -- at infinity: `1 - e^{-st} ≤ 1`
    have hmono : (∫⁻ t in Ioi (1 : ℝ),
          ENNReal.ofReal ((1 - Real.exp (-(s * t))) * k t / t))
        ≤ ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (k t / t) := by
      refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).mpr ?_)
      filter_upwards with t ht
      have htpos : (0 : ℝ) < t := lt_trans zero_lt_one (mem_Ioi.mp ht)
      have hkt : 0 ≤ k t := hk t (mem_Ioi.mpr htpos)
      refine ENNReal.ofReal_le_ofReal ?_
      have hle : (1 - Real.exp (-(s * t))) * k t ≤ k t := by
        nlinarith [Real.exp_pos (-(s * t))]
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_right hle (inv_nonneg.mpr htpos.le)
    exact ne_of_lt (lt_of_le_of_lt hmono (lt_top_iff_ne_top.mpr h1))

/-- The criterion, in the form the structure field asks for. -/
lemma levyExponentD_ne_top_of_integrableOn {b₀ : ℝ} (hk : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ k t) (hs : 0 ≤ s)
    (h0 : (∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (k t)) ≠ ⊤)
    (h1 : (∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (k t / t)) ≠ ⊤) :
    levyExponentD b₀ k s ≠ ⊤ :=
  ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, levyJump_ne_top_of_integrableOn hk hs h0 h1⟩

/-! ## The Gamma family, and the leaky integrator as its unit case

`k(t) = γ e^{-t}`. The closed form `F(s) = γ log(1+s)` is Frullani's integral and is proved
separately; admissibility needs only the estimates above. -/

/-- The Lévy density of the Gamma family, `γ e^{-t}`, guarded at the origin. -/
noncomputable def gammaDensity (γ : ℝ) : ℝ → ℝ := fun t => if 0 < t then γ * Real.exp (-t) else 0

lemma gammaDensity_nonneg {γ : ℝ} (hγ : 0 ≤ γ) (t : ℝ) : 0 ≤ gammaDensity γ t := by
  unfold gammaDensity
  split
  · positivity
  · exact le_rfl

lemma gammaDensity_antitoneOn {γ : ℝ} (hγ : 0 ≤ γ) :
    AntitoneOn (gammaDensity γ) (Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  simp only [gammaDensity, if_pos (mem_Ioi.mp hx), if_pos (mem_Ioi.mp hy)]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hγ

/-- **The Gamma family**, blueprint `prop:gamma-family` (Proposition 8.2): admissibility. -/
noncomputable def gammaExponent (γ : ℝ) (hγ : 0 ≤ γ) : SelfDecomposableExponent where
  b₀ := 0
  k := gammaDensity γ
  b₀_nonneg := le_rfl
  k_nonneg := fun t _ => gammaDensity_nonneg hγ t
  k_antitone := gammaDensity_antitoneOn hγ
  k_zero := by simp [gammaDensity]
  ne_top := by
    intro s hs
    refine levyExponentD_ne_top_of_integrableOn (fun t _ => gammaDensity_nonneg hγ t) hs ?_ ?_
    · -- bounded by `γ` on a set of finite measure
      have hle : (∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (gammaDensity γ t))
          ≤ ∫⁻ _ in Ioc (0 : ℝ) 1, ENNReal.ofReal γ := by
        refine lintegral_mono fun t => ENNReal.ofReal_le_ofReal ?_
        unfold gammaDensity
        split
        · nlinarith [Real.exp_le_one_iff.mpr (by linarith : -t ≤ 0), Real.exp_pos (-t)]
        · exact hγ
      refine ne_of_lt (lt_of_le_of_lt hle ?_)
      rw [setLIntegral_const, Real.volume_Ioc]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
    · -- `k t / t ≤ γ e^{-t}` for `t ≥ 1`, which is integrable
      have hle : (∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (gammaDensity γ t / t))
          ≤ ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (γ * Real.exp (-1 * t)) := by
        refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).mpr ?_)
        filter_upwards with t ht
        have ht1 : (1 : ℝ) < t := mem_Ioi.mp ht
        have htpos : (0 : ℝ) < t := lt_trans zero_lt_one ht1
        refine ENNReal.ofReal_le_ofReal ?_
        simp only [gammaDensity, if_pos htpos]
        rw [div_le_iff₀ htpos, neg_one_mul]
        nlinarith [Real.exp_pos (-t), mul_nonneg hγ (Real.exp_pos (-t)).le]
      refine ne_of_lt (lt_of_le_of_lt hle ?_)
      refine lt_top_iff_ne_top.mpr (lintegral_ofReal_ne_top_of_integrableOn ?_)
      exact ((exp_neg_integrableOn_Ioi (1 : ℝ) zero_lt_one).const_mul γ)

/-- **The leaky integrator**, `k(t) = e^{-t}`: the Gamma family at `γ = 1`. -/
noncomputable def leakyIntegrator : SelfDecomposableExponent := gammaExponent 1 zero_le_one

/-! ## The Dickman rays

`k = 1_{(0,τ)}`, the compactly supported extreme of the class: by `rem:extreme-rays` these are
exactly the extreme rays of the admissible cone, so every admissible exponent is a superposition
of these and drift. Their `F` is the Dickman exponent `Ein(τs) = ∫₀^τ (1 - e^{-st}) dt / t`,
which has no elementary closed form; what the chapter uses is that a `k` with a hard cutoff is
admissible at all, which is what makes the extreme rays inhabit the cone they generate. -/

/-- The Lévy density of the Dickman ray of delay `τ`: `1` on `(0,τ)` and `0` elsewhere. -/
noncomputable def dickmanDensity (τ : ℝ) : ℝ → ℝ := fun t => if 0 < t ∧ t < τ then 1 else 0

lemma dickmanDensity_nonneg (τ t : ℝ) : 0 ≤ dickmanDensity τ t := by
  unfold dickmanDensity
  split
  · exact zero_le_one
  · exact le_rfl

lemma dickmanDensity_le_one (τ t : ℝ) : dickmanDensity τ t ≤ 1 := by
  unfold dickmanDensity
  split
  · exact le_rfl
  · exact zero_le_one

lemma dickmanDensity_antitoneOn (τ : ℝ) : AntitoneOn (dickmanDensity τ) (Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  unfold dickmanDensity
  by_cases hy1 : y < τ
  · rw [if_pos ⟨mem_Ioi.mp hy, hy1⟩, if_pos ⟨mem_Ioi.mp hx, lt_of_le_of_lt hxy hy1⟩]
  · rw [if_neg (fun h => hy1 h.2)]
    split
    · exact zero_le_one
    · exact le_rfl

lemma dickmanDensity_eq_zero_of_le {τ t : ℝ} (h : τ ≤ t) : dickmanDensity τ t = 0 := by
  rw [dickmanDensity, if_neg (fun hc => absurd hc.2 (not_lt.mpr h))]

/-- **The Dickman ray of delay `τ`**, `k = 1_{(0,τ)}`. -/
noncomputable def dickmanExponent (τ : ℝ) : SelfDecomposableExponent where
  b₀ := 0
  k := dickmanDensity τ
  b₀_nonneg := le_rfl
  k_nonneg := fun t _ => dickmanDensity_nonneg τ t
  k_antitone := dickmanDensity_antitoneOn τ
  k_zero := by simp [dickmanDensity]
  ne_top := by
    intro s hs
    refine levyExponentD_ne_top_of_integrableOn (fun t _ => dickmanDensity_nonneg τ t) hs ?_ ?_
    · have hle : (∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (dickmanDensity τ t))
          ≤ ∫⁻ _ in Ioc (0 : ℝ) 1, (1 : ℝ≥0∞) := by
        refine lintegral_mono fun t => ?_
        simpa using ENNReal.ofReal_le_ofReal (dickmanDensity_le_one τ t)
      refine ne_of_lt (lt_of_le_of_lt hle ?_)
      rw [setLIntegral_const, Real.volume_Ioc, one_mul]
      exact ENNReal.ofReal_lt_top
    · -- past the cutoff the density is bounded by `1/t`, and below it the interval is bounded
      have hle : (∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (dickmanDensity τ t / t))
          ≤ ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (dickmanDensity τ t) := by
        refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).mpr ?_)
        filter_upwards with t ht
        have ht1 : (1 : ℝ) < t := mem_Ioi.mp ht
        refine ENNReal.ofReal_le_ofReal ?_
        rw [div_le_iff₀ (lt_trans zero_lt_one ht1)]
        nlinarith [dickmanDensity_nonneg τ t]
      refine ne_of_lt (lt_of_le_of_lt hle ?_)
      have hle2 : (∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (dickmanDensity τ t))
          ≤ ∫⁻ t in Ioi (1 : ℝ), Set.indicator (Ioo (0 : ℝ) τ) (fun _ => (1 : ℝ≥0∞)) t := by
        refine lintegral_mono fun t => ?_
        by_cases ht : t ∈ Ioo (0 : ℝ) τ
        · simpa [Set.indicator_of_mem ht] using ENNReal.ofReal_le_ofReal (dickmanDensity_le_one τ t)
        · rw [Set.indicator_of_notMem ht, dickmanDensity, if_neg (fun hc => ht ⟨hc.1, hc.2⟩)]
          simp
      refine lt_of_le_of_lt hle2 ?_
      refine lt_of_le_of_lt (lintegral_mono_set (subset_univ _)) ?_
      rw [lintegral_indicator measurableSet_Ioo, setLIntegral_const, Measure.restrict_univ,
        Real.volume_Ioo, one_mul]
      exact ENNReal.ofReal_lt_top

end Hemigroup
