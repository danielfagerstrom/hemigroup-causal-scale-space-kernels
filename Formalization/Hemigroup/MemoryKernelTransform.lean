/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.ExponentDerivative

/-!
# The memory kernel's Laplace transform

Blueprint: `lem:memory-kernel-transform` (node 9.15), the clause split off from Lemma 9.1 when
its derivative half was proved.

`κ^{(x)} = b₀δ₀ + (1/x)k(t/x)dt` is the first object in the development that is neither finite
nor a probability measure, and that is the whole difficulty: `laplace` is a Bochner integral, so
every step needs its own integrability, and the measure is a sum of two pieces of quite different
character. The mathematical content is one substitution.
-/

namespace Hemigroup

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent) {x s : ℝ}

/-- **The substitution `τ = t/x`.** The `L¹` normalisation of the dilated kernel is exactly what
makes this an equality rather than a proportionality. -/
theorem integral_dilate_k (hx : 0 < x) (s : ℝ) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(s * t)) * (F.k (t / x) / x))
      = ∫ τ in Ioi (0 : ℝ), Real.exp (-(x * s * τ)) * F.k τ := by
  have h := integral_comp_mul_left_Ioi
    (fun u => Real.exp (-(s * u)) * (F.k (u / x) / x)) 0 hx
  rw [mul_zero] at h
  have hg : ∀ τ : ℝ, Real.exp (-(s * (x * τ))) * (F.k (x * τ / x) / x)
      = x⁻¹ * (Real.exp (-(x * s * τ)) * F.k τ) := by
    intro τ
    rw [mul_div_cancel_left₀ τ (ne_of_gt hx), show -(s * (x * τ)) = -(x * s * τ) by ring]
    field_simp
  have hx' : x ≠ 0 := ne_of_gt hx
  calc (∫ t in Ioi (0 : ℝ), Real.exp (-(s * t)) * (F.k (t / x) / x))
      = x • ∫ τ in Ioi (0 : ℝ), Real.exp (-(s * (x * τ))) * (F.k (x * τ / x) / x) := by
        rw [h, smul_smul, mul_inv_cancel₀ hx', one_smul]
    _ = ∫ τ in Ioi (0 : ℝ), Real.exp (-(x * s * τ)) * F.k τ := by
        simp_rw [hg]
        rw [integral_const_mul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hx', one_mul]

/-- The dilated kernel is integrable against the exponential, by the substitution above and
`integrableOn_exp_mul_k`. -/
theorem integrableOn_dilate_k (hx : 0 < x) (hs : 0 < s) :
    IntegrableOn (fun t => Real.exp (-(s * t)) * (F.k (t / x) / x)) (Ioi 0) := by
  have hbase : IntegrableOn (fun τ => Real.exp (-(x * s * τ)) * F.k τ) (Ioi 0) :=
    F.integrableOn_exp_mul_k (mul_pos hx hs)
  have h := (integrableOn_Ioi_comp_mul_left_iff
    (fun u => Real.exp (-(s * u)) * (F.k (u / x) / x)) 0 hx).mp
  rw [mul_zero] at h
  refine (h ?_)
  have heq : ∀ τ ∈ Ioi (0 : ℝ), Real.exp (-(s * (x * τ))) * (F.k (x * τ / x) / x)
      = x⁻¹ * (Real.exp (-(x * s * τ)) * F.k τ) := by
    intro τ _
    rw [mul_div_cancel_left₀ τ (ne_of_gt hx), show -(s * (x * τ)) = -(x * s * τ) by ring]
    field_simp
  exact IntegrableOn.congr_fun (hbase.const_mul x⁻¹) (fun τ hτ => (heq τ hτ).symm)
    measurableSet_Ioi

/-- **`lem:memory-kernel-transform`** (node 9.15): `s · κ̂^{(x)}(s) = φ_x(s)`, so the symbol is
`s` times the memory kernel's transform. -/
theorem laplace_memoryKernel (hx : 0 < x) (hs : 0 < s) :
    laplace (F.memoryKernel x) s = F.symbol x s / s := by
  have hxs : 0 < x * s := mul_pos hx hs
  have hdens : AEMeasurable (fun t : ℝ => ENNReal.ofReal (F.k (t / x) / x))
      (volume.restrict (Ioi 0)) := by
    have hk : AEMeasurable (fun t : ℝ => F.k (t / x)) (volume.restrict (Ioi 0)) := by
      have := (aemeasurable_of_antitoneOn (antitoneOn_comp_div F.k_antitone hx))
      exact this
    exact ((hk.div_const x).ennreal_ofReal)
  have hlt : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ENNReal.ofReal (F.k (t / x) / x) < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hnn : AEMeasurable (fun t : ℝ => (F.k (t / x) / x).toNNReal)
      (volume.restrict (Ioi (0 : ℝ))) :=
    ((aemeasurable_of_antitoneOn (antitoneOn_comp_div F.k_antitone hx)).div_const x).real_toNNReal
  have hI1 : Integrable (fun t : ℝ => Real.exp (-(s * t)))
      (ENNReal.ofReal F.b₀ • Measure.dirac (0 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  have hI2 : Integrable (fun t : ℝ => Real.exp (-(s * t)))
      ((volume.restrict (Ioi (0 : ℝ))).withDensity fun t => ENNReal.ofReal (F.k (t / x) / x)) := by
    rw [show (fun t : ℝ => ENNReal.ofReal (F.k (t / x) / x))
        = (fun t : ℝ => ((F.k (t / x) / x).toNNReal : ℝ≥0∞)) from rfl,
      integrable_withDensity_iff_integrable_smul₀ hnn]
    refine IntegrableOn.congr_fun (F.integrableOn_dilate_k hx hs) (fun t ht => ?_)
      measurableSet_Ioi
    have hkt : 0 ≤ F.k (t / x) / x :=
      div_nonneg (F.k_nonneg _ (mem_Ioi.mpr (div_pos (mem_Ioi.mp ht) hx))) hx.le
    rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ hkt]
    ring
  rw [laplace, memoryKernel, integral_add_measure hI1 hI2, integral_smul_measure,
    integral_dirac, integral_withDensity_eq_integral_toReal_smul₀ hdens hlt]
  have hpt : ∀ t ∈ Ioi (0 : ℝ),
      (ENNReal.ofReal (F.k (t / x) / x)).toReal • Real.exp (-(s * t))
        = Real.exp (-(s * t)) * (F.k (t / x) / x) := by
    intro t ht
    have hkt : 0 ≤ F.k (t / x) / x :=
      div_nonneg (F.k_nonneg _ (mem_Ioi.mpr (div_pos (mem_Ioi.mp ht) hx))) hx.le
    rw [smul_eq_mul, ENNReal.toReal_ofReal hkt]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, F.integral_dilate_k hx s, symbol,
    (F.hasDerivAt_toRealExponent hxs).deriv, ENNReal.toReal_ofReal F.b₀_nonneg]
  simp only [mul_zero, neg_zero, Real.exp_zero, smul_eq_mul, mul_one]
  field_simp

/-- The transform of `κ^{(x)}` converges: an infinite measure, so nothing about it is automatic,
but the integrability is the one already proved for the substitution. -/
theorem laplaceL_memoryKernel_ne_top (hx : 0 < x) (hs : 0 < s) :
    laplaceL (F.memoryKernel x) s ≠ ⊤ := by
  have hdens : AEMeasurable (fun t : ℝ => ENNReal.ofReal (F.k (t / x) / x))
      (volume.restrict (Ioi 0)) :=
    ((aemeasurable_of_antitoneOn
      (antitoneOn_comp_div F.k_antitone hx)).div_const x).ennreal_ofReal
  rw [laplaceL, memoryKernel, lintegral_add_measure, lintegral_smul_measure, lintegral_dirac,
    lintegral_withDensity_eq_lintegral_mul₀ hdens (by fun_prop)]
  refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top, ?_⟩
  have hpt : ∀ t ∈ Ioi (0 : ℝ),
      (fun t => ENNReal.ofReal (F.k (t / x) / x)) t * ENNReal.ofReal (Real.exp (-(s * t)))
        = ENNReal.ofReal (Real.exp (-(s * t)) * (F.k (t / x) / x)) := by
    intro t ht
    have hkt : 0 ≤ F.k (t / x) / x :=
      div_nonneg (F.k_nonneg _ (mem_Ioi.mpr (div_pos (mem_Ioi.mp ht) hx))) hx.le
    rw [← ENNReal.ofReal_mul hkt, mul_comm]
  simp only [Pi.mul_apply]
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt]
  exact lintegral_ofReal_ne_top_of_integrableOn (F.integrableOn_dilate_k hx hs)

/-- `lem:memory-kernel-transform` in the `ℝ≥0∞` reading, which is the form the Sonine identity
compares against — a Bochner integral would leave the degenerate case ambiguous. -/
theorem laplaceL_memoryKernel (hx : 0 < x) (hs : 0 < s) :
    laplaceL (F.memoryKernel x) s = ENNReal.ofReal (F.symbol x s / s) := by
  rw [← F.laplace_memoryKernel hx hs, laplace_eq_toReal_laplaceL,
    ENNReal.ofReal_toReal (F.laplaceL_memoryKernel_ne_top hx hs)]

/-! ## Nondegeneracy, in the form the Sonine identity needs

Axiom (ND) says `F ≢ 0`. On the representation side that is exactly "the drift or the Lévy
density is somewhere positive", and what every downstream statement actually consumes is the
consequence below: the symbol never vanishes. Without it `κ^{(x)}` is the zero measure and the
Sonine identity is false, so this is a hypothesis and not a lemma. -/

/-- Axiom (ND) read off the representation. -/
def Nondegenerate (F : SelfDecomposableExponent) : Prop :=
  0 < F.b₀ ∨ ∃ t : ℝ, 0 < t ∧ 0 < F.k t

/-- **(ND) makes `F'` strictly positive.** If the drift vanishes the Lévy density carries it:
`k` is nonincreasing, so a single positive value makes it positive on a whole initial interval,
and the exponential is bounded below there. -/
theorem deriv_toRealExponent_pos (hnd : F.Nondegenerate) {u : ℝ} (hu : 0 < u) :
    0 < deriv F.toRealExponent u := by
  rw [(F.hasDerivAt_toRealExponent hu).deriv]
  have hnn : 0 ≤ ∫ t in Ioi (0 : ℝ), Real.exp (-(u * t)) * F.k t :=
    setIntegral_nonneg measurableSet_Ioi fun t ht =>
      mul_nonneg (Real.exp_pos _).le (F.k_nonneg t ht)
  rcases hnd with hb | ⟨t₀, ht₀, hkt₀⟩
  · linarith
  · have hpos : 0 < ∫ t in Ioi (0 : ℝ), Real.exp (-(u * t)) * F.k t := by
      set c : ℝ := Real.exp (-(u * t₀)) * F.k t₀ with hc
      have hcpos : 0 < c := mul_pos (Real.exp_pos _) hkt₀
      have hlow : ∀ t ∈ Ioc (0 : ℝ) t₀, c ≤ Real.exp (-(u * t)) * F.k t := by
        intro t ht
        refine mul_le_mul (Real.exp_le_exp.mpr (by nlinarith [ht.2, ht.1]))
          (F.k_antitone (mem_Ioi.mpr ht.1) (mem_Ioi.mpr ht₀) ht.2) hkt₀.le (Real.exp_pos _).le
      have hsmall : c * t₀ ≤ ∫ t in Ioc (0 : ℝ) t₀, Real.exp (-(u * t)) * F.k t := by
        have hint : IntegrableOn (fun t => Real.exp (-(u * t)) * F.k t) (Ioc 0 t₀) :=
          (F.integrableOn_exp_mul_k hu).mono_set Ioc_subset_Ioi_self
        have h := setIntegral_ge_of_const_le measurableSet_Ioc
          (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) hlow hint
        rwa [measureReal_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal ht₀.le,
          smul_eq_mul, mul_comm] at h
      have hmono : (∫ t in Ioc (0 : ℝ) t₀, Real.exp (-(u * t)) * F.k t)
          ≤ ∫ t in Ioi (0 : ℝ), Real.exp (-(u * t)) * F.k t := by
        refine setIntegral_mono_set (F.integrableOn_exp_mul_k hu) ?_
          (HasSubset.Subset.eventuallyLE Ioc_subset_Ioi_self)
        exact (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht =>
          mul_nonneg (Real.exp_pos _).le (F.k_nonneg t ht))
      nlinarith [mul_pos hcpos ht₀]
    linarith [F.b₀_nonneg]

/-- **The symbol never vanishes**, which is what the Sonine identity consumes. -/
theorem symbol_pos (hnd : F.Nondegenerate) (hx : 0 < x) (hs : 0 < s) : 0 < F.symbol x s :=
  mul_pos hs (F.deriv_toRealExponent_pos hnd (mul_pos hx hs))

/-! ## The two renderings of (ND) agree

Chapter 9 states (ND) on the representation (`Nondegenerate`: the drift or the density is
somewhere positive); the headline theorems state it on the exponent
(`∃ s₀ > 0, F.exponent s₀ ≠ 0`, the article's `F ≢ 0`). Fidelity review finding R4: the two had
no bridge. They are equivalent, and the lemma below is the bridge. -/

/-- The exponent is strictly increasing on `(0,∞)` under (ND): its derivative is positive there
(`deriv_toRealExponent_pos`) and it is continuous, being differentiable. -/
theorem strictMonoOn_toRealExponent (hnd : F.Nondegenerate) :
    StrictMonoOn F.toRealExponent (Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) ?_ ?_
  · exact fun u hu => (F.hasDerivAt_toRealExponent (mem_Ioi.mp hu)).continuousAt.continuousWithinAt
  · intro u hu
    rw [interior_Ioi] at hu
    exact F.deriv_toRealExponent_pos hnd (mem_Ioi.mp hu)

/-- **The two readings of (ND) coincide.** `F ≢ 0` on `(0,∞)` iff the drift or the Lévy density
is somewhere positive. (⇒): with `b₀ = 0` and `k = 0` on `(0,∞)` the exponent is `0`. (⇐): the
exponent is then strictly increasing on `(0,∞)`, so `F(1) > F(1/2) ≥ 0`. -/
theorem nondegenerate_iff_exists_exponent_ne_zero (F : SelfDecomposableExponent) :
    F.Nondegenerate ↔ ∃ s₀ : ℝ, 0 < s₀ ∧ F.exponent s₀ ≠ 0 := by
  constructor
  · intro hnd
    refine ⟨1, one_pos, fun h0 => ?_⟩
    have hlt := F.strictMonoOn_toRealExponent hnd (mem_Ioi.mpr (by norm_num : (0:ℝ) < 1/2))
      (mem_Ioi.mpr one_pos) (by norm_num)
    have h1 : F.toRealExponent 1 = 0 := by simp [toRealExponent, h0]
    have hnn : 0 ≤ F.toRealExponent (1/2) := ENNReal.toReal_nonneg
    linarith
  · rintro ⟨s₀, hs₀, hne⟩
    by_contra hnd
    simp only [Nondegenerate, not_or, not_lt, not_exists, not_and] at hnd
    obtain ⟨hb, hk⟩ := hnd
    have hb0 : F.b₀ = 0 := le_antisymm hb F.b₀_nonneg
    apply hne
    simp only [exponent, levyExponentD, hb0, zero_mul, ENNReal.ofReal_zero, zero_add, levyJump]
    refine (setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)).trans lintegral_zero
    have : F.k t = 0 := le_antisymm (hk t (mem_Ioi.mp ht)) (F.k_nonneg t ht)
    simp [this]

end SelfDecomposableExponent

end Hemigroup
