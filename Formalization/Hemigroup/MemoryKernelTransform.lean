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

end SelfDecomposableExponent

end Hemigroup
