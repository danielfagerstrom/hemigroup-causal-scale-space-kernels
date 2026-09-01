/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the MIT license as described in the file LICENSES/MIT.txt.
Authors: Daniel Fagerström
-/
import Hemigroup.ClosedForms
import Hemigroup.MemoryKernelTransform

/-!
# Sonine conservation

Blueprint: `thm:sonine-conservation` (Theorem 9.5). `κ^{(x)} ∗ ℓ^{(x)} = \mathrm{Leb}` on
`[0,∞)`.

The argument is a transform comparison and nothing else, which is why it can be stated against an
arbitrary `ℓ` meeting the potential-kernel specification rather than against a chosen one: the
theorem does not depend on how existence is discharged, and so does not wait on it.

Everything it needs was built for other reasons — `laplaceL_conv` in chapter 4,
`laplaceL_memoryKernel` for node 9.15, `symbol_pos` from axiom (ND), and
`laplaceL_injective_of_ne_top` from the Phase 3 extension of ledger A6 to measures that are not
finite. That last one is the reason this chapter needed the extension at all: `κ^{(x)}`,
`ℓ^{(x)}` and Lebesgue measure are none of them finite, and this identity compares them.
-/

namespace Hemigroup

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- Lebesgue measure on the half-line has transform `1/s`. -/
theorem laplaceL_volume_Ici {s : ℝ} (hs : 0 < s) :
    laplaceL (volume.restrict (Ici (0 : ℝ))) s = ENNReal.ofReal (1 / s) := by
  have hset : volume.restrict (Ici (0 : ℝ)) = volume.restrict (Ioi (0 : ℝ)) :=
    Measure.restrict_congr_set Ioi_ae_eq_Ici.symm
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-(s * t))) (Ioi 0) := by
    have := exp_neg_integrableOn_Ioi (0 : ℝ) hs
    refine IntegrableOn.congr_fun this (fun t _ => ?_) measurableSet_Ioi
    rw [neg_mul]
  have hne : laplaceL (volume.restrict (Ici (0 : ℝ))) s ≠ ⊤ := by
    rw [hset, laplaceL]
    exact lintegral_ofReal_ne_top_of_integrableOn hint
  rw [← ENNReal.ofReal_toReal hne, ← laplace_eq_toReal_laplaceL, laplace, hset]
  rw [show (∫ t, Real.exp (-(s * t)) ∂(volume.restrict (Ioi (0 : ℝ))))
      = ∫ t in Ioi (0 : ℝ), Real.exp (-(s * t)) from rfl, integral_exp_neg_mul_Ioi hs]

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent) {x s : ℝ}

instance instSFiniteMemoryKernel : SFinite (F.memoryKernel x) := by
  unfold memoryKernel
  infer_instance

/-- The memory kernel is carried by `[0,∞)`: the atom sits at the origin and the density lives
on `(0,∞)`. -/
theorem isCausal_memoryKernel : IsCausal (F.memoryKernel x) := by
  rw [IsCausal, memoryKernel, Measure.add_apply, Measure.smul_apply,
    withDensity_apply _ measurableSet_Iio, Measure.dirac_apply' _ measurableSet_Iio]
  rw [Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi, Ioo_self]
  simp

/-- **`thm:sonine-conservation`.** Stated against an arbitrary `ℓ` meeting the potential-kernel
specification, so that it does not wait on `lem:potential-kernel`'s existence half. The identity
here is restricted to `[0,∞)`; `sonine_conservation'` below is the unrestricted equality of
measures on `ℝ` that the article states. -/
theorem sonine_conservation (hnd : F.Nondegenerate) (hx : 0 < x) (ℓ : Measure ℝ) [SFinite ℓ]
    (hcaus : IsCausal ℓ)
    (hℓ : ∀ s : ℝ, 0 < s → laplaceL ℓ s = ENNReal.ofReal (F.symbol x s)⁻¹) :
    (F.memoryKernel x ∗ ℓ).restrict (Ici 0) = volume.restrict (Ici 0) := by
  have hkey : ∀ s : ℝ, 0 < s →
      laplaceL (F.memoryKernel x ∗ ℓ) s = laplaceL (volume.restrict (Ici (0 : ℝ))) s := by
    intro s hs
    have hsym : 0 < F.symbol x s := F.symbol_pos hnd hx hs
    rw [laplaceL_conv, F.laplaceL_memoryKernel hx hs, hℓ s hs, laplaceL_volume_Ici hs,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  have hfin : laplaceL (F.memoryKernel x ∗ ℓ) 1 ≠ ⊤ := by
    rw [hkey 1 zero_lt_one, laplaceL_volume_Ici zero_lt_one]
    exact ENNReal.ofReal_ne_top
  have heq : F.memoryKernel x ∗ ℓ = volume.restrict (Ici (0 : ℝ)) := by
    refine laplaceL_injective_of_ne_top (F.isCausal_memoryKernel.conv hcaus) ?_ hfin ?_
    · rw [IsCausal, Measure.restrict_apply measurableSet_Iio, Iio_inter_Ici, Ico_self,
        measure_empty]
    · intro s hs
      exact hkey s (lt_of_lt_of_le zero_lt_one hs)
  rw [heq, Measure.restrict_restrict measurableSet_Ici, inter_self]

/-- **`thm:sonine-conservation`, unrestricted.** `κ^{(x)} ∗ ℓ^{(x)} = \mathrm{Leb}_{[0,∞)}` as
measures on all of `ℝ`, which is the identity the article states (Theorem 9.5): both sides vanish
on `Iio 0` — the left because a convolution of causal measures is causal, the right by
construction — so restricting to `[0,∞)`, where `sonine_conservation` already identifies them,
loses no information. -/
theorem sonine_conservation' (hnd : F.Nondegenerate) (hx : 0 < x) (ℓ : Measure ℝ) [SFinite ℓ]
    (hcaus : IsCausal ℓ)
    (hℓ : ∀ s : ℝ, 0 < s → laplaceL ℓ s = ENNReal.ofReal (F.symbol x s)⁻¹) :
    F.memoryKernel x ∗ ℓ = volume.restrict (Ici (0 : ℝ)) := by
  have hcausconv : IsCausal (F.memoryKernel x ∗ ℓ) := F.isCausal_memoryKernel.conv hcaus
  have hrestr := F.sonine_conservation hnd hx ℓ hcaus hℓ
  have hleft : (F.memoryKernel x ∗ ℓ).restrict (Ici 0) = F.memoryKernel x ∗ ℓ := by
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff, show {a : ℝ | a ∉ Ici (0 : ℝ)} = Iio 0 from compl_Ici]
    exact hcausconv
  rw [← hleft, hrestr]

end SelfDecomposableExponent

end Hemigroup
