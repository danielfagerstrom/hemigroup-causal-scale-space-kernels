/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.L1Continuity
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# The constructed family is a `CascadeFamily`

The specification check M6a exists for: `Family.lean` says what the axioms of
`def:cascade-family` are, and this file exhibits the kernels of `Construction.lean` as an
instance. A mis-stated axiom is otherwise silent — it makes the main theorem vacuous or false
rather than unprovable — and the only thing that catches it is a model known independently to
satisfy the mathematics.

## What the check already caught

Two things, neither of which would have surfaced from reading the structure:

* the family is indexed from `x = 0`, and the Lean construction started at `x > 0` — fixed at
  the source by the `k(0) = 0` normalisation (`increment_zero_left`), not by narrowing the
  specification;
* the axioms have to carry the index restriction `0 ≤ x ≤ y` explicitly, because `Φ` is a total
  function of `(x,y)` and is junk off the range. Without it (A5) would be false for the
  constructed family, since `μ_{x,y}` is the zero measure there.

## (A7)

The one clause needing more than transport. `tendsto_mconvL1_kernel` extends the compactly
supported case to all of `L¹` by density, and `continuousOn_mconvL1_kernel` converts the
sequential statement into `ContinuousOn`, which is legitimate because `ℝ × ℝ` is first countable.
-/

namespace Hemigroup

open MeasureTheory Set Filter
open scoped ENNReal

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent)

/-- **(A7) in `L¹`, for every `f`.** The compactly supported case plus density.

`Integrable.exists_hasCompactSupport_lintegral_sub_le` supplies the approximant — note it is
the *compactly supported* density result, not `Lp.boundedContinuousFunction_dense`, because the
tail estimate needs the support. The approximation error does not grow under the operators,
since each is a contraction (`norm_mconvL1_le`) uniformly in the parameter. -/
theorem tendsto_mconvL1_kernel {u v : ℕ → ℝ} {α β B : ℝ}
    (hB : 0 < B) (hu0 : ∀ n, 0 ≤ u n) (huv : ∀ n, u n ≤ v n) (hvB : ∀ n, v n ≤ B)
    (hα : Tendsto u atTop (nhds α)) (hβ : Tendsto v atTop (nhds β))
    (hα0 : 0 ≤ α) (hαβ : α ≤ β) (hβB : β ≤ B) (g : X) :
    Tendsto (fun n => mconvL1 (F.kernel (u n) (v n)) g) atTop
      (nhds (mconvL1 (F.kernel α β) g)) := by
  haveI hprobn : ∀ n, IsProbabilityMeasure (F.kernel (u n) (v n)) := fun n =>
    isProbabilityMeasure_kernel (hu0 n) (huv n)
  haveI hprob : IsProbabilityMeasure (F.kernel α β) := isProbabilityMeasure_kernel hα0 hαβ
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Approximate `g` by a compactly supported continuous `f`, to within `ε/4`.
  obtain ⟨f, hcs, hclose, hcont, hfint⟩ :=
    Integrable.exists_hasCompactSupport_lintegral_sub_le (L1.integrable_coeFn g)
      (ε := ENNReal.ofReal (ε / 4)) (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith)
  set fL : X := hfint.toL1 f with hfL
  have hgf : ‖g - fL‖ ≤ ε / 4 := by
    rw [norm_sub_eq_lintegral]
    have hae : ∫⁻ t, ‖(g : ℝ → ℝ) t - (fL : ℝ → ℝ) t‖ₑ = ∫⁻ t, ‖(g : ℝ → ℝ) t - f t‖ₑ := by
      refine lintegral_congr_ae ?_
      filter_upwards [Integrable.coeFn_toL1 hfint] with t ht
      rw [ht]
    calc (∫⁻ t, ‖(g : ℝ → ℝ) t - (fL : ℝ → ℝ) t‖ₑ).toReal
        = (∫⁻ t, ‖(g : ℝ → ℝ) t - f t‖ₑ).toReal := by rw [hae]
      _ ≤ (ENNReal.ofReal (ε / 4)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hclose
      _ = ε / 4 := ENNReal.toReal_ofReal (by linarith)
  -- The middle term converges, by the compactly supported case.
  have hmid : Tendsto (fun n => ‖mconvL1 (F.kernel (u n) (v n)) fL
      - mconvL1 (F.kernel α β) fL‖) atTop (nhds 0) := by
    have hcore := tendsto_lintegral_enorm_mconv_kernel_sub F hB hu0 huv hvB hα hβ hα0 hαβ hβB
      hcont hcs
    have hcongr : ∀ n, ‖mconvL1 (F.kernel (u n) (v n)) fL - mconvL1 (F.kernel α β) fL‖
        = (∫⁻ t, ‖mconv (F.kernel (u n) (v n)) f t - mconv (F.kernel α β) f t‖ₑ).toReal := by
      intro n
      rw [norm_sub_eq_lintegral]
      congr 1
      refine lintegral_congr_ae ?_
      filter_upwards [(coeFn_mconvL1 (F.kernel (u n) (v n)) fL).trans
          (mconv_congr_ae _ (Integrable.coeFn_toL1 hfint)),
        (coeFn_mconvL1 (F.kernel α β) fL).trans
          (mconv_congr_ae _ (Integrable.coeFn_toL1 hfint))] with t h1 h2
      rw [h1, h2]
    simp only [hcongr]
    have hconv := (ENNReal.tendsto_toReal (by norm_num)).comp hcore
    simp only [Function.comp_def, ENNReal.toReal_zero] at hconv
    exact hconv
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hmid (ε / 2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have hstep := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at hstep
  -- Split through the approximant.
  have h1 : ‖mconvL1 (F.kernel (u n) (v n)) g - mconvL1 (F.kernel (u n) (v n)) fL‖ ≤ ε / 4 := by
    rw [← ContinuousLinearMap.map_sub]
    exact (norm_mconvL1_le _ _).trans hgf
  have h2 : ‖mconvL1 (F.kernel α β) fL - mconvL1 (F.kernel α β) g‖ ≤ ε / 4 := by
    rw [← ContinuousLinearMap.map_sub, ← norm_neg, ← ContinuousLinearMap.map_neg, neg_sub]
    exact (norm_mconvL1_le _ _).trans hgf
  have ht1 := dist_triangle (mconvL1 (F.kernel (u n) (v n)) g)
    (mconvL1 (F.kernel (u n) (v n)) fL) (mconvL1 (F.kernel α β) g)
  have ht2 := dist_triangle (mconvL1 (F.kernel (u n) (v n)) fL)
    (mconvL1 (F.kernel α β) fL) (mconvL1 (F.kernel α β) g)
  simp only [dist_eq_norm] at ht1 ht2 ⊢
  linarith

/-- **(A7)**, in the form `def:cascade-family` states it. The sequential statement transfers
because `𝓝[s] p` on `ℝ × ℝ` is countably generated. -/
theorem continuousOn_mconvL1_kernel (g : X) :
    ContinuousOn (fun p : ℝ × ℝ => mconvL1 (F.kernel p.1 p.2) g)
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2} := by
  rintro p ⟨hp0, hp12⟩
  rw [ContinuousWithinAt, Filter.tendsto_iff_seq_tendsto]
  intro q hq
  -- A tail of `q` lies in the index set; shift to it.
  have hqn : Tendsto q atTop (nhds p) := hq.mono_right nhdsWithin_le_nhds
  obtain ⟨N₀, hN₀⟩ : ∃ N₀, ∀ n ≥ N₀, 0 ≤ (q n).1 ∧ (q n).1 ≤ (q n).2 :=
    Filter.eventually_atTop.mp (hq (self_mem_nhdsWithin))
  set q' : ℕ → ℝ × ℝ := fun n => q (n + N₀) with hq'
  have hmem : ∀ n, 0 ≤ (q' n).1 ∧ (q' n).1 ≤ (q' n).2 := fun n => hN₀ _ (Nat.le_add_left _ _)
  have hq'n : Tendsto q' atTop (nhds p) := hqn.comp (tendsto_add_atTop_nat N₀)
  have hu : Tendsto (fun n => (q' n).1) atTop (nhds p.1) := (continuous_fst.tendsto p).comp hq'n
  have hv : Tendsto (fun n => (q' n).2) atTop (nhds p.2) := (continuous_snd.tendsto p).comp hq'n
  obtain ⟨B₀, hB₀⟩ := hv.bddAbove_range
  set B : ℝ := max (max B₀ p.2) 1 with hBdef
  have hB : 0 < B := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hvB : ∀ n, (q' n).2 ≤ B := fun n =>
    le_trans (hB₀ ⟨n, rfl⟩) ((le_max_left _ _).trans (le_max_left _ _))
  have hβB : p.2 ≤ B := (le_max_right _ _).trans (le_max_left _ _)
  have hmain := tendsto_mconvL1_kernel F hB (fun n => (hmem n).1) (fun n => (hmem n).2) hvB
    hu hv hp0 hp12 hβB g
  -- Undo the shift.
  rw [← tendsto_add_atTop_iff_nat N₀]
  exact hmain

/-! ## The instance -/

/-- **The constructed family is a `CascadeFamily`.**

Every clause of `def:cascade-family`, for the kernels built from a nondegenerate `F`. This is
`thm:main-characterization` (⇐) at the level the theorem states it — not "the kernels satisfy
properties we named (A1)–(A8)", but "the kernels are a causal cascade measurement family". -/
noncomputable def cascadeFamily (hF : ∃ s₀, 0 < s₀ ∧ F.exponent s₀ ≠ 0) : CascadeFamily where
  Φ x y := mconvL1 (F.kernel x y)
  S σ x := σ * x
  translation x y _ _ a f := mconvL1_transL1 a f
  causal x y hx hxy t₀ f hf :=
    vanishesBefore_mconvL1 (isCausal_kernel hx hxy) t₀ f hf
  positive x y _ _ f hf := isNonneg_mconvL1 f hf
  unit_area x y hx hxy f _ := by
    haveI := isProbabilityMeasure_kernel (F := F) hx hxy
    exact integral_mconvL1 f
  refl x hx := by rw [mconvL1_congr (kernel_self hx)]; exact mconvL1_dirac_zero
  cascade x y z hx hxy hyz := by
    haveI : IsFiniteMeasure ((F.kernel x y) ∗ (F.kernel y z)) := by
      rw [kernel_conv hx hxy hyz]; infer_instance
    rw [mconvL1_comp, mconvL1_congr (kernel_conv hx hxy hyz)]
  continuous g := continuousOn_mconvL1_kernel F g
  S_mapsTo σ hσ x hx := by simpa using mul_nonneg hσ.le hx
  S_strictMonoOn σ hσ x _ y _ hxy := by
    simpa using mul_lt_mul_of_pos_left hxy hσ
  S_surjOn σ hσ x hx := ⟨σ⁻¹ * x, by
    simp only [mem_Ici] at hx ⊢
    exact mul_nonneg (inv_nonneg.mpr hσ.le) hx, by
    field_simp⟩
  scale σ hσ x y hx hxy := by
    haveI : IsFiniteMeasure ((F.kernel x y).map (fun t => σ * t)) := by
      rw [← kernel_map_const_mul hσ hx hxy]; infer_instance
    rw [dilL1_comp_mconvL1 hσ (F.kernel x y),
      mconvL1_congr (kernel_map_const_mul hσ hx hxy).symm]
  nondegenerate x y hx hxy hid := by
    haveI := isProbabilityMeasure_kernel (F := F) hx hxy.le
    -- If the operator is the identity, the kernel is `δ₀`, so its exponent vanishes.
    have hδ : F.kernel x y = Measure.dirac 0 := by
      refine eq_dirac_of_mconv_box (isCausal_kernel hx hxy.le) ?_
      have h := congrArg (fun T : X →L[ℝ] X => T (integrable_box.toL1 box)) hid
      simp only [ContinuousLinearMap.id_apply] at h
      calc mconv (F.kernel x y) box
          =ᵐ[volume] mconv (F.kernel x y) ((integrable_box.toL1 box : X) : ℝ → ℝ) :=
            mconv_congr_ae _ (Integrable.coeFn_toL1 integrable_box).symm
        _ =ᵐ[volume] ((integrable_box.toL1 box : X) : ℝ → ℝ) := by
            refine ((coeFn_mconvL1 _ _).symm.trans ?_)
            rw [h]
        _ =ᵐ[volume] box := Integrable.coeFn_toL1 integrable_box
    -- But the transform of `δ₀` is `1`, so the increment vanishes, contradicting (ND).
    obtain ⟨s₀, hs₀, hs₀ne⟩ := hF
    have hincr : F.increment x y s₀ = 0 := by
      have h1 := laplace_kernel (F := F) hx hxy.le hs₀.le
      rw [hδ, laplace_dirac_zero] at h1
      have h3 : Real.exp (-(F.increment x y s₀).toReal) = Real.exp 0 := by
        rw [Real.exp_zero]; exact h1.symm
      have h2 : (F.increment x y s₀).toReal = 0 := by
        have := Real.exp_eq_exp.mp h3; linarith
      exact ((ENNReal.toReal_eq_zero_iff _).mp h2).resolve_right
        (increment_ne_top hx hxy.le hs₀.le)
    -- `g_{x,y}` vanishing at one point makes it vanish identically, hence `F(y·) = F(x·)`.
    have hzero : ∀ s, 0 ≤ s → F.increment x y s = 0 :=
      levyExponentD_eq_zero_of_eq_zero (mul_nonneg F.b₀_nonneg (by linarith))
        (aemeasurable_incrementDensity hx (hx.trans hxy.le)) hs₀ hincr
    have hfix : ∀ s, 0 ≤ s → F.exponent (x * s) = F.exponent (y * s) := fun s hs => by
      have h := exponent_add_increment (F := F) hx hxy.le hs
      rw [hzero s hs, add_zero] at h
      exact h
    have hy0 : 0 < y := lt_of_le_of_lt hx hxy
    rcases hx.eq_or_lt with hx0 | hx0
    · -- `x = 0`: then `F` vanishes at `y · s` for every `s`, so everywhere.
      have hs : F.exponent (y * (s₀ / y)) = 0 := by
        have h := hfix (s₀ / y) (by positivity)
        rw [← hx0, zero_mul] at h
        rw [← h]
        simp [exponent, levyExponentD, levyJump]
      rw [mul_div_cancel₀ _ hy0.ne'] at hs
      exact hs₀ne hs
    · -- `x > 0`: strict monotonicity forbids `F(x) = F(y)`.
      exact absurd (by simpa using hfix 1 zero_le_one)
        (exponent_strictMono F ⟨s₀, hs₀, hs₀ne⟩ hx0 hxy).ne

end SelfDecomposableExponent

end Hemigroup
