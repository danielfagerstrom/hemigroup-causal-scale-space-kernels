/-
Copyright (c) 2026 Daniel Fagerstrom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerstrom
-/
import Hemigroup.InversionSymbol

/-!
# Vertical decay of Gamma, and the profile's vertical integrability

Blueprint: `lem:mellin-vertical` (11.13), the clause ledger **A12**'s retirement turns on --
`Complex.VerticalIntegrable (mellin H) c` is *verbatim* the hypothesis Mathlib's
`mellinInv_mellin_eq` asks for.

## The obstruction that was recorded as upstream, and why it was not

Three earlier assessments of A12 are recorded in `blueprint/AXIOMS.md`. The last of them concluded
that the entry is blocked on a **missing Mathlib estimate**: `lem:mellin-data` bounds
`|H~(c+i tau)|` by `E[T_1^{-c}] |Gamma(c+i tau)|`, and integrating that in `tau` needs the decay
of `|Gamma(c+i tau)|` -- for which Mathlib has nothing, its `Stirling.lean` being Stirling's
formula for `n!` alone.

That reading was right that Mathlib has no such estimate and wrong that one was needed. The
classical fact is the asymptotic `|Gamma(c+i tau)| ~ sqrt(2 pi) |tau|^(c-1/2) e^(-pi|tau|/2)`,
which does require Stirling in the complex plane. **Integrability needs far less**, and the far
less is elementary:

* `|Gamma(sigma + i tau)| <= Gamma(sigma)` for `sigma > 0`, because the imaginary part only
  rotates the integrand of Euler's integral;
* `Gamma(z+2) = (z+1) z Gamma(z)`, and both `|z|` and `|z+1|` are at least `|tau|` since both have
  imaginary part `tau`; hence `|Gamma(c+i tau)| tau^2 <= Gamma(c+2)`.

Adding the two gives `|Gamma(c+i tau)| (1 + tau^2) <= Gamma(c) + Gamma(c+2)`, and `(1+tau^2)^(-1)`
is integrable. Quadratic decay where the truth is exponential -- and quadratic is enough.

**The lesson, and it is the fourth time this ledger entry has taught one.** The first reading
compared Mathlib to the *cited theorem*; the second to the article's *use* of it; the third
identified a missing lemma by name. All three were reasoning about what the classical proof needs.
What actually settles it is what the *statement* needs, which was two orders of magnitude less. A
survey answers "is this theory present?"; only attempting the proof answers "is this theorem
reachable?".
-/

namespace Hemigroup

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- `|Γ(σ+iτ)| ≤ Γ(σ)`: the imaginary part only rotates the integrand. -/
theorem norm_Gamma_le_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz, Complex.GammaIntegral, Real.Gamma_eq_integral hz]
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx' : (0 : ℝ) < x := mem_Ioi.mp hx
  rw [norm_mul, Complex.norm_real, Complex.norm_cpow_eq_rpow_re_of_pos hx']
  simp [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- **`|Γ(c+iτ)| · τ² ≤ Γ(c+2)`.**

The functional equation twice: `Γ(z+2) = (z+1)·z·Γ(z)`, and both `|z|` and `|z+1|` are at least
`|τ|` because both have imaginary part `τ`. -/
theorem norm_Gamma_mul_sq_le {c : ℝ} (hc : 0 < c) (τ : ℝ) :
    ‖Complex.Gamma (c + τ * Complex.I)‖ * τ ^ 2 ≤ Real.Gamma (c + 2) := by
  set z : ℂ := (c : ℂ) + τ * Complex.I with hzdef
  have hre : z.re = c := by simp [hzdef]
  have him : z.im = τ := by simp [hzdef]
  have hz0 : z ≠ 0 := fun h => by rw [h] at hre; simp at hre; linarith
  have hz1 : z + 1 ≠ 0 := fun h => by
    have : (z + 1).re = 0 := by rw [h]; simp
    rw [Complex.add_re, hre] at this; simp at this; linarith
  -- `Γ(z+2) = (z+1) z Γ(z)`
  have hfe : Complex.Gamma (z + 2) = (z + 1) * (z * Complex.Gamma z) := by
    rw [show z + 2 = (z + 1) + 1 from by ring, Complex.Gamma_add_one _ hz1,
      Complex.Gamma_add_one _ hz0]
  have hnorm : ‖Complex.Gamma (z + 2)‖ = ‖z + 1‖ * (‖z‖ * ‖Complex.Gamma z‖) := by
    rw [hfe, norm_mul, norm_mul]
  have hzabs : |τ| ≤ ‖z‖ := by rw [← him]; exact Complex.abs_im_le_norm z
  have hz1abs : |τ| ≤ ‖z + 1‖ := by
    have : (z + 1).im = τ := by rw [Complex.add_im, him]; simp
    rw [← this]; exact Complex.abs_im_le_norm (z + 1)
  have hre2 : (z + 2).re = c + 2 := by rw [Complex.add_re, hre]; simp
  calc ‖Complex.Gamma z‖ * τ ^ 2 = |τ| * (|τ| * ‖Complex.Gamma z‖) := by
        rw [← sq_abs τ]; ring
    _ ≤ ‖z + 1‖ * (‖z‖ * ‖Complex.Gamma z‖) := by gcongr
    _ = ‖Complex.Gamma (z + 2)‖ := hnorm.symm
    _ ≤ Real.Gamma (z + 2).re := norm_Gamma_le_of_re_pos (by rw [hre2]; linarith)
    _ = Real.Gamma (c + 2) := by rw [hre2]

/-- **`Γ` decays at least quadratically along every vertical line in the right half-plane.**

Enough for integrability, and elementary: no Stirling estimate is involved. -/
theorem norm_Gamma_vertical_le {c : ℝ} (hc : 0 < c) (τ : ℝ) :
    ‖Complex.Gamma (c + τ * Complex.I)‖
      ≤ (Real.Gamma c + Real.Gamma (c + 2)) * (1 + τ ^ 2)⁻¹ := by
  have hre : ((c : ℂ) + τ * Complex.I).re = c := by simp
  have h1 : ‖Complex.Gamma (c + τ * Complex.I)‖ ≤ Real.Gamma c := by
    have := norm_Gamma_le_of_re_pos (z := (c : ℂ) + τ * Complex.I) (by rw [hre]; exact hc)
    rwa [hre] at this
  have h2 := norm_Gamma_mul_sq_le hc τ
  have hpos : (0 : ℝ) < 1 + τ ^ 2 := by positivity
  rw [le_mul_inv_iff₀ hpos]
  nlinarith [h1, h2]

theorem continuous_Gamma_vertical {c : ℝ} (hc : 0 < c) :
    Continuous fun τ : ℝ => Complex.Gamma (c + τ * Complex.I) := by
  refine continuous_iff_continuousAt.mpr fun τ => ?_
  have hre : ((c : ℂ) + τ * Complex.I).re = c := by simp
  have hcomp := ContinuousAt.comp (g := Complex.Gamma)
    (f := fun t : ℝ => (c : ℂ) + t * Complex.I) (x := τ)
    (analyticAt_Gamma (z := (c : ℂ) + τ * Complex.I) (by rw [hre]; exact hc)).continuousAt
    (by fun_prop)
  simpa [Function.comp_def] using hcomp

/-- **`Γ` is integrable along every vertical line in the right half-plane.** -/
theorem integrable_norm_Gamma_vertical {c : ℝ} (hc : 0 < c) :
    Integrable fun τ : ℝ => ‖Complex.Gamma (c + τ * Complex.I)‖ := by
  refine (integrable_inv_one_add_sq.const_mul (Real.Gamma c + Real.Gamma (c + 2))).mono'
    ((continuous_Gamma_vertical hc).norm.aestronglyMeasurable) ?_
  filter_upwards with τ
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact norm_Gamma_vertical_le hc τ

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent)

/-- **`lem:mellin-vertical`** (11.13): the profile's transform is absolutely integrable on every
vertical line of the strip. -/
theorem verticalIntegrable_mellin_profile (hH : F.StandingHypothesis) {c : ℝ} (hc : 0 < c)
    (hc' : c < F.zStar) :
    Complex.VerticalIntegrable (mellin fun s => (F.profile s : ℂ)) c := by
  have hcont : Continuous fun τ : ℝ => mellin (fun s => (F.profile s : ℂ)) (c + τ * Complex.I) := by
    refine continuous_iff_continuousAt.mpr fun τ => ?_
    have hre : ((c : ℂ) + τ * Complex.I).re = c := by simp
    have hcomp := ContinuousAt.comp (g := mellin fun s => (F.profile s : ℂ))
      (f := fun t : ℝ => (c : ℂ) + t * Complex.I) (x := τ)
      (F.analyticAt_mellin_profile hH (z := (c : ℂ) + τ * Complex.I)
        ⟨by rw [hre]; exact hc, by rw [hre]; exact hc'⟩).continuousAt (by fun_prop)
    simpa [Function.comp_def] using hcomp
  refine ((integrable_norm_Gamma_vertical hc).const_mul (F.negMoment c).toReal).mono'
    hcont.aestronglyMeasurable ?_
  filter_upwards with τ
  exact F.norm_mellin_profile_le hH hc hc' τ

end SelfDecomposableExponent

end Hemigroup
