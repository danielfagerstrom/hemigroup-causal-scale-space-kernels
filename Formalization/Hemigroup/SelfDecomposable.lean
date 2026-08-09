/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.Levy
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Self-decomposable exponents and their dilation increments

M1b of the formalisation ladder. Blueprint: `lem:selfdecomposable-exponents` (Lemma 7.1),
`blueprint/src/parts/07-characterization.tex`.

## What is proved here, and what is not

Lemma 7.1 states three equivalent conditions on `F ∈ BF₀`:

1. every dilation increment `F(b ·) - F(a ·)` is again in `BF₀`;
2. `s ↦ s F'(s)` is a Bernstein function;
3. `F` has the representation `F s = b₀ s + ∫ (1 - e^{-st}) k t / t dt` with `k` nonincreasing.

This file proves **(3) ⇒ (1)**, in representation form: `levyExponentD_increment`. That is the
direction the main theorem's constructive half consumes — `thm:main-characterization` (⇐) needs
exactly "each `g_{a,b} := F(b ·) - F(a ·)` lies in `BF₀`", and nothing else from Lemma 7.1.

(1) ⇒ (2) and (2) ⇔ (3) are *not* proved here. They are the direction the analysis half of the
main theorem uses, and both rest on cited interfaces: (1) ⇒ (2) on closure of `BF` under
pointwise limits (ledger A4) and (2) ⇔ (3) on uniqueness of the Lévy–Khintchine triple
(ledger A3). Formalising them means formalising those, which the trust boundary deliberately
declines to do.

## Why (3) ⇒ (1) is elementary here

In the blueprint the increment is shown Bernstein through condition (2) and closure properties.
From the representation it is a change of variables and a sign: `u = c t` carries `dt / t` to
`du / u` — the measure `dt/t` is the Haar measure of the multiplicative group, so dilation acts
on the *density* alone — and the increment's density

  `u ↦ k (u / b) - k (u / a)`

is nonnegative precisely because `k` is nonincreasing and `u / b ≤ u / a`. No closure theorem,
no derivative, no complete monotonicity.

Note what the increment is *not*: `u ↦ k (u/b) - k (u/a)` need not be nonincreasing, so the
increment is a Lévy exponent but generally not a self-decomposable one. Condition (1) asks only
for the former, and that is what is proved.
-/

namespace Hemigroup

open MeasureTheory Set
open scoped ENNReal

variable {k : ℝ → ℝ} {b₀ s a b c : ℝ}

/-! ## Lévy exponents given by a density against `dt / t` -/

/-- The jump part of a Lévy exponent whose Lévy measure has density `k t / t` against Lebesgue
measure on `(0,∞)`: `s ↦ ∫₀^∞ (1 - e^{-st}) k t / t dt`. -/
noncomputable def levyJump (k : ℝ → ℝ) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.exp (-(s * t))) * k t / t)

/-- The Lévy exponent of the blueprint's (7.1): drift `b₀` plus the jump part of density
`k t / t`. This is `levyExponent` specialised to an absolutely continuous Lévy measure; the two
agree by `levyExponentD_eq_levyExponent`. -/
noncomputable def levyExponentD (b₀ : ℝ) (k : ℝ → ℝ) (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (b₀ * s) + levyJump k s

/-- The Lévy measure of (7.1): density `k t / t` against Lebesgue measure on `(0,∞)`. -/
noncomputable def levyMeasureOfDensity (k : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity fun t => ENNReal.ofReal (k t / t)

/-- A Lévy measure given by a density on `(0,∞)` is causal, so `Levy.lean`'s results —
in particular the vanishing lemma — apply to it. -/
lemma isCausal_levyMeasureOfDensity (k : ℝ → ℝ) : IsCausal (levyMeasureOfDensity k) := by
  refine withDensity_absolutelyContinuous _ _ ?_
  rw [Measure.restrict_apply measurableSet_Iio, inter_comm, Ioi_inter_Iio, Ioo_self,
    measure_empty]

/-! ## Measurability

`k` is only assumed nonincreasing on `(0,∞)`, so it is not measurable as a function on `ℝ`.
It is a.e. measurable for the restricted measure, which is all any integral here needs, and
that is what `aemeasurable_restrict_of_antitoneOn` supplies. -/

/-- Precomposition with a dilation preserves antitonicity on the half-line. -/
lemma antitoneOn_comp_div (hk : AntitoneOn k (Ioi (0 : ℝ))) (hc : 0 < c) :
    AntitoneOn (fun u => k (u / c)) (Ioi (0 : ℝ)) := fun _ hx _ hy hxy =>
  hk (mem_Ioi.mpr (div_pos (mem_Ioi.mp hx) hc)) (mem_Ioi.mpr (div_pos (mem_Ioi.mp hy) hc))
    (by gcongr)

/-- The integrand of `levyJump` is a.e. measurable for the restricted measure. -/
lemma aemeasurable_levyJump_integrand (hk : AntitoneOn k (Ioi (0 : ℝ))) (s : ℝ) :
    AEMeasurable (fun t : ℝ => ENNReal.ofReal ((1 - Real.exp (-(s * t))) * k t / t))
      (volume.restrict (Ioi (0 : ℝ))) := by
  have hk' : AEMeasurable k (volume.restrict (Ioi (0 : ℝ))) :=
    aemeasurable_restrict_of_antitoneOn measurableSet_Ioi hk
  have hw : Measurable fun t : ℝ => 1 - Real.exp (-(s * t)) := by fun_prop
  exact (((hw.aemeasurable).mul hk').div aemeasurable_id).ennreal_ofReal

/-! ## Dilation acts on the density alone -/

/-- Lebesgue measure on the half-line, pushed forward by `t ↦ c t`, is `c⁻¹` times itself.
The half-line is invariant because `c > 0`. -/
lemma map_mul_restrict_Ioi (hc : 0 < c) :
    Measure.map (fun t : ℝ => c * t) (volume.restrict (Ioi (0 : ℝ)))
      = ENNReal.ofReal c⁻¹ • volume.restrict (Ioi (0 : ℝ)) := by
  have hpre : (fun t : ℝ => c * t) ⁻¹' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
    ext t
    simp only [mem_preimage, mem_Ioi, mul_pos_iff_of_pos_left hc]
  have h1 : Measure.map (fun t : ℝ => c * t) (volume.restrict (Ioi (0 : ℝ)))
      = (Measure.map (fun t : ℝ => c * t) volume).restrict (Ioi (0 : ℝ)) := by
    rw [Measure.restrict_map (measurable_const_mul c) measurableSet_Ioi, hpre]
  rw [h1, Real.map_volume_mul_left hc.ne', Measure.restrict_smul,
    abs_of_pos (inv_pos.mpr hc)]

/-- **Dilation invariance of `dt / t`.** Dilating the argument of a Lévy exponent of the
form (7.1) dilates the density and nothing else:
`levyJump k (c s) = levyJump (k (· / c)) s`.

This is the computational heart of the file. The Jacobian `c⁻¹` of `u = c t` cancels exactly
against the `c` produced by `t = u / c` in the denominator — which is the statement that
`dt / t` is invariant under the multiplicative group. -/
lemma levyJump_comp_mul (k : ℝ → ℝ) (hc : 0 < c) (s : ℝ) :
    levyJump k (c * s) = levyJump (fun u => k (u / c)) s := by
  have hc0 : c ≠ 0 := hc.ne'
  have hemb : MeasurableEmbedding (fun t : ℝ => c * t) :=
    (Homeomorph.mulLeft₀ c hc0).toMeasurableEquiv.measurableEmbedding
  set G : ℝ → ℝ≥0∞ :=
    fun u => ENNReal.ofReal ((1 - Real.exp (-(s * u))) * k (u / c) / (u / c)) with hG
  -- Push forward along `t ↦ c t`. No measurability of `G` is needed: the map is an embedding.
  have hpush : ∫⁻ u, G u ∂(Measure.map (fun t : ℝ => c * t) (volume.restrict (Ioi (0 : ℝ))))
      = ∫⁻ t in Ioi (0 : ℝ), G (c * t) := hemb.lintegral_map G
  rw [map_mul_restrict_Ioi hc, lintegral_smul_measure] at hpush
  -- The right-hand side of `hpush` is `levyJump k (c * s)`.
  have hrhs : ∫⁻ t in Ioi (0 : ℝ), G (c * t) = levyJump k (c * s) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [hG]
    rw [show c * t / c = t by field_simp, show s * (c * t) = c * s * t by ring]
  -- The left-hand side is `ofReal c⁻¹ * ofReal c * levyJump (k (· / c)) s`.
  have hlhs : ∫⁻ u in Ioi (0 : ℝ), G u
      = ENNReal.ofReal c * levyJump (fun u => k (u / c)) s := by
    rw [levyJump, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    simp only [hG]
    rw [← ENNReal.ofReal_mul hc.le]
    congr 1
    field_simp
  rw [hlhs, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (inv_pos.mpr hc).le,
    inv_mul_cancel₀ hc0, ENNReal.ofReal_one, one_mul, hrhs] at hpush
  exact hpush.symm

/-- The same statement for the full exponent: dilating the argument rescales the drift and
dilates the density. -/
lemma levyExponentD_comp_mul (b₀ : ℝ) (k : ℝ → ℝ) (hc : 0 < c) (s : ℝ) :
    levyExponentD b₀ k (c * s) = levyExponentD (b₀ * c) (fun u => k (u / c)) s := by
  rw [levyExponentD, levyExponentD, levyJump_comp_mul k hc s]
  congr 2
  ring

/-! ## The increment of a self-decomposable exponent -/

/-- The increment density is nonnegative: this is the *only* place monotonicity of `k` is used,
and it is what makes the increment a Lévy exponent rather than a mere difference. -/
lemma increment_density_nonneg (hk : AntitoneOn k (Ioi (0 : ℝ))) (ha : 0 < a) (hab : a ≤ b)
    {u : ℝ} (hu : u ∈ Ioi (0 : ℝ)) : 0 ≤ k (u / b) - k (u / a) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hu' : 0 < u := hu
  exact sub_nonneg.mpr <|
    hk (mem_Ioi.mpr (div_pos hu' hb)) (mem_Ioi.mpr (div_pos hu' ha)) (by gcongr)

/-- The jump parts add: the jump part at `a` plus the jump part of the increment density is the
jump part at `b`. -/
lemma levyJump_add_increment (hk : AntitoneOn k (Ioi (0 : ℝ)))
    (hk₀ : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ k t) (ha : 0 < a) (hab : a ≤ b) (hs : 0 ≤ s) :
    levyJump (fun u => k (u / a)) s + levyJump (fun u => k (u / b) - k (u / a)) s
      = levyJump (fun u => k (u / b)) s := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  rw [levyJump, levyJump, levyJump,
    ← lintegral_add_left' (aemeasurable_levyJump_integrand (antitoneOn_comp_div hk ha) s)]
  refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu' : 0 < u := hu
  -- `1 - e^{-su} ≥ 0` because `s ≥ 0` and `u > 0`.
  have hw : 0 ≤ 1 - Real.exp (-(s * u)) := by
    have : Real.exp (-(s * u)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    linarith
  have h1 : 0 ≤ (1 - Real.exp (-(s * u))) * k (u / a) / u :=
    div_nonneg (mul_nonneg hw (hk₀ _ (mem_Ioi.mpr (div_pos hu' ha)))) hu'.le
  have h2 : 0 ≤ (1 - Real.exp (-(s * u))) * (k (u / b) - k (u / a)) / u :=
    div_nonneg (mul_nonneg hw (increment_density_nonneg hk ha hab hu)) hu'.le
  rw [← ENNReal.ofReal_add h1 h2]
  congr 1
  ring

/-- **(3) ⇒ (1) of Lemma 7.1**, in representation form: for `0 < a ≤ b` the dilation increment
of a Lévy exponent with nonincreasing `k` is *itself* a Lévy exponent, with drift
`b₀ (b - a) ≥ 0` and Lévy density `(k (u/b) - k (u/a)) / u ≥ 0`.

Stated additively, `F(a s) + G(s) = F(b s)`, rather than as a truncated `ℝ≥0∞` subtraction: the
two are equivalent where `F(a s) < ∞`, and the additive form is what
`thm:main-characterization` (⇐) actually uses, since it needs exponents to *add* along a
cascade. -/
theorem levyExponentD_increment (hb₀ : 0 ≤ b₀) (hk : AntitoneOn k (Ioi (0 : ℝ)))
    (hk₀ : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ k t) (ha : 0 < a) (hab : a ≤ b) (hs : 0 ≤ s) :
    levyExponentD b₀ k (a * s)
        + levyExponentD (b₀ * (b - a)) (fun u => k (u / b) - k (u / a)) s
      = levyExponentD b₀ k (b * s) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  rw [levyExponentD_comp_mul b₀ k ha s, levyExponentD_comp_mul b₀ k hb s]
  rw [levyExponentD, levyExponentD, levyExponentD, add_add_add_comm]
  rw [levyJump_add_increment hk hk₀ ha hab hs]
  congr 1
  rw [← ENNReal.ofReal_add (mul_nonneg (mul_nonneg hb₀ ha.le) hs)
    (mul_nonneg (mul_nonneg hb₀ (by linarith)) hs)]
  congr 1
  ring

/-! ## The bridge to `Levy.lean`

`levyExponentD` is `levyExponent` for an absolutely continuous Lévy measure. Recording that
identification is what lets M1a's vanishing lemma — proved for a general causal Lévy measure —
apply to the exponents of (7.1), which is how `thm:main-characterization` (⇐) discharges (ND).
-/

/-- The two exponents agree: `levyExponentD b₀ k` is `levyExponent b₀` of the Lévy measure with
density `k t / t` on `(0,∞)`.

No sign hypothesis on `k` is needed. Where `k` is negative both sides are zero, because
`1 - e^{-st} ≥ 0` for `s ≥ 0` and `ENNReal.ofReal` truncates. -/
lemma levyExponentD_eq_levyExponent (b₀ : ℝ) (hk : AntitoneOn k (Ioi (0 : ℝ))) (hs : 0 ≤ s) :
    levyExponentD b₀ k s = levyExponent b₀ (levyMeasureOfDensity k) s := by
  have hf : AEMeasurable (fun t : ℝ => ENNReal.ofReal (k t / t)) (volume.restrict (Ioi (0 : ℝ))) :=
    ((aemeasurable_restrict_of_antitoneOn measurableSet_Ioi hk).div
      aemeasurable_id).ennreal_ofReal
  have hg : AEMeasurable (fun t : ℝ => ENNReal.ofReal (1 - Real.exp (-(s * t))))
      (volume.restrict (Ioi (0 : ℝ))) := by fun_prop
  rw [levyExponent, levyExponentD, levyMeasureOfDensity,
    lintegral_withDensity_eq_lintegral_mul₀ hf hg, levyJump]
  congr 1
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht' : 0 < t := ht
  have hw : 0 ≤ 1 - Real.exp (-(s * t)) := by
    have : Real.exp (-(s * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    linarith
  rw [Pi.mul_apply, ← ENNReal.ofReal_mul' hw]
  congr 1
  ring

/-- **The vanishing lemma for exponents of the form (7.1)**: `lem:vanishing` transported along
the bridge. A Lévy exponent of the self-decomposable form that vanishes at one positive point
vanishes identically — which is how the main theorem's constructive direction verifies (ND),
and equivalently says that a nonzero `F` is strictly increasing. -/
theorem levyExponentD_eq_zero_of_eq_zero (hb₀ : 0 ≤ b₀) (hk : AntitoneOn k (Ioi (0 : ℝ)))
    {s₀ : ℝ} (hs₀ : 0 < s₀) (h : levyExponentD b₀ k s₀ = 0) :
    ∀ s, 0 ≤ s → levyExponentD b₀ k s = 0 := by
  intro s hs
  rw [levyExponentD_eq_levyExponent b₀ hk hs]
  refine levyExponent_eq_zero_of_eq_zero hb₀ (isCausal_levyMeasureOfDensity k) hs₀ ?_ s hs
  rw [← levyExponentD_eq_levyExponent b₀ hk hs₀.le]
  exact h

end Hemigroup
