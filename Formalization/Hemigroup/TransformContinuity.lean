/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the MIT license as described in the file LICENSES/MIT.txt.
Authors: Daniel Fagerström
-/
import Hemigroup.Representation

/-!
# `lem:transform-continuity`: the exponent `g_{x,y}(s) = -log μ̂_{x,y}(s)`

With `lem:convolution-representation` in hand, `μ_{x,y}` exists and is named; this file turns
(A7) — continuity of `(x,y) ↦ Φ_{x,y} f` in `X` — into continuity of the *transform*, which is
what every argument from Chapter 5 onwards actually uses.

## The bridge

The transform is not a continuous functional of the operator on the nose: `e^{-st}` is not
bounded on `ℝ`, so it is not in `X^* = L^∞`. The clamp `g_s(t) = e^{-s\max(t,0)}` is, and it
agrees with `e^{-st}` exactly where causal mass lives. Pairing it against `Φ_{x,y} 1_{(0,1)}`
gives

  `⟨g_s, μ_{x,y} * 1_{(0,1)}⟩ = ⟨g_s, 1_{(0,1)}⟩ · μ̂_{x,y}(s)`,

which is `integral_clampExp_mconv_box`, already proved for the uniqueness clause. The left side
is a bounded functional applied to a continuous function of `(x,y)`; the constant on the right
is at least `e^{-s} > 0`. Dividing by it is the whole proof.

This is the fifth use of the clamp — after `Injectivity.lean`, `WeakConvergence.lean`,
`Nondegeneracy.lean` and the uniqueness clause — and for the same reason each time.

## Continuity in `s`

Separate, and easier: dominated convergence with the constant bound `1`, valid on `[0,∞)`
because the measure is causal. `μ̂(0) = 1` for a probability measure, so `g_{x,y}(\zp) = 0`
is continuity at the endpoint rather than a limit computation.
-/

namespace Hemigroup

open MeasureTheory Set Filter
open scoped ENNReal

/-! ## Multiplication by a bounded function, as a functional on `X` -/

/-- `h ↦ ∫ g h` for measurable `g` with `|g| ≤ 1`: a bounded functional on `X` of norm at most
`1`. The hypotheses are carried as arguments because they are what boundedness needs — for the
clamp they hold only for `s ≥ 0`. -/
noncomputable def mulCLM (g : ℝ → ℝ) (hg : Measurable g) (hgb : ∀ t, |g t| ≤ 1) : X →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun h => ∫ t, g t * (h : ℝ → ℝ) t
      map_add' := fun h₁ h₂ => by
        rw [← integral_add ((L1.integrable_coeFn h₁).bdd_mul (c := 1) hg.aestronglyMeasurable
            (Filter.Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact hgb t))
          ((L1.integrable_coeFn h₂).bdd_mul (c := 1) hg.aestronglyMeasurable
            (Filter.Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact hgb t))]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add h₁ h₂] with t ht
        rw [ht]
        change g t * ((h₁ : ℝ → ℝ) t + (h₂ : ℝ → ℝ) t) = _
        ring
      map_smul' := fun c h => by
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c h] with t ht
        rw [ht]
        change g t * (c • (h : ℝ → ℝ) t) = c * (g t * (h : ℝ → ℝ) t)
        rw [smul_eq_mul]
        ring }
    1 fun h => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      calc ‖∫ t, g t * (h : ℝ → ℝ) t‖ ≤ ∫ t, ‖g t * (h : ℝ → ℝ) t‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ t, ‖(h : ℝ → ℝ) t‖ := by
            refine integral_mono ((L1.integrable_coeFn h).bdd_mul (c := 1)
              hg.aestronglyMeasurable (Filter.Eventually.of_forall fun t => by
                rw [Real.norm_eq_abs]; exact hgb t)).norm
              (L1.integrable_coeFn h).norm fun t => ?_
            rw [norm_mul]
            refine mul_le_of_le_one_left (norm_nonneg _) ?_
            rw [Real.norm_eq_abs]
            exact hgb t
        _ = ‖h‖ := by
            rw [Lp.norm_def, eLpNorm_one_eq_lintegral_enorm,
              ← integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable h)]

@[simp] lemma mulCLM_apply (g : ℝ → ℝ) (hg : Measurable g) (hgb : ∀ t, |g t| ≤ 1) (h : X) :
    mulCLM g hg hgb h = ∫ t, g t * (h : ℝ → ℝ) t := rfl

/-- The clamp pairing `Ψ_s`, for `s ≥ 0`. -/
noncomputable def clampCLM {s : ℝ} (hs : 0 ≤ s) : X →L[ℝ] ℝ :=
  mulCLM (clampExp s) (measurable_clampExp s) (abs_clampExp_le_one hs)

/-- **The transform, read off a bounded functional.** -/
theorem clampCLM_mconvL1_boxL1 {μ : Measure ℝ} [IsFiniteMeasure μ] (hμ : IsCausal μ) {s : ℝ}
    (hs : 0 ≤ s) :
    clampCLM hs (mconvL1 μ boxL1) = (∫ t, clampExp s t * box t) * laplace μ s := by
  rw [clampCLM, mulCLM_apply, ← integral_clampExp_mconv_box hμ hs]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_mconvL1_boxL1 μ] with t ht
  rw [ht]

/-! ## The transform of a causal probability measure

The two elementary bounds `\hat\mu(s) \in (0,1]` that make `-\log \hat\mu` well defined and
nonnegative, and continuity in `s` by dominated convergence.
-/

theorem laplace_le_one {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsCausal μ) {s : ℝ}
    (hs : 0 ≤ s) : laplace μ s ≤ 1 := by
  rw [laplace_eq_toReal_laplaceL]
  calc (laplaceL μ s).toReal ≤ (μ univ).toReal :=
        ENNReal.toReal_mono (measure_ne_top μ univ) (laplaceL_le_mass hμ hs)
    _ = 1 := by rw [measure_univ, ENNReal.toReal_one]

@[simp] theorem laplace_zero_prob (μ : Measure ℝ) [IsProbabilityMeasure μ] : laplace μ 0 = 1 := by
  rw [laplace_eq_toReal_laplaceL, laplaceL_zero_prob, ENNReal.toReal_one]

theorem laplace_pos_of_prob {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsCausal μ) {s : ℝ}
    (hs : 0 ≤ s) : 0 < laplace μ s :=
  laplace_pos hμ (IsProbabilityMeasure.ne_zero μ) hs

/-- **`s ↦ \hat\mu(s)` is continuous on `[0,∞)`.** Dominated convergence with the constant
bound `1`, which is where causality is used: off `[0,∞)` the integrand is unbounded. -/
theorem continuousOn_laplace {μ : Measure ℝ} [IsFiniteMeasure μ] (hμ : IsCausal μ) :
    ContinuousOn (fun s => laplace μ s) (Ici 0) := by
  refine continuousOn_of_dominated (bound := fun _ => 1)
    (fun s _ => (Real.continuous_exp.comp (by fun_prop)).aestronglyMeasurable)
    (fun s hs => ?_) (integrable_const 1) ?_
  · have hs0 : 0 ≤ s := hs
    filter_upwards [hμ.ae_nonneg] with t ht
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  · filter_upwards with t
    exact (Real.continuous_exp.comp (by fun_prop)).continuousOn

namespace CascadeCore

variable {Fam : CascadeCore} {x y : ℝ}

/-- The index set of the family, `{0 ≤ x ≤ y}`. -/
def Index : Set (ℝ × ℝ) := {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2}

theorem clampCLM_Phi_boxL1 (hx : 0 ≤ x) (hxy : x ≤ y) {s : ℝ} (hs : 0 ≤ s) :
    clampCLM hs (Fam.Φ x y boxL1)
      = (∫ t, clampExp s t * box t) * laplace (Fam.repr x y) s := by
  rw [Phi_eq_mconvL1_repr hx hxy]
  exact clampCLM_mconvL1_boxL1 (isCausal_repr Fam x y) hs

/-- **The transform is continuous in the parameters**, for each fixed `s ≥ 0`. This is (A7)
divided by the strictly positive constant `⟨g_s, 1_{(0,1)}⟩`. -/
theorem continuousOn_laplace_repr (Fam : CascadeCore) {s : ℝ} (hs : 0 ≤ s) :
    ContinuousOn (fun p : ℝ × ℝ => laplace (Fam.repr p.1 p.2) s) Index := by
  set Λ : ℝ := ∫ t, clampExp s t * box t with hΛdef
  have hΛ : 0 < Λ := integral_clampExp_box_pos hs
  have hcont : ContinuousOn (fun p : ℝ × ℝ => clampCLM hs (Fam.Φ p.1 p.2 boxL1) / Λ) Index :=
    (((clampCLM hs).continuous.comp_continuousOn (Fam.continuous boxL1)).div_const Λ)
  refine hcont.congr fun p hp => ?_
  change laplace (Fam.repr p.1 p.2) s = clampCLM hs (Fam.Φ p.1 p.2 boxL1) / Λ
  rw [clampCLM_Phi_boxL1 hp.1 hp.2 hs, ← hΛdef, mul_comm, mul_div_assoc, div_self hΛ.ne',
    mul_one]

/-! ## The exponent -/

/-- **`g_{x,y}(s) = -\log \hat\mu_{x,y}(s)`**, the object Chapter 5 works with. -/
noncomputable def exponent (Fam : CascadeCore) (x y s : ℝ) : ℝ :=
  -Real.log (laplace (Fam.repr x y) s)

/-- The exponent is nonnegative: the transform of a causal probability measure is at most `1`. -/
theorem exponent_nonneg (Fam : CascadeCore) (x y : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ Fam.exponent x y s := by
  rw [exponent, neg_nonneg]
  exact Real.log_nonpos (laplace_pos_of_prob (isCausal_repr Fam x y) hs).le
    (laplace_le_one (isCausal_repr Fam x y) hs)

/-- **`g_{x,y}(\zp) = 0`.** No limit is taken: the value at `0` is already `0`, and continuity
in `s` on `[0,∞)` — the next result — turns that into the statement the article makes. -/
@[simp] theorem exponent_zero (Fam : CascadeCore) (x y : ℝ) : Fam.exponent x y 0 = 0 := by
  rw [exponent, laplace_zero_prob, Real.log_one, neg_zero]

/-- **The exponent is continuous in the parameters**, for each fixed `s ≥ 0`. -/
theorem continuousOn_exponent (Fam : CascadeCore) {s : ℝ} (hs : 0 ≤ s) :
    ContinuousOn (fun p : ℝ × ℝ => Fam.exponent p.1 p.2 s) Index := by
  refine ContinuousOn.neg (ContinuousOn.log (continuousOn_laplace_repr Fam hs) fun p _ => ?_)
  exact (laplace_pos_of_prob (isCausal_repr Fam p.1 p.2) hs).ne'

/-- **The exponent is continuous in `s` on `[0,∞)`.** -/
theorem continuousOn_exponent_right (Fam : CascadeCore) (x y : ℝ) :
    ContinuousOn (fun s => Fam.exponent x y s) (Ici 0) := by
  refine ContinuousOn.neg
    (ContinuousOn.log (continuousOn_laplace (isCausal_repr Fam x y)) fun s hs => ?_)
  exact (laplace_pos_of_prob (isCausal_repr Fam x y) hs).ne'

/-- **`lem:transform-continuity`.** The exponent is well defined and nonnegative, vanishes at
the origin, and is continuous separately in the parameters and in `s`. -/
theorem transform_continuity (Fam : CascadeCore) :
    (∀ (x y s : ℝ), 0 ≤ s → 0 ≤ Fam.exponent x y s) ∧
      (∀ x y : ℝ, Fam.exponent x y 0 = 0) ∧
      (∀ s : ℝ, 0 ≤ s → ContinuousOn (fun p : ℝ × ℝ => Fam.exponent p.1 p.2 s) Index) ∧
      (∀ x y : ℝ, ContinuousOn (fun s => Fam.exponent x y s) (Ici 0)) :=
  ⟨fun x y _ hs => exponent_nonneg Fam x y hs, exponent_zero Fam,
    fun _ hs => continuousOn_exponent Fam hs, continuousOn_exponent_right Fam⟩

end CascadeCore

end Hemigroup
