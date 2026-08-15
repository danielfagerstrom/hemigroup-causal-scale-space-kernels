/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.MainTheorem
import Hemigroup.SignalingForm
import Hemigroup.SemigroupCase
import Hemigroup.LocalityClassification
import Hemigroup.GammaDensity
import Hemigroup.ClosedForms
import Hemigroup.DelayCore

/-!
# Witnesses: the headline hypotheses are jointly satisfiable

`PLAN-fidelity-review.md`, P1. Nothing in the development imports this file, and nothing here is
cited by a blueprint node. Its only purpose is to show, by *named* theorems that `CIAxiomGuard`
can `#print axioms`, that the hypotheses of the headline theorems are satisfied together at
concrete models — so that no headline theorem is true only because its hypotheses are empty.

A hypothesis that no model satisfies would be a vacuity finding; a hypothesis a model satisfies
only under a restriction the article does not state would be a domain finding. Both are what this
file is for, and both are recorded per target and per model below.

## Models

* **Pure drift**, `driftExponent b₀`: `b₀ > 0`, `k = 0`. Its kernels are point masses,
  `μ_{0,x} = δ_{b₀ x}`, so `T₁ = b₀` almost surely, every negative moment is `b₀^{-ζ} < ∞`,
  `z_* = ∞`, and `F(s) = b₀ s → ∞`. It is also the one-parameter family with `α = 1`.
* **Gamma**, `gammaExponent γ`: `k(t) = γ e^{-t}`, `F(s) = γ log(1+s)`, `T₁ ~ Gamma(γ, 1)`.
  `E[T₁^{-ζ}] < ∞` iff `ζ < γ`, so `z_* ≥ γ` and (H) holds for `γ > 1`.
* **Stable**, `stableExponent α`: `F(s) = s^α`, `0 < α < 1`.

## Targets and what is discharged

`main_characterization` (Theorem 2′):
* (⇐) `hF`: drift (`b₀ > 0`), Gamma (`γ > 0`), stable (all `α`).
* (⇒) `IsScaleCovariant Fam (Ioi 0) S`: for every admissible `F` with `hF`, at
  `Fam = (F.cascadeFamily hF).toCascadeCore` and `S σ x = σ * x` (`cascadeFamily_S`), hence at
  all three models.
* uniqueness: `χ = id` with `F' = F` satisfies all six hypotheses, for every `F` with `hF`.

`signaling_form` (Theorem 4′):
* `StandingHypothesis`: drift (`b₀ > 0`), Gamma (`γ > 1`). Stable: **not shown** — it needs a
  negative moment of the stable law past the first, and the development has no closed form for
  the stable density (`prop:stable-moments` is about positive moments and does not help).
* `hc`, `hc'`: drift (any `c > 0`, since `z_* = ∞`); Gamma with `c = (γ-1)/2` for `γ > 1`, since
  `c + 1 = (γ+1)/2 < γ ≤ z_*`. **No `γ > 2` restriction arises**: `hc'` asks
  `c + 1 < z_*`, and any `γ > 1` leaves room for some `c > 0`.
* the signal `g, f`: `g = box − box(· − 1)`, `f = ∫₀^· g` (a tent on `[0,2]`), which is causal,
  integrable, and — the clause the docstring of `SignalingForm.lean` warns about — has `∫ g = 0`,
  so that `f` is integrable. This is model-independent (`signal_hypotheses`).
  So `signaling_form`'s hypotheses are jointly satisfied at drift and at Gamma (`γ > 1`).

`semigroup_case` (Corollary 7.4): `IsScaleCovariant`, `IsOneParameter`, and `G 1 1 = 1`, at
drift with `b₀ = 1` (where the corollary's conclusion reads `α = 1`). `IsOneParameter` fails for
`gammaExponent` and `stableExponent` *as constructed here*, i.e. in the canonical gauge, where the
increment over `[x, x+r]` depends on `x`; the one-parameter stable semigroups with `α < 1` that
the corollary also classifies are those cores after the reparametrisation `x ↦ x^{1/α}`, which
this file does not build.

`lem:local-polynomial-symbol` (`isLocalOfOrderCoreOfSymbolEq`, `not_isLocalOfOrder_zero`,
`exists_moment_form_of_isLocalOfOrder`): `StandingHypothesis`, `0 < c`, and
`ENNReal.ofReal c < F.zStar - 1`, at drift (any `c`, plus `AllNegMomentsFinite`, the `hA13`
hypothesis) and at Gamma (`γ > 1`, `c = (γ-1)/2`).

## What is deliberately not here

The *conclusions* of the targets at the models — e.g. that `main_analysis` returns `χ = id` at
drift — are not checked; that is the business of the fidelity cards, not of a witness file.
-/

namespace Hemigroup

open MeasureTheory Set Filter

open scoped Topology ENNReal

namespace SelfDecomposableExponent

variable {F : SelfDecomposableExponent}

/-! ## Generic facts, for every admissible `F` -/

/-- `F(s) ≠ 0` in `ℝ` implies `F(s) ≠ 0` in `[0,∞]`. -/
theorem exponent_ne_zero_of_toRealExponent_ne_zero {s : ℝ} (h : F.toRealExponent s ≠ 0) :
    F.exponent s ≠ 0 := fun h0 => h (by rw [toRealExponent, h0, ENNReal.toReal_zero])

/-- The scaling action of the constructed family is multiplication: `S σ x = σ x`. -/
theorem cascadeFamily_S (hF : ∃ s₀, 0 < s₀ ∧ F.exponent s₀ ≠ 0) :
    (F.cascadeFamily hF).S = fun σ x => σ * x := rfl

/-- The representing measures of the constructed family are the kernels it was built from. -/
theorem repr_cascadeFamily (hF : ∃ s₀, 0 < s₀ ∧ F.exponent s₀ ≠ 0) {x y : ℝ} (hx : 0 ≤ x)
    (hxy : x ≤ y) : (F.cascadeFamily hF).toCascadeCore.repr x y = F.kernel x y :=
  mconvL1_injective (CascadeCore.isCausal_repr _ x y) (isCausal_kernel hx hxy)
    (CascadeCore.Phi_eq_mconvL1_repr hx hxy).symm

/-- **`main_characterization` (⇒), instantiated**: for every admissible nondegenerate `F`, the
constructed family is a scale-covariant cascade core, with the multiplicative action. -/
theorem witness_main_characterization_covariant (hF : ∃ s₀, 0 < s₀ ∧ F.exponent s₀ ≠ 0) :
    IsScaleCovariant (F.cascadeFamily hF).toCascadeCore (Ioi 0) (fun σ x => σ * x) :=
  (F.cascadeFamily hF).covariant

/-- **`main_characterization` (uniqueness), instantiated**: `χ = id`, `F' = F` satisfy all six
hypotheses of the uniqueness clause. -/
theorem witness_main_characterization_uniqueness (hF : ∃ s₀, 0 < s₀ ∧ F.exponent s₀ ≠ 0) :
    (∀ u : ℝ, 0 < u → 0 < id u) ∧
    (∀ ⦃u v : ℝ⦄, 0 < u → u ≤ v → id u ≤ id v) ∧
    (∀ ε : ℝ, 0 < ε → ∃ u : ℝ, 0 < u ∧ id u < ε) ∧
    (∀ u v : ℝ, 0 < u → u ≤ v → F.kernel (id u) (id v) = F.kernel u v) ∧
    id (1 : ℝ) = 1 ∧ (∃ s₀ : ℝ, 0 < s₀ ∧ F.exponent s₀ ≠ 0) :=
  ⟨fun _ hu => hu, fun _ _ _ huv => huv,
   fun ε hε => ⟨ε / 2, by positivity, by simp; linarith⟩,
   fun _ _ _ _ => rfl, rfl, hF⟩

/-! ## The signal for `signaling_form`

`g = box − box(· − 1)`, the derivative of the tent `f(r) = r` on `[0,1]`, `2 − r` on `[1,2]`,
`0` elsewhere. The point of the choice: `∫ g = 0` by translation invariance, without computing
either integral, and that is exactly what makes the primitive integrable. -/

/-- The signal's derivative. -/
noncomputable def tentDeriv : ℝ → ℝ := fun t => box t - box (t - 1)

/-- The signal: the primitive of `tentDeriv` from the origin. -/
noncomputable def tent : ℝ → ℝ := fun r => ∫ ρ in Ioc (0 : ℝ) r, tentDeriv ρ

theorem measurable_tentDeriv : Measurable tentDeriv :=
  measurable_box.sub (measurable_box.comp (measurable_id.sub_const 1))

theorem integrable_tentDeriv : Integrable tentDeriv :=
  integrable_box.sub (integrable_box.comp_sub_right 1)

theorem box_eq_zero_of_not_mem {t : ℝ} (h : t ∉ Ioo (0 : ℝ) 1) : box t = 0 :=
  indicator_of_notMem h _

theorem tentDeriv_causal : ∀ r : ℝ, r < 0 → tentDeriv r = 0 := fun r hr => by
  change box r - box (r - 1) = 0
  rw [box_eq_zero_of_not_mem (fun h => absurd h.1 (not_lt.mpr hr.le)),
    box_eq_zero_of_not_mem (fun h => absurd h.1 (by linarith)), sub_zero]

theorem tentDeriv_eq_zero_of_two_le {r : ℝ} (hr : 2 ≤ r) : tentDeriv r = 0 := by
  change box r - box (r - 1) = 0
  rw [box_eq_zero_of_not_mem (fun h => absurd h.2 (by linarith)),
    box_eq_zero_of_not_mem (fun h => absurd h.2 (by linarith)), sub_zero]

/-- `∫ g = 0`: the two boxes have the same integral, being translates. -/
theorem integral_tentDeriv : ∫ t, tentDeriv t = 0 := by
  change ∫ t, (box t - box (t - 1)) = 0
  rw [integral_sub integrable_box (integrable_box.comp_sub_right 1),
    integral_sub_right_eq_self box 1, sub_self]

theorem tent_eq_intervalIntegral (r : ℝ) : tent r = ∫ ρ in (0 : ℝ)..r, tentDeriv ρ :=
  setIntegral_Ioc_eq_intervalIntegral_of_causal integrable_tentDeriv tentDeriv_causal r

theorem continuous_tent : Continuous tent :=
  (integrable_tentDeriv.continuous_primitive 0).congr fun r => (tent_eq_intervalIntegral r).symm

theorem measurable_tent : Measurable tent := continuous_tent.measurable

/-- `f` vanishes to the left of the origin ... -/
theorem tent_eq_zero_of_neg {r : ℝ} (hr : r < 0) : tent r = 0 := by
  rw [tent, Ioc_eq_empty (not_lt.mpr hr.le), Measure.restrict_empty, integral_zero_measure]

/-- ... and beyond `2`, because `∫ g = 0`. -/
theorem tentDeriv_eq_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) : tentDeriv t = 0 := by
  rcases ht.lt_or_eq with ht | rfl
  · exact tentDeriv_causal t ht
  · change box 0 - box (0 - 1) = 0
    simp [box]

theorem tent_eq_zero_of_two_le {r : ℝ} (hr : 2 ≤ r) : tent r = 0 := by
  have h : ∫ ρ in Ioc (0 : ℝ) r, tentDeriv ρ = ∫ t, tentDeriv t := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_
    rw [mem_Ioc, not_and_or, not_lt, not_le] at ht
    rcases ht with ht | ht
    · exact tentDeriv_eq_zero_of_nonpos ht
    · exact tentDeriv_eq_zero_of_two_le (by linarith)
  rw [tent, h, integral_tentDeriv]

/-- `|f| ≤ ‖g‖₁` everywhere. -/
theorem abs_tent_le (r : ℝ) : |tent r| ≤ ∫ t, |tentDeriv t| := by
  rw [tent]
  calc |∫ ρ in Ioc (0 : ℝ) r, tentDeriv ρ| ≤ ∫ ρ in Ioc (0 : ℝ) r, |tentDeriv ρ| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ t, |tentDeriv t| :=
        setIntegral_le_integral integrable_tentDeriv.abs (.of_forall fun _ => abs_nonneg _)

/-- `f ∈ L¹`: bounded, and supported in `[0,2]`. -/
theorem integrable_tent : Integrable tent := by
  refine Integrable.mono' (g := (Icc (0 : ℝ) 2).indicator fun _ => ∫ t, |tentDeriv t|)
    ((integrableOn_const (C := ∫ t, |tentDeriv t|) (s := Icc (0 : ℝ) 2)
      (measure_Icc_lt_top.ne)).integrable_indicator measurableSet_Icc)
    continuous_tent.aestronglyMeasurable (Eventually.of_forall fun r => ?_)
  by_cases hr : r ∈ Icc (0 : ℝ) 2
  · rw [indicator_of_mem hr, Real.norm_eq_abs]
    exact abs_tent_le r
  · rw [indicator_of_notMem hr, Real.norm_eq_abs]
    rw [mem_Icc, not_and_or, not_le, not_le] at hr
    rcases hr with hr | hr
    · rw [tent_eq_zero_of_neg hr, abs_zero]
    · rw [tent_eq_zero_of_two_le hr.le, abs_zero]

/-- **The six signal hypotheses of `signaling_form`, satisfied by the tent.** In particular
`f ∈ 𝒟` (`HasCoreDeriv tent tentDeriv`, by `memCore_iff_signaling_hypotheses`). -/
theorem signal_hypotheses :
    Measurable tentDeriv ∧ Integrable tentDeriv ∧ (∀ r : ℝ, r < 0 → tentDeriv r = 0) ∧
      Measurable tent ∧ Integrable tent ∧
      (∀ r : ℝ, tent r = ∫ ρ in Ioc (0 : ℝ) r, tentDeriv ρ) :=
  ⟨measurable_tentDeriv, integrable_tentDeriv, tentDeriv_causal, measurable_tent,
   integrable_tent, fun _ => rfl⟩

theorem hasCoreDeriv_tent : HasCoreDeriv tent tentDeriv :=
  memCore_iff_signaling_hypotheses.mpr signal_hypotheses

/-! ## Model 1: pure drift -/

/-- **Pure drift**: `b₀ ≥ 0`, `k = 0`. The kernels are point masses at `b₀ x`. -/
noncomputable def driftExponent (b₀ : ℝ) (hb : 0 ≤ b₀) : SelfDecomposableExponent where
  b₀ := b₀
  k := fun _ => 0
  b₀_nonneg := hb
  k_nonneg := fun _ _ => le_rfl
  k_antitone := fun _ _ _ _ _ => le_rfl
  k_zero := rfl
  ne_top := fun _ _ => by simp [levyExponentD, levyJump]

variable {b₀ : ℝ}

theorem driftExponent_exponent (hb : 0 ≤ b₀) (s : ℝ) :
    (driftExponent b₀ hb).exponent s = ENNReal.ofReal (b₀ * s) := by
  simp [exponent, levyExponentD, levyJump, driftExponent]

theorem driftExponent_toRealExponent (hb : 0 ≤ b₀) {s : ℝ} (hs : 0 ≤ s) :
    (driftExponent b₀ hb).toRealExponent s = b₀ * s := by
  rw [toRealExponent, driftExponent_exponent, ENNReal.toReal_ofReal (mul_nonneg hb hs)]

theorem driftExponent_increment (hb : 0 ≤ b₀) (a b s : ℝ) :
    (driftExponent b₀ hb).increment a b s = ENNReal.ofReal (b₀ * (b - a) * s) := by
  simp [increment, incrementDensity, levyExponentD, levyJump, driftExponent]

/-- The transform of a point mass. -/
theorem laplace_dirac (a s : ℝ) : laplace (Measure.dirac a) s = Real.exp (-(s * a)) := by
  rw [laplace, integral_dirac]

/-- **The drift kernels are point masses**: `μ_{a,b} = δ_{b₀(b-a)}`. -/
theorem driftExponent_kernel (hb : 0 ≤ b₀) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (driftExponent b₀ hb).kernel a b = Measure.dirac (b₀ * (b - a)) := by
  refine ((driftExponent b₀ hb).kernel_unique (isCausal_dirac (by nlinarith)) ha hab
    fun s hs => ?_).symm
  rw [laplace_dirac, driftExponent_increment,
    ENNReal.toReal_ofReal (by have := sub_nonneg.mpr hab; positivity)]
  ring_nf

theorem driftExponent_lawT₁ (hb : 0 ≤ b₀) :
    (driftExponent b₀ hb).lawT₁ = Measure.dirac b₀ := by
  rw [lawT₁, driftExponent_kernel hb le_rfl zero_le_one, sub_zero, mul_one]

/-- (ND) at drift: `F(1) = b₀ ≠ 0`. -/
theorem witness_hF_drift (hb : 0 < b₀) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ (driftExponent b₀ hb.le).exponent s₀ ≠ 0 :=
  ⟨1, zero_lt_one, exponent_ne_zero_of_toRealExponent_ne_zero
    (by rw [driftExponent_toRealExponent hb.le zero_le_one, mul_one]; exact hb.ne')⟩

/-- Every negative moment of `T₁ = b₀` is finite: `E[T₁^{-ζ}] ≤ b₀^{-ζ}`. -/
theorem driftExponent_allNegMomentsFinite (hb : 0 < b₀) :
    (driftExponent b₀ hb.le).AllNegMomentsFinite := by
  intro ζ _
  rw [negMoment, driftExponent_lawT₁]
  refine ne_top_of_le_ne_top ?_ (setLIntegral_le_lintegral _ _)
  rw [lintegral_dirac]
  exact ENNReal.ofReal_ne_top

theorem driftExponent_tendsto (hb : 0 < b₀) :
    Tendsto (driftExponent b₀ hb.le).toRealExponent atTop atTop := by
  refine (Tendsto.const_mul_atTop hb tendsto_id).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
  exact (driftExponent_toRealExponent hb.le hs).symm

/-- **(H) at drift.** -/
theorem witness_standingHypothesis_drift (hb : 0 < b₀) :
    (driftExponent b₀ hb.le).StandingHypothesis :=
  ⟨driftExponent_tendsto hb,
   by rw [(driftExponent b₀ hb.le).zStar_eq_top (driftExponent_allNegMomentsFinite hb)]
      exact ENNReal.one_lt_top⟩

/-- **`main_characterization` at drift**: (⇐)'s `hF`; (⇒)'s covariant core; uniqueness's `χ`. -/
theorem witness_main_characterization_drift (hb : 0 < b₀) :
    (∃ s₀ : ℝ, 0 < s₀ ∧ (driftExponent b₀ hb.le).exponent s₀ ≠ 0) ∧
    IsScaleCovariant ((driftExponent b₀ hb.le).cascadeFamily (witness_hF_drift hb)).toCascadeCore
      (Ioi 0) (fun σ x => σ * x) ∧
    (∀ u : ℝ, 0 < u → 0 < id u) ∧
    (∀ ⦃u v : ℝ⦄, 0 < u → u ≤ v → id u ≤ id v) ∧
    (∀ ε : ℝ, 0 < ε → ∃ u : ℝ, 0 < u ∧ id u < ε) ∧
    (∀ u v : ℝ, 0 < u → u ≤ v →
      (driftExponent b₀ hb.le).kernel (id u) (id v) = (driftExponent b₀ hb.le).kernel u v) ∧
    id (1 : ℝ) = 1 :=
  ⟨witness_hF_drift hb, witness_main_characterization_covariant _,
   (witness_main_characterization_uniqueness (witness_hF_drift hb)).1,
   (witness_main_characterization_uniqueness (witness_hF_drift hb)).2.1,
   (witness_main_characterization_uniqueness (witness_hF_drift hb)).2.2.1,
   (witness_main_characterization_uniqueness (witness_hF_drift hb)).2.2.2.1,
   rfl⟩

/-- **`signaling_form` at drift**: (H), (ND), any `c > 0` (since `z_* = ∞`), and the tent. -/
theorem witness_signaling_form_drift (hb : 0 < b₀) {c : ℝ} (hc : 0 < c) :
    (driftExponent b₀ hb.le).StandingHypothesis ∧
    (∃ s₀ : ℝ, 0 < s₀ ∧ (driftExponent b₀ hb.le).exponent s₀ ≠ 0) ∧
    0 < c ∧ ENNReal.ofReal (c + 1) < (driftExponent b₀ hb.le).zStar ∧
    Measurable tentDeriv ∧ Integrable tentDeriv ∧ (∀ r : ℝ, r < 0 → tentDeriv r = 0) ∧
    Measurable tent ∧ Integrable tent ∧
    (∀ r : ℝ, tent r = ∫ ρ in Ioc (0 : ℝ) r, tentDeriv ρ) :=
  ⟨witness_standingHypothesis_drift hb, witness_hF_drift hb, hc,
   (driftExponent b₀ hb.le).ofReal_lt_zStar_of_all (driftExponent_allNegMomentsFinite hb) _,
   signal_hypotheses⟩

/-- **`lem:local-polynomial-symbol` at drift**: (H), any `c > 0` below `z_* - 1 = ∞`, and
`AllNegMomentsFinite` (the `hA13` hypothesis of `exists_moment_form_of_isLocalOfOrder`). -/
theorem witness_local_polynomial_symbol_drift (hb : 0 < b₀) {c : ℝ} (hc : 0 < c) :
    (driftExponent b₀ hb.le).StandingHypothesis ∧ 0 < c ∧
    ENNReal.ofReal c < (driftExponent b₀ hb.le).zStar - 1 ∧
    (driftExponent b₀ hb.le).AllNegMomentsFinite :=
  ⟨witness_standingHypothesis_drift hb, hc,
   (driftExponent b₀ hb.le).ofReal_lt_zStar_sub_one_of_all (driftExponent_allNegMomentsFinite hb) _,
   driftExponent_allNegMomentsFinite hb⟩

/-- **The drift family is one-parameter**: `μ_{x,x+r} = δ_{b₀ r} = μ_{0,r}`. -/
theorem driftExponent_isOneParameter (hb : 0 < b₀) :
    ((driftExponent b₀ hb.le).cascadeFamily (witness_hF_drift hb)).toCascadeCore.IsOneParameter :=
  fun x r hx hr => by
    change mconvL1 ((driftExponent b₀ hb.le).kernel x (x + r))
      = mconvL1 ((driftExponent b₀ hb.le).kernel 0 r)
    rw [mconvL1_congr (driftExponent_kernel hb.le hx (by linarith)),
      mconvL1_congr (driftExponent_kernel hb.le le_rfl hr), add_sub_cancel_left, sub_zero]

/-- The normalisation `G(1,1) = 1` at drift with `b₀ = 1`. -/
theorem driftExponent_G_one_one :
    ((driftExponent 1 zero_le_one).cascadeFamily (witness_hF_drift zero_lt_one)).toCascadeCore.G
      1 1 = 1 := by
  rw [CascadeCore.G, CascadeCore.exponent, repr_cascadeFamily _ le_rfl zero_le_one,
    laplace_kernel le_rfl zero_le_one zero_le_one, Real.log_exp, neg_neg,
    driftExponent_increment, ENNReal.toReal_ofReal (by norm_num)]
  norm_num

/-- **`semigroup_case` at drift with `b₀ = 1`**: covariance, one-parameter, normalised. -/
theorem witness_semigroup_case_drift :
    IsScaleCovariant ((driftExponent 1 zero_le_one).cascadeFamily
        (witness_hF_drift zero_lt_one)).toCascadeCore (Ioi 0) (fun σ x => σ * x) ∧
    ((driftExponent 1 zero_le_one).cascadeFamily
        (witness_hF_drift zero_lt_one)).toCascadeCore.IsOneParameter ∧
    ((driftExponent 1 zero_le_one).cascadeFamily
        (witness_hF_drift zero_lt_one)).toCascadeCore.G 1 1 = 1 :=
  ⟨witness_main_characterization_covariant _, driftExponent_isOneParameter zero_lt_one,
   driftExponent_G_one_one⟩

/-! ## Model 2: the Gamma family -/

variable {γ : ℝ}

/-- (ND) at Gamma: `F(1) = γ log 2 ≠ 0`. -/
theorem witness_hF_gamma (hγ : 0 < γ) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ (gammaExponent γ hγ.le).exponent s₀ ≠ 0 :=
  ⟨1, zero_lt_one, exponent_ne_zero_of_toRealExponent_ne_zero (by
    rw [gammaExponent_toRealExponent hγ.le zero_lt_one]
    exact (mul_pos hγ (Real.log_pos (by norm_num))).ne')⟩

theorem gammaExponent_tendsto (hγ : 0 < γ) :
    Tendsto (gammaExponent γ hγ.le).toRealExponent atTop atTop := by
  have h : Tendsto (fun s : ℝ => γ * Real.log (1 + s)) atTop atTop :=
    (Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_left _ 1 tendsto_id)).const_mul_atTop hγ
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  exact (gammaExponent_toRealExponent hγ.le hs).symm

theorem gammaExponent_lawT₁ (hγ : 0 < γ) :
    (gammaExponent γ hγ.le).lawT₁ = ProbabilityTheory.gammaMeasure γ 1 := by
  rw [lawT₁, gammaExponent_kernel_eq_gammaMeasure hγ zero_lt_one, inv_one]

/-- **`E[T₁^{-ζ}] < ∞` for `ζ < γ`**: `t^{-ζ} · t^{γ-1}e^{-t}` is integrable at the origin exactly
when `γ - ζ > 0`. (The converse, divergence for `ζ ≥ γ`, is true and not needed here.) -/
theorem gammaExponent_negMoment_ne_top (hγ : 0 < γ) {ζ : ℝ} (hζ : ζ < γ) :
    (gammaExponent γ hγ.le).negMoment ζ ≠ ⊤ := by
  open ProbabilityTheory in
  rw [negMoment, gammaExponent_lawT₁ hγ, gammaMeasure,
    setLIntegral_withDensity_eq_setLIntegral_mul _ (f := gammaPDF γ 1)
      (measurable_gammaPDFReal γ 1).ennreal_ofReal
      (g := fun t : ℝ => ENNReal.ofReal (t ^ (-ζ)))
      ((measurable_id.pow_const _).ennreal_ofReal) measurableSet_Ioi]
  have hint : IntegrableOn
      (fun t : ℝ => (1 : ℝ) ^ γ / Real.Gamma γ * (t ^ (γ - ζ - 1) * Real.exp (-(1 * t))))
      (Ioi 0) := by
    have h := (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := γ - ζ - 1) (b := 1)
      (by linarith) le_rfl zero_lt_one)
    have h2 : IntegrableOn (fun t : ℝ => (1 : ℝ) ^ γ / Real.Gamma γ
        * (t ^ (γ - ζ - 1) * Real.exp (-1 * t ^ (1 : ℝ)))) (Ioi 0) := h.const_mul _
    refine h2.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_one, neg_mul, one_mul]
  have hpt : ∀ t ∈ Ioi (0 : ℝ),
      (ProbabilityTheory.gammaPDF γ 1 * fun t : ℝ => ENNReal.ofReal (t ^ (-ζ))) t
        = ENNReal.ofReal
            ((1 : ℝ) ^ γ / Real.Gamma γ * (t ^ (γ - ζ - 1) * Real.exp (-(1 * t)))) := by
    intro t ht
    have ht' : (0 : ℝ) < t := mem_Ioi.mp ht
    simp only [Pi.mul_apply, ProbabilityTheory.gammaPDF, ProbabilityTheory.gammaPDFReal,
      if_pos ht'.le]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [show γ - ζ - 1 = (γ - 1) + (-ζ) by ring, Real.rpow_add ht']
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt]
  exact lintegral_ofReal_ne_top_of_integrableOn hint

/-- **(H) at Gamma, for `γ > 1`**: `F(s) = γ log(1+s) → ∞`, and `E[T₁^{-ζ}] < ∞` at
`ζ = (1+γ)/2 ∈ (1, γ)`. -/
theorem witness_standingHypothesis_gamma (hγ : 1 < γ) :
    (gammaExponent γ (zero_le_one.trans hγ.le)).StandingHypothesis :=
  ⟨gammaExponent_tendsto (zero_lt_one.trans hγ), by
    rw [← ENNReal.ofReal_one]
    exact (gammaExponent γ (zero_le_one.trans hγ.le)).ofReal_lt_zStar_of_lt (ζ := (1 + γ) / 2)
      zero_le_one (by linarith)
      (gammaExponent_negMoment_ne_top (zero_lt_one.trans hγ) (by linarith))⟩

/-- **`c + 1 < z_*` at Gamma with `c = (γ-1)/2`, for `γ > 1`.** No further restriction on `γ`
is needed: `c + 1 = (γ+1)/2 < (3γ+1)/4 < γ`, and the moment at `(3γ+1)/4` is finite. -/
theorem gammaExponent_ofReal_lt_zStar (hγ : 1 < γ) :
    ENNReal.ofReal ((γ - 1) / 2 + 1) < (gammaExponent γ (zero_le_one.trans hγ.le)).zStar :=
  (gammaExponent γ (zero_le_one.trans hγ.le)).ofReal_lt_zStar_of_lt (ζ := (3 * γ + 1) / 4)
    (by linarith) (by linarith)
    (gammaExponent_negMoment_ne_top (zero_lt_one.trans hγ) (by linarith))

/-- **`main_characterization` at Gamma (`γ > 0`)**: (⇐)'s `hF`; (⇒)'s covariant core;
uniqueness's `χ`. -/
theorem witness_main_characterization_gamma (hγ : 0 < γ) :
    (∃ s₀ : ℝ, 0 < s₀ ∧ (gammaExponent γ hγ.le).exponent s₀ ≠ 0) ∧
    IsScaleCovariant ((gammaExponent γ hγ.le).cascadeFamily (witness_hF_gamma hγ)).toCascadeCore
      (Ioi 0) (fun σ x => σ * x) ∧
    (∀ u : ℝ, 0 < u → 0 < id u) ∧
    (∀ ⦃u v : ℝ⦄, 0 < u → u ≤ v → id u ≤ id v) ∧
    (∀ ε : ℝ, 0 < ε → ∃ u : ℝ, 0 < u ∧ id u < ε) ∧
    (∀ u v : ℝ, 0 < u → u ≤ v →
      (gammaExponent γ hγ.le).kernel (id u) (id v) = (gammaExponent γ hγ.le).kernel u v) ∧
    id (1 : ℝ) = 1 :=
  ⟨witness_hF_gamma hγ, witness_main_characterization_covariant _,
   (witness_main_characterization_uniqueness (witness_hF_gamma hγ)).1,
   (witness_main_characterization_uniqueness (witness_hF_gamma hγ)).2.1,
   (witness_main_characterization_uniqueness (witness_hF_gamma hγ)).2.2.1,
   (witness_main_characterization_uniqueness (witness_hF_gamma hγ)).2.2.2.1,
   rfl⟩

/-- **`signaling_form` at Gamma (`γ > 1`)**: (H), (ND), `c = (γ-1)/2`, and the tent. -/
theorem witness_signaling_form_gamma (hγ : 1 < γ) :
    (gammaExponent γ (zero_le_one.trans hγ.le)).StandingHypothesis ∧
    (∃ s₀ : ℝ, 0 < s₀ ∧ (gammaExponent γ (zero_le_one.trans hγ.le)).exponent s₀ ≠ 0) ∧
    0 < (γ - 1) / 2 ∧
    ENNReal.ofReal ((γ - 1) / 2 + 1) < (gammaExponent γ (zero_le_one.trans hγ.le)).zStar ∧
    Measurable tentDeriv ∧ Integrable tentDeriv ∧ (∀ r : ℝ, r < 0 → tentDeriv r = 0) ∧
    Measurable tent ∧ Integrable tent ∧
    (∀ r : ℝ, tent r = ∫ ρ in Ioc (0 : ℝ) r, tentDeriv ρ) :=
  ⟨witness_standingHypothesis_gamma hγ, witness_hF_gamma (zero_lt_one.trans hγ), by linarith,
   gammaExponent_ofReal_lt_zStar hγ, signal_hypotheses⟩

/-- **`lem:local-polynomial-symbol` at Gamma (`γ > 1`)**: (H) and `0 < c < z_* - 1` at
`c = (γ-1)/2`. (`AllNegMomentsFinite` — the `hA13` hypothesis of
`exists_moment_form_of_isLocalOfOrder` — is *false* at Gamma, where `E[T₁^{-ζ}] = ∞` for `ζ ≥ γ`;
that hypothesis is ledger A13's conclusion for a *local* operator, which the Gamma family with
its infinite negative moments is not, so this is expected rather than a finding.) -/
theorem witness_local_polynomial_symbol_gamma (hγ : 1 < γ) :
    (gammaExponent γ (zero_le_one.trans hγ.le)).StandingHypothesis ∧ 0 < (γ - 1) / 2 ∧
    ENNReal.ofReal ((γ - 1) / 2) < (gammaExponent γ (zero_le_one.trans hγ.le)).zStar - 1 :=
  ⟨witness_standingHypothesis_gamma hγ, by linarith, by
    rw [lt_tsub_iff_right, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by linarith) zero_le_one]
    exact gammaExponent_ofReal_lt_zStar hγ⟩

/-! ## Model 3: the stable family

Only (ND) and covariance. (H) is not shown: `1 < z_*` needs `E[T₁^{-ζ}] < ∞` for some `ζ > 1`,
which is true (every negative moment of the positive stable law is finite) but the development
has no closed form for the stable density, and the moment cannot be read off the exponent
`s^α` without the Mellin machinery of chapter 9, which presupposes (H). -/

variable {α : ℝ}

/-- (ND) at stable: `F(1) = 1`. -/
theorem witness_hF_stable (hα : 0 < α) (hα1 : α < 1) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ (stableExponent α hα hα1).exponent s₀ ≠ 0 :=
  ⟨1, zero_lt_one, exponent_ne_zero_of_toRealExponent_ne_zero (by
    rw [stableExponent_toRealExponent hα hα1 zero_lt_one, Real.one_rpow]; exact one_ne_zero)⟩

/-- **`main_characterization` at stable**: (⇐)'s `hF`; (⇒)'s covariant core; uniqueness's `χ`. -/
theorem witness_main_characterization_stable (hα : 0 < α) (hα1 : α < 1) :
    (∃ s₀ : ℝ, 0 < s₀ ∧ (stableExponent α hα hα1).exponent s₀ ≠ 0) ∧
    IsScaleCovariant ((stableExponent α hα hα1).cascadeFamily
      (witness_hF_stable hα hα1)).toCascadeCore (Ioi 0) (fun σ x => σ * x) ∧
    (∀ u : ℝ, 0 < u → 0 < id u) ∧
    (∀ ⦃u v : ℝ⦄, 0 < u → u ≤ v → id u ≤ id v) ∧
    (∀ ε : ℝ, 0 < ε → ∃ u : ℝ, 0 < u ∧ id u < ε) ∧
    (∀ u v : ℝ, 0 < u → u ≤ v →
      (stableExponent α hα hα1).kernel (id u) (id v) = (stableExponent α hα hα1).kernel u v) ∧
    id (1 : ℝ) = 1 :=
  ⟨witness_hF_stable hα hα1, witness_main_characterization_covariant _,
   (witness_main_characterization_uniqueness (witness_hF_stable hα hα1)).1,
   (witness_main_characterization_uniqueness (witness_hF_stable hα hα1)).2.1,
   (witness_main_characterization_uniqueness (witness_hF_stable hα hα1)).2.2.1,
   (witness_main_characterization_uniqueness (witness_hF_stable hα hα1)).2.2.2.1,
   rfl⟩

end SelfDecomposableExponent

end Hemigroup
