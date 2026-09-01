/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the MIT license as described in the file LICENSES/MIT.txt.
Authors: Daniel Fagerström
-/
import Hemigroup.MainTheorem
import Hemigroup.SignalingForm
import Hemigroup.SemigroupCase
import Hemigroup.LocalityClassification
import Hemigroup.GammaDensity
import Hemigroup.ClosedForms
import Hemigroup.DelayCore
import Mathlib.MeasureTheory.Integral.Gamma

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

## R14: a Lean-core witness

Every model above passes through `kernel`, so every witness of `main_characterization`'s (⇒)
hypotheses so far is A17-dependent however elementary the model — `driftExponent` included, since
`witness_main_characterization_covariant` is stated at `(F.cascadeFamily hF).toCascadeCore`, and
`cascadeFamily` is built on `kernel`. `delayCore`, below, is a second, independent witness that
does not: `Φ_{x,y} = τ_{y-x}` is literal translation by the increment, and its `CascadeCore` and
`IsScaleCovariant` fields are all facts about `transL1`/`dilL1` (chapter 4's isometries), so
`witness_main_characterization_delayCore` prints Lean core alone. That the hypothesis class is
nonempty independently of the construction that proves the theorem is the fact the P1 vacuity
pass exists to check; the drift/Gamma/stable models check it only up to A17, and `delayCore`
closes that gap.
-/

namespace Hemigroup

open MeasureTheory Set Filter

open scoped Topology ENNReal

/-! ## The pure-delay core (R14)

Built to witness that the (⇒) hypotheses of `main_characterization` — a `CascadeCore` together
with `IsScaleCovariant` at the multiplicative action — are satisfiable at a model resting on
nothing beyond Lean core: no kernel, hence no ledger axiom A17. Everything below rests on facts
about `transL1`/`dilL1` already proved for chapter 4's Wendel argument (`Symmetries.lean`,
`Representation.lean`); `transL1_add` (composition) and `dilL1_comp_transL1` (the
dilation/translation intertwining) are the two the development did not already need and this
file does.
-/

/-- **Translations compose additively.** `τ_a ∘ τ_b = τ_{a+b}`, the one composition fact about
`transL1` chapter 4's Wendel argument did not need. -/
theorem transL1_add (a b : ℝ) (f : X) : transL1 a (transL1 b f) = transL1 (a + b) f := by
  refine Lp.ext ?_
  have ha : (transL1 a (transL1 b f) : ℝ → ℝ) =ᵐ[volume] fun t => (transL1 b f : ℝ → ℝ) (t - a) :=
    coeFn_transL1 a (transL1 b f)
  have hpull : (fun t : ℝ => (transL1 b f : ℝ → ℝ) (t - a))
      =ᵐ[volume] fun t => (f : ℝ → ℝ) (t - a - b) :=
    (measurePreserving_sub_const a).quasiMeasurePreserving.ae (coeFn_transL1 b f)
  have heq : (fun t : ℝ => (f : ℝ → ℝ) (t - a - b)) = fun t => (f : ℝ → ℝ) (t - (a + b)) := by
    funext t; rw [sub_sub]
  rw [heq] at hpull
  exact (ha.trans hpull).trans (coeFn_transL1 (a + b) f).symm

/-- **(A2) for `delayCore`.** Translation commutes with translation. -/
theorem delayCore_translation (x y a : ℝ) (f : X) :
    transL1 (y - x) (transL1 a f) = transL1 a (transL1 (y - x) f) := by
  rw [transL1_add, transL1_add, add_comm]

/-- **(A3) for `delayCore`.** Translating forward by `r ≥ 0` cannot move mass earlier than `t₀`:
if `f` vanishes before `t₀`, its translate does too (in fact before `t₀ + r`, but the weaker
statement is all (A3) asks). -/
theorem vanishesBefore_transL1 {r : ℝ} (hr : 0 ≤ r) {t₀ : ℝ} {f : X}
    (hf : VanishesBefore t₀ f) : VanishesBefore t₀ (transL1 r f) := by
  have hpull : ∀ᵐ t : ℝ, t - r < t₀ → (f : ℝ → ℝ) (t - r) = 0 :=
    (measurePreserving_sub_const r).quasiMeasurePreserving.ae hf
  filter_upwards [coeFn_transL1 r f, hpull] with t ht hsub htlt
  rw [ht]
  exact hsub (by linarith)

/-- **(A4) for `delayCore`.** Translation preserves the positive cone. -/
theorem isNonneg_transL1 (r : ℝ) {f : X} (hf : IsNonneg f) : IsNonneg (transL1 r f) := by
  have hpull : 0 ≤ᵐ[volume] fun t => (f : ℝ → ℝ) (t - r) :=
    (measurePreserving_sub_const r).quasiMeasurePreserving.ae hf
  filter_upwards [coeFn_transL1 r f, hpull] with t ht h0
  rw [Pi.zero_apply, ht]
  exact h0

/-- **(A5) for `delayCore`.** Translation preserves the integral — Lebesgue measure is
translation invariant. -/
theorem integral_transL1 (r : ℝ) (f : X) :
    ∫ t, ((transL1 r f : X) : ℝ → ℝ) t = ∫ t, (f : ℝ → ℝ) t := by
  rw [integral_congr_ae (coeFn_transL1 r f)]
  exact integral_sub_right_eq_self (f : ℝ → ℝ) r

/-- **(A6), the cascade clause, for `delayCore`.** `τ_{z-y} ∘ τ_{y-x} = τ_{z-x}`. -/
theorem delayCore_cascade (x y z : ℝ) :
    (transL1 (z - y)).comp (transL1 (y - x)) = transL1 (z - x) := by
  refine ContinuousLinearMap.ext fun f => ?_
  rw [ContinuousLinearMap.comp_apply, transL1_add, show z - y + (y - x) = z - x by ring]

/-- **(A7) for `delayCore`.** `(x,y) ↦ τ_{y-x} f` is continuous everywhere: `continuous_transL1`
composed with the continuous map `(x,y) ↦ y - x`. -/
theorem delayCore_continuous (f : X) :
    ContinuousOn (fun p : ℝ × ℝ => transL1 (p.2 - p.1) f) {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2} :=
  ((continuous_transL1 f).comp (continuous_snd.sub continuous_fst)).continuousOn

/-- The box does not agree a.e. with its own shift by `r > 0`: on `(0, min(r,1))`, which has
positive measure, the box is `1` and the shift is `0`. The fact behind (ND) for `delayCore`. -/
theorem box_ne_ae_shift {r : ℝ} (hr : 0 < r) :
    ¬ ((box : ℝ → ℝ) =ᵐ[volume] fun t => box (t - r)) := by
  intro hae
  have hSpos : 0 < volume (Ioo (0 : ℝ) (min r 1)) := by
    rw [Real.volume_Ioo, sub_zero]
    exact ENNReal.ofReal_pos.mpr (lt_min hr one_pos)
  have hSsub : Ioo (0 : ℝ) (min r 1) ⊆ {t | box t ≠ box (t - r)} := by
    intro t ht
    have ht1 : t ∈ Ioo (0 : ℝ) 1 := ⟨ht.1, ht.2.trans_le (min_le_right r 1)⟩
    have ht2 : t - r < 0 := by linarith [ht.2.trans_le (min_le_left r 1)]
    have hb1 : box t = 1 := indicator_of_mem ht1 _
    have hb0 : box (t - r) = 0 :=
      indicator_of_notMem (fun h => absurd h.1 (not_lt.mpr ht2.le)) _
    show box t ≠ box (t - r)
    rw [hb1, hb0]
    norm_num
  have hnull : volume {t : ℝ | box t ≠ box (t - r)} = 0 := ae_iff.mp hae
  exact absurd (hnull ▸ measure_mono hSsub) (not_le.mpr hSpos)

/-- **(ND) for `delayCore`.** `τ_r ≠ \Id` for `r > 0`, witnessed by the box. -/
theorem transL1_ne_id {r : ℝ} (hr : 0 < r) : transL1 r ≠ ContinuousLinearMap.id ℝ X := by
  intro h
  have h2 : transL1 r boxL1 = boxL1 := by rw [h, ContinuousLinearMap.id_apply]
  have h1 : (transL1 r boxL1 : ℝ → ℝ) =ᵐ[volume] fun t => (boxL1 : ℝ → ℝ) (t - r) :=
    coeFn_transL1 r boxL1
  rw [h2] at h1
  exact box_ne_ae_shift hr
    (coeFn_boxL1.symm.trans (h1.trans
      ((measurePreserving_sub_const r).quasiMeasurePreserving.ae coeFn_boxL1)))

/-- **The pure-delay core**: `Φ_{x,y} = τ_{y-x}`. Every field is a fact about `transL1` proved
above, none of them going through a kernel. -/
noncomputable def delayCore : CascadeCore where
  Φ x y := transL1 (y - x)
  translation x y _ _ a f := delayCore_translation x y a f
  causal x y hx hxy t₀ f hf := vanishesBefore_transL1 (by linarith) hf
  positive x y _ _ f hf := isNonneg_transL1 (y - x) hf
  unit_area x y _ _ f _ := integral_transL1 (y - x) f
  refl x _ := ContinuousLinearMap.ext fun f => by
    rw [ContinuousLinearMap.id_apply, sub_self, transL1_zero]
  cascade x y z _ _ _ := delayCore_cascade x y z
  continuous f := delayCore_continuous f
  nondegenerate x y _ hxy := transL1_ne_id (by linarith)

/-- **The intertwining of `dilL1` and `transL1`**: `D_σ τ_r = τ_{σr} D_σ`. Pointwise this is
`σ⁻¹ f(σ⁻¹(t - σr)) = σ⁻¹ f(σ⁻¹t - r)`, then lifted to `L¹` along the two isometries. -/
theorem dilL1_comp_transL1 {σ : ℝ} (hσ : 0 < σ) (r : ℝ) (f : X) :
    dilL1 hσ (transL1 r f) = transL1 (σ * r) (dilL1 hσ f) := by
  refine Lp.ext ?_
  have h1 : (dilL1 hσ (transL1 r f) : ℝ → ℝ) =ᵐ[volume] dilate σ (transL1 r f : ℝ → ℝ) :=
    coeFn_dilL1 hσ (transL1 r f)
  have h2 : dilate σ (transL1 r f : ℝ → ℝ) =ᵐ[volume] dilate σ (fun t => (f : ℝ → ℝ) (t - r)) :=
    dilate_congr_ae hσ.ne' (coeFn_transL1 r f)
  have h3 : dilate σ (fun t => (f : ℝ → ℝ) (t - r))
      = fun t => (dilate σ (f : ℝ → ℝ)) (t - σ * r) := by
    funext t
    have harg : σ⁻¹ * t - r = σ⁻¹ * (t - σ * r) := by
      rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hσ.ne', one_mul]
    simp only [dilate, harg]
  have h4 : (fun t => (dilate σ (f : ℝ → ℝ)) (t - σ * r))
      =ᵐ[volume] fun t => (dilL1 hσ f : ℝ → ℝ) (t - σ * r) :=
    (measurePreserving_sub_const (σ * r)).quasiMeasurePreserving.ae (coeFn_dilL1 hσ f).symm
  have h5 : (fun t => (dilL1 hσ f : ℝ → ℝ) (t - σ * r))
      =ᵐ[volume] (transL1 (σ * r) (dilL1 hσ f) : ℝ → ℝ) :=
    (coeFn_transL1 (σ * r) (dilL1 hσ f)).symm
  rw [h3] at h2
  exact h1.trans (h2.trans (h4.trans h5))

/-- **`witness_main_characterization_delayCore`.** `delayCore` is scale-covariant at the
multiplicative action — the (⇒) hypotheses of `main_characterization`, jointly satisfiable at a
model resting on Lean core alone. -/
theorem witness_main_characterization_delayCore :
    IsScaleCovariant delayCore (Ioi 0) (fun σ x => σ * x) where
  S_mapsTo σ hσ _ x hx := by simpa using mul_nonneg hσ.le hx
  S_strictMonoOn σ hσ _ x _ y _ hxy := by simpa using mul_lt_mul_of_pos_left hxy hσ
  S_surjOn σ hσ _ x hx := ⟨σ⁻¹ * x, by
      simp only [mem_Ici] at hx ⊢
      exact mul_nonneg (inv_nonneg.mpr hσ.le) hx, by field_simp⟩
  scale σ hσ _ x y _ _ := by
    show (dilL1 hσ).comp (transL1 (y - x)) = (transL1 (σ * y - σ * x)).comp (dilL1 hσ)
    rw [show σ * y - σ * x = σ * (y - x) by ring]
    exact ContinuousLinearMap.ext fun f => dilL1_comp_transL1 hσ (y - x) f

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

(ND), covariance, and — the density-free route the plan records — (H): every negative moment of
`T₁` is finite, so `z_* = ∞`, so (H) holds outright. The moment cannot be read off the exponent
`s^α` through a closed form for the stable density (the development has none), but it can be read
off the exponent through its *Laplace transform*, which is exactly `s^α`: the hinge
`lintegral_lintegral_gamma_of_ae_mem_Ioi` turns `E[T₁^{-ζ}]` into an outer integral over `t`
against `lawT₁`, and swapping it (`lintegral_lintegral_swap`) into an outer integral over `s`
against Lebesgue measure lands on `∫₀^∞ s^{ζ-1}e^{-s^α}ds`, finite by the Gamma-integral formula
`integral_rpow_mul_exp_neg_rpow` for every `ζ > 0` and every `α ∈ (0,1)` — no closed form for the
law is needed, only for its transform, which is the exponent itself. -/

variable {α : ℝ}

/-- (ND) at stable: `F(1) = 1`. -/
theorem witness_hF_stable (hα : 0 < α) (hα1 : α < 1) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ (stableExponent α hα hα1).exponent s₀ ≠ 0 :=
  ⟨1, zero_lt_one, exponent_ne_zero_of_toRealExponent_ne_zero (by
    rw [stableExponent_toRealExponent hα hα1 zero_lt_one, Real.one_rpow]; exact one_ne_zero)⟩

/-- **`F(∞) = ∞` at stable.** `toRealExponent s = s^α → ∞` as `s → ∞`, since `α > 0`. -/
theorem stableExponent_tendsto (hα : 0 < α) (hα1 : α < 1) :
    Tendsto (stableExponent α hα hα1).toRealExponent atTop atTop := by
  refine (tendsto_rpow_atTop hα).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  exact (stableExponent_toRealExponent hα hα1 hs).symm

/-- **`s^{ζ-1}e^{-s^α}` is integrable on `(0,∞)`, for every `ζ, α > 0`.**

Mathlib's own Gamma-integral formula (`integral_rpow_mul_exp_neg_rpow`) needs no restriction
`α ≥ 1`, unlike the paired `IntegrableOn` lemma in the same file — and integrability follows from
the formula itself: the Bochner integral of a non-integrable function is `0` by convention, and
the formula's right side, `Γ(ζ/α)/α`, is not. -/
theorem integrableOn_rpow_mul_exp_neg_rpow_of_pos {ζ α : ℝ} (hα : 0 < α) (hζ : 0 < ζ) :
    IntegrableOn (fun s : ℝ => s ^ (ζ - 1) * Real.exp (-(s ^ α))) (Ioi 0) := by
  by_contra hni
  have heq := integral_rpow_mul_exp_neg_rpow hα (show (-1 : ℝ) < ζ - 1 by linarith)
  rw [integral_undef hni] at heq
  have hΓpos : (0 : ℝ) < 1 / α * Real.Gamma ((ζ - 1 + 1) / α) := by
    have h1 : (0 : ℝ) < (ζ - 1 + 1) / α := by
      rw [show ζ - 1 + 1 = ζ by ring]; positivity
    exact mul_pos (by positivity) (Real.Gamma_pos_of_pos h1)
  linarith

/-- **Every negative moment of the stable law is finite** (the plan's density-free route): the
Tonelli hinge `lintegral_lintegral_gamma_of_ae_mem_Ioi` reads `Γ(ζ) · E[T₁^{-ζ}]` as the double
integral `∫∫ s^{ζ-1}e^{-ts} ds dlawT₁(t)`; swapping the order of integration
(`lintegral_lintegral_swap`) and evaluating the inner `t`-integral pointwise as the Laplace
transform (`laplaceL_lawT₁`, which *is* `e^{-s^α}` here) turns it into
`∫₀^∞ s^{ζ-1}e^{-s^α} ds`, finite by `integrableOn_rpow_mul_exp_neg_rpow_of_pos`. -/
theorem stableExponent_negMoment_ne_top (hα : 0 < α) (hα1 : α < 1) {ζ : ℝ} (hζ : 0 < ζ) :
    (stableExponent α hα hα1).negMoment ζ ≠ ⊤ := by
  have h0 : (stableExponent α hα hα1).lawT₁ {(0 : ℝ)} = 0 :=
    (stableExponent α hα hα1).lawT₁_singleton_zero (stableExponent_tendsto hα hα1)
  have hν : ∀ᵐ t ∂(stableExponent α hα hα1).lawT₁, t ∈ Ioi (0 : ℝ) :=
    (stableExponent α hα hα1).ae_mem_Ioi_lawT₁ h0
  have hmeas : Measurable (Function.uncurry fun t s : ℝ =>
      ENNReal.ofReal (s ^ (ζ - 1) * Real.exp (-(t * s)))) := by fun_prop
  have hswap := lintegral_lintegral_swap
    (μ := (stableExponent α hα hα1).lawT₁) (ν := volume.restrict (Ioi (0 : ℝ)))
    hmeas.aemeasurable
  have hhinge := lintegral_lintegral_gamma_of_ae_mem_Ioi hν hζ
  have hinner : ∀ s ∈ Ioi (0 : ℝ),
      (∫⁻ t, ENNReal.ofReal (s ^ (ζ - 1) * Real.exp (-(t * s)))
        ∂(stableExponent α hα hα1).lawT₁)
        = ENNReal.ofReal (s ^ (ζ - 1) * Real.exp (-(s ^ α))) := by
    intro s hs
    have hs' : (0 : ℝ) < s := hs
    have hcongr : (fun t : ℝ => ENNReal.ofReal (s ^ (ζ - 1) * Real.exp (-(t * s))))
        = fun t : ℝ => ENNReal.ofReal (s ^ (ζ - 1)) * ENNReal.ofReal (Real.exp (-(s * t))) := by
      funext t
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hs'.le _), show t * s = s * t from mul_comm t s]
    rw [hcongr, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    show ENNReal.ofReal (s ^ (ζ - 1)) * laplaceL (stableExponent α hα hα1).lawT₁ s = _
    rw [(stableExponent α hα hα1).laplaceL_lawT₁ hs'.le, stableExponent_toRealExponent hα hα1 hs',
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hs'.le _)]
  have hswap' : (∫⁻ s in Ioi (0 : ℝ), ∫⁻ t,
        ENNReal.ofReal (s ^ (ζ - 1) * Real.exp (-(t * s))) ∂(stableExponent α hα hα1).lawT₁)
      = ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (ζ - 1) * Real.exp (-(s ^ α))) :=
    setLIntegral_congr_fun measurableSet_Ioi hinner
  have hfin : (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (ζ - 1) * Real.exp (-(s ^ α)))) ≠ ⊤ :=
    lintegral_ofReal_ne_top_of_integrableOn (integrableOn_rpow_mul_exp_neg_rpow_of_pos hα hζ)
  rw [← hswap', ← hswap, hhinge, ← (stableExponent α hα hα1).negMoment_eq_lintegral h0] at hfin
  intro hcontra
  exact hfin (by
    rw [hcontra, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (Real.Gamma_pos_of_pos hζ)).ne'])

/-- **`AllNegMomentsFinite` at stable** (ledger A13's conclusion, for free): every negative
moment, not only one past `1`. -/
theorem stableExponent_allNegMomentsFinite (hα : 0 < α) (hα1 : α < 1) :
    (stableExponent α hα hα1).AllNegMomentsFinite := fun _ζ hζ =>
  stableExponent_negMoment_ne_top hα hα1 hζ

/-- **(H) at stable, for every `α ∈ (0,1)`.** `z_* = ∞`, exactly as at drift. -/
theorem witness_standingHypothesis_stable (hα : 0 < α) (hα1 : α < 1) :
    (stableExponent α hα hα1).StandingHypothesis :=
  ⟨stableExponent_tendsto hα hα1,
   by rw [(stableExponent α hα hα1).zStar_eq_top (stableExponent_allNegMomentsFinite hα hα1)]
      exact ENNReal.one_lt_top⟩

/-- **`signaling_form` at stable**: (H), (ND), any `c > 0` (since `z_* = ∞`), and the tent. -/
theorem witness_signaling_form_stable (hα : 0 < α) (hα1 : α < 1) {c : ℝ} (hc : 0 < c) :
    (stableExponent α hα hα1).StandingHypothesis ∧
    (∃ s₀ : ℝ, 0 < s₀ ∧ (stableExponent α hα hα1).exponent s₀ ≠ 0) ∧
    0 < c ∧ ENNReal.ofReal (c + 1) < (stableExponent α hα hα1).zStar ∧
    Measurable tentDeriv ∧ Integrable tentDeriv ∧ (∀ r : ℝ, r < 0 → tentDeriv r = 0) ∧
    Measurable tent ∧ Integrable tent ∧
    (∀ r : ℝ, tent r = ∫ ρ in Ioc (0 : ℝ) r, tentDeriv ρ) :=
  ⟨witness_standingHypothesis_stable hα hα1, witness_hF_stable hα hα1, hc,
   (stableExponent α hα hα1).ofReal_lt_zStar_of_all (stableExponent_allNegMomentsFinite hα hα1) _,
   signal_hypotheses⟩

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
