/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Hemigroup.LevyTriple

/-!
# Chapter 6: covariance in the transform, and the rigidity of the action

Blueprint: `blueprint/src/parts/06-covariance.tex`.

(A8) is an identity between operators. `lem:covariance-laplace` turns it into an identity between
*measures*, and then into the single scalar identity `(6.1)`

  `G(S_σ x, s) = G(x, σ s)`

that everything else in the chapter runs on. Once that is available the action is pinned down by
order arguments alone: `G(\cdot, s)` is strictly increasing by `cor:strict-monotonicity`, hence
injective, and injectivity is what makes `(6.1)` *determine* `S_σ` rather than merely constrain
it.

## Why the operator identity becomes a measure identity

Dilation is invertible on `L¹` — `D_{σ^{-1}}` undoes it, the `σ^{-1}` normalisation and the
Jacobian cancelling exactly — so `D_σ` can be cancelled from the right of (A8). What is left is
an identity between convolution operators, and the uniqueness clause of
`lem:convolution-representation` (`mconvL1_injective`) makes it an identity between the measures.
From there the transform is arithmetic: `laplace_map_const_mul` says dilating a measure
reparametrises its transform, and `-\log` of that is `(6.1)`.

## What is here and what is not

`lem:covariance-laplace` and all four clauses of `lem:action-rigidity` are proved here, clause
(3) — continuity of `σ ↦ S_σ x` — included (`continuousOn_S_apply`); `prop:canonical-gauge`
lives in `Gauge.lean`. (`covariance_laplace` states the (A8) ⇒ transform-identity direction of
the blueprint's equivalence; the converse is `dilL1_comp_mconvL1` with `mconvL1_congr`, used as
such by `Instance.lean` — fidelity review R18.)
-/

namespace Hemigroup

open MeasureTheory Set Filter
open scoped Topology

/-! ## Dilation is invertible on `L¹`

Needed to cancel `D_σ` from the right of (A8). Nothing subtle: `D_{σ^{-1}}` is a two-sided
inverse, which the definition `D_σ f(t) = σ^{-1} f(σ^{-1} t)` gives after one `field_simp`.
-/

/-- `D_σ D_{σ^{-1}} = \Id`: dilation is surjective, with an explicit right inverse. -/
theorem dilL1_dilL1_inv {σ : ℝ} (hσ : 0 < σ) (f : X) :
    dilL1 hσ (dilL1 (inv_pos.mpr hσ) f) = f := by
  refine Lp.ext ?_
  refine (coeFn_dilL1 hσ _).trans ?_
  refine (dilate_congr_ae hσ.ne' (coeFn_dilL1 (inv_pos.mpr hσ) f)).trans ?_
  filter_upwards with t
  simp only [dilate, inv_inv]
  field_simp

theorem dilL1_surjective {σ : ℝ} (hσ : 0 < σ) : Function.Surjective (dilL1 hσ) :=
  fun f => ⟨dilL1 (inv_pos.mpr hσ) f, dilL1_dilL1_inv hσ f⟩

/-- Two operators agreeing after precomposition with a dilation agree. -/
theorem eq_of_comp_dilL1 {σ : ℝ} (hσ : 0 < σ) {A B : X →L[ℝ] X}
    (h : A.comp (dilL1 hσ) = B.comp (dilL1 hσ)) : A = B := by
  refine ContinuousLinearMap.ext fun f => ?_
  obtain ⟨g, rfl⟩ := dilL1_surjective hσ f
  exact congrArg (fun T : X →L[ℝ] X => T g) h

/-! ## The transform is strictly decreasing in `s`

Needed for clause (3), and not available from anything proved so far: `cor:strict-monotonicity`
is monotonicity in the *scale*, this is monotonicity in the transform variable. The blueprint
reads it off the derivative of a Bernstein function; here it is one line of measure theory, and
no Bernstein vocabulary is involved.
-/

/-- A causal probability measure carried by the origin *is* the point mass there. Proved through
the transform rather than by hand: both sides have transform `1`. -/
theorem eq_dirac_zero_of_ae_eq_zero {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsCausal μ)
    (h : ∀ᵐ t ∂μ, t = 0) : μ = Measure.dirac 0 :=
  laplace_injective hμ (isCausal_dirac le_rfl) fun s _ => by
    have hcongr : ∫ t, Real.exp (-(s * t)) ∂μ = ∫ _t : ℝ, (1 : ℝ) ∂μ :=
      integral_congr_ae (h.mono fun t ht => by simp [ht])
    rw [laplace_dirac_zero, laplace, hcongr]
    simp

/-- **The Laplace transform of a causal probability measure other than `δ_0` is strictly
decreasing.** The support of `e^{-st} - e^{-s't}` is exactly `t \ne 0`, and that set carries
positive mass precisely because the measure is not the point mass. -/
theorem laplace_strictAnti {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsCausal μ)
    (hne : μ ≠ Measure.dirac 0) {s s' : ℝ} (hs : 0 ≤ s) (hss : s < s') :
    laplace μ s' < laplace μ s := by
  have hs' : 0 ≤ s' := hs.trans hss.le
  have hsupp : 0 < μ {t : ℝ | t ≠ 0} := by
    rcases eq_zero_or_pos (μ {t : ℝ | t ≠ 0}) with h | h
    · exact absurd (eq_dirac_zero_of_ae_eq_zero hμ (ae_iff.mpr h)) hne
    · exact h
  have hnn : 0 ≤ᵐ[μ] fun t => Real.exp (-(s * t)) - Real.exp (-(s' * t)) := by
    filter_upwards [hμ.ae_nonneg] with t ht
    simp only [Pi.zero_apply, sub_nonneg]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hint : Integrable (fun t => Real.exp (-(s * t)) - Real.exp (-(s' * t))) μ :=
    (integrable_exp_of_causal hμ hs).sub (integrable_exp_of_causal hμ hs')
  have hsupport :
      Function.support (fun t => Real.exp (-(s * t)) - Real.exp (-(s' * t))) = {t : ℝ | t ≠ 0} := by
    ext t
    simp only [Function.mem_support, ne_eq, sub_eq_zero, Real.exp_eq_exp, neg_inj, mem_setOf_eq]
    constructor
    · exact fun h hzero => h (by rw [hzero, mul_zero, mul_zero])
    · exact fun h heq => h (by
        have : (s - s') * t = 0 := by linarith [heq]
        rcases mul_eq_zero.mp this with hc | hc
        · exact absurd (by linarith : s = s') (ne_of_lt hss)
        · exact hc)
  rw [laplace, laplace, ← sub_pos,
    ← integral_sub (integrable_exp_of_causal hμ hs) (integrable_exp_of_causal hμ hs')]
  exact (integral_pos_iff_support_of_nonneg_ae hnn hint).mpr (by rw [hsupport]; exact hsupp)

namespace CascadeCore

variable {Fam : CascadeCore} {Gs : Set ℝ} {S : ℝ → ℝ → ℝ} {x y : ℝ}

/-- **The exponent is strictly increasing in `s`** on a nondegenerate increment. -/
theorem exponent_strictMonoOn_right (Fam : CascadeCore) {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    StrictMonoOn (fun s => Fam.exponent x y s) (Ici 0) := by
  intro a ha b _ hab
  have hne := repr_ne_dirac (Fam := Fam) hx hxy
  have hlt := laplace_strictAnti (isCausal_repr Fam x y) hne (mem_Ici.mp ha) hab
  have hpb := laplace_pos_of_prob (isCausal_repr Fam x y) ((mem_Ici.mp ha).trans hab.le)
  simp only [exponent, neg_lt_neg_iff]
  exact Real.log_lt_log hpb hlt

/-- The same for `G(x, \cdot)`, `x > 0`. -/
theorem G_strictMonoOn_right (Fam : CascadeCore) {x : ℝ} (hx : 0 < x) :
    StrictMonoOn (fun s => Fam.G x s) (Ici 0) :=
  exponent_strictMonoOn_right Fam le_rfl hx

/-! ## `lem:covariance-laplace`

Stated for an arbitrary set `Gs` of admissible factors, because each clause is a statement about
one `σ`: nothing here needs the group structure, and the companion note's strata reuse it
verbatim.
-/

/-- The action is monotone where it is defined. -/
theorem monotoneOn_S (hcov : IsScaleCovariant Fam Gs S) {σ : ℝ} (hσ : 0 < σ) (hmem : σ ∈ Gs) :
    MonotoneOn (S σ) (Ici 0) :=
  (hcov.S_strictMonoOn σ hσ hmem).monotoneOn

/-- **An increasing bijection of `[0,∞)` fixes the origin.** Used constantly below, and the
reason `(6.1)` is a statement about `G = g_{0,\cdot}` at all. -/
theorem S_zero (hcov : IsScaleCovariant Fam Gs S) {σ : ℝ} (hσ : 0 < σ) (hmem : σ ∈ Gs) :
    S σ 0 = 0 := by
  obtain ⟨a, ha, hSa⟩ := hcov.S_surjOn σ hσ hmem (mem_Ici.mpr le_rfl)
  have h0 : 0 ≤ S σ 0 := hcov.S_mapsTo σ hσ hmem (mem_Ici.mpr le_rfl)
  rcases eq_or_lt_of_le (mem_Ici.mp ha) with rfl | hpos
  · exact hSa
  · exact absurd (hSa ▸ hcov.S_strictMonoOn σ hσ hmem (mem_Ici.mpr le_rfl) ha hpos)
      (not_lt.mpr h0)

/-- **(A8) at the level of measures.** The dilated kernel *is* the kernel at the dilated scales
— an identity of measures, not merely of the operators they induce. -/
theorem repr_map_const_mul (hcov : IsScaleCovariant Fam Gs S) {σ : ℝ} (hσ : 0 < σ) (hmem : σ ∈ Gs)
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    (Fam.repr x y).map (fun t => σ * t) = Fam.repr (S σ x) (S σ y) := by
  have hSx : 0 ≤ S σ x := hcov.S_mapsTo σ hσ hmem (mem_Ici.mpr hx)
  have hSxy : S σ x ≤ S σ y :=
    monotoneOn_S hcov hσ hmem (mem_Ici.mpr hx) (mem_Ici.mpr (hx.trans hxy)) hxy
  haveI : IsProbabilityMeasure ((Fam.repr x y).map (fun t => σ * t)) :=
    Measure.isProbabilityMeasure_map (measurable_const_mul σ).aemeasurable
  -- Cancel the dilation from the right of (A8), then apply the uniqueness clause.
  have hscale := hcov.scale σ hσ hmem x y hx hxy
  rw [Phi_eq_mconvL1_repr hx hxy, Phi_eq_mconvL1_repr hSx hSxy,
    dilL1_comp_mconvL1 hσ (Fam.repr x y)] at hscale
  refine mconvL1_injective ((isCausal_repr Fam x y).map_const_mul hσ)
    (isCausal_repr Fam (S σ x) (S σ y)) (eq_of_comp_dilL1 hσ hscale)

/-- **`(6.1)` for the two-parameter exponent**: dilating the scales reparametrises `s`. -/
theorem exponent_scale (hcov : IsScaleCovariant Fam Gs S) {σ : ℝ} (hσ : 0 < σ) (hmem : σ ∈ Gs)
    (hx : 0 ≤ x) (hxy : x ≤ y) (s : ℝ) :
    Fam.exponent (S σ x) (S σ y) s = Fam.exponent x y (σ * s) := by
  rw [exponent, exponent, ← repr_map_const_mul hcov hσ hmem hx hxy,
    laplace_map_const_mul _ hσ]

/-- **`(6.1)`.** `G(S_σ x, s) = G(x, σ s)`, the identity the rest of the chapter runs on. -/
theorem G_scale (hcov : IsScaleCovariant Fam Gs S) {σ : ℝ} (hσ : 0 < σ) (hmem : σ ∈ Gs)
    (hx : 0 ≤ x) (s : ℝ) : Fam.G (S σ x) s = Fam.G x (σ * s) := by
  have h := exponent_scale hcov hσ hmem (le_refl (0 : ℝ)) hx s
  rw [S_zero hcov hσ hmem] at h
  exact h

/-- **`lem:covariance-laplace`.** (A8) as an identity of measures, of exponents, and of `G`. -/
theorem covariance_laplace (hcov : IsScaleCovariant Fam Gs S) :
    (∀ σ : ℝ, 0 < σ → σ ∈ Gs → ∀ x y : ℝ, 0 ≤ x → x ≤ y →
        (Fam.repr x y).map (fun t => σ * t) = Fam.repr (S σ x) (S σ y)) ∧
      (∀ σ : ℝ, 0 < σ → σ ∈ Gs → ∀ x y s : ℝ, 0 ≤ x → x ≤ y →
        Fam.exponent (S σ x) (S σ y) s = Fam.exponent x y (σ * s)) ∧
      (∀ σ : ℝ, 0 < σ → σ ∈ Gs → ∀ x s : ℝ, 0 ≤ x → Fam.G (S σ x) s = Fam.G x (σ * s)) :=
  ⟨fun _ hσ hmem _ _ hx hxy => repr_map_const_mul hcov hσ hmem hx hxy,
    fun _ hσ hmem _ _ _ hx hxy => exponent_scale hcov hσ hmem hx hxy _,
    fun _ hσ hmem _ _ hx => G_scale hcov hσ hmem hx _⟩

/-- **The converse of `lem:covariance-laplace`'s measure identity.** Given the `S`-shape fields of
`IsScaleCovariant` and, for `σ ∈ Gs`, `σ > 0`, `0 ≤ x ≤ y`, the measure identity
`(Fam.repr x y).map (σ ·) = Fam.repr (S σ x) (S σ y)`, (A8) follows: cancel the dilation from the
kernel factorisation `Φ = mconvL1 ∘ repr` (`Phi_eq_mconvL1_repr`), push it through
`dilL1_comp_mconvL1`, and rewrite the dilated measure by hypothesis (`mconvL1_congr`) — the same
three lemmas `Instance.lean:221–225` uses for the multiplicative witness. This is Lemma 6.1's
"is equivalent to" direction not carried by `covariance_laplace` (fidelity review R18). -/
theorem isScaleCovariant_of_repr_map
    (hmapsTo : ∀ σ, 0 < σ → σ ∈ Gs → MapsTo (S σ) (Ici 0) (Ici 0))
    (hmono : ∀ σ, 0 < σ → σ ∈ Gs → StrictMonoOn (S σ) (Ici 0))
    (hsurj : ∀ σ, 0 < σ → σ ∈ Gs → SurjOn (S σ) (Ici 0) (Ici 0))
    (hid : ∀ σ : ℝ, 0 < σ → σ ∈ Gs → ∀ x y : ℝ, 0 ≤ x → x ≤ y →
        (Fam.repr x y).map (fun t => σ * t) = Fam.repr (S σ x) (S σ y)) :
    IsScaleCovariant Fam Gs S where
  S_mapsTo := hmapsTo
  S_strictMonoOn := hmono
  S_surjOn := hsurj
  scale := fun σ hσ hmem x y hx hxy => by
    have hSx : 0 ≤ S σ x := hmapsTo σ hσ hmem (mem_Ici.mpr hx)
    have hSxy : S σ x ≤ S σ y :=
      (hmono σ hσ hmem).monotoneOn (mem_Ici.mpr hx) (mem_Ici.mpr (hx.trans hxy)) hxy
    haveI : IsProbabilityMeasure ((Fam.repr x y).map (fun t => σ * t)) :=
      Measure.isProbabilityMeasure_map (measurable_const_mul σ).aemeasurable
    rw [Phi_eq_mconvL1_repr hx hxy, Phi_eq_mconvL1_repr hSx hSxy,
      dilL1_comp_mconvL1 hσ (Fam.repr x y), mconvL1_congr (hid σ hσ hmem x y hx hxy)]

/-! ## `lem:action-rigidity`, the order clauses

`G(\cdot, s)` is strictly increasing (`cor:strict-monotonicity`), hence injective on `[0,∞)`,
and that single fact carries clauses (1), (2) and (4).
-/

/-- **(1) The action is determined by `(6.1)`.** Injectivity of `G(\cdot, s)`, which is
`cor:strict-monotonicity` read as a statement about equality. -/
theorem eq_of_G_eq (Fam : CascadeCore) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {s : ℝ} (hs : 0 < s)
    (h : Fam.G a s = Fam.G b s) : a = b :=
  (G_strictMonoOn Fam hs).injOn (mem_Ici.mpr ha) (mem_Ici.mpr hb) h

/-- **(2) The group law.** `S_σ S_τ = S_{στ}`, from `(6.1)` applied twice. -/
theorem S_comp (hcov : IsScaleCovariant Fam Gs S) {σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ)
    (hσm : σ ∈ Gs) (hτm : τ ∈ Gs) (hστ : σ * τ ∈ Gs) (hx : 0 ≤ x) :
    S σ (S τ x) = S (σ * τ) x := by
  have hτx : 0 ≤ S τ x := hcov.S_mapsTo τ hτ hτm (mem_Ici.mpr hx)
  refine eq_of_G_eq Fam (hcov.S_mapsTo σ hσ hσm (mem_Ici.mpr hτx))
    (hcov.S_mapsTo (σ * τ) (mul_pos hσ hτ) hστ (mem_Ici.mpr hx)) one_pos ?_
  rw [G_scale hcov hσ hσm hτx, G_scale hcov hτ hτm hx,
    G_scale hcov (mul_pos hσ hτ) hστ hx]
  ring_nf

/-- **(2) The unit.** `S_1 = \Id` on `[0,∞)`. -/
theorem S_one (hcov : IsScaleCovariant Fam Gs S) (hmem : (1 : ℝ) ∈ Gs) (hx : 0 ≤ x) :
    S 1 x = x := by
  refine eq_of_G_eq Fam (hcov.S_mapsTo 1 one_pos hmem (mem_Ici.mpr hx)) hx one_pos ?_
  rw [G_scale hcov one_pos hmem hx, one_mul]

/-! ### Clause (3): the orbit map

The blueprint composes `G(\cdot, s_0)^{-1}` with `σ ↦ G(x, σ s_0)`. Lean does not need the
inverse function: `StrictMonoOn.continuousAt_of_exists_between` asks only for orbit points
squeezed between a given bound and `S_{σ_0} x`, and those come from continuity of
`σ ↦ G(x, σ)` at `σ_0` together with the fact that `G(\cdot, 1)` reflects order. Avoiding
`Set.invFunOn` also avoids having to prove its range is a neighbourhood, which is the step the
blueprint's phrase "on its range" hides.
-/

/-- The action preserves strict positivity — it fixes the origin and is strictly increasing. -/
theorem S_pos (hcov : IsScaleCovariant Fam Gs S) {σ : ℝ} (hσ : 0 < σ) (hmem : σ ∈ Gs)
    (hx : 0 < x) : 0 < S σ x := by
  rw [← S_zero hcov hσ hmem]
  exact hcov.S_strictMonoOn σ hσ hmem (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx.le) hx

/-- **(3), the monotone half.** `σ ↦ S_σ x` is strictly increasing: `(6.1)` turns it into strict
monotonicity of `G(x, \cdot)`, and `G(\cdot, 1)` reflects the order back. -/
theorem strictMonoOn_S_apply (hcov : IsScaleCovariant Fam (Ioi 0) S) {x : ℝ} (hx : 0 < x) :
    StrictMonoOn (fun σ => S σ x) (Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := mem_Ioi.mp ha
  have hb' : (0 : ℝ) < b := mem_Ioi.mp hb
  refine ((G_strictMonoOn Fam one_pos).lt_iff_lt
    (mem_Ici.mpr (hcov.S_mapsTo a ha' ha (mem_Ici.mpr hx.le)))
    (mem_Ici.mpr (hcov.S_mapsTo b hb' hb (mem_Ici.mpr hx.le)))).mp ?_
  rw [G_scale hcov ha' ha hx.le, G_scale hcov hb' hb hx.le]
  exact G_strictMonoOn_right Fam hx (mem_Ici.mpr (by positivity)) (mem_Ici.mpr (by positivity))
    (by nlinarith)

/-- **(3), the continuity half.** -/
theorem continuousOn_S_apply (hcov : IsScaleCovariant Fam (Ioi 0) S) {x : ℝ} (hx : 0 < x) :
    ContinuousOn (fun σ => S σ x) (Ioi 0) := by
  intro σ₀ hσ₀
  refine ContinuousAt.continuousWithinAt ?_
  have hσ₀' : (0 : ℝ) < σ₀ := mem_Ioi.mp hσ₀
  have humono : StrictMonoOn (fun z => Fam.G z 1) (Ici 0) := G_strictMonoOn Fam one_pos
  have hSmem : ∀ σ : ℝ, 0 < σ → S σ x ∈ Ici (0 : ℝ) := fun σ hσ =>
    mem_Ici.mpr (hcov.S_mapsTo σ hσ (mem_Ioi.mpr hσ) (mem_Ici.mpr hx.le))
  -- `(6.1)` at `s = 1`: the orbit is the graph of `G(x, \cdot)` seen through `G(\cdot, 1)`.
  have hkey : ∀ σ : ℝ, 0 < σ → Fam.G (S σ x) 1 = Fam.G x σ := fun σ hσ => by
    have h := G_scale hcov hσ (mem_Ioi.mpr hσ) hx.le 1
    rwa [mul_one] at h
  have hwcont : ContinuousAt (fun σ => Fam.G x σ) σ₀ :=
    (continuousOn_G_right Fam x).continuousAt (Ici_mem_nhds hσ₀')
  have hSσ₀ : (0 : ℝ) < S σ₀ x := S_pos hcov hσ₀' hσ₀ hx
  refine (strictMonoOn_S_apply hcov hx).continuousAt_of_exists_between
    (Ioi_mem_nhds hσ₀') ?_ ?_
  · -- Approach from below.
    intro b hb
    have hb'mem : max b 0 ∈ Ici (0 : ℝ) := mem_Ici.mpr (le_max_right _ _)
    have hub : Fam.G (max b 0) 1 < Fam.G x σ₀ := by
      rw [← hkey σ₀ hσ₀']
      exact humono hb'mem (hSmem σ₀ hσ₀') (max_lt hb hSσ₀)
    have hev : ∀ᶠ c in 𝓝[<] σ₀, Fam.G (max b 0) 1 < Fam.G x c :=
      (hwcont.mono_left nhdsWithin_le_nhds) (Ioi_mem_nhds hub)
    obtain ⟨c, hcw, hcmem⟩ := (hev.and (Ioo_mem_nhdsLT hσ₀')).exists
    have hc0 : (0 : ℝ) < c := hcmem.1
    refine ⟨c, mem_Ioi.mpr hc0, ?_, ?_⟩
    · rw [← hkey c hc0] at hcw
      exact le_of_lt ((le_max_left b 0).trans_lt (humono.lt_iff_lt hb'mem (hSmem c hc0) |>.mp hcw))
    · exact strictMonoOn_S_apply hcov hx (mem_Ioi.mpr hc0) hσ₀ hcmem.2
  · -- Approach from above.
    intro b hb
    have hbmem : b ∈ Ici (0 : ℝ) := mem_Ici.mpr (hSσ₀.le.trans hb.le)
    have hub : Fam.G x σ₀ < Fam.G b 1 := by
      rw [← hkey σ₀ hσ₀']
      exact humono (hSmem σ₀ hσ₀') hbmem hb
    have hev : ∀ᶠ c in 𝓝[>] σ₀, Fam.G x c < Fam.G b 1 :=
      (hwcont.mono_left nhdsWithin_le_nhds) (Iio_mem_nhds hub)
    obtain ⟨c, hcw, hcmem⟩ := (hev.and (self_mem_nhdsWithin (a := σ₀) (s := Ioi σ₀))).exists
    have hcσ : σ₀ < c := mem_Ioi.mp hcmem
    have hc0 : (0 : ℝ) < c := hσ₀'.trans hcσ
    refine ⟨c, mem_Ioi.mpr hc0, strictMonoOn_S_apply hcov hx hσ₀ (mem_Ioi.mpr hc0) hcσ, ?_⟩
    rw [← hkey c hc0] at hcw
    exact le_of_lt ((humono.lt_iff_lt (hSmem c hc0) hbmem).mp hcw)

/-- **(4) No fixed point in `(0,∞)`.** A fixed scale would make `G(x^*, \cdot)` constant on
`(0,∞)`; continuity at the origin forces that constant to be `0`, and `cor:strict-monotonicity`
under (ND) forbids it above `x^* = 0`. -/
theorem eq_zero_of_fixed (hcov : IsScaleCovariant Fam (Ioi 0) S) (hx : 0 ≤ x)
    (hfix : ∀ σ : ℝ, 0 < σ → S σ x = x) : x = 0 := by
  by_contra hne
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hne)
  -- `G(x, \cdot)` is constant on `(0,∞)`, by `(6.1)` and the fixed point.
  have hconst : ∀ σ : ℝ, 0 < σ → Fam.G x σ = Fam.G x 1 := by
    intro σ hσ
    have h := G_scale hcov hσ (mem_Ioi.mpr hσ) hx 1
    rw [hfix σ hσ, mul_one] at h
    exact h.symm
  -- Its limit at the origin is `G(x, 0) = 0`.
  have hcont : Tendsto (fun σ : ℝ => Fam.G x σ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc := (continuousOn_G_right Fam x) 0 self_mem_Ici
    rw [ContinuousWithinAt, G_atZero] at hc
    exact hc.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have heq : (fun σ : ℝ => Fam.G x σ) =ᶠ[𝓝[>] (0 : ℝ)] fun _ => Fam.G x 1 := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ using hconst σ (mem_Ioi.mp hσ)
  have hzero : (0 : ℝ) = Fam.G x 1 :=
    tendsto_nhds_unique (Tendsto.congr' heq hcont) tendsto_const_nhds
  -- But it is strictly positive, by (ND).
  exact absurd hzero (ne_of_lt (exponent_pos Fam le_rfl hxpos one_pos))

/-- **`lem:action-rigidity`.** The action is determined by `(6.1)`, is a group action, moves each
positive scale continuously and strictly increasingly, and fixes nothing but the origin. -/
theorem action_rigidity (hcov : IsScaleCovariant Fam (Ioi 0) S) :
    (∀ a b s : ℝ, 0 ≤ a → 0 ≤ b → 0 < s → Fam.G a s = Fam.G b s → a = b) ∧
      (∀ σ τ z : ℝ, 0 < σ → 0 < τ → 0 ≤ z → S σ (S τ z) = S (σ * τ) z) ∧
      (∀ z : ℝ, 0 ≤ z → S 1 z = z) ∧
      (∀ z : ℝ, 0 < z → ContinuousOn (fun σ => S σ z) (Ioi 0) ∧
        StrictMonoOn (fun σ => S σ z) (Ioi 0)) ∧
      (∀ z : ℝ, 0 ≤ z → (∀ σ : ℝ, 0 < σ → S σ z = z) → z = 0) :=
  ⟨fun _ _ _ ha hb hs h => eq_of_G_eq Fam ha hb hs h,
    fun _ _ _ hσ hτ hz => S_comp hcov hσ hτ (mem_Ioi.mpr hσ) (mem_Ioi.mpr hτ)
      (mem_Ioi.mpr (mul_pos hσ hτ)) hz,
    fun _ hz => S_one hcov (mem_Ioi.mpr one_pos) hz,
    fun _ hz => ⟨continuousOn_S_apply hcov hz, strictMonoOn_S_apply hcov hz⟩,
    fun _ hz hfix => eq_zero_of_fixed hcov hz hfix⟩

end CascadeCore

end Hemigroup
