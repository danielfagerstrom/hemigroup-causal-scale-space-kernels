/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.Construction
import Hemigroup.WeakConvergence
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Towards axiom (A7): tightness of the kernel family

Axiom (A7) is continuity of `(a,b) ↦ Φ_{a,b}`, and the blueprint discharges it with the
continuity theorem for Laplace transforms — ledger **A5**. The open question this file exists to
settle is whether A5 has to become a second interface axiom, or whether the pieces are already
available: Mathlib has Prokhorov, and `prop:laplace-continuity`'s own assignment clause in
`AXIOMS.md` says the *tightness* argument is ours and is held `[T]`.

## What this file establishes

**Tightness, in full.** A Markov bound read off the transform,

  `μ(t > T) · (1 - e^{-sT}) ≤ 1 - μ̂(s)`     (`measureReal_Ioi_mul_le`)

made uniform over the kernel family as `μ_{a,b}(t > T) ≤ F(Bs)/(1 - e^{-sT})` for `b ≤ B`
(`kernel_tail_le`); the fact that makes it bite, `F(0+) = 0` (`exists_exponent_lt`), so that `s`
can be chosen to make the numerator as small as wanted; and the whole thing repackaged as
`IsTightMeasureSet` (`isTightMeasureSet_kernel`), the form Prokhorov consumes — with `[0,T]` as
the compact set, since causality kills the left tail outright.

**Convergence of the transforms, in full.** `tendsto_exponent` gives continuity of the exponent
(`r n → ρ` with `r n ≤ R` implies `F(r n) → F(ρ)`, dominated convergence against the integrand
at `R`); `tendsto_increment_toReal` turns that into convergence of the increments, in `ℝ` rather
than `ℝ≥0∞` because truncated subtraction is not continuous; and `tendsto_laplace_kernel`
delivers `μ̂_{u n, v n}(s) → μ̂_{α,β}(s)`.

So the blueprint's claim that the tightness argument is ours is **checked**, not merely asserted.

## Status of A5 (resolved 2026-08-09)

**A5 is not needed.** The continuity theorem, in the probability / transforms-to-measures form
this development uses, is proved in `WeakConvergence.lean` as
`tendsto_integral_of_tendsto_laplace`, on Lean core alone. The route below — Prokhorov and a
subsequence argument — turned out to be unnecessary: pushing forward along `x = e^{-t}` lands
everything on a compact carrier where Weierstrass replaces compactness. `isTightMeasureSet_kernel`
is kept because it is the tightness statement in Mathlib's own vocabulary and is the natural
thing for any other consumer to use, but nothing in this development now depends on Prokhorov.

The route that was *expected* to be needed, recorded because it is the standard one:

* repackage the family as a `Set (ProbabilityMeasure ℝ)` — Prokhorov's
  `isCompact_closure_of_isTightMeasureSet` takes the set there and the tightness hypothesis on
  the coerced measures, which is what `isTightMeasureSet_kernel` supplies;
* compact closure ⇒ a convergent subsequence (`ℝ` is Polish, so the weak topology on
  `ProbabilityMeasure ℝ` is metrizable and compactness gives sequential compactness);
* any subsequential limit is causal by portmanteau on the open set `Iio 0`, and has the limiting
  transform by testing against the bounded surrogate `t ↦ e^{-s · max t 0}`, which agrees with
  `e^{-st}` where causal measures live — the surrogate exists precisely because `e^{-st}` itself
  is unbounded on `ℝ`, the same obstruction `Injectivity.lean` had to route around;
* `laplace_injective` identifies that limit, and compact-plus-unique-cluster-point upgrades the
  subsequence to the sequence.

This is a different API surface from everything above — the weak topology on
`ProbabilityMeasure`, not integrals — which is why it is separated out rather than attempted
piecemeal.

None of it was needed. See `WeakConvergence.lean`.
-/

namespace Hemigroup

open MeasureTheory Set
open scoped ENNReal

/-! ## A Markov bound from the transform -/

/-- **The tail of a causal probability measure is controlled by its Laplace transform.**

`μ(t > T) · (1 - e^{-sT}) ≤ 1 - μ̂(s)`. The content is pointwise: on `t > T` the integrand
`1 - e^{-st}` is at least `1 - e^{-sT}`, and off that set it is still nonnegative because the
measure is causal.

No hypothesis on `T` is needed — causality already supplies the sign that a `T ≥ 0` assumption
would have. -/
theorem measureReal_Ioi_mul_le {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsCausal μ)
    {s T : ℝ} (hs : 0 ≤ s) :
    (μ (Ioi T)).toReal * (1 - Real.exp (-(s * T))) ≤ 1 - laplace μ s := by
  have hint : Integrable (fun t => Real.exp (-(s * t))) μ := integrable_exp_of_causal hμ hs
  have h1 : 1 - laplace μ s = ∫ t, (1 - Real.exp (-(s * t))) ∂μ := by
    rw [laplace, integral_sub (integrable_const 1) hint, integral_const]
    simp
  have hind : Integrable ((Ioi T).indicator fun _ => 1 - Real.exp (-(s * T))) μ :=
    (integrable_const _).indicator measurableSet_Ioi
  rw [h1]
  calc (μ (Ioi T)).toReal * (1 - Real.exp (-(s * T)))
      = ∫ t, (Ioi T).indicator (fun _ => 1 - Real.exp (-(s * T))) t ∂μ := by
        rw [integral_indicator_const _ measurableSet_Ioi, smul_eq_mul, measureReal_def]
    _ ≤ ∫ t, (1 - Real.exp (-(s * t))) ∂μ := by
        refine integral_mono_ae hind ((integrable_const 1).sub hint) ?_
        filter_upwards [hμ.ae_nonneg] with t ht
        by_cases hcase : t ∈ Ioi T
        · rw [indicator_of_mem hcase]
          have : Real.exp (-(s * t)) ≤ Real.exp (-(s * T)) :=
            Real.exp_le_exp.mpr (by nlinarith [mem_Ioi.mp hcase])
          linarith
        · rw [indicator_of_notMem hcase]
          have : Real.exp (-(s * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
          linarith

/-- The tail bound in the form tightness needs: `μ(t > T) ≤ (1 - μ̂(s)) / (1 - e^{-sT})`. -/
theorem measureReal_Ioi_le_div {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsCausal μ)
    {s T : ℝ} (hs : 0 < s) (hT : 0 < T) :
    (μ (Ioi T)).toReal ≤ (1 - laplace μ s) / (1 - Real.exp (-(s * T))) := by
  have hden : 0 < 1 - Real.exp (-(s * T)) := by
    have : Real.exp (-(s * T)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
    linarith
  rw [le_div_iff₀ hden]
  exact measureReal_Ioi_mul_le hμ hs.le

/-! ## The uniform tail estimate for the kernel family -/

namespace SelfDecomposableExponent

variable {F : SelfDecomposableExponent} {a b s T B : ℝ}

/-- `1 - e^{-g} ≤ g`, the elementary step that replaces the transform by the exponent. -/
private lemma one_sub_exp_neg_le {g : ℝ} (_hg : 0 ≤ g) : 1 - Real.exp (-g) ≤ g := by
  have := Real.add_one_le_exp (-g)
  linarith

/-- **The uniform tail estimate.** For kernels with `b` bounded above by `B`, the tail is
controlled by `F` alone, uniformly in the pair:

  `μ_{a,b}(t > T) ≤ F(Bs) / (1 - e^{-sT})`.

Given `ε`, choosing `s` small makes `F(Bs)` small — because `F(0+) = 0` — and then `T` large
makes the denominator close to `1`. That is tightness, and every ingredient is ours. -/
theorem kernel_tail_le (ha : 0 ≤ a) (hab : a ≤ b) (hbB : b ≤ B) (hs : 0 < s) (hT : 0 < T) :
    ((F.kernel a b) (Ioi T)).toReal
      ≤ (F.exponent (B * s)).toReal / (1 - Real.exp (-(s * T))) := by
  haveI := isProbabilityMeasure_kernel (F := F) ha hab
  have hden : 0 < 1 - Real.exp (-(s * T)) := by
    have : Real.exp (-(s * T)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
    linarith
  have hB : 0 ≤ B := (ha.trans hab).trans hbB
  -- `1 - μ̂(s) ≤ g_{a,b}(s) ≤ F(Bs)`, the second step because exponents add along `a ≤ b ≤ B`.
  have hnum : 1 - laplace (F.kernel a b) s ≤ (F.exponent (B * s)).toReal := by
    rw [laplace_kernel ha hab hs.le]
    refine (one_sub_exp_neg_le ENNReal.toReal_nonneg).trans ?_
    have hmono : F.increment a b s ≤ F.exponent (B * s) := by
      calc F.increment a b s ≤ F.exponent (b * s) := by
            rw [← exponent_add_increment (F := F) ha hab hs.le]; exact le_add_self
        _ ≤ F.exponent (B * s) := by
            rw [← exponent_add_increment (F := F) (ha.trans hab) hbB hs.le]
            exact le_self_add
    exact ENNReal.toReal_mono (F.ne_top _ (by positivity)) hmono
  refine (measureReal_Ioi_le_div (isCausal_kernel ha hab) hs hT).trans ?_
  gcongr

/-! ## `F(0+) = 0`: the dominated-convergence step

`kernel_tail_le` turns tightness into "make `F(Bs)` small by taking `s` small", which needs the
exponent to vanish at the origin. `levyExponentD` gives `F(0) = 0` outright, but the tail
argument needs the *limit*, and that is a dominated-convergence argument on the Lévy integral:
the integrand `(1 - e^{-rt}) k t / t` increases in `r`, so the value at `r = 1` dominates the
whole family and is finite because `F` is.
-/

/-- **The exponent is sequentially continuous** on any bounded set of arguments: if `r n → ρ`
with `r n ≤ R`, then `F(r n) → F(ρ)`.

Dominated convergence on the Lévy integral. The integrand `(1 - e^{-rt}) k t / t` increases in
`r`, so the value at `R` dominates the whole family, and it is finite because `F` is. No
hypothesis that `r n ≥ 0` is needed: where `r n < 0` the integrand is negative and
`ENNReal.ofReal` truncates it to zero, which the bound still covers. -/
theorem tendsto_exponent (F : SelfDecomposableExponent) {r : ℕ → ℝ} {ρ R : ℝ}
    (hrR : ∀ n, r n ≤ R) (hR : 0 ≤ R) (hlim : Filter.Tendsto r Filter.atTop (nhds ρ)) :
    Filter.Tendsto (fun n => F.exponent (r n)) Filter.atTop (nhds (F.exponent ρ)) := by
  have hk : AEMeasurable F.k (volume.restrict (Ioi (0 : ℝ))) :=
    aemeasurable_of_antitoneOn F.k_antitone
  have hdrift : Filter.Tendsto (fun n => ENNReal.ofReal (F.b₀ * r n)) Filter.atTop
      (nhds (ENNReal.ofReal (F.b₀ * ρ))) := ENNReal.tendsto_ofReal (hlim.const_mul F.b₀)
  have hfin : levyJump F.k R ≠ ⊤ := by
    have h := F.ne_top R hR
    rw [levyExponentD] at h
    exact (ENNReal.add_ne_top.mp h).2
  have hbnd : ∀ n : ℕ,
      (fun t => ENNReal.ofReal ((1 - Real.exp (-(r n * t))) * F.k t / t))
        ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
        fun t => ENNReal.ofReal ((1 - Real.exp (-(R * t))) * F.k t / t) := by
    intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : 0 < t := ht
    have hnum : 1 - Real.exp (-(r n * t)) ≤ 1 - Real.exp (-(R * t)) := by
      have : Real.exp (-(R * t)) ≤ Real.exp (-(r n * t)) :=
        Real.exp_le_exp.mpr (by nlinarith [hrR n])
      linarith
    refine ENNReal.ofReal_le_ofReal ?_
    have hkt : 0 ≤ F.k t := F.k_nonneg t ht
    gcongr
  have hlm : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      Filter.Tendsto (fun n => ENNReal.ofReal ((1 - Real.exp (-(r n * t))) * F.k t / t))
        Filter.atTop (nhds (ENNReal.ofReal ((1 - Real.exp (-(ρ * t))) * F.k t / t))) := by
    filter_upwards with t
    have h0 : Filter.Tendsto (fun n => -(r n * t)) Filter.atTop (nhds (-(ρ * t))) :=
      (hlim.mul_const t).neg
    have hr : Filter.Tendsto (fun n => 1 - Real.exp (-(r n * t))) Filter.atTop
        (nhds (1 - Real.exp (-(ρ * t)))) :=
      ((Real.continuous_exp.tendsto _).comp h0).const_sub 1
    exact ENNReal.tendsto_ofReal ((hr.mul_const (F.k t)).div_const t)
  have hdom := tendsto_lintegral_of_dominated_convergence'
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun n t => ENNReal.ofReal ((1 - Real.exp (-(r n * t))) * F.k t / t))
    (f := fun t => ENNReal.ofReal ((1 - Real.exp (-(ρ * t))) * F.k t / t))
    (fun t => ENNReal.ofReal ((1 - Real.exp (-(R * t))) * F.k t / t))
    (fun n => aemeasurable_levyJump_integrand hk (r n)) hbnd (by rw [← levyJump]; exact hfin) hlm
  have hjump : Filter.Tendsto (fun n => levyJump F.k (r n)) Filter.atTop
      (nhds (levyJump F.k ρ)) := by simpa [levyJump] using hdom
  simpa [exponent, levyExponentD] using hdrift.add hjump

/-- The special case tightness consumes: `F(0+) = 0`. -/
theorem tendsto_exponent_atZero (F : SelfDecomposableExponent) {r : ℕ → ℝ}
    (hr1 : ∀ n, r n ≤ 1) (hlim : Filter.Tendsto r Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => F.exponent (r n)) Filter.atTop (nhds 0) := by
  have h0 : F.exponent 0 = 0 := by simp [exponent, levyExponentD, levyJump]
  have h := tendsto_exponent F hr1 zero_le_one hlim
  rwa [h0] at h

/-- **What tightness consumes**: the exponent can be made arbitrarily small near the origin. -/
theorem exists_exponent_lt (F : SelfDecomposableExponent) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ F.exponent r < ε := by
  have hr : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / (n + 1) := fun n => by positivity
  have hle : ∀ n : ℕ, (1 : ℝ) / (n + 1) ≤ 1 := fun n => by
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  obtain ⟨n, hn⟩ :=
    ((tendsto_exponent_atZero F hle hr).eventually
      (gt_mem_nhds hε)).exists
  exact ⟨1 / (n + 1), hpos n, hn⟩

/-! ## Convergence of the increments, and of the transforms

The last step before the Prokhorov assembly. Note it is carried out in `ℝ` rather than
`ℝ≥0∞`: truncated subtraction on `ℝ≥0∞` is not continuous, so the identity
`F(as) + g_{a,b}(s) = F(bs)` is pushed through `ENNReal.toReal` first, where every term is finite
and ordinary subtraction applies.
-/

/-- **The increments converge.** If `u n → α` and `v n → β` inside a bounded range, then
`g_{u n, v n}(s) → g_{α,β}(s)`. -/
theorem tendsto_increment_toReal (F : SelfDecomposableExponent) {u v : ℕ → ℝ} {α β B s : ℝ}
    (hs : 0 ≤ s) (hB : 0 ≤ B) (huB : ∀ n, u n ≤ B) (hvB : ∀ n, v n ≤ B)
    (hu0 : ∀ n, 0 ≤ u n) (huv : ∀ n, u n ≤ v n)
    (hα : Filter.Tendsto u Filter.atTop (nhds α)) (hβ : Filter.Tendsto v Filter.atTop (nhds β))
    (hα0 : 0 ≤ α) (hαβ : α ≤ β) :
    Filter.Tendsto (fun n => (F.increment (u n) (v n) s).toReal) Filter.atTop
      (nhds (F.increment α β s).toReal) := by
  have hBs : (0 : ℝ) ≤ B * s := by positivity
  -- The two exponents converge, by `tendsto_exponent` with the common bound `B * s`.
  have hEu : Filter.Tendsto (fun n => (F.exponent (u n * s)).toReal) Filter.atTop
      (nhds (F.exponent (α * s)).toReal) :=
    (ENNReal.tendsto_toReal (F.ne_top _ (mul_nonneg hα0 hs))).comp
      (tendsto_exponent F (fun n => mul_le_mul_of_nonneg_right (huB n) hs) hBs (hα.mul_const s))
  have hEv : Filter.Tendsto (fun n => (F.exponent (v n * s)).toReal) Filter.atTop
      (nhds (F.exponent (β * s)).toReal) :=
    (ENNReal.tendsto_toReal (F.ne_top _ (mul_nonneg (hα0.trans hαβ) hs))).comp
      (tendsto_exponent F (fun n => mul_le_mul_of_nonneg_right (hvB n) hs) hBs (hβ.mul_const s))
  -- `g` is the difference of the two exponents, in `ℝ`.
  have hdiff : ∀ {p q : ℝ}, 0 ≤ p → p ≤ q → (F.increment p q s).toReal
      = (F.exponent (q * s)).toReal - (F.exponent (p * s)).toReal :=
    fun hp hpq => increment_toReal hp hpq hs
  simp only [hdiff (hu0 _) (huv _), hdiff hα0 hαβ]
  exact hEv.sub hEu

/-- **The transforms converge** — the input Prokhorov needs, alongside `kernel_tail_le`. -/
theorem tendsto_laplace_kernel (F : SelfDecomposableExponent) {u v : ℕ → ℝ} {α β B s : ℝ}
    (hs : 0 ≤ s) (hB : 0 ≤ B) (huB : ∀ n, u n ≤ B) (hvB : ∀ n, v n ≤ B)
    (hu0 : ∀ n, 0 ≤ u n) (huv : ∀ n, u n ≤ v n)
    (hα : Filter.Tendsto u Filter.atTop (nhds α)) (hβ : Filter.Tendsto v Filter.atTop (nhds β))
    (hα0 : 0 ≤ α) (hαβ : α ≤ β) :
    Filter.Tendsto (fun n => laplace (F.kernel (u n) (v n)) s) Filter.atTop
      (nhds (laplace (F.kernel α β) s)) := by
  refine Filter.Tendsto.congr (fun n => (laplace_kernel (hu0 n) (huv n) hs).symm) ?_
  rw [laplace_kernel hα0 hαβ hs]
  exact (Real.continuous_exp.tendsto _).comp
    (tendsto_increment_toReal F hs hB huB hvB hu0 huv hα hβ hα0 hαβ).neg

/-! ## Tightness in Mathlib's sense

`kernel_tail_le` repackaged as `IsTightMeasureSet`, which is what Prokhorov consumes. The
compact set is `[0,T]`: causality kills the left tail outright, so the whole content is the
right tail, and `T` is chosen after `s` — first make `F(Bs)` small, then make the denominator
at least `1/2`.
-/

/-- **The uniform tail bound**, in `ℝ` and quantified over the whole admissible range: for any
`η > 0` there is a `T` beyond which every kernel with `b ≤ B` carries mass at most `η`.

This is tightness in the shape `tendsto_integral_of_tendsto_laplace` asks for. The two
parameters are chosen in order — `s` small enough that `F(Bs) < η/2`, which is where `F(0+) = 0`
is used, then `T` large enough that the denominator is at least `1/2`. -/
theorem exists_kernel_tail_le (F : SelfDecomposableExponent) {B : ℝ} (hB : 0 < B)
    {η : ℝ} (hη : 0 < η) :
    ∃ T : ℝ, 0 < T ∧ ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ B →
      ((F.kernel a b) (Ioi T)).toReal ≤ η := by
  obtain ⟨r, hr0, hrlt⟩ := exists_exponent_lt F (ε := ENNReal.ofReal (η / 2))
    (by simp only [ENNReal.ofReal_pos]; linarith)
  have hBne : B ≠ 0 := hB.ne'
  set s : ℝ := r / B with hs_def
  have hs : 0 < s := div_pos hr0 hB
  have hsne : s ≠ 0 := hs.ne'
  have hBs : B * s = r := by rw [hs_def]; field_simp
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set T : ℝ := (Real.log 2 + 1) / s with hT_def
  have hT0 : 0 < T := by positivity
  have hsT : s * T = Real.log 2 + 1 := by rw [hT_def]; field_simp
  have hhalf : (1 : ℝ) / 2 ≤ 1 - Real.exp (-(s * T)) := by
    have h1 : Real.exp (-(s * T)) ≤ 1 / 2 := by
      rw [hsT]
      calc Real.exp (-(Real.log 2 + 1)) ≤ Real.exp (-Real.log 2) :=
            Real.exp_le_exp.mpr (by linarith)
        _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log two_pos]; norm_num
    linarith
  have hexp_lt : (F.exponent r).toReal < η / 2 := by
    have h := (ENNReal.toReal_lt_toReal (F.ne_top r hr0.le) ENNReal.ofReal_ne_top).mpr hrlt
    rwa [ENNReal.toReal_ofReal (by linarith)] at h
  refine ⟨T, hT0, fun a b ha hab hbB => ?_⟩
  have htail := kernel_tail_le (F := F) ha hab hbB hs hT0
  rw [hBs] at htail
  have hden : (0 : ℝ) < 1 - Real.exp (-(s * T)) := by linarith
  have hquot : (F.exponent r).toReal / (1 - Real.exp (-(s * T))) ≤ η := by
    rw [div_le_iff₀ hden]
    nlinarith [ENNReal.toReal_nonneg (a := F.exponent r)]
  linarith

/-- **The kernel family is tight**, for parameters bounded above by `B`. -/
theorem isTightMeasureSet_kernel (F : SelfDecomposableExponent) {u v : ℕ → ℝ} {B : ℝ}
    (hB : 0 < B) (hu0 : ∀ n, 0 ≤ u n) (huv : ∀ n, u n ≤ v n) (hvB : ∀ n, v n ≤ B) :
    IsTightMeasureSet {μ : Measure ℝ | ∃ n, μ = F.kernel (u n) (v n)} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hεtop
  · exact ⟨∅, isCompact_empty, fun μ _ => le_top⟩
  have he0 : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
  obtain ⟨T, hT0, hT⟩ := exists_kernel_tail_le F hB he0
  refine ⟨Icc 0 T, isCompact_Icc, ?_⟩
  rintro μ ⟨n, rfl⟩
  haveI := isProbabilityMeasure_kernel (F := F) (hu0 n) (huv n)
  -- The left tail is null by causality, so only `Ioi T` matters.
  have hsub : (Icc (0 : ℝ) T)ᶜ ⊆ Iio 0 ∪ Ioi T := by
    intro x hx
    simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at hx
    exact hx.imp id id
  have hle : (F.kernel (u n) (v n)) ((Icc (0 : ℝ) T)ᶜ)
      ≤ (F.kernel (u n) (v n)) (Ioi T) := by
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    rw [isCausal_kernel (hu0 n) (huv n), zero_add]
  refine hle.trans ((ENNReal.toReal_le_toReal (measure_ne_top _ _) hεtop).mp ?_)
  exact hT _ _ (hu0 n) (huv n) (hvB n)

end SelfDecomposableExponent

/-! ## The general statement: tightness from a uniform transform bound (R25)

`lem:transform-tightness`'s second sentence, for an *arbitrary* family of causal probability
measures — not only the kernel family `exists_kernel_tail_le`/`isTightMeasureSet_kernel` above
specialise to. Nothing in the Markov-bound argument is about a kernel: `measureReal_Ioi_le_div` is
already stated for a bare causal probability measure, and the `s`-then-`T` choice that turns the
bound into a uniform tail estimate only needs the hypothesis `sup_i (1 - laplace(μ i) s) → 0` (here
in the equivalent "for every ε" form, matching how the specialised proof consumes it) — not that
`s` and `T` come from an `F.exponent`. -/

/-- **The general tail bound**: a family of causal probability measures whose transforms satisfy
`∀ ε > 0, ∃ s > 0, ∀ i, 1 - μ̂ᵢ(s) ≤ ε` has a uniform tail estimate, for every `η > 0`. Same
`s`-then-`T` choice as `exists_kernel_tail_le`, read off the hypothesis directly instead of
through `F.exponent`. -/
theorem exists_tail_le_of_forall_laplace {ι : Type*} {μ : ι → Measure ℝ}
    (hprob : ∀ i, IsProbabilityMeasure (μ i)) (hcausal : ∀ i, IsCausal (μ i))
    (hunif : ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ ∀ i, 1 - laplace (μ i) s ≤ ε) {η : ℝ} (hη : 0 < η) :
    ∃ T : ℝ, 0 < T ∧ ∀ i, (μ i (Ioi T)).toReal ≤ η := by
  obtain ⟨s, hs, hs'⟩ := hunif (η / 2) (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set T : ℝ := (Real.log 2 + 1) / s with hT_def
  have hT0 : 0 < T := by positivity
  have hsT : s * T = Real.log 2 + 1 := by rw [hT_def]; field_simp
  have hhalf : (1 : ℝ) / 2 ≤ 1 - Real.exp (-(s * T)) := by
    have h1 : Real.exp (-(s * T)) ≤ 1 / 2 := by
      rw [hsT]
      calc Real.exp (-(Real.log 2 + 1)) ≤ Real.exp (-Real.log 2) :=
            Real.exp_le_exp.mpr (by linarith)
        _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log two_pos]; norm_num
    linarith
  refine ⟨T, hT0, fun i => ?_⟩
  haveI := hprob i
  have hden : (0 : ℝ) < 1 - Real.exp (-(s * T)) := by linarith
  refine (measureReal_Ioi_le_div (hcausal i) hs hT0).trans ?_
  rw [div_le_iff₀ hden]
  nlinarith [hs' i, mul_le_mul_of_nonneg_left hhalf hη.le]

/-- **The general statement, in Mathlib's own vocabulary**: `Set.range μ` is tight. The compact
set is `[0,T]` exactly as in `isTightMeasureSet_kernel`, for the same reason — causality kills the
left tail outright. -/
theorem isTightMeasureSet_of_forall_laplace {ι : Type*} {μ : ι → Measure ℝ}
    (hprob : ∀ i, IsProbabilityMeasure (μ i)) (hcausal : ∀ i, IsCausal (μ i))
    (hunif : ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ ∀ i, 1 - laplace (μ i) s ≤ ε) :
    IsTightMeasureSet (Set.range μ) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hεtop
  · exact ⟨∅, isCompact_empty, fun ν _ => le_top⟩
  have he0 : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
  obtain ⟨T, hT0, hT⟩ := exists_tail_le_of_forall_laplace hprob hcausal hunif he0
  refine ⟨Icc 0 T, isCompact_Icc, ?_⟩
  rintro ν ⟨i, rfl⟩
  haveI := hprob i
  have hsub : (Icc (0 : ℝ) T)ᶜ ⊆ Iio 0 ∪ Ioi T := by
    intro x hx
    simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at hx
    exact hx.imp id id
  have hle : (μ i) ((Icc (0 : ℝ) T)ᶜ) ≤ (μ i) (Ioi T) := by
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    rw [hcausal i, zero_add]
  refine hle.trans ((ENNReal.toReal_le_toReal (measure_ne_top _ _) hεtop).mp ?_)
  exact hT i

namespace SelfDecomposableExponent

/-! ## Strict monotonicity of `F`

The last analytic ingredient of `thm:main-characterization` (⇐): its uniqueness clause recovers
`χ(x)` as the unique `c` with `g_{0,x} = F(c ·)`, and "unique" is exactly strict monotonicity.
-/

/-- `F` is nondecreasing — immediate from `F(as) + g_{a,b}(s) = F(bs)`, since the increment is
a nonnegative quantity. -/
theorem exponent_mono (F : SelfDecomposableExponent) {s₁ s₂ : ℝ} (h1 : 0 < s₁) (h12 : s₁ ≤ s₂) :
    F.exponent s₁ ≤ F.exponent s₂ := by
  have hc : 1 ≤ s₂ / s₁ := (one_le_div h1).mpr h12
  have h := exponent_add_increment (F := F) (a := 1) (b := s₂ / s₁) zero_le_one hc h1.le
  rw [one_mul, div_mul_cancel₀ _ h1.ne'] at h
  rw [← h]
  exact le_self_add

/-- **If `F` is not identically zero it is strictly increasing on `(0,∞)`.**

Suppose an increment `g_{1,c}` vanished at one point. By `lem:vanishing` — in the Lean form
`levyExponentD_eq_zero_of_eq_zero` — it vanishes identically, so `F(cs) = F(s)` for every `s`.
Iterating *downwards* gives `F(s₀) = F(s₀ / cⁿ)` for all `n`, and `s₀ / cⁿ → 0` because `c > 1`,
so continuity at the origin forces `F(s₀) = F(0) = 0`. Since `s₀` was an arbitrary point,
`F ≡ 0`.

Note the direction: iterating *upwards* would need monotonicity and a boundedness argument;
downwards it is just `tendsto_exponent` at `ρ = 0`. -/
theorem exponent_strictMono (F : SelfDecomposableExponent)
    (hne : ∃ s₀, 0 < s₀ ∧ F.exponent s₀ ≠ 0)
    {s₁ s₂ : ℝ} (h1 : 0 < s₁) (h12 : s₁ < s₂) : F.exponent s₁ < F.exponent s₂ := by
  obtain ⟨s₀, hs₀, hs₀ne⟩ := hne
  set c : ℝ := s₂ / s₁ with hc_def
  have hc1 : 1 < c := (one_lt_div h1).mpr h12
  have hc0 : 0 < c := lt_trans one_pos hc1
  have hkey := exponent_add_increment (F := F) (a := 1) (b := c) zero_le_one hc1.le h1.le
  rw [one_mul, hc_def, div_mul_cancel₀ _ h1.ne'] at hkey
  rw [← hkey]
  refine ENNReal.lt_add_right (F.ne_top _ h1.le) ?_
  -- Suppose the increment vanished at `s₁`.
  intro hzero
  -- Then it vanishes identically, so `F(c s) = F(s)` for every `s ≥ 0`.
  have hdens : AEMeasurable (F.incrementDensity 1 c) (volume.restrict (Ioi (0 : ℝ))) :=
    aemeasurable_incrementDensity zero_le_one hc0.le
  have hInc : ∀ s, 0 ≤ s → F.increment 1 c s = 0 :=
    levyExponentD_eq_zero_of_eq_zero (mul_nonneg F.b₀_nonneg (by linarith)) hdens h1 hzero
  have hfix : ∀ s, 0 ≤ s → F.exponent (c * s) = F.exponent s := by
    intro s hs
    have h := exponent_add_increment (F := F) (a := 1) (b := c) zero_le_one hc1.le hs
    rw [one_mul, hInc s hs, add_zero] at h
    exact h.symm
  -- Iterate downwards: `F(s₀ / cⁿ) = F(s₀)`.
  have hiter : ∀ n : ℕ, F.exponent (s₀ / c ^ n) = F.exponent s₀ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hpos : (0 : ℝ) ≤ s₀ / c ^ (n + 1) := by positivity
        have hstep : c * (s₀ / c ^ (n + 1)) = s₀ / c ^ n := by
          field_simp
          ring
        rw [← ih, ← hstep, hfix _ hpos]
  -- `s₀ / cⁿ → 0`, so `F(s₀) = F(0) = 0`, contradicting the hypothesis.
  have hlim : Filter.Tendsto (fun n : ℕ => s₀ / c ^ n) Filter.atTop (nhds 0) := by
    have hpow : Filter.Tendsto (fun n : ℕ => (c ^ n)⁻¹) Filter.atTop (nhds 0) :=
      (tendsto_pow_atTop_atTop_of_one_lt hc1).inv_tendsto_atTop
    simpa [div_eq_mul_inv] using hpow.const_mul s₀
  have hbound : ∀ n : ℕ, s₀ / c ^ n ≤ s₀ := by
    intro n
    rw [div_le_iff₀ (by positivity)]
    nlinarith [one_le_pow₀ hc1.le (n := n), hs₀.le]
  have h0 : F.exponent 0 = 0 := by simp [exponent, levyExponentD, levyJump]
  have := tendsto_exponent F hbound hs₀.le hlim
  simp only [hiter, h0] at this
  exact hs₀ne (tendsto_nhds_unique tendsto_const_nhds this)

/-! ## Axiom (A7) -/

/-- **Axiom (A7)**: the kernel family is weakly continuous in its parameters. If
`(a_n, b_n) → (α, β)` inside a bounded range, then `μ_{a_n,b_n} → μ_{α,β}` weakly.

Both inputs are proved above and neither is cited: transform convergence is
`tendsto_laplace_kernel`, tightness is `exists_kernel_tail_le`, and the continuity theorem that
combines them is `tendsto_integral_of_tendsto_laplace` — ledger A5's content, proved rather than
assumed. So (A7) costs nothing at the trust boundary. -/
theorem tendsto_integral_kernel (F : SelfDecomposableExponent) {u v : ℕ → ℝ} {α β B : ℝ}
    (hB : 0 < B) (hu0 : ∀ n, 0 ≤ u n) (huv : ∀ n, u n ≤ v n) (hvB : ∀ n, v n ≤ B)
    (hα : Filter.Tendsto u Filter.atTop (nhds α))
    (hβ : Filter.Tendsto v Filter.atTop (nhds β))
    (hα0 : 0 ≤ α) (hαβ : α ≤ β) (hβB : β ≤ B) (f : BoundedContinuousFunction ℝ ℝ) :
    Filter.Tendsto (fun n => ∫ t, f t ∂(F.kernel (u n) (v n))) Filter.atTop
      (nhds (∫ t, f t ∂(F.kernel α β))) := by
  haveI : ∀ n, IsProbabilityMeasure (F.kernel (u n) (v n)) := fun n =>
    isProbabilityMeasure_kernel (hu0 n) (huv n)
  haveI : IsProbabilityMeasure (F.kernel α β) := isProbabilityMeasure_kernel hα0 hαβ
  refine tendsto_integral_of_tendsto_laplace (fun n => isCausal_kernel (hu0 n) (huv n))
    (isCausal_kernel hα0 hαβ) (fun η hη => ?_) (fun s hs => ?_) f
  · obtain ⟨T, _, hT⟩ := exists_kernel_tail_le F hB hη
    exact ⟨T, fun n => hT _ _ (hu0 n) (huv n) (hvB n), hT _ _ hα0 hαβ hβB⟩
  · exact tendsto_laplace_kernel F hs hB.le (fun n => (huv n).trans (hvB n)) hvB hu0 huv
      hα hβ hα0 hαβ

end SelfDecomposableExponent

end Hemigroup
