/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.Construction
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
(`kernel_tail_le`); and the fact that makes it bite, `F(0+) = 0` (`exists_exponent_lt`), so that
`s` can be chosen to make the numerator as small as wanted. Every step is Lean core.

**Continuity of the exponent** (`tendsto_exponent`): `r n → ρ` with `r n ≤ R` gives
`F(r n) → F(ρ)`, by dominated convergence against the integrand at `R`. This is the
pointwise-convergence-of-transforms ingredient.

So the blueprint's claim that the tightness argument is ours is **checked**, not merely asserted.

## What remains

Two steps, neither needing a citation:

* convergence of the *increments*: `g_{aₙ,bₙ}(s) → g_{a,b}(s)` when `(aₙ,bₙ) → (a,b)`. The
  exponents are continuous by `tendsto_exponent` and `F(a s) + g_{a,b}(s) = F(b s)` with every
  term finite, so this is cancellation in `ℝ≥0∞` — short, but not written here;
* the assembly: tight + convergent transforms ⇒ weak convergence. Prokhorov (Mathlib has it)
  gives a convergent subsequence, `laplace_injective` identifies its limit, and
  compact-plus-unique-limit-point upgrades that to the full sequence.

Until those are written, **A5 remains a live candidate for the trust boundary.** The evidence
here says it is very likely avoidable; it does not yet say it is avoided.
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
theorem kernel_tail_le (ha : 0 < a) (hab : a ≤ b) (hbB : b ≤ B) (hs : 0 < s) (hT : 0 < T) :
    ((F.kernel a b) (Ioi T)).toReal
      ≤ (F.exponent (B * s)).toReal / (1 - Real.exp (-(s * T))) := by
  haveI := isProbabilityMeasure_kernel (F := F) ha hab
  have hden : 0 < 1 - Real.exp (-(s * T)) := by
    have : Real.exp (-(s * T)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
    linarith
  have hB : 0 < B := lt_of_lt_of_le (lt_of_lt_of_le ha hab) hbB
  -- `1 - μ̂(s) ≤ g_{a,b}(s) ≤ F(Bs)`, the second step because exponents add along `a ≤ b ≤ B`.
  have hnum : 1 - laplace (F.kernel a b) s ≤ (F.exponent (B * s)).toReal := by
    rw [laplace_kernel ha hab hs.le]
    refine (one_sub_exp_neg_le ENNReal.toReal_nonneg).trans ?_
    have hmono : F.increment a b s ≤ F.exponent (B * s) := by
      calc F.increment a b s ≤ F.exponent (b * s) := by
            rw [← exponent_add_increment (F := F) ha hab hs.le]; exact le_add_self
        _ ≤ F.exponent (B * s) := by
            rw [← exponent_add_increment (F := F) (lt_of_lt_of_le ha hab) hbB hs.le]
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

end SelfDecomposableExponent

end Hemigroup
