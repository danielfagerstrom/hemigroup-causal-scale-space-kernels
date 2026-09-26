/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Hemigroup.ZStarLogGrowth
import Hemigroup.ExponentDerivative

/-!
# `lem:zstar-log-growth` (11.23), the driftless clause

With `b₀ = 0` the log-growth rate of the exponent is the catalogue height
`k(0⁺) = sup_{t>0} k(t)`, valued in `[0,∞]`.

## The route, and why it is not the blueprint's

The blueprint proves this through `B(s) := sF'(s) = b₀s + ∫₀^∞ e^{-u}k(u/s)du`, which converges
to `k(0⁺)` by monotone convergence, and then a Cesàro step
`F(s)/log s = (log s)^{-1}∫_1^s B(v)v^{-1}dv → \lim B`. That step is an `∞/∞` L'Hôpital, and
**Mathlib carries the `0/0` form only** (`Mathlib/Analysis/Calculus/LHopital.lean`).

The route taken here never differentiates. Both bounds come from splitting the defining integral
and using nothing but monotonicity of `k` and `∫_a^b dt/t = log(b/a)`:

* **below.** Fix `t₀` with `k(t₀)` above the level wanted; `k ≥ k(t₀)` on all of `(0,t₀]` because
  `k` is nonincreasing. On `(M/s, t₀]` also `1 - e^{-st} ≥ 1 - e^{-M}`, so
  `F(s) ≥ (1-e^{-M})k(t₀)·log(t₀s/M)`, and dividing by `log s` and letting `M → ∞` gives every
  level below `k(0⁺)`;
* **above** (needed only when `k(0⁺) < ∞`). Split at `1/s`: on `(0,1/s]` use `1 - e^{-st} ≤ st`,
  which contributes at most `k(0⁺)`; on `(1/s,1]` use `1 - e^{-st} ≤ 1`, contributing
  `k(0⁺)log s`; and `(1,∞)` contributes a constant, finite because `levyJump k 1` is.

So `F(s)/log s` is squeezed between `(1-e^{-M})k(t₀)·(1 + \log(t₀/M)/\log s)` and
`k(0⁺) + C/\log s`. The two-sided form is assembled by `tendsto_order`, which handles
`k(0⁺) = ∞` without a case split: there is then no level above it to check.
-/

namespace Hemigroup

open MeasureTheory Set Filter
open scoped ENNReal Topology

variable {k : ℝ → ℝ}

/-! ## `∫_a^b dt/t = log(b/a)` as an `ℝ≥0∞`-valued integral -/

/-- The Haar integral of the multiplicative group on a compact piece of the half-line. -/
lemma lintegral_ofReal_inv_Ioc {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫⁻ t in Ioc a b, ENNReal.ofReal t⁻¹ = ENNReal.ofReal (Real.log (b / a)) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hmem : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    exact fun h => absurd h.1 (not_le.2 ha)
  have hii : IntervalIntegrable (fun t : ℝ => t⁻¹) volume a b :=
    intervalIntegrable_inv_iff.2 (Or.inr hmem)
  have hint : IntegrableOn (fun t : ℝ => t⁻¹) (Ioc a b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hii
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc a b)] fun t : ℝ => t⁻¹ := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    exact inv_nonneg.2 (le_of_lt (lt_of_lt_of_le ha ht.1.le))
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn,
    ← intervalIntegral.integral_of_le hab, integral_inv_of_pos ha hb]

/-! ## The lower bound -/

/-- **Below.** On `(a,b]` with `k ≥ c` and `st ≥ M`, the jump part dominates
`(1-e^{-M})c·\log(b/a)`. -/
lemma le_levyJump_of_le {a b c M s : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc : 0 ≤ c) (hM : 0 ≤ M)
    (hs : 0 ≤ s) (hMa : M ≤ s * a) (hk : ∀ t ∈ Ioc a b, c ≤ k t) :
    ENNReal.ofReal ((1 - Real.exp (-M)) * c * Real.log (b / a)) ≤ levyJump k s := by
  have hβ : 0 ≤ 1 - Real.exp (-M) := by
    have : Real.exp (-M) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    linarith
  set β : ℝ := (1 - Real.exp (-M)) * c with hβdef
  have hβ0 : 0 ≤ β := mul_nonneg hβ hc
  have hpt : ∀ t ∈ Ioc a b,
      ENNReal.ofReal β * ENNReal.ofReal t⁻¹
        ≤ ENNReal.ofReal ((1 - Real.exp (-(s * t))) * k t / t) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ha ht.1.le
    have hst : M ≤ s * t := le_trans hMa (mul_le_mul_of_nonneg_left ht.1.le hs)
    have hexp : Real.exp (-(s * t)) ≤ Real.exp (-M) := Real.exp_le_exp.2 (by linarith)
    have hkt : c ≤ k t := hk t ht
    rw [← ENNReal.ofReal_mul hβ0]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← div_eq_mul_inv, div_le_div_iff_of_pos_right ht0]
    exact mul_le_mul (by linarith) hkt hc (by linarith)
  have hstep : ∫⁻ t in Ioc a b, ENNReal.ofReal β * ENNReal.ofReal t⁻¹
      ≤ ∫⁻ t in Ioc a b, ENNReal.ofReal ((1 - Real.exp (-(s * t))) * k t / t) := by
    refine lintegral_mono_ae ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht using hpt t ht
  have hconst : ∫⁻ t in Ioc a b, ENNReal.ofReal β * ENNReal.ofReal t⁻¹
      = ENNReal.ofReal β * ENNReal.ofReal (Real.log (b / a)) := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_ofReal_inv_Ioc ha hab]
  have hsub : ∫⁻ t in Ioc a b, ENNReal.ofReal ((1 - Real.exp (-(s * t))) * k t / t)
      ≤ levyJump k s :=
    lintegral_mono_set (fun t ht => ha.trans ht.1)
  rw [ENNReal.ofReal_mul hβ0]
  exact le_trans (le_of_eq hconst.symm) (hstep.trans hsub)

/-! ## The upper bound -/

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent)

/-- The tail mass `∫_1^∞ k(t)t^{-1}dt` is finite — forced by `ne_top` at `s = 1`, not assumed. -/
lemma lintegral_tail_ne_top :
    (∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (F.k t / t)) ≠ ⊤ := by
  set C : ℝ := (1 - Real.exp (-1))⁻¹ with hC
  have he1 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
  have hC0 : 0 < C := inv_pos.2 (by linarith)
  have hpt : ∀ t ∈ Ioi (1 : ℝ), ENNReal.ofReal (F.k t / t)
      ≤ ENNReal.ofReal C * ENNReal.ofReal ((1 - Real.exp (-(1 * t))) * F.k t / t) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
    have hkt : 0 ≤ F.k t := F.k_nonneg t (mem_Ioi.mpr ht0)
    have hexp : Real.exp (-(1 * t)) ≤ Real.exp (-1) :=
      Real.exp_le_exp.2 (by simpa using le_of_lt ht)
    rw [← ENNReal.ofReal_mul hC0.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have key : F.k t ≤ C * ((1 - Real.exp (-(1 * t))) * F.k t) := by
      rw [hC, inv_mul_eq_div, le_div_iff₀ (by linarith)]
      nlinarith
    calc F.k t / t ≤ C * ((1 - Real.exp (-(1 * t))) * F.k t) / t :=
          div_le_div_of_nonneg_right key ht0.le
      _ = C * ((1 - Real.exp (-(1 * t))) * F.k t / t) := by ring
  have hle : (∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (F.k t / t))
      ≤ ENNReal.ofReal C * levyJump F.k 1 := by
    calc (∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (F.k t / t))
        ≤ ∫⁻ t in Ioi (1 : ℝ),
            ENNReal.ofReal C * ENNReal.ofReal ((1 - Real.exp (-(1 * t))) * F.k t / t) := by
          refine lintegral_mono_ae ?_
          filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht using hpt t ht
      _ = ENNReal.ofReal C
            * ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal ((1 - Real.exp (-(1 * t))) * F.k t / t) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal C * levyJump F.k 1 := by
          gcongr
          exact lintegral_mono_set fun t ht => mem_Ioi.mpr (lt_trans zero_lt_one (mem_Ioi.mp ht))
  exact ne_top_of_le_ne_top (by simp [ENNReal.mul_ne_top, F.levyJump_one_ne_top]) hle

/-- **Above.** With `k ≤ x` throughout, the jump part at `s ≥ 1` is at most `x + x\log s` plus the
tail mass beyond `1`. The three pieces are `(0,1/s]`, where `1 - e^{-st} \le st` absorbs the
singularity of `dt/t`; `(1/s,1]`, where `1 - e^{-st} \le 1` leaves exactly `\log s`; and
`(1,\infty)`, which does not grow with `s` at all. -/
lemma levyJump_le_of_le {x s : ℝ} (hx : 0 ≤ x) (hs : 1 ≤ s)
    (hk : ∀ t ∈ Ioi (0 : ℝ), F.k t ≤ x) :
    levyJump F.k s ≤ ENNReal.ofReal x + ENNReal.ofReal (x * Real.log s)
      + ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (F.k t / t) := by
  have hs0 : (0 : ℝ) < s := lt_of_lt_of_le zero_lt_one hs
  set r : ℝ := 1 / s with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r ≤ 1 := by rw [hr]; rw [div_le_one hs0]; exact hs
  set f : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal ((1 - Real.exp (-(s * t))) * F.k t / t) with hf
  -- split `(0,∞) = (0,r] ∪ (r,1] ∪ (1,∞)`
  have hd1 : Disjoint (Ioc (0 : ℝ) 1) (Ioi (1 : ℝ)) := by
    rw [Set.disjoint_left]
    exact fun t ht ht' => absurd (mem_Ioi.mp ht') (not_lt.2 ht.2)
  have hd2 : Disjoint (Ioc (0 : ℝ) r) (Ioc r 1) := by
    rw [Set.disjoint_left]
    exact fun t ht ht' => absurd ht'.1 (not_lt.2 ht.2)
  have hsplit1 : ∫⁻ t in Ioi (0 : ℝ), f t
      = (∫⁻ t in Ioc (0 : ℝ) 1, f t) + ∫⁻ t in Ioi (1 : ℝ), f t := by
    rw [← lintegral_union measurableSet_Ioi hd1, Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
  have hsplit2 : ∫⁻ t in Ioc (0 : ℝ) 1, f t
      = (∫⁻ t in Ioc (0 : ℝ) r, f t) + ∫⁻ t in Ioc r 1, f t := by
    rw [← lintegral_union measurableSet_Ioc hd2, Set.Ioc_union_Ioc_eq_Ioc hr0.le hr1]
  -- the piece below `1/s`
  have hA : ∫⁻ t in Ioc (0 : ℝ) r, f t ≤ ENNReal.ofReal x := by
    have hpt : ∀ t ∈ Ioc (0 : ℝ) r, f t ≤ ENNReal.ofReal (x * s) := by
      intro t ht
      have ht0 : (0 : ℝ) < t := ht.1
      have hkt : 0 ≤ F.k t := F.k_nonneg t (mem_Ioi.mpr ht0)
      have hexp : 1 - Real.exp (-(s * t)) ≤ s * t := by
        have := Real.add_one_le_exp (-(s * t)); linarith
      have hexp0 : 0 ≤ 1 - Real.exp (-(s * t)) := by
        have : Real.exp (-(s * t)) ≤ 1 :=
          Real.exp_le_one_iff.2 (by nlinarith)
        linarith
      refine ENNReal.ofReal_le_ofReal ?_
      rw [div_le_iff₀ ht0]
      nlinarith [hk t (mem_Ioi.mpr ht0)]
    calc ∫⁻ t in Ioc (0 : ℝ) r, f t ≤ ∫⁻ _t in Ioc (0 : ℝ) r, ENNReal.ofReal (x * s) := by
          refine lintegral_mono_ae ?_
          filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht using hpt t ht
      _ = ENNReal.ofReal (x * s) * ENNReal.ofReal r := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero]
      _ = ENNReal.ofReal x := by
          rw [← ENNReal.ofReal_mul (by positivity), hr]
          congr 1
          field_simp
  -- the piece between `1/s` and `1`
  have hB : ∫⁻ t in Ioc r 1, f t ≤ ENNReal.ofReal (x * Real.log s) := by
    have hpt : ∀ t ∈ Ioc r 1, f t ≤ ENNReal.ofReal x * ENNReal.ofReal t⁻¹ := by
      intro t ht
      have ht0 : (0 : ℝ) < t := lt_trans hr0 ht.1
      have hkt : 0 ≤ F.k t := F.k_nonneg t (mem_Ioi.mpr ht0)
      have hexp1 : 1 - Real.exp (-(s * t)) ≤ 1 := by
        have := Real.exp_pos (-(s * t)); linarith
      have hexp0 : 0 ≤ 1 - Real.exp (-(s * t)) := by
        have : Real.exp (-(s * t)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
        linarith
      rw [← ENNReal.ofReal_mul hx]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← div_eq_mul_inv, div_le_div_iff_of_pos_right ht0]
      nlinarith [hk t (mem_Ioi.mpr ht0)]
    calc ∫⁻ t in Ioc r 1, f t ≤ ∫⁻ t in Ioc r 1, ENNReal.ofReal x * ENNReal.ofReal t⁻¹ := by
          refine lintegral_mono_ae ?_
          filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht using hpt t ht
      _ = ENNReal.ofReal x * ENNReal.ofReal (Real.log (1 / r)) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_ofReal_inv_Ioc hr0 hr1]
      _ = ENNReal.ofReal (x * Real.log s) := by
          rw [← ENNReal.ofReal_mul hx, hr]
          congr 2
          rw [one_div_one_div]
  -- the tail
  have hC : ∫⁻ t in Ioi (1 : ℝ), f t ≤ ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (F.k t / t) := by
    refine lintegral_mono_ae ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
    have hkt : 0 ≤ F.k t := F.k_nonneg t (mem_Ioi.mpr ht0)
    have hexp1 : 1 - Real.exp (-(s * t)) ≤ 1 := by
      have := Real.exp_pos (-(s * t)); linarith
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_div_iff_of_pos_right ht0]
    nlinarith
  calc levyJump F.k s = (∫⁻ t in Ioc (0 : ℝ) r, f t) + (∫⁻ t in Ioc r 1, f t)
        + ∫⁻ t in Ioi (1 : ℝ), f t := by
        rw [levyJump, hsplit1, hsplit2]
    _ ≤ ENNReal.ofReal x + ENNReal.ofReal (x * Real.log s)
        + ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (F.k t / t) := by
        gcongr

/-! ## The limit -/

/-- **`lem:zstar-log-growth`(2), driftless case**: with `b₀ = 0` the log-growth rate is the
catalogue height `k(0⁺) = sup_{t>0} k(t)`, valued in `[0,∞]` for the same reason `zStar` is (a
nonincreasing `k` unbounded near `0` would junk a real-valued supremum to `0`). Unconditional —
no no-atom hypothesis, this being a statement about the exponent alone. -/
theorem tendsto_toRealExponent_div_log_atTop_of_b₀_zero (hb : F.b₀ = 0) :
    Tendsto (fun s => ENNReal.ofReal (F.toRealExponent s / Real.log s)) atTop
      (𝓝 (⨆ t ∈ Ioi (0 : ℝ), ENNReal.ofReal (F.k t))) := by
  set K : ℝ≥0∞ := ⨆ t ∈ Ioi (0 : ℝ), ENNReal.ofReal (F.k t) with hK
  have hEq : ∀ s : ℝ, F.exponent s = levyJump F.k s := by
    intro s
    simp [SelfDecomposableExponent.exponent, levyExponentD, hb]
  have hFne : ∀ s : ℝ, 0 ≤ s → levyJump F.k s ≠ ⊤ := fun s hs => (hEq s) ▸ F.ne_top s hs
  have hFval : ∀ s : ℝ, F.toRealExponent s = (levyJump F.k s).toReal := by
    intro s; rw [SelfDecomposableExponent.toRealExponent, hEq]
  refine tendsto_order.2 ⟨?_, ?_⟩
  · -- every level below `k(0⁺)` is eventually passed
    intro a ha
    obtain ⟨t₀, ht₀, hat₀⟩ : ∃ t₀, 0 < t₀ ∧ a < ENNReal.ofReal (F.k t₀) := by
      by_contra hcon
      push_neg at hcon
      exact absurd (iSup₂_le fun t ht => hcon t ht) (not_le.2 ha)
    have haT : a ≠ ⊤ := (lt_of_lt_of_le hat₀ le_top).ne_top
    set α : ℝ := a.toReal with hα
    have haeq : a = ENNReal.ofReal α := (ENNReal.ofReal_toReal haT).symm
    have hα0 : 0 ≤ α := ENNReal.toReal_nonneg
    set c : ℝ := F.k t₀ with hc
    have hc0 : 0 ≤ c := F.k_nonneg t₀ (mem_Ioi.mpr ht₀)
    have hαc : α < c := (ENNReal.lt_ofReal_iff_toReal_lt haT).1 hat₀
    -- a cut-off `M` for which `(1 - e^{-M})c` still beats the level
    have hlim : Tendsto (fun M : ℝ => (1 - Real.exp (-M)) * c) atTop (𝓝 c) := by
      have h0 : Tendsto (fun M : ℝ => Real.exp (-M)) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
      have h1 : Tendsto (fun M : ℝ => (1 - Real.exp (-M)) * c) atTop (𝓝 ((1 - 0) * c)) :=
        (tendsto_const_nhds.sub h0).mul tendsto_const_nhds
      simpa using h1
    obtain ⟨M, hMα, hM0⟩ :=
      ((hlim.eventually (lt_mem_nhds hαc)).and (eventually_gt_atTop (0 : ℝ))).exists
    set β : ℝ := (1 - Real.exp (-M)) * c with hβ
    -- the comparison function, whose limit is `β`
    have hg : Tendsto (fun s : ℝ => β + β * Real.log (t₀ / M) / Real.log s) atTop (𝓝 β) := by
      have := tendsto_const_nhds (x := β * Real.log (t₀ / M)) (f := atTop (α := ℝ))
      simpa using tendsto_const_nhds.add (this.div_atTop Real.tendsto_log_atTop)
    filter_upwards [hg.eventually (lt_mem_nhds hMα), eventually_ge_atTop (M / t₀),
      eventually_gt_atTop (1 : ℝ)] with s hgs hsM hs1
    have hs0 : (0 : ℝ) < s := lt_trans zero_lt_one hs1
    have hlog : 0 < Real.log s := Real.log_pos hs1
    have hMs : 0 < M / s := div_pos hM0 hs0
    have hMne : M ≠ 0 := hM0.ne'
    have hsne : s ≠ 0 := hs0.ne'
    have hlogne : Real.log s ≠ 0 := hlog.ne'
    have hMst : M / s ≤ t₀ := by
      rw [div_le_iff₀ hs0]
      have h1 : M / t₀ * t₀ ≤ s * t₀ := mul_le_mul_of_nonneg_right hsM ht₀.le
      rw [div_mul_cancel₀ _ ht₀.ne'] at h1
      exact le_trans h1 (le_of_eq (mul_comm s t₀))
    have hlow := le_levyJump_of_le (k := F.k) hMs hMst hc0 hM0.le hs0.le
      (by rw [mul_div_cancel₀ _ hs0.ne'])
      (fun t ht => F.k_antitone (mem_Ioi.mpr (lt_of_lt_of_le hMs ht.1.le))
        (mem_Ioi.mpr ht₀) ht.2)
    have hsplitlog : Real.log (t₀ / (M / s)) = Real.log s + Real.log (t₀ / M) := by
      rw [show t₀ / (M / s) = s * (t₀ / M) by field_simp]
      rw [Real.log_mul hs0.ne' (by positivity)]
    rw [hsplitlog] at hlow
    have hreal : β * (Real.log s + Real.log (t₀ / M)) ≤ F.toRealExponent s := by
      rw [hFval s]
      exact (ENNReal.ofReal_le_iff_le_toReal (hFne s hs0.le)).1 hlow
    have hdiv : β + β * Real.log (t₀ / M) / Real.log s ≤ F.toRealExponent s / Real.log s := by
      have heq : β + β * Real.log (t₀ / M) / Real.log s
          = β * (Real.log s + Real.log (t₀ / M)) / Real.log s := by
        field_simp
      rw [heq, div_le_div_iff_of_pos_right hlog]
      exact hreal
    have hfin : α < F.toRealExponent s / Real.log s := lt_of_lt_of_le hgs hdiv
    rw [haeq]
    exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt hα0 hfin)).2 hfin
  · -- and no level above it is ever reached
    intro b hb'
    obtain ⟨r₂, hKr₂, hr₂b⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hb'
    obtain ⟨r₁, hKr₁, hr₁r₂⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hKr₂
    set x : ℝ := (r₁ : ℝ) with hx
    set y : ℝ := (r₂ : ℝ) with hy
    have hx0 : 0 ≤ x := r₁.coe_nonneg
    have hxy : x < y := by exact_mod_cast (ENNReal.coe_lt_coe.1 hr₁r₂)
    have hy0 : 0 < y := lt_of_le_of_lt hx0 hxy
    have hkx : ∀ t ∈ Ioi (0 : ℝ), F.k t ≤ x := by
      intro t ht
      have h1 : ENNReal.ofReal (F.k t) ≤ K :=
        le_iSup₂ (f := fun t (_ : t ∈ Ioi (0 : ℝ)) => ENNReal.ofReal (F.k t)) t ht
      have h2 : ENNReal.ofReal (F.k t) < ENNReal.ofReal x := by
        rw [hx, ENNReal.ofReal_coe_nnreal]
        exact lt_of_le_of_lt h1 hKr₁
      exact le_of_lt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (F.k_nonneg t ht)).1 h2)
    set T : ℝ≥0∞ := ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (F.k t / t) with hT
    have hTne : T ≠ ⊤ := F.lintegral_tail_ne_top
    set τ : ℝ := T.toReal with hτ
    have hτ0 : 0 ≤ τ := ENNReal.toReal_nonneg
    have hlim : Tendsto (fun s : ℝ => x + (x + τ) / Real.log s) atTop (𝓝 x) := by
      simpa using tendsto_const_nhds.add
        ((tendsto_const_nhds (x := x + τ) (f := atTop (α := ℝ))).div_atTop Real.tendsto_log_atTop)
    filter_upwards [hlim.eventually (gt_mem_nhds hxy), eventually_gt_atTop (1 : ℝ)]
      with s hs hs1
    have hs0 : (0 : ℝ) < s := lt_trans zero_lt_one hs1
    have hlog : 0 < Real.log s := Real.log_pos hs1
    have hup := F.levyJump_le_of_le hx0 hs1.le hkx
    have hsum : (ENNReal.ofReal x + ENNReal.ofReal (x * Real.log s) + T).toReal
        = x + x * Real.log s + τ := by
      rw [ENNReal.toReal_add (by simp [ENNReal.add_ne_top]) hTne,
        ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal hx0, ENNReal.toReal_ofReal (by positivity)]
    have hreal : F.toRealExponent s ≤ x + x * Real.log s + τ := by
      rw [hFval s, ← hsum]
      exact ENNReal.toReal_mono (by simp [ENNReal.add_ne_top, hTne]) hup
    have hlogne : Real.log s ≠ 0 := hlog.ne'
    have hdiv : F.toRealExponent s / Real.log s ≤ x + (x + τ) / Real.log s := by
      have heq : x + (x + τ) / Real.log s = (x * Real.log s + (x + τ)) / Real.log s := by
        field_simp
      rw [heq, div_le_div_iff_of_pos_right hlog]
      linarith [hreal]
    have hfin : F.toRealExponent s / Real.log s < y := lt_of_le_of_lt hdiv hs
    calc ENNReal.ofReal (F.toRealExponent s / Real.log s) < ENNReal.ofReal y :=
          (ENNReal.ofReal_lt_ofReal_iff hy0).2 hfin
      _ = (r₂ : ℝ≥0∞) := by rw [hy, ENNReal.ofReal_coe_nnreal]
      _ < b := hr₂b

end SelfDecomposableExponent

end Hemigroup
