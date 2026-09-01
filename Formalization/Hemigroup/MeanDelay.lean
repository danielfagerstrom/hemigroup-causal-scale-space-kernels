/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Hemigroup.Ein
import Hemigroup.MemoryFractional

/-!
# `prop:moments`: the mean delay and the influence curve

Blueprint: `prop:moments` (Proposition 8.4). `E T_x = x F'(0+) = x(b₀ + ∫₀^∞ k)`, finite iff `k`
is integrable at infinity, and the influence curve is linear in `x`.

## `F'(0+)` is `[0,∞]`-valued, and that is the statement rather than a convenience

The proposition's whole second clause is about when the mean is *infinite*, so the mean rate is
defined in `ℝ≥0∞` and the identity is stated there. No hypothesis of finiteness appears anywhere
below; where the blueprint says "finite if and only if", the Lean statement is
`meanRate ≠ ⊤ ↔ IntegrableOn k (Ioi 1)` and both sides may fail.

## The influence curve is linear because `μ_{0,x}` is the law of `x T₁`

The blueprint reaches linearity from the identity — `E T_x = xF'(0+)` is linear in `x` because the
right-hand side is. In Lean it is cheaper and comes first: `kernel_zero_eq_map_lawT₁`, proved for
chapter 11, says `μ_{0,x}` is the pushforward of `μ_{0,1}` under `t ↦ xt`, so *every* moment scales
and the mean identity is only ever needed at `x = 1`. That splits the proposition cleanly: the
scaling is a change of variables, and the Tauberian step `E T₁ = F'(0+)` is the rest.
-/

namespace Hemigroup

open MeasureTheory Set Filter

open scoped ENNReal Topology

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent)

/-- **`F'(0+) = b₀ + ∫₀^∞ k(t) dt`**, the mean rate, valued in `[0,∞]`. -/
noncomputable def meanRate : ℝ≥0∞ :=
  ENNReal.ofReal F.b₀ + ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (F.k t)

/-- **The mean rate is finite exactly when `k` is integrable at infinity.**

The other end costs nothing: `∫₀¹ k < ∞` is forced by the structure's own `ne_top` field
(`integrableOn_k`) and not assumed, so the only condition is at infinity — which is what the
blueprint asserts. -/
theorem meanRate_ne_top_iff : F.meanRate ≠ ⊤ ↔ IntegrableOn F.k (Ioi 1) := by
  have hnn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ F.k t := fun t ht => F.k_nonneg t ht
  have hsplit : (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (F.k t))
      = (∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (F.k t))
        + ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (F.k t) := by
    rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1),
      lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same]
  have hlow : (∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (F.k t)) ≠ ⊤ :=
    F.lintegral_ofReal_k_Ioc_ne_top
  constructor
  · intro h
    refine integrableOn_of_lintegral_ofReal_ne_top
      ((F.aemeasurable_k fun t ht => lt_trans zero_lt_one (mem_Ioi.mp ht)).aestronglyMeasurable)
      ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun t ht =>
        hnn t (mem_Ioi.mpr (lt_trans zero_lt_one (mem_Ioi.mp ht)))))
    rw [meanRate, hsplit] at h
    exact (ENNReal.add_ne_top.mp ((ENNReal.add_ne_top.mp h).2)).2
  · intro h
    have hhigh : (∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (F.k t)) ≠ ⊤ := by
      have h2 := h.2
      rw [hasFiniteIntegral_iff_enorm] at h2
      refine ne_of_lt (lt_of_le_of_lt (lintegral_mono_ae ?_) h2)
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun t ht => ?_)
      rw [Real.enorm_eq_ofReal (hnn t (mem_Ioi.mpr (lt_trans zero_lt_one (mem_Ioi.mp ht))))]
    rw [meanRate, hsplit]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.add_ne_top.mpr ⟨hlow, hhigh⟩⟩

/-- **The influence curve is linear**: every scale's delay law is the unit law dilated, so the
mean delay scales exactly.

This is `kernel_zero_eq_map_lawT₁` and a change of variables, and it holds whether or not the mean
is finite — which is why it is separated from the identity `E T₁ = F'(0+)` rather than deduced
from it. -/
theorem lintegral_id_kernel_zero {x : ℝ} (hx : 0 < x) :
    ∫⁻ t, ENNReal.ofReal t ∂(F.kernel 0 x)
      = ENNReal.ofReal x * ∫⁻ t, ENNReal.ofReal t ∂F.lawT₁ := by
  rw [F.kernel_zero_eq_map_lawT₁ hx,
    lintegral_map (by fun_prop) (measurable_const_mul x),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact lintegral_congr fun t => ENNReal.ofReal_mul hx.le

/-! ## `E T₁ = F'(0+)`: two monotone limits and a squeeze

The blueprint's proof is "differentiating the transform at the origin". In `[0,∞]` there is no
differentiation to do and no Tauberian theorem to cite, because the difference quotient
`(1 - e^{-st})/s` is *monotone* in `s` — that is `antitoneOn_einIntegrand`, and it is what turns
the whole argument into monotone convergence applied twice:

* on the law, `∫ t \,d\mu_{0,1}` is the increasing limit of `\int (1 - e^{-s_nt})/s_n \,d\mu_{0,1}`,
  which the transform evaluates as `(1 - e^{-F(s_n)})/s_n`;
* inside the Lévy integral, `F(s)/s = b_0 + \int einIntegrand(st)k(t)\,dt` increases to
  `meanRate`.

What joins the two is the squeeze `we^{-w} \le 1 - e^{-w} \le w` at `w = F(s_n) \to 0`. It is the
only step that is not monotone convergence, and it costs no finiteness hypothesis: the lower bound
is multiplied by a factor tending to `1`, and `ENNReal.Tendsto.mul` at a limit of `1` has no side
condition, so the `⊤` case — the one the proposition's second clause exists to describe — needs no
separate treatment.
-/

/-- The scales the difference quotient is sampled at: `s_n = 1/(n+1)`. Any positive nonincreasing
null sequence would do; this one is at hand. -/
private noncomputable def sampleScale (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

private theorem sampleScale_pos (n : ℕ) : 0 < sampleScale n := by
  rw [sampleScale]
  positivity

private theorem antitone_sampleScale : Antitone sampleScale := by
  intro n m hnm
  have h : ((n : ℝ) + 1) ≤ (m : ℝ) + 1 := by
    have : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hnm
    linarith
  exact one_div_le_one_div_of_le (by positivity) h

private theorem tendsto_sampleScale : Tendsto sampleScale atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- **The transform of the law**, in `ℝ≥0∞`: `E[e^{-sT₁}] = e^{-F(s)}`. `profile_eq_exp_neg` with
the passage between the two readings of the transform done once, here, rather than at each use. -/
theorem laplaceL_lawT₁ {s : ℝ} (hs : 0 ≤ s) :
    laplaceL F.lawT₁ s = ENNReal.ofReal (Real.exp (-F.toRealExponent s)) := by
  rw [← F.profile_eq_exp_neg hs, profile, laplace_eq_toReal_laplaceL,
    ENNReal.ofReal_toReal (laplaceL_ne_top_of_causal F.isCausal_lawT₁ hs)]

/-- The exponent read back from its real reading; `ne_top` is what makes this available with no
hypothesis beyond `s ≥ 0`. -/
theorem exponent_eq_ofReal {s : ℝ} (hs : 0 ≤ s) :
    F.exponent s = ENNReal.ofReal (F.toRealExponent s) :=
  (ENNReal.ofReal_toReal (F.ne_top s hs)).symm

/-- **The difference quotient of the law is the difference quotient of the transform**:
`∫ (1 - e^{-st})/s \,d\mu_{0,1} = (1 - e^{-F(s)})/s`.

The one place the transform enters at all. Everything else in the identity is monotone
convergence. -/
theorem lintegral_quotient_lawT₁ {s : ℝ} (hs : 0 < s) :
    ∫⁻ t, ENNReal.ofReal (t * einIntegrand (s * t)) ∂F.lawT₁
      = ENNReal.ofReal (s⁻¹ * (1 - Real.exp (-F.toRealExponent s))) := by
  have hpt : ∀ t : ℝ, ENNReal.ofReal (t * einIntegrand (s * t))
      = ENNReal.ofReal s⁻¹ * ENNReal.ofReal (1 - Real.exp (-(s * t))) := by
    intro t
    rw [← quotient_eq_mul_einIntegrand s t,
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ s⁻¹), div_eq_inv_mul]
  have hsub : ∀ t : ℝ, ENNReal.ofReal (1 - Real.exp (-(s * t)))
      = 1 - ENNReal.ofReal (Real.exp (-(s * t))) := by
    intro t
    rw [ENNReal.ofReal_sub _ (Real.exp_pos _).le, ENNReal.ofReal_one]
  have hle : (fun t => ENNReal.ofReal (Real.exp (-(s * t)))) ≤ᵐ[F.lawT₁] fun _ => 1 := by
    filter_upwards [F.isCausal_lawT₁.ae_nonneg] with t ht
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr (by nlinarith))
  have hfin : ∫⁻ t, ENNReal.ofReal (Real.exp (-(s * t))) ∂F.lawT₁ ≠ ⊤ :=
    laplaceL_ne_top_of_causal F.isCausal_lawT₁ hs.le
  calc ∫⁻ t, ENNReal.ofReal (t * einIntegrand (s * t)) ∂F.lawT₁
      = ∫⁻ t, ENNReal.ofReal s⁻¹ * ENNReal.ofReal (1 - Real.exp (-(s * t))) ∂F.lawT₁ :=
        lintegral_congr hpt
    _ = ENNReal.ofReal s⁻¹ * ∫⁻ t, ENNReal.ofReal (1 - Real.exp (-(s * t))) ∂F.lawT₁ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal s⁻¹
          * ∫⁻ t, (1 : ℝ≥0∞) - ENNReal.ofReal (Real.exp (-(s * t))) ∂F.lawT₁ := by
        rw [lintegral_congr hsub]
    _ = ENNReal.ofReal s⁻¹
          * ((∫⁻ _, (1 : ℝ≥0∞) ∂F.lawT₁)
              - ∫⁻ t, ENNReal.ofReal (Real.exp (-(s * t))) ∂F.lawT₁) := by
        rw [lintegral_sub (by fun_prop) hfin hle]
    _ = ENNReal.ofReal s⁻¹ * (1 - ENNReal.ofReal (Real.exp (-F.toRealExponent s))) := by
        rw [← F.laplaceL_lawT₁ hs.le, laplaceL]
        simp
    _ = ENNReal.ofReal (s⁻¹ * (1 - Real.exp (-F.toRealExponent s))) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (Real.exp_pos _).le,
          ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ s⁻¹)]

/-- **Monotone convergence on the law**: the mean is the increasing limit of the difference
quotients. -/
theorem tendsto_lintegral_quotient_lawT₁ {s : ℕ → ℝ} (hpos : ∀ n, 0 < s n) (hanti : Antitone s)
    (hlim : Tendsto s atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ t, ENNReal.ofReal (t * einIntegrand (s n * t)) ∂F.lawT₁) atTop
      (𝓝 (∫⁻ t, ENNReal.ofReal t ∂F.lawT₁)) := by
  refine lintegral_tendsto_of_tendsto_of_monotone (fun n => ?_) ?_ ?_
  · exact ((measurable_id.mul
      (measurable_einIntegrand.comp (measurable_id.const_mul (s n)))).ennreal_ofReal).aemeasurable
  · filter_upwards [F.isCausal_lawT₁.ae_nonneg] with t ht
    intro n m hnm
    exact ENNReal.ofReal_le_ofReal (mul_einIntegrand_le_of_le ht (hpos m) (hanti hnm))
  · filter_upwards [F.isCausal_lawT₁.ae_nonneg] with t ht
    exact ENNReal.tendsto_ofReal (tendsto_mul_einIntegrand ht hpos hlim)

/-- **The difference quotient of the exponent**, termwise: `F(s)/s = b₀ + ∫ einIntegrand(su)k(u)du`.

The dilation `(1 - e^{-su})/u = s·einIntegrand(su)` is `dilate_einIntegrand`, and dividing by `s`
is what leaves an integrand that increases to `k` as `s ↓ 0`. -/
theorem ofReal_inv_mul_exponent {s : ℝ} (hs : 0 < s) :
    ENNReal.ofReal s⁻¹ * F.exponent s
      = ENNReal.ofReal F.b₀
        + ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (einIntegrand (s * u) * F.k u) := by
  rw [exponent, levyExponentD, mul_add]
  congr 1
  · rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ s⁻¹)]
    congr 1
    field_simp
  · rw [levyJump, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ s⁻¹)]
    congr 1
    calc s⁻¹ * ((1 - Real.exp (-(s * u))) * F.k u / u)
        = s⁻¹ * (((1 - Real.exp (-(s * u))) / u) * F.k u) := by ring
      _ = s⁻¹ * (s * einIntegrand (s * u) * F.k u) := by rw [dilate_einIntegrand]
      _ = einIntegrand (s * u) * F.k u := by field_simp

/-- **Monotone convergence inside the Lévy integral** — the clause the node's annotation names,
"monotone convergence in (7.1) and nothing else". -/
theorem tendsto_ofReal_inv_mul_exponent {s : ℕ → ℝ} (hpos : ∀ n, 0 < s n) (hanti : Antitone s)
    (hlim : Tendsto s atTop (𝓝 0)) :
    Tendsto (fun n => ENNReal.ofReal (s n)⁻¹ * F.exponent (s n)) atTop (𝓝 F.meanRate) := by
  have hjump : Tendsto (fun n => ∫⁻ u in Ioi (0 : ℝ),
      ENNReal.ofReal (einIntegrand (s n * u) * F.k u)) atTop
      (𝓝 (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (F.k u))) := by
    refine lintegral_tendsto_of_tendsto_of_monotone (fun n => ?_) ?_ ?_
    · exact (((measurable_einIntegrand.comp
        (measurable_id.const_mul (s n))).aemeasurable.mul
          (F.aemeasurable_k subset_rfl)).ennreal_ofReal)
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun u hu => ?_)
      intro n m hnm
      have hu' : (0 : ℝ) < u := mem_Ioi.mp hu
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (F.k_nonneg u hu))
      exact antitoneOn_einIntegrand (mem_Ioi.mpr (mul_pos (hpos m) hu'))
        (mem_Ioi.mpr (mul_pos (hpos n) hu')) (by nlinarith [hanti hnm])
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun u hu => ?_)
      have hu' : (0 : ℝ) < u := mem_Ioi.mp hu
      exact ENNReal.tendsto_ofReal (by
        simpa using (tendsto_einIntegrand_mul hu' hpos hlim).mul_const (F.k u))
  have := hjump.const_add (ENNReal.ofReal F.b₀)
  refine this.congr fun n => (F.ofReal_inv_mul_exponent (hpos n)).symm

/-- **`E T₁ = F'(0+)`**, in `[0,∞]` and with no finiteness hypothesis. -/
theorem lintegral_id_lawT₁ : ∫⁻ t, ENNReal.ofReal t ∂F.lawT₁ = F.meanRate := by
  have hpos := sampleScale_pos
  have hanti := antitone_sampleScale
  have hlim := tendsto_sampleScale
  have hA := F.tendsto_lintegral_quotient_lawT₁ hpos hanti hlim
  have hB := F.tendsto_ofReal_inv_mul_exponent hpos hanti hlim
  have hAeq : ∀ n, ∫⁻ t, ENNReal.ofReal (t * einIntegrand (sampleScale n * t)) ∂F.lawT₁
      = ENNReal.ofReal ((sampleScale n)⁻¹
          * (1 - Real.exp (-F.toRealExponent (sampleScale n)))) :=
    fun n => F.lintegral_quotient_lawT₁ (hpos n)
  have hBeq : ∀ n, ENNReal.ofReal (sampleScale n)⁻¹ * F.exponent (sampleScale n)
      = ENNReal.ofReal ((sampleScale n)⁻¹ * F.toRealExponent (sampleScale n)) := fun n => by
    rw [F.exponent_eq_ofReal (hpos n).le,
      ← ENNReal.ofReal_mul (inv_nonneg.mpr (hpos n).le)]
  -- `F(s_n) → 0`, so the factor separating the two quotients tends to `1`.
  have hw : Tendsto (fun n => F.toRealExponent (sampleScale n)) atTop (𝓝 0) := by
    have hin : Tendsto sampleScale atTop (𝓝[>] (0 : ℝ)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hlim
        (Eventually.of_forall fun n => hpos n)
    simpa [Function.comp_def] using F.tendsto_toRealExponent_nhdsGT_zero.comp hin
  have hc : Tendsto (fun n => ENNReal.ofReal (Real.exp (-F.toRealExponent (sampleScale n))))
      atTop (𝓝 1) := by
    have h1 : Tendsto (fun n => Real.exp (-F.toRealExponent (sampleScale n))) atTop (𝓝 1) := by
      have hn : Tendsto (fun n => -F.toRealExponent (sampleScale n)) atTop (𝓝 0) := by
        simpa using hw.neg
      simpa [Function.comp_def] using (Real.continuous_exp.tendsto 0).comp hn
    simpa using ENNReal.tendsto_ofReal h1
  refine le_antisymm ?_ ?_
  · -- `1 - e^{-w} ≤ w`
    refine le_of_tendsto_of_tendsto' hA hB fun n => ?_
    rw [hAeq n, hBeq n]
    exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (one_sub_exp_neg_le _) (inv_nonneg.mpr (hpos n).le))
  · -- `w e^{-w} ≤ 1 - e^{-w}`, and the factor `e^{-w}` disappears in the limit
    have hBc : Tendsto (fun n => ENNReal.ofReal (sampleScale n)⁻¹ * F.exponent (sampleScale n)
        * ENNReal.ofReal (Real.exp (-F.toRealExponent (sampleScale n)))) atTop (𝓝 F.meanRate) := by
      have := ENNReal.Tendsto.mul hB (Or.inr ENNReal.one_ne_top) hc (Or.inl one_ne_zero)
      rwa [mul_one] at this
    refine le_of_tendsto_of_tendsto' hBc hA fun n => ?_
    have hwnn : 0 ≤ F.toRealExponent (sampleScale n) := ENNReal.toReal_nonneg
    rw [hAeq n, hBeq n,
      ← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.mpr (hpos n).le) hwnn)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hkey : F.toRealExponent (sampleScale n)
          * Real.exp (-F.toRealExponent (sampleScale n))
        ≤ 1 - Real.exp (-F.toRealExponent (sampleScale n)) := by
      have h := mul_le_mul_of_nonneg_right
        (Real.add_one_le_exp (F.toRealExponent (sampleScale n)))
        (Real.exp_pos (-F.toRealExponent (sampleScale n))).le
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h
      nlinarith [h]
    calc (sampleScale n)⁻¹ * F.toRealExponent (sampleScale n)
            * Real.exp (-F.toRealExponent (sampleScale n))
        = (sampleScale n)⁻¹ * (F.toRealExponent (sampleScale n)
            * Real.exp (-F.toRealExponent (sampleScale n))) := by ring
      _ ≤ (sampleScale n)⁻¹ * (1 - Real.exp (-F.toRealExponent (sampleScale n))) :=
          mul_le_mul_of_nonneg_left hkey (inv_nonneg.mpr (hpos n).le)

end SelfDecomposableExponent

/-- **`prop:moments` (Proposition 8.4).** The mean delay is `x F'(0+)`, so the influence curve is
exactly linear in the canonical gauge; and it is finite exactly when `k` is integrable at
infinity.

The two clauses are independent: the first is `kernel_zero_eq_map_lawT₁` and a change of
variables, needing the identity `E T₁ = F'(0+)` only at `x = 1`, where the blueprint reads
linearity off the identity at every `x`. -/
theorem moments (F : SelfDecomposableExponent) :
    (∀ x : ℝ, 0 < x →
        ∫⁻ t, ENNReal.ofReal t ∂(F.kernel 0 x) = ENNReal.ofReal x * F.meanRate) ∧
      (F.meanRate ≠ ⊤ ↔ IntegrableOn F.k (Ioi 1)) :=
  ⟨fun _ hx => by rw [F.lintegral_id_kernel_zero hx, F.lintegral_id_lawT₁],
   F.meanRate_ne_top_iff⟩

end Hemigroup
