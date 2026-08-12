/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.Sonine
import Mathlib.Analysis.MellinInversion

/-!
# The Mellin data of the profile

Blueprint: `lem:mellin-data` (Lemma 11.2), chapter 11's entry point, together with the
vertical-integrability clause split off as `lem:mellin-vertical` (11.13).

`H(s) = E[e^{-sT₁}]` is the Laplace profile of the construction's kernel `μ_{0,1}`, and this
file proves the two clauses of Lemma 11.2 that Mathlib reaches:

* `mellin_profile` — the identity `H̃(z) = Γ(z) · E[T₁^{-z}]` on the strip `0 < Re z < z_*`;
* `norm_mellin_profile_le` — the bound `|H̃(c+iτ)| ≤ E[T₁^{-c}] · |Γ(c+iτ)|`.

## The hinge, and what it settles

Everything here comes out of one `ℝ≥0∞` computation, `lintegral_lintegral_gamma`:

  `∫∫ s^{c-1} e^{-ts} ds dμ(t) = Γ(c) · E[T₁^{-c}]`.

It is worth isolating because it is *three* statements at once — the Fubini side condition for
the identity, the bound, and the finiteness that vertical integrability would rest on — and
proving it once settles all of them together. What it shows is that the exchange of integrals is
licensed **exactly** by `c < z_*` and by nothing else: the left-hand side is the total mass of
`|integrand|` for the product measure, so joint integrability holds *iff* the right-hand side is
finite, which is `negMoment_ne_top_of_lt_zStar`. This is the shape of chapter 8's
`prop:admissibility-criterion` again — the condition that makes the analysis go through turns out
to be characteristic rather than merely sufficient, and recognising that is what keeps a
hypothesis from being invented.

Carrying it in `ℝ≥0∞` rather than as a Bochner integral is the convention chapter 9 paid for
learning: a Bochner integral reads `0` where the true value is `⊤`, so a side condition stated
with one cannot distinguish "the exchange is licensed" from "the integrand is not integrable".

## What the first clause of (H) is for

`Tendsto F.toRealExponent atTop atTop` — the article's `F(∞) = ∞`, glossed there as "no atom of
the kernels at zero delay" — is used exactly once, in `lawT₁_singleton_zero`, and the gloss is
the whole content: `μ{0} ≤ laplaceL μ s = e^{-F(s)}` for every `s ≥ 0`, and the right-hand side
tends to `0`. Without it the hinge is false, not merely unprovable: at an atom `t = 0` the inner
integral `∫₀^∞ s^{c-1} ds` diverges, while `negMoment` — restricted to `(0,∞)` — does not see
the atom at all.

## Design decisions carried over from the skeleton

* **`T₁` is `F.kernel 0 1`**, the kernel `μ_{0,1}` the construction already produces. No new
  object enters, and in particular the density `φ₁` does not — the chapter's Mellin data is a
  statement about the *law*, so `prop:pair-regularity`'s absolute continuity (ledger A9) is not
  needed even to state it.
* **The profile is the Laplace transform, not the density**, so `H̃` is the Mellin transform of a
  function `ℝ → ℝ` and Mathlib's `mellin` applies directly.
* **Negative moments are `ℝ≥0∞`-valued.** `E[T₁^{-ζ}]` is exactly the quantity that may diverge —
  `z_*` is defined by where it stops being finite — so carrying it in `[0,∞]` keeps `z_*`
  definable without a side condition, as `levyExponent` is carried for the same reason.

## The vertical-integrability clause is not here

`Complex.VerticalIntegrable (mellin H) c` — the clause ledger A12's retirement turns on, because
it is *verbatim* the hypothesis Mathlib's `mellinInv_mellin_eq` asks for — is `lem:mellin-vertical`
and lives in `MellinVertical.lean`. It follows from the bound above and nothing else, but not from
anything Mathlib carries about `Γ`: `Analysis/SpecialFunctions/Stirling.lean` is Stirling's formula
for `n !` only, and there is no bound on `‖Complex.Gamma‖` along a vertical line anywhere in the
library. That was recorded here twice as the reason the clause was blocked, and it was the wrong
inference — integrability needs only quadratic decay, which is the functional equation twice. See
that file.
-/

namespace Hemigroup

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## The Gamma integral, in `ℝ≥0∞`

Mathlib's `Complex.integral_cpow_mul_exp_neg_mul_Ioi` is a Bochner integral, and the hinge needs
the same identity as a `lintegral`. Both readings are used: the real one here, the complex one in
`mellin_profile`. -/

/-- `s ↦ s^{c-1} e^{-ts}` is integrable on `(0,∞)` for `c, t > 0`: Mathlib's Gaussian-integral
lemma at exponent `p = 1`. -/
theorem integrableOn_rpow_mul_exp_neg_mul {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    IntegrableOn (fun s : ℝ => s ^ (c - 1) * Real.exp (-(t * s))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := c - 1) (b := t)
    (by linarith) le_rfl ht
  refine h.congr_fun (fun s _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_one, neg_mul]

/-- The Gamma integral as an `ℝ≥0∞` computation: `∫₀^∞ s^{c-1} e^{-ts} ds = Γ(c) · t^{-c}`. -/
theorem lintegral_ofReal_rpow_mul_exp {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (c - 1) * Real.exp (-(t * s)))
      = ENNReal.ofReal (Real.Gamma c) * ENNReal.ofReal (t ^ (-c)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_rpow_mul_exp_neg_mul hc ht)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun s hs =>
        (mul_nonneg (Real.rpow_nonneg (mem_Ioi.mp hs).le _) (Real.exp_pos _).le))),
    ← ENNReal.ofReal_mul (Real.Gamma_nonneg_of_nonneg hc.le)]
  rw [show (∫ s in Ioi (0 : ℝ), s ^ (c - 1) * Real.exp (-(t * s)))
      = ∫ s : ℝ in Ioi 0, s ^ (c - 1) * Real.exp (-(t * s)) from rfl,
    Real.integral_rpow_mul_exp_neg_mul_Ioi hc ht]
  congr 1
  rw [one_div, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le, mul_comm]

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent)

/-! ## The objects of `lem:mellin-data` -/

/-- The law of `T₁`: the kernel `μ_{0,1}` of the construction. -/
noncomputable def lawT₁ : Measure ℝ := F.kernel 0 1

instance isProbabilityMeasure_lawT₁ : IsProbabilityMeasure F.lawT₁ :=
  isProbabilityMeasure_kernel le_rfl zero_le_one

theorem isCausal_lawT₁ : IsCausal F.lawT₁ := isCausal_kernel le_rfl zero_le_one

/-- **The profile** `H(s) = E[e^{-sT₁}]`, whose Mellin transform the chapter is about. -/
noncomputable def profile (s : ℝ) : ℝ := laplace F.lawT₁ s

/-- **The negative moment** `E[T₁^{-ζ}]`, in `[0,∞]` because divergence is the point. -/
noncomputable def negMoment (ζ : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-ζ)) ∂F.lawT₁

/-- **`z_*`**, the abscissa beyond which the negative moments diverge. -/
noncomputable def zStar : ℝ := sSup {ζ : ℝ | 0 < ζ ∧ F.negMoment ζ ≠ ⊤}

/-- **The standing hypothesis (H)**, `def:standing-hypothesis`: no atom at zero delay, and the
negative moments survive past the first. -/
def StandingHypothesis : Prop :=
  Tendsto F.toRealExponent atTop atTop ∧ 1 < F.zStar

/-- The profile is `e^{-F}`: `increment_zero_left` at `b = 1`. -/
theorem profile_eq_exp_neg {s : ℝ} (hs : 0 ≤ s) :
    F.profile s = Real.exp (-F.toRealExponent s) := by
  rw [profile, lawT₁, laplace_kernel le_rfl zero_le_one hs, increment_zero_left zero_le_one s,
    one_mul, toRealExponent]

/-! ## No atom at zero delay -/

/-- `T₁` has no atom at the origin: the content of the first clause of (H).

The mass at the origin is bounded by the transform at *every* `s ≥ 0`, because the integrand is
`1` there; and `F(s) → ∞` sends the transform `e^{-F(s)}` to `0`. -/
theorem lawT₁_singleton_zero (h : Tendsto F.toRealExponent atTop atTop) :
    F.lawT₁ {(0 : ℝ)} = 0 := by
  have hbound : ∀ s : ℝ, 0 ≤ s →
      F.lawT₁ {(0 : ℝ)} ≤ ENNReal.ofReal (Real.exp (-F.toRealExponent s)) := by
    intro s hs
    have hone : ∀ t ∈ ({0} : Set ℝ), ENNReal.ofReal (Real.exp (-(s * t))) = 1 :=
      fun t ht => by simp [show t = 0 from ht]
    have h1 : ∫⁻ t in ({0} : Set ℝ), ENNReal.ofReal (Real.exp (-(s * t))) ∂F.lawT₁
        = F.lawT₁ {(0 : ℝ)} := by
      rw [setLIntegral_congr_fun (measurableSet_singleton (0 : ℝ)) hone, setLIntegral_const,
        one_mul]
    calc F.lawT₁ {(0 : ℝ)} ≤ laplaceL F.lawT₁ s := by
          rw [← h1]; exact setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (Real.exp (-F.toRealExponent s)) := by
          rw [← F.profile_eq_exp_neg hs, profile, laplace_eq_toReal_laplaceL,
            ENNReal.ofReal_toReal (laplaceL_ne_top_of_causal F.isCausal_lawT₁ hs)]
  have hlim : Tendsto (fun s : ℝ => ENNReal.ofReal (Real.exp (-F.toRealExponent s))) atTop
      (𝓝 0) := by
    have : Tendsto (fun s : ℝ => Real.exp (-F.toRealExponent s)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h)
    simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp this
  exact le_antisymm (ge_of_tendsto hlim (eventually_atTop.mpr ⟨0, fun s hs => hbound s hs⟩))
    bot_le

/-- `T₁` is carried by `(0,∞)`: causality gives `[0,∞)`, and (H) removes the origin. -/
theorem ae_mem_Ioi_lawT₁ (h0 : F.lawT₁ {(0 : ℝ)} = 0) : ∀ᵐ t ∂F.lawT₁, t ∈ Ioi (0 : ℝ) := by
  rw [ae_iff]
  have hset : {t : ℝ | ¬ t ∈ Ioi (0 : ℝ)} = Iio 0 ∪ {0} := by
    ext t
    simp only [mem_setOf_eq, mem_Ioi, not_lt, mem_union, mem_Iio, mem_singleton_iff]
    exact le_iff_lt_or_eq
  rw [hset]
  exact measure_union_null F.isCausal_lawT₁ h0

/-! ## Negative moments below `z_*` -/

/-- The negative moments are finite *downwards*: below `1` the exponent `-c` is dominated by
`-ζ`, above `1` it is bounded by `1`, and `T₁` has unit mass. This is what makes `z_*` an
abscissa rather than merely a supremum. -/
theorem negMoment_ne_top_of_le {c ζ : ℝ} (hc : 0 < c) (hcζ : c ≤ ζ)
    (h : F.negMoment ζ ≠ ⊤) : F.negMoment c ≠ ⊤ := by
  have hpt : ∀ t ∈ Ioi (0 : ℝ),
      ENNReal.ofReal (t ^ (-c)) ≤ ENNReal.ofReal (t ^ (-ζ)) + 1 := by
    intro t ht
    rcases le_total t 1 with h1 | h1
    · exact le_trans (ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow_of_exponent_ge (mem_Ioi.mp ht) h1 (by linarith))) le_self_add
    · refine le_trans (ENNReal.ofReal_le_ofReal
        (Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith))) ?_
      simp
  have hle : F.negMoment c ≤ F.negMoment ζ + 1 := by
    calc F.negMoment c
        ≤ ∫⁻ t in Ioi (0 : ℝ), (ENNReal.ofReal (t ^ (-ζ)) + 1) ∂F.lawT₁ :=
          setLIntegral_mono' measurableSet_Ioi hpt
      _ = F.negMoment ζ + F.lawT₁ (Ioi 0) := by
          rw [lintegral_add_right _ measurable_const, setLIntegral_const, one_mul, negMoment]
      _ ≤ F.negMoment ζ + 1 := by gcongr; exact prob_le_one
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨h, ENNReal.one_ne_top⟩) hle

/-- **`c < z_*` is exactly finiteness of the `c`-th negative moment.**

The empty case is not a formality: `sSup ∅ = 0` in Lean, so `0 < c < z_*` is already enough to
know the defining set is nonempty, and no separate hypothesis is needed. -/
theorem negMoment_ne_top_of_lt_zStar {c : ℝ} (hc : 0 < c) (hc' : c < F.zStar) :
    F.negMoment c ≠ ⊤ := by
  have hne : {ζ : ℝ | 0 < ζ ∧ F.negMoment ζ ≠ ⊤}.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    rw [zStar, hemp, Real.sSup_empty] at hc'
    linarith
  obtain ⟨ζ, hζ, hcζ⟩ := exists_lt_of_lt_csSup hne hc'
  exact F.negMoment_ne_top_of_le hc hcζ.le hζ.2

/-! ## The hinge -/

/-- **The `ℝ≥0∞` computation the chapter turns on**:
`∫∫ s^{c-1} e^{-ts} ds dμ(t) = Γ(c) · E[T₁^{-c}]`.

See the module docstring: this single identity is the Fubini side condition for
`mellin_profile`, the bound of `norm_mellin_profile_le`, and the finiteness underneath vertical
integrability. Its right-hand side is finite iff `c < z_*`, so the exchange below is licensed by
the strip condition and by no further hypothesis. -/
theorem lintegral_lintegral_gamma {c : ℝ} (hc : 0 < c) (h0 : F.lawT₁ {(0 : ℝ)} = 0) :
    ∫⁻ t, (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (c - 1) * Real.exp (-(t * s)))) ∂F.lawT₁
      = ENNReal.ofReal (Real.Gamma c) * F.negMoment c := by
  have hae := F.ae_mem_Ioi_lawT₁ h0
  have hstep : (fun t : ℝ => ∫⁻ s in Ioi (0 : ℝ),
        ENNReal.ofReal (s ^ (c - 1) * Real.exp (-(t * s))))
      =ᵐ[F.lawT₁] fun t : ℝ => ENNReal.ofReal (Real.Gamma c) * ENNReal.ofReal (t ^ (-c)) := by
    filter_upwards [hae] with t ht
    exact lintegral_ofReal_rpow_mul_exp hc (mem_Ioi.mp ht)
  calc ∫⁻ t, (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (c - 1) * Real.exp (-(t * s)))) ∂F.lawT₁
      = ∫⁻ t, ENNReal.ofReal (Real.Gamma c) * ENNReal.ofReal (t ^ (-c)) ∂F.lawT₁ :=
        lintegral_congr_ae hstep
    _ = ENNReal.ofReal (Real.Gamma c) * ∫⁻ t, ENNReal.ofReal (t ^ (-c)) ∂F.lawT₁ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (Real.Gamma c) * F.negMoment c := by
        rw [negMoment, Measure.restrict_eq_self_of_ae_mem hae]

/-- Joint integrability of `(s,t) ↦ s^{z-1} e^{-ts}` for `volume|_(0,∞) ⊗ lawT₁`: the Fubini side
condition, and the hinge is all of it. Tonelli turns the total mass of the absolute value into
the double integral above, whose value is `Γ(Re z) · E[T₁^{-Re z}]`. -/
theorem integrable_mellin_laplace {z : ℂ} (hz : 0 < z.re) (hz' : z.re < F.zStar)
    (h0 : F.lawT₁ {(0 : ℝ)} = 0) :
    Integrable (Function.uncurry fun s t : ℝ =>
        (s : ℂ) ^ (z - 1) * Complex.exp (-((t : ℂ) * (s : ℂ))))
      ((volume.restrict (Ioi 0)).prod F.lawT₁) := by
  have hmeas : Measurable (Function.uncurry fun s t : ℝ =>
      (s : ℂ) ^ (z - 1) * Complex.exp (-((t : ℂ) * (s : ℂ)))) := by
    unfold Function.uncurry
    fun_prop
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod_symm _ (hmeas.enorm).aemeasurable]
  have hcongr : ∀ t : ℝ,
      (∫⁻ s, ‖Function.uncurry (fun s t : ℝ =>
          (s : ℂ) ^ (z - 1) * Complex.exp (-((t : ℂ) * (s : ℂ)))) (s, t)‖ₑ
        ∂(volume.restrict (Ioi (0 : ℝ))))
        = ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (z.re - 1) * Real.exp (-(t * s))) := by
    intro t
    refine setLIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
    have hs' : (0 : ℝ) < s := mem_Ioi.mp hs
    have h1 : ‖(s : ℂ) ^ (z - 1)‖ = s ^ (z.re - 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hs']; simp
    have h2 : ‖Complex.exp (-((t : ℂ) * (s : ℂ)))‖ = Real.exp (-(t * s)) := by
      rw [Complex.norm_exp]; simp
    rw [Function.uncurry_apply_pair, ← ofReal_norm, norm_mul, h1, h2]
  rw [lintegral_congr hcongr, F.lintegral_lintegral_gamma (by linarith) h0]
  exact lt_top_iff_ne_top.mpr
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (F.negMoment_ne_top_of_lt_zStar hz hz'))

/-! ## `lem:mellin-data` -/

/-- **`lem:mellin-data`**, the identity: `H̃(z) = Γ(z) · E[T₁^{-z}]` on the strip
`0 < Re z < z_*`.

Fubini on `∫₀^∞ s^{z-1} ∫ e^{-st} dμ(t) ds`, exchanged to `∫ (∫₀^∞ s^{z-1}e^{-st} ds) dμ(t)`.
The inner integral is Mathlib's `Complex.integral_cpow_mul_exp_neg_mul_Ioi`, which evaluates to
`(1/t)^z Γ(z)`, so no substitution is needed and the Gamma function enters as Mathlib's rather
than as a definition of ours. The exchange is licensed by `integrable_mellin_laplace`, i.e. by
the hinge, i.e. by `Re z < z_*`. -/
theorem mellin_profile (hH : F.StandingHypothesis) {z : ℂ} (hz : 0 < z.re)
    (hz' : z.re < F.zStar) :
    mellin (fun s => (F.profile s : ℂ)) z
      = Complex.Gamma z * ∫ t, (t : ℂ) ^ (-z) ∂F.lawT₁ := by
  have h0 := F.lawT₁_singleton_zero hH.1
  have hae := F.ae_mem_Ioi_lawT₁ h0
  -- The Mellin integrand is an inner `μ`-integral.
  have hinner : ∀ s : ℝ, (s : ℂ) ^ (z - 1) • ((F.profile s : ℝ) : ℂ)
      = ∫ t, (s : ℂ) ^ (z - 1) * Complex.exp (-((t : ℂ) * (s : ℂ))) ∂F.lawT₁ := by
    intro s
    have hprof : ((F.profile s : ℝ) : ℂ)
        = ∫ t, Complex.exp (-((t : ℂ) * (s : ℂ))) ∂F.lawT₁ := by
      have hof : ((∫ t, Real.exp (-(s * t)) ∂F.lawT₁ : ℝ) : ℂ)
          = ∫ t, ((Real.exp (-(s * t)) : ℝ) : ℂ) ∂F.lawT₁ := (integral_ofReal (𝕜 := ℂ)).symm
      rw [profile, laplace, hof]
      refine integral_congr_ae (.of_forall fun t => ?_)
      dsimp only
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    rw [integral_const_mul, smul_eq_mul, hprof]
  -- The inner Gamma integral, for `t > 0`.
  have hgamma : ∀ t ∈ Ioi (0 : ℝ),
      (∫ s in Ioi (0 : ℝ), (s : ℂ) ^ (z - 1) * Complex.exp (-((t : ℂ) * (s : ℂ))))
        = (t : ℂ) ^ (-z) * Complex.Gamma z := by
    intro t ht
    have ht' : (0 : ℝ) < t := mem_Ioi.mp ht
    rw [Complex.integral_cpow_mul_exp_neg_mul_Ioi hz ht']
    congr 1
    rw [one_div, Complex.inv_cpow _ _ (by
      rw [Complex.arg_ofReal_of_nonneg ht'.le]; exact Real.pi_ne_zero.symm),
      ← Complex.cpow_neg]
  calc mellin (fun s => (F.profile s : ℂ)) z
      = ∫ s in Ioi (0 : ℝ), ∫ t, (s : ℂ) ^ (z - 1) * Complex.exp (-((t : ℂ) * (s : ℂ)))
          ∂F.lawT₁ := by
        rw [mellin]
        exact setIntegral_congr_fun measurableSet_Ioi (fun s _ => hinner s)
    _ = ∫ t, (∫ s in Ioi (0 : ℝ), (s : ℂ) ^ (z - 1) * Complex.exp (-((t : ℂ) * (s : ℂ))))
          ∂F.lawT₁ :=
        integral_integral_swap (F.integrable_mellin_laplace hz hz' h0)
    _ = ∫ t, (t : ℂ) ^ (-z) * Complex.Gamma z ∂F.lawT₁ := by
        refine integral_congr_ae ?_
        filter_upwards [hae] with t ht
        exact hgamma t ht
    _ = Complex.Gamma z * ∫ t, (t : ℂ) ^ (-z) ∂F.lawT₁ := by
        rw [integral_mul_const, mul_comm]

/-- **`lem:mellin-data`**, convergence: the Mellin integral of the profile converges absolutely on
the strip.

The hinge again, read the other way round. `integrable_mellin_laplace` is joint integrability for
the product measure; Fubini's `Integrable.integral_prod_left` projects it onto the `s`-marginal,
and the inner `μ`-integral *is* `s^{z-1}H(s)`. So this costs nothing beyond what the identity
already paid for, and it is `MellinConvergent` verbatim — the first of the two hypotheses
`mellinInv_mellin_eq` asks for, the other being `lem:mellin-vertical`. -/
theorem mellinConvergent_profile (hH : F.StandingHypothesis) {z : ℂ} (hz : 0 < z.re)
    (hz' : z.re < F.zStar) : MellinConvergent (fun s => (F.profile s : ℂ)) z := by
  have h0 := F.lawT₁_singleton_zero hH.1
  have hprod := (F.integrable_mellin_laplace hz hz' h0).integral_prod_left
  refine hprod.congr (.of_forall fun s => ?_)
  have hprof : ((F.profile s : ℝ) : ℂ) = ∫ t, Complex.exp (-((t : ℂ) * (s : ℂ))) ∂F.lawT₁ := by
    have hof : ((∫ t, Real.exp (-(s * t)) ∂F.lawT₁ : ℝ) : ℂ)
        = ∫ t, ((Real.exp (-(s * t)) : ℝ) : ℂ) ∂F.lawT₁ := (integral_ofReal (𝕜 := ℂ)).symm
    rw [profile, laplace, hof]
    refine integral_congr_ae (.of_forall fun t => ?_)
    dsimp only
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  dsimp only [Function.uncurry]
  rw [integral_const_mul, ← hprof, smul_eq_mul]

/-- `E[T₁^{-c}]` as a Bochner integral. The two readings agree because `T₁ > 0` almost surely. -/
theorem integral_rpow_neg_eq_negMoment {c : ℝ} (h0 : F.lawT₁ {(0 : ℝ)} = 0) :
    ∫ t, t ^ (-c) ∂F.lawT₁ = (F.negMoment c).toReal := by
  have hae := F.ae_mem_Ioi_lawT₁ h0
  rw [integral_eq_lintegral_of_nonneg_ae
      (by filter_upwards [hae] with t ht using Real.rpow_nonneg (mem_Ioi.mp ht).le _)
      (by fun_prop), negMoment, Measure.restrict_eq_self_of_ae_mem hae]

/-- **`lem:mellin-data`**, the bound: `|H̃(c+iτ)| ≤ E[T₁^{-c}] · |Γ(c+iτ)|`.

Immediate from the identity, since `|t^{-(c+iτ)}| = t^{-c}` for `t > 0`. -/
theorem norm_mellin_profile_le (hH : F.StandingHypothesis) {c : ℝ} (hc : 0 < c)
    (hc' : c < F.zStar) (τ : ℝ) :
    ‖mellin (fun s => (F.profile s : ℂ)) (c + τ * Complex.I)‖
      ≤ (F.negMoment c).toReal * ‖Complex.Gamma (c + τ * Complex.I)‖ := by
  have h0 := F.lawT₁_singleton_zero hH.1
  have hae := F.ae_mem_Ioi_lawT₁ h0
  set z : ℂ := (c : ℂ) + τ * Complex.I with hzdef
  have hre : z.re = c := by simp [hzdef]
  have hnorm : (fun t : ℝ => ‖(t : ℂ) ^ (-z)‖) =ᵐ[F.lawT₁] fun t : ℝ => t ^ (-c) := by
    filter_upwards [hae] with t ht
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (mem_Ioi.mp ht), Complex.neg_re, hre]
  have key : ‖∫ t, (t : ℂ) ^ (-z) ∂F.lawT₁‖ ≤ (F.negMoment c).toReal := by
    calc ‖∫ t, (t : ℂ) ^ (-z) ∂F.lawT₁‖
        ≤ ∫ t, ‖(t : ℂ) ^ (-z)‖ ∂F.lawT₁ := norm_integral_le_integral_norm _
      _ = ∫ t, t ^ (-c) ∂F.lawT₁ := integral_congr_ae hnorm
      _ = (F.negMoment c).toReal := F.integral_rpow_neg_eq_negMoment h0
  rw [F.mellin_profile hH (by rw [hre]; exact hc) (by rw [hre]; exact hc'), norm_mul, mul_comm]
  gcongr

end SelfDecomposableExponent

end Hemigroup
