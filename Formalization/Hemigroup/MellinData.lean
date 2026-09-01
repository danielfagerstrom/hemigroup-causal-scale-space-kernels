/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the MIT license as described in the file LICENSES/MIT.txt.
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

## Stated for a measure, not for `T₁`

Nothing in the exchange is about `T₁`. What it needs of the measure is that it charges only
`(0,∞)`, where the inner Gamma integral converges, and that the negative moment in play is
finite, which is what licenses the exchange. So the three steps below --- the hinge, the Fubini
side condition, and the identity --- are stated for an arbitrary `ν` carried by the half-line and
instantiated at `lawT₁` afterwards.

That is not generality for its own sake: chapter 12 spends it. `∂ₓ^j H(sx) = (-s)^j ∫ tʲ e^{-sxt}
dμ(t)` says that the `j`-th derivative of the profile is again the Laplace transform of a measure
--- the *weighted* measure `tʲ μ(dt)` --- so the Gamma-integral computation applies to it
verbatim rather than being restated with a weight carried through it. The pointwise inner step
`lintegral_ofReal_rpow_mul_exp` needed nothing at all, having been stated for an arbitrary
`t > 0` from the start.

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

/-! ## The hinge, for a measure carried by the open half-line

See the module docstring: `lem:mellin-data` is a statement about a measure on `(0,∞)` with a
finite negative moment, and `lawT₁` enters only by being one. Chapter 12 applies the same three
steps to `tʲ μ(dt)`. -/

section OfMeasure

variable {ν : Measure ℝ}

/-- **The `ℝ≥0∞` hinge**, for any measure carried by `(0,∞)`:
`∫∫ s^{c-1} e^{-ts} ds dν(t) = Γ(c) · ∫ t^{-c} dν(t)`. -/
theorem lintegral_lintegral_gamma_of_ae_mem_Ioi (hν : ∀ᵐ t ∂ν, t ∈ Ioi (0 : ℝ)) {c : ℝ}
    (hc : 0 < c) :
    ∫⁻ t, (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (c - 1) * Real.exp (-(t * s)))) ∂ν
      = ENNReal.ofReal (Real.Gamma c) * ∫⁻ t, ENNReal.ofReal (t ^ (-c)) ∂ν := by
  have hstep : (fun t : ℝ => ∫⁻ s in Ioi (0 : ℝ),
        ENNReal.ofReal (s ^ (c - 1) * Real.exp (-(t * s))))
      =ᵐ[ν] fun t : ℝ => ENNReal.ofReal (Real.Gamma c) * ENNReal.ofReal (t ^ (-c)) := by
    filter_upwards [hν] with t ht
    exact lintegral_ofReal_rpow_mul_exp hc (mem_Ioi.mp ht)
  rw [lintegral_congr_ae hstep, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- Joint integrability of `(s,t) ↦ s^{z-1} e^{-ts}` for `volume|_(0,∞) ⊗ ν`: the Fubini side
condition, and the hinge is all of it. Tonelli turns the total mass of the absolute value into
the double integral above, whose value is `Γ(Re z)` times the `Re z`-th negative moment of `ν`. -/
theorem integrable_mellin_laplace_of_ae_mem_Ioi [SFinite ν] (hν : ∀ᵐ t ∂ν, t ∈ Ioi (0 : ℝ))
    {z : ℂ} (hz : 0 < z.re) (hfin : ∫⁻ t, ENNReal.ofReal (t ^ (-z.re)) ∂ν ≠ ⊤) :
    Integrable (Function.uncurry fun s t : ℝ =>
        (s : ℂ) ^ (z - 1) * Complex.exp (-((t : ℂ) * (s : ℂ))))
      ((volume.restrict (Ioi 0)).prod ν) := by
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
  rw [lintegral_congr hcongr, lintegral_lintegral_gamma_of_ae_mem_Ioi hν hz]
  exact lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin)

/-- The Mellin integrand of a Laplace transform is an inner `ν`-integral. -/
theorem ofReal_laplace_eq_integral (ν : Measure ℝ) (s : ℝ) :
    ((laplace ν s : ℝ) : ℂ) = ∫ t, Complex.exp (-((t : ℂ) * (s : ℂ))) ∂ν := by
  have hof : ((∫ t, Real.exp (-(s * t)) ∂ν : ℝ) : ℂ)
      = ∫ t, ((Real.exp (-(s * t)) : ℝ) : ℂ) ∂ν := (integral_ofReal (𝕜 := ℂ)).symm
  rw [laplace, hof]
  refine integral_congr_ae (.of_forall fun t => ?_)
  dsimp only
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- **`lem:mellin-data`'s identity, for a measure carried by `(0,∞)`**:
`M[laplace ν](z) = Γ(z) · ∫ t^{-z} dν(t)`.

Fubini on `∫₀^∞ s^{z-1} ∫ e^{-st} dν(t) ds`, exchanged to `∫ (∫₀^∞ s^{z-1}e^{-st} ds) dν(t)`. The
inner integral is Mathlib's `Complex.integral_cpow_mul_exp_neg_mul_Ioi`, which evaluates to
`(1/t)^z Γ(z)`, so no substitution is needed and the Gamma function enters as Mathlib's rather
than as a definition of ours. -/
theorem mellin_laplace_of_ae_mem_Ioi [SFinite ν] (hν : ∀ᵐ t ∂ν, t ∈ Ioi (0 : ℝ)) {z : ℂ}
    (hz : 0 < z.re) (hfin : ∫⁻ t, ENNReal.ofReal (t ^ (-z.re)) ∂ν ≠ ⊤) :
    mellin (fun s => (laplace ν s : ℂ)) z = Complex.Gamma z * ∫ t, (t : ℂ) ^ (-z) ∂ν := by
  have hinner : ∀ s : ℝ, (s : ℂ) ^ (z - 1) • ((laplace ν s : ℝ) : ℂ)
      = ∫ t, (s : ℂ) ^ (z - 1) * Complex.exp (-((t : ℂ) * (s : ℂ))) ∂ν := by
    intro s
    rw [integral_const_mul, smul_eq_mul, ofReal_laplace_eq_integral]
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
  calc mellin (fun s => (laplace ν s : ℂ)) z
      = ∫ s in Ioi (0 : ℝ), ∫ t, (s : ℂ) ^ (z - 1) * Complex.exp (-((t : ℂ) * (s : ℂ)))
          ∂ν := by
        rw [mellin]
        exact setIntegral_congr_fun measurableSet_Ioi (fun s _ => hinner s)
    _ = ∫ t, (∫ s in Ioi (0 : ℝ), (s : ℂ) ^ (z - 1) * Complex.exp (-((t : ℂ) * (s : ℂ))))
          ∂ν :=
        integral_integral_swap (integrable_mellin_laplace_of_ae_mem_Ioi hν hz hfin)
    _ = ∫ t, (t : ℂ) ^ (-z) * Complex.Gamma z ∂ν := by
        refine integral_congr_ae ?_
        filter_upwards [hν] with t ht
        exact hgamma t ht
    _ = Complex.Gamma z * ∫ t, (t : ℂ) ^ (-z) ∂ν := by
        rw [integral_mul_const, mul_comm]

/-- **`lem:mellin-data`'s convergence clause, for a measure carried by `(0,∞)`.**

The hinge again, read the other way round: `integrable_mellin_laplace_of_ae_mem_Ioi` is joint
integrability for the product measure, Fubini's `Integrable.integral_prod_left` projects it onto
the `s`-marginal, and the inner `ν`-integral *is* `s^{z-1}·(laplace ν s)`. -/
theorem mellinConvergent_laplace_of_ae_mem_Ioi [SFinite ν] (hν : ∀ᵐ t ∂ν, t ∈ Ioi (0 : ℝ))
    {z : ℂ} (hz : 0 < z.re) (hfin : ∫⁻ t, ENNReal.ofReal (t ^ (-z.re)) ∂ν ≠ ⊤) :
    MellinConvergent (fun s => (laplace ν s : ℂ)) z := by
  have hprod := (integrable_mellin_laplace_of_ae_mem_Ioi hν hz hfin).integral_prod_left
  refine hprod.congr (.of_forall fun s => ?_)
  dsimp only [Function.uncurry]
  rw [integral_const_mul, ← ofReal_laplace_eq_integral, smul_eq_mul]

end OfMeasure

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

/-- **`z_*`**, the abscissa beyond which the negative moments diverge, valued in `[0,∞]`.

**Not in `ℝ`, and the difference is not cosmetic.** `lem:moment-recursion`(2) concludes `z_* = ∞`
for a local operator, and that is the truth for the stable and inverse-gamma families --- every
negative moment of `T₁ = 1/(2γ_a)` is finite. `Real.sSup` of an unbounded set is the junk value
`0`, so a real-valued abscissa would make `1 < z_*` *false* exactly there, and every theorem
stated under (H) vacuous for precisely the kernels chapter 12 classifies. In `ℝ≥0∞` the supremum
is `⊤` and says what it means.

Stated as the supremum of the *image*, so that the ambient order is `ℝ≥0∞` throughout;
`le_zStar_of_negMoment_ne_top` and `negMoment_ne_top_of_lt_zStar` are the two directions anything
downstream uses, and neither mentions the image again. -/
noncomputable def zStar : ℝ≥0∞ := sSup (ENNReal.ofReal '' {ζ : ℝ | 0 < ζ ∧ F.negMoment ζ ≠ ⊤})

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

/-- The pointwise domination behind the two statements below: on `(0,∞)` and for `c ≤ ζ`, the
integrand `t^{-c}` is at most `t^{-ζ} + 1` --- below `1` the exponent `-c` is dominated by `-ζ`,
above `1` the power is itself at most `1`. -/
theorem rpow_neg_le_of_le {c ζ : ℝ} (hc : 0 ≤ c) (hcζ : c ≤ ζ) {t : ℝ}
    (ht : t ∈ Ioi (0 : ℝ)) :
    ENNReal.ofReal (t ^ (-c)) ≤ ENNReal.ofReal (t ^ (-ζ)) + 1 := by
  rcases le_total t 1 with h1 | h1
  · exact le_trans (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_ge (mem_Ioi.mp ht) h1 (by linarith))) le_self_add
  · refine le_trans (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith))) ?_
    simp

/-- **The moments decrease downwards up to one unit of mass**: `m(c) ≤ m(ζ) + 1` for `c ≤ ζ`.

Stated separately from `negMoment_ne_top_of_le` because chapter 12 needs the *bound* and not only
the finiteness it implies: it is what keeps `m(c+1)` bounded as `c ↓ 0`, which is the numerator
estimate in `lem:moment-recursion`(1). -/
theorem negMoment_le_of_le {c ζ : ℝ} (hc : 0 ≤ c) (hcζ : c ≤ ζ) :
    F.negMoment c ≤ F.negMoment ζ + 1 :=
  calc F.negMoment c
      ≤ ∫⁻ t in Ioi (0 : ℝ), (ENNReal.ofReal (t ^ (-ζ)) + 1) ∂F.lawT₁ :=
        setLIntegral_mono' measurableSet_Ioi fun _ ht => rpow_neg_le_of_le hc hcζ ht
    _ = F.negMoment ζ + F.lawT₁ (Ioi 0) := by
        rw [lintegral_add_right _ measurable_const, setLIntegral_const, one_mul, negMoment]
    _ ≤ F.negMoment ζ + 1 := by gcongr; exact prob_le_one

/-- The negative moments are finite *downwards*. This is what makes `z_*` an abscissa rather than
merely a supremum. -/
theorem negMoment_ne_top_of_le {c ζ : ℝ} (hc : 0 < c) (hcζ : c ≤ ζ)
    (h : F.negMoment ζ ≠ ⊤) : F.negMoment c ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨h, ENNReal.one_ne_top⟩) (F.negMoment_le_of_le hc.le hcζ)

/-- A finite moment is below the abscissa. One of the two directions anything downstream uses. -/
theorem le_zStar_of_negMoment_ne_top {ζ : ℝ} (hζ : 0 < ζ) (h : F.negMoment ζ ≠ ⊤) :
    ENNReal.ofReal ζ ≤ F.zStar :=
  le_sSup ⟨ζ, ⟨hζ, h⟩, rfl⟩

/-- **`c < z_*` is exactly finiteness of the `c`-th negative moment**, and this is the other
direction.

No nonemptiness side condition is needed: `sSup ∅ = 0` in `ℝ≥0∞` too, so `ofReal c < z_*` already
forces the defining set to be inhabited --- and `lt_sSup_iff`, `ℝ≥0∞` being a complete *linear*
order, hands the witness over directly. -/
theorem negMoment_ne_top_of_lt_zStar {c : ℝ} (hc : 0 < c)
    (hc' : ENNReal.ofReal c < F.zStar) : F.negMoment c ≠ ⊤ := by
  rw [zStar, lt_sSup_iff] at hc'
  obtain ⟨x, ⟨ζ, ⟨hζ0, hζ⟩, rfl⟩, hlt⟩ := hc'
  exact F.negMoment_ne_top_of_le hc (le_of_lt (by exact_mod_cast ENNReal.ofReal_lt_ofReal_iff_of_nonneg hc.le |>.mp hlt)) hζ

/-- Monotonicity in the argument, which is what call sites want: everything below something known
to be below the abscissa is below it. In `ℝ` this was `linarith`; here it is a lemma, and having
it once keeps the arithmetic out of the call sites. -/
theorem ofReal_lt_zStar_of_le {c d : ℝ} (hcd : c ≤ d) (hd : ENNReal.ofReal d < F.zStar) :
    ENNReal.ofReal c < F.zStar :=
  lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hcd) hd

/-- A finite moment strictly above `c` puts `c` strictly below the abscissa. This is how a witness
becomes a strip condition, and with `z_*` possibly infinite it is the only way. -/
theorem ofReal_lt_zStar_of_lt {c ζ : ℝ} (hc : 0 ≤ c) (hcζ : c < ζ)
    (h : F.negMoment ζ ≠ ⊤) : ENNReal.ofReal c < F.zStar :=
  lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hc).mpr hcζ)
    (F.le_zStar_of_negMoment_ne_top (lt_of_le_of_lt hc hcζ) h)

/-- **`z_* = ∞`, sayable at last**: if every negative moment is finite then the abscissa is `⊤`.

This is what `lem:moment-recursion`(2) concludes for a local operator, and it is the truth for the
stable and inverse-gamma families. It is also the check on the definition above: with `zStar : ℝ`
the same hypothesis gave `z_* = 0`, since `Real.sSup` of an unbounded set is junk, and so made
(H)'s `1 < z_*` **false** for exactly the kernels chapter 12 classifies --- every theorem stated
under (H) vacuous there. -/
theorem zStar_eq_top_of_forall_negMoment_ne_top (h : ∀ ζ : ℝ, 0 < ζ → F.negMoment ζ ≠ ⊤) :
    F.zStar = ⊤ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  refine le_trans ?_ (F.le_zStar_of_negMoment_ne_top (ζ := (r : ℝ) + 1) (by positivity)
    (h _ (by positivity)))
  rw [← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- …and then (H)'s second clause holds rather than fails. -/
theorem one_lt_zStar_of_forall_negMoment_ne_top (h : ∀ ζ : ℝ, 0 < ζ → F.negMoment ζ ≠ ⊤) :
    (1 : ℝ≥0∞) < F.zStar := by
  rw [F.zStar_eq_top_of_forall_negMoment_ne_top h]
  exact ENNReal.one_lt_top

/-- The real interval `(0, z_*)`: the orders strictly below the abscissa.

Open and convex, which is what the analyticity and identity-theorem arguments need and what a bare
finiteness condition would not supply --- the set where `m` is finite may contain its right
endpoint, and `z_*` is precisely the supremum that discards it. -/
def momentInterval : Set ℝ := {c : ℝ | 0 < c ∧ ENNReal.ofReal c < F.zStar}

lemma mem_momentInterval {c : ℝ} : c ∈ F.momentInterval ↔ 0 < c ∧ ENNReal.ofReal c < F.zStar :=
  Iff.rfl

lemma isOpen_momentInterval : IsOpen F.momentInterval :=
  (isOpen_lt continuous_const continuous_id).inter
    (isOpen_Iio.preimage ENNReal.continuous_ofReal)

lemma convex_momentInterval : Convex ℝ F.momentInterval := by
  refine (convex_iff_ordConnected (𝕜 := ℝ)).mpr ⟨fun x hx y hy z hz => ?_⟩
  exact ⟨lt_of_lt_of_le hx.1 hz.1, F.ofReal_lt_zStar_of_le hz.2 hy.2⟩

/-- Under (H) there is a real `ζ > 1` with `m(ζ)` finite.

In the real-valued reading one took the midpoint of `(1, z_*)`; with `z_*` possibly infinite that
is not available, and the witness comes from the supremum instead. -/
theorem exists_one_lt_negMoment_ne_top (hH : F.StandingHypothesis) :
    ∃ ζ : ℝ, 1 < ζ ∧ F.negMoment ζ ≠ ⊤ := by
  have h1 : (1 : ℝ≥0∞) < F.zStar := hH.2
  rw [zStar, lt_sSup_iff] at h1
  obtain ⟨x, ⟨ζ, ⟨hζ0, hζ⟩, rfl⟩, hlt⟩ := h1
  refine ⟨ζ, ?_, hζ⟩
  rwa [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp,
    ENNReal.ofReal_lt_ofReal_iff_of_nonneg zero_le_one] at hlt

/-! ## The hinge -/

/-- The negative moment as an unrestricted `lintegral`, which is the form the general statements
above are stated in: `T₁` charges only `(0,∞)`, so restricting changes nothing. -/
theorem negMoment_eq_lintegral (h0 : F.lawT₁ {(0 : ℝ)} = 0) (ζ : ℝ) :
    F.negMoment ζ = ∫⁻ t, ENNReal.ofReal (t ^ (-ζ)) ∂F.lawT₁ := by
  rw [negMoment, Measure.restrict_eq_self_of_ae_mem (F.ae_mem_Ioi_lawT₁ h0)]

/-- **The `ℝ≥0∞` computation the chapter turns on**:
`∫∫ s^{c-1} e^{-ts} ds dμ(t) = Γ(c) · E[T₁^{-c}]`.

See the module docstring: this single identity is the Fubini side condition for
`mellin_profile`, the bound of `norm_mellin_profile_le`, and the finiteness underneath vertical
integrability. Its right-hand side is finite iff `c < z_*`, so the exchange below is licensed by
the strip condition and by no further hypothesis. -/
theorem lintegral_lintegral_gamma {c : ℝ} (hc : 0 < c) (h0 : F.lawT₁ {(0 : ℝ)} = 0) :
    ∫⁻ t, (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (c - 1) * Real.exp (-(t * s)))) ∂F.lawT₁
      = ENNReal.ofReal (Real.Gamma c) * F.negMoment c := by
  rw [lintegral_lintegral_gamma_of_ae_mem_Ioi (F.ae_mem_Ioi_lawT₁ h0) hc,
    F.negMoment_eq_lintegral h0]

/-- Joint integrability of `(s,t) ↦ s^{z-1} e^{-ts}` for `volume|_(0,∞) ⊗ lawT₁`: the Fubini side
condition, and the hinge is all of it. Tonelli turns the total mass of the absolute value into
the double integral above, whose value is `Γ(Re z) · E[T₁^{-Re z}]`. -/
theorem integrable_mellin_laplace {z : ℂ} (hz : 0 < z.re) (hz' : ENNReal.ofReal z.re < F.zStar)
    (h0 : F.lawT₁ {(0 : ℝ)} = 0) :
    Integrable (Function.uncurry fun s t : ℝ =>
        (s : ℂ) ^ (z - 1) * Complex.exp (-((t : ℂ) * (s : ℂ))))
      ((volume.restrict (Ioi 0)).prod F.lawT₁) :=
  integrable_mellin_laplace_of_ae_mem_Ioi (F.ae_mem_Ioi_lawT₁ h0) hz
    (by rw [← F.negMoment_eq_lintegral h0]; exact F.negMoment_ne_top_of_lt_zStar hz hz')

/-! ## `lem:mellin-data` -/

/-- **`lem:mellin-data`**, the identity: `H̃(z) = Γ(z) · E[T₁^{-z}]` on the strip
`0 < Re z < z_*`.

Fubini on `∫₀^∞ s^{z-1} ∫ e^{-st} dμ(t) ds`, exchanged to `∫ (∫₀^∞ s^{z-1}e^{-st} ds) dμ(t)`.
The inner integral is Mathlib's `Complex.integral_cpow_mul_exp_neg_mul_Ioi`, which evaluates to
`(1/t)^z Γ(z)`, so no substitution is needed and the Gamma function enters as Mathlib's rather
than as a definition of ours. The exchange is licensed by `integrable_mellin_laplace`, i.e. by
the hinge, i.e. by `Re z < z_*`. -/
theorem mellin_profile (hH : F.StandingHypothesis) {z : ℂ} (hz : 0 < z.re)
    (hz' : ENNReal.ofReal z.re < F.zStar) :
    mellin (fun s => (F.profile s : ℂ)) z
      = Complex.Gamma z * ∫ t, (t : ℂ) ^ (-z) ∂F.lawT₁ := by
  have h0 := F.lawT₁_singleton_zero hH.1
  exact mellin_laplace_of_ae_mem_Ioi (F.ae_mem_Ioi_lawT₁ h0) hz
    (by rw [← F.negMoment_eq_lintegral h0]; exact F.negMoment_ne_top_of_lt_zStar hz hz')

/-- **`lem:mellin-data`**, convergence: the Mellin integral of the profile converges absolutely on
the strip.

The hinge again, read the other way round. `integrable_mellin_laplace` is joint integrability for
the product measure; Fubini's `Integrable.integral_prod_left` projects it onto the `s`-marginal,
and the inner `μ`-integral *is* `s^{z-1}H(s)`. So this costs nothing beyond what the identity
already paid for, and it is `MellinConvergent` verbatim — the first of the two hypotheses
`mellinInv_mellin_eq` asks for, the other being `lem:mellin-vertical`. -/
theorem mellinConvergent_profile (hH : F.StandingHypothesis) {z : ℂ} (hz : 0 < z.re)
    (hz' : ENNReal.ofReal z.re < F.zStar) : MellinConvergent (fun s => (F.profile s : ℂ)) z := by
  have h0 := F.lawT₁_singleton_zero hH.1
  exact mellinConvergent_laplace_of_ae_mem_Ioi (F.ae_mem_Ioi_lawT₁ h0) hz
    (by rw [← F.negMoment_eq_lintegral h0]; exact F.negMoment_ne_top_of_lt_zStar hz hz')

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
    (hc' : ENNReal.ofReal c < F.zStar) (τ : ℝ) :
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

/-! ## `lem:standing-kernel-readings` (11.21), the part stateable here

The two readings of `def:standing-hypothesis`'s clauses that the definition used to assert in
passing, now a node of their own: the first clause is exactly "no atom at zero delay", and under
it, the integral `∫₀^∞ e^{-F(s)}ds` reads off the first negative moment. The clause comparing
`F.kernel 0 x {0}` for general `x` needs `kernel_zero_eq_map_lawT₁`, which lives in
`MemoryFractional.lean` (downstream of this file, to avoid a cycle); it and the assembled bundle
`standing_kernel_readings` are there, right after that lemma. -/

/-- The converse of `lawT₁_singleton_zero`: no atom at the origin forces `F(∞) = ∞`.

`laplaceL F.lawT₁` tends to the mass at the origin as `s → ∞` (`tendsto_laplaceL_atTop`); with
that mass `0` the transform tends to `0`, and `profile = laplaceL.toReal` inherits the limit.
Composing with `Real.exp` — via `Real.comap_exp_nhds_zero`, that the preimage filter of `𝓝 0`
under `exp` is `atBot` — turns "the transform tends to `0`" into "the exponent tends to `∞`". -/
theorem tendsto_toRealExponent_atTop_of_lawT₁_singleton_zero
    (h0 : F.lawT₁ {(0 : ℝ)} = 0) : Tendsto F.toRealExponent atTop atTop := by
  have hL : Tendsto (laplaceL F.lawT₁) atTop (𝓝 (F.lawT₁ {(0 : ℝ)})) :=
    tendsto_laplaceL_atTop F.isCausal_lawT₁
  rw [h0] at hL
  have hprofile : Tendsto F.profile atTop (𝓝 0) := by
    change Tendsto (fun s => laplace F.lawT₁ s) atTop (𝓝 0)
    simp_rw [laplace_eq_toReal_laplaceL]
    have hcont := (ENNReal.tendsto_toReal (a := (0 : ℝ≥0∞)) (by simp)).comp hL
    simpa [Function.comp_def] using hcont
  have hexp : Tendsto (fun s : ℝ => Real.exp (-F.toRealExponent s)) atTop (𝓝 0) := by
    refine hprofile.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs using F.profile_eq_exp_neg hs
  have hneg : Tendsto (fun s : ℝ => -F.toRealExponent s) atTop atBot := by
    rw [← Real.comap_exp_nhds_zero, tendsto_comap_iff]
    exact hexp
  simpa [Function.comp_def] using tendsto_neg_atBot_atTop.comp hneg

/-- **`lem:standing-kernel-readings`(2), the identity**: under no atom at the origin, the
integral `∫₀^∞ e^{-F(s)}ds` — the profile's Mellin data at the left edge — is exactly the first
negative moment `E[T₁^{-1}]`, both read in `[0,∞]`.

Tonelli swaps `∫⁻ s in Ioi 0, laplaceL F.lawT₁ s ds` into the shape `lintegral_lintegral_gamma`
computes at `c = 1`, where the weight `s^{c-1}` is `1` and drops out. `ofReal (profile s)` agrees
with `laplaceL F.lawT₁ s` for `s > 0` because the transform is finite there
(`laplaceL_ne_top_of_causal`), so passing through `ofReal` costs nothing on the strip. -/
theorem lintegral_profile_eq_negMoment_one (h0 : F.lawT₁ {(0 : ℝ)} = 0) :
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (F.profile s) = F.negMoment 1 := by
  have heq : Set.EqOn (fun s => ENNReal.ofReal (F.profile s)) (laplaceL F.lawT₁) (Ioi 0) := by
    intro s hs
    change ENNReal.ofReal (F.profile s) = laplaceL F.lawT₁ s
    rw [profile, laplace_eq_toReal_laplaceL,
      ENNReal.ofReal_toReal (laplaceL_ne_top_of_causal F.isCausal_lawT₁ (mem_Ioi.mp hs).le)]
  rw [setLIntegral_congr_fun measurableSet_Ioi heq]
  have hswap : ∫⁻ s in Ioi (0 : ℝ), laplaceL F.lawT₁ s
      = ∫⁻ t, (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(t * s)))) ∂F.lawT₁ := by
    have hswap' := lintegral_lintegral_swap (μ := volume.restrict (Ioi (0 : ℝ))) (ν := F.lawT₁)
      (f := fun s t : ℝ => ENNReal.ofReal (Real.exp (-(s * t))))
      (by unfold Function.uncurry; fun_prop)
    rw [show (∫⁻ s in Ioi (0 : ℝ), laplaceL F.lawT₁ s)
        = ∫⁻ s in Ioi (0 : ℝ), ∫⁻ t, ENNReal.ofReal (Real.exp (-(s * t))) ∂F.lawT₁ from rfl,
      hswap']
    refine lintegral_congr fun t => ?_
    exact setLIntegral_congr_fun measurableSet_Ioi fun s _ => by rw [mul_comm]
  rw [hswap]
  have hgamma := F.lintegral_lintegral_gamma (c := 1) one_pos h0
  simp only [show (1 : ℝ) - 1 = 0 from by norm_num, Real.rpow_zero, one_mul, Real.Gamma_one,
    ENNReal.ofReal_one] at hgamma
  exact hgamma

/-- **`lem:standing-kernel-readings`(2), the two consequences.** `z_* > 1` forces the first
negative moment finite. Neither this nor its converse below needs the no-atom hypothesis: both
are the general moment/abscissa lemmas above, instantiated at `ζ = 1`. -/
theorem negMoment_one_ne_top_of_one_lt_zStar (hz : 1 < F.zStar) : F.negMoment 1 ≠ ⊤ :=
  F.negMoment_ne_top_of_lt_zStar one_pos (by rwa [ENNReal.ofReal_one])

/-- Finiteness of the first negative moment forces `z_* ≥ 1`. -/
theorem one_le_zStar_of_negMoment_one_ne_top (h1 : F.negMoment 1 ≠ ⊤) : (1 : ℝ≥0∞) ≤ F.zStar := by
  have := F.le_zStar_of_negMoment_ne_top (ζ := 1) one_pos h1
  rwa [ENNReal.ofReal_one] at this

end SelfDecomposableExponent

/-- `E[T₁^{-c}]` as a Bochner-integrable function.

Chapter 11 uses it as the outer factor of a Fubini side condition; chapter 12 uses it as the
dominating function of a dominated-convergence argument. It belongs here rather than at either
use, being a statement about `negMoment` and nothing else. -/
theorem integrable_rpow_neg (F : SelfDecomposableExponent) (hH : F.StandingHypothesis) {c : ℝ}
    (hc : 0 < c) (hc' : ENNReal.ofReal c < F.zStar) : Integrable (fun τ : ℝ => τ ^ (-c)) F.lawT₁ := by
  have h0 := F.lawT₁_singleton_zero hH.1
  have hae := F.ae_mem_Ioi_lawT₁ h0
  refine ⟨by fun_prop, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hcalc : ∫⁻ τ, ‖τ ^ (-c)‖ₑ ∂F.lawT₁ = F.negMoment c := by
    rw [SelfDecomposableExponent.negMoment, Measure.restrict_eq_self_of_ae_mem hae]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with τ hτ
    rw [← ofReal_norm, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (mem_Ioi.mp hτ).le _)]
  rw [hcalc]
  exact lt_top_iff_ne_top.mpr (F.negMoment_ne_top_of_lt_zStar hc hc')

end Hemigroup
