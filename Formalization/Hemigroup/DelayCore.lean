/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.SignalingForm
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-!
# Chapter 10's setting: `X₀`, the delay semigroup `T_r`, and the core `𝒟`

Blueprint: the preamble of chapter 10, and the objects `lem:delay-core` (10.1) is about. The
lemma itself is stated in `Skeleton/Chapter10.lean`; **this file carries only definitions and the
facts about them that are proved**, so that the chapter has a setting before it has a theorem.

Chapter 11 has been using `𝒟` in prose since it was written, and defining none of it: it takes
the consequences it needs as hypotheses. So the first obligation of this file is not to state
10.1 but to say what `X₀` and `𝒟` *are*, in a way from which chapter 11's hypotheses follow —
`memCore_iff_signaling_hypotheses` below is that check, and it is an `iff` on purpose.

## `X₀` is a predicate on `X`, not a type

`def:cascade-family` already acts on `X = L¹(ℝ)` and states causality as a predicate
(`VanishesBefore`), exactly as the measure side states it as `IsCausal μ` rather than carrying
measures on a half-line type. `DESIGN-formalization-strategy.md`'s M0 takes that decision one
level down and gives the reason: *"measures on ℝ supported in `[0,∞)` rather than on a bespoke
half-line type, so `Measure.conv` and the convolution API apply directly."* The same argument
applies verbatim one level up. `Φ_{x,y}` is an `X →L[ℝ] X`; so are `transL1`, `dilL1` and
`mconvL1`; a subtype `L¹(ℝ₊)` would need every one of them re-mounted, and would buy nothing,
because "every `Φ_{x,y}` restricts to `X₀`" is (A3) — a *theorem shape the development already
has* rather than something a type would give.

So `causalL1 = {F : X | VanishesBefore 0 F}`, and `T_r` is `transL1 r`.

## `𝒟` is primarily a predicate on functions, and only derivatively on `X`

This is the decision with consequences, and the direction is forced by chapter 11 rather than
chosen. Chapter 11's hypotheses are *pointwise* — `Measurable f`, `∀ r < 0, f r = 0`,
`∀ r, f r = ∫_{(0,r]} g` — because `delayedField` exists precisely to name a representative that
an `L¹` class does not have. A purely `L¹`-level `𝒟` therefore could not *derive* them; it could
only assert them again. So the primary object is `HasCoreDeriv f g`, on genuine functions, and
`coreL1` is its image in `X`.

That is the (a)/(b) fork of `PLAN-chapters-8-12.md` answered one notch further along. The record
there is that "the question was never *whether* to name a representative but *how widely*".
`HasCoreDeriv` is that naming at the width chapter 10 needs, and `coreL1` is what the density and
invariance clauses — which are genuinely about `L¹` classes — are stated in.

## `𝒟` is written as a primitive, not as absolute continuity

The blueprint writes `𝒟 = {f ∈ X₀ : f absolutely continuous, f' ∈ X₀, f(0) = 0}`. Mathlib now has
`AbsolutelyContinuousOnInterval`, so that wording is expressible — and it would be the wrong
choice, for a reason the `StieltjesFunction` episode of chapter 9 already recorded: **it names a
tool where a property is meant.** What every consumer uses is the primitive form `f = ∫₀^· g`,
and getting from absolute continuity to it is the Lebesgue fundamental theorem, which Mathlib does
*not* have; the direction Mathlib does have is the one nothing uses. Defining `𝒟` by the primitive
makes the three clauses free (`causal`, `apply_zero`, `abs_le`) and leaves the blueprint's own
wording available as a derived fact, `HasCoreDeriv.absolutelyContinuousOnInterval`.

Note also that `f ∈ X₀` is a *separate* field and not a consequence: a primitive of an `L¹`
function tends to `∫₀^∞ g`, so it is integrable only when that limit vanishes. `SignalingForm.lean`
records the same point, discovered there by assembling clauses that were each fine without it.
-/

namespace Hemigroup

open MeasureTheory Set Filter

open scoped ENNReal Topology

/-! ## The delay semigroup -/

/-- The **delay semigroup** at the level of functions, `(T_r f)(t) = f(t-r)·1_{t ≥ r}`.

The indicator is what the blueprint writes, and on `X₀` it is redundant — see
`delay_eq_translate`. Keeping it in the definition is what makes `T_r` a positive operator on all
of `X` rather than only on the causal part, which is the reading the blueprint's "semigroup of
positive isometries" asks for. -/
noncomputable def delay (r : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (Ici r).indicator fun t => f (t - r)

/-- **On causal functions the indicator is redundant**, so `T_r` is translation and the `L¹`
operator is `transL1 r`.

Causality alone does it: below `t = r` the argument `t - r` is negative, where `f` already
vanishes. This is why chapter 10 needs no new operator on `X`. -/
theorem delay_eq_translate {f : ℝ → ℝ} (hf : ∀ s : ℝ, s < 0 → f s = 0) (r : ℝ) :
    delay r f = fun t => f (t - r) := by
  funext t
  by_cases ht : r ≤ t
  · rw [delay, indicator_of_mem (mem_Ici.mpr ht)]
  · rw [delay, indicator_of_notMem (by simpa using ht), hf (t - r) (by linarith [not_le.mp ht])]

/-! ## The two analytic inputs are already in the library

`lem:delay-core`'s density clause and its difference quotient rest on two facts, and the
blueprint names both. Neither is new work here, and finding that out is the round's main saving.

**Continuity of translation in `L¹`** is `continuous_transL1`, proved in
`Hemigroup/Representation.lean` for chapter 4's Wendel-style representation argument, which needs
`r ↦ τ_r g` strongly measurable and buys it with continuity. That file also records the Mathlib
answer, which is worth repeating because it is not findable by name: Mathlib has no lemma about
translation in `Lᵖ`, but it has `MeasureTheory.Lp.compMeasurePreserving_continuous`, joint
continuity of `(g, φ) ↦ g ∘ φ` over measure-preserving `φ` varying in `C(ℝ,ℝ)`, which is the same
fact wearing a different hat.

**The mollifier is chapter 4's approximate identity.** `approxId ε = ε⁻¹·1_{(0,ε)}` is carried by
`[0,ε]`, hence *causal* — a property chapter 4 needed for an unrelated reason, its approximants
having to be causal probability densities for Prokhorov — and causality is exactly what makes
`ρ_ε * f` land in `𝒟` rather than merely near it. `tendsto_bconv_approxId` is `ρ_ε * f → f`
in `L¹`.

Worth recording as a pattern, because it runs opposite to this project's usual finding. The usual
one is that a node's stated prerequisite exceeds what the obligation needs. Here the obligation's
genuine prerequisites were both **already proved, six chapters earlier, inside an argument with no
visible relation to this one**. The move that located them is the same — write the statement and
ask what it consumes — but what it turned up was a library fact rather than a Mathlib one, and a
survey of Mathlib would have missed both.

`tendsto_norm_transL1_sub` below is the one repackaging the quantitative clauses want: continuity
at the origin, read as a real-valued limit.
-/

/-- **`‖T_r f - f‖₁ → 0` as `r → 0`** — `continuous_transL1` at the origin, in the form the
difference-quotient clause consumes. -/
theorem tendsto_norm_transL1_sub (F : X) :
    Tendsto (fun r : ℝ => ‖transL1 r F - F‖) (𝓝 0) (𝓝 0) := by
  have h : Tendsto (fun r : ℝ => transL1 r F - F) (𝓝 0) (𝓝 (transL1 (0 : ℝ) F - F)) :=
    ((continuous_transL1 F).tendsto 0).sub tendsto_const_nhds
  rw [transL1_zero, sub_self] at h
  simpa [Function.comp_def] using (continuous_norm.tendsto (0 : X)).comp h

/-! ## Three facts about causal integrands

Every clause of `lem:delay-core` moves the base point of an integral — by a substitution, by a
translation, or by Chasles — and each time causality is what moves it back. These are the three
forms that takes.
-/

/-- A causal integrand contributes nothing to the left of the origin. -/
theorem setIntegral_Ioc_eq_zero_of_causal {g : ℝ → ℝ} (hgc : ∀ r : ℝ, r < 0 → g r = 0) {a b : ℝ}
    (hb : b ≤ 0) : (∫ w in Ioc a b, g w) = 0 := by
  have hne : ∀ᵐ w : ℝ, w ≠ 0 := by
    rw [ae_iff]
    simp
  refine integral_eq_zero_of_ae ((ae_restrict_iff' measurableSet_Ioc).mpr ?_)
  filter_upwards [hne] with w hw hwmem
  exact hgc w (lt_of_le_of_ne (hwmem.2.trans hb) hw)

/-- **A causal integrand does not see the left end of the interval.** Extending the domain of a
primitive to the left of the origin changes nothing, because there is nothing there. -/
theorem setIntegral_Ioc_of_causal {g : ℝ → ℝ} (hg : Integrable g)
    (hgc : ∀ r : ℝ, r < 0 → g r = 0) {a : ℝ} (ha : a ≤ 0) (b : ℝ) :
    (∫ w in Ioc a b, g w) = ∫ w in Ioc (0 : ℝ) b, g w := by
  rcases lt_or_ge 0 b with hb | hb
  · have hsplit : Ioc a b = Ioc a 0 ∪ Ioc (0 : ℝ) b := (Ioc_union_Ioc_eq_Ioc ha hb.le).symm
    have hdisj : Disjoint (Ioc a (0 : ℝ)) (Ioc (0 : ℝ) b) := by
      rw [Set.disjoint_left]
      rintro w ⟨-, hw2⟩ ⟨hw3, -⟩
      exact absurd hw3 (not_lt.mpr hw2)
    rw [hsplit, setIntegral_union hdisj measurableSet_Ioc hg.integrableOn hg.integrableOn,
      setIntegral_Ioc_eq_zero_of_causal hgc le_rfl, zero_add]
  · rw [setIntegral_Ioc_eq_zero_of_causal hgc hb, Ioc_eq_empty (not_lt.mpr hb),
      Measure.restrict_empty, integral_zero_measure]

/-- **The primitive of a causal integrand is an interval integral at every real point**, the
negative half-line included, where both sides vanish. Having it everywhere rather than on
`[0,∞)` is what lets Chasles be applied without a case split. -/
theorem setIntegral_Ioc_eq_intervalIntegral_of_causal {g : ℝ → ℝ} (hg : Integrable g)
    (hgc : ∀ r : ℝ, r < 0 → g r = 0) (t : ℝ) :
    (∫ ρ in Ioc (0 : ℝ) t, g ρ) = ∫ ρ in (0 : ℝ)..t, g ρ := by
  rcases le_or_gt 0 t with ht | ht
  · rw [intervalIntegral.integral_of_le ht]
  · rw [Ioc_eq_empty (not_lt.mpr ht.le), Measure.restrict_empty, integral_zero_measure,
      intervalIntegral.integral_of_ge ht.le, setIntegral_Ioc_eq_zero_of_causal hgc le_rfl,
      neg_zero]

/-- `μ ∗ f` is genuinely measurable when `f` is, not merely `AEStronglyMeasurable`.

`Operator.lean` supplies the `L¹` facts about `mconv`, which is all (A1) needs; the core needs
more, because `HasCoreDeriv` asks for `Measurable` — a demand chapter 11 also makes, and for the
recorded reason that a `volume`-null set need not pull back to a null set for the product measure
when the other factor has atoms. This is Mathlib's strong measurability of a parametric integral,
with `SFinite` the only hypothesis. -/
theorem measurable_mconv (μ : Measure ℝ) [SFinite μ] {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (mconv μ f) :=
  ((hf.comp measurable_sub).stronglyMeasurable.integral_prod_right' (ν := μ)).measurable

/-- **`μ ∗ f` is the primitive of `μ ∗ g` whenever `f` is the primitive of `g`.**

The analytic content of `lem:delay-core`'s `Φ`-invariance clause, and the blueprint's own
argument: `f = 1_{[0,∞)} ∗ g`, so `μ ∗ f = 1_{[0,∞)} ∗ (μ ∗ g)`. In Lean it is Fubini on
`Ioc 0 t × μ`, and **causality of `μ` is what keeps the primitive based at the origin** — the
substitution `s ↦ s - τ` moves the lower endpoint to `-τ`, and `τ ≥ 0` a.e. is what
`setIntegral_Ioc_of_causal` needs to move it back.

`delayedField_eq_setIntegral` is this statement for `μ = ` the law of `xT₁`; that it was proved
there first, one chapter later and for one measure, is the shape this whole file is correcting. -/
theorem mconv_eq_setIntegral_mconv {μ : Measure ℝ} [IsFiniteMeasure μ] (hμ : IsCausal μ)
    {f g : ℝ → ℝ} (hgm : Measurable g) (hg : Integrable g) (hgc : ∀ r : ℝ, r < 0 → g r = 0)
    (hf : ∀ r : ℝ, f r = ∫ ρ in Ioc (0 : ℝ) r, g ρ) (t : ℝ) :
    mconv μ f t = ∫ ρ in Ioc (0 : ℝ) t, mconv μ g ρ := by
  rcases lt_or_ge t 0 with ht | ht
  · rw [Ioc_eq_empty (not_lt.mpr ht.le), Measure.restrict_empty, integral_zero_measure]
    refine mconv_eq_zero_of_lt hμ (fun s hs => ?_) ht
    rw [hf s, Ioc_eq_empty (not_lt.mpr hs.le), Measure.restrict_empty, integral_zero_measure]
  · have hinner : ∀ τ : ℝ, 0 ≤ τ → (∫ s in Ioc (0 : ℝ) t, g (s - τ)) = f (t - τ) := by
      intro τ hτ
      have hsub : (∫ s in Ioc (0 : ℝ) t, g (s - τ)) = ∫ w in Ioc (0 - τ) (t - τ), g w := by
        rw [← intervalIntegral.integral_of_le ht, ← intervalIntegral.integral_of_le (by linarith)]
        exact intervalIntegral.integral_comp_sub_right (fun w => g w) τ
      rw [hsub, setIntegral_Ioc_of_causal hg hgc (by linarith) (t - τ), hf]
    have hmeas : Measurable (Function.uncurry fun s τ : ℝ => g (s - τ)) := by
      unfold Function.uncurry
      fun_prop
    have hint : Integrable (Function.uncurry fun s τ : ℝ => g (s - τ))
        ((volume.restrict (Ioc (0 : ℝ) t)).prod μ) := by
      refine ⟨hmeas.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_enorm, lintegral_prod_symm _ hmeas.enorm.aemeasurable]
      have hC : ∫⁻ w, ‖g w‖ₑ ≠ ⊤ := by
        have h2 := hg.2
        rw [hasFiniteIntegral_iff_enorm] at h2
        exact h2.ne
      have hbnd : ∀ τ : ℝ,
          (∫⁻ s in Ioc (0 : ℝ) t, ‖Function.uncurry (fun s τ : ℝ => g (s - τ)) (s, τ)‖ₑ)
            ≤ ∫⁻ w, ‖g w‖ₑ := by
        intro τ
        calc (∫⁻ s in Ioc (0 : ℝ) t, ‖g (s - τ)‖ₑ)
            ≤ ∫⁻ s, ‖g (s - τ)‖ₑ := setLIntegral_le_lintegral _ _
          _ = ∫⁻ w, ‖g w‖ₑ := lintegral_sub_right_eq_self (fun w => ‖g w‖ₑ) τ
      calc ∫⁻ τ, (∫⁻ s in Ioc (0 : ℝ) t,
              ‖Function.uncurry (fun s τ : ℝ => g (s - τ)) (s, τ)‖ₑ) ∂μ
          ≤ ∫⁻ _τ, (∫⁻ w, ‖g w‖ₑ) ∂μ := lintegral_mono hbnd
        _ = (∫⁻ w, ‖g w‖ₑ) * μ univ := lintegral_const _
        _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hC) (measure_lt_top μ univ)
    calc mconv μ f t
        = ∫ τ, f (t - τ) ∂μ := rfl
      _ = ∫ τ, (∫ s in Ioc (0 : ℝ) t, g (s - τ)) ∂μ := by
          refine (integral_congr_ae ?_).symm
          filter_upwards [hμ.ae_nonneg] with τ hτ using hinner τ hτ
      _ = ∫ s in Ioc (0 : ℝ) t, ∫ τ, g (s - τ) ∂μ := (integral_integral_swap hint).symm
      _ = ∫ s in Ioc (0 : ℝ) t, mconv μ g s := rfl

/-! ## The core, on functions -/

/-- **`f ∈ 𝒟`, with the derivative named**: `f` is the primitive of a causal `g ∈ X₀`, and lies in
`X₀` itself.

The blueprint's three conditions map onto the fields as follows. *Absolutely continuous with
`f' ∈ X₀`* is `primitive` together with the three `g`-fields — see the module docstring for why
the primitive is the definition and absolute continuity the derived fact. *`f(0) = 0`* is
`primitive` at `r = 0`, where the domain of integration is empty (`apply_zero`). *`f ∈ X₀`* is
`integrable` together with `causal`, and it is genuinely a separate demand. -/
structure HasCoreDeriv (f g : ℝ → ℝ) : Prop where
  /-- The derivative is measurable. Free for an `L¹` class, and mandatory in Lean: the delayed
  average composes `g` with a map under which a `volume`-null set need not stay null. -/
  measurable_deriv : Measurable g
  /-- `f' ∈ L¹`. -/
  integrable_deriv : Integrable g
  /-- `f'` is causal — the `X₀` half of `f' ∈ X₀`. -/
  causal_deriv : ∀ r : ℝ, r < 0 → g r = 0
  /-- `f` is the primitive of `g` from the origin. This carries absolute continuity and
  `f(0) = 0` at once. -/
  primitive : ∀ r : ℝ, f r = ∫ ρ in Ioc (0 : ℝ) r, g ρ
  /-- `f ∈ L¹`. Not implied by the rest: a primitive of an `L¹` function tends to `∫₀^∞ g`. -/
  integrable : Integrable f

/-- **`f ∈ 𝒟`**. -/
def MemCore (f : ℝ → ℝ) : Prop := ∃ g, HasCoreDeriv f g

namespace HasCoreDeriv

variable {f g : ℝ → ℝ}

/-- `f` is causal — the `X₀` half of `f ∈ X₀`, and free from the primitive. -/
theorem causal (h : HasCoreDeriv f g) : ∀ r : ℝ, r < 0 → f r = 0 := fun r hr => by
  rw [h.primitive r, Ioc_eq_empty (not_lt.mpr hr.le), Measure.restrict_empty,
    integral_zero_measure]

/-- `f(0) = 0`. -/
theorem apply_zero (h : HasCoreDeriv f g) : f 0 = 0 := by
  rw [h.primitive 0, Ioc_self, Measure.restrict_empty, integral_zero_measure]

/-- The primitive read as an interval integral, valid on all of `ℝ`.

To the left of the origin both sides vanish — the left by the empty domain, the right because `g`
does. Having the identity at *every* `r` is what makes continuity a one-liner. -/
theorem eq_intervalIntegral (h : HasCoreDeriv f g) (r : ℝ) : f r = ∫ ρ in (0 : ℝ)..r, g ρ := by
  rw [h.primitive r,
    setIntegral_Ioc_eq_intervalIntegral_of_causal h.integrable_deriv h.causal_deriv r]

/-- `f` is continuous — Mathlib's continuity of a primitive, once `eq_intervalIntegral` has put
`f` in that form. -/
theorem continuous (h : HasCoreDeriv f g) : Continuous f :=
  (h.integrable_deriv.continuous_primitive 0).congr fun r => (h.eq_intervalIntegral r).symm

/-- `f` is measurable. This is the one hypothesis of `thm:signaling-form` that `𝒟` does not carry
as a field. -/
theorem measurable (h : HasCoreDeriv f g) : Measurable f := h.continuous.measurable

/-- **`f` is bounded by `‖f'‖₁`** — the feature of `𝒟` that widens the strip of
`lem:memory-fractional-integrals` from `Re z > 1` to `Re z > 0`, and hence the one that makes
`thm:signaling-form`(2) chain. -/
theorem abs_le (h : HasCoreDeriv f g) (r : ℝ) : |f r| ≤ ∫ w, |g w| := by
  rw [h.primitive r]
  exact SelfDecomposableExponent.abs_primitive_le h.integrable_deriv r

/-- **The blueprint's own wording, recovered**: `f` is absolutely continuous on every `[0,b]`.

Nothing downstream uses this; it is here because `𝒟` is *defined* by the primitive and the
blueprint defines it by absolute continuity, so the agreement of the two should be checked rather
than asserted. Only this direction is available — Mathlib has no Lebesgue fundamental theorem —
and it is the direction that makes the definition faithful rather than the one that would make it
usable. -/
theorem absolutelyContinuousOnInterval (h : HasCoreDeriv f g) (b : ℝ) :
    AbsolutelyContinuousOnInterval f 0 b := by
  have hf : f = fun x => ∫ ρ in (0 : ℝ)..x, g ρ := funext h.eq_intervalIntegral
  rw [hf]
  exact h.integrable_deriv.intervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral
    left_mem_uIcc

/-- `T_r` acts on the core's members by plain translation. -/
theorem delay_eq (h : HasCoreDeriv f g) (r : ℝ) : delay r f = fun t => f (t - r) :=
  delay_eq_translate h.causal r

/-- **`lem:delay-core`, invariance under the delay semigroup**, with the derivative tracked:
`(T_r f)' = T_r f'`.

The blueprint's three assertions — `T_r f` is absolutely continuous, vanishes on `[0,r]`, and has
derivative `T_r f'` — are here the single field `primitive`, because the primitive form carries
all three. `r ≥ 0` is used exactly twice: to keep `T_r f'` causal, and to keep the substituted
interval `Ioc (-r) (s-r)` reachable from `Ioc 0 (s-r)` by `setIntegral_Ioc_of_causal`. -/
theorem translate (h : HasCoreDeriv f g) {r : ℝ} (hr : 0 ≤ r) :
    HasCoreDeriv (fun t => f (t - r)) fun t => g (t - r) where
  measurable_deriv := h.measurable_deriv.comp (measurable_id.sub_const r)
  integrable_deriv := integrable_translate h.integrable_deriv r
  causal_deriv := fun s hs => h.causal_deriv (s - r) (by linarith)
  primitive := fun s => by
    rcases lt_or_ge s 0 with hs | hs
    · rw [h.causal (s - r) (by linarith), Ioc_eq_empty (not_lt.mpr hs.le), Measure.restrict_empty,
        integral_zero_measure]
    · have hsub : (∫ ρ in Ioc (0 : ℝ) s, g (ρ - r)) = ∫ w in Ioc (0 - r) (s - r), g w := by
        rw [← intervalIntegral.integral_of_le hs, ← intervalIntegral.integral_of_le (by linarith)]
        exact intervalIntegral.integral_comp_sub_right (fun w => g w) r
      rw [hsub, setIntegral_Ioc_of_causal h.integrable_deriv h.causal_deriv (by linarith) (s - r),
        h.primitive]
  integrable := integrable_translate h.integrable r

/-- **`lem:delay-core`, invariance under `Φ_{x,y}`**, with the derivative tracked:
`(μ ∗ f)' = μ ∗ f'`.

Stated for a causal probability measure — the level at which `lem:convolution-representation`
supplies `Φ`, and therefore the honest content of the node's `\uses` edge. Reading it back onto
an abstract `CascadeCore` is that representation theorem and not this lemma. -/
theorem conv {μ : Measure ℝ} [IsProbabilityMeasure μ] (h : HasCoreDeriv f g) (hμ : IsCausal μ) :
    HasCoreDeriv (mconv μ f) (mconv μ g) where
  measurable_deriv := measurable_mconv μ h.measurable_deriv
  integrable_deriv :=
    integrable_mconv μ h.integrable_deriv.aestronglyMeasurable h.integrable_deriv
  causal_deriv := fun _ hs => mconv_eq_zero_of_lt hμ h.causal_deriv hs
  primitive := mconv_eq_setIntegral_mconv hμ h.measurable_deriv h.integrable_deriv h.causal_deriv
    h.primitive
  integrable := integrable_mconv μ h.integrable.aestronglyMeasurable h.integrable

end HasCoreDeriv

/-- **The derivation check: `f ∈ 𝒟` is exactly what `thm:signaling-form` asks of its signal.**

An `iff`, and both halves are the point. Left to right is the obligation this file exists to
discharge — chapter 11 has been quantifying over the consequences of `f ∈ 𝒟` without `𝒟` existing,
and the model chosen here has to *supply* them, not merely be compatible with them. Right to left
says the model adds nothing: `𝒟` is not a strengthening smuggled in under a chapter-10 name.

The six conjuncts are, in order, the six hypotheses `signaling_form` takes about `f` and `g`.
`Measurable f` is the only one that is not a field of `HasCoreDeriv`; it comes from continuity of
the primitive. -/
theorem memCore_iff_signaling_hypotheses {f g : ℝ → ℝ} :
    HasCoreDeriv f g ↔
      Measurable g ∧ Integrable g ∧ (∀ r : ℝ, r < 0 → g r = 0) ∧
        Measurable f ∧ Integrable f ∧ (∀ r : ℝ, f r = ∫ ρ in Ioc (0 : ℝ) r, g ρ) :=
  ⟨fun h => ⟨h.measurable_deriv, h.integrable_deriv, h.causal_deriv, h.measurable, h.integrable,
      h.primitive⟩,
   fun ⟨hgm, hg, hgc, _, hfi, hf⟩ => ⟨hgm, hg, hgc, hf, hfi⟩⟩

/-! ## The core and `X₀`, on `X` -/

/-- **`X₀ = L¹(ℝ₊)`**, as the causal elements of `X`. -/
def causalL1 : Set X := {F | VanishesBefore 0 F}

/-- **`F ∈ 𝒟` with its derivative named, at the level of `L¹` classes.**

The existential over representatives is what a statement about `L¹` classes has to say: `𝒟` is a
subset of `X₀`, and membership is the existence of a representative in the core. -/
def HasCoreDerivL1 (F G : X) : Prop :=
  ∃ f g, HasCoreDeriv f g ∧ (F : ℝ → ℝ) =ᵐ[volume] f ∧ (G : ℝ → ℝ) =ᵐ[volume] g

/-- **`𝒟` as a subset of `X`.** -/
def coreL1 : Set X := {F | ∃ G, HasCoreDerivL1 F G}

/-- `𝒟 ⊆ X₀`: the core sits inside the causal part, which is what makes "dense in `X₀`" the right
statement rather than "dense in `X`". -/
theorem coreL1_subset_causalL1 : coreL1 ⊆ causalL1 := by
  rintro F ⟨G, f, g, hfg, hF, -⟩
  filter_upwards [hF] with t ht htlt
  rw [ht]
  exact hfg.causal t htlt

/-- `X₀` is invariant under the delay semigroup — the trivial half of `lem:delay-core`'s
invariance clause, and the one that does not mention the core. -/
theorem causalL1_transL1 {r : ℝ} (hr : 0 ≤ r) {F : X} (hF : F ∈ causalL1) :
    transL1 r F ∈ causalL1 := by
  have hsh : ∀ᵐ t : ℝ, t - r < 0 → (F : ℝ → ℝ) (t - r) = 0 :=
    (measurePreserving_sub_const r).quasiMeasurePreserving.ae hF
  change VanishesBefore 0 (transL1 r F)
  filter_upwards [coeFn_transL1 r F, hsh] with t ht hsub htlt
  rw [ht]
  exact hsub (by linarith)

/-- **`lem:delay-core`, invariance under `T_r` on `X`.** The function-level statement transported
along `coeFn_transL1`; the two-layer model is doing exactly the work it was chosen for, since the
content is all in `HasCoreDeriv.translate` and the transport is three lines. -/
theorem hasCoreDerivL1_transL1 {r : ℝ} (hr : 0 ≤ r) {F G : X} (h : HasCoreDerivL1 F G) :
    HasCoreDerivL1 (transL1 r F) (transL1 r G) := by
  obtain ⟨f, g, hfg, hF, hG⟩ := h
  exact ⟨fun t => f (t - r), fun t => g (t - r), hfg.translate hr,
    (coeFn_transL1 r F).trans (translate_congr_ae r hF),
    (coeFn_transL1 r G).trans (translate_congr_ae r hG)⟩

/-- **`lem:delay-core`, invariance under `Φ_{x,y}` on `X`.** -/
theorem hasCoreDerivL1_mconvL1 (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : IsCausal μ)
    {F G : X} (h : HasCoreDerivL1 F G) :
    HasCoreDerivL1 (mconvL1 μ F) (mconvL1 μ G) := by
  obtain ⟨f, g, hfg, hF, hG⟩ := h
  exact ⟨mconv μ f, mconv μ g, hfg.conv hμ,
    (coeFn_mconvL1 μ F).trans (mconv_congr_ae μ hF),
    (coeFn_mconvL1 μ G).trans (mconv_congr_ae μ hG)⟩

/-! ## The two quantitative clauses

Both run on one pointwise identity, `f(t) - f(t-r) = ∫₀^r g(t-u) du`, and one exchange of
integrals in `ℝ≥0∞` — where no integrability side condition is needed. The estimate takes the
crude bound `‖g(t-u)‖` on the inner integrand; the difference quotient subtracts `g(t)` first and
takes `‖T_u g - g‖₁`, which continuity of translation makes small. That is the whole difference
between them.
-/

/-- The `L¹` norm as a lower integral of a chosen representative. -/
theorem norm_eq_lintegral_of_ae {a : X} {φ : ℝ → ℝ} (h : (a : ℝ → ℝ) =ᵐ[volume] φ) :
    ‖a‖ = (∫⁻ t, ‖φ t‖ₑ).toReal := by
  rw [Lp.norm_def, eLpNorm_one_eq_lintegral_enorm]
  exact congrArg ENNReal.toReal (lintegral_congr_ae (h.mono fun t ht => by simp only [ht]))

namespace HasCoreDeriv

variable {f g : ℝ → ℝ}

/-- **The pointwise identity both quantitative clauses run on**: `f(t) - f(t-r) = ∫₀^r g(t-u) du`.

The reflection `u ↦ t - u` turns the right-hand side into `∫_{t-r}^t g`, and Chasles does the
rest. No sign condition on `r` or `t`: `eq_intervalIntegral` holds at every real point, which is
what it was extended to the negative half-line for. -/
theorem sub_translate (h : HasCoreDeriv f g) (r t : ℝ) :
    f t - f (t - r) = ∫ u in (0 : ℝ)..r, g (t - u) := by
  have hcomp : (∫ u in (0 : ℝ)..r, g (t - u)) = ∫ x in (t - r)..(t - 0), g x :=
    intervalIntegral.integral_comp_sub_left (fun x => g x) t
  have hadd : (∫ x in (0 : ℝ)..(t - r), g x) + (∫ x in (t - r)..t, g x) = ∫ x in (0 : ℝ)..t, g x :=
    intervalIntegral.integral_add_adjacent_intervals
      h.integrable_deriv.intervalIntegrable h.integrable_deriv.intervalIntegrable
  rw [hcomp, sub_zero, h.eq_intervalIntegral t, h.eq_intervalIntegral (t - r)]
  linarith

/-- The pointwise bound behind the estimate. -/
theorem enorm_sub_translate_le (h : HasCoreDeriv f g) {r : ℝ} (hr : 0 ≤ r) (t : ℝ) :
    ‖f (t - r) - f t‖ₑ ≤ ∫⁻ u in Ioc (0 : ℝ) r, ‖g (t - u)‖ₑ := by
  have hid : f (t - r) - f t = -∫ u in (0 : ℝ)..r, g (t - u) := by
    rw [← h.sub_translate r t]; ring
  rw [hid, enorm_neg, intervalIntegral.integral_of_le hr]
  exact enorm_integral_le_lintegral_enorm _

/-- The pointwise bound behind the difference quotient. Subtracting `g(t)` inside the integral is
the whole of the blueprint's `-h⁻¹∫_{t-h}^t (f'(ρ) - f'(t))dρ`. -/
theorem enorm_differenceQuotient_le (h : HasCoreDeriv f g) {r : ℝ} (hr : 0 < r) (t : ℝ) :
    ‖r⁻¹ * (f (t - r) - f t) + g t‖ₑ
      ≤ ENNReal.ofReal r⁻¹ * ∫⁻ u in Ioc (0 : ℝ) r, ‖g (t - u) - g t‖ₑ := by
  have hgt : IntervalIntegrable (fun u : ℝ => g (t - u)) volume 0 r :=
    (h.integrable_deriv.comp_sub_left t).intervalIntegrable
  have hsplit : (∫ u in (0 : ℝ)..r, (g (t - u) - g t))
      = (f t - f (t - r)) - r * g t := by
    rw [intervalIntegral.integral_sub hgt intervalIntegrable_const, ← h.sub_translate r t,
      intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  have hid : r⁻¹ * (f (t - r) - f t) + g t = -(r⁻¹ * ∫ u in (0 : ℝ)..r, (g (t - u) - g t)) := by
    rw [hsplit]
    field_simp
    ring
  rw [hid, enorm_neg, enorm_mul, Real.enorm_eq_ofReal (by positivity),
    intervalIntegral.integral_of_le hr.le]
  gcongr
  exact enorm_integral_le_lintegral_enorm _

end HasCoreDeriv

/-- The exchange of integrals behind the estimate: `∫∫_{(0,r]} ‖g(t-u)‖ = r·‖g‖₁`. -/
theorem lintegral_lintegral_enorm_translate {g : ℝ → ℝ} (hgm : Measurable g) (r : ℝ) :
    ∫⁻ t, (∫⁻ u in Ioc (0 : ℝ) r, ‖g (t - u)‖ₑ) = ENNReal.ofReal r * ∫⁻ w, ‖g w‖ₑ := by
  have hm : AEMeasurable (Function.uncurry fun t u : ℝ => ‖g (t - u)‖ₑ)
      (volume.prod (volume.restrict (Ioc (0 : ℝ) r))) := by
    have : Measurable (Function.uncurry fun t u : ℝ => ‖g (t - u)‖ₑ) := by
      unfold Function.uncurry
      fun_prop
    exact this.aemeasurable
  rw [lintegral_lintegral_swap hm]
  have hinner : ∀ u : ℝ, (∫⁻ t, ‖g (t - u)‖ₑ) = ∫⁻ w, ‖g w‖ₑ := fun u =>
    lintegral_sub_right_eq_self (fun w => ‖g w‖ₑ) u
  calc ∫⁻ u in Ioc (0 : ℝ) r, (∫⁻ t, ‖g (t - u)‖ₑ)
      = ∫⁻ _u in Ioc (0 : ℝ) r, ∫⁻ w, ‖g w‖ₑ := by simp only [hinner]
    _ = (∫⁻ w, ‖g w‖ₑ) * volume (Ioc (0 : ℝ) r) := setLIntegral_const _ _
    _ = ENNReal.ofReal r * ∫⁻ w, ‖g w‖ₑ := by
        rw [Real.volume_Ioc, sub_zero, mul_comm]

/-- The exchange of integrals behind the difference quotient. The inner integral is the `L¹`
distance from `g` to its own translate, which is what continuity of translation controls. -/
theorem lintegral_lintegral_enorm_translate_sub {g : ℝ → ℝ} (hgm : Measurable g) (r : ℝ) :
    ∫⁻ t, (∫⁻ u in Ioc (0 : ℝ) r, ‖g (t - u) - g t‖ₑ)
      = ∫⁻ u in Ioc (0 : ℝ) r, ∫⁻ t, ‖g (t - u) - g t‖ₑ := by
  have hm : AEMeasurable (Function.uncurry fun t u : ℝ => ‖g (t - u) - g t‖ₑ)
      (volume.prod (volume.restrict (Ioc (0 : ℝ) r))) := by
    have : Measurable (Function.uncurry fun t u : ℝ => ‖g (t - u) - g t‖ₑ) := by
      unfold Function.uncurry
      fun_prop
    exact this.aemeasurable
  exact lintegral_lintegral_swap hm

/-- `‖T_u f - f‖₁` as a lower integral of a chosen representative. -/
theorem norm_transL1_sub_eq_lintegral {G : X} {g : ℝ → ℝ} (hG : (G : ℝ → ℝ) =ᵐ[volume] g)
    (u : ℝ) : ‖transL1 u G - G‖ = (∫⁻ t, ‖g (t - u) - g t‖ₑ).toReal := by
  refine norm_eq_lintegral_of_ae ?_
  filter_upwards [Lp.coeFn_sub (transL1 u G) G, coeFn_transL1 u G, hG,
    (measurePreserving_sub_const u).quasiMeasurePreserving.ae hG] with t h1 h2 h3 h4
  simp only [h1, Pi.sub_apply, h2, h3, h4]

/-- **`lem:delay-core`, the estimate**: `‖T_r f - f‖₁ ≤ min(2‖f‖₁, r‖f'‖₁)`.

The first half is the triangle inequality and the isometry, and holds for every `f ∈ X`. The
second is where the core enters: `f(t-r) - f(t) = -∫₀^r f'(t-u)du`, and integrating that bound in
`t` is one exchange in `ℝ≥0∞`. The blueprint reaches it as the integrated form of the difference
quotient, through an `X`-valued Bochner integral `T_rf - f = -∫₀^r T_ρ f' dρ`; going through
`ℝ≥0∞` instead needs no integrability side condition and no vector-valued integral, and gives the
same constant. -/
theorem norm_transL1_sub_le {r : ℝ} (hr : 0 ≤ r) {F G : X} (h : HasCoreDerivL1 F G) :
    ‖transL1 r F - F‖ ≤ min (2 * ‖F‖) (r * ‖G‖) := by
  obtain ⟨f, g, hfg, hF, hG⟩ := h
  refine le_min ?_ ?_
  · calc ‖transL1 r F - F‖ ≤ ‖transL1 r F‖ + ‖F‖ := norm_sub_le _ _
      _ ≤ ‖F‖ + ‖F‖ := by gcongr; exact norm_transL1_le r F
      _ = 2 * ‖F‖ := by ring
  · have hLne : (∫⁻ w, ‖g w‖ₑ) ≠ ⊤ := by
      have h2 := hfg.integrable_deriv.2
      rw [hasFiniteIntegral_iff_enorm] at h2
      exact h2.ne
    have hbound : (∫⁻ t, ‖f (t - r) - f t‖ₑ) ≤ ENNReal.ofReal r * ∫⁻ w, ‖g w‖ₑ :=
      calc (∫⁻ t, ‖f (t - r) - f t‖ₑ)
          ≤ ∫⁻ t, ∫⁻ u in Ioc (0 : ℝ) r, ‖g (t - u)‖ₑ :=
            lintegral_mono fun t => hfg.enorm_sub_translate_le hr t
        _ = ENNReal.ofReal r * ∫⁻ w, ‖g w‖ₑ :=
            lintegral_lintegral_enorm_translate hfg.measurable_deriv r
    rw [norm_transL1_sub_eq_lintegral hF r, norm_eq_lintegral_of_ae hG]
    refine le_trans (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hLne)
      hbound) ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hr]

/-- **The difference quotient, quantitatively.** If every delay in `(0,r]` moves `f'` by at most
`ε` in `X₀`, then the quotient is within `ε` of `-f'`.

This is the whole of the blueprint's limit argument except for the choice of `ε`: the identity
`h⁻¹(T_hf - f) + f' = -h⁻¹∫₀^h (T_uf' - f')du` is exact, so the quotient is an *average* of the
translation defects and cannot exceed their supremum. The blueprint's separate treatment of the
interval `[0,h)`, where it uses `f(0) = 0`, is not needed in this form — `f(0) = 0` is already
inside `HasCoreDeriv`, carried by the primitive, and what it buys is the identity itself. -/
theorem norm_differenceQuotient_le {r : ℝ} (hr : 0 < r) {F G : X} (h : HasCoreDerivL1 F G)
    {ε : ℝ} (hε : ∀ u ∈ Ioc (0 : ℝ) r, ‖transL1 u G - G‖ ≤ ε) :
    ‖r⁻¹ • (transL1 r F - F) + G‖ ≤ ε := by
  obtain ⟨f, g, hfg, hF, hG⟩ := h
  have hε0 : 0 ≤ ε := le_trans (norm_nonneg _) (hε r ⟨hr, le_rfl⟩)
  set N : ℝ → ℝ≥0∞ := fun u => ∫⁻ t, ‖g (t - u) - g t‖ₑ with hN
  have hNne : ∀ u : ℝ, N u ≠ ⊤ := fun u => by
    have hint : Integrable fun t => g (t - u) - g t :=
      (hfg.integrable_deriv.comp_sub_right u).sub hfg.integrable_deriv
    have h2 := hint.2
    rw [hasFiniteIntegral_iff_enorm] at h2
    exact h2.ne
  have hNle : ∀ u ∈ Ioc (0 : ℝ) r, N u ≤ ENNReal.ofReal ε := fun u hu => by
    rw [← ENNReal.ofReal_toReal (hNne u), ← norm_transL1_sub_eq_lintegral hG u]
    exact ENNReal.ofReal_le_ofReal (hε u hu)
  -- the chosen representative of the quotient
  have hae : ((r⁻¹ • (transL1 r F - F) + G : X) : ℝ → ℝ)
      =ᵐ[volume] fun t => r⁻¹ * (f (t - r) - f t) + g t := by
    filter_upwards [Lp.coeFn_add (r⁻¹ • (transL1 r F - F)) G, Lp.coeFn_smul r⁻¹
      (transL1 r F - F), Lp.coeFn_sub (transL1 r F) F, coeFn_transL1 r F, hF, hG,
      (measurePreserving_sub_const r).quasiMeasurePreserving.ae hF] with t h1 h2 h3 h4 h5 h6 h7
    simp only [h1, Pi.add_apply, h2, Pi.smul_apply, h3, Pi.sub_apply, h4, h5, h6, h7, smul_eq_mul]
  have hbound : (∫⁻ t, ‖r⁻¹ * (f (t - r) - f t) + g t‖ₑ)
      ≤ ENNReal.ofReal r⁻¹ * (ENNReal.ofReal ε * ENNReal.ofReal r) :=
    calc (∫⁻ t, ‖r⁻¹ * (f (t - r) - f t) + g t‖ₑ)
        ≤ ∫⁻ t, ENNReal.ofReal r⁻¹ * ∫⁻ u in Ioc (0 : ℝ) r, ‖g (t - u) - g t‖ₑ :=
          lintegral_mono fun t => hfg.enorm_differenceQuotient_le hr t
      _ = ENNReal.ofReal r⁻¹ * ∫⁻ t, ∫⁻ u in Ioc (0 : ℝ) r, ‖g (t - u) - g t‖ₑ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal r⁻¹ * ∫⁻ u in Ioc (0 : ℝ) r, N u := by
          rw [lintegral_lintegral_enorm_translate_sub hfg.measurable_deriv r]
      _ ≤ ENNReal.ofReal r⁻¹ * ∫⁻ _u in Ioc (0 : ℝ) r, ENNReal.ofReal ε :=
          mul_le_mul' le_rfl (setLIntegral_mono' measurableSet_Ioc hNle)
      _ = ENNReal.ofReal r⁻¹ * (ENNReal.ofReal ε * ENNReal.ofReal r) := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero]
  rw [norm_eq_lintegral_of_ae hae]
  refine le_trans (ENNReal.toReal_mono (by finiteness) hbound) (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal hε0, ENNReal.toReal_ofReal hr.le]
  field_simp

/-- **`lem:delay-core`, the difference quotient**: `h⁻¹(T_h f - f) → -f'` in `X₀` as `h ↓ 0`.

Continuity of translation supplies the `ε`; `norm_differenceQuotient_le` does the rest, since the
quotient is an average of translation defects over `(0,h]` and every one of them is small once `h`
is. -/
theorem tendsto_differenceQuotient {F G : X} (h : HasCoreDerivL1 F G) :
    Tendsto (fun r : ℝ => r⁻¹ • (transL1 r F - F)) (𝓝[>] (0 : ℝ)) (𝓝 (-G)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine Metric.tendsto_nhds.mpr fun δ hδ => ?_
  obtain ⟨η, hη, hηb⟩ := Metric.eventually_nhds_iff.mp
    (Metric.tendsto_nhds.mp (tendsto_norm_transL1_sub G) (δ / 2) (by linarith))
  have h1 : ∀ᶠ r : ℝ in 𝓝 (0 : ℝ), dist r 0 < η :=
    Metric.eventually_nhds_iff.mpr ⟨η, hη, fun _ hx => hx⟩
  filter_upwards [h1.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with r hrη hrpos
  have hr : (0 : ℝ) < r := hrpos
  have hrlt : r < η := by rwa [Real.dist_eq, sub_zero, abs_of_pos hr] at hrη
  have hbound : ‖r⁻¹ • (transL1 r F - F) + G‖ ≤ δ / 2 := by
    refine norm_differenceQuotient_le hr h fun u hu => ?_
    have hdu : dist u (0 : ℝ) < η := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hu.1]
      linarith [hu.2]
    have hlt := hηb hdu
    rw [Real.dist_eq, sub_zero, abs_norm] at hlt
    exact hlt.le
  simp only [sub_neg_eq_add, Real.dist_eq, sub_zero, abs_norm]
  linarith

/-! ## Density

The blueprint says "standard", and the standard route is the wrong one: step functions are dense
in `X₀` and are not in `𝒟` at all, while the smooth compactly supported functions Mathlib does
supply are not causal. What works is the mollification `ρ_ε * f`, which lands *in* `𝒟` rather than
near it — and both halves of it are chapter 4's, `approxId` and `tendsto_bconv_approxId`. All that
has to be written here is that `ρ_ε * f` is the primitive of `ε⁻¹(f - T_ε f)`, which is Chasles
twice.
-/

/-- A causal element of `X` has a representative that is measurable and causal **at every point**.

Truncating a measurable representative below the origin costs nothing, because a causal class
already vanishes a.e. there — which is where the hypothesis is spent. `𝒟`'s pointwise reading
needs this: `HasCoreDeriv` quantifies over all of `ℝ`, not almost all of it. -/
theorem exists_causal_representative {F : X} (hF : F ∈ causalL1) :
    ∃ f : ℝ → ℝ, Measurable f ∧ Integrable f ∧ (∀ r : ℝ, r < 0 → f r = 0) ∧
      (F : ℝ → ℝ) =ᵐ[volume] f := by
  set f₁ := (Lp.aestronglyMeasurable F).mk (F : ℝ → ℝ) with hf₁
  have hm : Measurable f₁ := (Lp.aestronglyMeasurable F).stronglyMeasurable_mk.measurable
  have hae : (F : ℝ → ℝ) =ᵐ[volume] f₁ := (Lp.aestronglyMeasurable F).ae_eq_mk
  have hcut : (fun t => if t < 0 then (0 : ℝ) else f₁ t) =ᵐ[volume] f₁ := by
    filter_upwards [hae, hF] with t ht htc
    by_cases h0 : t < 0
    · simp only [if_pos h0, ← ht, htc h0]
    · simp only [if_neg h0]
  refine ⟨fun t => if t < 0 then (0 : ℝ) else f₁ t,
    Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const hm,
    ((L1.integrable_coeFn F).congr hae).congr hcut.symm, fun r hr => if_pos hr,
    hae.trans hcut.symm⟩

/-- **The mollification is the primitive of its own difference quotient**:
`(ρ_ε * f)(t) = ∫₀^t ε⁻¹(f(ρ) - f(ρ-ε)) dρ`.

Both sides are `ε⁻¹(P(t) - P(t-ε))` for `P` the primitive of `f`; the left by the substitution
`ρ = t - r` and Chasles, the right by Chasles after causality has discarded `∫_{-ε}^0 f`. This
is the whole content of the density clause. -/
theorem setIntegral_Ioc_differenceQuotient {f : ℝ → ℝ} (hf : Integrable f)
    (hfc : ∀ r : ℝ, r < 0 → f r = 0) {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    (∫ ρ in Ioc (0 : ℝ) t, ε⁻¹ * (f ρ - f (ρ - ε))) = ∫ r, approxId ε r * f (t - r) := by
  have hft : Integrable fun ρ : ℝ => f (ρ - ε) := integrable_translate hf ε
  have hftc : ∀ r : ℝ, r < 0 → f (r - ε) = 0 := fun r hr => hfc _ (by linarith)
  -- the left-hand side
  have hL : (∫ ρ in Ioc (0 : ℝ) t, ε⁻¹ * (f ρ - f (ρ - ε)))
      = ε⁻¹ * ((∫ ρ in (0 : ℝ)..t, f ρ) - ∫ ρ in (0 : ℝ)..(t - ε), f ρ) := by
    rw [integral_const_mul, integral_sub hf.integrableOn hft.integrableOn,
      setIntegral_Ioc_eq_intervalIntegral_of_causal hf hfc t,
      setIntegral_Ioc_eq_intervalIntegral_of_causal hft hftc t]
    congr 2
    have hshift : (∫ ρ in (0 : ℝ)..t, f (ρ - ε)) = ∫ w in (0 - ε)..(t - ε), f w :=
      intervalIntegral.integral_comp_sub_right (fun w => f w) ε
    have hchasles : (∫ w in (0 - ε)..(0 : ℝ), f w) + (∫ w in (0 : ℝ)..(t - ε), f w)
        = ∫ w in (0 - ε)..(t - ε), f w :=
      intervalIntegral.integral_add_adjacent_intervals hf.intervalIntegrable hf.intervalIntegrable
    have hleft : (∫ w in (0 - ε)..(0 : ℝ), f w) = 0 := by
      rw [intervalIntegral.integral_of_le (by linarith)]
      exact setIntegral_Ioc_eq_zero_of_causal hfc le_rfl
    rw [hshift, ← hchasles, hleft, zero_add]
  -- the right-hand side
  have hind : ∀ r : ℝ,
      approxId ε r * f (t - r) = ε⁻¹ * (Ioo (0 : ℝ) ε).indicator (fun r' => f (t - r')) r := by
    intro r
    by_cases hr : r ∈ Ioo (0 : ℝ) ε
    · rw [approxId, indicator_of_mem hr, indicator_of_mem hr, mul_one]
    · rw [approxId, indicator_of_notMem hr, indicator_of_notMem hr, mul_zero, zero_mul]
  have hR : (∫ r, approxId ε r * f (t - r))
      = ε⁻¹ * ((∫ ρ in (0 : ℝ)..t, f ρ) - ∫ ρ in (0 : ℝ)..(t - ε), f ρ) := by
    simp only [hind]
    rw [integral_const_mul, integral_indicator measurableSet_Ioo,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hε.le]
    congr 1
    have hsub : (∫ r in (0 : ℝ)..ε, f (t - r)) = ∫ w in (t - ε)..(t - 0), f w :=
      intervalIntegral.integral_comp_sub_left (fun w => f w) t
    have hchasles : (∫ w in (0 : ℝ)..(t - ε), f w) + (∫ w in (t - ε)..t, f w)
        = ∫ w in (0 : ℝ)..t, f w :=
      intervalIntegral.integral_add_adjacent_intervals hf.intervalIntegrable hf.intervalIntegrable
    rw [hsub, sub_zero]
    linarith
  rw [hL, hR]

/-- **`ρ_ε * f ∈ 𝒟`** for causal `f` and `ε > 0`, with derivative `ε⁻¹(f - T_ε f)`.

Causality of the mollifier is what makes this true rather than merely approximately true: `ρ_ε`
is carried by `[0,ε]`, so `ρ_ε * f` is causal and starts at the origin. -/
theorem hasCoreDerivL1_bconv_approxId {ε : ℝ} (hε : 0 < ε) {F : X} (hF : F ∈ causalL1) :
    bconv (approxId ε) F ∈ coreL1 := by
  obtain ⟨f, hfm, hfi, hfc, hFf⟩ := exists_causal_representative hF
  set g : ℝ → ℝ := fun t => ε⁻¹ * (f t - f (t - ε)) with hg
  set φ : ℝ → ℝ := fun t => ∫ ρ in Ioc (0 : ℝ) t, g ρ with hφ
  have hgm : Measurable g := (hfm.sub (hfm.comp (measurable_id.sub_const ε))).const_mul _
  have hgi : Integrable g := ((hfi.sub (integrable_translate hfi ε))).const_mul _
  have hgc : ∀ r : ℝ, r < 0 → g r = 0 := fun r hr => by
    simp only [hg, hfc r hr, hfc (r - ε) (by linarith), sub_zero, mul_zero]
  -- the mollification, computed
  have hbconv : (bconv (approxId ε) F : ℝ → ℝ) =ᵐ[volume] φ := by
    refine (coeFn_bconv (integrable_approxId ε) F).trans ?_
    refine .of_forall fun t => ?_
    show (∫ r, approxId ε r * (F : ℝ → ℝ) (t - r)) = φ t
    have hswap : (∫ r, approxId ε r * (F : ℝ → ℝ) (t - r)) = ∫ r, approxId ε r * f (t - r) := by
      refine integral_congr_ae ?_
      filter_upwards [(measurePreserving_const_sub t).quasiMeasurePreserving.ae hFf] with r hr
      rw [hr]
    rw [hswap]
    exact (setIntegral_Ioc_differenceQuotient hfi hfc hε t).symm
  have hφi : Integrable φ := (L1.integrable_coeFn (bconv (approxId ε) F)).congr hbconv
  exact ⟨hgi.toL1 g, φ, g, ⟨hgm, hgi, hgc, fun _ => rfl, hφi⟩, hbconv, hgi.coeFn_toL1⟩

/-- **`lem:delay-core`, density**: `𝒟` is dense in `X₀`.

Stated as `X₀ ⊆ closure 𝒟` rather than with `Dense`, which would ask for density in all of `X`:
`𝒟` is not dense in `X`, and `coreL1_subset_causalL1` is why. -/
theorem dense_coreL1 : causalL1 ⊆ closure coreL1 := fun F hF =>
  mem_closure_of_tendsto (tendsto_bconv_approxId F)
    ((eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)).mono fun _ hε =>
      hasCoreDerivL1_bconv_approxId hε hF)

/-- **`lem:delay-core` (Lemma 10.1).** `𝒟` is dense in `X₀` and invariant under every `T_r` and
every `Φ_{x,y}`; the difference quotient `h⁻¹(T_hf - f)` converges to `-f'` in `X₀`; and the
delay of a core element is controlled two ways.

The collation the node carries, assembled from the five lemmas above. Two things it says that
they do not. The `Φ`-clause is stated for the convolution operators
`lem:convolution-representation` produces, which is where the node's `\uses` edge is discharged.
And the invariance clauses appear here in the form the blueprint states — `T_r f ∈ 𝒟` — while the
lemmas prove the stronger tracked form `(T_r f)' = T_r f'`, which is what `def:phillips-generator`
will want. -/
theorem delay_core :
    causalL1 ⊆ closure coreL1 ∧
      (∀ r : ℝ, 0 ≤ r → ∀ F ∈ coreL1, transL1 r F ∈ coreL1) ∧
      (∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], IsCausal μ → ∀ F ∈ coreL1,
        mconvL1 μ F ∈ coreL1) ∧
      (∀ F G : X, HasCoreDerivL1 F G →
        Tendsto (fun r : ℝ => r⁻¹ • (transL1 r F - F)) (𝓝[>] (0 : ℝ)) (𝓝 (-G))) ∧
      (∀ r : ℝ, 0 ≤ r → ∀ F G : X, HasCoreDerivL1 F G →
        ‖transL1 r F - F‖ ≤ min (2 * ‖F‖) (r * ‖G‖)) :=
  ⟨dense_coreL1,
   fun _ hr _ ⟨G, hG⟩ => ⟨transL1 _ G, hasCoreDerivL1_transL1 hr hG⟩,
   fun μ _ hμ _ ⟨G, hG⟩ => ⟨mconvL1 μ G, hasCoreDerivL1_mconvL1 μ hμ hG⟩,
   fun _ _ h => tendsto_differenceQuotient h,
   fun _ hr _ _ h => norm_transL1_sub_le hr h⟩

end Hemigroup
