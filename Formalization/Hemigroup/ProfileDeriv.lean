/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Hemigroup.MellinData
import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Derivatives of the profile

The profile clause of `def:locality-pmp` speaks of `∂ₓ^j H(sx)`, and chapter 11 never had occasion
to differentiate `H` at all --- its whole calculus is on the transform side. What is needed is

  `H^{(j)}(u) = (-1)^j E[T₁^j e^{-uT₁}]`   (`u > 0`),

differentiation under the integral sign `j` times.

## It is free, and the reason is worth recording

`H(u) = E[e^{-uT₁}]` **is Mathlib's moment generating function** at a negative argument:
`H(u) = mgf id lawT₁ (-u)`. Mathlib carries `ProbabilityTheory.iteratedDeriv_mgf`, which gives
every derivative on the interior of the set where the exponential moment converges --- and for a
law on `[0,∞)` that set contains `(-∞, 0]`, so its interior contains every argument the article
uses. The dominated-convergence induction that this step looked like it needed is already done.

The repo's `laplace` and Mathlib's `mgf` are the same object under a sign, which is the only
thing that has to be checked (`profile_eq_mgf`). It is worth noticing that the development already
used the complex counterpart --- `InversionSymbol.lean` identifies `negMomentC` with
`complexMGF` --- so the two vocabularies had met once before, on the other transform.

## The sign and the dilation, in one induction

What the clause actually needs is `∂ᵥ^j H(sv)`, so both a sign and a dilation stand between the
profile and the `mgf`. Neither is composed on afterwards: `iteratedDerivWithin_comp_const_smul`
asks the dilation to map the set to *itself*, and `v ↦ (-s)v` maps `(0,∞)` to `(-∞,0)`, so it does
not apply --- and reaching for it would in any case require `ContDiffOn` of the profile, hence the
analyticity of `mgf` transported across the sign, to reprove what one induction gives directly.

The induction needs only that `(0,∞)` is open --- so the inductive hypothesis is an `EventuallyEq`
and `deriv` respects it --- together with Mathlib's `hasDerivAt_iteratedDeriv_mgf`.
-/

namespace Hemigroup

open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent)

/-- The profile is Mathlib's moment generating function at a negative argument. -/
theorem profile_eq_mgf (u : ℝ) : F.profile u = mgf id F.lawT₁ (-u) := by
  rw [profile, laplace, mgf]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp [neg_mul]

/-- A causal law has every negative exponential moment: the integrand is bounded by `1`. -/
theorem Iic_subset_integrableExpSet : Iic (0 : ℝ) ⊆ integrableExpSet id F.lawT₁ := by
  intro t ht
  have hae : ∀ᵐ ω ∂F.lawT₁, ‖Real.exp (t * id ω)‖ ≤ 1 := by
    filter_upwards [F.isCausal_lawT₁.ae_nonneg] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg ht hω)
  exact Integrable.mono' (integrable_const 1) (by fun_prop) hae

/-- Every argument the article uses lies in the interior. -/
theorem neg_mem_interior_integrableExpSet {u : ℝ} (hu : 0 < u) :
    -u ∈ interior (integrableExpSet id F.lawT₁) := by
  have hsub : Iio (0 : ℝ) ⊆ interior (integrableExpSet id F.lawT₁) :=
    interior_maximal (Iio_subset_Iic_self.trans F.Iic_subset_integrableExpSet) isOpen_Iio
  exact hsub (mem_Iio.mpr (neg_lt_zero.mpr hu))

/-- **The derivatives of the dilated profile**, sign and dilation carried through together by one
induction: on `(0,∞)`, `∂ᵥ^j H(sv)|_{v=u} = (-s)^j · (d/dt)^j mgf(t)|_{t = -su}`.

The dilation is built in rather than composed afterwards. Composing would need
`iteratedDerivWithin_comp_const_smul`, hence `ContDiffOn` of the profile, hence the analyticity of
`mgf` transported across the sign --- all to reprove what the same induction gives directly. -/
theorem iteratedDeriv_profile_comp_mul_eq_mgf {s : ℝ} (hs : 0 < s) (j : ℕ) {u : ℝ} (hu : 0 < u) :
    iteratedDeriv j (fun v : ℝ => F.profile (s * v)) u
      = (-s) ^ j * iteratedDeriv j (mgf id F.lawT₁) ((-s) * u) := by
  have hprof : (fun v : ℝ => F.profile (s * v)) = fun v : ℝ => mgf id F.lawT₁ ((-s) * v) := by
    funext v
    rw [F.profile_eq_mgf]
    ring_nf
  have hmem : ∀ {v : ℝ}, 0 < v → (-s) * v ∈ interior (integrableExpSet id F.lawT₁) := by
    intro v hv
    have := F.neg_mem_interior_integrableExpSet (mul_pos hs hv)
    simpa [neg_mul] using this
  induction j generalizing u with
  | zero => simp [hprof]
  | succ k ih =>
      have heq : iteratedDeriv k (fun v : ℝ => F.profile (s * v))
          =ᶠ[𝓝 u] fun v : ℝ => (-s) ^ k * iteratedDeriv k (mgf id F.lawT₁) ((-s) * v) := by
        filter_upwards [isOpen_Ioi.mem_nhds hu] with v hv
        exact ih hv
      have hderiv : HasDerivAt
          (fun v : ℝ => (-s) ^ k * iteratedDeriv k (mgf id F.lawT₁) ((-s) * v))
          ((-s) ^ k * (iteratedDeriv (k + 1) (mgf id F.lawT₁) ((-s) * u) * (-s))) u := by
        have hbase := hasDerivAt_iteratedDeriv_mgf (hmem hu) k
        have hval : iteratedDeriv (k + 1) (mgf id F.lawT₁) ((-s) * u)
            = F.lawT₁[fun ω => id ω ^ (k + 1) * Real.exp ((-s) * u * id ω)] :=
          iteratedDeriv_mgf (hmem hu) (k + 1)
        rw [hval]
        have hinner : HasDerivAt (fun v : ℝ => (-s) * v) (-s) u := by
          simpa using (hasDerivAt_id u).const_mul (-s)
        exact (hbase.comp u hinner).const_mul ((-s) ^ k)
      rw [iteratedDeriv_succ, heq.deriv_eq, hderiv.deriv, iteratedDeriv_succ]
      ring

/-- **`∂ᵥ^j H(sv)|_{v=u} = (-s)^j E[T₁^j e^{-suT₁}]`**, the form the profile clause of
`def:locality-pmp` needs. -/
theorem iteratedDeriv_profile_comp_mul {s : ℝ} (hs : 0 < s) (j : ℕ) {u : ℝ} (hu : 0 < u) :
    iteratedDeriv j (fun v : ℝ => F.profile (s * v)) u
      = (-s) ^ j * ∫ t, t ^ j * Real.exp (-(s * u * t)) ∂F.lawT₁ := by
  have hmem : (-s) * u ∈ interior (integrableExpSet id F.lawT₁) := by
    have := F.neg_mem_interior_integrableExpSet (mul_pos hs hu)
    simpa [neg_mul] using this
  rw [F.iteratedDeriv_profile_comp_mul_eq_mgf hs j hu, iteratedDeriv_mgf hmem j]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp [neg_mul]

/-- Each derivative of the profile is again differentiable on `(0,∞)`, since each is a sign times
a derivative of the `mgf` and Mathlib knows those are analytic on the interior. -/
theorem differentiableAt_iteratedDeriv_profile_comp_mul {s : ℝ} (hs : 0 < s) (j : ℕ) {u : ℝ}
    (hu : 0 < u) : DifferentiableAt ℝ (iteratedDeriv j fun v : ℝ => F.profile (s * v)) u := by
  have hmem : (-s) * u ∈ interior (integrableExpSet id F.lawT₁) := by
    have := F.neg_mem_interior_integrableExpSet (mul_pos hs hu)
    simpa [neg_mul] using this
  have heq : (iteratedDeriv j fun v : ℝ => F.profile (s * v))
      =ᶠ[𝓝 u] fun v : ℝ => (-s) ^ j * iteratedDeriv j (mgf id F.lawT₁) ((-s) * v) := by
    filter_upwards [isOpen_Ioi.mem_nhds hu] with v hv
    exact F.iteratedDeriv_profile_comp_mul_eq_mgf hs j hv
  refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
  have hinner : DifferentiableAt ℝ (fun v : ℝ => iteratedDeriv j (mgf id F.lawT₁) ((-s) * v)) u :=
    (differentiableAt_iteratedDeriv_mgf hmem j).comp u ((differentiable_id.const_mul (-s)) u)
  exact hinner.const_mul _

end SelfDecomposableExponent

/-! ## Iterated derivatives and the real-to-complex coercion

`def:locality-pmp`'s profile clause differentiates `u ↦ (H(su) : ℂ)`, while everything proved
above is about the real `H`. The two agree, and the proof is an induction that needs only an open
set on which every derivative is again differentiable --- so it is stated that way rather than
through `ContinuousLinearMap.iteratedFDerivWithin_comp_left`, which would require converting
between `iteratedFDeriv` and `iteratedDeriv` at each step. -/

/-- On an open set where every iterated derivative is differentiable, `iteratedDeriv` commutes
with `ofReal`. -/
theorem iteratedDeriv_ofReal_comp {f : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (hf : ∀ j : ℕ, ∀ x ∈ s, DifferentiableAt ℝ (iteratedDeriv j f) x) :
    ∀ (j : ℕ) {x : ℝ}, x ∈ s →
      iteratedDeriv j (fun u : ℝ => (f u : ℂ)) x = ((iteratedDeriv j f x : ℝ) : ℂ) := by
  intro j
  induction j with
  | zero => intro x _; simp
  | succ k ih =>
      intro x hx
      have heq : iteratedDeriv k (fun u : ℝ => (f u : ℂ))
          =ᶠ[𝓝 x] fun v : ℝ => ((iteratedDeriv k f v : ℝ) : ℂ) := by
        filter_upwards [hs.mem_nhds hx] with v hv
        exact ih hv
      have hd : HasDerivAt (fun v : ℝ => ((iteratedDeriv k f v : ℝ) : ℂ))
          ((iteratedDeriv (k + 1) f x : ℝ) : ℂ) x := by
        have hbase : HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f x) x := by
          rw [iteratedDeriv_succ]
          exact (hf k x hx).hasDerivAt
        exact hbase.ofReal_comp
      rw [iteratedDeriv_succ, heq.deriv_eq, hd.deriv]

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent)

/-- **The profile clause's derivative side, as an explicit integral.**

`∂ᵥ^j (H(sv) : ℂ)|_{v=u} = (-s)^j E[T₁^j e^{-suT₁}]` on `(0,∞)`, in the complex form
`def:locality-pmp` states the clause in. This is what the Fubini computation consumes. -/
theorem iteratedDeriv_profileC_comp_mul {s : ℝ} (hs : 0 < s) (j : ℕ) {u : ℝ} (hu : 0 < u) :
    iteratedDeriv j (fun v : ℝ => (F.profile (s * v) : ℂ)) u
      = (((-s) ^ j * ∫ t, t ^ j * Real.exp (-(s * u * t)) ∂F.lawT₁ : ℝ) : ℂ) := by
  rw [iteratedDeriv_ofReal_comp (f := fun v : ℝ => F.profile (s * v)) isOpen_Ioi
    (fun k x hx => F.differentiableAt_iteratedDeriv_profile_comp_mul hs k hx) j
    (mem_Ioi.mpr hu), F.iteratedDeriv_profile_comp_mul hs j hu]

end SelfDecomposableExponent

end Hemigroup
