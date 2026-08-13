/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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

## The composition with the sign

`iteratedDerivWithin_comp_const_smul` does not apply: it asks the dilation to map the set to
itself, and `u ↦ -u` maps `(0,∞)` to `(-∞,0)`. So the sign is carried through by a direct
induction, which needs only that `(0,∞)` is open (so that the inductive hypothesis is an
`EventuallyEq` and `deriv` respects it) and Mathlib's `hasDerivAt_iteratedDeriv_mgf`.
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

/-- **The derivatives of the profile**, with the sign carried through by induction: on `(0,∞)`,
`H^{(j)}(u) = (-1)^j · (d/dt)^j mgf(t)|_{t = -u}`. -/
theorem iteratedDeriv_profile_eq_mgf (j : ℕ) {u : ℝ} (hu : 0 < u) :
    iteratedDeriv j F.profile u = (-1) ^ j * iteratedDeriv j (mgf id F.lawT₁) (-u) := by
  have hprof : F.profile = fun v : ℝ => mgf id F.lawT₁ (-v) := funext F.profile_eq_mgf
  induction j generalizing u with
  | zero => simp [hprof]
  | succ k ih =>
      have hopen : Ioi (0 : ℝ) ∈ 𝓝 u := isOpen_Ioi.mem_nhds hu
      have heq : iteratedDeriv k F.profile
          =ᶠ[𝓝 u] fun v : ℝ => (-1) ^ k * iteratedDeriv k (mgf id F.lawT₁) (-v) := by
        filter_upwards [hopen] with v hv
        exact ih hv
      have hderiv : HasDerivAt (fun v : ℝ => (-1) ^ k * iteratedDeriv k (mgf id F.lawT₁) (-v))
          ((-1) ^ k * (-(iteratedDeriv (k + 1) (mgf id F.lawT₁) (-u)))) u := by
        have hbase := hasDerivAt_iteratedDeriv_mgf (F.neg_mem_interior_integrableExpSet hu) k
        have hval : iteratedDeriv (k + 1) (mgf id F.lawT₁) (-u)
            = F.lawT₁[fun ω => id ω ^ (k + 1) * Real.exp (-u * id ω)] :=
          iteratedDeriv_mgf (F.neg_mem_interior_integrableExpSet hu) (k + 1)
        rw [hval]
        have hneg : HasDerivAt (fun v : ℝ => -v) (-1 : ℝ) u := hasDerivAt_neg u
        have := (hbase.comp u hneg)
        simpa using this.const_mul ((-1 : ℝ) ^ k)
      rw [iteratedDeriv_succ, heq.deriv_eq, hderiv.deriv, iteratedDeriv_succ]
      ring

/-- **`H^{(j)}(u) = (-1)^j E[T₁^j e^{-uT₁}]`**, the form the profile clause of
`def:locality-pmp` needs. -/
theorem iteratedDeriv_profile (j : ℕ) {u : ℝ} (hu : 0 < u) :
    iteratedDeriv j F.profile u
      = (-1) ^ j * ∫ t, t ^ j * Real.exp (-(u * t)) ∂F.lawT₁ := by
  rw [F.iteratedDeriv_profile_eq_mgf j hu,
    iteratedDeriv_mgf (F.neg_mem_interior_integrableExpSet hu) j]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp [neg_mul]

/-- Each derivative of the profile is again differentiable on `(0,∞)`, since each is a sign times
a derivative of the `mgf` and Mathlib knows those are analytic on the interior. -/
theorem differentiableAt_iteratedDeriv_profile (j : ℕ) {u : ℝ} (hu : 0 < u) :
    DifferentiableAt ℝ (iteratedDeriv j F.profile) u := by
  have heq : iteratedDeriv j F.profile
      =ᶠ[𝓝 u] fun v : ℝ => (-1) ^ j * iteratedDeriv j (mgf id F.lawT₁) (-v) := by
    filter_upwards [isOpen_Ioi.mem_nhds hu] with v hv
    exact F.iteratedDeriv_profile_eq_mgf j hv
  refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
  have hinner : DifferentiableAt ℝ (fun v : ℝ => iteratedDeriv j (mgf id F.lawT₁) (-v)) u :=
    (differentiableAt_iteratedDeriv_mgf (F.neg_mem_interior_integrableExpSet hu) j).comp u
      (differentiable_neg u)
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

`∂ᵥ^j (H(v) : ℂ) = (-1)^j E[T₁^j e^{-vT₁}]` on `(0,∞)`, in the complex form
`def:locality-pmp` states the clause in. -/
theorem iteratedDeriv_profileC (j : ℕ) {u : ℝ} (hu : 0 < u) :
    iteratedDeriv j (fun v : ℝ => (F.profile v : ℂ)) u
      = (((-1) ^ j * ∫ t, t ^ j * Real.exp (-(u * t)) ∂F.lawT₁ : ℝ) : ℂ) := by
  rw [iteratedDeriv_ofReal_comp isOpen_Ioi
    (fun k x hx => F.differentiableAt_iteratedDeriv_profile k hx) j (mem_Ioi.mpr hu),
    F.iteratedDeriv_profile j hu]

end SelfDecomposableExponent

end Hemigroup
