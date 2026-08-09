/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.Symmetries

/-!
# `def:cascade-family`: the axioms, as a structure on `L¹`

The primitive object of the article, stated in Lean. Every earlier file proves things *about*
kernels; this one says what it means to be a causal cascade measurement family, and is
therefore the only file in the development where an error is silent — a mis-stated axiom makes
the theorem vacuous or false rather than unprovable. The guard against that is the instance:
`Construction.lean`'s family is exhibited as a `CascadeFamily`, so the specification is checked
against a model known independently to satisfy the mathematics.

## Fidelity notes

Each field is the blueprint clause, not a convenient variant.

* **(A1)** is carried by the type: `X →L[ℝ] X` *is* "bounded linear operator on `X`".
* **(A5)** is stated on the positive cone only, as the blueprint states it. It happens to hold
  for all of `X` in the constructed family, but strengthening the field would *narrow* the
  structure, and a narrower specification is a different theorem.
* **(A3)**'s hypothesis and conclusion are both `a.e.`, as in the blueprint. The pointwise form
  is false for `μ = δ_{r₀}` — see `Operator.lean`'s note — which is exactly why the a.e. form is
  the right one here.
* **(A8)** carries the action `S` as data together with the requirement that each `S σ` be an
  increasing bijection of `[0,∞)`; `\Sact` is existentially quantified in the blueprint, and
  bundling it is the standard Lean rendering of that.

## State

The structure is stated in full. Of the transport results, (A2)–(A5) are proved here; (A6),
(A7), (A8) and (ND) are still to come, and the instance is assembled once they are all
available.
-/

namespace Hemigroup

open MeasureTheory Set
open scoped ENNReal

/-- `X = L¹(ℝ)`, the space `def:cascade-family` acts on. -/
noncomputable abbrev X := ℝ →₁[volume] ℝ

/-- The positive cone `X₊`. -/
def IsNonneg (f : X) : Prop := 0 ≤ᵐ[volume] (f : ℝ → ℝ)

/-- `f` vanishes a.e. on `(-∞, t₀)` — the hypothesis and the conclusion of (A3). -/
def VanishesBefore (t₀ : ℝ) (f : X) : Prop := ∀ᵐ t ∂volume, t < t₀ → (f : ℝ → ℝ) t = 0

/-- **`def:cascade-family`**: a causal cascade measurement family. -/
structure CascadeFamily where
  /-- The operators, indexed by ordered pairs of scales. (A1) is the type. -/
  Φ : ℝ → ℝ → (X →L[ℝ] X)
  /-- The scaling action `S_σ` of (A8), carried as data. -/
  S : ℝ → ℝ → ℝ
  /-- **(A2)** Time-translation covariance. -/
  translation : ∀ x y a f, Φ x y (transL1 a f) = transL1 a (Φ x y f)
  /-- **(A3)** Causality. -/
  causal : ∀ x y t₀ f, VanishesBefore t₀ f → VanishesBefore t₀ (Φ x y f)
  /-- **(A4)** Positivity. -/
  positive : ∀ x y f, IsNonneg f → IsNonneg (Φ x y f)
  /-- **(A5)** Unit area, on the positive cone. -/
  unit_area : ∀ x y f, IsNonneg f →
    ∫ t, ((Φ x y f : X) : ℝ → ℝ) t = ∫ t, (f : ℝ → ℝ) t
  /-- **(A6)** The diagonal is the identity. -/
  refl : ∀ x, 0 ≤ x → Φ x x = ContinuousLinearMap.id ℝ X
  /-- **(A6)** The cascade law — a hemigroup, not a semigroup: no dependence on `y - x`. -/
  cascade : ∀ x y z, 0 ≤ x → x ≤ y → y ≤ z → (Φ y z).comp (Φ x y) = Φ x z
  /-- **(A7)** Continuity in the parameters, into `X`. -/
  continuous : ∀ f : X, ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2 f)
    {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2}
  /-- **(A8)** Each `S σ` maps `[0,∞)` into itself, ... -/
  S_mapsTo : ∀ σ, 0 < σ → MapsTo (S σ) (Ici 0) (Ici 0)
  /-- ... increasingly, ... -/
  S_strictMonoOn : ∀ σ, 0 < σ → StrictMonoOn (S σ) (Ici 0)
  /-- ... and onto. -/
  S_surjOn : ∀ σ, 0 < σ → SurjOn (S σ) (Ici 0) (Ici 0)
  /-- **(A8)** Scale covariance. -/
  scale : ∀ (σ : ℝ) (hσ : 0 < σ) (x y : ℝ), 0 ≤ x → x ≤ y →
    (dilL1 hσ).comp (Φ x y) = (Φ (S σ x) (S σ y)).comp (dilL1 hσ)
  /-- **(ND)** Nondegeneracy. -/
  nondegenerate : ∀ x y, 0 ≤ x → x < y → Φ x y ≠ ContinuousLinearMap.id ℝ X

/-! ## Transport: the axioms for `Φ f = μ * f`

Each is the corresponding result of `Operator.lean` read through `coeFn_mconvL1`, with the
pointwise hypotheses those results take supplied a.e. by `ae_ae_sub_of_ae`.
-/

variable {μ : Measure ℝ}

/-- **(A2)** for `mconvL1`: convolution commutes with translation. -/
theorem mconvL1_transL1 [IsFiniteMeasure μ] (a : ℝ) (f : X) :
    mconvL1 μ (transL1 a f) = transL1 a (mconvL1 μ f) := by
  refine Lp.ext ?_
  refine (coeFn_mconvL1 μ (transL1 a f)).trans ?_
  refine (mconv_congr_ae μ (coeFn_transL1 a f)).trans ?_
  rw [mconv_comp_sub]
  refine Filter.EventuallyEq.symm ?_
  refine (coeFn_transL1 a (mconvL1 μ f)).trans ?_
  exact translate_congr_ae a (coeFn_mconvL1 μ f)

/-- **(A3)** for `mconvL1`: a causal measure cannot move mass backwards.

The blueprint's hypothesis is `a.e.`, and the pointwise conclusion of `mconv_eq_zero_of_lt`
cannot be had from it. What `ae_ae_sub_of_ae` supplies instead is exactly enough: for a.e. `t`,
the integrand vanishes for `μ`-a.e. `r`, because causality forces `t - r ≤ t < t₀`. -/
theorem vanishesBefore_mconvL1 [IsFiniteMeasure μ] (hμ : IsCausal μ) (t₀ : ℝ) (f : X)
    (hf : VanishesBefore t₀ f) : VanishesBefore t₀ (mconvL1 μ f) := by
  filter_upwards [coeFn_mconvL1 μ f, ae_ae_sub_of_ae μ hf] with t hcoe ht hlt
  rw [hcoe, mconv_apply]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [ht, hμ.ae_nonneg] with r hr hr0
  exact hr (by linarith)

/-- **(A4)** for `mconvL1`: the positive cone is preserved. -/
theorem isNonneg_mconvL1 [IsFiniteMeasure μ] (f : X) (hf : IsNonneg f) :
    IsNonneg (mconvL1 μ f) := by
  filter_upwards [coeFn_mconvL1 μ f, ae_ae_sub_of_ae μ hf] with t hcoe ht
  rw [Pi.zero_apply, hcoe, mconv_apply]
  exact integral_nonneg_of_ae ht

/-- **(A6)** for `mconvL1`, the cascade clause: composing the operators convolves the measures.

Note the order — `Φ_{y,z} Φ_{x,y}` corresponds to `μ_{x,y} ∗ μ_{y,z}`, which is what
`kernel_conv` produces. -/
theorem mconvL1_comp (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure (μ ∗ ν)] :
    (mconvL1 ν).comp (mconvL1 μ) = mconvL1 (μ ∗ ν) := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  refine (coeFn_mconvL1 ν (mconvL1 μ f)).trans ?_
  refine (mconv_congr_ae ν (coeFn_mconvL1 μ f)).trans ?_
  refine (mconv_conv μ ν (Lp.aestronglyMeasurable f) (L1.integrable_coeFn f)).trans ?_
  exact (coeFn_mconvL1 (μ ∗ ν) f).symm

/-- **(A6)** for `mconvL1`, the diagonal clause: `δ₀ * f = f`. -/
theorem mconvL1_dirac_zero : mconvL1 (Measure.dirac (0 : ℝ)) = ContinuousLinearMap.id ℝ X := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  refine (coeFn_mconvL1 _ f).trans ?_
  rw [mconv_dirac_zero]
  rfl

/-- **(A5)** for `mconvL1`: unit area, for a probability measure.

Stated for every `f`, though `def:cascade-family` only asks it on the positive cone: the
Tonelli identity behind `integral_mconv` does not see the sign. -/
theorem integral_mconvL1 [IsProbabilityMeasure μ] (f : X) :
    ∫ t, ((mconvL1 μ f : X) : ℝ → ℝ) t = ∫ t, (f : ℝ → ℝ) t := by
  rw [integral_congr_ae (coeFn_mconvL1 μ f),
    integral_mconv μ (Lp.aestronglyMeasurable f) (L1.integrable_coeFn f),
    measure_univ, ENNReal.toReal_one, one_mul]

end Hemigroup
