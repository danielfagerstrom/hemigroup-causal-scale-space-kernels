/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Hemigroup.TransformContinuity

/-!
# `lem:additivity`: the cascade, at the level of measures and exponents

Chapter 5 opens by transporting (A6) down two levels. `lem:convolution-representation` turned
the operators into measures; composition of operators is convolution of measures, and the
Laplace transform turns that into multiplication, so `-\log` turns it into addition. What comes
out is a two-parameter family of exponents that is *additive along the cascade*, hence the
difference of a single one-parameter function `G(x, s) = g_{0,x}(s)`.

## Why this is short

Every step is a transport of something already proved. The only inputs are (A6) itself,
`Phi_eq_mconvL1_repr`, and `mconvL1_injective` — the uniqueness clause, which is what lets an
identity between *operators* be read as an identity between *measures*. Positivity of the
transform, needed to split the logarithm, is `laplace_pos_of_prob`.

## What the next chapter needs, and what the companion note needs

`thm:increments-bernstein` consumes exactly two things from here: additivity, to write
`g_{x,y}` as a sum over a partition, and continuity of `G(\cdot, s)`, to make the mesh of that
sum vanish. Both are below.

The monotonicity clause is worth naming separately. The companion note reads the covariance-free
stratum as "`x \mapsto b(x)` and `x \mapsto \nu_x` are nondecreasing, and all increments are
Bernstein" — the first half of which is `G_monotoneOn` here, the second `thm:increments-bernstein`.
Stating monotonicity of `G` now, rather than leaving it inside a proof, is what makes that
reading available later without re-deriving it.
-/

namespace Hemigroup

open MeasureTheory Set

namespace CascadeCore

variable {Fam : CascadeCore} {x y z : ℝ}

/-! ## (A6), transported to the representing measures -/

/-- **The cascade law as a convolution**: `μ_{x,z} = μ_{x,y} ∗ μ_{y,z}`.

The blueprint writes `μ_{y,z} * μ_{x,y}`; convolution of measures on `ℝ` is commutative, and
this is the order `mconvL1_comp` produces — the first-applied operator on the left. -/
theorem repr_conv (hx : 0 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) :
    Fam.repr x z = Fam.repr x y ∗ Fam.repr y z := by
  refine mconvL1_injective (isCausal_repr Fam x z)
    ((isCausal_repr Fam x y).conv (isCausal_repr Fam y z)) ?_
  rw [← Phi_eq_mconvL1_repr hx (hxy.trans hyz), ← mconvL1_comp,
    ← Phi_eq_mconvL1_repr hx hxy, ← Phi_eq_mconvL1_repr (hx.trans hxy) hyz]
  exact (Fam.cascade x y z hx hxy hyz).symm

/-- **The diagonal**: `μ_{x,x} = δ₀`. -/
theorem repr_self (hx : 0 ≤ x) : Fam.repr x x = Measure.dirac 0 := by
  refine mconvL1_injective (isCausal_repr Fam x x) (isCausal_dirac le_rfl) ?_
  rw [← Phi_eq_mconvL1_repr hx le_rfl, mconvL1_dirac_zero]
  exact Fam.refl x hx

/-- **(ND) transported**: strictly below the diagonal the representing measure is not `δ₀`. -/
theorem repr_ne_dirac (hx : 0 ≤ x) (hxy : x < y) : Fam.repr x y ≠ Measure.dirac 0 := by
  intro h
  refine Fam.nondegenerate x y hx hxy ?_
  rw [Phi_eq_mconvL1_repr hx hxy.le, mconvL1_congr h, mconvL1_dirac_zero]

/-! ## Additivity of the exponents -/

/-- **`g_{x,z} = g_{x,y} + g_{y,z}`.** Convolution becomes multiplication under the transform,
and multiplication becomes addition under `-\log` — legitimate because the transform of a causal
probability measure never vanishes. -/
theorem exponent_add (hx : 0 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) {s : ℝ} (hs : 0 ≤ s) :
    Fam.exponent x z s = Fam.exponent x y s + Fam.exponent y z s := by
  simp only [exponent]
  rw [repr_conv hx hxy hyz, laplace_conv,
    Real.log_mul (laplace_pos_of_prob (isCausal_repr Fam x y) hs).ne'
      (laplace_pos_of_prob (isCausal_repr Fam y z) hs).ne']
  ring

/-- **`g_{x,x} = 0`.** -/
@[simp] theorem exponent_self (hx : 0 ≤ x) (s : ℝ) : Fam.exponent x x s = 0 := by
  simp only [exponent, repr_self hx, laplace_dirac_zero, Real.log_one, neg_zero]

/-- **(ND) at the level of exponents**: the increment does not vanish identically.

This is everything `cor:strict-monotonicity` needs from (ND). What that corollary still waits on
is `thm:increments-bernstein`: knowing `g_{x,y}` is a Lévy exponent, the vanishing lemma
upgrades "not identically zero" to "nowhere zero on `(0,∞)`", and with `exponent_nonneg` that is
strict positivity. -/
theorem exists_exponent_ne_zero (hx : 0 ≤ x) (hxy : x < y) :
    ∃ s, 0 ≤ s ∧ Fam.exponent x y s ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  refine repr_ne_dirac hx hxy
    (laplace_injective (isCausal_repr Fam x y) (isCausal_dirac le_rfl) fun s hs => ?_)
  rw [laplace_dirac_zero]
  have hpos := laplace_pos_of_prob (isCausal_repr Fam x y) hs
  have hlog : Real.log (laplace (Fam.repr x y) s) = 0 := by
    have := hcon s hs
    rw [exponent, neg_eq_zero] at this
    exact this
  calc laplace (Fam.repr x y) s = Real.exp (Real.log (laplace (Fam.repr x y) s)) :=
        (Real.exp_log hpos).symm
    _ = 1 := by rw [hlog, Real.exp_zero]

/-! ## `G`, the one-parameter reduction

Additivity says the two-parameter family is a difference, so all of the content sits in the
single function `G(x, s) = g_{0,x}(s)`. Everything Chapter 6 does to the gauge, it does to `G`.
-/

/-- **`G(x, s) = g_{0,x}(s)`.** -/
noncomputable def G (Fam : CascadeCore) (x s : ℝ) : ℝ := Fam.exponent 0 x s

@[simp] theorem G_zero_left (Fam : CascadeCore) (s : ℝ) : Fam.G 0 s = 0 :=
  exponent_self le_rfl s

@[simp] theorem G_atZero (Fam : CascadeCore) (x : ℝ) : Fam.G x 0 = 0 := exponent_zero Fam 0 x

/-- **`g_{x,y} = G(y, \cdot) - G(x, \cdot)`.** -/
theorem exponent_eq_G_sub (hx : 0 ≤ x) (hxy : x ≤ y) {s : ℝ} (hs : 0 ≤ s) :
    Fam.exponent x y s = Fam.G y s - Fam.G x s := by
  have h := exponent_add (Fam := Fam) le_rfl hx hxy hs
  rw [G, G]
  linarith

/-- **`G(\cdot, s)` is nondecreasing.** This is the nonnegativity of the increments, which is
`exponent_nonneg`, read through the difference. -/
theorem G_monotoneOn (Fam : CascadeCore) {s : ℝ} (hs : 0 ≤ s) :
    MonotoneOn (fun x => Fam.G x s) (Ici 0) := by
  intro a ha b _ hab
  have hsub := exponent_eq_G_sub (Fam := Fam) ha hab hs
  have hnn := exponent_nonneg Fam a b hs
  simp only
  linarith

/-- **`G(\cdot, s)` is continuous on `[0,∞)`** — (A7) along the slice `x ↦ (0, x)`. -/
theorem continuousOn_G (Fam : CascadeCore) {s : ℝ} (hs : 0 ≤ s) :
    ContinuousOn (fun x => Fam.G x s) (Ici 0) := by
  have hmap : MapsTo (fun x : ℝ => ((0 : ℝ), x)) (Ici 0) Index := fun x hx => ⟨le_rfl, hx⟩
  exact (continuousOn_exponent Fam hs).comp (Continuous.continuousOn (by fun_prop)) hmap

/-- **`G(x, \cdot)` is continuous on `[0,∞)`**, with `G(x, \zp) = 0`. -/
theorem continuousOn_G_right (Fam : CascadeCore) (x : ℝ) :
    ContinuousOn (fun s => Fam.G x s) (Ici 0) := continuousOn_exponent_right Fam 0 x

/-- **`lem:additivity`.** The cascade law at the level of measures, its consequence for the
exponents, and the reduction to the one-parameter `G`. -/
theorem additivity (Fam : CascadeCore) :
    (∀ x y z : ℝ, 0 ≤ x → x ≤ y → y ≤ z → Fam.repr x z = Fam.repr x y ∗ Fam.repr y z) ∧
      (∀ x y z s : ℝ, 0 ≤ x → x ≤ y → y ≤ z → 0 ≤ s →
        Fam.exponent x z s = Fam.exponent x y s + Fam.exponent y z s) ∧
      (∀ x s : ℝ, 0 ≤ x → Fam.exponent x x s = 0) ∧
      (∀ x y s : ℝ, 0 ≤ x → x ≤ y → 0 ≤ s → Fam.exponent x y s = Fam.G y s - Fam.G x s) ∧
      (∀ s : ℝ, Fam.G 0 s = 0) ∧
      (∀ s : ℝ, 0 ≤ s → MonotoneOn (fun x => Fam.G x s) (Ici 0)) ∧
      (∀ s : ℝ, 0 ≤ s → ContinuousOn (fun x => Fam.G x s) (Ici 0)) ∧
      (∀ x : ℝ, Fam.G x 0 = 0) :=
  ⟨fun _ _ _ hx hxy hyz => repr_conv hx hxy hyz,
    fun _ _ _ _ hx hxy hyz hs => exponent_add hx hxy hyz hs,
    fun _ _ hx => exponent_self hx _,
    fun _ _ _ hx hxy hs => exponent_eq_G_sub hx hxy hs,
    G_zero_left Fam,
    fun _ hs => G_monotoneOn Fam hs,
    fun _ hs => continuousOn_G Fam hs,
    G_atZero Fam⟩

end CascadeCore

end Hemigroup
