/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the MIT license as described in the file LICENSES/MIT.txt.
Authors: Daniel Fagerström
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# The shifted Gamma recursion: Krull--Webster in the order-two case

Blueprint: the step of `thm:locality` carried by ledger **A15**.

`thm:locality`'s order-2 case reaches the functional equation

  `m(z+1) = c (z + a) m(z)`,  `m` log-convex on `(0,∞)`,  `m(0+) = 1`,

and concludes `m(z) = c^z Γ(a+z)/Γ(a)`. The blueprint cites the Krull--Webster uniqueness theorem
for this. That citation is correct and it is also more than the order-2 case needs: with a single
Gamma factor the statement is the **Bohr--Mollerup theorem**, which Mathlib carries as
`Real.eq_Gamma_of_log_convex`. This file discharges the step from it.

## The obstacle, and the shift that removes it

Bohr--Mollerup pins a function on `(0,∞)` satisfying `f(y+1) = y f(y)`. Ours has the shift `a`,
so the obvious substitution `f(y) := m(y - a) · …` needs `m` on `(-a, ∞)` -- below the interval it
is given on. Extending `m` downward through the recursion is possible but is a nested induction on
`⌈a⌉` and puts the object outside the domain where log-convexity was proved.

The shift the other way costs nothing. Pick `n : ℕ` with `a ≤ n` and set

  `f(y) := m(y + (n - a)) · c^(a - n - y) / P(y)`,   `P(y) := ∏_{j<n} (y + j)`.

Then `f` uses `m` only on `(n - a, ∞) ⊆ (0,∞)`, and the two shifts cancel exactly:
`m(y+1+(n-a)) = c(y+n) m(y+(n-a))` while `P(y+1) = P(y)(y+n)/y`, leaving `f(y+1) = y f(y)`. The
price is that `log P` must be shown concave, which it is termwise, `-log(y+j)` being convex for
`j ≥ 0` because `log` is concave.

## What is proved here, and what it costs

`eq_gamma_form_of_logConvex_of_recursion` is stated for an arbitrary real function, with no
reference to this development: it is the analytic content of A15 restricted to a linear `Q`, and
nothing in it knows about subordinators. `#print axioms` on it gives Lean core alone.

Two honest notes. First, this is **longer than the citation it replaces** -- unlike the five
substitutions of §2's vocabulary discussion, where the elementary route was also the shorter one.
The gain is the trust base, not the exposition. Second, it settles the order-2 case only:
`prop:local-ladder`'s order-`n` recursion has `n-1` Gamma factors, for which log-convexity alone
still needs the general Krull--Webster theorem, and A15 stays there.
-/

namespace Hemigroup

open Set Filter Real
open scoped Topology

/-! ## Convexity of the elementary pieces -/

/-- An affine function is convex on any convex set: the defining inequality is an equality. -/
theorem convexOn_affine_Ioi (α β : ℝ) :
    ConvexOn ℝ (Ioi (0 : ℝ)) (fun y => α * y + β) := by
  refine ⟨convex_Ioi 0, fun x _ y _ p q _ _ hpq => ?_⟩
  have hq' : q = 1 - p := by linarith
  subst hq'
  simp only [smul_eq_mul]
  have : α * (p * x + (1 - p) * y) + β
      = p * (α * x + β) + (1 - p) * (α * y + β) := by ring
  exact le_of_eq this

/-- `y ↦ -log (y + d)` is convex on `(0,∞)` for `d ≥ 0`: concavity of `log`, precomposed with a
translation that keeps the argument positive. -/
theorem convexOn_neg_log_add {d : ℝ} (hd : 0 ≤ d) :
    ConvexOn ℝ (Ioi (0 : ℝ)) (fun y => -Real.log (y + d)) := by
  refine ⟨convex_Ioi 0, fun x hx y hy p q hp hq hpq => ?_⟩
  have hx0 : (0 : ℝ) < x := hx
  have hy0 : (0 : ℝ) < y := hy
  have hx' : (0 : ℝ) < x + d := by linarith
  have hy' : (0 : ℝ) < y + d := by linarith
  have hcc := strictConcaveOn_log_Ioi.concaveOn.2 (mem_Ioi.mpr hx') (mem_Ioi.mpr hy') hp hq hpq
  simp only [smul_eq_mul] at hcc ⊢
  have harg : p * x + q * y + d = p * (x + d) + q * (y + d) := by
    have hq' : q = 1 - p := by linarith
    subst hq'; ring
  rw [harg]
  linarith

/-- The falling-factorial product `P(y) = ∏_{j<n} (y + j)` that converts the shifted recursion
into Bohr--Mollerup's. -/
noncomputable def shiftProd (n : ℕ) (y : ℝ) : ℝ := ∏ j ∈ Finset.range n, (y + (j : ℝ))

theorem shiftProd_zero (y : ℝ) : shiftProd 0 y = 1 := by simp [shiftProd]

theorem shiftProd_succ (n : ℕ) (y : ℝ) :
    shiftProd (n + 1) y = shiftProd n y * (y + (n : ℝ)) := by
  simp [shiftProd, Finset.prod_range_succ]

theorem shiftProd_pos {n : ℕ} {y : ℝ} (hy : 0 < y) : 0 < shiftProd n y := by
  refine Finset.prod_pos fun j _ => ?_
  have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  linarith

/-- The step identity `P(y+1) · y = P(y) · (y + n)`, which is where the two shifts cancel. -/
theorem shiftProd_add_one (n : ℕ) (y : ℝ) :
    shiftProd n (y + 1) * y = shiftProd n y * (y + (n : ℝ)) := by
  induction n with
  | zero => simp [shiftProd_zero]
  | succ k ih =>
      rw [shiftProd_succ, shiftProd_succ]
      push_cast
      linear_combination (y + 1 + (k : ℝ)) * ih

/-- `Γ(y + n) = P(y) · Γ(y)`: the product is exactly the Gamma shift by an integer. -/
theorem gamma_add_nat (n : ℕ) {y : ℝ} (hy : 0 < y) :
    Real.Gamma (y + (n : ℝ)) = shiftProd n y * Real.Gamma y := by
  induction n with
  | zero => simp [shiftProd_zero]
  | succ k ih =>
      have hpos : (0 : ℝ) < y + (k : ℝ) := by
        have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        linarith
      have hstep : Real.Gamma (y + ((k : ℝ) + 1)) = (y + (k : ℝ)) * Real.Gamma (y + (k : ℝ)) := by
        rw [← add_assoc, Real.Gamma_add_one hpos.ne']
      push_cast
      rw [hstep, ih, shiftProd_succ]
      ring

/-- A finite sum of the convex pieces above is convex. -/
theorem convexOn_sum_neg_log (n : ℕ) :
    ConvexOn ℝ (Ioi (0 : ℝ)) (fun y => ∑ j ∈ Finset.range n, -Real.log (y + (j : ℝ))) := by
  induction n with
  | zero => simpa using convexOn_const (0 : ℝ) (convex_Ioi (0 : ℝ))
  | succ k ih =>
      have h := ih.add (convexOn_neg_log_add (d := (k : ℝ)) (Nat.cast_nonneg k))
      exact h.congr fun y _ => by simp [Pi.add_apply, Finset.sum_range_succ, add_comm]

/-- `log ∘ P` is concave on `(0,∞)`; stated as convexity of its negative, which is the shape the
Bohr--Mollerup hypothesis needs. -/
theorem convexOn_neg_log_shiftProd (n : ℕ) :
    ConvexOn ℝ (Ioi (0 : ℝ)) (fun y => -Real.log (shiftProd n y)) := by
  refine (convexOn_sum_neg_log n).congr fun y hy => ?_
  have hy0 : (0 : ℝ) < y := hy
  have hne : ∀ j ∈ Finset.range n, y + (j : ℝ) ≠ 0 := by
    intro j _
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    exact (by linarith : (0 : ℝ) < y + (j : ℝ)).ne'
  rw [shiftProd, Real.log_prod hne]
  simp

/-- Precomposing a convex function with a translation that keeps the argument positive. -/
theorem convexOn_comp_add_const {g : ℝ → ℝ} {d : ℝ} (hd : 0 ≤ d)
    (hg : ConvexOn ℝ (Ioi (0 : ℝ)) g) :
    ConvexOn ℝ (Ioi (0 : ℝ)) (fun y => g (y + d)) := by
  refine ⟨convex_Ioi 0, fun x hx y hy p q hp hq hpq => ?_⟩
  have hx0 : (0 : ℝ) < x := hx
  have hy0 : (0 : ℝ) < y := hy
  have hx' : (0 : ℝ) < x + d := by linarith
  have hy' : (0 : ℝ) < y + d := by linarith
  have h := hg.2 (mem_Ioi.mpr hx') (mem_Ioi.mpr hy') hp hq hpq
  simp only [smul_eq_mul] at h ⊢
  have harg : p * x + q * y + d = p * (x + d) + q * (y + d) := by
    have hq' : q = 1 - p := by linarith
    subst hq'; ring
  rw [harg]
  linarith

/-! ## The theorem

The order-2 case of Krull--Webster, from Bohr--Mollerup. -/

/-- **A log-convex solution of `m(z+1) = c(z+a)m(z)` normalised at the origin is the Gamma form.**

This is the step of `thm:locality` that the blueprint takes from Krull--Webster, in the only case
that theorem is applied to there: `Q` linear, hence a single Gamma factor, hence Bohr--Mollerup.
Nothing in the statement mentions this development. -/
theorem eq_gamma_form_of_logConvex_of_recursion
    {m : ℝ → ℝ} {c a : ℝ} (hc : 0 < c) (ha : 0 < a)
    (hpos : ∀ ⦃z : ℝ⦄, 0 < z → 0 < m z)
    (hconv : ConvexOn ℝ (Ioi (0 : ℝ)) (fun z => Real.log (m z)))
    (hrec : ∀ ⦃z : ℝ⦄, 0 < z → m (z + 1) = c * (z + a) * m z)
    (hlim : Tendsto m (𝓝[>] (0 : ℝ)) (𝓝 1)) :
    ∀ ⦃z : ℝ⦄, 0 < z → m z = c ^ z * Real.Gamma (a + z) / Real.Gamma a := by
  -- `G` is the claimed closed form up to the constant, and satisfies the same recursion
  set G : ℝ → ℝ := fun z => c ^ z * Real.Gamma (z + a) with hGdef
  have hGpos : ∀ ⦃z : ℝ⦄, 0 < z → 0 < G z := fun z hz =>
    mul_pos (Real.rpow_pos_of_pos hc z) (Real.Gamma_pos_of_pos (by linarith))
  have hGrec : ∀ ⦃z : ℝ⦄, 0 < z → G (z + 1) = c * (z + a) * G z := by
    intro z hz
    have hza : (0 : ℝ) < z + a := by linarith
    have : Real.Gamma (z + 1 + a) = (z + a) * Real.Gamma (z + a) := by
      rw [show z + 1 + a = (z + a) + 1 by ring, Real.Gamma_add_one hza.ne']
    simp only [hGdef]
    rw [this, Real.rpow_add hc, Real.rpow_one]
    ring
  -- an integer `n` at least `a`, and the shift `d = n - a ≥ 0`
  obtain ⟨n, hn⟩ : ∃ n : ℕ, a ≤ (n : ℝ) := ⟨⌈a⌉₊, Nat.le_ceil a⟩
  set d : ℝ := (n : ℝ) - a with hddef
  have hd : 0 ≤ d := by rw [hddef]; linarith
  have hda : d + a = (n : ℝ) := by rw [hddef]; ring
  -- the Bohr--Mollerup surrogate
  set f : ℝ → ℝ := fun y => m (y + d) * c ^ (-(y + d)) / shiftProd n y with hfdef
  have hfpos : ∀ ⦃y : ℝ⦄, 0 < y → 0 < f y := by
    intro y hy
    exact div_pos (mul_pos (hpos (by linarith)) (Real.rpow_pos_of_pos hc _))
      (shiftProd_pos hy)
  have hfrec : ∀ ⦃y : ℝ⦄, 0 < y → f (y + 1) = y * f y := by
    intro y hy
    have hyd : (0 : ℝ) < y + d := by linarith
    have hP : (0 : ℝ) < shiftProd n y := shiftProd_pos hy
    have hP1 : (0 : ℝ) < shiftProd n (y + 1) := shiftProd_pos (by linarith)
    have hstep : m (y + 1 + d) = c * (y + (n : ℝ)) * m (y + d) := by
      have := hrec hyd
      rw [show y + d + 1 = y + 1 + d by ring, show y + d + a = y + (n : ℝ) by
        rw [← hda]; ring] at this
      exact this
    have hpow : c ^ (-(y + 1 + d)) = c ^ (-(y + d)) * c⁻¹ := by
      rw [show -(y + 1 + d) = -(y + d) + (-1 : ℝ) by ring, Real.rpow_add hc,
        Real.rpow_neg_one]
    have hprod := shiftProd_add_one n y
    simp only [hfdef]
    rw [hstep, hpow]
    field_simp
    linear_combination (-m (y + d)) * hprod
  have hfconv : ConvexOn ℝ (Ioi (0 : ℝ)) (fun y => Real.log (f y)) := by
    have h₁ : ConvexOn ℝ (Ioi (0 : ℝ)) (fun y => Real.log (m (y + d))) :=
      convexOn_comp_add_const hd hconv
    have h₂ := convexOn_affine_Ioi (-(Real.log c)) (-d * Real.log c)
    have h₃ := convexOn_neg_log_shiftProd n
    refine ((h₁.add h₂).add h₃).congr fun y hy => ?_
    have hy0 : (0 : ℝ) < y := hy
    have hm : (0 : ℝ) < m (y + d) := hpos (by linarith)
    have hP : (0 : ℝ) < shiftProd n y := shiftProd_pos hy0
    have hpw : (0 : ℝ) < c ^ (-(y + d)) := Real.rpow_pos_of_pos hc _
    simp only [Pi.add_apply, hfdef]
    rw [Real.log_div (by positivity) hP.ne', Real.log_mul hm.ne' hpw.ne',
      Real.log_rpow hc]
    ring
  -- Bohr--Mollerup, applied to `f` normalised at `1`
  set C : ℝ := f 1 with hCdef
  have hC : 0 < C := hfpos one_pos
  have hBM : ∀ ⦃y : ℝ⦄, 0 < y → f y = C * Real.Gamma y := by
    have hkey : EqOn (fun y => f y / C) Real.Gamma (Ioi (0 : ℝ)) := by
      refine Real.eq_Gamma_of_log_convex ?_ ?_ ?_ ?_
      · refine (hfconv.add_const (-Real.log C)).congr fun y hy => ?_
        have hy0 : (0 : ℝ) < y := hy
        simp only [Function.comp_apply, Pi.add_apply]
        rw [Real.log_div (hfpos hy0).ne' hC.ne']
        ring
      · intro y hy
        rw [hfrec hy]
        field_simp
      · intro y hy
        exact div_pos (hfpos hy) hC
      · rw [← hCdef]
        exact div_self hC.ne'
    intro y hy
    have := hkey (mem_Ioi.mpr hy)
    field_simp at this
    linarith [this]
  -- the closed form above `d`, from the definition of `f`
  have hlarge : ∀ ⦃z : ℝ⦄, d < z → m z = C * G z := by
    intro z hz
    have hy : (0 : ℝ) < z - d := by linarith
    have hP : (0 : ℝ) < shiftProd n (z - d) := shiftProd_pos hy
    have hfz := hBM hy
    have hzd : z - d + d = z := by ring
    simp only [hfdef, hzd] at hfz
    have hpw : (0 : ℝ) < c ^ (-z) := Real.rpow_pos_of_pos hc _
    have hmz : m z = C * Real.Gamma (z - d) * shiftProd n (z - d) * c ^ z := by
      have h1 : m z * c ^ (-z) = C * Real.Gamma (z - d) * shiftProd n (z - d) := by
        field_simp at hfz
        linear_combination hfz
      have h2 : c ^ (-z) * c ^ z = 1 := by
        rw [← Real.rpow_add hc]; simp
      calc m z = m z * c ^ (-z) * c ^ z := by
            rw [mul_assoc, h2, mul_one]
        _ = C * Real.Gamma (z - d) * shiftProd n (z - d) * c ^ z := by rw [h1]
    have hgam : shiftProd n (z - d) * Real.Gamma (z - d) = Real.Gamma (z + a) := by
      rw [← gamma_add_nat n hy, show z - d + (n : ℝ) = z + a by rw [← hda]; ring]
    rw [hmz]
    simp only [hGdef]
    linear_combination (C * c ^ z) * hgam
  -- both `m` and `G` satisfy the recursion, so the ratio is one-periodic
  have hshift : ∀ (k : ℕ) ⦃z : ℝ⦄, 0 < z → m (z + k) * G z = m z * G (z + k) := by
    intro k
    induction k with
    | zero => intro z _; simp
    | succ j ih =>
        intro z hz
        have hzj : (0 : ℝ) < z + (j : ℝ) := by
          have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
          linarith
        have hm1 := hrec hzj
        have hg1 := hGrec hzj
        have hcast : z + ((j : ℝ) + 1) = z + (j : ℝ) + 1 := by ring
        push_cast
        rw [hcast, hm1, hg1]
        have hih := ih hz
        linear_combination (c * (z + (j : ℝ) + a)) * hih
  have hall : ∀ ⦃z : ℝ⦄, 0 < z → m z = C * G z := by
    intro z hz
    obtain ⟨k, hk⟩ : ∃ k : ℕ, d < z + (k : ℝ) := by
      obtain ⟨k, hk⟩ := exists_nat_gt (d - z)
      exact ⟨k, by linarith⟩
    have hzk : (0 : ℝ) < z + (k : ℝ) := by
      have : (0 : ℝ) ≤ d := hd
      linarith
    have h1 := hshift k hz
    have h2 := hlarge hk
    rw [h2] at h1
    have hGk : 0 < G (z + (k : ℝ)) := hGpos hzk
    have h3 : (C * G z) * G (z + (k : ℝ)) = m z * G (z + (k : ℝ)) := by linear_combination h1
    exact (mul_right_cancel₀ hGk.ne' h3).symm
  -- and the normalisation at the origin pins `C`
  have hGcont : Tendsto G (𝓝[>] (0 : ℝ)) (𝓝 (Real.Gamma a)) := by
    have hΓ : ContinuousAt Real.Gamma a :=
      (Real.differentiableAt_Gamma (fun k => by
        have : -(k : ℝ) ≤ 0 := neg_nonpos.mpr (Nat.cast_nonneg k)
        intro h; rw [h] at ha; linarith)).continuousAt
    have h1 : Tendsto (fun z : ℝ => c ^ z) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      have hcont : Continuous fun z : ℝ => Real.exp (Real.log c * z) := by fun_prop
      have h := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Ioi 0))
      simpa [Real.rpow_def_of_pos hc] using h
    have h2 : Tendsto (fun z : ℝ => Real.Gamma (z + a)) (𝓝[>] (0 : ℝ))
        (𝓝 (Real.Gamma a)) := by
      have hadd : Tendsto (fun z : ℝ => z + a) (𝓝[>] (0 : ℝ)) (𝓝 a) := by
        have hcont : Continuous fun z : ℝ => z + a := by fun_prop
        have h := (hcont.tendsto (0 : ℝ)).mono_left
          (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Ioi 0))
        simpa using h
      exact hΓ.tendsto.comp hadd
    simpa [hGdef] using h1.mul h2
  have hCval : C * Real.Gamma a = 1 := by
    have hlim' : Tendsto m (𝓝[>] (0 : ℝ)) (𝓝 (C * Real.Gamma a)) := by
      refine Tendsto.congr' ?_ (hGcont.const_mul C)
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact (hall hz).symm
    exact tendsto_nhds_unique hlim' hlim
  intro z hz
  have hΓa : (0 : ℝ) < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have hCeq : C = 1 / Real.Gamma a := by rw [eq_div_iff hΓa.ne']; exact hCval
  rw [hall hz]
  simp only [hGdef]
  rw [hCeq, show a + z = z + a by ring]
  ring

end Hemigroup
