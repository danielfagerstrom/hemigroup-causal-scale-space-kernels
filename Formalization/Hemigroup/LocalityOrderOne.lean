/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the MIT license as described in the file LICENSES/MIT.txt.
Authors: Daniel Fagerström
-/
import Hemigroup.LocalityOrderTwo

/-!
# The order-one case of `thm:locality`: the moments are a pure power

Blueprint: the order-1 branch of `thm:locality`'s (⇒) direction (12.5) --- the degenerate member,
`B(θ) = -c'θ`, where the kernels are the deterministic delays `μ_{0,x} = δ_{x/c'}` and the
signaling problem is the transport equation.

## What the branch needs, and what it does not

At order one `Q` is the *constant* `-γ₁`, so the recursion reads `m(z+1) = c'·m(z)` with `c' > 0`,
and the blueprint's argument is one line: `log m` is convex with constant unit increments, hence
affine, so `m(z) = c'^z`. The order-two branch's citation of `lem:gamma-recursion-uniqueness`
--- Bohr--Mollerup --- is not used here and never was: the entry the article records against this
branch is precisely that it needs none.

**What it does need is a fact about convexity that Mathlib does not carry**: a convex function on
`(0,∞)` with period one is constant. That is `eq_of_convexOn_of_periodic` below, and the proof is
elementary in a way worth recording, because the obvious route is not.

## The obvious route, and the shorter one

The usual argument is: a periodic function is bounded, a convex function bounded above on
`(0,∞)` is nonincreasing, and nonincreasing plus periodic is constant. Boundedness there comes
from continuity of a convex function on an open interval, which is a real theorem.

None of that is needed. Convexity on the three points `x < y < y+1`, with `y` written as the
combination `λx + (1-λ)(y+1)` at `λ = 1/(y+1-x)`, gives

  `g(y) ≤ λ g(x) + (1-λ) g(y+1) = λ g(x) + (1-λ) g(y)`

by periodicity alone, and cancelling leaves `g(y) ≤ g(x)`. So the function is antitone with no
limit taken and no continuity used; periodicity then closes it, since `g(x) = g(x+n) ≤ g(y)` for
`n` large. Three points and one inequality.

The limit enters only once and at the end, to fix the constant: `g(z) → 0` as `z ↓ 0`, because
`m(z) → 1` is `tendsto_negMoment_nhdsGT_zero`.
-/

namespace Hemigroup

open MeasureTheory Set Filter

open scoped ENNReal Topology

/-! ## A convex function of period one is constant -/

/-- A linear function is convex --- with equality, which is why this is a one-liner and why the
statement below can subtract one without meeting a sign condition. -/
theorem convexOn_const_mul_id (s : Set ℝ) (hs : Convex ℝ s) (k : ℝ) :
    ConvexOn ℝ s (fun z : ℝ => k * z) :=
  ⟨hs, fun _ _ _ _ _ _ _ _ _ => le_of_eq (by simp only [smul_eq_mul]; ring)⟩

/-- **A convex function on `(0,∞)` of period one is antitone**, by one convexity inequality on
`x < y < y+1` and nothing else. No continuity, no boundedness, no limit. -/
theorem antitone_of_convexOn_of_periodic {g : ℝ → ℝ} (hconv : ConvexOn ℝ (Ioi (0 : ℝ)) g)
    (hper : ∀ x : ℝ, 0 < x → g (x + 1) = g x) {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    g y ≤ g x := by
  have hy : 0 < y := lt_trans hx hxy
  have hd : (0 : ℝ) < y + 1 - x := by linarith
  set l : ℝ := 1 / (y + 1 - x) with hldef
  have hl0 : 0 < l := by rw [hldef]; positivity
  have hl1 : l ≤ 1 := by rw [hldef, div_le_one hd]; linarith
  have hpt : l * x + (1 - l) * (y + 1) = y := by
    rw [hldef]
    field_simp
    ring
  have hcomb := hconv.2 (mem_Ioi.mpr hx) (mem_Ioi.mpr (show (0 : ℝ) < y + 1 by linarith))
    hl0.le (by linarith : (0 : ℝ) ≤ 1 - l) (by ring)
  simp only [smul_eq_mul, hpt] at hcomb
  rw [hper y hy] at hcomb
  nlinarith [hcomb, hl0]

/-- Period one iterated: `g(x + n) = g(x)`. -/
theorem eq_add_natCast_of_periodic {g : ℝ → ℝ} (hper : ∀ x : ℝ, 0 < x → g (x + 1) = g x)
    {x : ℝ} (hx : 0 < x) : ∀ n : ℕ, g (x + n) = g x := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
      have hxk : (0 : ℝ) < x + k := by have := Nat.cast_nonneg (α := ℝ) k; linarith
      rw [show x + ((k + 1 : ℕ) : ℝ) = (x + k) + 1 from by push_cast; ring, hper _ hxk, ih]

/-- **A convex function on `(0,∞)` of period one is constant.** -/
theorem eq_of_convexOn_of_periodic {g : ℝ → ℝ} (hconv : ConvexOn ℝ (Ioi (0 : ℝ)) g)
    (hper : ∀ x : ℝ, 0 < x → g (x + 1) = g x) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    g x = g y := by
  -- it is enough to do it for `x < y`, the statement being symmetric
  have key : ∀ u v : ℝ, 0 < u → u < v → g u = g v := by
    intro u v hu huv
    have hle : g v ≤ g u := antitone_of_convexOn_of_periodic hconv hper hu huv
    obtain ⟨n, hn⟩ := exists_nat_ge (v - u)
    have hun : v ≤ u + n := by linarith
    have hge : g (u + n) ≤ g v := by
      rcases eq_or_lt_of_le hun with heq | hlt
      · exact le_of_eq (by rw [heq])
      · exact antitone_of_convexOn_of_periodic hconv hper (lt_trans hu (by linarith)) hlt
    rw [eq_add_natCast_of_periodic hper hu n] at hge
    exact le_antisymm hge hle
  rcases lt_trichotomy x y with h | h | h
  · exact key x y hx h
  · rw [h]
  · exact (key y x hy h).symm

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent)

/-- At order one the quotient is the constant `-γ₁`. -/
theorem symbolQuotient_one (γ : ℕ → ℂ) (z : ℂ) : symbolQuotient γ 1 z = -γ 1 := by
  rw [symbolQuotient, Finset.sum_range_one, mellinEulerFactor_zero]
  ring

/-- **`thm:locality`(⇒), the order-one branch.** A local operator of order `1` forces
`m(z) = c'^z` on `(0,∞)` with `c' > 0` --- so `T₁ = 1/c'` almost surely, and `A = -c'∂ₓ`.

As at order two, both citations of that direction are hypotheses: `hA13` is
`lem:moment-recursion`(2) and the order `1` is Courrège's bound. Unlike order two this branch
uses no Krull--Webster and no Bohr--Mollerup: the recursion has a constant multiplier, and a
convex function with constant unit increments is affine. -/
theorem exists_pow_form_of_isLocalOfOrder_one (hH : F.StandingHypothesis)
    (hA13 : F.AllNegMomentsFinite) {c : ℝ} (hc : 0 < c) (hL : F.IsLocalOfOrder c 1) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ z : ℝ, 0 < z → (F.negMoment z).toReal = c' ^ z := by
  have h0 := F.lawT₁_singleton_zero hH.1
  have hc' : ENNReal.ofReal c < F.zStar - 1 := F.ofReal_lt_zStar_sub_one_of_all hA13 c
  set γ : ℕ → ℂ := fun j => hL.coeff j 1 with hγdef
  have hsymbol : ∀ z : ℂ, 0 < z.re → ENNReal.ofReal z.re < F.zStar - 1 →
      mellin (fun s => (F.profile s : ℂ)) z ≠ 0 →
      F.inversionSymbol z = ∑ j ∈ Finset.range (1 + 1), γ j * mellinEulerFactor j z :=
    fun z hz hz' hne =>
      (F.sameSymbolAction_of_isLocalOfOrder hH hc hc' hL).eqOn_of_ne_zero ⟨⟨hz, hz'⟩, hne⟩
  have hrec : ∀ z : ℝ, 0 < z → ∃ q : ℝ, 0 < q ∧ symbolQuotient γ 1 (z : ℂ) = (q : ℂ) ∧
      (F.negMoment (z + 1)).toReal = q * (F.negMoment z).toReal :=
    fun z hz => F.exists_pos_symbolQuotient_of_symbol_eq hH γ hsymbol hz
      (F.ofReal_lt_zStar_sub_one_of_all hA13 z)
  -- the multiplier is one and the same constant at every point
  obtain ⟨c', hc'pos, hc'eq, -⟩ := hrec 1 one_pos
  have hqconst : ∀ z : ℝ, 0 < z → (F.negMoment (z + 1)).toReal = c' * (F.negMoment z).toReal := by
    intro z hz
    obtain ⟨q, -, hqz, hqrec⟩ := hrec z hz
    rw [symbolQuotient_one] at hqz hc'eq
    have : ((q : ℝ) : ℂ) = ((c' : ℝ) : ℂ) := by rw [← hqz, hc'eq]
    rw [hqrec, (by exact_mod_cast this : q = c')]
  -- the convex function with unit period
  have hmpos : ∀ z : ℝ, 0 < z → 0 < (F.negMoment z).toReal := fun z hz =>
    F.negMoment_toReal_pos hH hz (F.ofReal_lt_zStar_of_all hA13 z)
  set g : ℝ → ℝ := fun z => Real.log (F.negMoment z).toReal - Real.log c' * z with hgdef
  have hconv : ConvexOn ℝ (Ioi (0 : ℝ)) g := by
    have hlog : ConvexOn ℝ (Ioi (0 : ℝ)) (fun z => Real.log (F.negMoment z).toReal) := by
      have := F.convexOn_log_negMoment h0
      rwa [F.momentInterval_eq_Ioi hA13] at this
    have hsub : ConcaveOn ℝ (Ioi (0 : ℝ)) (fun z : ℝ => Real.log c' * z) :=
      ⟨convex_Ioi 0, fun _ _ _ _ _ _ _ _ _ => le_of_eq (by simp only [smul_eq_mul]; ring)⟩
    exact hlog.sub hsub
  have hper : ∀ x : ℝ, 0 < x → g (x + 1) = g x := by
    intro x hx
    rw [hgdef]
    simp only
    rw [hqconst x hx, Real.log_mul (ne_of_gt hc'pos) (ne_of_gt (hmpos x hx))]
    ring
  -- so `g` is constant, and the constant is `0` because `m(z) → 1`
  have hg0 : g 1 = 0 := by
    have hlim : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 (g 1)) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact eq_of_convexOn_of_periodic hconv hper one_pos hz
    have hlim0 : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hlog : Tendsto (fun z : ℝ => Real.log (F.negMoment z).toReal) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have := (Real.continuousAt_log one_ne_zero).tendsto.comp
          (F.tendsto_negMoment_nhdsGT_zero hH)
        simpa [Function.comp_def] using this
      have hlin : Tendsto (fun z : ℝ => Real.log c' * z) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have : Tendsto (fun z : ℝ => Real.log c' * z) (𝓝[>] (0 : ℝ))
            (𝓝 (Real.log c' * 0)) :=
          Tendsto.const_mul _ (tendsto_id.mono_left nhdsWithin_le_nhds)
        simpa using this
      simpa [hgdef] using hlog.sub hlin
    exact tendsto_nhds_unique hlim hlim0
  refine ⟨c', hc'pos, fun z hz => ?_⟩
  have hgz : Real.log (F.negMoment z).toReal - Real.log c' * z = 0 := by
    have := eq_of_convexOn_of_periodic hconv hper one_pos hz
    rw [hg0] at this
    exact this.symm
  have : Real.log (F.negMoment z).toReal = Real.log c' * z := by linarith
  rw [Real.rpow_def_of_pos hc'pos, ← this, Real.exp_log (hmpos z hz)]

end SelfDecomposableExponent

end Hemigroup
