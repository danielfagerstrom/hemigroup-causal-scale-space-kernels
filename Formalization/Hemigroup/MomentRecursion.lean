/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the MIT license as described in the file LICENSES/MIT.txt.
Authors: Daniel Fagerström
-/
import Hemigroup.Locality
import Hemigroup.ProfileEuler

/-!
# The symbol's linear factor, and the moment recursion

Blueprint: the `[T]` clauses of `lem:moment-recursion` (12.3) --- the factorisation half of its
clause (1), and its clause (3) --- split off as `lem:moment-recursion-quotient` so that a node
spending ledger **A13** on clause (2) does not appear to spend it on these.

## What is here, and what is not

Clause (1) is two statements. `B(0) = 0` is `lem:symbol-vanishes-at-origin`, proved already and
without the polynomial hypothesis, which is inert in it. What is left is the consequence: a
polynomial symbol vanishing at the origin has a factor `z`, so `B(-z) = z·Q(z)`. That is
`sum_mellinEulerFactor_eq_mul_symbolQuotient` here, and the factorisation is exact rather than
approximate --- `E_{j+1}(z) = -z·E_j(z+1)` is the Euler factors' own recursion
(`mellinEulerFactor_succ`), so `Q` comes out in the same basis one degree lower.

Clause (3) is the recursion `m(z+1) = Q(z)·m(z)` with `Q > 0`, and it is `lem:mellin-data` read at
a *real* point of the strip: `B(-z) = z·m(z+1)/m(z)` there, `H̃` does not vanish at real points
(`mellin_profile_ofReal_ne_zero`), so the symbol identity holds pointwise and the `z` cancels.
Positivity is then inherited rather than argued: `Q(z)` is a ratio of two positive real moments.

**The range is `0 < z < z_* - 1`, not `(0,∞)`.** The blueprint states clause (3) on the whole
half-line, and that is clause (2) --- `z_* = ∞` --- being used, which is the one thing in the node
that ledger A13 carries. Stating the range that A13 is not needed for is what keeps the split
honest; on the locality hypothesis, once A13 is spent, the two ranges coincide.

## Why `Polynomial ℂ` does not appear

The blueprint says `Q` is a polynomial *of degree `n-1`*, and the degree is not stated here as
`Polynomial.degree`. The development has no polynomial vocabulary at all --- `mellinEulerFactor`
is a plain function --- and introducing it for one adjective would propagate. What is stated
instead is the expansion `Q(z) = -∑_{k<n} γ_{k+1} E_k(z+1)`, which *is* the degree claim in the
falling-factorial basis, that basis being triangular; and `symbolQuotient_two` makes it literal at
the order the chapter consumes, where `Q` is linear with leading coefficient `γ_2 ≠ 0` and
`lem:gamma-recursion-uniqueness` takes it from there.
-/

namespace Hemigroup

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## The Euler factors at the origin, and the factorisation -/

/-- Every Euler factor beyond the zeroth vanishes at the origin: its `i = 0` factor is `-z` and
`z = 0`. This is why `B(0) = 0` says exactly that the constant coefficient vanishes. -/
theorem mellinEulerFactor_zero_eq_zero {j : ℕ} (hj : j ≠ 0) : mellinEulerFactor j 0 = 0 := by
  rw [mellinEulerFactor]
  exact Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.pos_of_ne_zero hj)) (by simp)

/-- A polynomial symbol at the origin is its constant coefficient. -/
theorem sum_mellinEulerFactor_zero (γ : ℕ → ℂ) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), γ j * mellinEulerFactor j 0 = γ 0 := by
  rw [Finset.sum_eq_single 0 (fun b _ hb => by rw [mellinEulerFactor_zero_eq_zero hb, mul_zero])
    fun hmem => absurd (Finset.mem_range.mpr (Nat.succ_pos n)) hmem]
  simp

/-- **`Q`**, the symbol with its factor of `z` removed: `B(-z) = z·Q(z)`.

Written in the Euler basis one degree lower, which is what the factorisation delivers and what
every consumer wants: `E_{j+1}(z) = -z·E_j(z+1)`, so removing the factor shifts the argument by
one and drops the index by one. -/
noncomputable def symbolQuotient (γ : ℕ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  -∑ k ∈ Finset.range n, γ (k + 1) * mellinEulerFactor k (z + 1)

/-- **`lem:moment-recursion`(1), the factorisation.** A polynomial symbol with vanishing constant
coefficient is `z` times a polynomial one degree lower.

Exact, and with no analysis in it: the Euler factors' own recursion does the whole of it. -/
theorem sum_mellinEulerFactor_eq_mul_symbolQuotient {γ : ℕ → ℂ} (h0 : γ 0 = 0) (n : ℕ) (z : ℂ) :
    ∑ j ∈ Finset.range (n + 1), γ j * mellinEulerFactor j z = z * symbolQuotient γ n z := by
  have key : ∀ k ∈ Finset.range n, γ (k + 1) * mellinEulerFactor (k + 1) z
      = -(z * (γ (k + 1) * mellinEulerFactor k (z + 1))) := by
    intro k _
    rw [mellinEulerFactor_succ]
    ring
  calc ∑ j ∈ Finset.range (n + 1), γ j * mellinEulerFactor j z
      = ∑ k ∈ Finset.range n, γ (k + 1) * mellinEulerFactor (k + 1) z := by
        rw [Finset.sum_range_succ', h0, zero_mul, add_zero]
    _ = ∑ k ∈ Finset.range n, -(z * (γ (k + 1) * mellinEulerFactor k (z + 1))) :=
        Finset.sum_congr rfl key
    _ = -∑ k ∈ Finset.range n, z * (γ (k + 1) * mellinEulerFactor k (z + 1)) := by simp
    _ = z * symbolQuotient γ n z := by
        rw [symbolQuotient, ← Finset.mul_sum, mul_neg]

/-- At order two --- the order `thm:locality` leaves after the maximum principle --- `Q` is
literally linear, with leading coefficient `γ_2`. This is the form
`lem:gamma-recursion-uniqueness` consumes. -/
theorem symbolQuotient_two (γ : ℕ → ℂ) (z : ℂ) :
    symbolQuotient γ 2 z = γ 2 * z + (γ 2 - γ 1) := by
  rw [symbolQuotient, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    mellinEulerFactor_zero, mellinEulerFactor_succ, mellinEulerFactor_zero]
  ring

/-- The polynomial symbol is continuous, which is what turns `lem:symbol-vanishes-at-origin`'s
limit into a value at the origin. -/
theorem continuous_sum_mellinEulerFactor (γ : ℕ → ℂ) (n : ℕ) :
    Continuous fun z : ℂ => ∑ j ∈ Finset.range (n + 1), γ j * mellinEulerFactor j z := by
  refine continuous_finsetSum _ fun j _ => continuous_const.mul ?_
  show Continuous fun z : ℂ => ∏ i ∈ Finset.range j, (-z - (i : ℂ))
  exact continuous_finsetProd _ fun i _ => by fun_prop

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent)

/-! ## `B(0) = 0`, read off the polynomial -/

/-- **`lem:moment-recursion`(1), the vanishing.** A symbol that is the polynomial `∑ γ_j E_j` on
the strip has `γ_0 = 0`.

`lem:symbol-vanishes-at-origin` supplies the limit `B(-c) → 0` as `c ↓ 0` and says nothing about
`B`'s form; the polynomial hypothesis enters exactly here, and only to make the limit a value.
The symbol identity is available at the real points of the strip because `H̃` does not vanish
there --- which is the one place the side condition it carries is discharged rather than assumed
away. -/
theorem coeff_zero_eq_zero_of_symbol_eq (hH : F.StandingHypothesis) {n : ℕ} (γ : ℕ → ℂ)
    (hsymbol : ∀ z : ℂ, 0 < z.re → ENNReal.ofReal z.re < F.zStar - 1 →
      mellin (fun s => (F.profile s : ℂ)) z ≠ 0 →
      F.inversionSymbol z = ∑ j ∈ Finset.range (n + 1), γ j * mellinEulerFactor j z) :
    γ 0 = 0 := by
  obtain ⟨ζ, hζ1, hζtop⟩ := F.exists_one_lt_negMoment_ne_top hH
  -- the polynomial's own limit at the origin
  have hP : Tendsto (fun c : ℝ => ∑ j ∈ Finset.range (n + 1), γ j * mellinEulerFactor j (c : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (γ 0)) := by
    have hcomp : Continuous fun c : ℝ =>
        ∑ j ∈ Finset.range (n + 1), γ j * mellinEulerFactor j (c : ℂ) :=
      (continuous_sum_mellinEulerFactor γ n).comp Complex.continuous_ofReal
    have hlim : Tendsto (fun c : ℝ => ∑ j ∈ Finset.range (n + 1), γ j * mellinEulerFactor j (c : ℂ))
        (𝓝[>] (0 : ℝ))
        (𝓝 (∑ j ∈ Finset.range (n + 1), γ j * mellinEulerFactor j (((0 : ℝ) : ℂ)))) :=
      (hcomp.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    simpa [sum_mellinEulerFactor_zero] using hlim
  -- and the symbol's, which is `lem:symbol-vanishes-at-origin`
  have hsmall : ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ), ENNReal.ofReal c < F.zStar - 1 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (gt_mem_nhds (by linarith : (0 : ℝ) < ζ - 1))] with c hc hcζ
    exact (ofReal_lt_sub_one_iff (le_of_lt hc)).mpr
      (F.ofReal_lt_zStar_of_lt (by linarith [mem_Ioi.mp hc]) (by linarith) hζtop)
  have heq : ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ), F.inversionSymbol (c : ℂ)
      = ∑ j ∈ Finset.range (n + 1), γ j * mellinEulerFactor j (c : ℂ) := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with c hc hcz
    have hc0 : (0 : ℝ) < c := hc
    have hre : ((c : ℂ)).re = c := Complex.ofReal_re c
    exact hsymbol _ (by rw [hre]; exact hc0) (by rw [hre]; exact hcz)
      (F.mellin_profile_ofReal_ne_zero hH hc0 (lt_of_lt_sub_one hcz))
  exact (tendsto_nhds_unique ((F.tendsto_inversionSymbol_nhdsGT_zero hH).congr' heq) hP).symm

/-! ## The recursion at a real point of the strip -/

/-- `m(c)` is a positive real, at every order the strip allows. -/
theorem negMoment_toReal_pos (hH : F.StandingHypothesis) {c : ℝ} (hc : 0 < c)
    (hc' : ENNReal.ofReal c < F.zStar) : 0 < (F.negMoment c).toReal :=
  ENNReal.toReal_pos (F.negMoment_pos (F.lawT₁_singleton_zero hH.1) c).ne'
    (F.negMoment_ne_top_of_lt_zStar hc hc')

/-- **`lem:moment-recursion`(3).** At a real point of the strip, `m(z+1) = Q(z)·m(z)` with `Q(z)`
a positive real.

The whole of it is `lem:inversion-symbol`'s closed form `B(-z) = z·m(z+1)/m(z)` read where the
symbol is known to be the polynomial --- which at a real point it is, `H̃` not vanishing there ---
followed by cancelling `z`. Positivity of `Q` is not a separate argument: `Q(z)` *is* a ratio of
positive moments, so it inherits both realness and sign.

The range is `0 < z < z_* - 1`. Extending it to `(0,∞)`, which is how the blueprint states the
clause, is `z_* = ∞`, i.e. clause (2), i.e. ledger A13. -/
theorem exists_pos_symbolQuotient_of_symbol_eq (hH : F.StandingHypothesis) {n : ℕ} (γ : ℕ → ℂ)
    (hsymbol : ∀ z : ℂ, 0 < z.re → ENNReal.ofReal z.re < F.zStar - 1 →
      mellin (fun s => (F.profile s : ℂ)) z ≠ 0 →
      F.inversionSymbol z = ∑ j ∈ Finset.range (n + 1), γ j * mellinEulerFactor j z)
    {z : ℝ} (hz : 0 < z) (hz' : ENNReal.ofReal z < F.zStar - 1) :
    ∃ q : ℝ, 0 < q ∧ symbolQuotient γ n (z : ℂ) = (q : ℂ) ∧
      (F.negMoment (z + 1)).toReal = q * (F.negMoment z).toReal := by
  have h0 := F.lawT₁_singleton_zero hH.1
  have hre : ((z : ℂ)).re = z := Complex.ofReal_re z
  have hzne : (z : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
  have hz1' : ENNReal.ofReal (z + 1) < F.zStar := ofReal_add_one_lt_of_lt_sub_one hz.le hz'
  have hmz : 0 < (F.negMoment z).toReal :=
    F.negMoment_toReal_pos hH hz (lt_of_lt_sub_one hz')
  have hmz1 : 0 < (F.negMoment (z + 1)).toReal :=
    F.negMoment_toReal_pos hH (by linarith) hz1'
  -- the two readings of the symbol at `z`
  have hpoly : F.inversionSymbol (z : ℂ)
      = ∑ j ∈ Finset.range (n + 1), γ j * mellinEulerFactor j (z : ℂ) :=
    hsymbol _ (by rw [hre]; exact hz) (by rw [hre]; exact hz')
      (F.mellin_profile_ofReal_ne_zero hH hz (lt_of_lt_sub_one hz'))
  have hclosed : F.inversionSymbol (z : ℂ)
      = (z : ℂ) * F.negMomentC ((z : ℂ) + 1) / F.negMomentC (z : ℂ) :=
    F.inversionSymbol_eq hH ⟨by rw [hre]; exact hz, by rw [hre]; exact hz'⟩
  -- both moments, as positive reals
  have hmC : F.negMomentC (z : ℂ) = ((F.negMoment z).toReal : ℂ) := F.negMomentC_ofReal h0 z
  have hmC1 : F.negMomentC ((z : ℂ) + 1) = ((F.negMoment (z + 1)).toReal : ℂ) := by
    rw [show ((z : ℂ) + 1) = ((z + 1 : ℝ) : ℂ) from by push_cast; ring, F.negMomentC_ofReal h0]
  refine ⟨(F.negMoment (z + 1)).toReal / (F.negMoment z).toReal, div_pos hmz1 hmz, ?_, ?_⟩
  · -- `z·Q(z) = z·m(z+1)/m(z)`, and `z ≠ 0`
    have hfac := sum_mellinEulerFactor_eq_mul_symbolQuotient
      (F.coeff_zero_eq_zero_of_symbol_eq hH γ hsymbol) n (z : ℂ)
    rw [hfac] at hpoly
    have hmne : ((F.negMoment z).toReal : ℂ) ≠ 0 := by exact_mod_cast hmz.ne'
    have := hpoly.symm.trans hclosed
    rw [hmC, hmC1] at this
    refine mul_left_cancel₀ hzne ?_
    rw [this, mul_div_assoc]
    push_cast
    ring
  · rw [div_mul_cancel₀ _ hmz.ne']

/-! ## The node

Clause (1)'s factorisation and clause (3), for a local operator: `lem:local-polynomial-symbol`
supplies the symbol identity, and everything above consumes it. -/

/-- **`lem:moment-recursion-quotient`**: the `[T]` content of `lem:moment-recursion`(1) and (3).

`B(-z) = z·Q(z)` identically, and on the real part of the strip `m(z+1) = Q(z)·m(z)` with `Q > 0`.
What is *not* here is clause (2), `z_* = ∞`, which is ledger A13 and which is also what would
widen the second display's range to the whole half-line. -/
theorem exists_symbolQuotient_of_isLocalOfOrder (hH : F.StandingHypothesis) {c : ℝ} (hc : 0 < c)
    (hc' : ENNReal.ofReal c < F.zStar - 1) {n : ℕ} (hL : F.IsLocalOfOrder c n) :
    ∃ Q : ℂ → ℂ,
      (∀ z : ℂ, (∑ j ∈ Finset.range (n + 1), hL.coeff j 1 * mellinEulerFactor j z)
        = z * Q z) ∧
      (∀ z : ℝ, 0 < z → ENNReal.ofReal z < F.zStar - 1 → ∃ q : ℝ, 0 < q ∧ Q (z : ℂ) = (q : ℂ) ∧
        (F.negMoment (z + 1)).toReal = q * (F.negMoment z).toReal) := by
  have hsymbol : ∀ z : ℂ, 0 < z.re → ENNReal.ofReal z.re < F.zStar - 1 →
      mellin (fun s => (F.profile s : ℂ)) z ≠ 0 →
      F.inversionSymbol z
        = ∑ j ∈ Finset.range (n + 1), hL.coeff j 1 * mellinEulerFactor j z :=
    fun z hz hz' hne =>
      (F.sameSymbolAction_of_isLocalOfOrder hH hc hc' hL).eqOn_of_ne_zero ⟨⟨hz, hz'⟩, hne⟩
  exact ⟨symbolQuotient (fun j => hL.coeff j 1) n,
    fun z => sum_mellinEulerFactor_eq_mul_symbolQuotient
      (F.coeff_zero_eq_zero_of_symbol_eq hH _ hsymbol) n z,
    fun z hz hz' => F.exists_pos_symbolQuotient_of_symbol_eq hH _ hsymbol hz hz'⟩

end SelfDecomposableExponent

end Hemigroup
