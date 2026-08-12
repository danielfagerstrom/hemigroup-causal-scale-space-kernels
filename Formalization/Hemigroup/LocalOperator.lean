/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.InversionOperator
import Hemigroup.MellinEuler

/-!
# Local inversion operators

Blueprint: `def:locality-pmp` (12.1), and the (⇐) direction of `lem:local-polynomial-symbol`
(12.2).

## The modelling choice

`IsLocalOfOrder` is a **structure carrying the coefficients**, not a `Prop` asserting that some
differential expression exists. The reason is 12.2 itself, whose conclusion is a statement *about*
the coefficients --- `c_j(x) = γ_j x^{j-1}`. Under the existential reading that conclusion cannot
be stated: a caller would `obtain` coefficients and have no way to say they are the same ones it
was given. As fields they are `hL.coeff j`, and the lemma says what the blueprint says.

The cost is that locality is then data, so the direction proved here concludes
`Nonempty (F.IsLocalOfOrder c n)` --- the propositional reading, and the one `thm:locality`
quantifies over. A caller wanting the coefficients takes the structure instead.

## What the (⇐) direction actually is

Nothing analytic, once `MellinEuler.lean` is in hand. A polynomial symbol acts on a test function
by the Euler factors, `mellin_pow_mul_iteratedDeriv` turns each factor into `x^j ∂_x^j`, and
`mellinInv` --- linear along the line, and inverting the transform of a test function exactly ---
carries the whole sum back. The weight `x^{-1}` in `def:inversion-operator` is what turns `x^j`
into `x^{j-1}`, which is where the homogeneous form of the coefficients comes from: it is not
imposed, it is what the Mellin class permits.
-/

namespace Hemigroup

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent)

/-- **`def:locality-pmp`, the locality half.** `A` is *local of order `n`* at height `c`. -/
structure IsLocalOfOrder (c : ℝ) (n : ℕ) where
  /-- The coefficients `c_j` of the differential expression. -/
  coeff : ℕ → ℝ → ℂ
  /-- Each is continuous on the half-line. -/
  continuousOn_coeff : ∀ j, ContinuousOn (coeff j) (Ioi 0)
  /-- The leading coefficient does not vanish identically, which is what fixes the order. -/
  leading_ne_zero : ∃ x₀ : ℝ, 0 < x₀ ∧ coeff n x₀ ≠ 0
  /-- Agreement with the differential expression, on the test class and on the half-line. -/
  eq_sum_iteratedDeriv : ∀ {g : ℝ → ℂ}, IsTestFunction g → ∀ {x : ℝ}, 0 < x →
    F.inversionOperator c g x = ∑ j ∈ Finset.range (n + 1), coeff j x * iteratedDeriv j g x

/-- **`def:locality-pmp`, the maximum-principle half**, in its real-valued reading.

`inversionOperator` is `ℂ`-valued and `(Ag)(x₀) ≤ 0` is not a statement about a complex number.
Asserting `Re (Ag)(x₀) ≤ 0` is weaker than first proving that `A` preserves realness, and is
therefore the safer of the two readings. -/
def SatisfiesPMP (c : ℝ) : Prop :=
  ∀ {g : ℝ → ℝ}, IsTestFunction (fun x => (g x : ℂ)) → ∀ {x₀ : ℝ}, 0 < x₀ → 0 ≤ g x₀ →
    (∀ x : ℝ, 0 < x → g x ≤ g x₀) →
      (F.inversionOperator c (fun x => (g x : ℂ)) x₀).re ≤ 0

/-- **`lem:local-polynomial-symbol`, the (⇐) direction.** A polynomial symbol, expanded in Euler
factors, gives a differential expression whose coefficients are `γ_j x^{j-1}`.

**The standing hypothesis (H) is not among the hypotheses**, and its absence is not an oversight.
The blueprint states the whole of chapter 12 under (H), and this direction turns out not to use
it: the symbol identity is supplied by `hsymbol`, and everything else --- the Euler factors, the
vertical decay, the inversion --- is a fact about test functions and needs nothing about `F`.
Where (H) does enter is in making the statement non-vacuous, since `0 < c < z_* - 1` is inhabited
only when `z_* > 1`. That is a different role from being used in the proof, and the two are worth
keeping apart. -/
theorem isLocalOfOrder_of_symbol_eq {c : ℝ} (hc : 0 < c)
    (hc' : c < F.zStar - 1) {n : ℕ} (γ : ℕ → ℂ) (hγ : γ n ≠ 0)
    (hsymbol : ∀ z : ℂ, 0 < z.re → z.re < F.zStar - 1 →
      F.inversionSymbol z = ∑ j ∈ Finset.range (n + 1), γ j * mellinEulerFactor j z) :
    Nonempty (F.IsLocalOfOrder c n) := by
  refine ⟨{ coeff := fun j x => γ j * (x : ℂ) ^ ((j : ℤ) - 1)
            continuousOn_coeff := ?_
            leading_ne_zero := ⟨1, one_pos, by simpa using hγ⟩
            eq_sum_iteratedDeriv := ?_ }⟩
  · intro j
    refine continuousOn_const.mul (ContinuousOn.zpow₀ ?_ _ fun x hx => Or.inl ?_)
    · exact Complex.continuous_ofReal.continuousOn
    · simpa using ne_of_gt (mem_Ioi.mp hx)
  · intro g hg x hx
    have hxne : (x : ℂ) ≠ 0 := by simpa using ne_of_gt hx
    -- the symbol identity, transported to the transforms along the line
    have hline : ∀ y : ℝ,
        F.inversionSymbol ((c : ℂ) + y * Complex.I) * mellin g ((c : ℂ) + y * Complex.I)
          = ∑ j ∈ Finset.range (n + 1),
              γ j * mellin (fun t : ℝ => (t : ℂ) ^ j * iteratedDeriv j g t)
                ((c : ℂ) + y * Complex.I) := by
      intro y
      have hre : ((c : ℂ) + y * Complex.I).re = c := by simp
      rw [hsymbol _ (by rw [hre]; exact hc) (by rw [hre]; exact hc'), Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mellin_pow_mul_iteratedDeriv hg j]
      ring
    have hvi : ∀ j ∈ Finset.range (n + 1),
        Complex.VerticalIntegrable
          (fun z => γ j * mellin (fun t : ℝ => (t : ℂ) ^ j * iteratedDeriv j g t) z) c :=
      fun j _ => (verticalIntegrable_mellin (hg.pow_mul_iteratedDeriv j) c).const_mul (γ j)
    have hterm : ∀ j : ℕ, mellinInv c
        (fun z => γ j * mellin (fun t : ℝ => (t : ℂ) ^ j * iteratedDeriv j g t) z) x
          = γ j * ((x : ℂ) ^ j * iteratedDeriv j g x) := by
      intro j
      rw [mellinInv_const_mul,
        mellinInv_mellin_of_isTestFunction (hg.pow_mul_iteratedDeriv j) c hx]
    rw [inversionOperator,
      mellinInv_congr_line (G := fun z => F.inversionSymbol z * mellin g z)
        (G' := fun z => ∑ j ∈ Finset.range (n + 1),
          γ j * mellin (fun t : ℝ => (t : ℂ) ^ j * iteratedDeriv j g t) z) c x hline,
      mellinInv_finset_sum _ c _ hx hvi]
    simp only [hterm]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [zpow_sub₀ hxne, zpow_natCast, zpow_one]
    push_cast
    field_simp

end SelfDecomposableExponent

/-! ## Covariance

The blueprint's proof of `lem:local-polynomial-symbol` opens the (⇒) direction with "every
operator of `def:inversion-operator` satisfies the covariance `A Δ_σ = σ^{-1} Δ_σ A`", asserted
in passing. It is what turns "some continuous `c_j`" into `γ_j x^{j-1}`, so it is the load-bearing
step of that direction and is proved here rather than asserted.

The mechanism is entirely Mellin-side: dilation multiplies the transform by `σ^z`
(`mellin_comp_mul_left`), and multiplying the symbol by `σ^z` translates the inverse transform's
argument, because `x^{-(c+iy)} σ^{c+iy} = (x/σ)^{-(c+iy)}`. Everything reduces to that one
identity between positive reals raised to a complex power, which is cleanest through `exp`. -/

/-- Dilation on the memory line, `(Δ_σ g)(x) = g(x/σ)`. -/
noncomputable def lineDilate (σ : ℝ) (g : ℝ → ℂ) : ℝ → ℂ := fun x => g (x / σ)

/-- A positive real to a complex power, through `exp`: the form in which the two identities below
are one line of `ring_nf`. -/
theorem ofReal_cpow_eq_exp {a : ℝ} (ha : 0 < a) (w : ℂ) :
    (a : ℂ) ^ w = Complex.exp ((Real.log a : ℂ) * w) := by
  rw [Complex.cpow_def_of_ne_zero (by simpa using ne_of_gt ha), Complex.ofReal_log ha.le]

theorem mellin_lineDilate {σ : ℝ} (hσ : 0 < σ) (g : ℝ → ℂ) (z : ℂ) :
    mellin (lineDilate σ g) z = (σ : ℂ) ^ z * mellin g z := by
  have h : lineDilate σ g = fun x : ℝ => g (σ⁻¹ * x) := by
    funext x; simp [lineDilate, div_eq_inv_mul]
  rw [h, mellin_comp_mul_left g z (by positivity : (0 : ℝ) < σ⁻¹), smul_eq_mul]
  congr 1
  rw [ofReal_cpow_eq_exp (by positivity : (0 : ℝ) < σ⁻¹), ofReal_cpow_eq_exp hσ,
    Real.log_inv]
  push_cast
  ring_nf

/-- Multiplying the symbol by `σ^z` dilates the argument of the inverse transform. -/
theorem mellinInv_cpow_mul {σ : ℝ} (hσ : 0 < σ) (c : ℝ) (G : ℂ → ℂ) {x : ℝ} (hx : 0 < x) :
    mellinInv c (fun z => (σ : ℂ) ^ z * G z) x = mellinInv c G (x / σ) := by
  simp only [mellinInv]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  rw [smul_eq_mul, smul_eq_mul, ← mul_assoc]
  congr 1
  have hxσ : (0 : ℝ) < x / σ := div_pos hx hσ
  rw [ofReal_cpow_eq_exp hx, ofReal_cpow_eq_exp hσ, ofReal_cpow_eq_exp hxσ,
    Real.log_div (ne_of_gt hx) (ne_of_gt hσ), ← Complex.exp_add]
  push_cast
  ring_nf

/-- **The covariance of the inversion operator**: `A Δ_σ = σ^{-1} Δ_σ A`. -/
theorem inversionOperator_lineDilate (F : SelfDecomposableExponent) (c : ℝ) {σ : ℝ} (hσ : 0 < σ)
    (g : ℝ → ℂ) {x : ℝ} (hx : 0 < x) :
    F.inversionOperator c (lineDilate σ g) x
      = (σ⁻¹ : ℝ) * F.inversionOperator c g (x / σ) := by
  have hσne : (σ : ℂ) ≠ 0 := by simpa using ne_of_gt hσ
  have hxne : (x : ℂ) ≠ 0 := by simpa using ne_of_gt hx
  have hm : (fun z => F.inversionSymbol z * mellin (lineDilate σ g) z)
      = fun z => (σ : ℂ) ^ z * (F.inversionSymbol z * mellin g z) := by
    funext z
    rw [mellin_lineDilate hσ]
    ring
  rw [SelfDecomposableExponent.inversionOperator, SelfDecomposableExponent.inversionOperator, hm,
    mellinInv_cpow_mul hσ c _ hx]
  push_cast
  field_simp

/-- Dilation preserves the test class, which is what lets the covariance be applied to it. -/
theorem IsTestFunction.lineDilate {σ : ℝ} (hσ : 0 < σ) {g : ℝ → ℂ} (hg : IsTestFunction g) :
    IsTestFunction (_root_.Hemigroup.lineDilate σ g) where
  contDiff := by
    have h : ContDiff ℝ (⊤ : ℕ∞) fun x : ℝ => x / σ := by fun_prop
    exact hg.contDiff.comp h
  hasCompactSupport := by
    have himg : IsCompact ((fun x : ℝ => σ * x) '' tsupport g) :=
      hg.hasCompactSupport.isCompact.image (by fun_prop)
    refine HasCompactSupport.of_support_subset_isCompact himg fun x hx => ?_
    refine ⟨x / σ, subset_tsupport _ hx, ?_⟩
    field_simp
  tsupport_subset := by
    intro x hx
    have hsub : tsupport (_root_.Hemigroup.lineDilate σ g) ⊆ (fun t : ℝ => σ * t) '' tsupport g := by
      refine closure_minimal (fun y hy => ⟨y / σ, subset_tsupport _ hy, by field_simp⟩)
        (((hg.hasCompactSupport.isCompact.image (by fun_prop : Continuous fun t : ℝ => σ * t))).isClosed)
    obtain ⟨t, ht, rfl⟩ := hsub hx
    exact mul_pos hσ (hg.tsupport_subset ht)

end Hemigroup
