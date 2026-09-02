/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Hemigroup.InversionOperator
import Hemigroup.MellinEuler
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Local inversion operators

Blueprint: `def:locality-pmp` (12.1), and the (⇐) direction of `lem:local-polynomial-symbol`
(12.2).

## The modelling choice

`IsLocalOfOrderCore` is a **structure carrying the coefficients**, not a `Prop` asserting that some
differential expression exists. The reason is 12.2 itself, whose conclusion is a statement *about*
the coefficients --- `c_j(x) = γ_j x^{j-1}`. Under the existential reading that conclusion cannot
be stated: a caller would `obtain` coefficients and have no way to say they are the same ones it
was given. As fields they are `hL.coeff j`, and the lemma says what the blueprint says.

The cost is that locality is then data, so the direction proved here concludes
`Nonempty (F.IsLocalOfOrderCore c n)` --- the propositional reading, and the one `thm:locality`
quantifies over. A caller wanting the coefficients takes the structure instead.

## What the (⇐) direction actually is

Nothing analytic, once `MellinEuler.lean` is in hand. A polynomial symbol acts on a test function
by the Euler factors, `mellin_pow_mul_iteratedDeriv` turns each factor into `x^j ∂_x^j`, and
`mellinInv` --- linear along the line, and inverting the transform of a test function exactly ---
carries the whole sum back. The weight `x^{-1}` in `def:inversion-operator` is what turns `x^j`
into `x^{j-1}`, which is where the homogeneous form of the coefficients comes from: it is not
imposed, it is what the Mellin class permits.

The one thing it does need of `F` is that the zeros of `H̃` on the line are null, and that is not
a repair of the argument but the price of a hypothesis the *other* direction can supply. `B` is a
quotient with denominator `H̃`; where that vanishes, `B`'s value is Lean's `0` and no polynomial
identity holds, so a symbol hypothesis asserting one at every point of the strip is one the (⇒)
direction cannot deliver, and the two halves would not compose. Asking for it off the zeros costs
nothing here --- `mellinInv` integrates over the line and `mellinInv_congr_line_ae` discards a
null set --- and costs the standing hypothesis (H), which `ae_mellin_profile_ne_zero` needs and
which nothing else in this direction uses.
-/

namespace Hemigroup

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent)

/-- **`def:locality-pmp`, the locality half, on test functions only.**

The blueprint's Definition 12.1 tests agreement on `C_c^∞((0,∞))`, which is this. It is *not* the
whole of the definition as chapter 12 now states it --- see `IsLocalOfOrder` below --- but it is
what a polynomial symbol delivers cheaply, so it is worth having on its own. -/
structure IsLocalOfOrderCore (c : ℝ) (n : ℕ) where
  /-- The coefficients `c_j` of the differential expression. -/
  coeff : ℕ → ℝ → ℂ
  /-- Each is continuous on the half-line. -/
  continuousOn_coeff : ∀ j, ContinuousOn (coeff j) (Ioi 0)
  /-- The leading coefficient does not vanish identically, which is what fixes the order. -/
  leading_ne_zero : ∃ x₀ : ℝ, 0 < x₀ ∧ coeff n x₀ ≠ 0
  /-- Agreement with the differential expression, on the test class and on the half-line. -/
  eq_sum_iteratedDeriv : ∀ {g : ℝ → ℂ}, IsTestFunction g → ∀ {x : ℝ}, 0 < x →
    F.inversionOperator c g x = ∑ j ∈ Finset.range (n + 1), coeff j x * iteratedDeriv j g x

/-- **`def:locality-pmp`, the locality half.** `A` is *local of order `n`* at height `c`: it agrees
with the differential expression on the test functions **and on the profiles** `H(s·)`.

**Why the profiles are in the test class.** Formalising the (⇒) direction showed that the
blueprint's "Mellin-transforming on a line and using injectivity gives `B = P`" needs the two
symbols compared where `B`'s behaviour is known, and the only such place is
`lem:symbol-uniqueness`'s class --- the profiles. Locality tested on `C_c^∞((0,∞))` alone says
nothing there, the profiles being neither compactly supported nor supported away from the origin,
and passing from one class to the other is an approximation argument the article does not make.
Widening the definition is the smaller change and makes 12.2 and `lem:symbol-uniqueness` speak
about the same objects, which they otherwise do not.

The two clauses are separated because they cost differently, and the difference is worth keeping
visible now that both are proved. The test-function clause is `isLocalOfOrderCore_of_symbol_eq`,
here. The profile clause is true for the same reason but by two different ingredients, and lives
in `ProfileEuler.lean` where they are: the engine `M[xʲ∂ₓʲH(s·)](w) = E_j(w)M[H(s·)](w)`, which
needs no integration by parts because `∂ₓ^j H(sx) = ∫ (-st)^j e^{-sxt} dμ(t)` is already an
integral; and vertical integrability of `P(z)·s^{-z}H̃(z)`, which needs
`∫ |τ|ⁿ‖Γ(c+iτ)‖ dτ < ∞` where `lem:mellin-vertical` needed only the case `n = 0`. The second was
the whole of what was missing, and it is the same induction: `Γ(z+k)/Γ(z)` is `k` factors of
imaginary part `τ`. See `isLocalOfOrder_of_symbol_eq` and
`nonempty_isLocalOfOrder_iff_symbol_eq`, which is the equivalence the blueprint states. -/
structure IsLocalOfOrder (c : ℝ) (n : ℕ) extends IsLocalOfOrderCore F c n where
  /-- Agreement with the differential expression on the profiles as well. -/
  eq_sum_iteratedDeriv_profile : ∀ {s : ℝ}, 0 < s → ∀ {x : ℝ}, 0 < x →
    F.inversionOperator c (fun u : ℝ => (F.profile (s * u) : ℂ)) x
      = ∑ j ∈ Finset.range (n + 1),
          coeff j x * iteratedDeriv j (fun u : ℝ => (F.profile (s * u) : ℂ)) x

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

**The symbol identity is asked for off the zeros of `H̃`, which is what the (⇒) direction
delivers.** `F.inversionSymbol` is the quotient `H̃(z+1)/H̃(z)`, so at a zero of the denominator
its value is Lean's `0` and no identity with a polynomial can hold there; a hypothesis asserting
one on the whole strip is unsatisfiable at exactly the points where the (⇒) direction has nothing
to say, and the two halves would not compose. Restricting it costs nothing, because `mellinInv`
integrates over the line and never evaluates on it: the zeros are null there
(`ae_mellin_profile_ne_zero`) and `mellinInv_congr_line_ae` discards them.

**What it does cost is the standing hypothesis (H)**, and the trade is worth recording rather than
hiding. Nothing in the argument proper uses (H) --- the Euler factors, the vertical decay and the
inversion are facts about test functions and say nothing about `F` --- and this direction was
stated without it for that reason. But "the zeros are null" is `lem:inversion-symbol`, which needs
`H̃` analytic and not identically zero on the strip, which needs (H). So (H) enters here as the
price of a hypothesis the other direction can actually supply, not as a step of the proof. (H) was
in any case already doing something for this statement: `0 < c < z_* - 1` is inhabited only when
`z_* > 1`.

Locality is data, so the content of this direction is the *structure*, with its coefficients
displayed: that is `isLocalOfOrderCoreOfSymbolEq`, and a caller that has to say which coefficients
it got --- as the profile clause below does --- takes it rather than the `Nonempty` reading. -/
noncomputable def isLocalOfOrderCoreOfSymbolEq (hH : F.StandingHypothesis) {c : ℝ} (hc : 0 < c)
    (hc' : ENNReal.ofReal c < F.zStar - 1) {n : ℕ} (γ : ℕ → ℂ) (hγ : γ n ≠ 0)
    (hsymbol : ∀ z : ℂ, 0 < z.re → ENNReal.ofReal z.re < F.zStar - 1 →
      mellin (fun s => (F.profile s : ℂ)) z ≠ 0 →
      F.inversionSymbol z = ∑ j ∈ Finset.range (n + 1), γ j * mellinEulerFactor j z) :
    F.IsLocalOfOrderCore c n where
  coeff := fun j x => γ j * (x : ℂ) ^ ((j : ℤ) - 1)
  continuousOn_coeff := by
    intro j
    refine continuousOn_const.mul (ContinuousOn.zpow₀ ?_ _ fun x hx => Or.inl ?_)
    · exact Complex.continuous_ofReal.continuousOn
    · simpa using ne_of_gt (mem_Ioi.mp hx)
  leading_ne_zero := ⟨1, one_pos, by simpa using hγ⟩
  eq_sum_iteratedDeriv := by
    intro g hg x hx
    have hxne : (x : ℂ) ≠ 0 := by simpa using ne_of_gt hx
    -- the symbol identity, transported to the transforms along the line --- almost everywhere,
    -- the zeros of `H̃` on the line being null
    have hline : ∀ᵐ y : ℝ,
        F.inversionSymbol ((c : ℂ) + y * Complex.I) * mellin g ((c : ℂ) + y * Complex.I)
          = ∑ j ∈ Finset.range (n + 1),
              γ j * mellin (fun t : ℝ => (t : ℂ) ^ j * iteratedDeriv j g t)
                ((c : ℂ) + y * Complex.I) := by
      filter_upwards [F.ae_mellin_profile_ne_zero hH hc (lt_of_lt_sub_one hc')] with y hy
      have hre : ((c : ℂ) + y * Complex.I).re = c := by simp
      rw [hsymbol _ (by rw [hre]; exact hc) (by rw [hre]; exact hc') hy, Finset.sum_mul]
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
      mellinInv_congr_line_ae (G := fun z => F.inversionSymbol z * mellin g z)
        (G' := fun z => ∑ j ∈ Finset.range (n + 1),
          γ j * mellin (fun t : ℝ => (t : ℂ) ^ j * iteratedDeriv j g t) z) c x hline,
      mellinInv_finset_sum _ c _ hx hvi]
    simp only [hterm]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [zpow_sub₀ hxne, zpow_natCast, zpow_one]
    push_cast
    field_simp

/-- **`lem:local-polynomial-symbol`, the (⇐) direction**, in its propositional reading --- the one
`thm:locality` quantifies over. -/
theorem isLocalOfOrderCore_of_symbol_eq (hH : F.StandingHypothesis) {c : ℝ} (hc : 0 < c)
    (hc' : ENNReal.ofReal c < F.zStar - 1) {n : ℕ} (γ : ℕ → ℂ) (hγ : γ n ≠ 0)
    (hsymbol : ∀ z : ℂ, 0 < z.re → ENNReal.ofReal z.re < F.zStar - 1 →
      mellin (fun s => (F.profile s : ℂ)) z ≠ 0 →
      F.inversionSymbol z = ∑ j ∈ Finset.range (n + 1), γ j * mellinEulerFactor j z) :
    Nonempty (F.IsLocalOfOrderCore c n) :=
  ⟨F.isLocalOfOrderCoreOfSymbolEq hH hc hc' γ hγ hsymbol⟩

@[simp] theorem coeff_isLocalOfOrderCoreOfSymbolEq (hH : F.StandingHypothesis) {c : ℝ}
    (hc : 0 < c) (hc' : ENNReal.ofReal c < F.zStar - 1) {n : ℕ} (γ : ℕ → ℂ) (hγ : γ n ≠ 0)
    (hsymbol : ∀ z : ℂ, 0 < z.re → ENNReal.ofReal z.re < F.zStar - 1 →
      mellin (fun s => (F.profile s : ℂ)) z ≠ 0 →
      F.inversionSymbol z = ∑ j ∈ Finset.range (n + 1), γ j * mellinEulerFactor j z) (j : ℕ)
    (x : ℝ) :
    (F.isLocalOfOrderCoreOfSymbolEq hH hc hc' γ hγ hsymbol).coeff j x
      = γ j * (x : ℂ) ^ ((j : ℤ) - 1) := rfl

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

/-- Dilation scales the iterated derivatives: `(Δ_σ g)^{(j)}(x) = σ^{-j} g^{(j)}(x/σ)`. -/
theorem iteratedDeriv_lineDilate {σ : ℝ} (hσ : 0 < σ) {g : ℝ → ℂ} (hg : IsTestFunction g)
    (j : ℕ) (x : ℝ) :
    iteratedDeriv j (lineDilate σ g) x = ((σ⁻¹ : ℝ) ^ j) • iteratedDeriv j g (x / σ) := by
  have hfun : lineDilate σ g = fun t : ℝ => g (σ⁻¹ * t) := by
    funext t; simp [lineDilate, div_eq_inv_mul]
  have hcd : ContDiff ℝ (j : ℕ∞) g := hg.contDiff.of_le (by exact_mod_cast le_top)
  rw [hfun, iteratedDeriv_comp_const_smul hcd σ⁻¹]
  congr 2
  rw [div_eq_inv_mul]

/-! ## Prescribed jets

The (⇒) direction of `lem:local-polynomial-symbol` compares coefficients of `g^{(j)}(x/σ)`, which
is licensed only because a differential expression is determined by its coefficients. In Lean that
is this construction: at every point of `(0,∞)` and every order `m`, a test function whose jet
there is the `m`-th basis vector. Cutting a monomial off with a bump function supported inside
`(0,∞)` does it, and the bump is invisible to the jet because it is identically `1` near the
point. -/

/-- `t ↦ t - c` as a map `ℝ → ℂ` has derivative `1`. -/
theorem hasDerivAt_ofReal_sub (c : ℂ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => (t : ℂ) - c) 1 x := by
  have h : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := by
    simpa using (hasDerivAt_id x).ofReal_comp
  simpa using h.sub_const c

/-- The iterated derivative of `(t - c)^m`, with natural subtraction throughout: for `j > m` the
descending factorial is `0`, which is what makes the formula uniform. -/
theorem iteratedDeriv_ofReal_sub_pow (c : ℂ) (m : ℕ) :
    ∀ (j : ℕ) (x : ℝ), iteratedDeriv j (fun t : ℝ => ((t : ℂ) - c) ^ m) x
      = (m.descFactorial j : ℂ) * ((x : ℂ) - c) ^ (m - j) := by
  intro j
  induction j with
  | zero => intro x; simp
  | succ k ih =>
      intro x
      have hfun : iteratedDeriv k (fun t : ℝ => ((t : ℂ) - c) ^ m)
          = fun y : ℝ => (m.descFactorial k : ℂ) * ((y : ℂ) - c) ^ (m - k) := funext ih
      have hd : HasDerivAt (fun y : ℝ => (m.descFactorial k : ℂ) * ((y : ℂ) - c) ^ (m - k))
          ((m.descFactorial k : ℂ) *
            (((m - k : ℕ) : ℂ) * ((x : ℂ) - c) ^ (m - k - 1) * 1)) x :=
        HasDerivAt.const_mul _ ((hasDerivAt_ofReal_sub c x).pow (m - k))
      rw [iteratedDeriv_succ, hfun, hd.deriv, Nat.descFactorial_succ]
      push_cast
      rw [Nat.sub_sub]
      ring

/-- **A test function with a prescribed jet.** For every `x₀ > 0` and every order `m` there is a
test function whose derivatives at `x₀` are `δ_{jm}`.

This is what licenses comparing coefficients of a differential expression. The bump is chosen with
outer radius `x₀/2`, so its support sits inside `(0,∞)` — the same constraint that
`MellinEuler.lean` needs, arrived at from the other side. -/
theorem exists_isTestFunction_jet {x₀ : ℝ} (hx₀ : 0 < x₀) (m : ℕ) :
    ∃ g : ℝ → ℂ, IsTestFunction g ∧
      ∀ j : ℕ, iteratedDeriv j g x₀ = if j = m then 1 else 0 := by
  set φ : ContDiffBump x₀ := ⟨x₀ / 4, x₀ / 2, by positivity, by linarith⟩ with hφ
  set p : ℝ → ℂ := fun t : ℝ => ((t : ℂ) - (x₀ : ℂ)) ^ m / (m.factorial : ℂ) with hp
  refine ⟨fun t => (φ t : ℂ) * p t, ⟨?_, ?_, ?_⟩, ?_⟩
  · -- smooth
    have h1 : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => ((φ t : ℝ) : ℂ) :=
      Complex.ofRealCLM.contDiff.comp φ.contDiff
    have h2 : ContDiff ℝ (⊤ : ℕ∞) p := by
      have : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => ((t : ℂ) - (x₀ : ℂ)) :=
        Complex.ofRealCLM.contDiff.sub contDiff_const
      exact (this.pow m).div_const _
    exact h1.mul h2
  · -- compactly supported
    refine HasCompactSupport.intro (K := Metric.closedBall x₀ φ.rOut) (isCompact_closedBall _ _)
      fun t ht => ?_
    have : φ t = 0 := by
      refine image_eq_zero_of_notMem_tsupport ?_
      rw [φ.tsupport_eq]
      exact ht
    rw [this]
    simp
  · -- supported inside `(0,∞)`
    have hsub : tsupport (fun t : ℝ => ((φ t : ℝ) : ℂ) * p t)
        ⊆ Metric.closedBall x₀ φ.rOut := by
      refine closure_minimal (fun t ht => ?_) Metric.isClosed_closedBall
      by_contra hmem
      have hz : φ t = 0 := by
        refine image_eq_zero_of_notMem_tsupport ?_
        rw [φ.tsupport_eq]
        exact hmem
      exact ht (by simp [hz])
    intro t ht
    have h := Metric.mem_closedBall.mp (hsub ht)
    have hr : φ.rOut = x₀ / 2 := rfl
    rw [hr, Real.dist_eq] at h
    have habs := abs_le.mp h
    simp only [mem_Ioi]
    linarith [habs.1]
  · -- the jet
    intro j
    have hloc : (fun t : ℝ => ((φ t : ℝ) : ℂ) * p t) =ᶠ[𝓝 x₀] p := by
      have hball : Metric.ball x₀ φ.rIn ∈ 𝓝 x₀ := Metric.ball_mem_nhds _ φ.rIn_pos
      filter_upwards [hball] with t ht
      rw [φ.one_of_mem_closedBall (Metric.ball_subset_closedBall ht)]
      simp
    have hcongr : iteratedDeriv j (fun t : ℝ => ((φ t : ℝ) : ℂ) * p t) x₀ = iteratedDeriv j p x₀ := by
      rw [← iteratedDerivWithin_univ, ← iteratedDerivWithin_univ]
      exact Filter.EventuallyEq.iteratedDerivWithin_eq
        (by rwa [nhdsWithin_univ]) (by simpa using hloc.eq_of_nhds)
    rw [hcongr, hp]
    have hdiv : iteratedDeriv j (fun t : ℝ => ((t : ℂ) - (x₀ : ℂ)) ^ m / (m.factorial : ℂ)) x₀
        = iteratedDeriv j (fun t : ℝ => ((t : ℂ) - (x₀ : ℂ)) ^ m) x₀ / (m.factorial : ℂ) := by
      simpa [div_eq_mul_inv] using
        iteratedDeriv_const_mul (𝕜 := ℝ) (c := ((m.factorial : ℂ))⁻¹) (n := j)
          (f := fun t : ℝ => ((t : ℂ) - (x₀ : ℂ)) ^ m) x₀
    rw [hdiv, iteratedDeriv_ofReal_sub_pow]
    rcases lt_trichotomy j m with h | h | h
    · rw [if_neg (by omega)]
      have : m - j ≠ 0 := by omega
      simp [sub_self, zero_pow this]
    · subst h
      rw [if_pos rfl, Nat.sub_self, Nat.descFactorial_self]
      simp [Nat.factorial_ne_zero]
    · rw [if_neg (by omega), Nat.descFactorial_eq_zero_iff_lt.mpr h]
      simp

/-! ## Covariance forces the coefficients homogeneous

The first half of `lem:local-polynomial-symbol`'s (⇒) direction, and the half the blueprint gets by
"comparing coefficients of `g^{(j)}(x/σ)`". With the two ingredients above that comparison is a
computation: apply locality to `Δ_σ g` at the point `σ`, apply covariance to the same thing, and
feed both a test function whose jet at `1` is a basis vector. The sums collapse to a single term
and the identity `c_m(σ) σ^{-m} = σ^{-1} c_m(1)` falls out.

Only one point is needed, not a family: evaluating at `x = σ` sends `x/σ` to `1`, so a single jet
at `1` settles every `σ` at once. -/

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent)

/-- **The coefficients of a local inversion operator are homogeneous**: `c_m(σ) = c_m(1) σ^{m-1}`.

This is what the blueprint's covariance argument delivers, and it is where the article's claim that
the Mellin class *forces* the form `γ_j x^{j-1}` is discharged --- nothing is imposed. -/
theorem coeff_eq_of_isLocalOfOrder {c : ℝ} {n : ℕ} (hL : F.IsLocalOfOrderCore c n) {m : ℕ}
    (hm : m ≤ n) {σ : ℝ} (hσ : 0 < σ) :
    hL.coeff m σ = hL.coeff m 1 * (σ : ℂ) ^ ((m : ℤ) - 1) := by
  obtain ⟨g, hg, hjet⟩ := exists_isTestFunction_jet (x₀ := (1 : ℝ)) one_pos m
  have hσne : σ ≠ 0 := ne_of_gt hσ
  have hσne' : (σ : ℂ) ≠ 0 := by simpa using hσne
  have hdiv : σ / σ = 1 := div_self hσne
  -- the two readings of `A (Δ_σ g) (σ)`
  have hloc := hL.eq_sum_iteratedDeriv (IsTestFunction.lineDilate hσ hg) hσ
  have hcov := inversionOperator_lineDilate F c hσ g hσ
  have hbase := hL.eq_sum_iteratedDeriv hg one_pos
  -- both sums collapse against the jet
  have hcollapse : ∀ a : ℕ → ℂ,
      ∑ j ∈ Finset.range (n + 1), a j * (if j = m then 1 else 0) = a m := by
    intro a
    rw [Finset.sum_eq_single m (fun b _ hb => by simp [hb]) fun hmem => ?_]
    · simp
    · exact absurd (Finset.mem_range.mpr (by omega)) hmem
  have hleft : F.inversionOperator c (lineDilate σ g) σ
      = hL.coeff m σ * ((σ : ℂ) ^ m)⁻¹ := by
    rw [hloc]
    have : ∀ j : ℕ, hL.coeff j σ * iteratedDeriv j (lineDilate σ g) σ
        = (fun j => hL.coeff j σ * ((σ : ℂ) ^ j)⁻¹) j * (if j = m then 1 else 0) := by
      intro j
      rw [iteratedDeriv_lineDilate hσ hg, hdiv, hjet j, Complex.real_smul]
      push_cast
      rw [inv_pow]
      by_cases h : j = m <;> simp [h]
    rw [Finset.sum_congr rfl fun j _ => this j, hcollapse]
  have hright : F.inversionOperator c g 1 = hL.coeff m 1 := by
    rw [hbase]
    have : ∀ j : ℕ, hL.coeff j 1 * iteratedDeriv j g 1
        = hL.coeff j 1 * (if j = m then 1 else 0) := fun j => by rw [hjet j]
    rw [Finset.sum_congr rfl fun j _ => this j, hcollapse]
  rw [hdiv, hright] at hcov
  rw [hleft] at hcov
  -- `c_m(σ) σ^{-m} = σ^{-1} c_m(1)`
  push_cast at hcov
  rw [zpow_sub₀ hσne', zpow_natCast, zpow_one]
  field_simp at hcov ⊢
  linear_combination hcov

end SelfDecomposableExponent

end Hemigroup
