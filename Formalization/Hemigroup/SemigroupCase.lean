/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the MIT license as described in the file LICENSES/MIT.txt.
Authors: Daniel Fagerström
-/
import Hemigroup.Gauge

/-!
# `cor:semigroup-case`: the setting, and the two functional equations it runs on

Blueprint: `cor:semigroup-case` (Corollary 7.4). If the family is one-parameter — `Φ_{x,y}`
depending only on `y - x` — then `F(s) = s^α` with `0 < α ≤ 1`, and the kernels are the extremal
stable densities of the 2005 theorem together with the pure delay at `α = 1`.

The corollary and everything it runs on. The two Cauchy arguments are stated for arbitrary
functions and proved first, because neither mentions a hemigroup; `levyExponent_add_le` likewise.

## Two functional equations, and only one of them is on a half-line

The proof uses Cauchy's equation twice, and the two are not the same problem.

* **Additive, on `[0,∞)`.** `x ↦ G(x,s)` is additive because the cascade law makes increments add
  and the one-parameter hypothesis makes them depend only on the gap. It lives on the half-line,
  where Mathlib's `map_real_smul` — continuous additive maps of real vector spaces are linear —
  does not directly apply. `eq_mul_of_addOn_Ici` bridges that with an odd extension.
* **Multiplicative, on `(0,∞)`.** `c(σ) := S_σ 1` is multiplicative because the action composes.
  Conjugating by `exp`/`log` puts it on **all** of `ℝ`, where `map_real_smul` applies directly and
  no extension is needed.

The asymmetry is worth recording because it decided how much of this file is bookkeeping: the
multiplicative equation, which reads as the harder one and is the one the draft cites a lemma for,
is the cheaper of the two in Lean.

## The multiplier of the action *is* `F`

The blueprint introduces `c(σ)` with `S_σ x = c(σ)x` and `c(σ)g(s) = g(σs)`, and identifies
`c(σ) = σ^α` by Cauchy before concluding `g(s) = s^α`. Writing it in Lean collapses the two: with
the normalisation `g_{0,1}(1) = 1`, `(6.1)` at `s = 1` gives `S_σ x = x·G(1,σ)` outright, so
`c = F` on `(0,∞)` and **there is only one unknown function, not two**. The multiplicativity of
`c` and the scaling law for `g` are then the same identity, and the Cauchy step is applied once.

That is not a shortcut around the mathematics; it is what the normalisation is for, and the
blueprint's two-function presentation hides it.
-/

namespace Hemigroup

open MeasureTheory Set Filter

open scoped Topology

/-! ## Cauchy's equation, additively on the half-line -/

/-- The odd extension of a function on `[0,∞)`, written so that it is continuous by construction:
`max x 0` and `max (-x) 0` are continuous and land in `[0,∞)`. -/
noncomputable def oddExtend (h : ℝ → ℝ) (x : ℝ) : ℝ := h (max x 0) - h (max (-x) 0)

theorem oddExtend_of_nonneg {h : ℝ → ℝ} (h0 : h 0 = 0) {x : ℝ} (hx : 0 ≤ x) :
    oddExtend h x = h x := by
  rw [oddExtend, max_eq_left hx, max_eq_right (by linarith), h0, sub_zero]

theorem continuous_oddExtend {h : ℝ → ℝ} (hcont : ContinuousOn h (Ici 0)) :
    Continuous (oddExtend h) := by
  have hmax : ∀ y : ℝ, max y 0 ∈ Ici (0 : ℝ) := fun y => le_max_right y 0
  exact (hcont.comp_continuous (by fun_prop) hmax).sub
    (hcont.comp_continuous (by fun_prop) fun y => hmax (-y))

/-- **Cauchy's functional equation on `[0,∞)`.** A function continuous on the half-line and
additive there is linear there.

The odd extension is additive on all of `ℝ` — six sign cases, each an instance of the half-line
hypothesis — and continuous, so Mathlib's `map_real_smul` applies. -/
theorem eq_mul_of_addOn_Ici {h : ℝ → ℝ} (hcont : ContinuousOn h (Ici 0))
    (hadd : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → h (a + b) = h a + h b) {r : ℝ} (hr : 0 ≤ r) :
    h r = r * h 1 := by
  have h0 : h 0 = 0 := by
    have := hadd 0 0 le_rfl le_rfl
    rw [add_zero] at this
    linarith
  -- a difference of values depends only on the difference of arguments
  have hdiff : ∀ p q u v : ℝ, 0 ≤ p → 0 ≤ q → 0 ≤ u → 0 ≤ v → p + v = u + q →
      h p - h q = h u - h v := by
    intro p q u v hp hq hu hv heq
    have h1 := hadd p v hp hv
    have h2 := hadd u q hu hq
    rw [heq] at h1
    linarith
  have hmax : ∀ y : ℝ, 0 ≤ max y 0 := fun y => le_max_right y 0
  have hposneg : ∀ y : ℝ, max y 0 - max (-y) 0 = y := by
    intro y
    rcases le_or_gt 0 y with hy | hy
    · rw [max_eq_left hy, max_eq_right (by linarith), sub_zero]
    · rw [max_eq_right hy.le, max_eq_left (by linarith), zero_sub, neg_neg]
  have hHadd : ∀ a b : ℝ, oddExtend h (a + b) = oddExtend h a + oddExtend h b := by
    intro a b
    have hsum : oddExtend h a + oddExtend h b
        = h (max a 0 + max b 0) - h (max (-a) 0 + max (-b) 0) := by
      rw [oddExtend, oddExtend, hadd _ _ (hmax a) (hmax b), hadd _ _ (hmax (-a)) (hmax (-b))]
      ring
    rw [hsum, oddExtend]
    refine hdiff _ _ _ _ (hmax _) (hmax _) (by positivity) (by positivity) ?_
    have ha := hposneg a
    have hb := hposneg b
    have hab := hposneg (a + b)
    linarith
  set H : ℝ →+ ℝ := AddMonoidHom.mk' (oddExtend h) hHadd with hH
  have hHcont : Continuous H := continuous_oddExtend hcont
  have hlin : H (r • (1 : ℝ)) = r • H 1 := map_real_smul H hHcont r 1
  rw [smul_eq_mul, mul_one, smul_eq_mul] at hlin
  have h1 : H r = oddExtend h r := rfl
  have h2 : H 1 = oddExtend h 1 := rfl
  rw [h1, h2, oddExtend_of_nonneg h0 hr, oddExtend_of_nonneg h0 zero_le_one] at hlin
  exact hlin

/-! ## Cauchy's equation, multiplicatively on `(0,∞)` -/

/-- **A continuous multiplicative homomorphism of `(0,∞)` is a power.**

`log ∘ c ∘ exp` is additive and continuous on all of `ℝ`, so `map_real_smul` gives it directly;
the exponent is `α = log (c e)`. Positivity of `c` is what makes the logarithm available and is
not a technicality — it is (ND), through `S_pos`. -/
theorem exists_rpow_of_mul {c : ℝ → ℝ} (hpos : ∀ σ : ℝ, 0 < σ → 0 < c σ)
    (hcont : ContinuousOn c (Ioi 0))
    (hmul : ∀ σ τ : ℝ, 0 < σ → 0 < τ → c (σ * τ) = c σ * c τ) :
    ∃ α : ℝ, ∀ σ : ℝ, 0 < σ → c σ = σ ^ α := by
  have hce : ∀ u : ℝ, 0 < c (Real.exp u) := fun u => hpos _ (Real.exp_pos u)
  have hcexp : Continuous fun u : ℝ => c (Real.exp u) :=
    hcont.comp_continuous Real.continuous_exp fun u => mem_Ioi.mpr (Real.exp_pos u)
  have hdcont : Continuous fun u : ℝ => Real.log (c (Real.exp u)) :=
    hcexp.log fun u => (hce u).ne'
  have hdadd : ∀ u v : ℝ, Real.log (c (Real.exp (u + v)))
      = Real.log (c (Real.exp u)) + Real.log (c (Real.exp v)) := by
    intro u v
    rw [Real.exp_add, hmul _ _ (Real.exp_pos u) (Real.exp_pos v),
      Real.log_mul (hce u).ne' (hce v).ne']
  set D : ℝ →+ ℝ := AddMonoidHom.mk' (fun u => Real.log (c (Real.exp u))) hdadd with hD
  refine ⟨Real.log (c (Real.exp 1)), fun σ hσ => ?_⟩
  have hlin : D (Real.log σ • (1 : ℝ)) = Real.log σ • D 1 := map_real_smul D hdcont _ 1
  rw [smul_eq_mul, mul_one, smul_eq_mul] at hlin
  have hval : Real.log (c σ) = Real.log σ * Real.log (c (Real.exp 1)) := by
    have h1 : D (Real.log σ) = Real.log (c σ) := by
      show Real.log (c (Real.exp (Real.log σ))) = _
      rw [Real.exp_log hσ]
    have h2 : D 1 = Real.log (c (Real.exp 1)) := rfl
    rw [h1, h2] at hlin
    exact hlin
  rw [Real.rpow_def_of_pos hσ, ← hval, Real.exp_log (hpos σ hσ)]

/-! ## Subadditivity of a Lévy exponent -/

/-- **A Lévy exponent is subadditive.** `1 - e^{-(s+t)u} ≤ (1-e^{-su}) + (1-e^{-tu})`, which is
`(1-e^{-su})(1-e^{-tu}) ≥ 0` rearranged, plus additivity of the drift.

This is what bounds `α` by `1`: for `F(s) = s^α` it gives `2^α ≤ 2`. The blueprint reaches the
same bound through membership of `BF₀`; subadditivity is the part of that membership the bound
actually needs, and it is visible in the representation. -/
theorem levyExponent_add_le {b₀ : ℝ} (hb₀ : 0 ≤ b₀) {ν : Measure ℝ} (hν : IsCausal ν)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    levyExponent b₀ ν (s + t) ≤ levyExponent b₀ ν s + levyExponent b₀ ν t := by
  have hmeas : AEMeasurable (fun u : ℝ => ENNReal.ofReal (1 - Real.exp (-(s * u)))) ν := by
    fun_prop
  have hjump : (∫⁻ u, ENNReal.ofReal (1 - Real.exp (-((s + t) * u))) ∂ν)
      ≤ (∫⁻ u, ENNReal.ofReal (1 - Real.exp (-(s * u))) ∂ν)
        + ∫⁻ u, ENNReal.ofReal (1 - Real.exp (-(t * u))) ∂ν := by
    rw [← lintegral_add_left' hmeas]
    refine lintegral_mono_ae ?_
    filter_upwards [hν.ae_nonneg] with u hu
    have h1 : Real.exp (-(s * u)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have h2 : Real.exp (-(t * u)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hprod : Real.exp (-((s + t) * u)) = Real.exp (-(s * u)) * Real.exp (-(t * u)) := by
      rw [← Real.exp_add]
      ring_nf
    nlinarith [Real.exp_pos (-(s * u)), Real.exp_pos (-(t * u))]
  rw [levyExponent, levyExponent, levyExponent, mul_add,
    ENNReal.ofReal_add (mul_nonneg hb₀ hs) (mul_nonneg hb₀ ht)]
  calc ENNReal.ofReal (b₀ * s) + ENNReal.ofReal (b₀ * t)
        + ∫⁻ u, ENNReal.ofReal (1 - Real.exp (-((s + t) * u))) ∂ν
      ≤ ENNReal.ofReal (b₀ * s) + ENNReal.ofReal (b₀ * t)
        + ((∫⁻ u, ENNReal.ofReal (1 - Real.exp (-(s * u))) ∂ν)
          + ∫⁻ u, ENNReal.ofReal (1 - Real.exp (-(t * u))) ∂ν) := by gcongr
    _ = (ENNReal.ofReal (b₀ * s) + ∫⁻ u, ENNReal.ofReal (1 - Real.exp (-(s * u))) ∂ν)
        + (ENNReal.ofReal (b₀ * t) + ∫⁻ u, ENNReal.ofReal (1 - Real.exp (-(t * u))) ∂ν) := by
        ring

/-! ## The one-parameter hypothesis -/

namespace CascadeCore

/-- **The one-parameter (semigroup) case**: `Φ_{x,y}` depends only on `y - x`.

Written as `Φ_{x,x+r} = Φ_{0,r}` rather than as a two-sided condition on four indices; the two are
equivalent and this form is what every use needs. -/
def IsOneParameter (Fam : CascadeCore) : Prop :=
  ∀ x r : ℝ, 0 ≤ x → 0 ≤ r → Fam.Φ x (x + r) = Fam.Φ 0 r

variable {Fam : CascadeCore} {S : ℝ → ℝ → ℝ}

/-- One-parameter at the level of the representing measures, by uniqueness in
`lem:convolution-representation`. -/
theorem repr_of_isOneParameter (hone : Fam.IsOneParameter) {x r : ℝ} (hx : 0 ≤ x) (hr : 0 ≤ r) :
    Fam.repr x (x + r) = Fam.repr 0 r :=
  mconvL1_injective (isCausal_repr Fam x (x + r)) (isCausal_repr Fam 0 r)
    (((Phi_eq_mconvL1_repr hx (by linarith)).symm.trans (hone x r hx hr)).trans
      (Phi_eq_mconvL1_repr le_rfl hr))

/-- Hence at the level of the exponent: the increment over `[x, x+r]` is `G(r, ·)`. -/
theorem exponent_of_isOneParameter (hone : Fam.IsOneParameter) {x r : ℝ} (hx : 0 ≤ x)
    (hr : 0 ≤ r) (s : ℝ) : Fam.exponent x (x + r) s = Fam.G r s := by
  rw [exponent, G, exponent, repr_of_isOneParameter hone hx hr]

/-- **`G(·, s)` is additive.** The cascade law makes increments add; the one-parameter hypothesis
makes them depend only on the gap. This is the Cauchy equation the corollary runs on. -/
theorem G_add (hone : Fam.IsOneParameter) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {s : ℝ}
    (hs : 0 ≤ s) : Fam.G (a + b) s = Fam.G a s + Fam.G b s := by
  have h := exponent_add (Fam := Fam) (x := 0) (y := a) (z := a + b) le_rfl ha (by linarith) hs
  rwa [exponent_of_isOneParameter hone ha hb s] at h

/-- **Homogeneity**: `G(x,s) = x·G(1,s)`. Cauchy on the half-line, with continuity from (A7). -/
theorem G_eq_mul_of_isOneParameter (hone : Fam.IsOneParameter) {x s : ℝ} (hx : 0 ≤ x)
    (hs : 0 ≤ s) : Fam.G x s = x * Fam.G 1 s :=
  eq_mul_of_addOn_Ici (continuousOn_G Fam hs) (fun _ _ ha hb => G_add hone ha hb hs) hx

/-- **`cor:semigroup-case` (Corollary 7.4).** A one-parameter family, normalised by
`g_{0,1}(1) = 1`, has `F(s) = s^α` with `0 < α ≤ 1`; the scaling action is `S_σ x = σ^α x`, and
`G(x,s) = x s^α`.

The three steps of the blueprint's proof, in order: homogeneity is Cauchy on `[0,∞)`; `(6.1)` then
makes the action linear with multiplier `c(σ) = S_σ 1`, which turns out to be `F` itself; and `c`
is a continuous multiplicative homomorphism, hence a power. The bound `α ≤ 1` is subadditivity of
a Lévy exponent read at `s = t = 1`, which is the part of membership of `BF₀` the bound needs. -/
theorem semigroup_case (hcov : IsScaleCovariant Fam (Ioi 0) S) (hone : Fam.IsOneParameter)
    (hnorm : Fam.G 1 1 = 1) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧
      (∀ s : ℝ, 0 ≤ s → Fam.G 1 s = s ^ α) ∧
      (∀ x s : ℝ, 0 ≤ x → 0 ≤ s → Fam.G x s = x * s ^ α) ∧
      (∀ σ x : ℝ, 0 < σ → 0 ≤ x → S σ x = σ ^ α * x) := by
  -- `(6.1)` with homogeneity: the action is multiplication, and its multiplier *is* `F`
  have hSx : ∀ σ x : ℝ, 0 < σ → 0 ≤ x → S σ x = x * Fam.G 1 σ := by
    intro σ x hσ hx
    have hSxnn : 0 ≤ S σ x := hcov.S_mapsTo σ hσ (mem_Ioi.mpr hσ) (mem_Ici.mpr hx)
    have h := G_scale hcov hσ (mem_Ioi.mpr hσ) hx 1
    rw [G_eq_mul_of_isOneParameter hone hSxnn zero_le_one, hnorm, mul_one, mul_one,
      G_eq_mul_of_isOneParameter hone hx hσ.le] at h
    exact h
  have hS1 : ∀ σ : ℝ, 0 < σ → S σ 1 = Fam.G 1 σ := fun σ hσ => by
    simpa using hSx σ 1 hσ zero_le_one
  -- so `F` is a continuous multiplicative homomorphism of `(0,∞)`
  have hFpos : ∀ σ : ℝ, 0 < σ → 0 < Fam.G 1 σ := fun σ hσ =>
    exponent_pos Fam le_rfl one_pos hσ
  have hFcont : ContinuousOn (fun σ => Fam.G 1 σ) (Ioi 0) :=
    (continuousOn_G_right Fam 1).mono Ioi_subset_Ici_self
  have hFmul : ∀ σ τ : ℝ, 0 < σ → 0 < τ → Fam.G 1 (σ * τ) = Fam.G 1 σ * Fam.G 1 τ := by
    intro σ τ hσ hτ
    have h := S_comp hcov hσ hτ (mem_Ioi.mpr hσ) (mem_Ioi.mpr hτ)
      (mem_Ioi.mpr (mul_pos hσ hτ)) zero_le_one
    rw [hS1 τ hτ, hSx σ _ hσ (hFpos τ hτ).le, hS1 (σ * τ) (mul_pos hσ hτ)] at h
    rw [← h]
    ring
  obtain ⟨α, hα⟩ := exists_rpow_of_mul hFpos hFcont hFmul
  -- `0 < α`, from strict monotonicity of the action
  have hαpos : 0 < α := by
    have hlt : S 1 1 < S 2 1 :=
      strictMonoOn_S_apply hcov (x := 1) one_pos (mem_Ioi.mpr one_pos)
        (mem_Ioi.mpr two_pos) one_lt_two
    rw [S_one hcov (mem_Ioi.mpr one_pos) zero_le_one, hS1 2 two_pos, hα 2 two_pos] at hlt
    rcases (Real.one_lt_rpow_iff_of_pos two_pos).mp hlt with ⟨_, h⟩ | ⟨h, -⟩
    · exact h
    · linarith
  -- `F(s) = s^α`, the origin included
  have hF : ∀ s : ℝ, 0 ≤ s → Fam.G 1 s = s ^ α := by
    intro s hs
    rcases hs.eq_or_lt with rfl | hs'
    · rw [G_atZero, Real.zero_rpow hαpos.ne']
    · exact hα s hs'
  refine ⟨α, hαpos, ?_, hF, fun x s hx hs => ?_, fun σ x hσ hx => ?_⟩
  · -- `α ≤ 1`, from subadditivity of the Lévy exponent at `s = t = 1`
    obtain ⟨b₀, ν, hb₀, hν, hrep⟩ := exponent_hasLevyRep Fam (le_refl (0 : ℝ)) zero_le_one
    have hsub := levyExponent_add_le hb₀ hν (zero_le_one : (0 : ℝ) ≤ 1) (zero_le_one : (0 : ℝ) ≤ 1)
    rw [← hrep 1 zero_le_one, ← hrep (1 + 1) (by norm_num),
      ← ENNReal.ofReal_add (exponent_nonneg Fam 0 1 zero_le_one)
        (exponent_nonneg Fam 0 1 zero_le_one)] at hsub
    have hreal := (ENNReal.ofReal_le_ofReal_iff (by
      have := exponent_nonneg Fam 0 1 (zero_le_one : (0 : ℝ) ≤ 1)
      linarith)).mp hsub
    have h2 : Fam.G 1 (1 + 1) ≤ Fam.G 1 1 + Fam.G 1 1 := hreal
    rw [hF (1 + 1) (by norm_num), hnorm] at h2
    have h2' : (2 : ℝ) ^ α ≤ (2 : ℝ) ^ (1 : ℝ) := by
      rw [Real.rpow_one]
      norm_num at h2 ⊢
      exact h2
    exact (Real.rpow_le_rpow_left_iff one_lt_two).mp h2'
  · rw [G_eq_mul_of_isOneParameter hone hx hs, hF s hs]
  · rw [hSx σ x hσ hx, hF σ hσ.le, mul_comm]

end CascadeCore

end Hemigroup
