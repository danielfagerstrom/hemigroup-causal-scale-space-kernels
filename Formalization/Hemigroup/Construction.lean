/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.SelfDecomposable
import Hemigroup.Interfaces
import Hemigroup.Injectivity

/-!
# Constructing the kernel family from a self-decomposable exponent

M2 of the formalisation ladder: the constructive direction of `thm:main-characterization`
(Theorem 7.3 ⇐). Given `F` of the blueprint's form (7.1), build the kernels and verify the
axioms they satisfy.

This is the half of the main theorem that certifies *these kernels exist and satisfy the
axioms*, and it is worth having on its own — it does not depend on the analysis direction, which
is a collation of nine earlier nodes and is M6.

## What is established here

* `exists_kernel` — for `0 < a ≤ b` there is a causal probability measure `μ_{a,b}` with
  `μ̂_{a,b}(s) = exp (-(F(bs) - F(as)))`. This is where ledger A17 enters, and it is the only
  place in the file that leaves Lean core.
* `increment_add` / `kernel_conv` — **axiom (A6)**, the hemigroup law, first as
  `g_{a,b} + g_{b,c} = g_{a,c}` and then as `μ_{a,b} ∗ μ_{b,c} = μ_{a,c}`.
* `increment_comp_mul` / `kernel_map_const_mul` — **axiom (A8)**, scale covariance, as
  `g_{σa,σb}(s) = g_{a,b}(σs)` and then as `μ_{σa,σb} = D_σ μ_{a,b}`. The exponent form needs
  no hypothesis on `a`, `b` at all.
* `exponent_ne_zero` — **(ND)**, nondegeneracy, from M1a's vanishing lemma.
* `kernel_unique` — the choice made in `kernel` is immaterial: the transform pins the measure.

The passage from exponents to measures is pure transport, because the Laplace transform turns
convolution into multiplication and dilation into reparametrisation (`laplace_conv`,
`laplace_map_const_mul`) and is injective on causal measures (`laplace_injective`). None of
those three touches the trust boundary.

## What is deliberately left for later

(A1)–(A5) — the `L¹` operator properties — are not here; they are the converse half of
`lem:convolution-representation` and need no new analysis, only bookkeeping about `μ * f`.

(A7) is not here either, but it *is* proved: `Continuity.tendsto_integral_kernel`, resting on
`WeakConvergence.tendsto_integral_of_tendsto_laplace`. It was the step expected to cost a second
interface axiom (ledger A5); it did not.

## The subtlety that forced a refactor

`levyExponentD_increment` produces an increment whose Lévy density is `k(u/b) - k(u/a)`, which
is nonnegative but **not** nonincreasing. So the increment is a Lévy exponent without being a
self-decomposable one, and every lemma that had assumed `AntitoneOn` to get measurability had to
be loosened to an `AEMeasurable` hypothesis. `aemeasurable_of_antitoneOn` is now the single
bridge, applied once per factor and then closed under subtraction.
-/

namespace Hemigroup

open MeasureTheory Set
open scoped ENNReal

variable {a b c s σ : ℝ}

/-- The data of the blueprint's (7.1): a drift `b₀ ≥ 0` and a nonincreasing, nonnegative `k`,
whose exponent `s ↦ b₀ s + ∫ (1 - e^{-st}) k t / t dt` is finite.

Finiteness is carried as a field rather than derived from `∫₀¹ k < ∞` and `∫₁^∞ k(t)/t dt < ∞`
because it is what every result below actually uses; the two are equivalent, and the comparison
is recorded in ledger A17's hypothesis-translation note. -/
structure SelfDecomposableExponent where
  /-- The drift coefficient. -/
  b₀ : ℝ
  /-- The Lévy density, against `dt / t`. -/
  k : ℝ → ℝ
  b₀_nonneg : 0 ≤ b₀
  k_nonneg : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ k t
  k_antitone : AntitoneOn k (Ioi (0 : ℝ))
  /-- A normalisation, not a constraint: `k` is a density against `dt/t` on `(0,∞)` and every
  other field leaves `k 0` free. Fixing it to `0` is what makes the family's lower endpoint
  `x = 0` a special case of the general formula rather than a separate definition — see
  `increment_zero_left`. -/
  k_zero : k 0 = 0
  ne_top : ∀ s, 0 ≤ s → levyExponentD b₀ k s ≠ ⊤

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent)

/-- `F` as a function of `s`: the exponent of (7.1). -/
noncomputable def exponent (s : ℝ) : ℝ≥0∞ := levyExponentD F.b₀ F.k s

/-- The Lévy density of the dilation increment, `u ↦ k(u/b) - k(u/a)`. Nonnegative because `k`
is nonincreasing, but not itself nonincreasing — see the module docstring. -/
noncomputable def incrementDensity (a b : ℝ) : ℝ → ℝ := fun u => F.k (u / b) - F.k (u / a)

/-- The exponent of the kernel `μ_{a,b}`: the blueprint's `g_{a,b} = F(b·) - F(a·)`, in the
representation form supplied by `levyExponentD_increment`. -/
noncomputable def increment (a b : ℝ) (s : ℝ) : ℝ≥0∞ :=
  levyExponentD (F.b₀ * (b - a)) (F.incrementDensity a b) s

variable {F}

lemma aemeasurable_k_comp_div (hc : 0 ≤ c) :
    AEMeasurable (fun u => F.k (u / c)) (volume.restrict (Ioi (0 : ℝ))) := by
  rcases hc.eq_or_lt with rfl | hc'
  · simp only [div_zero]
    exact aemeasurable_const
  · exact aemeasurable_of_antitoneOn (antitoneOn_comp_div F.k_antitone hc')

lemma aemeasurable_incrementDensity (ha : 0 ≤ a) (hb : 0 ≤ b) :
    AEMeasurable (F.incrementDensity a b) (volume.restrict (Ioi (0 : ℝ))) :=
  (aemeasurable_k_comp_div hb).sub (aemeasurable_k_comp_div ha)

/-! ## The increment is an exponent in its own right -/

/-- **The lower endpoint is not a special case.** `g_{0,b} = F(b·)`, on the nose.

With `k 0 = 0` and Lean's `u / 0 = 0`, the increment density `k(u/b) - k(u/a)` at `a = 0` is
just `k(u/b)`, and the drift `b₀(b - a)` is `b₀ b`. That is exactly the dilated representation
of `F(b·)` supplied by `levyJump_comp_mul` — `du/u` being the Haar measure of the dilation
group, a dilation moves the density and nothing else. So `G(x,s) = g_{0,x}(s)`, the object the
whole similarity analysis is built on, needs no separate construction. -/
theorem increment_zero_left (hb : 0 ≤ b) (s : ℝ) : F.increment 0 b s = F.exponent (b * s) := by
  have hdens : F.incrementDensity 0 b = fun u => F.k (u / b) := by
    funext u
    simp only [incrementDensity, div_zero, F.k_zero, sub_zero]
  rcases hb.eq_or_lt with rfl | hb'
  · simp [increment, exponent, levyExponentD, levyJump, hdens, div_zero, F.k_zero]
  · rw [increment, hdens, exponent, levyExponentD, levyExponentD,
      levyJump_comp_mul F.k hb' s, sub_zero, mul_assoc]

/-- The defining identity, straight from M1b: `F(as) + g_{a,b}(s) = F(bs)`.

Stated for `0 ≤ a`, the index range of `def:cascade-family`: at `a = 0` it reads
`0 + g_{0,b} = F(b·)`, which is `increment_zero_left`. -/
theorem exponent_add_increment (ha : 0 ≤ a) (hab : a ≤ b) (hs : 0 ≤ s) :
    F.exponent (a * s) + F.increment a b s = F.exponent (b * s) := by
  rcases ha.eq_or_lt with rfl | ha'
  · rw [zero_mul, increment_zero_left (ha.trans hab) s, exponent, levyExponentD, levyJump]
    simp
  · exact levyExponentD_increment F.b₀_nonneg F.k_antitone F.k_nonneg ha' hab hs

/-- Every increment is finite, because `F` is. -/
theorem increment_ne_top (ha : 0 ≤ a) (hab : a ≤ b) (hs : 0 ≤ s) :
    F.increment a b s ≠ ⊤ := by
  have hb : 0 ≤ b := ha.trans hab
  have h := exponent_add_increment (F := F) ha hab hs
  have : F.exponent (b * s) ≠ ⊤ := F.ne_top _ (mul_nonneg hb hs)
  rw [← h] at this
  exact (ENNReal.add_ne_top.mp this).2

/-- The increment as a *difference* of exponents, in `ℝ`.

`exponent_add_increment` is an identity in `ℝ≥0∞`, where truncated subtraction makes the
difference form false in general. Pushed through `ENNReal.toReal` — legitimate because every
term is finite — it becomes ordinary subtraction, which is the form both the continuity
argument and the uniqueness argument use. -/
theorem increment_toReal (ha : 0 ≤ a) (hab : a ≤ b) (hs : 0 ≤ s) :
    (F.increment a b s).toReal
      = (F.exponent (b * s)).toReal - (F.exponent (a * s)).toReal := by
  have h := exponent_add_increment (F := F) ha hab hs
  have hfin : F.exponent (a * s) ≠ ⊤ := F.ne_top _ (mul_nonneg ha hs)
  rw [← h, ENNReal.toReal_add hfin (increment_ne_top (F := F) ha hab hs)]
  ring

/-! ## Axiom (A6): the hemigroup law -/

/-- **Axiom (A6)**, at the level of exponents: increments compose along a cascade,
`g_{a,b} + g_{b,c} = g_{a,c}`.

This is the identity that makes the family a *hemigroup* rather than a semigroup — it is
additivity in the pair `(a,b)`, with no requirement that the increment depend only on `b - a`.
Lifting it to `μ_{a,b} ∗ μ_{b,c} = μ_{a,c}` needs Laplace injectivity; see the module
docstring. -/
theorem increment_add (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hs : 0 ≤ s) :
    F.increment a b s + F.increment b c s = F.increment a c s := by
  have hb : 0 ≤ b := ha.trans hab
  have hac : a ≤ c := hab.trans hbc
  have h₁ := exponent_add_increment (F := F) ha hab hs
  have h₂ := exponent_add_increment (F := F) hb hbc hs
  have h₃ := exponent_add_increment (F := F) ha hac hs
  -- `F(as) + (g_{a,b} + g_{b,c}) = F(cs) = F(as) + g_{a,c}`, then cancel `F(as)`.
  have hcancel : F.exponent (a * s) + (F.increment a b s + F.increment b c s)
      = F.exponent (a * s) + F.increment a c s := by
    rw [h₃, ← h₂, ← h₁, add_assoc]
  exact (ENNReal.add_right_inj (F.ne_top _ (by positivity))).mp hcancel

/-! ## Axiom (A8): scale covariance -/

/-- **Axiom (A8)**: dilating the pair `(a,b)` dilates the argument,
`g_{σa,σb}(s) = g_{a,b}(σs)`.

Pure algebra — no hypothesis on `a` or `b`, and no finiteness. Both sides are the same
`levyExponentD`, because `levyJump_comp_mul` moves a dilation onto the density and
`u ↦ (u/σ)/b = u/(σb)` matches the two densities up. -/
theorem increment_comp_mul (hσ : 0 < σ) (a b s : ℝ) :
    F.increment (σ * a) (σ * b) s = F.increment a b (σ * s) := by
  rw [increment, increment, levyExponentD_comp_mul _ _ hσ]
  congr 1
  · ring
  · funext u
    simp only [incrementDensity, div_div]

/-! ## (ND): nondegeneracy -/

/-- **(ND)**: if `F` does not vanish identically it vanishes nowhere on `(0,∞)`.

This is M1a's vanishing lemma read contrapositively, and it is what the blueprint's proof of
Theorem 7.3 (⇐) uses to discharge (ND) — there phrased as "`F` is strictly increasing". -/
theorem exponent_ne_zero (h : ∃ s₁, 0 ≤ s₁ ∧ F.exponent s₁ ≠ 0) (hs : 0 < s) :
    F.exponent s ≠ 0 := by
  obtain ⟨s₁, hs₁, hne⟩ := h
  intro hzero
  exact hne (levyExponentD_eq_zero_of_eq_zero F.b₀_nonneg
    (aemeasurable_of_antitoneOn F.k_antitone) hs hzero s₁ hs₁)

/-! ## The kernels -/

/-- **The kernel measures exist.** For `0 ≤ a ≤ b` there is a causal probability measure
`μ_{a,b}` on `ℝ` whose Laplace transform is `exp (-g_{a,b}(s))`.

This is `thm:main-characterization` (⇐)'s construction step, and the single point in the
development where the trust boundary is crossed: it is ledger **A17**, the existence half of the
subordinator correspondence. Everything else in this file is Lean core.

The blueprint reaches the same measure through Bernstein–Widder, having first made `e^{-g}`
completely monotone. Here `g_{a,b}` arrives from `levyExponentD_increment` with its Lévy triple
attached, so what is needed is a construction from a triple, which is a strictly smaller
interface — see `Interfaces.lean`. -/
theorem exists_kernel (ha : 0 ≤ a) (hab : a ≤ b) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ IsCausal μ ∧
      ∀ s, 0 ≤ s → laplace μ s = Real.exp (-(F.increment a b s).toReal) := by
  have hb : 0 ≤ b := ha.trans hab
  have hdens := aemeasurable_incrementDensity (F := F) ha hb
  -- Transport the increment to the measure-based `levyExponent` of `Levy.lean`.
  have hbridge : ∀ s, 0 ≤ s → F.increment a b s
      = levyExponent (F.b₀ * (b - a)) (levyMeasureOfDensity (F.incrementDensity a b)) s :=
    fun s hs => levyExponentD_eq_levyExponent _ hdens hs
  obtain ⟨μ, hprob, hcausal, htrans⟩ :=
    exists_isProbabilityMeasure_laplace_eq_exp_neg_levyExponent
      (b₀ := F.b₀ * (b - a)) (ν := levyMeasureOfDensity (F.incrementDensity a b))
      (mul_nonneg F.b₀_nonneg (by linarith))
      (isCausal_levyMeasureOfDensity _)
      (fun s hs => by rw [← hbridge s hs]; exact increment_ne_top (F := F) ha hab hs)
  exact ⟨μ, hprob, hcausal, fun s hs => by rw [htrans s hs, hbridge s hs]⟩

/-! ## The kernel family, and the axioms at the level of measures

`exists_kernel` only asserts existence, and a convolution identity has to name its measures. So
fix a choice. Injectivity of the Laplace transform (`Injectivity.lean`) makes the choice
immaterial: any measure with the right transform *is* this one, by `kernel_unique`.
-/

open Classical in
/-- The kernel `μ_{a,b}`, chosen once and for all. Junk (the zero measure) outside `0 ≤ a ≤ b`,
which is the index range of `def:cascade-family` and the range every result below
hypothesises. -/
noncomputable def kernel (F : SelfDecomposableExponent) (a b : ℝ) : Measure ℝ :=
  if h : 0 ≤ a ∧ a ≤ b then (exists_kernel (F := F) h.1 h.2).choose else 0

lemma kernel_spec (ha : 0 ≤ a) (hab : a ≤ b) :
    IsProbabilityMeasure (F.kernel a b) ∧ IsCausal (F.kernel a b) ∧
      ∀ s, 0 ≤ s → laplace (F.kernel a b) s = Real.exp (-(F.increment a b s).toReal) := by
  rw [show F.kernel a b = (exists_kernel (F := F) ha hab).choose from dif_pos ⟨ha, hab⟩]
  exact (exists_kernel (F := F) ha hab).choose_spec

lemma isProbabilityMeasure_kernel (ha : 0 ≤ a) (hab : a ≤ b) :
    IsProbabilityMeasure (F.kernel a b) := (kernel_spec ha hab).1

lemma isCausal_kernel (ha : 0 ≤ a) (hab : a ≤ b) : IsCausal (F.kernel a b) :=
  (kernel_spec ha hab).2.1

lemma laplace_kernel (ha : 0 ≤ a) (hab : a ≤ b) (hs : 0 ≤ s) :
    laplace (F.kernel a b) s = Real.exp (-(F.increment a b s).toReal) :=
  (kernel_spec ha hab).2.2 s hs

/-- The choice made in `kernel` is immaterial: the transform pins the measure down. -/
theorem kernel_unique {μ : Measure ℝ} [IsFiniteMeasure μ] (hμ : IsCausal μ)
    (ha : 0 ≤ a) (hab : a ≤ b)
    (ht : ∀ s, 0 ≤ s → laplace μ s = Real.exp (-(F.increment a b s).toReal)) :
    μ = F.kernel a b := by
  haveI := isProbabilityMeasure_kernel (F := F) ha hab
  exact laplace_injective hμ (isCausal_kernel ha hab)
    fun s hs => by rw [ht s hs, laplace_kernel ha hab hs]

/-- **Axiom (A6) for the measures**: the kernels compose along a cascade under convolution.

This is `increment_add` transported across the Laplace transform, which turns convolution into
multiplication (`laplace_conv`) and is injective on causal measures (`laplace_injective`).
Neither step touches the trust boundary. -/
theorem kernel_conv (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    F.kernel a b ∗ F.kernel b c = F.kernel a c := by
  have hb : 0 ≤ b := ha.trans hab
  haveI := isProbabilityMeasure_kernel (F := F) ha hab
  haveI := isProbabilityMeasure_kernel (F := F) hb hbc
  haveI := isProbabilityMeasure_kernel (F := F) ha (hab.trans hbc)
  refine laplace_injective ((isCausal_kernel (F := F) ha hab).conv
    (isCausal_kernel (F := F) hb hbc)) (isCausal_kernel (F := F) ha (hab.trans hbc))
    fun s hs => ?_
  rw [laplace_conv, laplace_kernel ha hab hs, laplace_kernel hb hbc hs,
    laplace_kernel ha (hab.trans hbc) hs, ← Real.exp_add, ← neg_add,
    ← ENNReal.toReal_add (increment_ne_top (F := F) ha hab hs)
      (increment_ne_top (F := F) hb hbc hs), increment_add ha hab hbc hs]

/-- **Axiom (A8) for the measures**: dilating the pair dilates the kernel,
`μ_{σa,σb} = D_σ μ_{a,b}`.

`increment_comp_mul` transported the same way. On the transform side dilation is a
reparametrisation (`laplace_map_const_mul`), so this is again pure transport. -/
theorem kernel_map_const_mul (hσ : 0 < σ) (ha : 0 ≤ a) (hab : a ≤ b) :
    F.kernel (σ * a) (σ * b) = (F.kernel a b).map (fun t => σ * t) := by
  have ha' : 0 ≤ σ * a := mul_nonneg hσ.le ha
  have hab' : σ * a ≤ σ * b := by nlinarith
  haveI := isProbabilityMeasure_kernel (F := F) ha hab
  haveI := isProbabilityMeasure_kernel (F := F) ha' hab'
  haveI : IsProbabilityMeasure ((F.kernel a b).map (fun t => σ * t)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  refine laplace_injective (isCausal_kernel (F := F) ha' hab')
    ((isCausal_kernel (F := F) ha hab).map_const_mul hσ) fun s hs => ?_
  rw [laplace_map_const_mul _ hσ, laplace_kernel ha hab (by positivity),
    laplace_kernel ha' hab' hs, increment_comp_mul hσ]

end SelfDecomposableExponent

end Hemigroup
