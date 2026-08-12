/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.MemoryFractional
import Hemigroup.SymbolUniqueness

/-!
# Theorem 4′: the signaling form

Blueprint: `thm:signaling-form` (Theorem 11.6), the formulation the article exists for.

Everything here is assembly. The three clauses are proved in the files that develop them —
`InversionOperator.lean`, `MemoryFractional.lean`, `SymbolUniqueness.lean` — and this file states
the theorem they add up to, so that the node has one declaration to carry and the dependency graph
says what is true rather than what is nearly true.

That last point is the reason the file exists. The chapter's *lemmas* were all `\leanok` while
`thm:signaling-form` was not, and the gap was invisible in a summary that counted lemmas: clause
(2) asserts four things and only one of them, the Mellin form, had been proved. The theorem node
exists precisely because it asserts more than its lemmas do.

## What each conjunct is

| conjunct | proved in | by |
|---|---|---|
| (1) eigenfunctions | `InversionOperator` | `inversionOperator_profile` |
| (2a) causality in `t` | `MemoryFractional` | `delayedField_eq_zero` |
| (2b) `u(·,x) → f` in `X₀` | `MemoryFractional` | `tendsto_Phi_zero`, i.e. (A7) with (A6) |
| (2c) Laplace form | both | `laplaceFun_delayedField`, `inversionOperator_const_mul_profile` |
| (2d) Mellin form | `MemoryFractional` | `mellin_signaling_form` |
| (3) uniqueness | `SymbolUniqueness` | `eventuallyEq_inversionSymbol_of_realisesAction` |

`f` is presented as the primitive of a causal `g ∈ L¹`, **and separately as integrable** — both
halves of `f ∈ 𝒟`, and the second is not implied by the first. A primitive of an `L¹` function
tends to `∫₀^∞ g`, so it lies in `L¹` only when that limit is `0`; `𝒟` asks for `f ∈ X₀` and
`f' ∈ X₀` and thereby imposes it. Assembling the theorem is what made that visible — the clause
had been carried along as though "primitive of `g`" were the whole of `f ∈ 𝒟`.

See `MemoryFractional.lean` for why only two other features of `𝒟` turn out to be load-bearing,
and for why `∂_t u` has to be read in `X₀` rather than pointwise.
-/

namespace Hemigroup

open MeasureTheory Set Filter

open scoped Topology

namespace SelfDecomposableExponent

variable (F : SelfDecomposableExponent)

/-- **Theorem 4′ (`thm:signaling-form`): the signaling form.**

Assume (H) and work in the canonical gauge. Let `f` be the primitive of a causal `g ∈ L¹` — that
is, `f ∈ 𝒟` — and let `u(t,x) = E[f(t - xT₁)]` be the field, read through `delayedField`.

1. *(Eigenfunctions.)* Every profile dilate `H(s·)` is an eigenfunction of `A` with eigenvalue `s`.
2. *(The field solves the signaling problem.)* `u` is causal in `t`; `Φ_{0,x}f → f` in `X₀` as
   `x ↓ 0`; the Laplace profile is `û(s,x) = f̂(s)H(sx)` and satisfies `A[û(s,·)] = s·û(s,·)`; and
   the Mellin form `∂̃_t u(t,·)(z) = B(1-z)·ũ(t,·)(z-1)` holds on the strip.
3. *(Uniqueness.)* Any symbol whose operator has property (1) agrees with `B` as a meromorphic
   function on the strip. -/
theorem signaling_form (hH : F.StandingHypothesis) (hF : ∃ s₀, 0 < s₀ ∧ F.exponent s₀ ≠ 0)
    {c : ℝ} (hc : 0 < c) (hc' : c + 1 < F.zStar) {g f : ℝ → ℝ} (hgm : Measurable g)
    (hg : Integrable g) (hgc : ∀ r : ℝ, r < 0 → g r = 0) (hfm : Measurable f)
    (hfi : Integrable f) (hf : ∀ r : ℝ, f r = ∫ ρ in Ioc (0 : ℝ) r, g ρ) :
    -- (1) the profiles are eigenfunctions
    (∀ s : ℝ, 0 < s → ∀ x : ℝ, 0 < x →
        F.inversionOperator c (fun u : ℝ => (F.profile (s * u) : ℂ)) x
          = (s : ℂ) * (F.profile (s * x) : ℂ)) ∧
    -- (2a) the field is causal in time
    (∀ x : ℝ, 0 < x → ∀ t : ℝ, t < 0 → F.delayedField f t x = 0) ∧
    -- (2b) the boundary value is attained in `X₀`
    (∀ q : X, Tendsto (fun x : ℝ => (F.cascadeFamily hF).Φ 0 x q) (𝓝[≥] (0 : ℝ)) (𝓝 q)) ∧
    -- (2c) the Laplace profile of the field, and the Laplace form of the equation
    (∀ s : ℝ, 0 < s → ∀ x : ℝ, 0 < x →
        laplaceFun (fun t => F.delayedField f t x) s = F.profile (s * x) * laplaceFun f s ∧
        F.inversionOperator c
            (fun u : ℝ => ((laplaceFun f s : ℝ) : ℂ) * (F.profile (s * u) : ℂ)) x
          = (s : ℂ) * (((laplaceFun f s : ℝ) : ℂ) * (F.profile (s * x) : ℂ))) ∧
    -- (2d) the Mellin form
    (∀ z : ℂ, 1 < z.re → z.re < F.zStar → ∀ t : ℝ, 0 < t →
        mellin (fun s => (F.profile s : ℂ)) (z - 1) ≠ 0 →
        mellin (fun x : ℝ => (F.delayedField g t x : ℂ)) z
          = F.inversionSymbol (z - 1) * mellin (fun x : ℝ => (F.delayedField f t x : ℂ)) (z - 1))
      ∧
    -- (3) uniqueness of the symbol within the covariant Mellin class
    (∀ s : ℝ, 0 < s → ∀ B : ℂ → ℂ,
        (∀ c' : ℝ, 0 < c' → c' + 1 < F.zStar →
          F.RealisesAction c' B (fun u : ℝ => (F.profile (s * u) : ℂ))
            (fun x : ℝ => (s : ℂ) * (x : ℂ) * (F.profile (s * x) : ℂ))) →
        ∀ z ∈ verticalStrip 0 (F.zStar - 1), F.inversionSymbol =ᶠ[𝓝[≠] z] B) :=
  ⟨fun s hs x hx => F.inversionOperator_profile hH hc hc' hs hx,
   fun x hx t ht => F.delayedField_eq_zero hH (fun r hr => by rw [hf r,
      Ioc_eq_empty (not_lt.mpr hr.le), Measure.restrict_empty, integral_zero_measure]) hx ht,
   F.tendsto_Phi_zero hF,
   fun s hs x hx =>
     ⟨F.laplaceFun_delayedField hH hfm hfi (fun r hr => by
        rw [hf r, Ioc_eq_empty (not_lt.mpr hr.le), Measure.restrict_empty,
          integral_zero_measure]) hs.le hx,
      F.inversionOperator_const_mul_profile hH hc hc' hs _ hx⟩,
   fun z hz hz' t ht hne => F.mellin_signaling_form hH hz hz' hgm hg hgc hfm hf ht hne,
   fun s hs B hB z hz => F.eventuallyEq_inversionSymbol_of_realisesAction hH hs hB hz⟩

end SelfDecomposableExponent

end Hemigroup
