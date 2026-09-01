/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the MIT license as described in the file LICENSES/MIT.txt.
Authors: Daniel Fagerström
-/
import Hemigroup.MemoryFractional
import Hemigroup.SymbolUniqueness

/-!
# Theorem 4′: the signaling form

Blueprint: `thm:signaling-form` (Theorem 11.6), the formulation the article exists for.

Everything here is assembly, with one exception. The three clauses are proved in the files that
develop them — `InversionOperator.lean`, `MemoryFractional.lean`, `SymbolUniqueness.lean` — and
this file states the theorem they add up to, so that the node has one declaration to carry and
the dependency graph says what is true rather than what is nearly true. The exception is
`tendsto_laplaceFun_delayedField`, the boundary value `û(s,0+) = f̂(s)`, which needs the
transform's continuity (`TransformContinuity.lean`) and so is proved here rather than in
`MemoryFractional.lean`, which does not import it.

That last point is the reason the file exists. The chapter's *lemmas* were all `\leanok` while
`thm:signaling-form` was not, and the gap was invisible in a summary that counted lemmas: clause
(2) asserts four things and only one of them, the Mellin form, had been proved. The theorem node
exists precisely because it asserts more than its lemmas do.

## What each conjunct is

| conjunct | by |
|---|---|
| (1) domain + eigenfunctions | `realisesSymbolAction_profile`, `inversionOperator_profile` |
| (2a) causality in `t` | `delayedField_eq_zero` |
| (2b) `u(·,x) → f` in `X₀` | `tendsto_Phi_zero`, i.e. (A7) with (A6) |
| (2b) `u(·,x) = Φ_{0,x}f` | `coeFn_Phi_zero` |
| (2c) Laplace form | `laplaceFun_delayedField`, `inversionOperator_const_mul_profile` |
| (2c) `û(s,0+) = f̂(s)` | `tendsto_laplaceFun_delayedField` |
| (2d) `∂_t u` in `X₀` | `delayedField_eq_setIntegral'` |
| (2d) Mellin form, convergence | `mellin_signaling_form`, `mellinConvergent_delayedField_pair` |
| (3) uniqueness | `eventuallyEq_inversionSymbol_of_realisesAction` |

(1) is in `InversionOperator.lean`, (3) in `SymbolUniqueness.lean`, (2) in `MemoryFractional.lean`
except the boundary value, which is below.

The fidelity review (`PLAN-fidelity-review.md`, P2) added five conjuncts, none of them new
mathematics: the *domain* half of (1) — `H(s·)` lies in the domain of `def:inversion-operator`,
which for a total `A` is `RealisesSymbolAction`, finding R9; the identification of the field
with `Φ_{0,x}f`, so that (2b), stated for every `q : X`, is visibly about `f`; the boundary value
`û(s,0+) = f̂(s)`, finding R11; the reading of `∂_t u` in (2d) as the `X₀`-derivative — the field
of `f` is the primitive of the field of `f'` — as a conjunct rather than a comment; and the
convergence of both Mellin transforms in (2d), so that the identity is between transforms that
exist rather than between Mathlib's junk value `0` on both sides.

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

/-- **`thm:signaling-form`(2), the boundary value of the Laplace profile**: `û(s,0+) = f̂(s)`.
`û(s,x) = H(sx)f̂(s)` and `H` is continuous on `[0,∞)` with `H(0) = 1`. -/
theorem tendsto_laplaceFun_delayedField (hH : F.StandingHypothesis) {f : ℝ → ℝ}
    (hfm : Measurable f) (hf : Integrable f) (hfc : ∀ r : ℝ, r < 0 → f r = 0) {s : ℝ}
    (hs : 0 < s) :
    Tendsto (fun x : ℝ => laplaceFun (fun t => F.delayedField f t x) s) (𝓝[>] (0 : ℝ))
      (𝓝 (laplaceFun f s)) := by
  have hprof : Tendsto (fun x : ℝ => F.profile (s * x)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hcont : ContinuousWithinAt (fun u => laplace F.lawT₁ u) (Ici 0) 0 :=
      continuousOn_laplace F.isCausal_lawT₁ 0 (mem_Ici.mpr le_rfl)
    have hmap : Tendsto (fun x : ℝ => s * x) (𝓝[>] (0 : ℝ)) (𝓝[Ici 0] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have := ((continuous_const (y := s)).mul continuous_id).tendsto (0 : ℝ)
        simp only [Pi.mul_apply, id, mul_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      · exact Filter.Eventually.mono self_mem_nhdsWithin fun x hx =>
          mem_Ici.mpr (mul_nonneg hs.le (mem_Ioi.mp hx).le)
    have := hcont.tendsto.comp hmap
    rwa [laplace_zero_prob] at this
  have heq : (fun x : ℝ => laplaceFun (fun t => F.delayedField f t x) s)
      =ᶠ[𝓝[>] (0 : ℝ)] fun x => F.profile (s * x) * laplaceFun f s := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact F.laplaceFun_delayedField hH hfm hf hfc hs.le (mem_Ioi.mp hx)
  refine (Tendsto.congr' heq.symm ?_)
  simpa using hprof.mul_const (laplaceFun f s)


/-- **Theorem 4′ (`thm:signaling-form`): the signaling form.**

Assume (H) and work in the canonical gauge. Let `f` be the primitive of a causal `g ∈ L¹` — that
is, `f ∈ 𝒟` — and let `u(t,x) = E[f(t - xT₁)]` be the field, read through `delayedField`.

1. *(Eigenfunctions.)* Every profile dilate `H(s·)` lies in the domain of `A` (its symbol
   action is realised, by `s x H(sx)`) and is an eigenfunction of `A` with eigenvalue `s`.
2. *(The field solves the signaling problem.)* `u` is causal in `t`; `Φ_{0,x}q → q` in `X₀` as
   `x ↓ 0` for every `q`, and `u(·,x)` is `Φ_{0,x}f`; the Laplace profile is `û(s,x) = f̂(s)H(sx)`,
   satisfies `A[û(s,·)] = s·û(s,·)`, and has boundary value `û(s,0+) = f̂(s)`; `∂_t u` is the
   `X₀`-derivative (`u(·,x)` is the primitive of the field of `f'`); and the Mellin form
   `∂̃_t u(t,·)(z) = B(1-z)·ũ(t,·)(z-1)` holds on the strip off the zeros of `H̃(z-1)`, both
   transforms converging there.
3. *(Uniqueness.)* Any symbol whose operator has property (1) at every height agrees with `B` as
   a meromorphic function on the strip. -/
theorem signaling_form (hH : F.StandingHypothesis) (hF : ∃ s₀, 0 < s₀ ∧ F.exponent s₀ ≠ 0)
    {c : ℝ} (hc : 0 < c) (hc' : ENNReal.ofReal (c + 1) < F.zStar) {g f : ℝ → ℝ} (hgm : Measurable g)
    (hg : Integrable g) (hgc : ∀ r : ℝ, r < 0 → g r = 0) (hfm : Measurable f)
    (hfi : Integrable f) (hf : ∀ r : ℝ, f r = ∫ ρ in Ioc (0 : ℝ) r, g ρ) :
    -- (1) the profiles lie in the domain of `A` and are eigenfunctions
    (∀ s : ℝ, 0 < s →
        F.RealisesSymbolAction c (fun u : ℝ => (F.profile (s * u) : ℂ))
          (fun x : ℝ => (s : ℂ) * (x : ℂ) * (F.profile (s * x) : ℂ)) ∧
        ∀ x : ℝ, 0 < x →
          F.inversionOperator c (fun u : ℝ => (F.profile (s * u) : ℂ)) x
            = (s : ℂ) * (F.profile (s * x) : ℂ)) ∧
    -- (2a) the field is causal in time
    (∀ x : ℝ, 0 < x → ∀ t : ℝ, t < 0 → F.delayedField f t x = 0) ∧
    -- (2b) the boundary value is attained in `X₀`, and the field is `Φ_{0,x}f`
    (∀ q : X, Tendsto (fun x : ℝ => (F.cascadeFamily hF).Φ 0 x q) (𝓝[≥] (0 : ℝ)) (𝓝 q)) ∧
    (∀ x : ℝ, 0 < x →
        ⇑((F.cascadeFamily hF).Φ 0 x (hfi.toL1 f)) =ᵐ[volume] fun t => F.delayedField f t x) ∧
    -- (2c) the Laplace profile of the field, the Laplace form of the equation, and the
    -- boundary value `û(s,0+) = f̂(s)`
    (∀ s : ℝ, 0 < s →
        (∀ x : ℝ, 0 < x →
          laplaceFun (fun t => F.delayedField f t x) s = F.profile (s * x) * laplaceFun f s ∧
          F.inversionOperator c
              (fun u : ℝ => ((laplaceFun f s : ℝ) : ℂ) * (F.profile (s * u) : ℂ)) x
            = (s : ℂ) * (((laplaceFun f s : ℝ) : ℂ) * (F.profile (s * x) : ℂ))) ∧
        Tendsto (fun x : ℝ => laplaceFun (fun t => F.delayedField f t x) s) (𝓝[>] (0 : ℝ))
          (𝓝 (laplaceFun f s))) ∧
    -- (2d) `∂_t u` in `X₀`: the field of `f` is the primitive of the field of `f' = g`
    (∀ x : ℝ, 0 < x → ∀ t : ℝ,
        F.delayedField f t x = ∫ ρ in Ioc (0 : ℝ) t, F.delayedField g ρ x) ∧
    -- (2d) the Mellin form, with both transforms convergent
    (∀ z : ℂ, 1 < z.re → ENNReal.ofReal z.re < F.zStar → ∀ t : ℝ, 0 < t →
        MellinConvergent (fun x : ℝ => (F.delayedField g t x : ℂ)) z ∧
        MellinConvergent (fun x : ℝ => (F.delayedField f t x : ℂ)) (z - 1) ∧
        (mellin (fun s => (F.profile s : ℂ)) (z - 1) ≠ 0 →
          mellin (fun x : ℝ => (F.delayedField g t x : ℂ)) z
            = F.inversionSymbol (z - 1)
                * mellin (fun x : ℝ => (F.delayedField f t x : ℂ)) (z - 1)))
      ∧
    -- (3) uniqueness of the symbol within the covariant Mellin class
    (∀ s : ℝ, 0 < s → ∀ B : ℂ → ℂ,
        (∀ c' : ℝ, 0 < c' → ENNReal.ofReal (c' + 1) < F.zStar →
          F.RealisesAction c' B (fun u : ℝ => (F.profile (s * u) : ℂ))
            (fun x : ℝ => (s : ℂ) * (x : ℂ) * (F.profile (s * x) : ℂ))) →
        ∀ z ∈ verticalStrip 0 (F.zStar - 1), F.inversionSymbol =ᶠ[𝓝[≠] z] B) := by
  have hfc : ∀ r : ℝ, r < 0 → f r = 0 := fun r hr => by
    rw [hf r, Ioc_eq_empty (not_lt.mpr hr.le), Measure.restrict_empty, integral_zero_measure]
  exact
  ⟨fun s hs => ⟨F.realisesSymbolAction_profile hH hc hc' hs,
     fun x hx => F.inversionOperator_profile hH hc hc' hs hx⟩,
   fun x hx t ht => F.delayedField_eq_zero hH hfc hx ht,
   F.tendsto_Phi_zero hF,
   fun x hx => F.coeFn_Phi_zero hF hx hfm hfi,
   fun s hs =>
     ⟨fun x hx =>
       ⟨F.laplaceFun_delayedField hH hfm hfi hfc hs.le hx,
        F.inversionOperator_const_mul_profile hH hc hc' hs _ hx⟩,
      F.tendsto_laplaceFun_delayedField hH hfm hfi hfc hs⟩,
   fun x hx t => F.delayedField_eq_setIntegral' hgm hg hgc hf hH hx t,
   fun z hz hz' t ht =>
     ⟨(F.mellinConvergent_delayedField_pair hH hz hz' hgm hg hgc hfm hf ht).1,
      (F.mellinConvergent_delayedField_pair hH hz hz' hgm hg hgc hfm hf ht).2,
      fun hne => F.mellin_signaling_form hH hz hz' hgm hg hgc hfm hf ht hne⟩,
   fun s hs B hB z hz => F.eventuallyEq_inversionSymbol_of_realisesAction hH hs hB hz⟩

end SelfDecomposableExponent

end Hemigroup
