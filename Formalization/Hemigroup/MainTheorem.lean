/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the MIT license as described in the file LICENSES/MIT.txt.
Authors: Daniel Fagerström
-/
import Hemigroup.MainAnalysis
import Hemigroup.Uniqueness
import Hemigroup.Instance

/-!
# The main theorem, assembled

Blueprint: `thm:main-characterization` (Theorem 7.3).

Like `SignalingForm.lean`, this file proves nothing: it states the theorem its three halves add up
to, so that the node has one declaration to carry.

## Why the halves stay separate anyway

The node's own annotation argued against a statement of its own, and the argument is good and is
not overturned by this file. The three halves are proved by different means at different cost, and
— the point that matters — **they cross the trust boundary in different places**: `(⇐)` and the
uniqueness clause rest on `A17`, `(⇒)` on `A18`, and neither borrows the other's. That separation
is real, it is what `CIAxiomGuard.lean` checks per half, and a bundle cannot show it: the bundle
necessarily depends on both.

So the per-half `#print axioms` lines are the load-bearing ones and stay exactly as they were.
What the bundle adds is only that the dependency graph stops reporting the article's main theorem
as unproved when all of it is proved — the same gap that `thm:signaling-form` had, where counting
lemmas hid the fact that the theorem node asserts more than its parts.

## The shape of the `(⇐)` conjunct

`thm:main-construction` is a *definition* in Lean — `cascadeFamily` exhibits the structure rather
than asserting a property of it, which is the stronger reading and the reason the node is tagged
with a `def`. A conjunction needs a `Prop`, so `(⇐)` appears here as the existence statement the
definition witnesses. Nothing is weakened: the witness *is* `cascadeFamily`, and the extra clause
pins its operators to be convolution by `F`'s kernels, which is what the blueprint's display says.
-/

namespace Hemigroup

open MeasureTheory Set

namespace SelfDecomposableExponent

/-- **Theorem 2′ (`thm:main-characterization`): the main theorem.**

A family satisfies (A1)–(A8) and (ND) **iff** it is convolution by the kernels of an admissible
exponent, read through a gauge; and the pair (gauge, exponent) is unique up to `χ(1) = 1`.

1. *(⇐, the construction.)* Every admissible `F` gives a cascade family whose operators are
   convolution by `F`'s kernels — `thm:main-construction`, witnessed by `cascadeFamily`.
2. *(⇒, the analysis.)* Every scale-covariant cascade family arises that way, with a gauge `χ`
   conjugating the scaling action into multiplication — `thm:main-analysis`, in its round-trip
   form `main_analysis'`: the conclusion is a `SelfDecomposableExponent` and the identification
   `μ_{x,y} = μ^F_{χ(x),χ(y)}`, i.e. exactly the type conjunct 1 starts from, with `χ 1 = 1` so
   that conjunct 3 applies to it. (The `(b₀, k)` data of `main_analysis` are `F.b₀`, `F.k`.)
3. *(Uniqueness.)* The gauge and the exponent are pinned by the kernels, given `χ(1) = 1` —
   `prop:main-uniqueness`.

The three conjuncts are the three nodes; see the module docstring for why those nodes remain the
place the trust boundary is read off. -/
theorem main_characterization :
    -- (⇐) every admissible exponent gives a cascade family, with the stated kernels
    (∀ (F : SelfDecomposableExponent), (∃ s₀ : ℝ, 0 < s₀ ∧ F.exponent s₀ ≠ 0) →
        ∃ Fam : CascadeFamily, ∀ x y : ℝ, 0 ≤ x → x ≤ y →
          Fam.Φ x y = mconvL1 (F.kernel x y)) ∧
    -- (⇒) every scale-covariant cascade family is of that form: there are a normalised gauge
    -- `χ` and an admissible exponent `F` (nonzero, of the form (7.1)) whose kernels, read
    -- through `χ`, are the family's
    (∀ (S : ℝ → ℝ → ℝ) (Fam : CascadeCore), IsScaleCovariant Fam (Ioi 0) S →
        ∃ χ : ℝ → ℝ, ∃ F : SelfDecomposableExponent,
          χ 0 = 0 ∧ χ 1 = 1 ∧ StrictMonoOn χ (Ici 0) ∧ SurjOn χ (Ici 0) (Ici 0) ∧
          (∀ σ x : ℝ, 0 < σ → 0 ≤ x → χ (S σ x) = σ * χ x) ∧
          (∃ s₀ : ℝ, 0 < s₀ ∧ F.exponent s₀ ≠ 0) ∧
          ∀ x y : ℝ, 0 ≤ x → x ≤ y →
            Fam.repr x y = F.kernel (χ x) (χ y) ∧
            Fam.Φ x y = mconvL1 (F.kernel (χ x) (χ y))) ∧
    -- uniqueness of the gauge and the exponent
    (∀ (F F' : SelfDecomposableExponent) (χ : ℝ → ℝ),
        (∀ u : ℝ, 0 < u → 0 < χ u) →
        (∀ ⦃u v : ℝ⦄, 0 < u → u ≤ v → χ u ≤ χ v) →
        (∀ ε : ℝ, 0 < ε → ∃ u : ℝ, 0 < u ∧ χ u < ε) →
        (∀ u v : ℝ, 0 < u → u ≤ v → F'.kernel (χ u) (χ v) = F.kernel u v) →
        χ 1 = 1 → (∃ s₀ : ℝ, 0 < s₀ ∧ F.exponent s₀ ≠ 0) →
        (∀ u : ℝ, 0 < u → χ u = u) ∧ (∀ t : ℝ, 0 ≤ t → F'.exponent t = F.exponent t)) :=
  ⟨fun F hF => ⟨F.cascadeFamily hF, fun _ _ _ _ => rfl⟩,
   fun _ _ hcov => CascadeCore.main_analysis' _ hcov,
   fun _ _ _ hpos hmono hzero heq hχ1 hne =>
     gauge_and_exponent_unique hpos hmono hzero heq hχ1 hne⟩

end SelfDecomposableExponent

end Hemigroup
