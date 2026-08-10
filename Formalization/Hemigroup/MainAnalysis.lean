/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.Gauge

/-!
# `thm:main-analysis` up to its last step

Blueprint: `blueprint/src/parts/07-characterization.tex`, Theorem 7.5.

The analysis direction is a collation of chapters 4 to 6 followed by one appeal to
`lem:selfdecomposable-derivative`. Everything before that appeal is proved here, in one
statement, and it is worth separating for a reason that is not stylistic: the appeal is the only
place in the whole article where the analysis direction crosses the trust boundary, and it is
better to have the exact hypothesis it consumes written down as a Lean statement than to have it
buried inside a proof nobody can run.

## What `similarity_form` gives

For a family satisfying (A1)–(A8) and (ND): a gauge `χ`, an exponent `F = G(1,\cdot)`, and

* the convolution representation, `Φ_{x,y} f = μ_{x,y} * f`;
* the transform in similarity form,
  `\hat μ_{x,y}(s) = \exp[-(F(χ(y)s) - F(χ(x)s))]`;
* **every dilation increment of `F` is a Lévy exponent** — `F(b\,\cdot) - F(a\,\cdot) \in \LE`
  for all `0 < a \le b`;
* `F \not\equiv 0`.

The third clause is where the surjectivity of `χ` earns its place: an increment of `F` between
*arbitrary* `0 < a ≤ b` is an increment of `G` between the scales `χ^{-1}(a)` and `χ^{-1}(b)`,
which is what `thm:increments-bernstein` speaks about. Without surjectivity the statement would
only cover the dilation factors the family happens to realise.

## What is left

Exactly `lem:selfdecomposable-derivative`, in the direction (1) ⇒ (3): a `\LE` function all of
whose dilation increments are again in `\LE` has a Lévy measure with a *nonincreasing* density
`k(t)/t`. That is self-decomposability theory, not a statement about hemigroup families, and the
blueprint marks it not intended to be formalised: it runs through `prop:bernstein-toolbox`(4)
and the uniqueness of the Lévy–Khintchine triple, ledger A4 and A3. Its converse,
(3) ⇒ (1), *is* proved here, as `levyExponentD_increment`, which is why
`thm:main-construction` stays off both ledger entries.

So: the last step of the analysis direction needs a second entry in
`blueprint/trust-boundary.txt`, and that is a review decision rather than a piece of work. The
target type is stated in `Formalization/Skeleton/` and this file supplies its entire hypothesis.
-/

namespace Hemigroup

open MeasureTheory Set

namespace CascadeCore

variable {Fam : CascadeCore} {S : ℝ → ℝ → ℝ}

/-- **Chapters 4 to 6, collated.** The representation, the similarity form, and the fact that
every dilation increment of the exponent is a Lévy exponent.

This is `thm:main-analysis` with its last step — the identification of `F` as an exponent of the
form `(7.1)` — removed, and it is the exact hypothesis that step consumes. -/
theorem similarity_form (Fam : CascadeCore) (hcov : IsScaleCovariant Fam (Ioi 0) S) :
    ∃ χ : ℝ → ℝ, χ 0 = 0 ∧ StrictMonoOn χ (Ici 0) ∧ SurjOn χ (Ici 0) (Ici 0) ∧
      (∀ σ x : ℝ, 0 < σ → 0 ≤ x → χ (S σ x) = σ * χ x) ∧
      (∀ x y : ℝ, 0 ≤ x → x ≤ y → Fam.Φ x y = mconvL1 (Fam.repr x y)) ∧
      (∀ x y s : ℝ, 0 ≤ x → x ≤ y → 0 ≤ s →
        laplace (Fam.repr x y) s
          = Real.exp (-(Fam.G 1 (χ y * s) - Fam.G 1 (χ x * s)))) ∧
      (∀ a b : ℝ, 0 < a → a ≤ b → ∃ b₀ : ℝ, ∃ ν : Measure ℝ, 0 ≤ b₀ ∧ IsCausal ν ∧
        ∀ s : ℝ, 0 ≤ s →
          ENNReal.ofReal (Fam.G 1 (b * s) - Fam.G 1 (a * s)) = levyExponent b₀ ν s) ∧
      (∀ s : ℝ, 0 < s → Fam.G 1 s ≠ 0) := by
  refine ⟨gauge S, gauge_zero S, strictMonoOn_gauge hcov, surjOn_gauge hcov,
    fun _ _ hσ hx => gauge_S hcov hσ hx, fun _ _ hx hxy => Phi_eq_mconvL1_repr hx hxy, ?_, ?_, ?_⟩
  · -- The transform, read through the gauge.
    intro x y s hx hxy hs
    rw [laplace_repr_eq Fam x y hs, ← G_eq_gauge hcov (hx.trans hxy) s, ← G_eq_gauge hcov hx s,
      ← exponent_eq_G_sub hx hxy hs]
  · -- Every dilation increment of `F` is an increment of `G`, by surjectivity of the gauge.
    intro a b ha hab
    obtain ⟨x, hx, hxa⟩ := surjOn_gauge hcov (mem_Ici.mpr ha.le)
    obtain ⟨y, hy, hyb⟩ := surjOn_gauge hcov (mem_Ici.mpr (ha.le.trans hab))
    have hxy : x ≤ y := by
      by_contra hcon
      exact absurd (hxa ▸ hyb ▸ strictMonoOn_gauge hcov hy hx (not_le.mp hcon)) (not_lt.mpr hab)
    obtain ⟨b₀, ν, hb₀, hν, hrep⟩ := exponent_hasLevyRep Fam (mem_Ici.mp hx) hxy
    refine ⟨b₀, ν, hb₀, hν, fun s hs => ?_⟩
    rw [← hrep s hs, ← hxa, ← hyb, ← G_eq_gauge hcov (mem_Ici.mp hy) s,
      ← G_eq_gauge hcov (mem_Ici.mp hx) s, ← exponent_eq_G_sub (mem_Ici.mp hx) hxy hs]
  · -- `F \not\equiv 0`, which is (ND).
    exact fun _ hs => (exponent_pos Fam le_rfl one_pos hs).ne'

end CascadeCore

end Hemigroup
