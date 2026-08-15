/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.Gauge
import Hemigroup.Interfaces

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

## The last step

`main_analysis` closes the gap with one appeal to ledger **A18**
(`exists_antitone_density_of_dilation_increments`): a Lévy exponent whose dilation increments are
all Lévy exponents has a nonincreasing density `k(t)/t`. That is the blueprint's
`lem:selfdecomposable-derivative` in the direction (1) ⇒ (3), and it is the second and last entry
on the trust boundary.

The split is deliberate, and is what makes the article's own claim checkable. `similarity_form`
reduces to Lean core; `main_analysis` picks up A18 and nothing else; `thm:main-construction` and
`prop:main-uniqueness` pick up A17 and nothing else. So "the analysis direction crosses the
boundary where the constructive one does not" is a fact `#print axioms` reports, not a claim the
prose makes.

## The round trip

`main_analysis'` repackages `main_analysis` so that the analysis direction concludes in
*exactly* the type the constructive direction starts from: a `SelfDecomposableExponent` `F`, a
normalised gauge (`χ 0 = 0`, `χ 1 = 1`, strictly increasing and onto `[0,∞)`), and the
identification `Fam.repr x y = F.kernel (χ x) (χ y)`. That is the article's sentence — "there
exist `χ` and `F` of the form (7.1), `F ≢ 0`, with `Φ_{x,y} f = μ_{x,y} ∗ f` and
`μ̂_{x,y}(s) = e^{-(F(χ(y)s) - F(χ(x)s))}`" — and it is what `main_characterization` now states
for (⇒). Because `kernel` is what A17 constructs, `main_analysis'` prints **A17 and A18**, where
`main_analysis` prints A18 alone; the pair of lines in `CIAxiomGuard.lean` keeps both facts
visible.
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
    ∃ χ : ℝ → ℝ, χ 0 = 0 ∧ χ 1 = 1 ∧ StrictMonoOn χ (Ici 0) ∧ SurjOn χ (Ici 0) (Ici 0) ∧
      (∀ σ x : ℝ, 0 < σ → 0 ≤ x → χ (S σ x) = σ * χ x) ∧
      (∀ x y : ℝ, 0 ≤ x → x ≤ y → Fam.Φ x y = mconvL1 (Fam.repr x y)) ∧
      (∀ x y s : ℝ, 0 ≤ x → x ≤ y → 0 ≤ s →
        laplace (Fam.repr x y) s
          = Real.exp (-(Fam.G 1 (χ y * s) - Fam.G 1 (χ x * s)))) ∧
      (∀ a b : ℝ, 0 < a → a ≤ b → ∃ b₀ : ℝ, ∃ ν : Measure ℝ, 0 ≤ b₀ ∧ IsCausal ν ∧
        ∀ s : ℝ, 0 ≤ s →
          ENNReal.ofReal (Fam.G 1 (b * s) - Fam.G 1 (a * s)) = levyExponent b₀ ν s) ∧
      (∀ s : ℝ, 0 < s → Fam.G 1 s ≠ 0) := by
  refine ⟨gauge S, gauge_zero S, gauge_one hcov, strictMonoOn_gauge hcov, surjOn_gauge hcov,
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

/-- **`thm:main-analysis`**: every family satisfying (A1)–(A8) and (ND) comes from a gauge and an
exponent of the form `(7.1)`.

`similarity_form` supplies everything but the density; ledger **A18** supplies the density. -/
theorem main_analysis (Fam : CascadeCore) (hcov : IsScaleCovariant Fam (Ioi 0) S) :
    ∃ χ : ℝ → ℝ, ∃ b₀ : ℝ, ∃ k : ℝ → ℝ,
      χ 0 = 0 ∧ χ 1 = 1 ∧ StrictMonoOn χ (Ici 0) ∧ SurjOn χ (Ici 0) (Ici 0) ∧
      (∀ σ x : ℝ, 0 < σ → 0 ≤ x → χ (S σ x) = σ * χ x) ∧
      0 ≤ b₀ ∧ AntitoneOn k (Ioi 0) ∧ (∀ t : ℝ, 0 < t → 0 ≤ k t) ∧
      (∀ x y : ℝ, 0 ≤ x → x ≤ y → Fam.Φ x y = mconvL1 (Fam.repr x y)) ∧
      (∀ s : ℝ, 0 ≤ s → levyExponentD b₀ k s ≠ ⊤) ∧
      (∀ x y s : ℝ, 0 ≤ x → x ≤ y → 0 ≤ s →
        laplace (Fam.repr x y) s
          = Real.exp (-((levyExponentD b₀ k (χ y * s)).toReal
              - (levyExponentD b₀ k (χ x * s)).toReal))) ∧
      (∃ s : ℝ, 0 < s ∧ levyExponentD b₀ k s ≠ 0) := by
  obtain ⟨χ, hχ0, hχ1, hχmono, hχsurj, hχS, hrepr, htrans, hincr, hnd⟩ :=
    similarity_form Fam hcov
  -- `F = G(1,\cdot)` is itself a Lévy exponent — the increment from the origin.
  obtain ⟨b₀, ν, hb₀, hν, hF⟩ := exponent_hasLevyRep Fam le_rfl (zero_le_one (α := ℝ))
  have hFG : ∀ s : ℝ, 0 ≤ s → ENNReal.ofReal (Fam.G 1 s) = levyExponent b₀ ν s := hF
  -- A18: the dilation increments force a nonincreasing density.
  obtain ⟨c₀, k, hc₀, hk, hknn, hFD⟩ :=
    exists_antitone_density_of_dilation_increments hb₀ hν hFG hincr
  have hχnn : ∀ z : ℝ, 0 ≤ z → 0 ≤ χ z := fun z hz => by
    rw [← hχ0]; exact hχmono.monotoneOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr hz) hz
  -- On the half line the two readings of `F` agree as real numbers.
  have hGnn : ∀ u : ℝ, 0 ≤ u → 0 ≤ Fam.G 1 u := fun u hu => exponent_nonneg Fam 0 1 hu
  have htoReal : ∀ u : ℝ, 0 ≤ u → (levyExponentD c₀ k u).toReal = Fam.G 1 u := fun u hu => by
    rw [← hFD u hu, ENNReal.toReal_ofReal (hGnn u hu)]
  refine ⟨χ, c₀, k, hχ0, hχ1, hχmono, hχsurj, hχS, hc₀, hk, hknn, hrepr,
    fun s hs => by rw [← hFD s hs]; exact ENNReal.ofReal_ne_top,
    fun x y s hx hxy hs => ?_, ?_⟩
  · rw [htoReal _ (mul_nonneg (hχnn y (hx.trans hxy)) hs),
      htoReal _ (mul_nonneg (hχnn x hx) hs)]
    exact htrans x y s hx hxy hs
  · refine ⟨1, one_pos, ?_⟩
    rw [← hFD 1 zero_le_one, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact lt_of_le_of_ne (hGnn 1 zero_le_one) (Ne.symm (hnd 1 one_pos))

/-- **`thm:main-analysis`, concluding where `thm:main-construction` starts.** The analysis
direction lands in a `SelfDecomposableExponent` — the article's "`F` of the form (7.1),
`F ≢ 0`" — and identifies the family's kernels with `F`'s: `μ_{x,y} = μ^F_{χ(x),χ(y)}` and
`Φ_{x,y} = μ^F_{χ(x),χ(y)} ∗ ·`. This is the round-trip form of Theorem 7.3 (⇒), added by the
fidelity review (finding R1); `main_analysis` is its content and this is its packaging.

Three things are worth being explicit about. Finiteness of the exponent, which the structure's
`ne_top` field demands, is *not* re-derived: it is a conjunct of `main_analysis`, where it comes
free from ledger A18's conclusion `ofReal (F s) = levyExponentD c₀ k s`. The density A18
returns is normalised to `k 0 = 0` here — a value `levyExponentD` never reads, so the exponent
is unchanged and the normalisation is exactly what the structure's docstring says it is. And
the gauge is normalised, `χ 1 = 1` (`gauge_one`), which is the hypothesis `prop:main-uniqueness`
takes: without it the conjuncts pin `χ` only up to a positive scalar, and the uniqueness clause
would not be reachable from this one. The kernel identification is `kernel_unique`: `μ_{x,y}`
is causal with the transform of `F`'s increment, and Laplace injectivity does the rest. -/
theorem main_analysis' (Fam : CascadeCore) (hcov : IsScaleCovariant Fam (Ioi 0) S) :
    ∃ χ : ℝ → ℝ, ∃ F : SelfDecomposableExponent,
      χ 0 = 0 ∧ χ 1 = 1 ∧ StrictMonoOn χ (Ici 0) ∧ SurjOn χ (Ici 0) (Ici 0) ∧
      (∀ σ x : ℝ, 0 < σ → 0 ≤ x → χ (S σ x) = σ * χ x) ∧
      (∃ s₀ : ℝ, 0 < s₀ ∧ F.exponent s₀ ≠ 0) ∧
      ∀ x y : ℝ, 0 ≤ x → x ≤ y →
        Fam.repr x y = F.kernel (χ x) (χ y) ∧
        Fam.Φ x y = mconvL1 (F.kernel (χ x) (χ y)) := by
  obtain ⟨χ, b₀, k, hχ0, hχ1, hχmono, hχsurj, hχS, hb₀, hk, hknn, hrepr, hfin, htrans, hnd⟩ :=
    main_analysis Fam hcov
  -- Normalise the density at the origin; `levyExponentD` integrates over `Ioi 0` and never
  -- reads `k 0`, so the exponent is unchanged.
  set k' : ℝ → ℝ := fun t => if t = 0 then 0 else k t with hk'
  have hk'eq : ∀ t ∈ Ioi (0 : ℝ), k' t = k t := fun t ht => by
    simp only [hk', if_neg (ne_of_gt (mem_Ioi.mp ht))]
  have hexp : ∀ s, levyExponentD b₀ k' s = levyExponentD b₀ k s := fun s => by
    simp only [levyExponentD, levyJump]
    congr 1
    exact setLIntegral_congr_fun measurableSet_Ioi fun t ht => by rw [hk'eq t ht]
  let F : SelfDecomposableExponent :=
    { b₀ := b₀
      k := k'
      b₀_nonneg := hb₀
      k_nonneg := fun t ht => by rw [hk'eq t ht]; exact hknn t (mem_Ioi.mp ht)
      k_antitone := fun a ha b hb hab => by rw [hk'eq a ha, hk'eq b hb]; exact hk ha hb hab
      k_zero := by simp [hk']
      ne_top := fun s hs => by rw [hexp]; exact hfin s hs }
  have hFexp : ∀ s, F.exponent s = levyExponentD b₀ k s := fun s => hexp s
  have hχnn : ∀ z : ℝ, 0 ≤ z → 0 ≤ χ z := fun z hz => by
    rw [← hχ0]; exact hχmono.monotoneOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr hz) hz
  refine ⟨χ, F, hχ0, hχ1, hχmono, hχsurj, hχS, ?_, fun x y hx hxy => ?_⟩
  · obtain ⟨s, hs, hne⟩ := hnd
    exact ⟨s, hs, by rw [hFexp]; exact hne⟩
  · have hχx : 0 ≤ χ x := hχnn x hx
    have hχxy : χ x ≤ χ y := hχmono.monotoneOn (mem_Ici.mpr hx) (mem_Ici.mpr (hx.trans hxy)) hxy
    -- The kernel identification, by Laplace injectivity.
    have hker : Fam.repr x y = F.kernel (χ x) (χ y) := by
      refine SelfDecomposableExponent.kernel_unique (isCausal_repr Fam x y) hχx hχxy
        fun s hs => ?_
      rw [SelfDecomposableExponent.increment_toReal hχx hχxy hs, hFexp, hFexp]
      exact htrans x y s hx hxy hs
    exact ⟨hker, (hrepr x y hx hxy).trans (mconvL1_congr hker)⟩

end CascadeCore

end Hemigroup
