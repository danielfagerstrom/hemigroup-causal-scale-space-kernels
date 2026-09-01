/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Hemigroup.Instance

/-!
# Reparametrising a cascade family by a gauge

Blueprint: `thm:main-construction` in an arbitrary gauge (fidelity review, finding R8).

Theorem 7.3 (⇐) is stated for an arbitrary increasing bijection `χ` of `[0,∞)`: the family
`Φ_{x,y} = μ_{χ(x),χ(y)} ∗ ·` satisfies the axioms. `cascadeFamily` proves it in the canonical
gauge `χ = id`, which is what the article's own proof does ("work in the canonical gauge"). The
general case is the canonical one reparametrised, and this file is that reparametrisation:
`CascadeFamily.reparam` sends a family `Φ` and a gauge `χ` to `(x,y) ↦ Φ_{χ(x),χ(y)}`.

Every axiom transports verbatim except two. (A7) needs `χ` continuous on `[0,∞)`, which an
increasing bijection of `[0,∞)` is (`continuousOn_of_strictMonoOn_surjOn`, from Mathlib's
monotone-plus-surjective-implies-continuous lemmas); and (A8)'s action becomes
`S'_σ = χ⁻¹ ∘ S_σ ∘ χ`, with `χ⁻¹` the inverse on `[0,∞)` (`Function.invFunOn`).
`cascadeFamily_reparam` is then Theorem 7.3 (⇐) in the gauge `χ`, by `rfl`.
-/

namespace Hemigroup

open MeasureTheory Set Filter Topology

/-- An increasing bijection of `[0,∞)` is continuous on `[0,∞)`: at interior points by
`StrictMonoOn.continuousAt_of_image_mem_nhds`, at `0` from the right by
`StrictMonoOn.continuousWithinAt_right_of_surjOn`. -/
theorem continuousOn_of_strictMonoOn_surjOn {χ : ℝ → ℝ} (hχ0 : χ 0 = 0)
    (hmono : StrictMonoOn χ (Ici 0)) (hsurj : SurjOn χ (Ici 0) (Ici 0)) :
    ContinuousOn χ (Ici 0) := by
  intro a ha
  rcases eq_or_lt_of_le (mem_Ici.mp ha) with rfl | hapos
  · -- At the origin, from the right.
    have hs : Ici (0 : ℝ) ∈ 𝓝[≥] (0 : ℝ) := self_mem_nhdsWithin
    have hsurj' : SurjOn χ (Ici 0) (Ioi (χ 0)) := by
      rw [hχ0]; exact hsurj.mono subset_rfl Ioi_subset_Ici_self
    exact hmono.continuousWithinAt_right_of_surjOn hs hsurj'
  · -- Away from it, two-sided.
    have hs : Ici (0 : ℝ) ∈ 𝓝 a := Ici_mem_nhds hapos
    have hpos : 0 < χ a := by
      rw [← hχ0]; exact hmono (mem_Ici.mpr le_rfl) ha hapos
    have himg : χ '' Ici 0 ∈ 𝓝 (χ a) :=
      mem_of_superset (Ioi_mem_nhds hpos) fun b hb => hsurj (mem_Ici.mpr (mem_Ioi.mp hb).le)
    exact (hmono.continuousAt_of_image_mem_nhds hs himg).continuousWithinAt

namespace CascadeFamily

variable (Fam : CascadeFamily) {χ : ℝ → ℝ}

/-- **The reparametrised family.** `Φ'_{x,y} := Φ_{χ(x),χ(y)}` and `S'_σ := χ⁻¹ ∘ S_σ ∘ χ`, for
an increasing bijection `χ` of `[0,∞)` with `χ(0) = 0`. -/
noncomputable def reparam (hχ0 : χ 0 = 0) (hmono : StrictMonoOn χ (Ici 0))
    (hsurj : SurjOn χ (Ici 0) (Ici 0)) : CascadeFamily :=
  -- `χ` is nonnegative and monotone on `[0,∞)`; its inverse there is `invFunOn`.
  have hnn : ∀ x, 0 ≤ x → 0 ≤ χ x := fun x hx => by
    rw [← hχ0]; exact hmono.monotoneOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx) hx
  have hle : ∀ x y, 0 ≤ x → x ≤ y → χ x ≤ χ y := fun x y hx hxy =>
    hmono.monotoneOn (mem_Ici.mpr hx) (mem_Ici.mpr (hx.trans hxy)) hxy
  have hinv : ∀ b, 0 ≤ b → χ (Function.invFunOn χ (Ici 0) b) = b := fun b hb =>
    Function.invFunOn_eq (hsurj (mem_Ici.mpr hb))
  have hinv_mem : ∀ b, 0 ≤ b → 0 ≤ Function.invFunOn χ (Ici 0) b := fun b hb =>
    mem_Ici.mp (Function.invFunOn_mem (hsurj (mem_Ici.mpr hb)))
  have hleft : ∀ x, 0 ≤ x → Function.invFunOn χ (Ici 0) (χ x) = x := fun x hx =>
    hmono.injOn.leftInvOn_invFunOn (mem_Ici.mpr hx)
  { Φ := fun x y => Fam.Φ (χ x) (χ y)
    translation := fun x y hx hxy a f => Fam.translation _ _ (hnn x hx) (hle x y hx hxy) a f
    causal := fun x y hx hxy t₀ f hf => Fam.causal _ _ (hnn x hx) (hle x y hx hxy) t₀ f hf
    positive := fun x y hx hxy f hf => Fam.positive _ _ (hnn x hx) (hle x y hx hxy) f hf
    unit_area := fun x y hx hxy f hf => Fam.unit_area _ _ (hnn x hx) (hle x y hx hxy) f hf
    refl := fun x hx => Fam.refl _ (hnn x hx)
    cascade := fun x y z hx hxy hyz =>
      Fam.cascade _ _ _ (hnn x hx) (hle x y hx hxy) (hle y z (hx.trans hxy) hyz)
    continuous := fun f => by
      have hχc := continuousOn_of_strictMonoOn_surjOn hχ0 hmono hsurj
      have hg : ContinuousOn (fun p : ℝ × ℝ => (χ p.1, χ p.2))
          {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2} := by
        refine ContinuousOn.prodMk ?_ ?_
        · exact hχc.comp continuousOn_fst fun p hp => mem_Ici.mpr hp.1
        · exact hχc.comp continuousOn_snd fun p hp => mem_Ici.mpr (hp.1.trans hp.2)
      have hmaps : MapsTo (fun p : ℝ × ℝ => (χ p.1, χ p.2))
          {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2} {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2} :=
        fun p hp => ⟨hnn _ hp.1, hle _ _ hp.1 hp.2⟩
      exact (Fam.continuous f).comp hg hmaps
    nondegenerate := fun x y hx hxy =>
      Fam.nondegenerate _ _ (hnn x hx) (hmono (mem_Ici.mpr hx) (mem_Ici.mpr (hx.trans hxy.le)) hxy)
    S := fun σ x => Function.invFunOn χ (Ici 0) (Fam.S σ (χ x))
    covariant :=
      { S_mapsTo := fun σ hσ hmem x hx =>
          mem_Ici.mpr (hinv_mem _ (Fam.covariant.S_mapsTo σ hσ hmem (mem_Ici.mpr (hnn x hx))))
        S_strictMonoOn := fun σ hσ hmem x hx y hy hxy => by
          have hx' := hnn x hx
          have hy' := hnn y hy
          have h1 : Fam.S σ (χ x) < Fam.S σ (χ y) :=
            Fam.covariant.S_strictMonoOn σ hσ hmem (mem_Ici.mpr hx') (mem_Ici.mpr hy')
              (hmono hx hy hxy)
          have hSx := Fam.covariant.S_mapsTo σ hσ hmem (mem_Ici.mpr hx')
          have hSy := Fam.covariant.S_mapsTo σ hσ hmem (mem_Ici.mpr hy')
          by_contra hcon
          have := hle _ _ (hinv_mem _ hSy) (not_lt.mp hcon)
          rw [hinv _ hSx, hinv _ hSy] at this
          exact absurd h1 (not_lt.mpr this)
        S_surjOn := fun σ hσ hmem z hz => by
          obtain ⟨v, hv, hvz⟩ :=
            Fam.covariant.S_surjOn σ hσ hmem (mem_Ici.mpr (hnn z (mem_Ici.mp hz)))
          obtain ⟨x, hx, hxv⟩ := hsurj hv
          refine ⟨x, hx, ?_⟩
          change Function.invFunOn χ (Ici 0) (Fam.S σ (χ x)) = z
          rw [hxv, hvz, hleft z (mem_Ici.mp hz)]
        scale := fun σ hσ hmem x y hx hxy => by
          have hSx := Fam.covariant.S_mapsTo σ hσ hmem (mem_Ici.mpr (hnn x hx))
          have hSy := Fam.covariant.S_mapsTo σ hσ hmem (mem_Ici.mpr (hnn y (hx.trans hxy)))
          change (dilL1 hσ).comp (Fam.Φ (χ x) (χ y))
            = (Fam.Φ (χ (Function.invFunOn χ (Ici 0) (Fam.S σ (χ x))))
                (χ (Function.invFunOn χ (Ici 0) (Fam.S σ (χ y))))).comp (dilL1 hσ)
          rw [hinv _ hSx, hinv _ hSy]
          exact Fam.covariant.scale σ hσ hmem _ _ (hnn x hx) (hle x y hx hxy) } }

@[simp] theorem reparam_Φ (hχ0 : χ 0 = 0) (hmono : StrictMonoOn χ (Ici 0))
    (hsurj : SurjOn χ (Ici 0) (Ici 0)) (x y : ℝ) :
    (Fam.reparam hχ0 hmono hsurj).Φ x y = Fam.Φ (χ x) (χ y) := rfl

@[simp] theorem reparam_S (hχ0 : χ 0 = 0) (hmono : StrictMonoOn χ (Ici 0))
    (hsurj : SurjOn χ (Ici 0) (Ici 0)) (σ x : ℝ) :
    (Fam.reparam hχ0 hmono hsurj).S σ x = Function.invFunOn χ (Ici 0) (Fam.S σ (χ x)) := rfl

end CascadeFamily

namespace SelfDecomposableExponent

/-- **`thm:main-construction` in an arbitrary gauge.** For every admissible `F` and every
increasing bijection `χ` of `[0,∞)`, the family `Φ_{x,y} = μ^F_{χ(x),χ(y)} ∗ ·` is a causal
cascade measurement family — the reparametrisation of `cascadeFamily` by `χ`, whose scaling
action is `S_σ = χ⁻¹(σ χ(·))`. -/
theorem cascadeFamily_reparam (F : SelfDecomposableExponent)
    (hF : ∃ s₀, 0 < s₀ ∧ F.exponent s₀ ≠ 0) {χ : ℝ → ℝ} (hχ0 : χ 0 = 0)
    (hmono : StrictMonoOn χ (Ici 0)) (hsurj : SurjOn χ (Ici 0) (Ici 0)) (x y : ℝ) :
    ((F.cascadeFamily hF).reparam hχ0 hmono hsurj).Φ x y = mconvL1 (F.kernel (χ x) (χ y)) :=
  rfl

end SelfDecomposableExponent

end Hemigroup
