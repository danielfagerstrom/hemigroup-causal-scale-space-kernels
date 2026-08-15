/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.Covariance

/-!
# `prop:canonical-gauge`: the orbit coordinate

Blueprint: `blueprint/src/parts/06-covariance.tex`, Proposition 6.3.

The scale variable of a hemigroup family carries no intrinsic parametrisation — any increasing
bijection of `[0,∞)` gives an equivalent family — so a coordinate has to be *chosen*, and the
action chooses it. `c(σ) := S_σ 1` is the orbit of the unit scale; the gauge `χ` is its inverse,
and in that coordinate `S_σ` is multiplication by `σ` and `G` takes the similarity form
`G(x,s) = F(χ(x)\,s)`.

## The one thing that has to be proved

That `c` is *onto* `(0,∞)`. Everything else is already in `Covariance.lean`: `c` is continuous
and strictly increasing by `lem:action-rigidity`(3), and `c(1) = 1` by the group law. The
blueprint argues surjectivity by saying that the limits of `c` at the two ends are fixed points
of the action, and `lem:action-rigidity`(4) says the action has none in `(0,∞)`.

Here that is made exact without limits. The orbit `R = c((0,∞))` is invariant under every `S_ρ`
— the group law is precisely that. If `R` were bounded above, its supremum `M` would satisfy
`S_ρ M = M` for every `ρ`: no orbit point can be carried above `M`, because `S_ρ` maps `R` into
`R`, and none below it either, because `S_{ρ^{-1}}` would then carry `M` down and `S_ρ` is
monotone. So `M` is a fixed point, so `M = 0` — but `1 ∈ R`. The bounded-below case is the same
argument read downwards, and there `m > 0` is contradicted directly.

With `R` unbounded in both directions and `c` continuous, the intermediate value theorem
finishes.

## What the statement carries

`canonical_gauge` bundles `χ` with the conjugation `χ(S_σ x) = σ χ(x)` and the similarity form,
not just with its order properties. That is deliberate: `prop:main-uniqueness` quantifies over
gauges and declined to guess at the interface, and this is where it is fixed.
-/

namespace Hemigroup

open MeasureTheory Set Filter
open scoped Topology

namespace CascadeCore

variable {Fam : CascadeCore} {Gs : Set ℝ} {S : ℝ → ℝ → ℝ}

/-! ## The action is continuous in its argument

Not the same statement as `lem:action-rigidity`(3), which is continuity in `σ`. This one is free:
a strictly monotone map of `[0,∞)` *onto* `[0,∞)` is continuous at every interior point, because
its image is a neighbourhood of every image point.
-/

theorem continuousOn_S (hcov : IsScaleCovariant Fam Gs S) {σ : ℝ} (hσ : 0 < σ) (hmem : σ ∈ Gs) :
    ContinuousOn (S σ) (Ioi 0) := by
  intro a ha
  refine ContinuousAt.continuousWithinAt ?_
  have ha' : (0 : ℝ) < a := mem_Ioi.mp ha
  have himg : S σ '' (Ici 0) = Ici 0 :=
    Subset.antisymm (image_subset_iff.mpr (hcov.S_mapsTo σ hσ hmem)) (hcov.S_surjOn σ hσ hmem)
  refine (hcov.S_strictMonoOn σ hσ hmem).continuousAt_of_image_mem_nhds (Ici_mem_nhds ha') ?_
  rw [himg]
  exact Ici_mem_nhds (S_pos hcov hσ hmem ha')

/-! ## The orbit of the unit scale -/

/-- The orbit `R = \{S_σ 1 : σ > 0\}` is invariant under the action — which is the group law and
nothing else. -/
theorem mapsTo_S_orbit (hcov : IsScaleCovariant Fam (Ioi 0) S) {ρ : ℝ} (hρ : 0 < ρ) :
    MapsTo (S ρ) ((fun σ => S σ 1) '' (Ioi 0)) ((fun σ => S σ 1) '' (Ioi 0)) := by
  rintro _ ⟨τ, hτ, rfl⟩
  have hτ' : (0 : ℝ) < τ := mem_Ioi.mp hτ
  exact ⟨ρ * τ, mem_Ioi.mpr (mul_pos hρ hτ'),
    (S_comp hcov hρ hτ' (mem_Ioi.mpr hρ) hτ (mem_Ioi.mpr (mul_pos hρ hτ')) zero_le_one).symm⟩

/-- `1` is on the orbit. -/
theorem one_mem_orbit (hcov : IsScaleCovariant Fam (Ioi 0) S) :
    (1 : ℝ) ∈ (fun σ => S σ 1) '' (Ioi 0) :=
  ⟨1, mem_Ioi.mpr one_pos, S_one hcov (mem_Ioi.mpr one_pos) zero_le_one⟩

/-- **The orbit is unbounded above.** Otherwise its supremum is a fixed point of the action, and
`lem:action-rigidity`(4) allows none above the origin. -/
theorem exists_orbit_gt (hcov : IsScaleCovariant Fam (Ioi 0) S) (y : ℝ) :
    ∃ σ : ℝ, 0 < σ ∧ y < S σ 1 := by
  by_contra hcon
  push_neg at hcon
  set R : Set ℝ := (fun σ => S σ 1) '' (Ioi 0) with hR
  have hne : R.Nonempty := ⟨1, one_mem_orbit hcov⟩
  have hbdd : BddAbove R := ⟨y, by rintro _ ⟨τ, hτ, rfl⟩; exact hcon τ (mem_Ioi.mp hτ)⟩
  set M : ℝ := sSup R with hM
  have hub : ∀ z ∈ R, z ≤ M := fun z hz => le_csSup hbdd hz
  have hMpos : 0 < M := lt_of_lt_of_le one_pos (hub 1 (one_mem_orbit hcov))
  -- Nothing on the orbit can be carried above the supremum.
  have hle : ∀ ρ : ℝ, 0 < ρ → S ρ M ≤ M := by
    intro ρ hρ
    by_contra hlt
    push_neg at hlt
    have hcontρ : ContinuousAt (S ρ) M :=
      (continuousOn_S hcov hρ (mem_Ioi.mpr hρ)).continuousAt (Ioi_mem_nhds hMpos)
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hcontρ (Ioi_mem_nhds hlt))
    obtain ⟨z, hzR, hz⟩ := exists_lt_of_lt_csSup hne (show M - δ < M by linarith)
    have hzin : z ∈ Metric.ball M δ := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith, by linarith [hub z hzR]⟩
    exact absurd (hub _ (mapsTo_S_orbit hcov hρ hzR)) (not_le.mpr (hball hzin))
  -- Nor below it, since `S_{ρ^{-1}}` would have to carry it down.
  have hge : ∀ ρ : ℝ, 0 < ρ → M ≤ S ρ M := by
    intro ρ hρ
    have hinv := hle ρ⁻¹ (inv_pos.mpr hρ)
    have hmono := monotoneOn_S hcov hρ (mem_Ioi.mpr hρ)
      (mem_Ici.mpr (hcov.S_mapsTo ρ⁻¹ (inv_pos.mpr hρ) (mem_Ioi.mpr (inv_pos.mpr hρ))
        (mem_Ici.mpr hMpos.le))) (mem_Ici.mpr hMpos.le) hinv
    rwa [S_comp hcov hρ (inv_pos.mpr hρ) (mem_Ioi.mpr hρ) (mem_Ioi.mpr (inv_pos.mpr hρ))
      (mem_Ioi.mpr (by rw [mul_inv_cancel₀ hρ.ne']; exact one_pos)) hMpos.le,
      mul_inv_cancel₀ hρ.ne', S_one hcov (mem_Ioi.mpr one_pos) hMpos.le] at hmono
  exact absurd (eq_zero_of_fixed hcov hMpos.le fun ρ hρ => le_antisymm (hle ρ hρ) (hge ρ hρ))
    hMpos.ne'

/-- **The orbit reaches down to the origin.** The same argument read downwards, and simpler: a
positive infimum is itself the contradiction. -/
theorem exists_orbit_lt (hcov : IsScaleCovariant Fam (Ioi 0) S) {y : ℝ} (hy : 0 < y) :
    ∃ σ : ℝ, 0 < σ ∧ S σ 1 < y := by
  by_contra hcon
  push_neg at hcon
  set R : Set ℝ := (fun σ => S σ 1) '' (Ioi 0) with hR
  have hne : R.Nonempty := ⟨1, one_mem_orbit hcov⟩
  have hbdd : BddBelow R := ⟨y, by rintro _ ⟨τ, hτ, rfl⟩; exact hcon τ (mem_Ioi.mp hτ)⟩
  set m : ℝ := sInf R with hm
  have hlb : ∀ z ∈ R, m ≤ z := fun z hz => csInf_le hbdd hz
  have hylb : ∀ z ∈ R, y ≤ z := by
    rintro _ ⟨τ, hτ, rfl⟩
    exact hcon τ (mem_Ioi.mp hτ)
  have hmpos : 0 < m := lt_of_lt_of_le hy (le_csInf hne hylb)
  have hge : ∀ ρ : ℝ, 0 < ρ → m ≤ S ρ m := by
    intro ρ hρ
    by_contra hlt
    push_neg at hlt
    have hcontρ : ContinuousAt (S ρ) m :=
      (continuousOn_S hcov hρ (mem_Ioi.mpr hρ)).continuousAt (Ioi_mem_nhds hmpos)
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hcontρ (Iio_mem_nhds hlt))
    obtain ⟨z, hzR, hz⟩ := exists_lt_of_csInf_lt hne (show m < m + δ by linarith)
    have hzin : z ∈ Metric.ball m δ := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [hlb z hzR], by linarith⟩
    exact absurd (hlb _ (mapsTo_S_orbit hcov hρ hzR)) (not_le.mpr (hball hzin))
  have hle : ∀ ρ : ℝ, 0 < ρ → S ρ m ≤ m := by
    intro ρ hρ
    have hinv := hge ρ⁻¹ (inv_pos.mpr hρ)
    have hmono := monotoneOn_S hcov hρ (mem_Ioi.mpr hρ) (mem_Ici.mpr hmpos.le)
      (mem_Ici.mpr (hcov.S_mapsTo ρ⁻¹ (inv_pos.mpr hρ) (mem_Ioi.mpr (inv_pos.mpr hρ))
        (mem_Ici.mpr hmpos.le))) hinv
    rwa [S_comp hcov hρ (inv_pos.mpr hρ) (mem_Ioi.mpr hρ) (mem_Ioi.mpr (inv_pos.mpr hρ))
      (mem_Ioi.mpr (by rw [mul_inv_cancel₀ hρ.ne']; exact one_pos)) hmpos.le,
      mul_inv_cancel₀ hρ.ne', S_one hcov (mem_Ioi.mpr one_pos) hmpos.le] at hmono
  exact absurd (eq_zero_of_fixed hcov hmpos.le fun ρ hρ => le_antisymm (hle ρ hρ) (hge ρ hρ))
    hmpos.ne'

/-- **`c` is onto `(0,∞)`.** Unbounded in both directions and continuous, so the intermediate
value theorem applies. -/
theorem exists_orbit_eq (hcov : IsScaleCovariant Fam (Ioi 0) S) {y : ℝ} (hy : 0 < y) :
    ∃ σ : ℝ, 0 < σ ∧ S σ 1 = y := by
  obtain ⟨a, ha, hlt⟩ := exists_orbit_lt hcov hy
  obtain ⟨b, hb, hgt⟩ := exists_orbit_gt hcov y
  have hab : a < b := by
    by_contra hcon
    push_neg at hcon
    have hmono :=
      (strictMonoOn_S_apply hcov one_pos).monotoneOn (mem_Ioi.mpr hb) (mem_Ioi.mpr ha) hcon
    exact absurd (lt_of_lt_of_le hlt (le_trans (le_refl y) hgt.le)) (by linarith [hmono])
  have hsub : Icc a b ⊆ Ioi 0 := fun t ht => mem_Ioi.mpr (lt_of_lt_of_le ha ht.1)
  have hcont : ContinuousOn (fun σ => S σ 1) (Icc a b) :=
    (continuousOn_S_apply hcov one_pos).mono hsub
  obtain ⟨σ, hσmem, hσ⟩ :=
    intermediate_value_Icc hab.le hcont (⟨hlt.le, hgt.le⟩ : y ∈ Icc (S a 1) (S b 1))
  exact ⟨σ, lt_of_lt_of_le ha hσmem.1, hσ⟩

/-! ## The gauge -/

/-- **The canonical gauge** `χ`: the inverse of `σ ↦ S_σ 1`, extended by `χ(0) = 0`. -/
noncomputable def gauge (S : ℝ → ℝ → ℝ) (y : ℝ) : ℝ :=
  if 0 < y then Function.invFunOn (fun σ => S σ 1) (Ioi 0) y else 0

@[simp] theorem gauge_zero (S : ℝ → ℝ → ℝ) : gauge S 0 = 0 := if_neg (lt_irrefl 0)

theorem gauge_of_nonpos {y : ℝ} (hy : y ≤ 0) : gauge S y = 0 := if_neg (not_lt.mpr hy)

/-- On `(0,∞)` the gauge inverts the orbit map. -/
theorem orbit_gauge (hcov : IsScaleCovariant Fam (Ioi 0) S) {y : ℝ} (hy : 0 < y) :
    S (gauge S y) 1 = y := by
  obtain ⟨σ, hσ, hσy⟩ := exists_orbit_eq hcov hy
  rw [gauge, if_pos hy]
  exact Function.invFunOn_eq (f := fun σ : ℝ => S σ 1) (s := Ioi 0) ⟨σ, mem_Ioi.mpr hσ, hσy⟩

theorem gauge_pos (hcov : IsScaleCovariant Fam (Ioi 0) S) {y : ℝ} (hy : 0 < y) :
    0 < gauge S y := by
  obtain ⟨σ, hσ, hσy⟩ := exists_orbit_eq hcov hy
  rw [gauge, if_pos hy]
  exact mem_Ioi.mp (Function.invFunOn_mem (f := fun σ : ℝ => S σ 1) (s := Ioi 0)
    ⟨σ, mem_Ioi.mpr hσ, hσy⟩)

theorem gauge_nonneg (hcov : IsScaleCovariant Fam (Ioi 0) S) (y : ℝ) : 0 ≤ gauge S y := by
  by_cases hy : 0 < y
  · exact (gauge_pos hcov hy).le
  · rw [gauge_of_nonpos (not_lt.mp hy)]

/-- The other composite: the gauge of an orbit point is its parameter. -/
theorem gauge_orbit (hcov : IsScaleCovariant Fam (Ioi 0) S) {σ : ℝ} (hσ : 0 < σ) :
    gauge S (S σ 1) = σ := by
  have hpos : 0 < S σ 1 := S_pos hcov hσ (mem_Ioi.mpr hσ) one_pos
  refine (strictMonoOn_S_apply hcov one_pos).injOn
    (mem_Ioi.mpr (gauge_pos hcov hpos)) (mem_Ioi.mpr hσ) ?_
  exact orbit_gauge hcov hpos

/-- **The normalisation `χ(1) = 1`.** `1 = S_1 1` is the orbit point of parameter `1`, so the
gauge sends it to `1`. This is the normalisation `prop:main-uniqueness` hypothesises, and
exporting it from the analysis direction is what makes that clause reachable from
`thm:main-analysis`'s conclusion. -/
theorem gauge_one (hcov : IsScaleCovariant Fam (Ioi 0) S) : gauge S 1 = 1 := by
  have h := gauge_orbit hcov one_pos
  rwa [S_one hcov (mem_Ioi.mpr one_pos) zero_le_one] at h

theorem strictMonoOn_gauge (hcov : IsScaleCovariant Fam (Ioi 0) S) :
    StrictMonoOn (gauge S) (Ici 0) := by
  intro a ha b _ hab
  have hbpos : 0 < b := lt_of_le_of_lt (mem_Ici.mp ha) hab
  rcases eq_or_lt_of_le (mem_Ici.mp ha) with rfl | hapos
  · rw [gauge_zero]
    exact gauge_pos hcov hbpos
  · refine (strictMonoOn_S_apply hcov one_pos).lt_iff_lt
      (mem_Ioi.mpr (gauge_pos hcov hapos)) (mem_Ioi.mpr (gauge_pos hcov hbpos)) |>.mp ?_
    rw [orbit_gauge hcov hapos, orbit_gauge hcov hbpos]
    exact hab

theorem surjOn_gauge (hcov : IsScaleCovariant Fam (Ioi 0) S) :
    SurjOn (gauge S) (Ici 0) (Ici 0) := by
  intro t ht
  rcases eq_or_lt_of_le (mem_Ici.mp ht) with rfl | htpos
  · exact ⟨0, mem_Ici.mpr le_rfl, gauge_zero S⟩
  · exact ⟨S t 1, mem_Ici.mpr (S_pos hcov htpos (mem_Ioi.mpr htpos) one_pos).le,
      gauge_orbit hcov htpos⟩

/-- **The conjugation.** In the gauge, `S_σ` is multiplication by `σ`. -/
theorem gauge_S (hcov : IsScaleCovariant Fam (Ioi 0) S) {σ x : ℝ} (hσ : 0 < σ) (hx : 0 ≤ x) :
    gauge S (S σ x) = σ * gauge S x := by
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · rw [S_zero hcov hσ (mem_Ioi.mpr hσ), gauge_zero, mul_zero]
  · have hg : 0 < gauge S x := gauge_pos hcov hxpos
    have hrew : S σ x = S (σ * gauge S x) 1 := by
      conv_lhs => rw [← orbit_gauge hcov hxpos]
      exact S_comp hcov hσ hg (mem_Ioi.mpr hσ) (mem_Ioi.mpr hg)
        (mem_Ioi.mpr (mul_pos hσ hg)) zero_le_one
    rw [hrew, gauge_orbit hcov (mul_pos hσ hg)]

/-- **The similarity form** `(6.2)`: in the gauge, `G` depends on `x` and `s` only through their
product. -/
theorem G_eq_gauge (hcov : IsScaleCovariant Fam (Ioi 0) S) {x : ℝ} (hx : 0 ≤ x) (s : ℝ) :
    Fam.G x s = Fam.G 1 (gauge S x * s) := by
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · rw [gauge_zero, zero_mul, G_zero_left, G_atZero]
  · conv_lhs => rw [← orbit_gauge hcov hxpos]
    exact G_scale hcov (gauge_pos hcov hxpos) (mem_Ioi.mpr (gauge_pos hcov hxpos)) zero_le_one s

/-- **`prop:canonical-gauge`.** The gauge, with everything downstream needs of it: it is an
increasing bijection of `[0,∞)` fixing the origin, it conjugates the action into multiplication,
and it puts `G` into the similarity form `G(x,s) = F(χ(x)s)` with `F = G(1,\cdot)`.

`F \in \LE` is not asserted: `F = g_{0,1}`, so that is `thm:increments-bernstein` and nothing
new. -/
theorem canonical_gauge (hcov : IsScaleCovariant Fam (Ioi 0) S) :
    ∃ χ : ℝ → ℝ, χ 0 = 0 ∧ StrictMonoOn χ (Ici 0) ∧ SurjOn χ (Ici 0) (Ici 0) ∧
      (∀ σ x : ℝ, 0 < σ → 0 ≤ x → χ (S σ x) = σ * χ x) ∧
      (∀ x s : ℝ, 0 ≤ x → Fam.G x s = Fam.G 1 (χ x * s)) :=
  ⟨gauge S, gauge_zero S, strictMonoOn_gauge hcov, surjOn_gauge hcov,
    fun _ _ hσ hx => gauge_S hcov hσ hx, fun _ _ hx => G_eq_gauge hcov hx _⟩

end CascadeCore

end Hemigroup
