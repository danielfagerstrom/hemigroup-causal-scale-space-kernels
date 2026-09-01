/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the MIT license as described in the file LICENSES/MIT.txt.
Authors: Daniel Fagerström
-/
import Hemigroup.Additivity

/-!
# `thm:increments-bernstein`, part one: the null-array estimate

In the semigroup case every kernel is an `n`-fold convolution power and infinite divisibility is
immediate. In the hemigroup case there is no such power — the increments over a partition need
not be equal or even comparable — and what replaces it is a null-array limit. On the half line
that limit can be made elementary, and this file is the elementary part of it.

## The statement proved here

For `0 ≤ x ≤ y` and `s ≥ 0`,

  `∫ (1 - e^{-st}) dΠ_n(t) → g_{x,y}(s)`,

where `Π_n = Σ_i μ_{t_i, t_{i+1}}` over the uniform `n`-partition of `[x,y]`. Each `Π_n` is a
*finite* measure, so each approximant is a Lévy exponent with finite Lévy measure and no drift.
What remains for the theorem itself is to extract the limiting triple from `(Π_n)`, which is a
vague-compactness argument and is not here.

## Why it is elementary

Three ingredients, and no limit theorem for triangular arrays:

* additivity (`sum_exponent_part`), which makes `g_{x,y}(s)` the sum of the increments;
* uniform continuity of `G(\cdot, s)` on the compact `[x,y]`, which makes the increments
  uniformly small;
* the inequality `0 ≤ u - (1 - e^{-u}) ≤ u²`, which converts a sum of exponents into a sum of
  `1 - \hat\mu_i(s)`, i.e. into an integral against `Π_n`.

The blueprint writes the last with the constant `u²/2`. That constant needs a derivative
argument; `u²` follows from `e^u ≥ 1 + u` alone, and the factor is irrelevant — it multiplies a
quantity that is going to zero.
-/

namespace Hemigroup

open MeasureTheory Set Filter Finset

/-! ## The elementary inequality -/

-- `one_sub_exp_neg_le`, which the estimates below use, now lives in `Hemigroup.Levy`: chapter
-- 8's admissibility criterion needs the same inequality and does not import this file.

/-- `u - (1 - e^{-u}) ≤ u²` for `u ≥ 0` — the error in that replacement is quadratic.

From `e^u ≥ 1 + u` alone: it gives `e^{-u} ≤ 1/(1+u)`, whence
`u - 1 + e^{-u} ≤ u²/(1+u) ≤ u²`. -/
theorem sub_one_sub_exp_neg_le_sq {u : ℝ} (hu : 0 ≤ u) :
    u - (1 - Real.exp (-u)) ≤ u ^ 2 := by
  have h1 : u + 1 ≤ Real.exp u := Real.add_one_le_exp u
  have h2 : Real.exp (-u) * Real.exp u = 1 := by
    rw [← Real.exp_add]
    simp
  have h3 : 0 < Real.exp (-u) := Real.exp_pos _
  nlinarith [h1, h2, h3]

namespace CascadeCore

variable {Fam : CascadeCore} {x y : ℝ}

/-- `\hat\mu_{x,y}(s) = e^{-g_{x,y}(s)}` — the exponent, undone. -/
theorem laplace_repr_eq (Fam : CascadeCore) (x y : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    laplace (Fam.repr x y) s = Real.exp (-(Fam.exponent x y s)) := by
  rw [exponent, neg_neg, Real.exp_log (laplace_pos_of_prob (isCausal_repr Fam x y) hs)]

/-! ## The uniform partition -/

/-- The `i`-th point of the uniform `n`-partition of `[x,y]`. Total in `n`: at `n = 0` the
Lean convention `i / 0 = 0` makes every point `x`, which no statement below uses. -/
noncomputable def part (x y : ℝ) (n i : ℕ) : ℝ := x + (i / n : ℝ) * (y - x)

@[simp] lemma part_zero (x y : ℝ) (n : ℕ) : part x y n 0 = x := by simp [part]

lemma part_self {n : ℕ} (hn : n ≠ 0) (x y : ℝ) : part x y n n = y := by
  rw [part, div_self (Nat.cast_ne_zero.mpr hn)]
  ring

lemma part_le_succ (hxy : x ≤ y) (n i : ℕ) : part x y n i ≤ part x y n (i + 1) := by
  have hfrac : (i / n : ℝ) ≤ ((i + 1 : ℕ) / n : ℝ) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      gcongr
      exact_mod_cast Nat.le_succ i
  have hd : 0 ≤ y - x := sub_nonneg.mpr hxy
  rw [part, part]
  nlinarith

lemma part_mem_Icc (hxy : x ≤ y) {n i : ℕ} (hn : n ≠ 0) (hi : i ≤ n) :
    part x y n i ∈ Icc x y := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have h0 : (0 : ℝ) ≤ (i / n : ℝ) := by positivity
  have h1 : (i / n : ℝ) ≤ 1 := by
    rw [div_le_one hn']
    exact_mod_cast hi
  have hd : 0 ≤ y - x := sub_nonneg.mpr hxy
  constructor
  · rw [part]; nlinarith
  · rw [part]; nlinarith

lemma part_nonneg (hx : 0 ≤ x) (hxy : x ≤ y) (n i : ℕ) : 0 ≤ part x y n i := by
  have hfrac : (0 : ℝ) ≤ (i / n : ℝ) := by positivity
  have hd : 0 ≤ y - x := sub_nonneg.mpr hxy
  rw [part]
  nlinarith

/-- The mesh: consecutive partition points are `(y - x)/n` apart. -/
lemma part_succ_sub (hn : n ≠ 0) (x y : ℝ) (i : ℕ) :
    part x y n (i + 1) - part x y n i = (y - x) / n := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [part, part]
  push_cast
  field_simp
  ring

/-- **Additivity along the partition.** -/
theorem sum_exponent_part (hx : 0 ≤ x) (hxy : x ≤ y) {n : ℕ} (hn : n ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    ∑ i ∈ range n, Fam.exponent (part x y n i) (part x y n (i + 1)) s = Fam.exponent x y s := by
  have hstep : ∀ i : ℕ, Fam.exponent (part x y n i) (part x y n (i + 1)) s
      = Fam.G (part x y n (i + 1)) s - Fam.G (part x y n i) s := fun i =>
    exponent_eq_G_sub (part_nonneg hx hxy n i) (part_le_succ hxy n i) hs
  simp only [hstep]
  rw [Finset.sum_range_sub (fun i => Fam.G (part x y n i) s), part_self hn, part_zero]
  exact (exponent_eq_G_sub hx hxy hs).symm

/-! ## `Π_n`, the approximating Lévy measures -/

/-- `Π_n = Σ_i μ_{t_i, t_{i+1}}`: a *finite* measure carried by `[0,∞)`, whose total mass is
`n`. It is the Lévy measure of the `n`-th approximant. -/
noncomputable def partitionMeasure (Fam : CascadeCore) (x y : ℝ) (n : ℕ) : Measure ℝ :=
  ∑ i ∈ range n, Fam.repr (part x y n i) (part x y n (i + 1))

instance instIsFiniteMeasurePartitionMeasure (Fam : CascadeCore) (x y : ℝ) (n : ℕ) :
    IsFiniteMeasure (Fam.partitionMeasure x y n) := by
  constructor
  rw [partitionMeasure, Measure.coe_finsetSum, Finset.sum_apply]
  exact ENNReal.sum_lt_top.mpr fun i _ => measure_lt_top _ _

/-- **The `n`-th approximant, computed.** Pairing `1 - e^{-st}` against `Π_n` is exactly the
sum of `1 - \hat\mu_i(s)` over the partition. -/
theorem integral_partitionMeasure (Fam : CascadeCore) (x y : ℝ) (n : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    ∫ t, (1 - Real.exp (-(s * t))) ∂(Fam.partitionMeasure x y n)
      = ∑ i ∈ range n,
          (1 - Real.exp (-(Fam.exponent (part x y n i) (part x y n (i + 1)) s))) := by
  have hint : ∀ i ∈ range n, Integrable (fun t => 1 - Real.exp (-(s * t)))
      (Fam.repr (part x y n i) (part x y n (i + 1))) := fun i _ =>
    (integrable_const (1 : ℝ)).sub (integrable_exp_of_causal (isCausal_repr Fam _ _) hs)
  rw [partitionMeasure, integral_finsetSum_measure hint]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_sub (integrable_const (1 : ℝ))
      (integrable_exp_of_causal (isCausal_repr Fam _ _) hs),
    integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, mul_one]
  congr 1
  exact laplace_repr_eq Fam _ _ hs

/-! ## The estimate

The whole of the null-array argument, in one inequality. The caller supplies the bound `m` on
the partition increments; where `m` comes from — uniform continuity — is separated out below,
so that this step has no analysis in it at all.
-/

/-- **The null-array estimate.** If every partition increment is at most `m`, the `n`-th
approximant is within `m · g_{x,y}(s)` of `g_{x,y}(s)`. -/
theorem abs_sub_integral_partitionMeasure_le (hx : 0 ≤ x) (hxy : x ≤ y) {n : ℕ} (hn : n ≠ 0)
    {s : ℝ} (hs : 0 ≤ s) {m : ℝ}
    (hm : ∀ i ∈ range n, Fam.exponent (part x y n i) (part x y n (i + 1)) s ≤ m) :
    |Fam.exponent x y s - ∫ t, (1 - Real.exp (-(s * t))) ∂(Fam.partitionMeasure x y n)|
      ≤ m * Fam.exponent x y s := by
  set g : ℕ → ℝ := fun i => Fam.exponent (part x y n i) (part x y n (i + 1)) s with hg
  have hgnn : ∀ i, 0 ≤ g i := fun i => exponent_nonneg Fam _ _ hs
  have hsum : ∑ i ∈ range n, g i = Fam.exponent x y s := sum_exponent_part hx hxy hn hs
  -- The difference is a sum of the per-term errors.
  have hdiff : Fam.exponent x y s
      - ∫ t, (1 - Real.exp (-(s * t))) ∂(Fam.partitionMeasure x y n)
      = ∑ i ∈ range n, (g i - (1 - Real.exp (-(g i)))) := by
    rw [integral_partitionMeasure Fam x y n hs, ← hsum, ← Finset.sum_sub_distrib]
  rw [hdiff]
  -- Each error is between `0` and `g i ^ 2 ≤ m * g i`.
  have hlow : 0 ≤ ∑ i ∈ range n, (g i - (1 - Real.exp (-(g i)))) :=
    Finset.sum_nonneg fun i _ => by linarith [one_sub_exp_neg_le (g i)]
  have hhigh : ∑ i ∈ range n, (g i - (1 - Real.exp (-(g i)))) ≤ ∑ i ∈ range n, m * g i := by
    refine Finset.sum_le_sum fun i hi => ?_
    calc g i - (1 - Real.exp (-(g i))) ≤ g i ^ 2 := sub_one_sub_exp_neg_le_sq (hgnn i)
      _ = g i * g i := by ring
      _ ≤ m * g i := mul_le_mul_of_nonneg_right (hm i hi) (hgnn i)
  rw [abs_of_nonneg hlow]
  calc ∑ i ∈ range n, (g i - (1 - Real.exp (-(g i)))) ≤ ∑ i ∈ range n, m * g i := hhigh
    _ = m * Fam.exponent x y s := by rw [← Finset.mul_sum, hsum]

/-! ## The mesh vanishes

The only analysis in the file: `G(\cdot, s)` is continuous on the compact `[x,y]`, hence
uniformly continuous there, so the partition increments — differences of `G` across a gap of
`(y-x)/n` — are eventually uniformly small.
-/

/-- For every `m > 0`, all increments of a fine enough partition are at most `m`. -/
theorem exists_partition_increment_le (hx : 0 ≤ x) (hxy : x ≤ y) {s : ℝ} (hs : 0 ≤ s)
    {m : ℝ} (hm : 0 < m) :
    ∀ᶠ n : ℕ in atTop,
      ∀ i ∈ range n, Fam.exponent (part x y n i) (part x y n (i + 1)) s ≤ m := by
  -- Uniform continuity of `G(·, s)` on `[x, y]`.
  have hsub : Icc x y ⊆ Ici 0 := fun u hu => le_trans hx hu.1
  have hcont : ContinuousOn (fun u => Fam.G u s) (Icc x y) :=
    (continuousOn_G Fam hs).mono hsub
  have huc : UniformContinuousOn (fun u => Fam.G u s) (Icc x y) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hcont
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδb⟩ := huc m hm
  -- Take `n` large enough that the mesh is below `δ`.
  obtain ⟨N, hN⟩ := exists_nat_gt ((y - x) / δ)
  refine Filter.eventually_atTop.mpr ⟨max N 1, fun n hn i hi => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right N 1) hn
  have hnN : (N : ℝ) ≤ n := Nat.cast_le.mpr (le_trans (le_max_left N 1) hn)
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn1
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
  have hi' : i < n := Finset.mem_range.mp hi
  -- The gap between consecutive points is below `δ`.
  have hyx : (0 : ℝ) ≤ y - x := sub_nonneg.mpr hxy
  have hmesh : |part x y n (i + 1) - part x y n i| < δ := by
    rw [part_succ_sub hn0, abs_of_nonneg (div_nonneg hyx hnpos.le)]
    rw [div_lt_iff₀ hnpos]
    have h2 : (y - x) / δ < n := lt_of_lt_of_le hN hnN
    rw [div_lt_iff₀ hδ] at h2
    linarith [h2, mul_comm (n : ℝ) δ]
  -- So the increment of `G` across it is at most `m`.
  have h1 : part x y n (i + 1) ∈ Icc x y := part_mem_Icc hxy hn0 hi'
  have h0 : part x y n i ∈ Icc x y := part_mem_Icc hxy hn0 (le_of_lt hi')
  have hbound := hδb _ h1 _ h0 (by rwa [Real.dist_eq])
  rw [Real.dist_eq] at hbound
  have hstep : Fam.exponent (part x y n i) (part x y n (i + 1)) s
      = Fam.G (part x y n (i + 1)) s - Fam.G (part x y n i) s :=
    exponent_eq_G_sub (part_nonneg hx hxy n i) (part_le_succ hxy n i) hs
  rw [hstep]
  exact le_of_lt (lt_of_le_of_lt (le_abs_self _) hbound)

/-- **The null-array limit.** `g_{x,y}(s)` is the limit of the Lévy exponents of the finite
measures `Π_n`, with no drift and no killing term at any stage.

This is `thm:increments-bernstein` up to the extraction of the limiting triple. -/
theorem tendsto_integral_partitionMeasure (hx : 0 ≤ x) (hxy : x ≤ y) {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun n => ∫ t, (1 - Real.exp (-(s * t))) ∂(Fam.partitionMeasure x y n)) atTop
      (nhds (Fam.exponent x y s)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set g := Fam.exponent x y s with hgdef
  have hgnn : 0 ≤ g := exponent_nonneg Fam x y hs
  -- Choose the increment bound so that `m * g < ε`.
  set m : ℝ := ε / (2 * (g + 1)) with hmdef
  have hm : 0 < m := by positivity
  have hmg : m * g < ε := by
    rw [hmdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (exists_partition_increment_le (Fam := Fam) hx hxy hs hm)
  refine ⟨max N₀ 1, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp (le_trans (le_max_right N₀ 1) hn)
  have hbound := abs_sub_integral_partitionMeasure_le hx hxy hn0 hs
    (hN₀ n (le_trans (le_max_left N₀ 1) hn))
  rw [Real.dist_eq, abs_sub_comm]
  exact lt_of_le_of_lt hbound hmg

end CascadeCore

end Hemigroup
