/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Topology.Algebra.Module.Cardinality
import Hemigroup.InversionSymbol

/-!
# `lem:mode-rigidity` (11.25): a profile-dominated mode is pinned to the profile

The eigenvalue recursion `s·g̃(z)·H̃(z-1) = H̃(z)·g̃(z-1)` has the classical period-one ambiguity:
its general solution is `g̃(z) = s^{-z}·H̃(z)·p(z)` with `p` an arbitrary `1`-periodic function.
This file proves that asking `p` to be bounded on **one** period substrip kills the ambiguity, so
that a mode is pinned to the profile up to a single constant.

## The route, and where it departs from the blueprint proof

The blueprint argues meromorphically: patch the translates `p(· - n)` of the base strip into one
meromorphic `1`-periodic function on `ℂ`, transport the substrip's boundedness across every
translate by periodicity, then remove all the poles at once and apply Liouville. That order was
chosen because a zero of `H̃` outside the given substrip is not obviously bounded near *before*
the gluing supplies boundedness there.

The proof here reaches the same place by a different order, and the reordering is what makes it
cheap enough to check. The observation it turns on is that the hypothesis's boundedness already
propagates to the **whole** strip `(0, z_*)` without leaving it: for `z` in the strip there is an
integer `k` with `Re z + k ∈ [c, c+1]`, and every intermediate translate `Re z + j` lies between
`Re z` and `Re z + k`, hence in `(0, z_*)` since that is an interval. So the shift relation
`p(z) = p(z-1)` — which holds wherever `H̃` is nonzero at both ends — carries the bound `M` from
the substrip to every point of the strip whose *whole* integer orbit inside the strip avoids the
zeros of `H̃`. The points it does not reach form a countable set (a countable union of translates
of the countable zero set, `countable_zeros_mellin_profile`), and a countable set in `ℂ` has dense
complement, so the bound extends to every point of the strip off the zeros by continuity alone.

That inverts the blueprint's order: the singularities are removed **first**, on the strip
(`ModeRigidity.ext`, Riemann removability at each isolated zero), and the gluing is then a gluing
of *analytic* functions, which needs no more than the well-definedness of
`ext (z - n)` in `n` — proved by chaining one strip-width at a time, which is exactly where
`z_* > 1`, i.e. (H), is spent. Nothing meromorphic appears anywhere, and Mathlib's
`Complex.differentiableOn_update_limUnder_of_bddAbove` and
`Differentiable.exists_const_forall_eq_of_bounded` are the only analysis used.

The recurring device is `ModeRigidity.norm_le_of_continuousWithinAt`: a bound holding on a set
with countable complement holds everywhere a continuous function is defined. It is used three
times — to spread the substrip bound over the strip, to carry it across the removed
singularities, and to promote the shift relation from "off the zeros" to "everywhere on the
overlap".
-/

namespace Hemigroup

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace ModeRigidity

variable {F : SelfDecomposableExponent} {s c : ℝ} {gt : ℂ → ℂ}

/-- `H̃`, the Mellin transform of the profile, abbreviated for this file. -/
noncomputable def symbol (F : SelfDecomposableExponent) (z : ℂ) : ℂ :=
  mellin (fun u => (F.profile u : ℂ)) z

/-- The **periodic factor** `p(z) = s^z g̃(z)/H̃(z)` of a mode `g̃`. At a zero of `H̃` this is
Lean's junk value `0`; every statement about it below carries `symbol F z ≠ 0`. -/
noncomputable def factor (F : SelfDecomposableExponent) (s : ℝ) (gt : ℂ → ℂ) (z : ℂ) : ℂ :=
  (s : ℂ) ^ z * gt z / symbol F z

/-- The periodic factor with its singularities removed: at a zero of `H̃` the limiting value is
taken instead. Under the hypotheses of `mode_rigidity` this is analytic on the whole strip. -/
noncomputable def ext (F : SelfDecomposableExponent) (s : ℝ) (gt : ℂ → ℂ) (z : ℂ) : ℂ :=
  if symbol F z = 0 then limUnder (𝓝[≠] z) (factor F s gt) else factor F s gt z

/-- The `1`-periodic extension of `ext` to all of `ℂ`: translate `z` back into the substrip
`0 < Re w ≤ 1`, which `z_* > 1` puts inside the strip. -/
noncomputable def per (F : SelfDecomposableExponent) (s : ℝ) (gt : ℂ → ℂ) (z : ℂ) : ℂ :=
  ext F s gt (z - ((⌈z.re⌉ - 1 : ℤ) : ℂ))

/-! ## The strip is an interval -/

/-- The strip is cut out by a condition on the real part alone, and that condition is an
interval: a point whose real part lies between those of two members is a member. -/
theorem mem_strip_of_between {x y t : ℂ} (hx : x ∈ verticalStrip 0 F.zStar)
    (hy : y ∈ verticalStrip 0 F.zStar) (h1 : x.re ≤ t.re) (h2 : t.re ≤ y.re) :
    t ∈ verticalStrip 0 F.zStar :=
  ⟨lt_of_lt_of_le hx.1 h1, ofReal_lt_lower h2 hy.2⟩

/-- The strip where the recursion is stated is the overlap of the strip with its translate. -/
theorem mem_strip_one_iff {z : ℂ} :
    z ∈ verticalStrip 1 F.zStar ↔
      z ∈ verticalStrip 0 F.zStar ∧ z - 1 ∈ verticalStrip 0 F.zStar := by
  have hre : (z - 1).re = z.re - 1 := by simp
  constructor
  · intro h
    have h1 : (1 : ℝ) < z.re := h.1
    refine ⟨⟨by linarith, h.2⟩, ⟨by rw [hre]; linarith, ?_⟩⟩
    exact ofReal_lt_lower (by rw [hre]; linarith) h.2
  · rintro ⟨h0, h1⟩
    have h1' : (0 : ℝ) < (z - 1).re := h1.1
    rw [hre] at h1'
    exact ⟨by linarith, h0.2⟩

/-! ## A bound on a set with countable complement is a bound everywhere -/

/-- If `f` is continuous at `z` along `D` and bounded by `M` on `D`, and `z` is approached by
`D`, then `f z` is bounded by `M`. -/
theorem norm_le_of_continuousWithinAt {f : ℂ → ℂ} {D : Set ℂ} {z : ℂ} {M : ℝ}
    [NeBot (𝓝[D] z)] (hf : ContinuousWithinAt f D z) (hD : ∀ w ∈ D, ‖f w‖ ≤ M) :
    ‖f z‖ ≤ M :=
  le_of_tendsto hf.norm (eventually_nhdsWithin_of_forall hD)

/-- An open set minus a countable set still approaches each of its points: a countable set in `ℂ`
has dense complement. -/
theorem neBot_nhdsWithin_diff {E U : Set ℂ} (hE : E.Countable) (hU : IsOpen U) {z : ℂ}
    (hz : z ∈ U) : (𝓝[U \ E] z).NeBot := by
  have hdense : Dense Eᶜ := Set.Countable.dense_compl ℂ hE
  have h1 : (𝓝[Eᶜ] z).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hdense z)
  have h2 : 𝓝[U ∩ Eᶜ] z = 𝓝[Eᶜ] z :=
    nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hz))
  have hset : U \ E = U ∩ Eᶜ := rfl
  rw [hset, h2]
  exact h1

/-! ## The shift relation -/

/-- Off the zeros of `H̃`, the recursion says exactly that the periodic factor is `1`-periodic. -/
theorem factor_sub_one (hs : 0 < s)
    (hrec : ∀ z : ℂ, z ∈ verticalStrip 1 F.zStar →
      (s : ℂ) * gt z * symbol F (z - 1) = symbol F z * gt (z - 1))
    {z : ℂ} (hz : z ∈ verticalStrip 1 F.zStar) (h0 : symbol F z ≠ 0)
    (h1 : symbol F (z - 1) ≠ 0) :
    factor F s gt z = factor F s gt (z - 1) := by
  have hsne : (s : ℂ) ≠ 0 := by
    simpa using hs.ne'
  have hcpow : (s : ℂ) ^ (z - 1) * (s : ℂ) = (s : ℂ) ^ z := by
    rw [Complex.cpow_sub _ _ hsne, Complex.cpow_one, div_mul_cancel₀ _ hsne]
  have hrec' := hrec z hz
  unfold factor
  rw [div_eq_div_iff h0 h1]
  calc (s : ℂ) ^ z * gt z * symbol F (z - 1)
      = (s : ℂ) ^ (z - 1) * ((s : ℂ) * gt z * symbol F (z - 1)) := by rw [← hcpow]; ring
    _ = (s : ℂ) ^ (z - 1) * (symbol F z * gt (z - 1)) := by rw [hrec']
    _ = (s : ℂ) ^ (z - 1) * gt (z - 1) * symbol F z := by ring

/-- The points of the strip whose whole integer orbit inside the strip avoids the zeros of `H̃`.
The shift relation chains freely along such an orbit. -/
def Good (F : SelfDecomposableExponent) : Set ℂ :=
  {z : ℂ | ∀ n : ℤ, z + (n : ℂ) ∈ verticalStrip 0 F.zStar → symbol F (z + (n : ℂ)) ≠ 0}

/-- Along a good orbit the periodic factor is genuinely constant. -/
theorem factor_add_int (hs : 0 < s)
    (hrec : ∀ z : ℂ, z ∈ verticalStrip 1 F.zStar →
      (s : ℂ) * gt z * symbol F (z - 1) = symbol F z * gt (z - 1))
    {z : ℂ} (hz : z ∈ verticalStrip 0 F.zStar) (hgood : z ∈ Good F) (n : ℤ)
    (hzn : z + (n : ℂ) ∈ verticalStrip 0 F.zStar) :
    factor F s gt (z + (n : ℂ)) = factor F s gt z := by
  induction n using Int.induction_on with
  | zero => simp
  | succ i ih =>
    have hnn : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    have hcast : z + (((i : ℤ) + 1 : ℤ) : ℂ) = (z + ((i : ℤ) : ℂ)) + 1 := by push_cast; ring
    rw [hcast] at hzn ⊢
    have hre1 : (z + ((i : ℤ) : ℂ)).re = z.re + (i : ℝ) := by simp
    have hre2 : (z + ((i : ℤ) : ℂ) + 1).re = z.re + (i : ℝ) + 1 := by simp
    have hmid : z + ((i : ℤ) : ℂ) ∈ verticalStrip 0 F.zStar :=
      mem_strip_of_between hz hzn (by rw [hre1]; linarith) (by rw [hre1, hre2]; linarith)
    have hstep : (z + ((i : ℤ) : ℂ)) + 1 ∈ verticalStrip 1 F.zStar := by
      refine mem_strip_one_iff.mpr ⟨hzn, ?_⟩
      simpa using hmid
    have h0 : symbol F ((z + ((i : ℤ) : ℂ)) + 1) ≠ 0 := by
      have h := hgood ((i : ℤ) + 1) (by rw [hcast]; exact hzn)
      rw [hcast] at h
      exact h
    have h1 : symbol F ((z + ((i : ℤ) : ℂ)) + 1 - 1) ≠ 0 := by
      simpa using hgood (i : ℤ) hmid
    rw [factor_sub_one hs hrec hstep h0 h1]
    simpa using ih hmid
  | pred i ih =>
    have hnn : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    have hcast : z + ((-(i : ℤ) - 1 : ℤ) : ℂ) = (z + ((-(i : ℤ) : ℤ) : ℂ)) - 1 := by
      push_cast; ring
    rw [hcast] at hzn ⊢
    have hre1 : (z + ((-(i : ℤ) : ℤ) : ℂ)).re = z.re - (i : ℝ) := by
      simp; ring
    have hre2 : (z + ((-(i : ℤ) : ℤ) : ℂ) - 1).re = z.re - (i : ℝ) - 1 := by
      simp; ring
    have hmid : z + ((-(i : ℤ) : ℤ) : ℂ) ∈ verticalStrip 0 F.zStar :=
      mem_strip_of_between hzn hz (by rw [hre1, hre2]; linarith) (by rw [hre1]; linarith)
    have hstep : z + ((-(i : ℤ) : ℤ) : ℂ) ∈ verticalStrip 1 F.zStar :=
      mem_strip_one_iff.mpr ⟨hmid, hzn⟩
    have h0 : symbol F (z + ((-(i : ℤ) : ℤ) : ℂ)) ≠ 0 := hgood _ hmid
    have h1 : symbol F (z + ((-(i : ℤ) : ℤ) : ℂ) - 1) ≠ 0 := by
      have h := hgood (-(i : ℤ) - 1) (by rw [hcast]; exact hzn)
      rw [hcast] at h
      exact h
    rw [← factor_sub_one hs hrec hstep h0 h1]
    exact ih hmid

/-- Every point of the strip can be translated by an integer into the closed period substrip,
staying inside the strip. -/
theorem exists_shift_to_substrip (hc0 : 0 < c) (hc1 : ENNReal.ofReal (c + 1) < F.zStar)
    {z : ℂ} :
    ∃ k : ℤ, c ≤ (z + (k : ℂ)).re ∧ (z + (k : ℂ)).re ≤ c + 1 ∧
      z + (k : ℂ) ∈ verticalStrip 0 F.zStar := by
  refine ⟨⌈c - z.re⌉, ?_, ?_, ?_⟩
  · have := Int.le_ceil (c - z.re)
    simp only [Complex.add_re, Complex.intCast_re]
    linarith
  · have := Int.ceil_lt_add_one (c - z.re)
    simp only [Complex.add_re, Complex.intCast_re]
    linarith
  · refine ⟨?_, ?_⟩
    · have := Int.le_ceil (c - z.re)
      simp only [Complex.add_re, Complex.intCast_re]
      linarith
    · have hle : (z + ((⌈c - z.re⌉ : ℤ) : ℂ)).re ≤ c + 1 := by
        have := Int.ceil_lt_add_one (c - z.re)
        simp only [Complex.add_re, Complex.intCast_re]
        linarith
      exact ofReal_lt_lower hle hc1

/-! ## The bound spreads over the strip -/

/-- The points of the strip whose integer orbit inside the strip meets a zero of `H̃`. A countable
union of translates of the (countable) zero set, hence countable, hence with dense complement --
which is all the argument asks of it. -/
def Bad (F : SelfDecomposableExponent) : Set ℂ :=
  ⋃ n : ℤ, (fun w : ℂ => w + (n : ℂ)) ⁻¹' ({w : ℂ | symbol F w = 0} ∩ verticalStrip 0 F.zStar)

theorem countable_bad (hH : F.StandingHypothesis) : (Bad F).Countable := by
  refine Set.countable_iUnion fun n => ?_
  have hinj : Function.Injective (fun z : ℂ => z + (n : ℂ)) := fun a b hab => by simpa using hab
  exact (F.countable_zeros_mellin_profile hH).preimage hinj

theorem mem_good_of_notMem_bad {z : ℂ} (hz : z ∉ Bad F) : z ∈ Good F := by
  intro n hn hn0
  exact hz (Set.mem_iUnion.mpr ⟨n, hn0, hn⟩)

/-! ## The hypotheses of the lemma, bundled

Every step below wants the same seven hypotheses; `M` is the bound the statement's `BddAbove`
supplies, read off once in `mode_rigidity` itself. -/

/-- The data of `lem:mode-rigidity`: a mode `g̃` of the recursion at rate `s`, with periodic factor
bounded by `M` on the period substrip `[c, c+1]` off the zeros of `H̃`. -/
structure Setup (F : SelfDecomposableExponent) (s : ℝ) (gt : ℂ → ℂ) (c M : ℝ) : Prop where
  /-- the standing hypothesis (H) -/
  hH : F.StandingHypothesis
  /-- the rate is positive -/
  hs : 0 < s
  /-- the mode is analytic on the whole strip, with no exceptional set -/
  hgt : AnalyticOnNhd ℂ gt (verticalStrip 0 F.zStar)
  /-- the pole-free eigenvalue recursion -/
  hrec : ∀ z : ℂ, z ∈ verticalStrip 1 F.zStar →
    (s : ℂ) * gt z * symbol F (z - 1) = symbol F z * gt (z - 1)
  /-- the substrip sits inside the strip -/
  hc0 : 0 < c
  /-- ... at both edges -/
  hc1 : ENNReal.ofReal (c + 1) < F.zStar
  /-- the periodic factor is bounded on the substrip, off the zeros -/
  hM : ∀ w : ℂ, c ≤ w.re → w.re ≤ c + 1 → symbol F w ≠ 0 → ‖factor F s gt w‖ ≤ M

variable {M : ℝ}

theorem differentiableAt_symbol (hH : F.StandingHypothesis) {z : ℂ}
    (hz : z ∈ verticalStrip 0 F.zStar) : DifferentiableAt ℂ (symbol F) z :=
  (F.analyticAt_mellin_profile hH hz).differentiableAt

theorem differentiableAt_factor (S : Setup F s gt c M) {z : ℂ}
    (hz : z ∈ verticalStrip 0 F.zStar) (h0 : symbol F z ≠ 0) :
    DifferentiableAt ℂ (factor F s gt) z := by
  have hsne : (s : ℂ) ≠ 0 := by simpa using S.hs.ne'
  have h1 : DifferentiableAt ℂ (fun w : ℂ => (s : ℂ) ^ w) z :=
    differentiableAt_id.const_cpow (Or.inl hsne)
  exact (h1.mul (S.hgt z hz).differentiableAt).div (differentiableAt_symbol S.hH hz) h0

theorem ext_eq_factor {z : ℂ} (h0 : symbol F z ≠ 0) : ext F s gt z = factor F s gt z := by
  simp [ext, h0]

/-- **The bound of the hypothesis holds on the whole strip.** For a point whose integer orbit
inside the strip misses the zeros of `H̃`, the shift relation carries it there from the substrip;
the remaining points form the countable set `Bad F`, and continuity does the rest. -/
theorem norm_factor_le (S : Setup F s gt c M) {z : ℂ}
    (hz : z ∈ verticalStrip 0 F.zStar) (h0 : symbol F z ≠ 0) :
    ‖factor F s gt z‖ ≤ M := by
  have hgood : ∀ w ∈ verticalStrip 0 F.zStar \ Bad F, ‖factor F s gt w‖ ≤ M := by
    rintro w ⟨hw, hwb⟩
    have hwg : w ∈ Good F := mem_good_of_notMem_bad hwb
    obtain ⟨k, hk1, hk2, hk3⟩ := exists_shift_to_substrip (F := F) (z := w) S.hc0 S.hc1
    rw [← factor_add_int S.hs S.hrec hw hwg k hk3]
    exact S.hM _ hk1 hk2 (hwg k hk3)
  haveI : NeBot (𝓝[verticalStrip 0 F.zStar \ Bad F] z) :=
    neBot_nhdsWithin_diff (countable_bad S.hH) (isOpen_verticalStrip 0 F.zStar) hz
  exact norm_le_of_continuousWithinAt
    (differentiableAt_factor S hz h0).continuousAt.continuousWithinAt hgood

/-! ## Removing the singularities -/

/-- `ext` is analytic on the whole strip: away from a zero of `H̃` it *is* the periodic factor,
and at a zero Riemann removability applies, the bound of `norm_factor_le` being exactly the
hypothesis that theorem asks for. -/
theorem differentiableAt_ext (S : Setup F s gt c M) {z : ℂ}
    (hz : z ∈ verticalStrip 0 F.zStar) : DifferentiableAt ℂ (ext F s gt) z := by
  by_cases h0 : symbol F z = 0
  · have hev : ∀ᶠ w in 𝓝 z, w ∈ verticalStrip 0 F.zStar ∧ (w ≠ z → symbol F w ≠ 0) := by
      refine Filter.Eventually.and ((isOpen_verticalStrip 0 F.zStar).mem_nhds hz) ?_
      exact eventually_nhdsWithin_iff.mp (F.eventually_mellin_profile_ne_zero S.hH hz)
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hev
    have hd : DifferentiableOn ℂ (factor F s gt) (Metric.ball z r \ {z}) := by
      rintro w ⟨hw, hwz⟩
      have hw1 := hball (Metric.mem_ball.mp hw)
      exact (differentiableAt_factor S hw1.1 (hw1.2 (by simpa using hwz))).differentiableWithinAt
    have hb : BddAbove (norm ∘ factor F s gt '' (Metric.ball z r \ {z})) := by
      refine ⟨M, ?_⟩
      rintro y ⟨w, ⟨hw, hwz⟩, rfl⟩
      have hw1 := hball (Metric.mem_ball.mp hw)
      exact norm_factor_le S hw1.1 (hw1.2 (by simpa using hwz))
    have hdiff := Complex.differentiableOn_update_limUnder_of_bddAbove
      (Metric.ball_mem_nhds z hr) hd hb
    have heq : ∀ w ∈ Metric.ball z r,
        Function.update (factor F s gt) z (limUnder (𝓝[≠] z) (factor F s gt)) w
          = ext F s gt w := by
      intro w hw
      by_cases hwz : w = z
      · subst hwz; simp [ext, h0]
      · have hw1 := hball (Metric.mem_ball.mp hw)
        simp [ext, hwz, hw1.2 hwz]
    exact (hdiff.congr fun w hw => (heq w hw).symm).differentiableAt (Metric.ball_mem_nhds z hr)
  · have hnear : ∀ᶠ w in 𝓝 z, symbol F w ≠ 0 :=
      (differentiableAt_symbol S.hH hz).continuousAt.eventually_ne h0
    have heq : ext F s gt =ᶠ[𝓝 z] factor F s gt := hnear.mono fun w hw => ext_eq_factor hw
    exact heq.differentiableAt_iff.mpr (differentiableAt_factor S hz h0)

theorem norm_ext_le (S : Setup F s gt c M) {z : ℂ} (hz : z ∈ verticalStrip 0 F.zStar) :
    ‖ext F s gt z‖ ≤ M := by
  haveI : NeBot (𝓝[verticalStrip 0 F.zStar \
      ({w : ℂ | symbol F w = 0} ∩ verticalStrip 0 F.zStar)] z) :=
    neBot_nhdsWithin_diff (F.countable_zeros_mellin_profile S.hH)
      (isOpen_verticalStrip 0 F.zStar) hz
  refine norm_le_of_continuousWithinAt
    (D := verticalStrip 0 F.zStar \ ({w : ℂ | symbol F w = 0} ∩ verticalStrip 0 F.zStar))
    (differentiableAt_ext S hz).continuousAt.continuousWithinAt ?_
  rintro w ⟨hw, hwb⟩
  have hne : symbol F w ≠ 0 := fun h => hwb ⟨h, hw⟩
  rw [ext_eq_factor hne]
  exact norm_factor_le S hw hne

/-! ## Gluing the translates -/

/-- The shift relation, now as an identity of analytic functions with no exceptional set: it holds
off the zeros of `H̃` at both ends, and that is a set with countable complement. -/
theorem ext_sub_one (S : Setup F s gt c M) {z : ℂ} (hz : z ∈ verticalStrip 0 F.zStar)
    (hz1 : z - 1 ∈ verticalStrip 0 F.zStar) : ext F s gt z = ext F s gt (z - 1) := by
  have hzU : z ∈ verticalStrip 1 F.zStar := mem_strip_one_iff.mpr ⟨hz, hz1⟩
  have hEc : (({w : ℂ | symbol F w = 0} ∩ verticalStrip 0 F.zStar) ∪
      ((fun w : ℂ => w - 1) ⁻¹' ({w : ℂ | symbol F w = 0} ∩ verticalStrip 0 F.zStar))).Countable :=
    Set.Countable.union (F.countable_zeros_mellin_profile S.hH)
      ((F.countable_zeros_mellin_profile S.hH).preimage fun a b hab => by simpa using hab)
  haveI : NeBot (𝓝[verticalStrip 1 F.zStar \
      (({w : ℂ | symbol F w = 0} ∩ verticalStrip 0 F.zStar) ∪
        ((fun w : ℂ => w - 1) ⁻¹' ({w : ℂ | symbol F w = 0} ∩ verticalStrip 0 F.zStar)))] z) :=
    neBot_nhdsWithin_diff hEc (isOpen_verticalStrip 1 F.zStar) hzU
  have hsub : DifferentiableAt ℂ (fun w : ℂ => w - 1) z := differentiableAt_id.sub_const 1
  have hcont : ContinuousWithinAt (fun w => ext F s gt w - ext F s gt (w - 1))
      (verticalStrip 1 F.zStar \
        (({w : ℂ | symbol F w = 0} ∩ verticalStrip 0 F.zStar) ∪
          ((fun w : ℂ => w - 1) ⁻¹' ({w : ℂ | symbol F w = 0} ∩ verticalStrip 0 F.zStar)))) z := by
    have h2 : DifferentiableAt ℂ (fun w : ℂ => ext F s gt (w - 1)) z := by
      simpa [Function.comp_def] using (differentiableAt_ext S hz1).comp z hsub
    exact ((differentiableAt_ext S hz).sub h2).continuousAt.continuousWithinAt
  have hbound : ∀ w ∈ verticalStrip 1 F.zStar \
      (({w : ℂ | symbol F w = 0} ∩ verticalStrip 0 F.zStar) ∪
        ((fun w : ℂ => w - 1) ⁻¹' ({w : ℂ | symbol F w = 0} ∩ verticalStrip 0 F.zStar))),
      ‖ext F s gt w - ext F s gt (w - 1)‖ ≤ 0 := by
    rintro w ⟨hw, hwE⟩
    obtain ⟨hw0, hw1⟩ := mem_strip_one_iff.mp hw
    have hne0 : symbol F w ≠ 0 := fun h => hwE (Or.inl ⟨h, hw0⟩)
    have hne1 : symbol F (w - 1) ≠ 0 := fun h => hwE (Or.inr ⟨h, hw1⟩)
    rw [ext_eq_factor hne0, ext_eq_factor hne1, factor_sub_one S.hs S.hrec hw hne0 hne1]
    simp
  have hzero : ‖ext F s gt z - ext F s gt (z - 1)‖ ≤ 0 :=
    norm_le_of_continuousWithinAt (f := fun w => ext F s gt w - ext F s gt (w - 1)) hcont hbound
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hzero)

/-- Every integer translate that lands in the strip gives the same value: the chaining step, and
the place `z_* > 1` is spent, since it is what makes consecutive translates of the strip overlap
so that the chain can pass from one to the next without leaving the strip. -/
theorem ext_sub_int (S : Setup F s gt c M) (z : ℂ) (d : ℤ)
    (h0 : z ∈ verticalStrip 0 F.zStar) (hd : z - (d : ℂ) ∈ verticalStrip 0 F.zStar) :
    ext F s gt (z - (d : ℂ)) = ext F s gt z := by
  induction d using Int.induction_on with
  | zero => simp
  | succ i ih =>
    have hnn : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    have hcast : z - (((i : ℤ) + 1 : ℤ) : ℂ) = (z - ((i : ℤ) : ℂ)) - 1 := by push_cast; ring
    rw [hcast] at hd ⊢
    have hre1 : (z - ((i : ℤ) : ℂ)).re = z.re - (i : ℝ) := by simp; try ring
    have hre2 : ((z - ((i : ℤ) : ℂ)) - 1).re = z.re - (i : ℝ) - 1 := by simp; try ring
    have hmid : z - ((i : ℤ) : ℂ) ∈ verticalStrip 0 F.zStar :=
      mem_strip_of_between hd h0 (by rw [hre1, hre2]; linarith) (by rw [hre1]; linarith)
    rw [← ext_sub_one S hmid hd]
    exact ih hmid
  | pred i ih =>
    have hnn : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    have hcast : z - ((-(i : ℤ) - 1 : ℤ) : ℂ) = (z - ((-(i : ℤ) : ℤ) : ℂ)) + 1 := by
      push_cast; ring
    rw [hcast] at hd ⊢
    have hre1 : (z - ((-(i : ℤ) : ℤ) : ℂ)).re = z.re + (i : ℝ) := by simp; try ring
    have hre2 : ((z - ((-(i : ℤ) : ℤ) : ℂ)) + 1).re = z.re + (i : ℝ) + 1 := by simp; try ring
    have hmid : z - ((-(i : ℤ) : ℤ) : ℂ) ∈ verticalStrip 0 F.zStar :=
      mem_strip_of_between h0 hd (by rw [hre1]; linarith) (by rw [hre1, hre2]; linarith)
    have hone : (z - ((-(i : ℤ) : ℤ) : ℂ)) + 1 - 1 = z - ((-(i : ℤ) : ℤ) : ℂ) := by ring
    rw [ext_sub_one S hd (by rw [hone]; exact hmid), hone]
    exact ih hmid

/-- `z_* > 1` again: translating back by `⌈Re z⌉ - 1` lands in `0 < Re w ≤ 1`, inside the strip. -/
theorem mem_strip_sub_ceil (hH : F.StandingHypothesis) (z : ℂ) :
    z - ((⌈z.re⌉ - 1 : ℤ) : ℂ) ∈ verticalStrip 0 F.zStar := by
  have hre : (z - ((⌈z.re⌉ - 1 : ℤ) : ℂ)).re = z.re - (⌈z.re⌉ : ℝ) + 1 := by
    simp; try ring
  refine ⟨?_, ?_⟩
  · rw [hre]
    have := Int.ceil_lt_add_one z.re
    linarith
  · refine lt_of_le_of_lt ?_ hH.2
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hre]
    have := Int.le_ceil z.re
    linarith

theorem per_eq (S : Setup F s gt c M) (z : ℂ) (n : ℤ)
    (h : z - (n : ℂ) ∈ verticalStrip 0 F.zStar) :
    per F s gt z = ext F s gt (z - (n : ℂ)) := by
  have hmem := mem_strip_sub_ceil S.hH z
  have hcast : (z - (n : ℂ)) - (((⌈z.re⌉ - 1) - n : ℤ) : ℂ) = z - ((⌈z.re⌉ - 1 : ℤ) : ℂ) := by
    push_cast; ring
  have h' := ext_sub_int S (z - (n : ℂ)) ((⌈z.re⌉ - 1) - n) h (by rw [hcast]; exact hmem)
  rw [hcast] at h'
  exact h'

theorem differentiable_per (S : Setup F s gt c M) : Differentiable ℂ (per F s gt) := by
  intro z
  have hmem : z - ((⌈z.re⌉ - 1 : ℤ) : ℂ) ∈ verticalStrip 0 F.zStar := mem_strip_sub_ceil S.hH z
  have hU : IsOpen ((fun w : ℂ => w - ((⌈z.re⌉ - 1 : ℤ) : ℂ)) ⁻¹' verticalStrip 0 F.zStar) :=
    (isOpen_verticalStrip 0 F.zStar).preimage (continuous_id.sub continuous_const)
  have heq : per F s gt =ᶠ[𝓝 z] fun w => ext F s gt (w - ((⌈z.re⌉ - 1 : ℤ) : ℂ)) := by
    filter_upwards [hU.mem_nhds hmem] with w hw
    exact per_eq S w (⌈z.re⌉ - 1) hw
  have hsub : DifferentiableAt ℂ (fun w : ℂ => w - ((⌈z.re⌉ - 1 : ℤ) : ℂ)) z :=
    differentiableAt_id.sub_const _
  have hd : DifferentiableAt ℂ (fun w : ℂ => ext F s gt (w - ((⌈z.re⌉ - 1 : ℤ) : ℂ))) z := by
    simpa [Function.comp_def] using (differentiableAt_ext S hmem).comp z hsub
  exact heq.differentiableAt_iff.mpr hd

theorem isBounded_range_per (S : Setup F s gt c M) :
    Bornology.IsBounded (Set.range (per F s gt)) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨M, ?_⟩
  rintro y ⟨z, rfl⟩
  rw [per_eq S z (⌈z.re⌉ - 1) (mem_strip_sub_ceil S.hH z)]
  exact norm_ext_le S (mem_strip_sub_ceil S.hH z)

/-- Liouville, and then the identity theorem in the cheap form the isolated zeros allow: the two
analytic functions `s^z g̃(z)` and `κ H̃(z)` agree off the zeros of `H̃`, hence everywhere. -/
theorem exists_const (S : Setup F s gt c M) :
    ∃ κ : ℂ, ∀ z ∈ verticalStrip 0 F.zStar, (s : ℂ) ^ z * gt z = κ * symbol F z := by
  have hsne : (s : ℂ) ≠ 0 := by simpa using S.hs.ne'
  obtain ⟨κ, hκ⟩ := Differentiable.exists_const_forall_eq_of_bounded
    (differentiable_per S) (isBounded_range_per S)
  have hoff : ∀ z ∈ verticalStrip 0 F.zStar, symbol F z ≠ 0 →
      (s : ℂ) ^ z * gt z = κ * symbol F z := by
    intro z hz h0
    have hext : ext F s gt z = κ := by
      have := per_eq S z 0 (by simpa using hz)
      simp only [Int.cast_zero, sub_zero] at this
      rw [← this]
      exact hκ z
    rw [ext_eq_factor h0, factor, div_eq_iff h0] at hext
    exact hext
  refine ⟨κ, fun z hz => ?_⟩
  by_cases h0 : symbol F z = 0
  · have hdiff : DifferentiableAt ℂ (fun w : ℂ => (s : ℂ) ^ w * gt w - κ * symbol F w) z := by
      have h1 : DifferentiableAt ℂ (fun w : ℂ => (s : ℂ) ^ w) z :=
        differentiableAt_id.const_cpow (Or.inl hsne)
      exact (h1.mul (S.hgt z hz).differentiableAt).sub
        ((differentiableAt_symbol S.hH hz).const_mul κ)
    have hev : (fun w : ℂ => (s : ℂ) ^ w * gt w - κ * symbol F w) =ᶠ[𝓝[≠] z] fun _ => 0 := by
      filter_upwards [F.eventually_mellin_profile_ne_zero S.hH hz,
        nhdsWithin_le_nhds ((isOpen_verticalStrip 0 F.zStar).mem_nhds hz)] with w hw1 hw2
      rw [hoff w hw2 hw1, sub_self]
    have hlim := hdiff.continuousAt.continuousWithinAt (s := {z}ᶜ)
    have hzero : (s : ℂ) ^ z * gt z - κ * symbol F z = 0 :=
      tendsto_nhds_unique hlim (Filter.Tendsto.congr' hev.symm tendsto_const_nhds)
    exact sub_eq_zero.mp hzero
  · exact hoff z hz h0

end ModeRigidity

/-- **`lem:mode-rigidity`** (11.25): a mode of the eigenvalue recursion whose periodic factor is
bounded on one period substrip -- profile-dominated, in the blueprint's phrase -- is pinned to the
profile up to a single constant.

The proof is in `Hemigroup/ModeRigidity.lean`; its route is the blueprint's proof with the order
of the middle two steps exchanged (boundedness first, on the strip; gluing afterwards, of analytic
rather than meromorphic pieces), which is what makes the patching construction the blueprint
prices at a session's work come out as the well-definedness of `ModeRigidity.ext (z - n)` in `n`.
Nothing beyond Lean core is used. -/
theorem mode_rigidity (F : SelfDecomposableExponent) (hH : F.StandingHypothesis) {s : ℝ}
    (hs : 0 < s) {gt : ℂ → ℂ}
    (hgt : AnalyticOnNhd ℂ gt (verticalStrip 0 F.zStar))
    (hrec : ∀ z : ℂ, z ∈ verticalStrip 1 F.zStar →
      (s : ℂ) * gt z * mellin (fun u => (F.profile u : ℂ)) (z - 1)
        = mellin (fun u => (F.profile u : ℂ)) z * gt (z - 1))
    {c : ℝ} (hc0 : 0 < c) (hc1 : ENNReal.ofReal (c + 1) < F.zStar)
    (hbdd : BddAbove ((fun z : ℂ =>
        ‖(s : ℂ) ^ z * gt z / mellin (fun u => (F.profile u : ℂ)) z‖) ''
      ({z : ℂ | c ≤ z.re ∧ z.re ≤ c + 1} \
        {z : ℂ | mellin (fun u => (F.profile u : ℂ)) z = 0}))) :
    ∃ κ : ℂ, ∀ z : ℂ, z ∈ verticalStrip 0 F.zStar →
      gt z = κ * (s : ℂ) ^ (-z) * mellin (fun u => (F.profile u : ℂ)) z := by
  obtain ⟨M, hMub⟩ := hbdd
  have hM : ∀ w : ℂ, c ≤ w.re → w.re ≤ c + 1 → ModeRigidity.symbol F w ≠ 0 →
      ‖ModeRigidity.factor F s gt w‖ ≤ M := fun w h1 h2 h3 =>
    hMub (Set.mem_image_of_mem _ ⟨⟨h1, h2⟩, h3⟩)
  have S : ModeRigidity.Setup F s gt c M := ⟨hH, hs, hgt, hrec, hc0, hc1, hM⟩
  obtain ⟨κ, hκ⟩ := ModeRigidity.exists_const S
  have hsne : (s : ℂ) ≠ 0 := by simpa using hs.ne'
  have hpow : ∀ z : ℂ, (s : ℂ) ^ z ≠ 0 := fun z h => hsne ((Complex.cpow_eq_zero_iff _ _).mp h).1
  refine ⟨κ, fun z hz => ?_⟩
  have h := hκ z hz
  have hsym : ModeRigidity.symbol F z = mellin (fun u => (F.profile u : ℂ)) z := rfl
  rw [hsym] at h
  calc gt z = ((s : ℂ) ^ z)⁻¹ * ((s : ℂ) ^ z * gt z) := by
        rw [← mul_assoc, inv_mul_cancel₀ (hpow z), one_mul]
    _ = ((s : ℂ) ^ z)⁻¹ * (κ * mellin (fun u => (F.profile u : ℂ)) z) := by rw [h]
    _ = κ * (s : ℂ) ^ (-z) * mellin (fun u => (F.profile u : ℂ)) z := by
        rw [Complex.cpow_neg]; ring

end Hemigroup
