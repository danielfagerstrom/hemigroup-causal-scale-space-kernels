/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Hemigroup.Injectivity

/-!
# Convergence of moments forces weak convergence on `[0,1]`

The convergence counterpart of `Injectivity.ext_of_moments`, and the first half of the assembly
that settles whether ledger **A5** must become an interface axiom.

`Injectivity.lean` showed that two finite measures carried by `[0,1]` with the same moments are
equal, by Weierstrass. The same `ε/3` argument, with "equal" replaced by "converging", shows
that measures carried by `[0,1]` whose moments converge converge weakly — and on a compact
carrier that needs **no tightness at all**, which is why this half is separated out.

Tightness re-enters only when this is transported back along `x = e^{-t}`, in the second half:
weak convergence of the pushforwards does not by itself give weak convergence of the originals,
because mass can escape to `t = +∞`, which is exactly the atom at `x = 0` that tightness rules
out.
-/

namespace Hemigroup

open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology ENNReal

/-! ## Polynomials -/

/-- Convergence of moments gives convergence of polynomial integrals, by linearity. -/
theorem tendsto_integral_polynomial_of_moments {ν : ℕ → Measure ℝ} {ν₀ : Measure ℝ}
    [∀ n, IsFiniteMeasure (ν n)] [IsFiniteMeasure ν₀]
    (hcar : ∀ n, (ν n) (Icc (0 : ℝ) 1)ᶜ = 0) (hcar₀ : ν₀ (Icc (0 : ℝ) 1)ᶜ = 0)
    (hmom : ∀ k : ℕ, Tendsto (fun n => ∫ x, x ^ k ∂(ν n)) atTop (𝓝 (∫ x, x ^ k ∂ν₀)))
    (p : Polynomial ℝ) :
    Tendsto (fun n => ∫ x, p.eval x ∂(ν n)) atTop (𝓝 (∫ x, p.eval x ∂ν₀)) := by
  have hint : ∀ (σ : Measure ℝ) [IsFiniteMeasure σ], σ (Icc (0 : ℝ) 1)ᶜ = 0 → ∀ i : ℕ,
      Integrable (fun x : ℝ => p.coeff i * x ^ i) σ := fun σ _ hσ i =>
    integrable_of_carried isCompact_Icc hσ (by fun_prop)
  simp only [Polynomial.eval_eq_sum_range]
  have hsum : ∀ n, ∫ x, ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * x ^ i ∂(ν n)
      = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * ∫ x, x ^ i ∂(ν n) := by
    intro n
    rw [integral_finsetSum _ (fun i _ => hint (ν n) (hcar n) i)]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  have hsum₀ : ∫ x, ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * x ^ i ∂ν₀
      = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * ∫ x, x ^ i ∂ν₀ := by
    rw [integral_finsetSum _ (fun i _ => hint ν₀ hcar₀ i)]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  simp only [hsum]
  rw [hsum₀]
  exact tendsto_finsetSum _ fun i _ => (hmom i).const_mul _

/-! ## The `ε/3` argument -/

/-- **Converging moments force converging integrals**, for measures carried by `[0,1]`.

The compact carrier is what makes this unconditional: Weierstrass approximates any bounded
continuous `f` uniformly on `[0,1]` by a polynomial, and the measures see nothing else. -/
theorem tendsto_integral_of_moments {ν : ℕ → Measure ℝ} {ν₀ : Measure ℝ}
    [∀ n, IsProbabilityMeasure (ν n)] [IsProbabilityMeasure ν₀]
    (hcar : ∀ n, (ν n) (Icc (0 : ℝ) 1)ᶜ = 0) (hcar₀ : ν₀ (Icc (0 : ℝ) 1)ᶜ = 0)
    (hmom : ∀ k : ℕ, Tendsto (fun n => ∫ x, x ^ k ∂(ν n)) atTop (𝓝 (∫ x, x ^ k ∂ν₀)))
    (f : ℝ →ᵇ ℝ) :
    Tendsto (fun n => ∫ x, f x ∂(ν n)) atTop (𝓝 (∫ x, f x ∂ν₀)) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  -- Approximate `f` by a polynomial to within `δ/4` on the carrier.
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 (fun x => f x)
    f.continuous.continuousOn (δ / 4) (by linarith)
  have hb : ∀ x ∈ Icc (0 : ℝ) 1, |f x - p.eval x| ≤ δ / 4 := fun x hx => by
    rw [abs_sub_comm]; exact (hp x hx).le
  -- The two `ε` terms, using that every measure here has mass one.
  have hfν : ∀ n, Integrable (fun x => f x) (ν n) := fun n =>
    integrable_of_carried isCompact_Icc (hcar n) f.continuous
  have hpν : ∀ n, Integrable (fun x => p.eval x) (ν n) := fun n =>
    integrable_of_carried isCompact_Icc (hcar n) (by fun_prop)
  have hstep : ∀ n, |∫ x, f x ∂(ν n) - ∫ x, p.eval x ∂(ν n)| ≤ δ / 4 := by
    intro n
    have h := abs_integral_sub_le_of_carried (hcar n) (hfν n) (hpν n) hb
    simpa using h
  have hstep₀ : |∫ x, f x ∂ν₀ - ∫ x, p.eval x ∂ν₀| ≤ δ / 4 := by
    have h := abs_integral_sub_le_of_carried hcar₀
      (integrable_of_carried isCompact_Icc hcar₀ f.continuous)
      (integrable_of_carried isCompact_Icc hcar₀ (by fun_prop)) hb
    simpa using h
  -- The middle term converges.
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp
    (tendsto_integral_polynomial_of_moments hcar hcar₀ hmom p) (δ / 4) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have hmid : |∫ x, p.eval x ∂(ν n) - ∫ x, p.eval x ∂ν₀| < δ / 4 := by
    simpa [Real.dist_eq] using hN n hn
  have := hstep n
  rw [Real.dist_eq]
  calc |∫ x, f x ∂(ν n) - ∫ x, f x ∂ν₀|
      ≤ |∫ x, f x ∂(ν n) - ∫ x, p.eval x ∂(ν n)|
        + |∫ x, p.eval x ∂(ν n) - ∫ x, p.eval x ∂ν₀|
        + |∫ x, p.eval x ∂ν₀ - ∫ x, f x ∂ν₀| := by
        have h1 := abs_sub_le (∫ x, f x ∂(ν n)) (∫ x, p.eval x ∂(ν n)) (∫ x, p.eval x ∂ν₀)
        have h2 := abs_sub_le (∫ x, f x ∂(ν n)) (∫ x, p.eval x ∂ν₀) (∫ x, f x ∂ν₀)
        linarith
    _ < δ := by
        rw [abs_sub_comm (∫ x, p.eval x ∂ν₀)]
        linarith [hstep₀]

end Hemigroup
