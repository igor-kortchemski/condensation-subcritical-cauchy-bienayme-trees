module

public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Analysis.SpecialFunctions.Exp

import Mathlib.Tactic.Linarith

/-!
# Scalar estimates for forest height probabilities

These analytic lemmas justify the scalar limit steps in the proof of Proposition
`prop:height`. For independent trees with single-tree upper-tail probability `q`,
the probability that all `k` tree heights lie below the threshold is `(1-q)^k`.
This file proves the estimates and limits of that expression. Its identification
with an actual independent forest event is supplied by BienaymeForestHeight.
Transfer to conditioned trees remains a separate obligation.
-/

@[expose] public section

open Filter
open scoped Topology

namespace SubcriticalCauchy

/-- The scalar union bound, including an empty collection (`k = 0`). -/
theorem one_sub_pow_bounds {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (k : ℕ) :
    0 ≤ 1 - (1 - q) ^ k ∧ 1 - (1 - q) ^ k ≤ (k : ℝ) * q := by
  constructor
  · exact sub_nonneg.mpr (pow_le_one₀ (sub_nonneg.mpr hq1) (sub_le_self 1 hq0))
  · have hbernoulli : 1 - (k : ℝ) * q ≤ (1 - q) ^ k := by
      simpa only [mul_neg, ← sub_eq_add_neg] using
        one_add_mul_le_pow (show (-2 : ℝ) ≤ -q by linarith) k
    linarith

/-- Exponential upper bound on the probability that none of `k` independent
events of probability `q` occurs, stated purely as a real inequality. -/
theorem one_sub_pow_le_exp {q : ℝ} (hq1 : q ≤ 1) (k : ℕ) :
    (1 - q) ^ k ≤ Real.exp (-((k : ℝ) * q)) := by
  calc
    (1 - q) ^ k ≤ Real.exp (-q) ^ k :=
      pow_le_pow_left₀ (sub_nonneg.mpr hq1) (Real.one_sub_le_exp_neg q) k
    _ = Real.exp (-((k : ℝ) * q)) := by
      rw [← Real.exp_nat_mul, mul_neg]

/-- If the expected number of occurrences tends to zero, the scalar probability
of no occurrence tends to one. -/
theorem tendsto_one_sub_pow_of_mul_tendsto_zero {q : ℕ → ℝ} {k : ℕ → ℕ}
    (hq0 : ∀ n, 0 ≤ q n) (hq1 : ∀ n, q n ≤ 1)
    (hprod : Tendsto (fun n => (k n : ℝ) * q n) atTop (𝓝 0)) :
    Tendsto (fun n => (1 - q n) ^ k n) atTop (𝓝 1) := by
  have herror : Tendsto (fun n => 1 - (1 - q n) ^ k n) atTop (𝓝 0) := by
    exact squeeze_zero
      (fun n => (one_sub_pow_bounds (hq0 n) (hq1 n) (k n)).1)
      (fun n => (one_sub_pow_bounds (hq0 n) (hq1 n) (k n)).2) hprod
  simpa only [sub_sub_cancel, sub_zero] using
    (tendsto_const_nhds (x := (1 : ℝ))).sub herror

/-- If the expected number of occurrences diverges, the scalar probability
of no occurrence tends to zero. -/
theorem tendsto_one_sub_pow_of_mul_tendsto_atTop {q : ℕ → ℝ} {k : ℕ → ℕ}
    (hq1 : ∀ n, q n ≤ 1)
    (hprod : Tendsto (fun n => (k n : ℝ) * q n) atTop atTop) :
    Tendsto (fun n => (1 - q n) ^ k n) atTop (𝓝 0) := by
  have hneg : Tendsto (fun n => -((k n : ℝ) * q n)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hprod
  exact squeeze_zero
    (fun n => pow_nonneg (sub_nonneg.mpr (hq1 n)) (k n))
    (fun n => one_sub_pow_le_exp (hq1 n) (k n))
    (Real.tendsto_exp_atBot.comp hneg)

end SubcriticalCauchy
