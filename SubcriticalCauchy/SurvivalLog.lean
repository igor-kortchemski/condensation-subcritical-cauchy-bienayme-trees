module

public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Logarithmic growth from successive ratios

The proof of Proposition `prop:ex`, manuscript line 523, uses the sublinearity
of `log (1 / u n)` when `u n = Q n / m ^ n`. These deterministic lemmas prove
that implication from a positive sequence whose successive ratio tends to `m`.
They do not identify a sequence with a branching-process survival probability.

The proof uses Cesàro averaging of logarithmic increments, instead of the
manuscript's squeeze argument based on its geometric bounds.
-/

@[expose] public section

open Filter
open scoped Topology

namespace SubcriticalCauchy

/-- Converging successive differences give the corresponding linear growth
rate. The finite initial value contributes only a term tending to zero. -/
theorem tendsto_div_nat_of_tendsto_sub {u : ℕ → ℝ} {l : ℝ}
    (h : Tendsto (fun n => u (n + 1) - u n) atTop (𝓝 l)) :
    Tendsto (fun n => u n / (n : ℝ)) atTop (𝓝 l) := by
  have hbase : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * u 0) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_comm] using
      tendsto_const_div_atTop_nhds_zero_nat (u 0)
  simpa only [Finset.sum_range_sub, mul_sub, sub_add_cancel, add_zero,
    div_eq_mul_inv, mul_comm] using h.cesaro.add hbase

/-- A positive limiting successive ratio determines logarithmic growth. -/
theorem tendsto_log_div_nat_of_ratio {q : ℕ → ℝ} {m : ℝ}
    (hq : ∀ n, 0 < q n) (hm : 0 < m)
    (hratio : Tendsto (fun n => q (n + 1) / q n) atTop (𝓝 m)) :
    Tendsto (fun n => Real.log (q n) / (n : ℝ)) atTop (𝓝 (Real.log m)) := by
  apply tendsto_div_nat_of_tendsto_sub
  have h := hratio.log hm.ne'
  exact h.congr' (Eventually.of_forall fun n =>
    Real.log_div (hq (n + 1)).ne' (hq n).ne')

/-- After removing the principal geometric factor, the inverse logarithm is
sublinear. This is the analytic conclusion used at manuscript line 523. -/
theorem tendsto_log_normalized_inv_div_nat {q : ℕ → ℝ} {m : ℝ}
    (hq : ∀ n, 0 < q n) (hm : 0 < m)
    (hratio : Tendsto (fun n => q (n + 1) / q n) atTop (𝓝 m)) :
    Tendsto (fun n => Real.log (1 / (q n / m ^ n)) / (n : ℝ)) atTop (𝓝 0) := by
  have h := (tendsto_const_nhds (x := Real.log m)).sub
    (tendsto_log_div_nat_of_ratio hq hm hratio)
  simp only [sub_self] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnR : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  rw [one_div, Real.log_inv, Real.log_div (hq n).ne' (pow_ne_zero n hm.ne'),
    Real.log_pow, neg_sub, sub_div, mul_div_cancel_left₀ _ hnR]

end SubcriticalCauchy
