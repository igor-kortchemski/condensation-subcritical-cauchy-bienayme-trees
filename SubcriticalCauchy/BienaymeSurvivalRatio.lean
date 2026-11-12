module

public import SubcriticalCauchy.BienaymeSurvival
public import SubcriticalCauchy.SurvivalLog
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Algebra.Ring.GeomSum

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum

/-!
# Positive survival and its successive ratio

Finite-mean dominated convergence of finite geometric sums proves the ratio
limit directly. No regular variation is required. This proves Lemma 4.4(ii),
but does not establish the slowly varying correction asserted in part (i).
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section
open BGW BGW.LocallyFinite

theorem exists_pos_offspring (μ : Measure ℕ) (hm : 0 < offspringMean μ) :
    ∃ k : ℕ, 0 < k ∧ 0 < μ {k} := by
  by_contra h
  push Not at h
  have hz : offspringMean μ = 0 := by
    rw [offspringMean, lintegral_countable']
    apply ENNReal.tsum_eq_zero.mpr
    intro k
    cases k with
    | zero => simp
    | succ k => simp [le_antisymm (h _ (Nat.succ_pos k)) bot_le]
  exact hm.ne' hz

/-- Positive mean makes every finite generation reachable with positive probability,
even for an infinite-mean offspring law. -/
theorem survival_pos (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : 0 < offspringMean μ) (n : ℕ) : 0 < survival μ n := by
  obtain ⟨k, hk, hμk⟩ := exists_pos_offspring μ hm
  induction n with
  | zero => simp
  | succ n ih =>
    rw [survival_succ]
    apply tsub_pos_of_lt
    calc
      offspringGF μ (1 - survival μ n) < ∑' j : ℕ, μ {j} * 1 := by
        apply ENNReal.tsum_lt_tsum (i := k)
        · exact ne_top_of_le_ne_top ENNReal.one_ne_top (by
            simpa only [offspringGF] using
              (offspringGF_mono μ tsub_le_self).trans_eq (offspringGF_one μ))
        · intro j
          exact mul_le_mul_right (pow_le_one₀ bot_le tsub_le_self) _
        · apply (ENNReal.mul_lt_mul_iff_right hμk.ne' (measure_ne_top _ _)).mpr
          exact pow_lt_one₀ bot_le (ENNReal.sub_lt_self ENNReal.one_ne_top
            (by simp) ih.ne') hk.ne'
      _ = 1 := by simp [tsum_measure_singleton]

theorem survival_toReal_pos (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : 0 < offspringMean μ) (n : ℕ) : 0 < (survival μ n).toReal :=
  ENNReal.toReal_pos (survival_pos μ hm n).ne' (survival_ne_top μ n)

theorem offspringMean_eq_tsum (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    (offspringMean μ).toReal = ∑' k : ℕ, (μ {k}).toReal * (k : ℝ) := by
  rw [offspringMean, lintegral_countable', ENNReal.tsum_toReal_eq]
  · simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, mul_comm]
  · intro k
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top k) (measure_ne_top _ _)

theorem summable_offspringMean (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) : Summable (fun k : ℕ => (μ {k}).toReal * (k : ℝ)) := by
  rw [offspringMean, lintegral_countable'] at hm
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, mul_comm] using
    ENNReal.summable_toReal hm

/-- The finite-geometric-sum representation of the PGF's secant slope at one. -/
def offspringSlope (μ : Measure ℕ) (q : ℝ) : ℝ :=
  ∑' k : ℕ, (μ {k}).toReal * ∑ j ∈ Finset.range k, (1 - q) ^ j

theorem offspringSlope_term_bounds (μ : Measure ℕ) (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (k : ℕ) :
    0 ≤ (μ {k}).toReal * ∑ j ∈ Finset.range k, (1 - q) ^ j ∧
      (μ {k}).toReal * ∑ j ∈ Finset.range k, (1 - q) ^ j ≤
        (μ {k}).toReal * k := by
  constructor
  · positivity
  · apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    calc
      ∑ j ∈ Finset.range k, (1 - q) ^ j ≤ ∑ _j ∈ Finset.range k, (1 : ℝ) :=
        Finset.sum_le_sum (fun j _ => pow_le_one₀ (by linarith) (by linarith))
      _ = k := by simp

theorem summable_offspringSlope (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Summable (fun k : ℕ => (μ {k}).toReal * ∑ j ∈ Finset.range k, (1 - q) ^ j) := by
  exact (summable_offspringMean μ hm).of_nonneg_of_le
    (fun k => (offspringSlope_term_bounds μ q hq0 hq1 k).1)
    (fun k => (offspringSlope_term_bounds μ q hq0 hq1 k).2)

theorem mul_offspringSlope (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    q * offspringSlope μ q = 1 - pgfReal μ (1 - q) := by
  have hp := summable_pgfReal μ 1 (by norm_num) le_rfl
  have hp' : Summable (fun k : ℕ => (μ {k}).toReal) := by simpa using hp
  have hpsum : ∑' k : ℕ, (μ {k}).toReal = 1 := by
    have h := congrArg ENNReal.toReal (tsum_measure_singleton μ)
    simpa only [ENNReal.tsum_toReal_eq (fun k => measure_ne_top μ {k}),
      ENNReal.toReal_one] using h
  rw [offspringSlope, ← (summable_offspringSlope μ hm q hq0 hq1).tsum_mul_left,
    pgfReal_eq_tsum μ _ (by linarith)]
  rw [show 1 - (∑' k : ℕ, (μ {k}).toReal * (1 - q) ^ k) =
      (∑' k : ℕ, (μ {k}).toReal) - (∑' k : ℕ, (μ {k}).toReal * (1 - q) ^ k) by rw [hpsum],
    ← hp'.tsum_sub (summable_pgfReal μ (1 - q) (by linarith) (by linarith))]
  apply tsum_congr
  intro k
  have hgeom := geom_sum_mul_neg (1 - q) k
  simp only [sub_sub_cancel] at hgeom
  calc
    q * ((μ {k}).toReal * ∑ j ∈ Finset.range k, (1 - q) ^ j) =
        (μ {k}).toReal * ((∑ j ∈ Finset.range k, (1 - q) ^ j) * q) := by ring
    _ = _ := by rw [hgeom]; ring

theorem offspringSlope_tendsto (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) {q : ℕ → ℝ}
    (hq0 : ∀ n, 0 ≤ q n) (hq1 : ∀ n, q n ≤ 1)
    (hq : Tendsto q atTop (𝓝 0)) :
    Tendsto (fun n => offspringSlope μ (q n)) atTop (𝓝 (offspringMean μ).toReal) := by
  rw [offspringMean_eq_tsum]
  apply tendsto_tsum_of_dominated_convergence (summable_offspringMean μ hm)
  · intro k
    have hsum : Tendsto (fun n => ∑ j ∈ Finset.range k, (1 - q n) ^ j)
        atTop (𝓝 (∑ _j ∈ Finset.range k, (1 : ℝ))) := by
      apply tendsto_finsetSum
      intro j _
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hq).pow j
    simpa using tendsto_const_nhds.mul hsum
  · exact Filter.Eventually.of_forall (fun n k => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (offspringSlope_term_bounds μ (q n) (hq0 n) (hq1 n) k).1]
      exact (offspringSlope_term_bounds μ (q n) (hq0 n) (hq1 n) k).2)

/-- Successive height-tail ratios tend to the positive subcritical mean. -/
theorem survival_ratio_tendsto (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm0 : 0 < offspringMean μ) (hm1 : offspringMean μ < 1) :
    Tendsto (fun n => (survival μ (n + 1)).toReal / (survival μ n).toReal)
      atTop (𝓝 (offspringMean μ).toReal) := by
  have hm : offspringMean μ ≠ ∞ := ne_top_of_lt (hm1.trans ENNReal.one_lt_top)
  have heq (n : ℕ) : (survival μ (n + 1)).toReal / (survival μ n).toReal =
      offspringSlope μ (survival μ n).toReal := by
    rw [survival_toReal_succ, ← mul_offspringSlope μ hm _ ENNReal.toReal_nonneg
      (ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using survival_le_one μ n))]
    exact mul_div_cancel_left₀ _ (survival_toReal_pos μ hm0 n).ne'
  simp_rw [heq]
  exact offspringSlope_tendsto μ hm (fun _ => ENNReal.toReal_nonneg)
    (fun n => ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using survival_le_one μ n))
    (survival_toReal_tendsto_zero μ hm1)

/-- Lemma 4.4(ii), proved for every positive-mean subcritical law. -/
theorem survival_geometric_bounds (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm0 : 0 < offspringMean μ) (hm1 : offspringMean μ < 1) :
    (∀ n, (survival μ n).toReal ≤ (offspringMean μ).toReal ^ n) ∧
      ∀ η : ℝ, 0 < η → η < (offspringMean μ).toReal →
        ∀ᶠ n in atTop, ((offspringMean μ).toReal - η) ^ n ≤ (survival μ n).toReal := by
  have hm : offspringMean μ ≠ ∞ := ne_top_of_lt (hm1.trans ENNReal.one_lt_top)
  constructor
  · intro n
    simpa only [ENNReal.toReal_pow] using
      ENNReal.toReal_mono (ENNReal.pow_ne_top hm) (survival_le_mean_pow μ n)
  · intro η hη hηm
    exact eventually_pow_le_of_ratio (survival_toReal_pos μ hm0)
      (sub_pos.mpr hηm) (sub_lt_self _ hη) (survival_ratio_tendsto μ hm0 hm1)

/-- The logarithmic height-tail rate for the actual branching law. -/
theorem survival_log_div_nat_tendsto (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm0 : 0 < offspringMean μ) (hm1 : offspringMean μ < 1) :
    Tendsto (fun n => Real.log (survival μ n).toReal / (n : ℝ)) atTop
      (𝓝 (Real.log (offspringMean μ).toReal)) := by
  exact tendsto_log_div_nat_of_ratio (survival_toReal_pos μ hm0)
    (ENNReal.toReal_pos hm0.ne' (ne_top_of_lt (hm1.trans ENNReal.one_lt_top)))
    (survival_ratio_tendsto μ hm0 hm1)

/-- The actual-law sublinearity used in the proof of Proposition 4.5. -/
theorem survival_log_normalized_inv_div_nat (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm0 : 0 < offspringMean μ) (hm1 : offspringMean μ < 1) :
    Tendsto (fun n => Real.log (1 / ((survival μ n).toReal /
      (offspringMean μ).toReal ^ n)) / (n : ℝ)) atTop (𝓝 0) := by
  exact tendsto_log_normalized_inv_div_nat (survival_toReal_pos μ hm0)
    (ENNReal.toReal_pos hm0.ne' (ne_top_of_lt (hm1.trans ENNReal.one_lt_top)))
    (survival_ratio_tendsto μ hm0 hm1)

end
end SubcriticalCauchy.Bienayme
