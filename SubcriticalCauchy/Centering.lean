module

public import SubcriticalCauchy.OffspringWalk
public import SubcriticalCauchy.ScalingSublinear
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# First-order centering and its exact tail decomposition

The source centering uses the signed increment and the absolute cutoff.
Finite-mean dominated convergence proves its first-order asymptotic directly.
The refined asymptotic in terms of the integrated slowly varying tail is proved
in `RefinedCentering`; it is not an assumption of these results.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section
attribute [local instance] Classical.propDecidable

def truncatedIncrementMean (μ : Measure ℕ) (r : ℝ) : ℝ :=
  ∫ k : ℕ, (if |offspringIncrement k| ≤ r then offspringIncrement k else 0) ∂μ

def tailIncrementMean (μ : Measure ℕ) (r : ℝ) : ℝ :=
  ∫ k : ℕ, (if r < |offspringIncrement k| then offspringIncrement k else 0) ∂μ

/-- The paper's centering `b_n`, with no integer rounding in the absolute cutoff. -/
def centering (μ : Measure ℕ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * truncatedIncrementMean μ (a n)

theorem integrable_truncatedIncrement (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) (r : ℝ) :
    Integrable (fun k : ℕ => if |offspringIncrement k| ≤ r then offspringIncrement k else 0) μ := by
  apply (integrable_offspringIncrement μ hm).mono (measurable_of_countable _).aestronglyMeasurable
  exact Eventually.of_forall (fun k => by split_ifs <;> simp)

theorem integrable_tailIncrement (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) (r : ℝ) :
    Integrable (fun k : ℕ => if r < |offspringIncrement k| then offspringIncrement k else 0) μ := by
  apply (integrable_offspringIncrement μ hm).mono (measurable_of_countable _).aestronglyMeasurable
  exact Eventually.of_forall (fun k => by split_ifs <;> simp)

theorem truncated_add_tail_incrementMean (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) (r : ℝ) :
    truncatedIncrementMean μ r + tailIncrementMean μ r = (offspringMean μ).toReal - 1 := by
  rw [truncatedIncrementMean, tailIncrementMean,
    ← integral_add (integrable_truncatedIncrement μ hm r) (integrable_tailIncrement μ hm r),
    ← integral_offspringIncrement μ hm]
  apply integral_congr_ae
  exact Eventually.of_forall (fun k => by
    by_cases hk : |offspringIncrement k| ≤ r
    · simp [hk, not_lt.mpr hk]
    · simp [hk, lt_of_not_ge hk])

theorem truncatedIncrementMean_tendsto (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) :
    Tendsto (fun n => truncatedIncrementMean μ (a n)) atTop (𝓝 ((offspringMean μ).toReal - 1)) := by
  rw [← integral_offspringIncrement μ hm]
  apply tendsto_integral_of_dominated_convergence (fun k : ℕ => ‖offspringIncrement k‖)
    (fun _ => (measurable_of_countable _).aestronglyMeasurable)
    (integrable_offspringIncrement μ hm).norm
  · intro n
    exact Eventually.of_forall (fun k => by split_ifs <;> simp)
  · exact Eventually.of_forall (fun k => by
      apply tendsto_const_nhds.congr'
      filter_upwards [ha.eventually_ge_atTop |offspringIncrement k|] with n hn
      simp [hn])

theorem centering_div_nat_tendsto (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) :
    Tendsto (fun n : ℕ => centering μ a n / (n : ℝ)) atTop
      (𝓝 ((offspringMean μ).toReal - 1)) := by
  apply (truncatedIncrementMean_tendsto μ hm ha).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  simp only [centering]
  exact (mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hn.ne')).symm

theorem centering_shift_eq_tail (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) (a : ℕ → ℝ) (n : ℕ) :
    centering μ a n + (n : ℝ) * (1 - (offspringMean μ).toReal) =
      -(n : ℝ) * tailIncrementMean μ (a n) := by
  have h := truncated_add_tail_incrementMean μ hm (a n)
  unfold centering
  nlinarith

/-- First-order centering asymptotic in Lemma 2.2(ii). -/
theorem centering_ratio_tendsto_one (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ < 1) {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) :
    Tendsto (fun n : ℕ => centering μ a n /
      (-(n : ℝ) * (1 - (offspringMean μ).toReal))) atTop (𝓝 1) := by
  have hfin : offspringMean μ ≠ ∞ := ne_top_of_lt (hm.trans ENNReal.one_lt_top)
  have hmR : (offspringMean μ).toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hfin ENNReal.one_ne_top).mpr hm
  have hne : (offspringMean μ).toReal - 1 ≠ 0 := (sub_neg.mpr hmR).ne
  have h := (centering_div_nat_tendsto μ hfin ha).div_const ((offspringMean μ).toReal - 1)
  rw [div_self hne] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp
  ring

/-- The source's chosen scale supplies the growth premise for first-order centering. -/
theorem paper_centering_ratio_tendsto_one (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsSubcriticalCauchyOffspring μ) {a : ℕ → ℝ}
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => centering μ a n /
      (-(n : ℝ) * (1 - (offspringMean μ).toReal))) atTop (𝓝 1) :=
  centering_ratio_tendsto_one μ hμ.1 (scaling_tendsto_atTop μ hμ ha)

end
end SubcriticalCauchy.Bienayme
