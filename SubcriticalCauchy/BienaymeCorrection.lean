module

public import SubcriticalCauchy.BienaymeSurvivalRatio
public import Mathlib.Analysis.Normed.Group.FunctionSeries

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# The elementary survival correction function

The correction in Lemma 4.4(i) is the mean minus the secant slope of the
offspring PGF. Finite mean gives continuity, monotonicity and vanishing at zero.
Positive mass at an offspring count at least two gives strict positivity.
Slow variation and equivalence to the integrated tail remain separate,
heavy-tail-dependent obligations.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section
open BGW

/-- The correction in the actual survival recurrence, extended to zero. -/
def survivalCorrection (μ : Measure ℕ) (q : ℝ) : ℝ :=
  (offspringMean μ).toReal - offspringSlope μ q

theorem offspringSlope_bounds (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ offspringSlope μ q ∧ offspringSlope μ q ≤ (offspringMean μ).toReal := by
  constructor
  · exact tsum_nonneg (fun k => (offspringSlope_term_bounds μ q hq0 hq1 k).1)
  · rw [offspringMean_eq_tsum]
    exact (summable_offspringSlope μ hm q hq0 hq1).tsum_le_tsum
      (fun k => (offspringSlope_term_bounds μ q hq0 hq1 k).2)
      (summable_offspringMean μ hm)

theorem survivalCorrection_bounds (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ survivalCorrection μ q ∧ survivalCorrection μ q ≤ (offspringMean μ).toReal := by
  obtain ⟨h0, h1⟩ := offspringSlope_bounds μ hm hq0 hq1
  unfold survivalCorrection
  constructor <;> linarith

theorem offspringSlope_antitoneOn (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) : AntitoneOn (offspringSlope μ) (Set.Icc 0 1) := by
  intro x hx y hy hxy
  apply (summable_offspringSlope μ hm y hy.1 hy.2).tsum_le_tsum _
    (summable_offspringSlope μ hm x hx.1 hx.2)
  intro k
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  apply Finset.sum_le_sum
  intro j _
  exact pow_le_pow_left₀ (sub_nonneg.mpr hy.2) (sub_le_sub_left hxy 1) j

theorem survivalCorrection_monotoneOn (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) : MonotoneOn (survivalCorrection μ) (Set.Icc 0 1) := by
  intro x hx y hy hxy
  exact sub_le_sub_left (offspringSlope_antitoneOn μ hm hx hy hxy) _

@[simp] theorem offspringSlope_zero (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    offspringSlope μ 0 = (offspringMean μ).toReal := by
  simpa [offspringSlope] using (offspringMean_eq_tsum μ).symm

@[simp] theorem survivalCorrection_zero (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    survivalCorrection μ 0 = 0 := by simp [survivalCorrection]

theorem offspringSlope_continuousOn (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) : ContinuousOn (offspringSlope μ) (Set.Icc 0 1) := by
  have hc (k : ℕ) : Continuous (fun q : ℝ =>
      (μ {k}).toReal * ∑ j ∈ Finset.range k, (1 - q) ^ j) :=
    continuous_const.mul (continuous_finsetSum _ (fun j _ =>
      (continuous_const.sub continuous_id).pow j))
  exact continuousOn_tsum (fun k => (hc k).continuousOn) (summable_offspringMean μ hm)
    (fun k q hq => by
      rw [Real.norm_eq_abs, abs_of_nonneg (offspringSlope_term_bounds μ q hq.1 hq.2 k).1]
      exact (offspringSlope_term_bounds μ q hq.1 hq.2 k).2)

theorem survivalCorrection_continuousOn (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) : ContinuousOn (survivalCorrection μ) (Set.Icc 0 1) :=
  continuousOn_const.sub (offspringSlope_continuousOn μ hm)

/-- The correction tends to zero along positive real arguments, not only along
the survival sequence. -/
theorem survivalCorrection_tendsto_zero (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) :
    Tendsto (survivalCorrection μ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hc := (survivalCorrection_continuousOn μ hm) 0
    (show (0 : ℝ) ∈ Set.Icc 0 1 from ⟨le_rfl, zero_le_one⟩)
  rw [ContinuousWithinAt, survivalCorrection_zero] at hc
  apply hc.mono_left
  apply nhdsWithin_le_of_mem
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iic_mem_nhds (show (0 : ℝ) < 1 from zero_lt_one))] with q hq0 hq1
  exact ⟨hq0.le, hq1⟩

/-- A genuine branching offspring count makes the correction strictly positive
away from zero. This hypothesis is necessary: a law supported on zero and one
has identically zero correction. -/
theorem survivalCorrection_pos (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) (hbranch : ∃ k : ℕ, 2 ≤ k ∧ 0 < μ {k})
    {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) : 0 < survivalCorrection μ q := by
  obtain ⟨k, hk, hμk⟩ := hbranch
  have hgeo : (∑ j ∈ Finset.range k, (1 - q) ^ j) < (k : ℝ) := by
    calc
      _ < ∑ _j ∈ Finset.range k, (1 : ℝ) := by
        apply Finset.sum_lt_sum
        · intro j _
          exact pow_le_one₀ (sub_nonneg.mpr hq1) (sub_le_self _ hq0.le)
        · refine ⟨1, Finset.mem_range.mpr (Nat.lt_of_lt_of_le (Nat.lt_succ_self 1) hk), ?_⟩
          simpa using sub_lt_self (1 : ℝ) hq0
      _ = k := by simp
  have hp : 0 < (μ {k}).toReal := ENNReal.toReal_pos hμk.ne' (measure_ne_top _ _)
  have hlt := (summable_offspringSlope μ hm q hq0.le hq1).tsum_lt_tsum
    (fun j => (offspringSlope_term_bounds μ q hq0.le hq1 j).2)
    (mul_lt_mul_of_pos_left hgeo hp) (summable_offspringMean μ hm)
  rw [← offspringMean_eq_tsum] at hlt
  exact sub_pos.mpr hlt

theorem survivalCorrection_lt_mean (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) (hm0 : 0 < offspringMean μ)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    survivalCorrection μ q < (offspringMean μ).toReal := by
  obtain ⟨k, hk, hμk⟩ := exists_pos_offspring μ hm0
  have hgeo : 1 ≤ ∑ j ∈ Finset.range k, (1 - q) ^ j := by
    calc
      (1 : ℝ) = (1 - q) ^ 0 := by simp
      _ ≤ _ := Finset.single_le_sum (fun j _ => pow_nonneg (sub_nonneg.mpr hq1) j)
        (Finset.mem_range.mpr hk)
  have hp : 0 < (μ {k}).toReal := ENNReal.toReal_pos hμk.ne' (measure_ne_top _ _)
  have hs : 0 < offspringSlope μ q :=
    (summable_offspringSlope μ hm q hq0 hq1).tsum_pos
      (fun j => (offspringSlope_term_bounds μ q hq0 hq1 j).1) k
      (mul_pos hp (lt_of_lt_of_le zero_lt_one hgeo))
  exact sub_lt_self _ hs

/-- The PGF remainder identity, with endpoints included by the zero extension. -/
theorem pgfReal_survivalCorrection (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    pgfReal μ (1 - q) = 1 - (offspringMean μ).toReal * q + q * survivalCorrection μ q := by
  have h := mul_offspringSlope μ hm q hq0 hq1
  unfold survivalCorrection
  nlinarith

/-- Exact recurrence on the constructed Bienaymé law, with no heavy-tail or
subcriticality hypothesis needed for this algebraic identity. -/
theorem survival_toReal_succ_correction (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) (n : ℕ) :
    (survival μ (n + 1)).toReal = (survival μ n).toReal *
      ((offspringMean μ).toReal - survivalCorrection μ (survival μ n).toReal) := by
  rw [survival_toReal_succ, ← mul_offspringSlope μ hm _ ENNReal.toReal_nonneg
    (ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using survival_le_one μ n))]
  simp only [survivalCorrection, sub_sub_cancel]

theorem survivalCorrection_one (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) :
    survivalCorrection μ 1 = (offspringMean μ).toReal - 1 + (μ {0}).toReal := by
  have h := mul_offspringSlope μ hm 1 zero_le_one le_rfl
  simp [pgfReal, offspringGF_zero] at h
  unfold survivalCorrection
  rw [h]
  ring

/-- Iterating the actual correction recurrence gives its finite-product form,
including the empty product at generation zero. -/
theorem survival_toReal_eq_prod_correction (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) (n : ℕ) :
    (survival μ n).toReal = ∏ k ∈ Finset.range n,
      ((offspringMean μ).toReal - survivalCorrection μ (survival μ k).toReal) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [survival_toReal_succ_correction μ hm n, Finset.prod_range_succ]
    exact congrArg (fun x : ℝ => x *
      ((offspringMean μ).toReal - survivalCorrection μ (survival μ n).toReal)) ih

/-- On natural offspring counts, `Ioi j` is the tail `[j+1,∞)`. -/
theorem offspringTail_eq_tsum (μ : Measure ℕ) (j : ℕ) :
    μ (Set.Ioi j) = ∑' k : ℕ, if j < k then μ {k} else 0 := by
  classical
  have hset : Set.Ioi j = ⋃ k : ℕ, if j < k then ({k} : Set ℕ) else ∅ := by
    ext k
    simp only [Set.mem_Ioi, Set.mem_iUnion]
    constructor
    · intro hk
      exact ⟨k, by simp [hk]⟩
    · rintro ⟨i, hi⟩
      by_cases hji : j < i
      · simp only [ite_eq_left hji, Set.mem_singleton_iff] at hi
        simpa [hi] using hji
      · simp [hji] at hi
  have hd : Pairwise (fun a b : ℕ =>
      Disjoint (if j < a then ({a} : Set ℕ) else ∅)
        (if j < b then ({b} : Set ℕ) else ∅)) := by
    intro a b hab
    by_cases ha : j < a <;> by_cases hb : j < b <;>
      simp [ha, hb, hab]
  have hm (k : ℕ) : MeasurableSet (if j < k then ({k} : Set ℕ) else ∅) := by
    by_cases hk : j < k <;> simp [hk]
  rw [hset, measure_iUnion hd hm]
  apply tsum_congr
  intro k
  by_cases hk : j < k <;> simp [hk]

/-- Nonnegative Tonelli identity behind the intended tail-sum PGF formula.
It is valid even at infinite `s` or infinite mean. The source's intermediate
double sum has swapped mass/power indices; this is the intended ordering. -/
theorem offspringSlopeENN_eq_tsum_tail (μ : Measure ℕ) (s : ℝ≥0∞) :
    (∑' k : ℕ, μ {k} * ∑ j ∈ Finset.range k, s ^ j) =
      ∑' j : ℕ, μ (Set.Ioi j) * s ^ j := by
  classical
  have hrow (k : ℕ) : μ {k} * ∑ j ∈ Finset.range k, s ^ j =
      ∑' j : ℕ, if j < k then μ {k} * s ^ j else 0 := by
    rw [Finset.mul_sum]
    symm
    rw [tsum_eq_sum (s := Finset.range k) (fun j hj => by
      have hj' : ¬ j < k := by simpa using hj
      simp [hj'])]
    exact Finset.sum_congr rfl (fun j hj => by simp [Finset.mem_range.mp hj])
  simp_rw [hrow]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro j
  rw [offspringTail_eq_tsum, ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro k
  by_cases hk : j < k <;> simp [hk]

/-- Tail-sum formula for the mean, including infinite means. -/
theorem offspringMean_eq_tsum_tail (μ : Measure ℕ) :
    offspringMean μ = ∑' j : ℕ, μ (Set.Ioi j) := by
  rw [offspringMean, lintegral_countable']
  simpa [mul_comm] using offspringSlopeENN_eq_tsum_tail μ 1

theorem summable_offspringTail (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) : Summable (fun j : ℕ => (μ (Set.Ioi j)).toReal) := by
  rw [offspringMean_eq_tsum_tail] at hm
  exact ENNReal.summable_toReal hm

theorem offspringMean_toReal_eq_tsum_tail (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    (offspringMean μ).toReal = ∑' j : ℕ, (μ (Set.Ioi j)).toReal := by
  rw [offspringMean_eq_tsum_tail, ENNReal.tsum_toReal_eq (fun j => measure_ne_top μ (Set.Ioi j))]

theorem summable_offspringTail_geometric (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Summable (fun j : ℕ => (μ (Set.Ioi j)).toReal * (1 - q) ^ j) := by
  apply (summable_offspringTail μ hm).of_nonneg_of_le
  · intro j
    exact mul_nonneg ENNReal.toReal_nonneg (pow_nonneg (sub_nonneg.mpr hq1) j)
  · intro j
    simpa using mul_le_mul_of_nonneg_left
      (pow_le_one₀ (sub_nonneg.mpr hq1) (sub_le_self 1 hq0))
      (show 0 ≤ (μ (Set.Ioi j)).toReal from ENNReal.toReal_nonneg)

/-- The tail generating series is the PGF's secant slope. Finite mean makes the
series genuinely summable, as recorded by summable_offspringTail_geometric. -/
theorem offspringSlope_eq_tsum_tail (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    offspringSlope μ q = ∑' j : ℕ, (μ (Set.Ioi j)).toReal * (1 - q) ^ j := by
  have _hs := summable_offspringTail_geometric μ hm hq0 hq1
  have hinner (k : ℕ) : (∑ j ∈ Finset.range k, ENNReal.ofReal (1 - q) ^ j) ≠ ∞ :=
    ENNReal.sum_ne_top.mpr (fun j _ => ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hgeom (k : ℕ) : (∑ j ∈ Finset.range k, ENNReal.ofReal (1 - q) ^ j).toReal =
      ∑ j ∈ Finset.range k, (1 - q) ^ j := by
    rw [ENNReal.toReal_sum (fun j _ => ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
    simp only [ENNReal.toReal_pow, ENNReal.toReal_ofReal (sub_nonneg.mpr hq1)]
  calc
    offspringSlope μ q =
        (∑' k : ℕ, μ {k} * ∑ j ∈ Finset.range k, ENNReal.ofReal (1 - q) ^ j).toReal := by
      rw [ENNReal.tsum_toReal_eq (fun k => ENNReal.mul_ne_top (measure_ne_top _ _) (hinner k))]
      simp only [offspringSlope, ENNReal.toReal_mul, hgeom]
    _ = (∑' j : ℕ, μ (Set.Ioi j) * ENNReal.ofReal (1 - q) ^ j).toReal :=
      congrArg ENNReal.toReal (offspringSlopeENN_eq_tsum_tail μ _)
    _ = _ := by
      rw [ENNReal.tsum_toReal_eq (fun j => ENNReal.mul_ne_top (measure_ne_top _ _)
        (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))]
      simp only [ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hq1)]

/-- The intended source identity at `eq:l(s)`. -/
theorem survivalCorrection_eq_tsum_tail (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    survivalCorrection μ q = (offspringMean μ).toReal -
      ∑' j : ℕ, (μ (Set.Ioi j)).toReal * (1 - q) ^ j := by
  rw [survivalCorrection, offspringSlope_eq_tsum_tail μ hm hq0 hq1]

/-- A nonnegative-kernel form of the correction, useful for the remaining
heavy-tail asymptotics. -/
theorem survivalCorrection_eq_tsum_kernel (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    survivalCorrection μ q =
      ∑' j : ℕ, (μ (Set.Ioi j)).toReal * (1 - (1 - q) ^ j) := by
  rw [survivalCorrection_eq_tsum_tail μ hm hq0 hq1, offspringMean_toReal_eq_tsum_tail,
    ← (summable_offspringTail μ hm).tsum_sub (summable_offspringTail_geometric μ hm hq0 hq1)]
  exact tsum_congr (fun j => by ring)

end
end SubcriticalCauchy.Bienayme
