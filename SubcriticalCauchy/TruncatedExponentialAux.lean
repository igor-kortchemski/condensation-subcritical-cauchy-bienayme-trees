module

public import SubcriticalCauchy.PotterBounds

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Elementary truncated-moment estimates

Finite-prefix formulas for the truncated exponential estimate.  No axioms or
pointwise replacements of the slowly varying function are used.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace SubcriticalCauchy.Bienayme

lemma exp_le_one_add_add_sq_mul_exp_max (x : ℝ) :
    Real.exp x ≤ 1 + x + x ^ 2 * Real.exp (max x 0) := by
  rcases le_total x 0 with hx | hx
  · rw [max_eq_right hx, Real.exp_zero, mul_one]
    rcases le_total x (-1) with hx1 | hx1
    · calc
        Real.exp x ≤ 1 := Real.exp_le_one_iff.mpr hx
        _ ≤ 1 + x + x ^ 2 := by nlinarith
    · have hE : (1 - x) * Real.exp x ≤ 1 := by
        have h := Real.add_one_le_exp (-x)
        have hmul := mul_le_mul_of_nonneg_right h (Real.exp_pos x).le
        rw [← Real.exp_add] at hmul
        simpa [add_comm, sub_eq_add_neg] using hmul
      have he : Real.exp x ≤ 1 / (1 - x) := by
        exact (le_div_iff₀ (by linarith)).mpr (by nlinarith)
      calc
        Real.exp x ≤ 1 / (1 - x) := he
        _ ≤ 1 + x + x ^ 2 := by
          rw [div_le_iff₀ (by linarith : 0 < 1 - x)]
          nlinarith [sq_nonneg x]
  · rw [max_eq_left hx]
    rcases le_total 1 x with hx1 | hx1
    · have hs : (1 : ℝ) ≤ x ^ 2 := by nlinarith
      calc
        Real.exp x = 1 * Real.exp x := by ring
        _ ≤ x ^ 2 * Real.exp x := mul_le_mul_of_nonneg_right hs (Real.exp_pos _).le
        _ ≤ 1 + x + x ^ 2 * Real.exp x := by nlinarith [sq_nonneg x, Real.exp_pos x]
    · have hE : (1 - x) * Real.exp x ≤ 1 := by
        have h := Real.add_one_le_exp (-x)
        have hmul := mul_le_mul_of_nonneg_right h (Real.exp_pos x).le
        rw [← Real.exp_add] at hmul
        simpa [add_comm, sub_eq_add_neg] using hmul
      have hmul := mul_le_mul_of_nonneg_left hE (by linarith : 0 ≤ 1 + x)
      nlinarith

lemma integrable_truncated_exp (μ : Measure ℕ) [IsFiniteMeasure μ] (t B m : ℝ) (ht : 0 ≤ t) :
    Integrable (fun k : ℕ => if (k : ℝ) ≤ B then Real.exp (t * ((k : ℝ) - m)) else 0) μ := by
  refine Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable
    (Real.exp (t * (B + |m|))) ?_
  filter_upwards [] with k
  by_cases hk : (k : ℝ) ≤ B
  · simp only [hk, ite_true, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hm : -m ≤ |m| := neg_le_abs m
    exact mul_le_mul_of_nonneg_left (by linarith) ht
  · simp [hk, (Real.exp_pos _).le]

lemma integrable_truncated_sub (μ : Measure ℕ) [IsFiniteMeasure μ] (B m : ℝ) :
    Integrable (fun k : ℕ => if (k : ℝ) ≤ B then (k : ℝ) - m else 0) μ := by
  refine Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable
    (|B| + |m|) ?_
  filter_upwards [] with k
  by_cases hk : (k : ℝ) ≤ B
  · simp only [hk, ite_true, Real.norm_eq_abs]
    calc
      |(k : ℝ) - m| ≤ |(k : ℝ)| + |m| := abs_sub _ _
      _ ≤ |B| + |m| := add_le_add (by simpa using hk.trans (le_abs_self B)) le_rfl
  · simp [hk, add_nonneg (abs_nonneg B) (abs_nonneg m)]

lemma integrable_truncated_sq (μ : Measure ℕ) [IsFiniteMeasure μ] (B m : ℝ) :
    Integrable (fun k : ℕ => if (k : ℝ) ≤ B then ((k : ℝ) - m) ^ 2 else 0) μ := by
  refine Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable
    ((|B| + |m|) ^ 2) ?_
  filter_upwards [] with k
  by_cases hk : (k : ℝ) ≤ B
  · simp only [hk, ite_true, Real.norm_eq_abs, abs_pow]
    apply pow_le_pow_left₀ (abs_nonneg _)
    calc
      |(k : ℝ) - m| ≤ |(k : ℝ)| + |m| := abs_sub _ _
      _ ≤ |B| + |m| := add_le_add (by simpa using hk.trans (le_abs_self B)) le_rfl
  · simp [hk, pow_nonneg (add_nonneg (abs_nonneg B) (abs_nonneg m)) 2]

lemma integral_bounded_prefix (μ : Measure ℕ) [IsFiniteMeasure μ]
    (f : ℕ → ℝ) (B : ℝ) (hB : ∀ k : ℕ, ‖f k‖ ≤ B) {Y : ℕ}
    (hf : ∀ k : ℕ, Y ≤ k → f k = 0) :
    ∫ k, f k ∂μ = ∑ k ∈ Finset.range Y, (μ {k}).toReal * f k := by
  have hint : Integrable f μ := by
    refine Integrable.of_bound (measurable_of_countable f).aestronglyMeasurable B ?_
    exact ae_of_all _ hB
  rw [integral_countable hint]
  rw [tsum_eq_sum (s := Finset.range Y) (fun k hk => by
    simp only [Finset.mem_range, Nat.not_lt] at hk
    simp [hf k hk])]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [smul_eq_mul, measureReal_def]


lemma integral_truncated_center_nonpos
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ < 1) (Y : ℕ)
    (hmY : (offspringMean μ).toReal ≤ Y) :
    ∫ k : ℕ, (if k < Y then (k : ℝ) - (offspringMean μ).toReal else 0) ∂μ ≤ 0 := by
  let m := (offspringMean μ).toReal
  let p : ℕ → ℝ := fun k => (μ {k}).toReal
  have hmfin : offspringMean μ ≠ ⊤ := ne_top_of_lt hm
  have hp : Summable p := by
    have hp' := summable_pgfReal μ 1 (by norm_num) le_rfl
    simpa [p] using hp'
  have hpsum : ∑' k, p k = 1 := by
    have h := integral_countable (μ := μ) (f := fun _ : ℕ => (1 : ℝ)) (integrable_const 1)
    simpa [p, measureReal_def] using h.symm
  have hmean : ∑' k, p k * (k : ℝ) = m := by
    change (∑' k, (μ {k}).toReal * (k : ℝ)) = (offspringMean μ).toReal
    exact (offspringMean_eq_tsum μ).symm
  have hcsummable : Summable (fun k => p k * ((k : ℝ) - m)) := by
    have heq : (fun k => p k * ((k : ℝ) - m)) =
        (fun k => (μ {k}).toReal * (k : ℝ) - m * (μ {k}).toReal) := by
      funext k
      dsimp [p]
      ring
    rw [heq]
    exact (summable_offspringMean μ hmfin).sub (hp.mul_left m)
  have hcsum : ∑' k, p k * ((k : ℝ) - m) = 0 := by
    rw [show (fun k => p k * ((k : ℝ) - m)) =
        (fun k => p k * (k : ℝ) - m * p k) by funext k; ring]
    rw [(summable_offspringMean μ hmfin).tsum_sub (hp.mul_left m), hmean,
      hp.tsum_mul_left, hpsum]
    ring
  have hsplit := hcsummable.sum_add_tsum_nat_add Y
  rw [hcsum] at hsplit
  have htail : 0 ≤ ∑' k, p (Y + k) * (((Y + k : ℕ) : ℝ) - m) :=
    tsum_nonneg (fun k => mul_nonneg ENNReal.toReal_nonneg
      (sub_nonneg.mpr (hmY.trans (by exact_mod_cast Nat.le_add_right Y k))))
  have hbound (k : ℕ) : ‖if k < Y then (k : ℝ) - m else 0‖ ≤ (Y : ℝ) + |m| := by
    by_cases hk : k < Y
    · simp only [hk, ite_true]
      calc
        |(k : ℝ) - m| ≤ |(k : ℝ)| + |m| := abs_sub _ _
        _ ≤ (Y : ℝ) + |m| := add_le_add (by
          rw [abs_of_nonneg (Nat.cast_nonneg k)]
          exact_mod_cast hk.le) le_rfl
    · simp only [hk, ite_false, norm_zero]
      positivity
  rw [integral_bounded_prefix μ _ ((Y : ℝ) + |m|) hbound
    (fun k hk => by simp only [show ¬ k < Y from Nat.not_lt.mpr hk, ↓reduceIte])]
  change (∑ k ∈ Finset.range Y, p k * (if k < Y then (k : ℝ) - m else 0)) ≤ 0
  have hpre : (∑ k ∈ Finset.range Y, p k * (if k < Y then (k : ℝ) - m else 0)) =
      ∑ k ∈ Finset.range Y, p k * ((k : ℝ) - m) := by
    apply Finset.sum_congr rfl
    intro k hk
    simp [Finset.mem_range.mp hk]
  rw [hpre]
  have hsplit' : (∑ i ∈ Finset.range Y, p i * ((i : ℝ) - m)) +
      (∑' i, p (Y + i) * (((Y + i : ℕ) : ℝ) - m)) = 0 := by
    simpa [Nat.add_comm] using hsplit
  linarith

lemma integral_truncated_center_sq_le
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (Y : ℕ) :
    ∫ k : ℕ, (if k < Y then ((k : ℝ) - (offspringMean μ).toReal) ^ 2 else 0) ∂μ ≤
      (∑ k ∈ Finset.range Y, (k : ℝ) ^ 2 * (μ {k}).toReal) +
        (offspringMean μ).toReal ^ 2 := by
  let m := (offspringMean μ).toReal
  let p : ℕ → ℝ := fun k => (μ {k}).toReal
  have hm0 : 0 ≤ m := by
    change 0 ≤ (offspringMean μ).toReal
    rw [offspringMean_eq_tsum]
    exact tsum_nonneg (fun k => mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg k))
  have hp : Summable p := by
    have hp' := summable_pgfReal μ 1 (by norm_num) le_rfl
    simpa [p] using hp'
  have hpsum : ∑' k, p k = 1 := by
    have h := integral_countable (μ := μ) (f := fun _ : ℕ => (1 : ℝ)) (integrable_const 1)
    simpa [p, measureReal_def] using h.symm
  have hprob : ∑ k ∈ Finset.range Y, p k ≤ 1 := by
    rw [← hpsum]
    exact hp.sum_le_tsum (Finset.range Y) (fun k _ => ENNReal.toReal_nonneg)
  have hbound (k : ℕ) : ‖if k < Y then ((k : ℝ) - m) ^ 2 else 0‖ ≤
      ((Y : ℝ) + |m|) ^ 2 := by
    by_cases hk : k < Y
    · simp only [hk, ite_true, Real.norm_eq_abs, abs_pow]
      apply pow_le_pow_left₀ (abs_nonneg _)
      calc
        |(k : ℝ) - m| ≤ |(k : ℝ)| + |m| := abs_sub _ _
        _ ≤ (Y : ℝ) + |m| := add_le_add (by
          rw [abs_of_nonneg (Nat.cast_nonneg k)]
          exact_mod_cast hk.le) le_rfl
    · simp [hk, pow_nonneg (add_nonneg (Nat.cast_nonneg Y) (abs_nonneg m)) 2]
  rw [integral_bounded_prefix μ _ (((Y : ℝ) + |m|) ^ 2) hbound
    (fun k hk => by simp only [show ¬ k < Y from Nat.not_lt.mpr hk, ↓reduceIte])]
  change (∑ k ∈ Finset.range Y, p k * (if k < Y then ((k : ℝ) - m) ^ 2 else 0)) ≤
    (∑ k ∈ Finset.range Y, (k : ℝ) ^ 2 * p k) + m ^ 2
  calc
    _ ≤ ∑ k ∈ Finset.range Y, p k * ((k : ℝ) ^ 2 + m ^ 2) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' := Finset.mem_range.mp hk
      simp only [hk', ite_true]
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith [sq_nonneg m]
    _ = (∑ k ∈ Finset.range Y, (k : ℝ) ^ 2 * p k) + m ^ 2 * ∑ k ∈ Finset.range Y, p k := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      apply congrArg₂ (· + ·) <;> apply Finset.sum_congr rfl <;> intro k hk <;> ring
    _ ≤ _ := by
      have hm2 : 0 ≤ m ^ 2 := sq_nonneg m
      exact add_le_add_right (by simpa using mul_le_mul_of_nonneg_left hprob hm2) _

end SubcriticalCauchy.Bienayme
