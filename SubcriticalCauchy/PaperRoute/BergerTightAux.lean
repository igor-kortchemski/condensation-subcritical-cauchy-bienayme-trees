module

public import SubcriticalCauchy.IncrementTailAsymptotics
public import SubcriticalCauchy.DeletedIncrements
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Truncation and product-measure estimates for Berger tightness
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators

namespace SubcriticalCauchy.Bienayme

noncomputable section

attribute [local instance] Classical.propDecidable

local instance bergerTightIncrementLawIsProbability (μ : Measure ℕ)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (incrementLaw μ) := by
  unfold incrementLaw
  infer_instance

/-- Real truncation of an integer increment. -/
def bergerTrunc (r : ℝ) (z : ℤ) : ℝ :=
  if (z : ℝ) ≤ r then (z : ℝ) else 0

lemma bergerTrunc_mem {r : ℝ} (_hr : 0 ≤ r) (z : ℤ) (hz : (-1 : ℝ) ≤ (z : ℝ)) :
    bergerTrunc r z ∈ Set.Icc (-max r 1) (max r 1) := by
  unfold bergerTrunc
  split_ifs with h
  · have hrmax : r ≤ max r 1 := le_max_left _ _
    have h1max : (1 : ℝ) ≤ max r 1 := le_max_right _ _
    exact ⟨by linarith, by linarith⟩
  · exact ⟨neg_nonpos.mpr (by positivity), by positivity⟩

lemma bergerTrunc_memLp (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 ≤ r) : MemLp (bergerTrunc r) 2 (incrementLaw μ) := by
  apply memLp_of_bounded (a := -max r 1) (b := max r 1) _
    (measurable_of_countable _).aestronglyMeasurable 2
  rw [incrementLaw, ae_map_iff (measurable_of_countable _).aemeasurable
    (Set.to_countable _).measurableSet]
  exact Eventually.of_forall fun k => bergerTrunc_mem hr _ (by simp)

lemma bergerTrunc_integral (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 1 ≤ r) :
    ∫ z, bergerTrunc r z ∂incrementLaw μ = truncatedIncrementMean μ r := by
  rw [incrementLaw, integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable]
  unfold truncatedIncrementMean bergerTrunc offspringIncrement
  apply integral_congr_ae
  filter_upwards [] with k
  simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one]
  by_cases hk : k = 0
  · subst k
    simp only [Nat.cast_zero, zero_sub, abs_neg, abs_one]
    split_ifs <;> linarith
  · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk)
    rw [abs_of_nonneg (by linarith)]
lemma bergerTrunc_integral_sq_eq_tsum (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 ≤ r) :
    ∫ z, (bergerTrunc r z) ^ 2 ∂incrementLaw μ =
      ∑' k : ℕ, (μ {k}).toReal * (bergerTrunc r ((k : ℤ) - 1)) ^ 2 := by
  rw [incrementLaw, integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable]
  have hint : Integrable (fun k : ℕ => (bergerTrunc r ((k : ℤ) - 1)) ^ 2) μ := by
    refine Integrable.of_bound (μ := μ) (f := fun k : ℕ =>
      (bergerTrunc r ((k : ℤ) - 1)) ^ 2) ?_ ((max r 1) ^ 2) ?_
    · exact (measurable_of_countable _).aestronglyMeasurable
    · filter_upwards [] with k
      have hk := bergerTrunc_mem hr ((k : ℤ) - 1) (by simp)
      rw [Real.norm_eq_abs, abs_sq]
      have habs : |bergerTrunc r ((k : ℤ) - 1)| ≤ max r 1 := abs_le.mpr ⟨by
        have := le_max_left r 1
        linarith [hk.1], by
        have := le_max_left r 1
        linarith [hk.2]⟩
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) (zero_le_one.trans (le_max_right r 1))).mpr habs
  simpa only [measureReal_def, smul_eq_mul] using integral_countable hint

lemma bergerTrunc_integral_sq_le_sum (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 1 ≤ r) :
    (∫ z, (bergerTrunc r z) ^ 2 ∂incrementLaw μ) ≤
      1 + ∑ k ∈ Finset.range (⌈r + 1⌉₊ + 1), (k : ℝ) ^ 2 * (μ {k}).toReal := by
  rw [bergerTrunc_integral_sq_eq_tsum μ (zero_le_one.trans hr)]
  have hzero (k : ℕ) (hk : k ∉ Finset.range (⌈r + 1⌉₊ + 1)) :
      (μ {k}).toReal * (bergerTrunc r ((k : ℤ) - 1)) ^ 2 = 0 := by
    have hky : ⌈r + 1⌉₊ + 1 ≤ k := by simpa [Finset.mem_range] using hk
    have hk2 : 2 ≤ k := by
      have : 1 ≤ ⌈r + 1⌉₊ := Nat.one_le_iff_ne_zero.mpr (by positivity)
      omega
    have hnot : ¬ (k : ℝ) - 1 ≤ r := by
      have hceil : r + 1 ≤ (⌈r + 1⌉₊ : ℝ) := Nat.le_ceil _
      have hkR : (⌈r + 1⌉₊ + 1 : ℕ) ≤ (k : ℝ) := by exact_mod_cast hky
      push_cast at hkR
      linarith
    simp [bergerTrunc, hnot]
  rw [tsum_eq_sum (s := Finset.range (⌈r + 1⌉₊ + 1)) hzero]
  calc
    (∑ k ∈ Finset.range (⌈r + 1⌉₊ + 1),
        (μ {k}).toReal * (bergerTrunc r ((k : ℤ) - 1)) ^ 2)
        ≤ ∑ k ∈ Finset.range (⌈r + 1⌉₊ + 1),
          ((k : ℝ) ^ 2 * (μ {k}).toReal + if k = 0 then 1 else 0) := by
      apply Finset.sum_le_sum
      intro k hk
      by_cases htr : (k : ℝ) - 1 ≤ r
      · simp only [bergerTrunc, Int.cast_sub, Int.cast_natCast, Int.cast_one, htr, ↓reduceIte]
        by_cases hk0 : k = 0
        · subst k
          norm_num
          exact measureReal_le_one
        · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
          have hkR : (0 : ℝ) ≤ (k : ℝ) - 1 := by
            have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
            linarith
          simp only [hk0, ↓reduceIte, add_zero]
          apply (mul_le_mul_of_nonneg_left (show ((k : ℝ) - 1) ^ 2 ≤ (k : ℝ) ^ 2 by
            nlinarith) ENNReal.toReal_nonneg).trans_eq (by ring)
      · simp only [bergerTrunc, Int.cast_sub, Int.cast_natCast, Int.cast_one, htr, ↓reduceIte,
          zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]
        positivity
    _ = (∑ k ∈ Finset.range (⌈r + 1⌉₊ + 1), (k : ℝ) ^ 2 * (μ {k}).toReal) +
        ∑ k ∈ Finset.range (⌈r + 1⌉₊ + 1), if k = 0 then (1 : ℝ) else 0 :=
      Finset.sum_add_distrib
    _ ≤ 1 + ∑ k ∈ Finset.range (⌈r + 1⌉₊ + 1), (k : ℝ) ^ 2 * (μ {k}).toReal := by
      simp only [Finset.sum_ite_eq', Finset.mem_range, Nat.zero_lt_succ, ↓reduceIte]
      linarith

lemma bergerTrunc_sum_integral (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (j : ℕ) {r : ℝ} (hr : 1 ≤ r) :
    ∫ x : Fin j → ℤ, ∑ i, bergerTrunc r (x i) ∂(Measure.pi fun _ : Fin j => incrementLaw μ) =
      (j : ℝ) * truncatedIncrementMean μ r := by
  rw [integral_finsetSum]
  · have heq (i : Fin j) :
        (∫ x : Fin j → ℤ, bergerTrunc r (x i) ∂(Measure.pi fun _ : Fin j => incrementLaw μ)) =
          truncatedIncrementMean μ r := by
      rw [integral_comp_eval (μ := fun _ : Fin j => incrementLaw μ) (i := i)
        (f := bergerTrunc r) (bergerTrunc_memLp μ (zero_le_one.trans hr)).aestronglyMeasurable,
        bergerTrunc_integral μ hr]
    simp_rw [heq]
    simp
  · intro i _
    exact integrable_comp_eval (μ := fun _ : Fin j => incrementLaw μ) (i := i)
      (f := bergerTrunc r) ((bergerTrunc_memLp μ (zero_le_one.trans hr)).integrable (by norm_num))

lemma bergerTrunc_sum_memLp (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (j : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    MemLp (fun x : Fin j → ℤ => ∑ i, bergerTrunc r (x i)) 2
      (Measure.pi fun _ : Fin j => incrementLaw μ) := by
  apply memLp_finsetSum Finset.univ
  intro i _
  exact (bergerTrunc_memLp μ hr).comp_measurePreserving (measurePreserving_eval _ i)

lemma bergerTrunc_sum_variance_le (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (j : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    variance (fun x : Fin j → ℤ => ∑ i, bergerTrunc r (x i))
        (Measure.pi fun _ : Fin j => incrementLaw μ) ≤
      (j : ℝ) * ∫ z, (bergerTrunc r z) ^ 2 ∂incrementLaw μ := by
  rw [show (fun x : Fin j → ℤ => ∑ i, bergerTrunc r (x i)) =
      (∑ i : Fin j, fun x : Fin j → ℤ => bergerTrunc r (x i)) by ext x; simp]
  rw [variance_sum_pi (fun _ : Fin j => bergerTrunc_memLp μ hr)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  gcongr with i
  exact variance_le_expectation_sq (measurable_of_countable _).aestronglyMeasurable

lemma bergerTight_chebyshev (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (j : ℕ) {r q : ℝ} (hr : 1 ≤ r) (hq : 0 < q) :
    ((Measure.pi fun _ : Fin j => incrementLaw μ)
      {x | q ≤ |∑ i, bergerTrunc r (x i) - (j : ℝ) * truncatedIncrementMean μ r|}).toReal ≤
      (variance (fun x : Fin j → ℤ => ∑ i, bergerTrunc r (x i))
        (Measure.pi fun _ : Fin j => incrementLaw μ)) / q ^ 2 := by
  have hc := meas_ge_le_variance_div_sq (bergerTrunc_sum_memLp μ j (zero_le_one.trans hr)) hq
  rw [bergerTrunc_sum_integral μ j hr] at hc
  have hcR := ENNReal.toReal_mono ENNReal.ofReal_ne_top hc
  rwa [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg q))] at hcR

lemma bergerTight_bad_event_subset (j : ℕ) (r c q A ma mr : ℝ)
    (_hr : 1 ≤ r) (hmean : (j : ℝ) * |mr - ma| ≤ c * A) :
    {x : Fin j → ℤ | (c + q) * A < |(∑ i, (x i : ℝ)) - j * ma|} ⊆
      {x | ∃ i, r < (x i : ℝ)} ∪
      {x | q * A ≤ |∑ i, bergerTrunc r (x i) - j * mr|} := by
  intro x hx
  by_cases hmax : ∃ i, r < (x i : ℝ)
  · exact Or.inl hmax
  · apply Or.inr
    change (c + q) * A < |(∑ i, (x i : ℝ)) - (j : ℝ) * ma| at hx
    have htr (i : Fin j) : bergerTrunc r (x i) = (x i : ℝ) := by
      have hxi : (x i : ℝ) ≤ r := not_lt.mp (not_exists.mp hmax i)
      simp [bergerTrunc, hxi]
    have hjabs : |(j : ℝ) * (mr - ma)| ≤ c * A := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg j)]
      exact hmean
    have htri : |(∑ i, (x i : ℝ)) - (j : ℝ) * ma| ≤
        |(j : ℝ) * (mr - ma)| + |(∑ i, (x i : ℝ)) - (j : ℝ) * mr| := by
      calc
        |(∑ i, (x i : ℝ)) - (j : ℝ) * ma| =
            |(j : ℝ) * (mr - ma) + ((∑ i, (x i : ℝ)) - (j : ℝ) * mr)| := by
              congr 1
              ring
        _ ≤ |(j : ℝ) * (mr - ma)| + |(∑ i, (x i : ℝ)) - (j : ℝ) * mr| :=
          abs_add_le _ _
    have hlt : q * A < |(∑ i, (x i : ℝ)) - (j : ℝ) * mr| := by nlinarith
    change q * A ≤ |∑ i, bergerTrunc r (x i) - (j : ℝ) * mr|
    simpa only [htr] using hlt.le

/-- The strict coordinate tail is bounded by the non-strict real increment tail. -/
lemma incrementLaw_real_gt_le_incrementTail (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (y : ℝ) :
    ((incrementLaw μ) {z : ℤ | y < (z : ℝ)}).toReal ≤ (incrementTail μ y).toReal := by
  rw [incrementLaw, Measure.map_apply (measurable_of_countable _)
    (Set.to_countable _).measurableSet]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro k hk
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Int.cast_sub, Int.cast_natCast,
    Int.cast_one] at hk
  exact le_of_lt hk

/-- Union bound for one large coordinate in a finite product. -/
lemma incrementMax_measure_le (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (j : ℕ) (y : ℝ) :
    ((Measure.pi fun _ : Fin j => incrementLaw μ)
      {x | ∃ i, y < (x i : ℝ)}).toReal ≤
      (j : ℝ) * (incrementTail μ y).toReal := by
  have hset : {x : Fin j → ℤ | ∃ i, y < (x i : ℝ)} =
      ⋃ i : Fin j, {x | y < (x i : ℝ)} := by
    ext x
    simp
  rw [hset]
  calc
    ((Measure.pi fun _ : Fin j => incrementLaw μ) (⋃ i : Fin j, {x | y < (x i : ℝ)})).toReal
        ≤ ∑ i : Fin j, ((Measure.pi fun _ : Fin j => incrementLaw μ)
          {x | y < (x i : ℝ)}).toReal := by
          exact measureReal_iUnion_fintype_le _
    _ = (j : ℝ) * ((incrementLaw μ) {z : ℤ | y < (z : ℝ)}).toReal := by
          have heval (i : Fin j) :
              (Measure.pi fun _ : Fin j => incrementLaw μ) {x | y < (x i : ℝ)} =
                (incrementLaw μ) {z : ℤ | y < (z : ℝ)} := by
            let P := Measure.pi fun _ : Fin j => incrementLaw μ
            let S := {z : ℤ | y < (z : ℝ)}
            change P ((fun x : Fin j → ℤ => x i) ⁻¹' S) = (incrementLaw μ) S
            calc
              P ((fun x : Fin j → ℤ => x i) ⁻¹' S) = (P.map (fun x => x i)) S :=
                (Measure.map_apply (measurable_pi_apply i) (Set.to_countable _).measurableSet).symm
              _ = (incrementLaw μ) S := by
                rw [(measurePreserving_eval (fun _ : Fin j => incrementLaw μ) i).map_eq]
          simp_rw [heval]
          simp
    _ ≤ (j : ℝ) * (incrementTail μ y).toReal :=
      mul_le_mul_of_nonneg_left (incrementLaw_real_gt_le_incrementTail μ y) (Nat.cast_nonneg j)

end
end SubcriticalCauchy.Bienayme
