module

public import SubcriticalCauchy.OffspringHypothesis

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Growth and sublinearity of the source scaling sequence

The normalization `n * P(X ≥ a_n) → 1` for `X = offspring - 1` forces `a_n → ∞`
under unbounded support. Finite mean then gives `a_n / n → 0` by a dominated
first-moment tail bound. This proves Lemma 2.2(iii) without the paper's
regular-variation argument. Existence and regular variation of the scaling
sequence and the stable limit remain separate obligations.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Tail of the actual integer increment `offspring - 1` at a real threshold. -/
def incrementTail (μ : Measure ℕ) (x : ℝ) : ℝ≥0∞ := μ {k : ℕ | x ≤ (k : ℝ) - 1}

theorem incrementTail_pos (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsSubcriticalCauchyOffspring μ) (x : ℝ) : 0 < incrementTail μ x := by
  obtain ⟨k, hk, hmass⟩ := offspring_support_unbounded μ hμ ⌈x + 1⌉₊
  apply hmass.trans_le
  apply measure_mono
  intro j hj
  have hjk : j = k := Set.mem_singleton_iff.mp hj
  subst j
  change x ≤ (k : ℝ) - 1
  have hceil := Nat.le_ceil (x + 1)
  have hkR : (⌈x + 1⌉₊ : ℝ) ≤ k := by exact_mod_cast hk
  linarith

theorem incrementTail_antitone (μ : Measure ℕ) : Antitone (incrementTail μ) := by
  intro x y hxy
  apply measure_mono
  intro k hk
  exact hxy.trans hk

theorem scaling_tendsto_atTop (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsSubcriticalCauchyOffspring μ) {a : ℕ → ℝ}
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) : Tendsto a atTop atTop := by
  apply tendsto_atTop.2
  intro B
  have hc : 0 < (incrementTail μ B).toReal :=
    ENNReal.toReal_pos (incrementTail_pos μ hμ B).ne' (measure_ne_top _ _)
  have hg : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ B).toReal) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hc
  filter_upwards [hg.eventually_gt_atTop 2,
    ha.eventually (gt_mem_nhds (show (1 : ℝ) < 2 by norm_num))] with n hn hupper
  by_contra hnot
  have hmono : (incrementTail μ B).toReal ≤ (incrementTail μ (a n)).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (incrementTail_antitone μ (le_of_not_ge hnot))
  have := mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  linarith

/-- Real event masses as sums of singleton masses; all sets of naturals are measurable. -/
theorem measure_toReal_eq_tsum (μ : Measure ℕ) [IsProbabilityMeasure μ] (S : Set ℕ) :
    (μ S).toReal = ∑' k : ℕ, if k ∈ S then (μ {k}).toReal else 0 := by
  have hsum : μ S = ∑' k : ℕ, if k ∈ S then μ {k} else 0 := by
    rw [← lintegral_indicator_one (Set.to_countable S).measurableSet, lintegral_countable']
    apply tsum_congr
    intro k
    by_cases hk : k ∈ S <;> simp [hk]
  rw [hsum, ENNReal.tsum_toReal_eq (fun k => by
    split_ifs <;> simp [measure_ne_top])]
  apply tsum_congr
  intro k
  split_ifs <;> simp

def incrementTailMoment (μ : Measure ℕ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, if x ≤ (k : ℝ) - 1 then (μ {k}).toReal * (k : ℝ) else 0

theorem summable_incrementTailMoment (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) (x : ℝ) :
    Summable (fun k : ℕ => if x ≤ (k : ℝ) - 1 then (μ {k}).toReal * (k : ℝ) else 0) :=
  (summable_offspringMean μ hm).of_nonneg_of_le (fun k => by split_ifs <;> positivity)
    (fun k => by split_ifs <;> simp [mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg k)])

theorem incrementTailMoment_tendsto_zero (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) :
    Tendsto (fun n => incrementTailMoment μ (a n)) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (summable_offspringMean μ hm)
    (f := fun (n : ℕ) (k : ℕ) => if a n ≤ (k : ℝ) - 1 then (μ {k}).toReal * (k : ℝ) else 0)
    (g := fun _ : ℕ => (0 : ℝ))
    (fun k => by
      apply tendsto_const_nhds.congr'
      filter_upwards [ha.eventually_gt_atTop ((k : ℝ) - 1)] with n hn
      simp [not_le.mpr hn])
    (Eventually.of_forall (fun n k => by
      by_cases hk : a n ≤ (k : ℝ) - 1
      · simp only [hk, ↓reduceIte, Real.norm_eq_abs]
        exact (abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg k))).le
      · simp only [hk, ↓reduceIte, norm_zero]
        exact mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg k)))
  simpa only [incrementTailMoment, tsum_zero] using h

theorem mul_incrementTail_le_moment (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) (x : ℝ) :
    x * (incrementTail μ x).toReal ≤ incrementTailMoment μ x := by
  have hp : Summable (fun k : ℕ => (μ {k}).toReal) := by
    simpa using summable_pgfReal μ 1 zero_le_one le_rfl
  have htail : Summable (fun k : ℕ => if x ≤ (k : ℝ) - 1 then (μ {k}).toReal else 0) :=
    hp.of_nonneg_of_le (fun _ => by split_ifs <;> positivity)
      (fun _ => by split_ifs <;> simp [ENNReal.toReal_nonneg])
  rw [incrementTail, measure_toReal_eq_tsum]
  simp only [Set.mem_ofPred_eq]
  rw [← htail.tsum_mul_left]
  unfold incrementTailMoment
  apply (htail.mul_left x).tsum_le_tsum _ (summable_incrementTailMoment μ hm x)
  intro k
  by_cases hk : x ≤ (k : ℝ) - 1
  · simp only [hk, ↓reduceIte]
    nlinarith [ENNReal.toReal_nonneg (a := μ {k})]
  · simp [hk]

/-- Lemma 2.2(iii), from the defining scaling relation and finite mean. -/
theorem scaling_div_nat_tendsto_zero (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsSubcriticalCauchyOffspring μ) {a : ℕ → ℝ}
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) : Tendsto (fun n : ℕ => a n / (n : ℝ)) atTop (𝓝 0) := by
  have hm : offspringMean μ ≠ ∞ := ne_top_of_lt (hμ.1.trans ENNReal.one_lt_top)
  have hat := scaling_tendsto_atTop μ hμ ha
  have hmoment := incrementTailMoment_tendsto_zero μ hm hat
  have hprod : Tendsto (fun n => a n * (incrementTail μ (a n)).toReal) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ hmoment
    · filter_upwards [hat.eventually_ge_atTop 0] with n hn
      exact mul_nonneg hn ENNReal.toReal_nonneg
    · filter_upwards [hat.eventually_ge_atTop 0] with n hn
      exact mul_incrementTail_le_moment μ hm (a n)
  have hdiv := hprod.div ha (by norm_num : (1 : ℝ) ≠ 0)
  apply (show Tendsto (fun n : ℕ => (a n * (incrementTail μ (a n)).toReal) /
      ((n : ℝ) * (incrementTail μ (a n)).toReal)) atTop (𝓝 0) by simpa only [Pi.div_def, zero_div] using hdiv).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have ht : (incrementTail μ (a n)).toReal ≠ 0 :=
    (ENNReal.toReal_pos (incrementTail_pos μ hμ _).ne' (measure_ne_top _ _)).ne'
  field_simp

end
end SubcriticalCauchy.Bienayme
