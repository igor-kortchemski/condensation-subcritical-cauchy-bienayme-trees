module

public import SubcriticalCauchy.Propositions42_43
public import SubcriticalCauchy.SurvivalCriterion
public import SubcriticalCauchy.BienaymeForestLog
public import Mathlib.Analysis.Real.Sqrt

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Analytic helpers for Theorem 1.1(iii)(b)

This file contains the real-analysis and event-manipulation lemmas used by
`MainProofs.M5`.  The logarithmic thresholds are totalized at small indices;
only their eventual values enter the asymptotic arguments.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section
open BGW BGW.LocallyFinite

attribute [local instance] Classical.propDecidable

/-- The natural centre of the size-conditioned height. -/
def m5LogHeight (m : ℝ) (n : ℕ) : ℝ := Real.log n / Real.log (1 / m)

/-- A sublinear centreing rate; the maximum makes every totalized value nonnegative. -/
def m5SlowRate (m : ℝ) (n : ℕ) : ℝ := Real.sqrt (max (m5LogHeight m n) 0)

/-- Paper's normalized survival probabilities. -/
def m5U (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) : ℝ :=
  (survival μ n).toReal / (offspringMean μ).toReal ^ n

lemma m5MeanReal_pos (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) :
    0 < (offspringMean μ).toReal := by
  exact ENNReal.toReal_pos (offspringMean_pos_of_paper μ hμ.to_literal).ne'
    (ne_top_of_lt (hμ.1.trans ENNReal.one_lt_top))

lemma m5MeanReal_lt_one (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) :
    (offspringMean μ).toReal < 1 := by
  simpa using (ENNReal.toReal_lt_toReal
    (ne_top_of_lt (hμ.1.trans ENNReal.one_lt_top)) ENNReal.one_ne_top).mpr hμ.1

lemma m5LogDenom_pos (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) :
    0 < Real.log (1 / (offspringMean μ).toReal) :=
  log_inv_mean_pos (m5MeanReal_pos μ hμ) (m5MeanReal_lt_one μ hμ)

lemma m5LogHeight_tendsto (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) :
    Tendsto (m5LogHeight (offspringMean μ).toReal) atTop atTop := by
  exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const
    (m5LogDenom_pos μ hμ)

lemma m5SlowRate_nonneg (m : ℝ) (n : ℕ) : 0 ≤ m5SlowRate m n :=
  Real.sqrt_nonneg _

lemma m5SlowRate_tendsto (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) :
    Tendsto (m5SlowRate (offspringMean μ).toReal) atTop atTop := by
  apply Real.tendsto_sqrt_atTop.comp
  apply (m5LogHeight_tendsto μ hμ).congr'
  filter_upwards [(m5LogHeight_tendsto μ hμ) (eventually_ge_atTop 0)] with n hn
  exact (max_eq_left hn).symm

lemma m5SlowRate_le_logHeight (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) :
    ∀ᶠ n in atTop, m5SlowRate (offspringMean μ).toReal n ≤
      m5LogHeight (offspringMean μ).toReal n := by
  filter_upwards [(m5LogHeight_tendsto μ hμ) (eventually_ge_atTop 1)] with n hn
  change 1 ≤ m5LogHeight (offspringMean μ).toReal n at hn
  dsimp [m5SlowRate]
  rw [max_eq_left (by linarith : 0 ≤ m5LogHeight (offspringMean μ).toReal n)]
  exact Real.sqrt_le_self_iff.mpr (Or.inr hn)

lemma m5LogHeight_sub_slowRate_tendsto (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) :
    Tendsto (fun n => m5LogHeight (offspringMean μ).toReal n -
      m5SlowRate (offspringMean μ).toReal n) atTop atTop := by
  have hsq : Tendsto (fun n => m5SlowRate (offspringMean μ).toReal n ^ 2 -
      m5SlowRate (offspringMean μ).toReal n) atTop atTop := by
    have hm : Tendsto (fun x : ℝ => x ^ 2 - x) atTop atTop := by
      apply tendsto_atTop_mono' atTop _ tendsto_id
      filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
      change x ≤ x ^ 2 - x
      nlinarith
    exact hm.comp (m5SlowRate_tendsto μ hμ)
  apply hsq.congr'
  filter_upwards [(m5LogHeight_tendsto μ hμ) (eventually_ge_atTop 0)] with n hn
  dsimp [m5SlowRate]
  rw [max_eq_left hn, Real.sq_sqrt hn]

/-- Multiplication by `n` cancels the centreing exponent of a geometric power. -/
lemma m5Nat_mul_rpow_logHeight (m x : ℝ) (hm0 : 0 < m) (hm1 : m < 1)
    (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * m ^ (Real.log n / Real.log (1 / m) + x) = m ^ x := by
  have hd : Real.log (1 / m) = -Real.log m := by rw [one_div, Real.log_inv]
  have hlogm : Real.log m ≠ 0 := (Real.log_neg hm0 hm1).ne
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hcancel : Real.log (n : ℝ) / Real.log (1 / m) * Real.log m =
      -Real.log (n : ℝ) := by
    rw [hd]
    field_simp
  have hcancel' : Real.log m * (Real.log (n : ℝ) / Real.log (1 / m)) =
      -Real.log (n : ℝ) := by rw [mul_comm, hcancel]
  rw [Real.rpow_add hm0, Real.rpow_def_of_pos hm0, hcancel', Real.exp_neg,
    Real.exp_log hnr]
  field_simp

lemma m5U_pos (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (n : ℕ) : 0 < m5U μ n := by
  exact div_pos (survival_toReal_pos μ (offspringMean_pos_of_paper μ hμ.to_literal) n)
    (pow_pos (m5MeanReal_pos μ hμ) n)

lemma m5U_le_one (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (n : ℕ) : m5U μ n ≤ 1 := by
  rw [m5U, div_le_one (pow_pos (m5MeanReal_pos μ hμ) n)]
  simpa only [ENNReal.toReal_pow] using ENNReal.toReal_mono
    (ENNReal.pow_ne_top (ne_top_of_lt (hμ.1.trans ENNReal.one_lt_top)))
    (survival_le_mean_pow μ n)

lemma m5U_antitone (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) : Antitone (m5U μ) := by
  exact survival_div_mean_pow_antitone μ
    (offspringMean_pos_of_paper μ hμ.to_literal) hμ.1

lemma m5Survival_eq_u_mul_pow (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (n : ℕ) :
    (survival μ n).toReal = m5U μ n * (offspringMean μ).toReal ^ n := by
  exact (div_mul_cancel₀ _ (pow_ne_zero n (m5MeanReal_pos μ hμ).ne')).symm

lemma m5MeasurableSet_finiteTreeEvent (P : PlaneTree → Prop) :
    MeasurableSet (finiteTreeEvent P) :=
  ((Set.to_countable {t : PlaneTree | P t}).image
    PlaneTree.toLocallyFinite).measurableSet

lemma m5ToLocallyFinite_mem_finiteTreeEvent_iff
    (P : PlaneTree → Prop) (t : PlaneTree) :
    t.toLocallyFinite ∈ finiteTreeEvent P ↔ P t := by
  constructor
  · rintro ⟨s, hs, hst⟩
    have hst' : s = t := PlaneTree.toLocallyFinite_injective hst
    simpa only [hst', Set.mem_ofPred_eq] using hs
  · intro ht
    exact ⟨t, ht, rfl⟩


lemma m5Pow_antitone {m : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1) :
    Antitone (fun k : ℕ => m ^ k) := by
  intro a b hab
  change m ^ b ≤ m ^ a
  rw [← Real.rpow_natCast, ← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_ge hm0 hm1 (by exact_mod_cast hab)

lemma m5Pow_ceil_le_rpow {m : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1) (h : ℝ) :
    m ^ ⌈h⌉₊ ≤ m ^ h := by
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_ge hm0 hm1 (Nat.le_ceil h)

lemma m5_rpow_add_one_le_pow_ceil {m : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1)
    {h : ℝ} (hh : 0 ≤ h) : m ^ (h + 1) ≤ m ^ ⌈h⌉₊ := by
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_ge hm0 hm1 (Nat.ceil_lt_add_one hh).le

lemma m5Survival_real_antitone (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) {a b : ℝ} (hab : a ≤ b) :
    (survival μ ⌈b⌉₊).toReal ≤ (survival μ ⌈a⌉₊).toReal := by
  rw [m5Survival_eq_u_mul_pow μ hμ, m5Survival_eq_u_mul_pow μ hμ]
  exact mul_le_mul (m5U_antitone μ hμ (Nat.ceil_mono hab))
    (m5Pow_antitone (m5MeanReal_pos μ hμ) (m5MeanReal_lt_one μ hμ).le
      (Nat.ceil_mono hab)) (pow_nonneg (m5MeanReal_pos μ hμ).le _) (m5U_pos μ hμ _).le

lemma m5Expected_upper_bound (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (r : ℕ → ℝ)
    {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * (survival μ ⌈m5LogHeight (offspringMean μ).toReal n + r n⌉₊).toReal ≤
      (offspringMean μ).toReal ^ r n := by
  let m := (offspringMean μ).toReal
  have hm0 := m5MeanReal_pos μ hμ
  have hm1 := (m5MeanReal_lt_one μ hμ).le
  calc
    (n : ℝ) * (survival μ ⌈m5LogHeight m n + r n⌉₊).toReal =
        (n : ℝ) * (m5U μ ⌈m5LogHeight m n + r n⌉₊ * m ^ ⌈m5LogHeight m n + r n⌉₊) := by
      rw [m5Survival_eq_u_mul_pow μ hμ]
    _ ≤ (n : ℝ) * (1 * m ^ (m5LogHeight m n + r n)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul (m5U_le_one μ hμ _)
        (m5Pow_ceil_le_rpow hm0 hm1 _) (by positivity) (by positivity)
    _ = m ^ r n := by
      simpa only [one_mul, m5LogHeight] using m5Nat_mul_rpow_logHeight m (r n) hm0
        (m5MeanReal_lt_one μ hμ) n hn

lemma m5Expected_upper_tendsto_zero (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (r : ℕ → ℝ)
    (hr : Tendsto r atTop atTop) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      (survival μ ⌈m5LogHeight (offspringMean μ).toReal n + r n⌉₊).toReal)
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun n => by positivity)
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact m5Expected_upper_bound μ hμ r hn
  · exact (tendsto_rpow_atTop_of_base_lt_one (offspringMean μ).toReal
      (by linarith [m5MeanReal_pos μ hμ]) (m5MeanReal_lt_one μ hμ)).comp hr

lemma m5Expected_lower_eventually (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (r : ℕ → ℝ) {c : ℝ}
    (hc : 0 < c)
    (hu : Tendsto (m5U μ) atTop (𝓝 c))
    (hr : Tendsto (fun n => m5LogHeight (offspringMean μ).toReal n - r n) atTop atTop) :
    ∀ᶠ n in atTop, (c / 2) * (offspringMean μ).toReal ^ (1 - r n) ≤
      (n : ℝ) * (survival μ ⌈m5LogHeight (offspringMean μ).toReal n - r n⌉₊).toReal := by
  let m := (offspringMean μ).toReal
  have hm0 := m5MeanReal_pos μ hμ
  have hm1 := (m5MeanReal_lt_one μ hμ).le
  have hceil : Tendsto (fun n => ⌈m5LogHeight m n - r n⌉₊) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [hr (eventually_ge_atTop (b : ℝ))] with n hn
    exact_mod_cast hn.trans (Nat.le_ceil (m5LogHeight m n - r n))
  have hue : ∀ᶠ n in atTop, c / 2 ≤ m5U μ ⌈m5LogHeight m n - r n⌉₊ := by
    filter_upwards [(hu.comp hceil).eventually
      (eventually_gt_nhds (half_lt_self hc))] with n hn
    exact hn.le
  filter_upwards [hue, hr (eventually_ge_atTop 0), eventually_gt_atTop (0 : ℕ)] with n hUn hn0 hn
  have hp := m5_rpow_add_one_le_pow_ceil hm0 hm1 hn0
  have hpow : (n : ℝ) * m ^ (m5LogHeight m n + (1 - r n)) = m ^ (1 - r n) := by
    simpa only [m5LogHeight] using
      (m5Nat_mul_rpow_logHeight m (1 - r n) hm0 (m5MeanReal_lt_one μ hμ) n hn)
  calc
    (c / 2) * m ^ (1 - r n) = (c / 2) *
        (n * m ^ (m5LogHeight m n - r n + 1)) := by
      rw [show m5LogHeight m n - r n + 1 = m5LogHeight m n + (1 - r n) by ring, hpow]
    _ = (n : ℝ) * ((c / 2) * m ^ (m5LogHeight m n - r n + 1)) := by ring
    _ ≤ (n : ℝ) * (m5U μ ⌈m5LogHeight m n - r n⌉₊ * m ^ ⌈m5LogHeight m n - r n⌉₊) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul hUn hp (by positivity) (by linarith)
    _ = (n : ℝ) * (survival μ ⌈m5LogHeight m n - r n⌉₊).toReal := by
      rw [m5Survival_eq_u_mul_pow μ hμ]

lemma m5Expected_lower_tendsto_atTop (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (r : ℕ → ℝ) {c : ℝ}
    (hc : 0 < c) (hu : Tendsto (m5U μ) atTop (𝓝 c))
    (hr : Tendsto r atTop atTop)
    (hLr : Tendsto (fun n => m5LogHeight (offspringMean μ).toReal n - r n) atTop atTop) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      (survival μ ⌈m5LogHeight (offspringMean μ).toReal n - r n⌉₊).toReal)
      atTop atTop := by
  let m := (offspringMean μ).toReal
  have hm0 := m5MeanReal_pos μ hμ
  have hm1 := m5MeanReal_lt_one μ hμ
  have hgrow : Tendsto (fun n => m ^ (1 - r n)) atTop atTop := by
    have hbase : 1 < 1 / m := (one_lt_div hm0).mpr hm1
    have hshift : Tendsto (fun n => r n - 1) atTop atTop :=
      (tendsto_atTop_add_const_right atTop (-1) hr)
    have hp := (tendsto_rpow_atTop_of_base_gt_one (1 / m) hbase).comp hshift
    apply hp.congr'
    filter_upwards [] with n
    change (1 / m) ^ (r n - 1) = m ^ (1 - r n)
    rw [one_div, show 1 - r n = -(r n - 1) by ring, Real.rpow_neg_eq_inv_rpow]
  apply tendsto_atTop_mono' atTop (m5Expected_lower_eventually μ hμ r hc hu hLr)
  exact hgrow.const_mul_atTop (by linarith)

lemma m5Conditioned_apply_eq_tsum_plane (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (n : ℕ) (A : Set Tree) (hA : MeasurableSet A) :
    conditioned μ n A = ∑' t : PlaneTree, conditioned μ n {t.toLocallyFinite} *
      (if t.toLocallyFinite ∈ A then 1 else 0) := by
  classical
  let f (t : PlaneTree) : ℝ≥0∞ := conditioned μ n {t.toLocallyFinite} *
    (if t.toLocallyFinite ∈ A then 1 else 0)
  change conditioned μ n A = ∑' t : PlaneTree, f t
  change (bienaymeLaw μ (sizeEvent n))⁻¹ *
      (bienaymeLaw μ).restrict (sizeEvent n) A = _
  rw [restrict_sizeEvent_apply μ n A hA, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro t
  dsimp only [f]
  have hat : conditioned μ n {t.toLocallyFinite} =
      if t.size = n then
        PlaneTree.weight (fun k => μ {k}) t / bienaymeLaw μ (sizeEvent n) else 0 :=
    cond_sizeEvent_singleton μ n t
  rw [hat]
  by_cases ht : t.size = n
  · simp only [ht, ↓reduceIte, ENNReal.div_eq_inv_mul, mul_assoc]
  · simp only [ht, ↓reduceIte, zero_mul, mul_zero]

lemma m5Conditioned_eq_compl_not (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (n : ℕ) (P : PlaneTree → Prop) :
    conditioned μ n (finiteTreeEvent P) =
      conditioned μ n (finiteTreeEvent fun t => ¬ P t)ᶜ := by
  classical
  rw [m5Conditioned_apply_eq_tsum_plane μ n _ (m5MeasurableSet_finiteTreeEvent P),
    m5Conditioned_apply_eq_tsum_plane μ n _ (m5MeasurableSet_finiteTreeEvent _).compl]
  apply tsum_congr
  intro t
  by_cases ht : P t <;> simp [m5ToLocallyFinite_mem_finiteTreeEvent_iff, ht]

lemma m5Conditioned_compl_tendsto_zero (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (P : ℕ → PlaneTree → Prop)
    (hP : Tendsto (fun n => conditioned μ n (finiteTreeEvent (P n))) atTop (𝓝 1)) :
    Tendsto (fun n => conditioned μ n (finiteTreeEvent fun t => ¬ P n t)) atTop (𝓝 0) := by
  have hreal : Tendsto (fun n =>
      (conditioned μ n (finiteTreeEvent fun t => ¬ P n t)).toReal) atTop (𝓝 0) := by
    have htoreal := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp hP
    have hc := (tendsto_const_nhds (x := (1 : ℝ))).sub htoreal
    simp only [ENNReal.toReal_one, sub_self, Function.comp_apply] at hc
    apply hc.congr'
    filter_upwards [eventually_size_admissible μ hμ.to_literal] with n hn
    let _ : IsProbabilityMeasure (conditioned μ n) := conditioned_isProbability μ n hn
    rw [m5Conditioned_eq_compl_not μ n (P n),
      measure_compl (m5MeasurableSet_finiteTreeEvent _) (measure_ne_top _ _), measure_univ,
      ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
    ring
  have he := ENNReal.tendsto_ofReal hreal
  simp only [ENNReal.ofReal_zero] at he
  apply he.congr'
  filter_upwards [eventually_size_admissible μ hμ.to_literal] with n hn
  let _ : IsProbabilityMeasure (conditioned μ n) := conditioned_isProbability μ n hn
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

lemma m5Conditioned_eq_zero_of_not_size (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (n : ℕ) (P : PlaneTree → Prop) (hP : ∀ t : PlaneTree, t.size = n → ¬ P t) :
    conditioned μ n (finiteTreeEvent P) = 0 := by
  classical
  rw [m5Conditioned_apply_eq_tsum_plane μ n _ (m5MeasurableSet_finiteTreeEvent P)]
  apply ENNReal.tsum_eq_zero.mpr
  intro t
  have hat : conditioned μ n {t.toLocallyFinite} =
      if t.size = n then
        PlaneTree.weight (fun k => μ {k}) t / bienaymeLaw μ (sizeEvent n) else 0 :=
    cond_sizeEvent_singleton μ n t
  rw [hat]
  by_cases ht : t.size = n
  · have hnot := hP t ht
    simp [ht, m5ToLocallyFinite_mem_finiteTreeEvent_iff, hnot]
  · simp [ht]



lemma m5Conditioned_centered_tail_le_add (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (n : ℕ) (L r : ℝ) :
    conditioned μ n (finiteTreeEvent fun t => r ≤ |(height t : ℝ) - L|) ≤
      conditioned μ n (finiteTreeEvent fun t => ¬ (height t : ℝ) < L + r) +
      conditioned μ n (finiteTreeEvent fun t => ¬ (L + 1) - r ≤ (height t : ℝ)) := by
  apply le_trans (measure_mono ?_) (measure_union_le _ _)
  rintro _ ⟨t, ht, rfl⟩
  change r ≤ |(height t : ℝ) - L| at ht
  by_cases htu : (height t : ℝ) < L + r
  · refine Or.inr ⟨t, ?_, rfl⟩
    simp only [Set.mem_ofPred_eq, not_le]
    by_cases hsign : 0 ≤ (height t : ℝ) - L
    · rw [abs_of_nonneg hsign] at ht
      linarith
    · rw [abs_of_neg (lt_of_not_ge hsign)] at ht
      linarith
  · exact Or.inl ⟨t, htu, rfl⟩


/-- Upper half of the arbitrary-rate height concentration. -/
theorem m5Upper_rate_tail_tendsto_zero (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (r : ℕ → ℝ)
    (hr : Tendsto r atTop atTop) :
    Tendsto (fun n : ℕ => conditioned μ n (finiteTreeEvent fun t =>
      ¬ (height t : ℝ) < max
        (m5LogHeight (offspringMean μ).toReal n + r n) 1)) atTop (𝓝 0) := by
  let m := (offspringMean μ).toReal
  let L := m5LogHeight m
  let hU : ℕ → ℝ := fun n => max (L n + r n) 1
  have hLtop : Tendsto L atTop atTop := m5LogHeight_tendsto μ hμ
  have hplus : Tendsto (fun n => L n + r n) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hLtop
    filter_upwards [hr (eventually_ge_atTop 0)] with n hn
    change 0 ≤ r n at hn
    linarith
  have hUpos : ∀ n, 0 < hU n := fun n => lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hUtop : Tendsto hU atTop atTop :=
    tendsto_atTop_mono' atTop (Eventually.of_forall fun n => le_max_left _ _) hplus
  have hQUraw := m5Expected_upper_tendsto_zero μ hμ r hr
  have hQU : Tendsto (fun n : ℕ => (n : ℝ) * (survival μ ⌈hU n⌉₊).toReal)
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun n => by positivity) _
      (by simpa only [L, m] using hQUraw)
    exact Eventually.of_forall fun n => mul_le_mul_of_nonneg_left
      (m5Survival_real_antitone μ hμ (le_max_left _ _)) (by positivity)
  have hc := m5Conditioned_compl_tendsto_zero μ hμ
    (fun n t => (height t : ℝ) < hU n)
    (paper_height_upper μ hμ hU hUpos hUtop hQU)
  simpa only [hU, L, m] using hc

/-- Lower half of the arbitrary-rate height concentration. -/
theorem m5Lower_rate_tail_tendsto_zero (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (r : ℕ → ℝ) {c : ℝ}
    (hc : 0 < c) (hu : Tendsto (m5U μ) atTop (𝓝 c))
    (hr : Tendsto r atTop atTop)
    (hrL : ∀ᶠ n in atTop, r n ≤ m5LogHeight (offspringMean μ).toReal n / 2) :
    Tendsto (fun n : ℕ => conditioned μ n (finiteTreeEvent fun t =>
      ¬ max (m5LogHeight (offspringMean μ).toReal n + 1 - r n) 1 ≤
        (height t : ℝ))) atTop (𝓝 0) := by
  let m := (offspringMean μ).toReal
  let L := m5LogHeight m
  let hL : ℕ → ℝ := fun n => max ((L n + 1) - r n) 1
  have hLtop : Tendsto L atTop atTop := m5LogHeight_tendsto μ hμ
  have hhalf : Tendsto (fun n => L n / 2) atTop atTop := hLtop.atTop_div_const (by norm_num)
  have hminus : Tendsto (fun n => (L n + 1) - r n) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hhalf
    filter_upwards [hrL] with n hn
    dsimp [L]
    linarith
  have hLpos : ∀ n, 0 < hL n := fun n => lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hLtop' : Tendsto hL atTop atTop :=
    tendsto_atTop_mono' atTop (Eventually.of_forall fun n => le_max_left _ _) hminus
  have hr' : Tendsto (fun n => r n - 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (-1) hr
  have hminus' : Tendsto (fun n => L n - (r n - 1)) atTop atTop := by
    apply hminus.congr'
    filter_upwards [] with n
    ring
  have hQLraw := m5Expected_lower_tendsto_atTop μ hμ (fun n => r n - 1) hc hu hr'
    (by simpa only [L, m] using hminus')
  have hfun : (fun n => L n - (r n - 1)) = (fun n => (L n + 1) - r n) := by
    funext n
    ring
  have hQLraw0 : Tendsto (fun n : ℕ => (n : ℝ) *
      (survival μ ⌈L n - (r n - 1)⌉₊).toReal) atTop atTop := by
    simpa only [L, m] using hQLraw
  have heq (n : ℕ) : L n - (r n - 1) = (L n + 1) - r n := by ring
  have hQLraw' : Tendsto (fun n : ℕ => (n : ℝ) *
      (survival μ ⌈(L n + 1) - r n⌉₊).toReal) atTop atTop := by
    simpa only [heq] using hQLraw0
  have hQL : Tendsto (fun n : ℕ => (n : ℝ) * (survival μ ⌈hL n⌉₊).toReal)
      atTop atTop := by
    apply hQLraw'.congr'
    filter_upwards [hminus (eventually_gt_atTop 1)] with n hn
    have heq : hL n = (L n + 1) - r n := max_eq_left (by dsimp at hn ⊢; linarith)
    rw [heq]
  have hc := m5Conditioned_compl_tendsto_zero μ hμ
    (fun n t => hL n ≤ (height t : ℝ))
    (paper_height_lower μ hμ hL hLpos hLtop' hQL)
  simpa only [hL, L, m] using hc

lemma m5Centered_tail_of_two_tails (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (r hU hL : ℕ → ℝ)
    (hUeq : ∀ᶠ n in atTop, hU n = m5LogHeight (offspringMean μ).toReal n + r n)
    (hLeq : ∀ᶠ n in atTop, hL n =
      m5LogHeight (offspringMean μ).toReal n + 1 - r n)
    (hTU : Tendsto (fun n : ℕ => conditioned μ n (finiteTreeEvent fun t =>
      ¬ (height t : ℝ) < hU n)) atTop (𝓝 0))
    (hTL : Tendsto (fun n : ℕ => conditioned μ n (finiteTreeEvent fun t =>
      ¬ hL n ≤ (height t : ℝ))) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => conditioned μ n (finiteTreeEvent fun t =>
      r n ≤ |(height t : ℝ) - m5LogHeight (offspringMean μ).toReal n|))
      atTop (𝓝 0) := by
  have hsum := hTU.add hTL
  simp only [add_zero] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun n => bot_le)
  filter_upwards [hUeq, hLeq] with n hUn hLn
  rw [hUn, hLn]
  exact m5Conditioned_centered_tail_le_add μ n _ _

/-- Any diverging rate bounded above by half the logarithmic centre gives
vanishing centred height tails when the normalized survival probabilities have
a positive limit. -/
theorem m5Centered_tail_tendsto_zero_of_pos_limit
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (r : ℕ → ℝ) {c : ℝ}
    (hc : 0 < c) (hu : Tendsto (m5U μ) atTop (𝓝 c))
    (hr : Tendsto r atTop atTop)
    (hrL : ∀ᶠ n in atTop, r n ≤ m5LogHeight (offspringMean μ).toReal n / 2) :
    Tendsto (fun n : ℕ => conditioned μ n (finiteTreeEvent fun t =>
      r n ≤ |(height t : ℝ) - m5LogHeight (offspringMean μ).toReal n|))
      atTop (𝓝 0) := by
  let m := (offspringMean μ).toReal
  let L := m5LogHeight m
  let hU : ℕ → ℝ := fun n => max (L n + r n) 1
  let hL : ℕ → ℝ := fun n => max ((L n + 1) - r n) 1
  have hLtop : Tendsto L atTop atTop := m5LogHeight_tendsto μ hμ
  have hplus : Tendsto (fun n => L n + r n) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hLtop
    filter_upwards [hr (eventually_ge_atTop 0)] with n hn
    change 0 ≤ r n at hn
    linarith
  have hminus : Tendsto (fun n => (L n + 1) - r n) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ (hLtop.atTop_div_const (by norm_num : (0 : ℝ) < 2))
    filter_upwards [hrL] with n hn
    dsimp [L]
    linarith
  apply m5Centered_tail_of_two_tails μ r hU hL _ _
    (m5Upper_rate_tail_tendsto_zero μ hμ r hr)
    (m5Lower_rate_tail_tendsto_zero μ hμ r hc hu hr hrL)
  · filter_upwards [hplus (eventually_gt_atTop 1)] with n hn
    change 1 < L n + r n at hn
    exact max_eq_left (by linarith)
  · filter_upwards [hminus (eventually_gt_atTop 1)] with n hn
    change 1 < (L n + 1) - r n at hn
    exact max_eq_left (by linarith)

end
end SubcriticalCauchy.Bienayme
