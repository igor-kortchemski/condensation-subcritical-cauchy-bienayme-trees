module

public import SubcriticalCauchy.SurvivalCriterionAux

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Heathcote--Seneta--Vere-Jones survival criterion

For a positive-mean subcritical Bienaymé law, the survival probability divided by
the `n`-th power of the mean has a positive limit exactly when the offspring law
has finite `k log k` moment. Otherwise its limit is zero.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology BigOperators

namespace SubcriticalCauchy.Bienayme

lemma antitone_prod_one_sub {x : ℕ → ℝ} (hx0 : ∀ n, 0 ≤ x n) (hx1 : ∀ n, x n < 1) :
    Antitone (fun n : ℕ => ∏ k ∈ Finset.range n, (1 - x k)) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [Finset.prod_range_succ]
  have hp : 0 ≤ ∏ k ∈ Finset.range n, (1 - x k) :=
    Finset.prod_nonneg fun k _ => sub_nonneg.mpr (hx1 k).le
  have hf0 : 0 ≤ 1 - x n := sub_nonneg.mpr (hx1 n).le
  have hf1 : 1 - x n ≤ 1 := by linarith [hx0 n]
  exact mul_le_of_le_one_right hp hf1

/-- Positive convergence of a product of factors `1 - x n`, with
`0 ≤ x n < 1`, is equivalent to summability of `x`. -/
lemma exists_pos_tendsto_prod_one_sub_iff_summable {x : ℕ → ℝ}
    (hx0 : ∀ n, 0 ≤ x n) (hx1 : ∀ n, x n < 1) :
    (∃ c : ℝ, 0 < c ∧ Tendsto (fun n : ℕ => ∏ k ∈ Finset.range n, (1 - x k))
      atTop (𝓝 c)) ↔ Summable x := by
  let u : ℕ → ℝ := fun n => ∏ k ∈ Finset.range n, (1 - x k)
  have hf (n : ℕ) : 0 < 1 - x n := sub_pos.mpr (hx1 n)
  have hu (n : ℕ) : 0 < u n := Finset.prod_pos fun k _ => hf k
  have hanti : Antitone u := antitone_prod_one_sub hx0 hx1
  constructor
  · rintro ⟨c, hc, hlim⟩
    have hlogc (n : ℕ) : Real.log c ≤ Real.log (u n) :=
      Real.log_le_log hc (hanti.le_of_tendsto hlim n)
    have hlogprod (n : ℕ) : Real.log (u n) = ∑ k ∈ Finset.range n, Real.log (1 - x k) := by
      exact Real.log_prod (fun k hk => (hf k).ne')
    have hsum (n : ℕ) : (∑ k ∈ Finset.range n, x k) ≤ -Real.log c := by
      calc
        (∑ k ∈ Finset.range n, x k) ≤ ∑ k ∈ Finset.range n, -Real.log (1 - x k) := by
          apply Finset.sum_le_sum
          intro k hk
          have hlog := Real.log_le_sub_one_of_pos (hf k)
          linarith
        _ = -Real.log (u n) := by rw [hlogprod, Finset.sum_neg_distrib]
        _ ≤ -Real.log c := neg_le_neg (hlogc n)
    exact summable_of_sum_range_le hx0 hsum
  · intro hs
    have hlogs : Summable (fun n => Real.log (1 - x n)) := by
      simpa only [sub_eq_add_neg] using Real.summable_log_one_add_of_summable hs.neg
    refine ⟨Real.exp (∑' n, Real.log (1 - x n)), Real.exp_pos _, ?_⟩
    exact (Real.hasProd_of_hasSum_log hf hlogs.hasSum).tendsto_prod_nat

lemma survival_div_mean_pow_eq_prod (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm0 : 0 < offspringMean μ) (hm1 : offspringMean μ < 1) (n : ℕ) :
    (survival μ n).toReal / (offspringMean μ).toReal ^ n =
      ∏ k ∈ Finset.range n,
        (1 - survivalCorrection μ (survival μ k).toReal / (offspringMean μ).toReal) := by
  have hm : offspringMean μ ≠ ∞ := ne_top_of_lt (hm1.trans ENNReal.one_lt_top)
  have hM : 0 < (offspringMean μ).toReal := ENNReal.toReal_pos hm0.ne' hm
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      (survival μ (n + 1)).toReal / (offspringMean μ).toReal ^ (n + 1) =
          ((survival μ n).toReal / (offspringMean μ).toReal ^ n) *
            (1 - survivalCorrection μ (survival μ n).toReal / (offspringMean μ).toReal) := by
        rw [survival_toReal_succ_correction μ hm n, pow_succ]
        field_simp [hM.ne']
      _ = _ := by rw [ih, Finset.prod_range_succ]

lemma summable_survivalCorrection_survival_iff (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm0 : 0 < offspringMean μ) (hm1 : offspringMean μ < 1) :
    Summable (fun n : ℕ => survivalCorrection μ (survival μ n).toReal) ↔
      Summable (fun k : ℕ => (k : ℝ) * Real.log k * (μ {k}).toReal) := by
  have hm : offspringMean μ ≠ ∞ := ne_top_of_lt (hm1.trans ENNReal.one_lt_top)
  have hM0 : 0 < (offspringMean μ).toReal := ENNReal.toReal_pos hm0.ne' hm
  have hM1 : (offspringMean μ).toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hm ENNReal.one_ne_top).mpr hm1
  let M := (offspringMean μ).toReal
  let a : ℕ → ℝ := fun n => survivalCorrection μ (M ^ n)
  have ha0 (n : ℕ) : 0 ≤ a n :=
    (survivalCorrection_bounds μ hm (pow_nonneg hM0.le _) (pow_le_one₀ hM0.le hM1.le)).1
  have hanti : Antitone a := by
    intro m n hmn
    exact survivalCorrection_monotoneOn μ hm
      ⟨pow_nonneg hM0.le _, pow_le_one₀ hM0.le hM1.le⟩
      ⟨pow_nonneg hM0.le _, pow_le_one₀ hM0.le hM1.le⟩
      (pow_le_pow_of_le_one hM0.le hM1.le hmn)
  have hupper (n : ℕ) : survivalCorrection μ (survival μ n).toReal ≤ a n := by
    apply survivalCorrection_monotoneOn μ hm
      ⟨ENNReal.toReal_nonneg, (ENNReal.toReal_le_of_le_ofReal zero_le_one
        (by simpa using survival_le_one μ n))⟩
      ⟨pow_nonneg hM0.le _, pow_le_one₀ hM0.le hM1.le⟩
    exact (survival_geometric_bounds μ hm0 hm1).1 n
  have hmain : Summable (fun n : ℕ => survivalCorrection μ (survival μ n).toReal) ↔
      Summable a := by
    constructor
    · intro hs
      have heta0 : 0 < M - M ^ 2 := by dsimp [M]; nlinarith
      have hetaM : M - M ^ 2 < M := by nlinarith
      have hlower := (survival_geometric_bounds μ hm0 hm1).2 (M - M ^ 2) heta0 hetaM
      have hlower' : ∀ᶠ n : ℕ in atTop, (M ^ 2) ^ n ≤ (survival μ n).toReal := by
        simpa only [M, sub_sub_cancel] using hlower
      have hsample : Summable (fun n : ℕ => a (2 * n)) := by
        apply hs.of_norm_bounded_eventually
        filter_upwards [Nat.cofinite_eq_atTop ▸ hlower'] with n hn
        have hpow : M ^ (2 * n) ≤ (survival μ n).toReal := by
          simpa only [pow_mul, pow_two] using hn
        have hle := survivalCorrection_monotoneOn μ hm
          ⟨pow_nonneg hM0.le _, pow_le_one₀ hM0.le hM1.le⟩
          ⟨ENNReal.toReal_nonneg, (ENNReal.toReal_le_of_le_ofReal zero_le_one
            (by simpa using survival_le_one μ n))⟩ hpow
        rw [Real.norm_eq_abs, abs_of_nonneg (ha0 (2 * n))]
        simpa only [a, pow_mul, pow_two] using hle
      exact summable_of_summable_mul_of_antitone hanti ha0 (by omega : 0 < 2) hsample
    · intro hs
      exact hs.of_nonneg_of_le
        (fun n => (survivalCorrection_bounds μ hm ENNReal.toReal_nonneg
          (ENNReal.toReal_le_of_le_ofReal zero_le_one
            (by simpa using survival_le_one μ n))).1) hupper
  have hgeom : Summable a ↔ Summable (fun n : ℕ => survivalCorrection μ ((1 / 2 : ℝ) ^ n)) := by
    apply summable_geometric_comp_iff hM0 hM1 (by norm_num) (by norm_num)
    · exact survivalCorrection_monotoneOn μ hm
    · intro q hq
      exact (survivalCorrection_bounds μ hm hq.1 hq.2).1
  exact hmain.trans (hgeom.trans (summable_survivalCorrection_half_iff_mass_mul_log μ hm))

/-- The normalized survival probabilities are decreasing. -/
theorem survival_div_mean_pow_antitone
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm0 : 0 < offspringMean μ) (hm1 : offspringMean μ < 1) :
    Antitone (fun n : ℕ => (survival μ n).toReal / (offspringMean μ).toReal ^ n) := by
  have hm : offspringMean μ ≠ ∞ := ne_top_of_lt (hm1.trans ENNReal.one_lt_top)
  have hM0 : 0 < (offspringMean μ).toReal := ENNReal.toReal_pos hm0.ne' hm
  have hM1 : (offspringMean μ).toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hm ENNReal.one_ne_top).mpr hm1
  simp_rw [survival_div_mean_pow_eq_prod μ hm0 hm1]
  apply antitone_prod_one_sub
  · intro n
    exact div_nonneg (survivalCorrection_bounds μ hm ENNReal.toReal_nonneg
      (ENNReal.toReal_le_of_le_ofReal zero_le_one
        (by simpa using survival_le_one μ n))).1 hM0.le
  · intro n
    exact (div_lt_one hM0).mpr (survivalCorrection_lt_mean μ hm hm0
      ENNReal.toReal_nonneg (ENNReal.toReal_le_of_le_ofReal zero_le_one
        (by simpa using survival_le_one μ n)))

/-- The Heathcote--Seneta--Vere-Jones criterion, in its positive-limit form. -/
theorem survival_div_mean_pow_tendsto_pos_iff
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm0 : 0 < offspringMean μ) (hm1 : offspringMean μ < 1) :
    (∃ c : ℝ, 0 < c ∧ Tendsto
        (fun n : ℕ => (survival μ n).toReal / (offspringMean μ).toReal ^ n)
        atTop (𝓝 c)) ↔
      Summable (fun k : ℕ => (k : ℝ) * Real.log k * (μ {k}).toReal) := by
  have hm : offspringMean μ ≠ ∞ := ne_top_of_lt (hm1.trans ENNReal.one_lt_top)
  have hM0 : 0 < (offspringMean μ).toReal := ENNReal.toReal_pos hm0.ne' hm
  have hM1 : (offspringMean μ).toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hm ENNReal.one_ne_top).mpr hm1
  simp_rw [survival_div_mean_pow_eq_prod μ hm0 hm1]
  have hx0 (n : ℕ) : 0 ≤ survivalCorrection μ (survival μ n).toReal /
      (offspringMean μ).toReal :=
    div_nonneg (survivalCorrection_bounds μ hm ENNReal.toReal_nonneg
      (ENNReal.toReal_le_of_le_ofReal zero_le_one
        (by simpa using survival_le_one μ n))).1 hM0.le
  have hx1 (n : ℕ) : survivalCorrection μ (survival μ n).toReal /
      (offspringMean μ).toReal < 1 :=
    (div_lt_one hM0).mpr (survivalCorrection_lt_mean μ hm hm0
      ENNReal.toReal_nonneg (ENNReal.toReal_le_of_le_ofReal zero_le_one
        (by simpa using survival_le_one μ n)))
  rw [exists_pos_tendsto_prod_one_sub_iff_summable hx0 hx1]
  have hdiv : Summable (fun n : ℕ => survivalCorrection μ (survival μ n).toReal /
      (offspringMean μ).toReal) ↔
      Summable (fun n : ℕ => survivalCorrection μ (survival μ n).toReal) :=
    summable_div_const_iff hM0.ne'
  exact hdiv.trans (summable_survivalCorrection_survival_iff μ hm0 hm1)

/-- In the non-summable case the decreasing normalized survival sequence has
limit zero. -/
theorem survival_div_mean_pow_tendsto_zero
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm0 : 0 < offspringMean μ) (hm1 : offspringMean μ < 1)
    (h : ¬ Summable (fun k : ℕ => (k : ℝ) * Real.log k * (μ {k}).toReal)) :
    Tendsto (fun n : ℕ => (survival μ n).toReal / (offspringMean μ).toReal ^ n)
      atTop (𝓝 0) := by
  let u : ℕ → ℝ := fun n => (survival μ n).toReal / (offspringMean μ).toReal ^ n
  have hanti : Antitone u := survival_div_mean_pow_antitone μ hm0 hm1
  have hu0 (n : ℕ) : 0 ≤ u n := by
    exact div_nonneg ENNReal.toReal_nonneg (pow_nonneg ENNReal.toReal_nonneg _)
  have hbdd : BddBelow (Set.range u) := ⟨0, by rintro _ ⟨n, rfl⟩; exact hu0 n⟩
  have hlim : Tendsto u atTop (𝓝 (⨅ n, u n)) := tendsto_atTop_ciInf hanti hbdd
  have hc0 : 0 ≤ ⨅ n, u n := ge_of_tendsto hlim (Eventually.of_forall hu0)
  have hc : (⨅ n, u n) = 0 := by
    apply le_antisymm _ hc0
    by_contra hn
    have hcpos : 0 < ⨅ n, u n := lt_of_not_ge hn
    have hmass := (survival_div_mean_pow_tendsto_pos_iff μ hm0 hm1).mp
      ⟨⨅ n, u n, hcpos, hlim⟩
    exact h hmass
  simpa only [u, hc] using hlim

end SubcriticalCauchy.Bienayme
