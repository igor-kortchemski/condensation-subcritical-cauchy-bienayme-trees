module

public import SubcriticalCauchy.MainProofs.M5Aux

/-!
# The non-summable diagonal for M5

If `u_n = Q_n / m^n → 0`, a logarithmic diagonal supplies `r_n → ∞`
with `n Q_{L_n-r_n} → 0`.  The `max ... 1` guard only totalizes the
threshold at the first finitely many indices.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section
open BGW BGW.LocallyFinite

attribute [local instance] Classical.propDecidable

/-- Normalized survival sampled at half the logarithmic height. -/
def m5DiagonalSample (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) : ℝ :=
  m5U μ ⌈max (m5LogHeight (offspringMean μ).toReal n / 2) 0⌉₊

/-- A slow diagonal tending to infinity, bounded above by half the centre. -/
def m5DiagonalRate (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) : ℝ :=
  min (m5LogHeight (offspringMean μ).toReal n / 2)
    ((-Real.log (m5DiagonalSample μ n)) /
      (2 * Real.log (1 / (offspringMean μ).toReal)))

lemma m5DiagonalSample_pos (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (n : ℕ) :
    0 < m5DiagonalSample μ n := m5U_pos μ hμ _

lemma m5DiagonalSample_tendsto_zero (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ)
    (hu : Tendsto (m5U μ) atTop (𝓝 0)) :
    Tendsto (m5DiagonalSample μ) atTop (𝓝 0) := by
  let m := (offspringMean μ).toReal
  have hhalf : Tendsto (fun n => max (m5LogHeight m n / 2) 0) atTop atTop := by
    apply (m5LogHeight_tendsto μ hμ).atTop_div_const (by norm_num : (0 : ℝ) < 2) |>.congr'
    filter_upwards [(m5LogHeight_tendsto μ hμ) (eventually_ge_atTop 0)] with n hn
    change 0 ≤ m5LogHeight (offspringMean μ).toReal n at hn
    exact (max_eq_left (by linarith)).symm
  have hceil : Tendsto (fun n => ⌈max (m5LogHeight m n / 2) 0⌉₊) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [hhalf (eventually_ge_atTop (b : ℝ))] with n hn
    exact_mod_cast hn.trans (Nat.le_ceil _)
  exact hu.comp hceil

lemma m5DiagonalRate_tendsto (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ)
    (hu : Tendsto (m5U μ) atTop (𝓝 0)) :
    Tendsto (m5DiagonalRate μ) atTop atTop := by
  let m := (offspringMean μ).toReal
  have ha := m5DiagonalSample_tendsto_zero μ hμ hu
  have haw : Tendsto (m5DiagonalSample μ) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨ha, Eventually.of_forall (m5DiagonalSample_pos μ hμ)⟩
  have hlog : Tendsto (fun n => -Real.log (m5DiagonalSample μ n)) atTop atTop :=
    tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp haw)
  have hd : 0 < 2 * Real.log (1 / m) := by linarith [m5LogDenom_pos μ hμ]
  have hright : Tendsto (fun n => (-Real.log (m5DiagonalSample μ n)) /
      (2 * Real.log (1 / m))) atTop atTop := hlog.atTop_div_const hd
  have hleft : Tendsto (fun n => m5LogHeight m n / 2) atTop atTop :=
    (m5LogHeight_tendsto μ hμ).atTop_div_const (by norm_num)
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [hleft (eventually_ge_atTop b), hright (eventually_ge_atTop b)] with n hnl hnr
  exact le_min hnl hnr

lemma m5DiagonalRate_le_half (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) :
    m5DiagonalRate μ n ≤ m5LogHeight (offspringMean μ).toReal n / 2 :=
  min_le_left _ _

lemma m5DiagonalRate_le_log (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) :
    m5DiagonalRate μ n ≤ (-Real.log (m5DiagonalSample μ n)) /
      (2 * Real.log (1 / (offspringMean μ).toReal)) :=
  min_le_right _ _

lemma m5Diagonal_geometric_bound (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) {r a : ℝ}
    (ha : 0 < a)
    (hr : Real.log (1 / (offspringMean μ).toReal) * r ≤ (-Real.log a) / 2) :
    a * (offspringMean μ).toReal ^ (-r) ≤ Real.exp (Real.log a / 2) := by
  have hm0 := m5MeanReal_pos μ hμ
  have hrpow : (offspringMean μ).toReal ^ (-r) =
      Real.exp (Real.log (1 / (offspringMean μ).toReal) * r) := by
    rw [Real.rpow_def_of_pos hm0, one_div, Real.log_inv]
    congr 1
    ring
  calc
    a * (offspringMean μ).toReal ^ (-r) = Real.exp (Real.log a) *
        Real.exp (Real.log (1 / (offspringMean μ).toReal) * r) := by
      rw [Real.exp_log ha, hrpow]
    _ = Real.exp (Real.log a + Real.log (1 / (offspringMean μ).toReal) * r) :=
      (Real.exp_add _ _).symm
    _ ≤ Real.exp (Real.log a / 2) := Real.exp_le_exp.mpr (by linarith)

lemma m5Diagonal_expected_bound (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * (survival μ ⌈max
      (m5LogHeight (offspringMean μ).toReal n - m5DiagonalRate μ n) 1⌉₊).toReal ≤
      Real.exp (Real.log (m5DiagonalSample μ n) / 2) := by
  let m := (offspringMean μ).toReal
  let a := m5DiagonalSample μ n
  let r := m5DiagonalRate μ n
  let h := m5LogHeight m n - r
  have hm0 := m5MeanReal_pos μ hμ
  have hm1 := (m5MeanReal_lt_one μ hμ).le
  have hhalf : m5LogHeight m n / 2 ≤ max h 1 := by
    apply le_trans _ (le_max_left h 1)
    dsimp [h]
    linarith [m5DiagonalRate_le_half μ n]
  have hzero : (0 : ℝ) ≤ max h 1 := by positivity
  have hidx : ⌈max (m5LogHeight m n / 2) 0⌉₊ ≤ ⌈max h 1⌉₊ :=
    Nat.ceil_mono (max_le hhalf hzero)
  have hu : m5U μ ⌈max h 1⌉₊ ≤ a := m5U_antitone μ hμ hidx
  have hp : m ^ ⌈max h 1⌉₊ ≤ m ^ h :=
    (m5Pow_ceil_le_rpow hm0 hm1 (max h 1)).trans
      (Real.rpow_le_rpow_of_exponent_ge hm0 hm1 (le_max_left h 1))
  have hbound : (survival μ ⌈max h 1⌉₊).toReal ≤ a * m ^ h := by
    rw [m5Survival_eq_u_mul_pow μ hμ]
    exact mul_le_mul hu hp (by positivity) (m5U_pos μ hμ _).le
  calc
    (n : ℝ) * (survival μ ⌈max
      (m5LogHeight (offspringMean μ).toReal n - m5DiagonalRate μ n) 1⌉₊).toReal ≤
        (n : ℝ) * (a * m ^ h) := mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = a * ((n : ℝ) * m ^ h) := by ring
    _ = a * m ^ (-r) := by
      rw [show h = m5LogHeight m n + (-r) by ring]
      congr 1
      simpa only [m5LogHeight] using
        (m5Nat_mul_rpow_logHeight m (-r) hm0 (m5MeanReal_lt_one μ hμ) n hn)
    _ ≤ Real.exp (Real.log a / 2) := by
      apply m5Diagonal_geometric_bound μ hμ (m5DiagonalSample_pos μ hμ n)
      have hd : 0 < Real.log (1 / m) := m5LogDenom_pos μ hμ
      have hrle : r ≤ (-Real.log a) / (2 * Real.log (1 / m)) :=
        m5DiagonalRate_le_log μ n
      apply (le_div_iff₀ (by positivity : 0 < 2 * Real.log (1 / m))).mp at hrle
      linarith

lemma m5Diagonal_expected_tendsto_zero (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ)
    (hu : Tendsto (m5U μ) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (n : ℝ) * (survival μ ⌈max
      (m5LogHeight (offspringMean μ).toReal n - m5DiagonalRate μ n) 1⌉₊).toReal)
      atTop (𝓝 0) := by
  have ha := m5DiagonalSample_tendsto_zero μ hμ hu
  have haw : Tendsto (m5DiagonalSample μ) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨ha, Eventually.of_forall (m5DiagonalSample_pos μ hμ)⟩
  have hlog : Tendsto (fun n => Real.log (m5DiagonalSample μ n)) atTop atBot :=
    Real.tendsto_log_nhdsGT_zero.comp haw
  have hlim : Tendsto (fun n => Real.exp (Real.log (m5DiagonalSample μ n) / 2))
      atTop (𝓝 0) := Real.tendsto_exp_atBot.comp (hlog.atBot_div_const (by norm_num))
  apply squeeze_zero' (Eventually.of_forall fun n => by positivity) _ hlim
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact m5Diagonal_expected_bound μ hμ hn

lemma m5Diagonal_height_tendsto_one (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ)
    (hu : Tendsto (m5U μ) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => conditioned μ n (finiteTreeEvent fun t =>
      (height t : ℝ) < max
        (m5LogHeight (offspringMean μ).toReal n - m5DiagonalRate μ n) 1))
      atTop (𝓝 1) := by
  let h : ℕ → ℝ := fun n => max
    (m5LogHeight (offspringMean μ).toReal n - m5DiagonalRate μ n) 1
  apply paper_height_upper μ hμ h (fun n => lt_of_lt_of_le zero_lt_one (le_max_right _ _)) _
    (m5Diagonal_expected_tendsto_zero μ hμ hu)
  apply tendsto_atTop_mono' atTop _
    ((m5LogHeight_tendsto μ hμ).atTop_div_const (by norm_num : (0 : ℝ) < 2))
  exact Eventually.of_forall fun n => le_trans (by
    dsimp
    linarith [m5DiagonalRate_le_half μ n]) (le_max_left _ _)

end
end SubcriticalCauchy.Bienayme
