module

public import SubcriticalCauchy.HeightSecondOrderRecurrence
public import SubcriticalCauchy.HeightSecondOrderAux
public import SubcriticalCauchy.Propositions42_43
public import SubcriticalCauchy.BienaymeForestLog

/-!
# Second-order expansion of the normalized survival probabilities

The sole heavy-tail input is the stated right-neighborhood asymptotic for the
survival correction.  No result in this module assumes the tail asymptotic
used in the frozen tail-based formulation of Proposition 4.5.
-/

@[expose] public section

open MeasureTheory Filter Finset
open scoped ENNReal Topology BigOperators

namespace SubcriticalCauchy.Bienayme

noncomputable section
open BGW BGW.LocallyFinite

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

private theorem mean_real_pos (hμ : IsMeasurableSubcriticalCauchyOffspring μ) :
    0 < (offspringMean μ).toReal := by
  have hm0 : 0 < offspringMean μ := offspringMean_pos_of_paper μ hμ.to_literal
  exact ENNReal.toReal_pos hm0.ne'
    (ne_top_of_lt (hμ.1.trans ENNReal.one_lt_top))

omit [IsProbabilityMeasure μ] in
private theorem mean_real_lt_one (hμ : IsMeasurableSubcriticalCauchyOffspring μ) :
    (offspringMean μ).toReal < 1 := by
  have hfin : offspringMean μ ≠ ∞ := ne_top_of_lt (hμ.1.trans ENNReal.one_lt_top)
  simpa using (ENNReal.toReal_lt_toReal hfin ENNReal.one_ne_top).mpr hμ.1

private theorem mean_log_pos (hμ : IsMeasurableSubcriticalCauchyOffspring μ) :
    0 < Real.log (1 / (offspringMean μ).toReal) :=
  log_inv_mean_pos (mean_real_pos hμ) (mean_real_lt_one hμ)

private theorem normalizedSurvival_pos (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (n : ℕ) :
    0 < normalizedSurvival μ n := by
  exact div_pos (survival_toReal_pos μ (offspringMean_pos_of_paper μ hμ.to_literal) n)
    (pow_pos (mean_real_pos hμ) n)

/-- Exact normalized recurrence, with the correction divided by the mean. -/
theorem normalizedSurvival_succ (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (n : ℕ) :
    normalizedSurvival μ (n + 1) = normalizedSurvival μ n *
      (1 - survivalCorrection μ (survival μ n).toReal /
        (offspringMean μ).toReal) := by
  have hm := mean_real_pos hμ
  have hQ := survival_toReal_pos μ (offspringMean_pos_of_paper μ hμ.to_literal) n
  rw [normalizedSurvival, normalizedSurvival,
    survival_toReal_succ_correction μ (ne_top_of_lt (hμ.1.trans ENNReal.one_lt_top))]
  field_simp [hm.ne', pow_ne_zero n hm.ne']
  ring

/-- The inverse logarithm of `Q_n` is asymptotic to `n log(1/m)`. -/
theorem log_inv_survival_div_nat_mul_log_inv_mean (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (hμ : IsMeasurableSubcriticalCauchyOffspring μ) :
    Tendsto (fun n : ℕ => Real.log ((survival μ n).toReal)⁻¹ /
      ((n : ℝ) * Real.log (1 / (offspringMean μ).toReal))) atTop (𝓝 1) := by
  let a := Real.log (1 / (offspringMean μ).toReal)
  have ha : 0 < a := mean_log_pos hμ
  have hu := (log_inv_normalizedSurvival_div_nat μ hμ).div_const a
  rw [zero_div] at hu
  have hh := (tendsto_const_nhds (x := (1 : ℝ))).add hu
  rw [add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hm : (offspringMean μ).toReal ≠ 0 := (mean_real_pos hμ).ne'
  have hQ : (survival μ n).toReal ≠ 0 :=
    (survival_toReal_pos μ (offspringMean_pos_of_paper μ hμ.to_literal) n).ne'
  have hu0 : normalizedSurvival μ n ≠ 0 := (normalizedSurvival_pos μ hμ n).ne'
  have ha0 : a ≠ 0 := ha.ne'
  have hlogm : Real.log (1 / (offspringMean μ).toReal) =
      -Real.log (offspringMean μ).toReal := by rw [one_div, Real.log_inv]
  simp only [a] at ha0 ⊢
  rw [show Real.log ((survival μ n).toReal)⁻¹ =
      (n : ℝ) * a + Real.log (1 / normalizedSurvival μ n) by
    simp only [normalizedSurvival, one_div, Real.log_inv, Real.log_div hQ
      (pow_ne_zero n hm), Real.log_pow]
    dsimp [a]
    rw [hlogm]
    ring]
  field_simp
  ring

/-- The local correction hypothesis transported from a right neighborhood of
zero to the survival sequence. -/
theorem survivalCorrection_survival_div_model (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (hμ : IsMeasurableSubcriticalCauchyOffspring μ)
    {c β : ℝ} (hc : 0 < c) (hβ0 : 0 < β)
    (hℓ : Tendsto (fun x => survivalCorrection μ x /
      (c / (β * Real.log x⁻¹ ^ β))) (𝓝[>] 0) (𝓝 1)) :
    Tendsto (fun n : ℕ => survivalCorrection μ (survival μ n).toReal /
      (c / (β * ((n : ℝ) * Real.log (1 / (offspringMean μ).toReal)) ^ β)))
      atTop (𝓝 1) := by
  let a := Real.log (1 / (offspringMean μ).toReal)
  have ha : 0 < a := mean_log_pos hμ
  have hQ0 : Tendsto (fun n => (survival μ n).toReal) atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨survival_toReal_tendsto_zero μ hμ.1, ?_⟩
    exact Eventually.of_forall fun n =>
      survival_toReal_pos μ (offspringMean_pos_of_paper μ hμ.to_literal) n
  have hcomp := hℓ.comp hQ0
  let R : ℕ → ℝ := fun n => Real.log ((survival μ n).toReal)⁻¹ / ((n : ℝ) * a)
  have hR : Tendsto R atTop (𝓝 1) := by
    simpa only [R, a] using log_inv_survival_div_nat_mul_log_inv_mean μ hμ
  have hRp : Tendsto (fun n => R n ^ β) atTop (𝓝 1) := by
    have hh := hR.rpow (tendsto_const_nhds (x := β)) (Or.inl one_ne_zero)
    simpa only [Real.one_rpow] using hh
  have hh := hcomp.div hRp one_ne_zero
  rw [div_one] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    (hR.eventually (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)))] with n hn hRn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hna : (n : ℝ) * a ≠ 0 := (mul_pos hn0 ha).ne'
  change (survivalCorrection μ (survival μ n).toReal /
    (c / (β * Real.log ((survival μ n).toReal)⁻¹ ^ β))) / R n ^ β =
    survivalCorrection μ (survival μ n).toReal /
      (c / (β * ((n : ℝ) * a) ^ β))
  have hlog : Real.log ((survival μ n).toReal)⁻¹ = R n * ((n : ℝ) * a) := by
    dsimp [R]
    field_simp
  rw [hlog]
  rw [Real.mul_rpow hRn.le (mul_nonneg hn0.le ha.le)]
  simp only [a] at hna ⊢
  field_simp


/-- Logarithmic increments of normalized survival, normalized by the
non-integrated second-order rate. -/
theorem log_normalizedSurvival_increment_div_rate (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (hμ : IsMeasurableSubcriticalCauchyOffspring μ)
    {c β : ℝ} (hc : 0 < c) (hβ0 : 0 < β)
    (hℓ : Tendsto (fun x => survivalCorrection μ x /
      (c / (β * Real.log x⁻¹ ^ β))) (𝓝[>] 0) (𝓝 1)) :
    Tendsto (fun n : ℕ =>
      (Real.log (normalizedSurvival μ (n + 1)) - Real.log (normalizedSurvival μ n)) /
        ((c / (β * (offspringMean μ).toReal *
          Real.log (1 / (offspringMean μ).toReal) ^ β)) *
            ((n : ℝ) + 1) ^ (-β))) atTop (𝓝 (-1)) := by
  let m := (offspringMean μ).toReal
  let a := Real.log (1 / m)
  let Q : ℕ → ℝ := fun n => (survival μ n).toReal
  let ell : ℕ → ℝ := fun n => survivalCorrection μ (Q n)
  let model : ℕ → ℝ := fun n => c / (β * ((n : ℝ) * a) ^ β)
  let rate : ℕ → ℝ := fun n => (c / (β * m * a ^ β)) * ((n : ℝ) + 1) ^ (-β)
  have hm : 0 < m := mean_real_pos hμ
  have ha : 0 < a := mean_log_pos hμ
  have hmodel : Tendsto (fun n => ell n / model n) atTop (𝓝 1) := by
    simpa only [ell, model, Q, a, m] using
      survivalCorrection_survival_div_model μ hμ hc hβ0 hℓ
  have hbase : Tendsto (fun n : ℕ => (((n : ℝ) + 1) / (n : ℝ))) atTop (𝓝 1) := by
    have hz : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 1
    have hh := (tendsto_const_nhds (x := (1 : ℝ))).add hz
    rw [add_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
    field_simp
  have hp : Tendsto (fun n : ℕ => (((n : ℝ) + 1) / (n : ℝ)) ^ β) atTop (𝓝 1) := by
    have hh := hbase.rpow (tendsto_const_nhds (x := β)) (Or.inl one_ne_zero)
    simpa only [Real.one_rpow] using hh
  have hscale : Tendsto (fun n => model n / (m * rate n)) atTop (𝓝 1) := by
    apply hp.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hnp : (c : ℝ) ≠ 0 := hc.ne'
    have hβ' : β ≠ 0 := hβ0.ne'
    have haβ : a ^ β ≠ 0 := (Real.rpow_pos_of_pos ha _).ne'
    have hnβ : (n : ℝ) ^ β ≠ 0 := (Real.rpow_pos_of_pos hn0 _).ne'
    have hnaβ : ((n : ℝ) * a) ^ β ≠ 0 :=
      (Real.rpow_pos_of_pos (mul_pos hn0 ha) _).ne'
    have hNp : (((n : ℝ) + 1) ^ β) ≠ 0 :=
      (Real.rpow_pos_of_pos (by positivity) _).ne'
    simp only [model, rate]
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1),
      Real.mul_rpow hn0.le ha.le, Real.div_rpow (by positivity) (by positivity)]
    field_simp
  have hr : Tendsto (fun n => (ell n / m) / rate n) atTop (𝓝 1) := by
    have hh := hmodel.mul hscale
    rw [mul_one] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hm0 : model n ≠ 0 := by
      dsimp [model]
      exact div_ne_zero hc.ne' (mul_ne_zero hβ0.ne'
        (Real.rpow_pos_of_pos (mul_pos hn0 ha) _).ne')
    dsimp only [rate] at hm0 ⊢
    field_simp
  have hQwithin : Tendsto Q atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨survival_toReal_tendsto_zero μ hμ.1, ?_⟩
    exact Eventually.of_forall fun n =>
      survival_toReal_pos μ (offspringMean_pos_of_paper μ hμ.to_literal) n
  have hell0 : Tendsto ell atTop (𝓝 0) :=
    (survivalCorrection_tendsto_zero μ (ne_top_of_lt (hμ.1.trans ENNReal.one_lt_top))).comp hQwithin
  have hr0 : Tendsto (fun n => ell n / m) atTop (𝓝 0) := by
    simpa [zero_div] using hell0.div_const m
  have hrne : ∀ n, ell n / m ≠ 0 := by
    intro n
    apply div_ne_zero _ hm.ne'
    obtain ⟨k, hk, hμk⟩ := branching_mass_pos μ hμ.to_literal
    exact (survivalCorrection_pos μ
      (ne_top_of_lt (hμ.1.trans ENNReal.one_lt_top)) ⟨k, hk, hμk⟩
      (survival_toReal_pos μ (offspringMean_pos_of_paper μ hμ.to_literal) n)
      (ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using survival_le_one μ n))).ne'
  have hrwithin : Tendsto (fun n => ell n / m) atTop (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hr0, Eventually.of_forall hrne⟩
  have hlog := tendsto_log_one_sub_div_nhdsWithin_zero.comp hrwithin
  have hh := hlog.mul hr
  rw [neg_one_mul] at hh
  apply hh.congr'
  filter_upwards [hr0.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with n hrlt
  have hur : (1 : ℝ) - ell n / m ≠ 0 := by linarith
  have hu : normalizedSurvival μ n ≠ 0 := (normalizedSurvival_pos μ hμ n).ne'
  change (Real.log (1 - ell n / m) / (ell n / m)) * ((ell n / m) / rate n) =
    (Real.log (normalizedSurvival μ (n + 1)) - Real.log (normalizedSurvival μ n)) /
      (c / (β * m * a ^ β) * ((n : ℝ) + 1) ^ (-β))
  rw [normalizedSurvival_succ μ hμ n, Real.log_mul hu hur]
  ring_nf
  dsimp [rate]
  have hw : ((n : ℝ) + 1) ^ (-β) ≠ 0 := (Real.rpow_pos_of_pos (by positivity) _).ne'
  have hellne : ell n ≠ 0 := by
    intro he
    apply hrne n
    simp [he]
  field_simp [hrne n, hw, hellne]
  ring


private theorem log_normalizedSurvival_div_rate_sum (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (hμ : IsMeasurableSubcriticalCauchyOffspring μ)
    {c β : ℝ} (hc : 0 < c) (hβ0 : 0 < β)
    (hℓ : Tendsto (fun x => survivalCorrection μ x /
      (c / (β * Real.log x⁻¹ ^ β))) (𝓝[>] 0) (𝓝 1))
    (hsum : Tendsto (fun n : ℕ => ∑ k ∈ range n, ((k : ℝ) + 1) ^ (-β)) atTop atTop) :
    Tendsto (fun n : ℕ => Real.log (normalizedSurvival μ n) /
      (∑ k ∈ range n, (c / (β * (offspringMean μ).toReal *
        Real.log (1 / (offspringMean μ).toReal) ^ β)) * ((k : ℝ) + 1) ^ (-β)))
      atTop (𝓝 (-1)) := by
  let C := c / (β * (offspringMean μ).toReal *
    Real.log (1 / (offspringMean μ).toReal) ^ β)
  have hC : 0 < C := div_pos hc (mul_pos (mul_pos hβ0 (mean_real_pos hμ))
    (Real.rpow_pos_of_pos (mean_log_pos hμ) _))
  have hw : ∀ n : ℕ, 0 < C * ((n : ℝ) + 1) ^ (-β) := fun n =>
    mul_pos hC (Real.rpow_pos_of_pos (by positivity) _)
  have hwTop : Tendsto (fun n : ℕ =>
      ∑ k ∈ range n, C * ((k : ℝ) + 1) ^ (-β)) atTop atTop := by
    apply hsum.const_mul_atTop hC |>.congr'
    filter_upwards with n
    rw [Finset.mul_sum]
  exact tendsto_sum_weighted_of_tendsto_div_sub (fun n => by simpa only [C] using hw n) hwTop
    (log_normalizedSurvival_increment_div_rate μ hμ hc hβ0 hℓ)

/-- For `β = 1`, the logarithm of normalized survival has the second-order
logarithmic equivalent from Proposition 4.5(i). -/
theorem log_normalizedSurvival_div_log_of_beta_eq_one (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (hμ : IsMeasurableSubcriticalCauchyOffspring μ)
    {c : ℝ} (hc : 0 < c)
    (hℓ : Tendsto (fun x => survivalCorrection μ x /
      (c / (1 * Real.log x⁻¹ ^ (1 : ℝ)))) (𝓝[>] 0) (𝓝 1)) :
    Tendsto (fun n : ℕ => Real.log (normalizedSurvival μ n) / Real.log n)
      atTop (𝓝 (-c / ((offspringMean μ).toReal *
        Real.log (1 / (offspringMean μ).toReal)))) := by
  let a := Real.log (1 / (offspringMean μ).toReal)
  let C := c / ((offspringMean μ).toReal * a)
  have hC : C ≠ 0 := (div_pos hc (mul_pos (mean_real_pos hμ) (mean_log_pos hμ))).ne'
  have hmain := log_normalizedSurvival_div_rate_sum μ hμ hc zero_lt_one hℓ
    (by simpa only [Real.rpow_neg_one] using tendsto_sum_inv_succ_atTop)
  have hweights : (fun n : ℕ =>
      ∑ k ∈ range n, (c / (1 * (offspringMean μ).toReal * a ^ (1 : ℝ))) *
        ((k : ℝ) + 1) ^ (-1 : ℝ)) = (fun n => C * (harmonic n : ℝ)) := by
    funext n
    dsimp [C, a]
    simp only [one_mul, Real.rpow_one, Real.rpow_neg_one]
    rw [← Finset.mul_sum, sum_inv_succ_eq_harmonic]
  have hmain' : Tendsto (fun n : ℕ =>
      Real.log (normalizedSurvival μ n) / (C * (harmonic n : ℝ))) atTop (𝓝 (-1)) := by
    apply hmain.congr'
    filter_upwards with n
    rw [show (∑ k ∈ range n, (c / (1 * (offspringMean μ).toReal * a ^ (1 : ℝ))) *
      ((k : ℝ) + 1) ^ (-1 : ℝ)) = C * (harmonic n : ℝ) from congrFun hweights n]
  clear hmain
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hscale : Tendsto (fun n : ℕ => (C * (harmonic n : ℝ)) / Real.log n)
      atTop (𝓝 C) := by
    have hh := tendsto_harmonic_div_log.const_mul C
    rw [mul_one] at hh
    apply hh.congr'
    filter_upwards with n
    rw [mul_div_assoc]
  have hh := hmain'.mul hscale
  rw [neg_one_mul] at hh
  have hlim : -C = -c / ((offspringMean μ).toReal * a) := by
    dsimp [C]
    ring
  rw [hlim] at hh
  apply hh.congr'
  filter_upwards [hlog.eventually_ne_atTop 0,
    tendsto_sum_inv_succ_atTop.eventually_ne_atTop 0] with n hn hH
  have hH0 : (harmonic n : ℝ) ≠ 0 := by
    rw [← sum_inv_succ_eq_harmonic]
    exact hH
  field_simp

/-- For `0 < β < 1`, the logarithm of normalized survival has the corrected
(R10) polynomial second-order equivalent from Proposition 4.5(ii). -/
theorem log_normalizedSurvival_div_rpow_of_beta_lt_one (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (hμ : IsMeasurableSubcriticalCauchyOffspring μ)
    {c β : ℝ} (hc : 0 < c) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hℓ : Tendsto (fun x => survivalCorrection μ x /
      (c / (β * Real.log x⁻¹ ^ β))) (𝓝[>] 0) (𝓝 1)) :
    Tendsto (fun n : ℕ => Real.log (normalizedSurvival μ n) / (n : ℝ) ^ (1 - β))
      atTop (𝓝 (-c / ((1 - β) * β * (offspringMean μ).toReal *
        Real.log (1 / (offspringMean μ).toReal) ^ β))) := by
  let C := c / (β * (offspringMean μ).toReal *
    Real.log (1 / (offspringMean μ).toReal) ^ β)
  have hp : 0 < 1 - β := sub_pos.mpr hβ1
  have hS : Tendsto (fun n : ℕ => ∑ k ∈ range n, ((k : ℝ) + 1) ^ (-β)) atTop atTop := by
    have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - β)) atTop atTop :=
      (tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop
    have hh := hpow.atTop_mul_pos (div_pos zero_lt_one hp)
      (tendsto_sum_rpow_neg_div_rpow hβ0 hβ1)
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hD : (n : ℝ) ^ (1 - β) ≠ 0 := (Real.rpow_pos_of_pos hn0 _).ne'
    field_simp
  have hmain := log_normalizedSurvival_div_rate_sum μ hμ hc hβ0 hℓ hS
  change Tendsto (fun n : ℕ => Real.log (normalizedSurvival μ n) /
    (∑ k ∈ range n, C * ((k : ℝ) + 1) ^ (-β))) atTop (𝓝 (-1)) at hmain
  have hscale : Tendsto (fun n : ℕ =>
      (∑ k ∈ range n, C * ((k : ℝ) + 1) ^ (-β)) / (n : ℝ) ^ (1 - β))
      atTop (𝓝 (C / (1 - β))) := by
    have hh := (tendsto_sum_rpow_neg_div_rpow hβ0 hβ1).const_mul C
    rw [mul_one_div] at hh
    apply hh.congr'
    filter_upwards with n
    rw [← Finset.mul_sum, ← mul_div_assoc]
  have hh := hmain.mul hscale
  rw [neg_one_mul] at hh
  have hlim : -(C / (1 - β)) =
      -c / ((1 - β) * β * (offspringMean μ).toReal *
        Real.log (1 / (offspringMean μ).toReal) ^ β) := by
    dsimp [C]
    field_simp [(mean_real_pos hμ).ne', (mean_log_pos hμ).ne',
      (Real.rpow_pos_of_pos (mean_log_pos hμ) _).ne', hp.ne']
  rw [hlim] at hh
  apply hh.congr'
  filter_upwards [hscale.eventually (Ioi_mem_nhds (div_pos
    (div_pos hc (mul_pos (mul_pos hβ0 (mean_real_pos hμ))
      (Real.rpow_pos_of_pos (mean_log_pos hμ) _))) hp))] with n hSn
  have hsum0 : (∑ k ∈ range n, C * ((k : ℝ) + 1) ^ (-β)) ≠ 0 := by
    intro hzero
    exact hSn.ne' (by rw [hzero, zero_div])
  have hpD : (n : ℝ) ^ (1 - β) ≠ 0 := by
    intro hz
    rw [hz, div_zero] at hSn
    exact lt_irrefl _ hSn
  field_simp


private theorem log_nat_mul_survival_ceil_div_tendsto (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (hμ : IsMeasurableSubcriticalCauchyOffspring μ)
    {h g : ℕ → ℝ} {a B D : ℝ} (_ha : 0 < a)
    (haMean : a = Real.log (1 / (offspringMean μ).toReal))
    (hhTop : Tendsto h atTop atTop) (hgTop : Tendsto g atTop atTop)
    (hmain : Tendsto (fun n : ℕ => (Real.log n - a * h n) / g n) atTop (𝓝 B))
    (hU : Tendsto (fun n : ℕ => Real.log (normalizedSurvival μ ⌈h n⌉₊) / g n)
      atTop (𝓝 D)) :
    Tendsto (fun n : ℕ => Real.log ((n : ℝ) * (survival μ ⌈h n⌉₊).toReal) / g n)
      atTop (𝓝 (B + D)) := by
  have he : Tendsto (fun n => -a * (((⌈h n⌉₊ : ℝ) - h n) / g n)) atTop (𝓝 0) := by
    have hh := (ceil_sub_div_tendsto_zero hgTop (hhTop.eventually_ge_atTop 0)).const_mul (-a)
    simpa using hh
  have hh := (hmain.add hU).add he
  rw [add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ), hgTop.eventually_ne_atTop 0] with n hn hg
  rw [log_nat_mul_survival_ceil μ (offspringMean_pos_of_paper μ hμ.to_literal)
    (ne_top_of_lt (hμ.1.trans ENNReal.one_lt_top)) hn (h n)]
  have hlogm : Real.log (offspringMean μ).toReal = -a := by
    rw [haMean, one_div, Real.log_inv]
    ring
  rw [hlogm]
  field_simp
  ring

private theorem nat_mul_survival_ceil_tendsto_zero_of_div_neg (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (hμ : IsMeasurableSubcriticalCauchyOffspring μ)
    {h g : ℕ → ℝ} {L : ℝ} (hgTop : Tendsto g atTop atTop)
    (hdiv : Tendsto (fun n : ℕ => Real.log ((n : ℝ) *
      (survival μ ⌈h n⌉₊).toReal) / g n) atTop (𝓝 L)) (hL : L < 0) :
    Tendsto (fun n : ℕ => (n : ℝ) * (survival μ ⌈h n⌉₊).toReal) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log ((n : ℝ) *
      (survival μ ⌈h n⌉₊).toReal)) atTop atBot := by
    have hh := hgTop.atTop_mul_neg hL hdiv
    apply hh.congr'
    filter_upwards [hgTop.eventually_ne_atTop 0] with n hg
    field_simp
  have hh := Real.tendsto_exp_atBot.comp hlog
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact Real.exp_log (mul_pos (by exact_mod_cast hn)
    (survival_toReal_pos μ (offspringMean_pos_of_paper μ hμ.to_literal) _))

private theorem nat_mul_survival_ceil_tendsto_atTop_of_div_pos (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (hμ : IsMeasurableSubcriticalCauchyOffspring μ)
    {h g : ℕ → ℝ} {L : ℝ} (hgTop : Tendsto g atTop atTop)
    (hdiv : Tendsto (fun n : ℕ => Real.log ((n : ℝ) *
      (survival μ ⌈h n⌉₊).toReal) / g n) atTop (𝓝 L)) (hL : 0 < L) :
    Tendsto (fun n : ℕ => (n : ℝ) * (survival μ ⌈h n⌉₊).toReal) atTop atTop := by
  have hlog : Tendsto (fun n : ℕ => Real.log ((n : ℝ) *
      (survival μ ⌈h n⌉₊).toReal)) atTop atTop := by
    have hh := hgTop.atTop_mul_pos hL hdiv
    apply hh.congr'
    filter_upwards [hgTop.eventually_ne_atTop 0] with n hg
    field_simp
  have hh := Real.tendsto_exp_atTop.comp hlog
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact Real.exp_log (mul_pos (by exact_mod_cast hn)
    (survival_toReal_pos μ (offspringMean_pos_of_paper μ hμ.to_literal) _))

private theorem logarithmic_threshold_data {h g : ℕ → ℝ} {a A : ℝ} (ha : 0 < a)
    (hdef : h = fun n : ℕ => Real.log n / a + A * g n)
    (_hgTop : Tendsto g atTop atTop)
    (hglog : Tendsto (fun n => g n / Real.log n) atTop (𝓝 0)) :
    Tendsto h atTop atTop ∧
      Tendsto (fun n : ℕ => h n / (Real.log n / a)) atTop (𝓝 1) := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hfirst : Tendsto (fun n : ℕ => (Real.log n / a) / Real.log n)
      atTop (𝓝 (1 / a)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hlog.eventually_ne_atTop 0] with n hn
    field_simp
  have hratio : Tendsto (fun n : ℕ => h n / Real.log n) atTop (𝓝 (1 / a)) := by
    have hh := hfirst.add (hglog.const_mul A)
    simp only [mul_zero, add_zero] at hh
    apply hh.congr'
    filter_upwards [hlog.eventually_ne_atTop 0] with n hn
    simp only [hdef]
    field_simp
  have hhTop : Tendsto h atTop atTop := by
    have hh := hratio.pos_mul_atTop (div_pos zero_lt_one ha) hlog
    apply hh.congr'
    filter_upwards [hlog.eventually_ne_atTop 0] with n hn
    field_simp
  refine ⟨hhTop, ?_⟩
  have hh := hratio.const_mul a
  have hlim : a * (1 / a) = 1 := by field_simp
  rw [hlim] at hh
  apply hh.congr'
  filter_upwards [hlog.eventually_ne_atTop 0] with n hn
  field_simp [ha.ne']


local instance secondOrderPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

private theorem measurableSet_finiteTreeEvent_secondOrder (P : PlaneTree → Prop) :
    MeasurableSet (finiteTreeEvent P) := by
  classical
  exact ((Set.to_countable {t : PlaneTree | P t}).image
    PlaneTree.toLocallyFinite).measurableSet

private theorem toLocallyFinite_mem_finiteTreeEvent_secondOrder
    (P : PlaneTree → Prop) (t : PlaneTree) :
    t.toLocallyFinite ∈ finiteTreeEvent P ↔ P t := by
  constructor
  · rintro ⟨s, hs, hst⟩
    have hst' : s = t := PlaneTree.toLocallyFinite_injective hst
    simpa only [hst', Set.mem_ofPred_eq] using hs
  · intro ht
    exact ⟨t, ht, rfl⟩

private theorem conditioned_ne_top_secondOrder (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (n : ℕ) (A : Set Tree) : conditioned μ n A ≠ ∞ := by
  unfold conditioned
  finiteness

private theorem conditioned_apply_eq_tsum_plane_secondOrder (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (n : ℕ) (A : Set Tree) (hA : MeasurableSet A) :
    conditioned μ n A = ∑' t : PlaneTree, conditioned μ n {t.toLocallyFinite} *
      (if t.toLocallyFinite ∈ A then 1 else 0) := by
  classical
  let f (t : PlaneTree) : ℝ≥0∞ := conditioned μ n {t.toLocallyFinite} *
    (if t.toLocallyFinite ∈ A then 1 else 0)
  change conditioned μ n A = ∑' t : PlaneTree, f t
  change (bienaymeLaw μ (sizeEvent n))⁻¹ * (bienaymeLaw μ).restrict (sizeEvent n) A = _
  rw [restrict_sizeEvent_apply μ n A hA, ← ENNReal.tsum_mul_left]
  have hatom (t : PlaneTree) : conditioned μ n {t.toLocallyFinite} =
      (bienaymeLaw μ (sizeEvent n))⁻¹ *
        (if t.size = n then PlaneTree.weight (fun k => μ {k}) t else 0) := by
    change (bienaymeLaw μ (sizeEvent n))⁻¹ *
      (bienaymeLaw μ).restrict (sizeEvent n) {t.toLocallyFinite} = _
    rw [restrict_sizeEvent_apply μ n _ (MeasurableSet.singleton _)]
    have heq (s : PlaneTree) : s.toLocallyFinite = t.toLocallyFinite ↔ s = t := by
      constructor
      · exact fun h => PlaneTree.toLocallyFinite_injective h
      · exact congrArg PlaneTree.toLocallyFinite
    simp [heq]
  simp only [f, hatom, mul_assoc]

private theorem conditioned_finiteTreeEvent_not_eq_compl_secondOrder (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (n : ℕ) (P : PlaneTree → Prop) :
    conditioned μ n (finiteTreeEvent fun t => ¬P t) =
      conditioned μ n (finiteTreeEvent P)ᶜ := by
  classical
  rw [conditioned_apply_eq_tsum_plane_secondOrder μ n _
      (measurableSet_finiteTreeEvent_secondOrder _),
    conditioned_apply_eq_tsum_plane_secondOrder μ n _
      (measurableSet_finiteTreeEvent_secondOrder _).compl]
  apply tsum_congr
  intro t
  by_cases ht : P t <;> simp [toLocallyFinite_mem_finiteTreeEvent_secondOrder, ht]

private theorem conditioned_not_tendsto_zero_real_secondOrder (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (hμ : IsMeasurableSubcriticalCauchyOffspring μ)
    (P : ℕ → PlaneTree → Prop)
    (hP : Tendsto (fun n : ℕ => conditioned μ n (finiteTreeEvent (P n)))
      atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => (conditioned μ n
      (finiteTreeEvent fun t => ¬P n t)).toReal) atTop (𝓝 0) := by
  have hr : Tendsto (fun n : ℕ => (conditioned μ n
      (finiteTreeEvent (P n))).toReal) atTop (𝓝 1) := by
    simpa using (ENNReal.tendsto_toReal_iff
      (fun n => conditioned_ne_top_secondOrder μ n _) ENNReal.one_ne_top).mpr hP
  have hz := (tendsto_const_nhds (x := (1 : ℝ))).sub hr
  simp only [sub_self] at hz
  apply hz.congr'
  filter_upwards [eventually_size_admissible μ hμ.to_literal] with n hn
  let _ : IsProbabilityMeasure (conditioned μ n) := conditioned_isProbability μ n hn
  rw [conditioned_finiteTreeEvent_not_eq_compl_secondOrder,
    measure_compl (measurableSet_finiteTreeEvent_secondOrder _)
      (conditioned_ne_top_secondOrder μ n _), measure_univ,
    ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]


/-- Proposition 4.5(i), with the survival-correction hypothesis replacing the
integer-tail hypothesis. -/
theorem height_second_order_log_of_survivalCorrection (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (hμ : IsMeasurableSubcriticalCauchyOffspring μ)
    {c : ℝ} (hc : 0 < c)
    (hℓ : Tendsto (fun x => survivalCorrection μ x /
      (c / (1 * Real.log x⁻¹ ^ (1 : ℝ)))) (𝓝[>] 0) (𝓝 1))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => conditioned μ n (finiteTreeEvent fun t =>
      ε * Real.log (Real.log n) ≤
        |(height t : ℝ) - Real.log n / Real.log (1 / (offspringMean μ).toReal) +
          c / ((offspringMean μ).toReal * Real.log (1 / (offspringMean μ).toReal) ^ 2) *
            Real.log (Real.log n)|)) atTop (𝓝 0) := by
  let a := Real.log (1 / (offspringMean μ).toReal)
  let K := c / ((offspringMean μ).toReal * a ^ 2)
  let g : ℕ → ℝ := fun n => Real.log (Real.log n)
  let hu : ℕ → ℝ := fun n => Real.log n / a - K * g n + (ε / 2) * g n
  let hl : ℕ → ℝ := fun n => Real.log n / a - K * g n - (ε / 2) * g n
  let upper : ℕ → ℝ := fun n => max (hu n) 1
  let lower : ℕ → ℝ := fun n => max (hl n) 1
  have ha : 0 < a := mean_log_pos hμ
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hgTop : Tendsto g atTop atTop := Real.tendsto_log_atTop.comp hlog
  have hglog : Tendsto (fun n : ℕ => g n / Real.log n) atTop (𝓝 0) := by
    exact (Real.isLittleO_log_id_atTop.comp_tendsto hlog).tendsto_div_nhds_zero
  have hUbase := log_normalizedSurvival_div_log_of_beta_eq_one μ hμ hc hℓ
  have hKcancel : a * K = c / ((offspringMean μ).toReal * a) := by
    dsimp [K]
    field_simp [ha.ne']
  have huData : Tendsto hu atTop atTop ∧
      Tendsto (fun n : ℕ => hu n / (Real.log n / a)) atTop (𝓝 1) := by
    apply logarithmic_threshold_data ha (A := ε / 2 - K) _ hgTop hglog
    funext n
    simp only [hu]
    ring
  have hlData : Tendsto hl atTop atTop ∧
      Tendsto (fun n : ℕ => hl n / (Real.log n / a)) atTop (𝓝 1) := by
    apply logarithmic_threshold_data ha (A := -K - ε / 2) _ hgTop hglog
    funext n
    simp only [hl]
    ring
  have huU : Tendsto (fun n : ℕ => Real.log (normalizedSurvival μ ⌈hu n⌉₊) / g n)
      atTop (𝓝 (-a * K)) := by
    have hh := log_normalizedSurvival_ceil_div_loglog hu ha huData.1 huData.2 hUbase
    change Tendsto (fun n : ℕ => Real.log (normalizedSurvival μ ⌈hu n⌉₊) / g n)
      atTop (𝓝 (-c / ((offspringMean μ).toReal * a))) at hh
    have hKneg : -a * K = -c / ((offspringMean μ).toReal * a) := by
      calc
        -a * K = -(a * K) := by ring
        _ = -(c / ((offspringMean μ).toReal * a)) := congrArg (fun x : ℝ => -x) hKcancel
        _ = -c / ((offspringMean μ).toReal * a) := by ring
    rw [hKneg]
    exact hh
  have hlU : Tendsto (fun n : ℕ => Real.log (normalizedSurvival μ ⌈hl n⌉₊) / g n)
      atTop (𝓝 (-a * K)) := by
    have hh := log_normalizedSurvival_ceil_div_loglog hl ha hlData.1 hlData.2 hUbase
    change Tendsto (fun n : ℕ => Real.log (normalizedSurvival μ ⌈hl n⌉₊) / g n)
      atTop (𝓝 (-c / ((offspringMean μ).toReal * a))) at hh
    have hKneg : -a * K = -c / ((offspringMean μ).toReal * a) := by
      calc
        -a * K = -(a * K) := by ring
        _ = -(c / ((offspringMean μ).toReal * a)) := congrArg (fun x : ℝ => -x) hKcancel
        _ = -c / ((offspringMean μ).toReal * a) := by ring
    rw [hKneg]
    exact hh
  have huMain : Tendsto (fun n : ℕ => (Real.log n - a * hu n) / g n)
      atTop (𝓝 (a * K - a * (ε / 2))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hgTop.eventually_ne_atTop 0] with n hn
    simp only [hu]
    field_simp [ha.ne']
    ring
  have hlMain : Tendsto (fun n : ℕ => (Real.log n - a * hl n) / g n)
      atTop (𝓝 (a * K + a * (ε / 2))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hgTop.eventually_ne_atTop 0] with n hn
    simp only [hl]
    field_simp [ha.ne']
    ring
  have huDiv := log_nat_mul_survival_ceil_div_tendsto μ hμ ha rfl huData.1 hgTop huMain huU
  have hlDiv := log_nat_mul_survival_ceil_div_tendsto μ hμ ha rfl hlData.1 hgTop hlMain hlU
  rw [show a * K - a * (ε / 2) + -a * K = -a * (ε / 2) by ring] at huDiv
  rw [show a * K + a * (ε / 2) + -a * K = a * (ε / 2) by ring] at hlDiv
  have huQraw := nat_mul_survival_ceil_tendsto_zero_of_div_neg μ hμ hgTop huDiv
    (mul_neg_of_neg_of_pos (neg_neg_of_pos ha) (half_pos hε))
  have hlQraw := nat_mul_survival_ceil_tendsto_atTop_of_div_pos μ hμ hgTop hlDiv
    (mul_pos ha (half_pos hε))
  have huTop : Tendsto upper atTop atTop := by
    apply huData.1.congr'
    filter_upwards [huData.1.eventually_ge_atTop 1] with n hn
    exact (max_eq_left hn).symm
  have hlTop : Tendsto lower atTop atTop := by
    apply hlData.1.congr'
    filter_upwards [hlData.1.eventually_ge_atTop 1] with n hn
    exact (max_eq_left hn).symm
  have huQ : Tendsto (fun n : ℕ => (n : ℝ) * (survival μ ⌈upper n⌉₊).toReal)
      atTop (𝓝 0) := by
    apply huQraw.congr'
    filter_upwards [huData.1.eventually_ge_atTop 1] with n hn
    simp only [upper, max_eq_left hn]
  have hlQ : Tendsto (fun n : ℕ => (n : ℝ) * (survival μ ⌈lower n⌉₊).toReal)
      atTop atTop := by
    apply hlQraw.congr'
    filter_upwards [hlData.1.eventually_ge_atTop 1] with n hn
    simp only [lower, max_eq_left hn]
  have huGood := paper_height_upper μ hμ upper
    (fun n => lt_of_lt_of_le zero_lt_one (le_max_right _ _)) huTop huQ
  have hlGood := paper_height_lower μ hμ lower
    (fun n => lt_of_lt_of_le zero_lt_one (le_max_right _ _)) hlTop hlQ
  have huBad : Tendsto (fun n : ℕ => (conditioned μ n
      (finiteTreeEvent fun t => upper n ≤ (height t : ℝ))).toReal) atTop (𝓝 0) := by
    simpa only [not_lt] using conditioned_not_tendsto_zero_real_secondOrder μ hμ
      (fun n t => (height t : ℝ) < upper n) huGood
  have hlBad : Tendsto (fun n : ℕ => (conditioned μ n
      (finiteTreeEvent fun t => (height t : ℝ) < lower n)).toReal) atTop (𝓝 0) := by
    simpa only [not_le] using conditioned_not_tendsto_zero_real_secondOrder μ hμ
      (fun n t => lower n ≤ (height t : ℝ)) hlGood
  apply (ENNReal.tendsto_toReal_zero_iff
    (fun n => conditioned_ne_top_secondOrder μ n _)).mp
  apply squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) ?_
    (by simpa using huBad.add hlBad)
  filter_upwards [huData.1.eventually_ge_atTop 1, hlData.1.eventually_ge_atTop 1,
    hgTop.eventually_gt_atTop 0] with n huN hlN hgN
  dsimp [g] at hgN
  calc
    (conditioned μ n (finiteTreeEvent fun t => ε * g n ≤
      |(height t : ℝ) - Real.log n / a + K * g n|)).toReal ≤
      (conditioned μ n ((finiteTreeEvent fun t => upper n ≤ (height t : ℝ)) ∪
        (finiteTreeEvent fun t => (height t : ℝ) < lower n))).toReal := by
      apply ENNReal.toReal_mono (conditioned_ne_top_secondOrder μ n _)
      apply measure_mono
      rintro _ ⟨t, ht, rfl⟩
      change ε * g n ≤ |(height t : ℝ) - Real.log n / a + K * g n| at ht
      rcases le_abs.mp ht with hup | hlow
      · apply Or.inl
        refine ⟨t, ?_, rfl⟩
        change upper n ≤ (height t : ℝ)
        simp only [upper, max_eq_left huN, hu]
        dsimp [a, K, g] at hup ⊢
        nlinarith [hup]
      · apply Or.inr
        refine ⟨t, ?_, rfl⟩
        change (height t : ℝ) < lower n
        simp only [lower, max_eq_left hlN, hl]
        dsimp [a, K, g] at hlow ⊢
        nlinarith [hlow, mul_pos hε hgN]
    _ ≤ ((conditioned μ n (finiteTreeEvent fun t => upper n ≤ (height t : ℝ))) +
      (conditioned μ n (finiteTreeEvent fun t => (height t : ℝ) < lower n))).toReal :=
      ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
        ⟨conditioned_ne_top_secondOrder μ n _, conditioned_ne_top_secondOrder μ n _⟩)
        (measure_union_le _ _)
    _ = _ := ENNReal.toReal_add (conditioned_ne_top_secondOrder μ n _)
      (conditioned_ne_top_secondOrder μ n _)


/-- Proposition 4.5(ii), corrected (R10), with the survival-correction
hypothesis replacing the integer-tail hypothesis. -/
theorem height_second_order_pow_of_survivalCorrection (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (hμ : IsMeasurableSubcriticalCauchyOffspring μ)
    {c β : ℝ} (hc : 0 < c) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hℓ : Tendsto (fun x => survivalCorrection μ x /
      (c / (β * Real.log x⁻¹ ^ β))) (𝓝[>] 0) (𝓝 1))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => conditioned μ n (finiteTreeEvent fun t =>
      ε * Real.log n ^ (1 - β) ≤
        |(height t : ℝ) - Real.log n / Real.log (1 / (offspringMean μ).toReal) +
          c / ((1 - β) * β * (offspringMean μ).toReal *
            Real.log (1 / (offspringMean μ).toReal) ^ 2) * Real.log n ^ (1 - β)|))
      atTop (𝓝 0) := by
  let a := Real.log (1 / (offspringMean μ).toReal)
  let p : ℝ := 1 - β
  let K := c / (p * β * (offspringMean μ).toReal * a ^ 2)
  let g : ℕ → ℝ := fun n => Real.log n ^ p
  let hu : ℕ → ℝ := fun n => Real.log n / a - K * g n + (ε / 2) * g n
  let hl : ℕ → ℝ := fun n => Real.log n / a - K * g n - (ε / 2) * g n
  let upper : ℕ → ℝ := fun n => max (hu n) 1
  let lower : ℕ → ℝ := fun n => max (hl n) 1
  have ha : 0 < a := mean_log_pos hμ
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hp : 0 < p := sub_pos.mpr hβ1
  have hgTop : Tendsto g atTop atTop := (tendsto_rpow_atTop hp).comp hlog
  have hglog : Tendsto (fun n : ℕ => g n / Real.log n) atTop (𝓝 0) := by
    have hneg : Tendsto (fun n : ℕ => Real.log n ^ (-β)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hβ0).comp hlog
    apply hneg.congr'
    filter_upwards [hlog.eventually_gt_atTop 0] with n hn
    simp only [g]
    rw [show -β = p - 1 by dsimp [p]; ring, Real.rpow_sub hn, Real.rpow_one]
  have hUbase := log_normalizedSurvival_div_rpow_of_beta_lt_one μ hμ hc hβ0 hβ1 hℓ
  have hKcancel : a * K = c / (p * β * (offspringMean μ).toReal * a) := by
    dsimp [K]
    field_simp [ha.ne']
  have huData : Tendsto hu atTop atTop ∧
      Tendsto (fun n : ℕ => hu n / (Real.log n / a)) atTop (𝓝 1) := by
    apply logarithmic_threshold_data ha (A := ε / 2 - K) _ hgTop hglog
    funext n
    simp only [hu]
    ring
  have hlData : Tendsto hl atTop atTop ∧
      Tendsto (fun n : ℕ => hl n / (Real.log n / a)) atTop (𝓝 1) := by
    apply logarithmic_threshold_data ha (A := -K - ε / 2) _ hgTop hglog
    funext n
    simp only [hl]
    ring
  have huU : Tendsto (fun n : ℕ => Real.log (normalizedSurvival μ ⌈hu n⌉₊) / g n)
      atTop (𝓝 (-a * K)) := by
    have hh := log_normalizedSurvival_ceil_div_log_rpow hu ha hp.le huData.1 huData.2 hUbase
    change Tendsto (fun n : ℕ => Real.log (normalizedSurvival μ ⌈hu n⌉₊) / g n)
      atTop (𝓝 (-c / (p * β * (offspringMean μ).toReal * a ^ β) * (1 / a) ^ p)) at hh
    have hsum : β + p = 1 := by dsimp [p]; ring
    have hpow : a ^ β * a ^ p = a := by
      rw [← Real.rpow_add ha, hsum, Real.rpow_one]
    have hscale : -c / (p * β * (offspringMean μ).toReal * a ^ β) * (1 / a) ^ p =
        -a * K := by
      rw [show (1 / a) ^ p = (a ^ p)⁻¹ by rw [one_div, Real.inv_rpow ha.le]]
      dsimp [K]
      field_simp [ha.ne', hβ0.ne', hp.ne', (mean_real_pos hμ).ne',
        (Real.rpow_pos_of_pos ha β).ne', (Real.rpow_pos_of_pos ha p).ne']
      nlinarith [hpow]
    rw [← hscale]
    exact hh
  have hlU : Tendsto (fun n : ℕ => Real.log (normalizedSurvival μ ⌈hl n⌉₊) / g n)
      atTop (𝓝 (-a * K)) := by
    have hh := log_normalizedSurvival_ceil_div_log_rpow hl ha hp.le hlData.1 hlData.2 hUbase
    change Tendsto (fun n : ℕ => Real.log (normalizedSurvival μ ⌈hl n⌉₊) / g n)
      atTop (𝓝 (-c / (p * β * (offspringMean μ).toReal * a ^ β) * (1 / a) ^ p)) at hh
    have hsum : β + p = 1 := by dsimp [p]; ring
    have hpow : a ^ β * a ^ p = a := by
      rw [← Real.rpow_add ha, hsum, Real.rpow_one]
    have hscale : -c / (p * β * (offspringMean μ).toReal * a ^ β) * (1 / a) ^ p =
        -a * K := by
      rw [show (1 / a) ^ p = (a ^ p)⁻¹ by rw [one_div, Real.inv_rpow ha.le]]
      dsimp [K]
      field_simp [ha.ne', hβ0.ne', hp.ne', (mean_real_pos hμ).ne',
        (Real.rpow_pos_of_pos ha β).ne', (Real.rpow_pos_of_pos ha p).ne']
      nlinarith [hpow]
    rw [← hscale]
    exact hh
  have huMain : Tendsto (fun n : ℕ => (Real.log n - a * hu n) / g n)
      atTop (𝓝 (a * K - a * (ε / 2))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hgTop.eventually_ne_atTop 0] with n hn
    simp only [hu]
    field_simp [ha.ne']
    ring
  have hlMain : Tendsto (fun n : ℕ => (Real.log n - a * hl n) / g n)
      atTop (𝓝 (a * K + a * (ε / 2))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hgTop.eventually_ne_atTop 0] with n hn
    simp only [hl]
    field_simp [ha.ne']
    ring
  have huDiv := log_nat_mul_survival_ceil_div_tendsto μ hμ ha rfl huData.1 hgTop huMain huU
  have hlDiv := log_nat_mul_survival_ceil_div_tendsto μ hμ ha rfl hlData.1 hgTop hlMain hlU
  rw [show a * K - a * (ε / 2) + -a * K = -a * (ε / 2) by ring] at huDiv
  rw [show a * K + a * (ε / 2) + -a * K = a * (ε / 2) by ring] at hlDiv
  have huQraw := nat_mul_survival_ceil_tendsto_zero_of_div_neg μ hμ hgTop huDiv
    (mul_neg_of_neg_of_pos (neg_neg_of_pos ha) (half_pos hε))
  have hlQraw := nat_mul_survival_ceil_tendsto_atTop_of_div_pos μ hμ hgTop hlDiv
    (mul_pos ha (half_pos hε))
  have huTop : Tendsto upper atTop atTop := by
    apply huData.1.congr'
    filter_upwards [huData.1.eventually_ge_atTop 1] with n hn
    exact (max_eq_left hn).symm
  have hlTop : Tendsto lower atTop atTop := by
    apply hlData.1.congr'
    filter_upwards [hlData.1.eventually_ge_atTop 1] with n hn
    exact (max_eq_left hn).symm
  have huQ : Tendsto (fun n : ℕ => (n : ℝ) * (survival μ ⌈upper n⌉₊).toReal)
      atTop (𝓝 0) := by
    apply huQraw.congr'
    filter_upwards [huData.1.eventually_ge_atTop 1] with n hn
    simp only [upper, max_eq_left hn]
  have hlQ : Tendsto (fun n : ℕ => (n : ℝ) * (survival μ ⌈lower n⌉₊).toReal)
      atTop atTop := by
    apply hlQraw.congr'
    filter_upwards [hlData.1.eventually_ge_atTop 1] with n hn
    simp only [lower, max_eq_left hn]
  have huGood := paper_height_upper μ hμ upper
    (fun n => lt_of_lt_of_le zero_lt_one (le_max_right _ _)) huTop huQ
  have hlGood := paper_height_lower μ hμ lower
    (fun n => lt_of_lt_of_le zero_lt_one (le_max_right _ _)) hlTop hlQ
  have huBad : Tendsto (fun n : ℕ => (conditioned μ n
      (finiteTreeEvent fun t => upper n ≤ (height t : ℝ))).toReal) atTop (𝓝 0) := by
    simpa only [not_lt] using conditioned_not_tendsto_zero_real_secondOrder μ hμ
      (fun n t => (height t : ℝ) < upper n) huGood
  have hlBad : Tendsto (fun n : ℕ => (conditioned μ n
      (finiteTreeEvent fun t => (height t : ℝ) < lower n)).toReal) atTop (𝓝 0) := by
    simpa only [not_le] using conditioned_not_tendsto_zero_real_secondOrder μ hμ
      (fun n t => lower n ≤ (height t : ℝ)) hlGood
  apply (ENNReal.tendsto_toReal_zero_iff
    (fun n => conditioned_ne_top_secondOrder μ n _)).mp
  apply squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) ?_
    (by simpa using huBad.add hlBad)
  filter_upwards [huData.1.eventually_ge_atTop 1, hlData.1.eventually_ge_atTop 1,
    hgTop.eventually_gt_atTop 0] with n huN hlN hgN
  dsimp [g] at hgN
  calc
    (conditioned μ n (finiteTreeEvent fun t => ε * g n ≤
      |(height t : ℝ) - Real.log n / a + K * g n|)).toReal ≤
      (conditioned μ n ((finiteTreeEvent fun t => upper n ≤ (height t : ℝ)) ∪
        (finiteTreeEvent fun t => (height t : ℝ) < lower n))).toReal := by
      apply ENNReal.toReal_mono (conditioned_ne_top_secondOrder μ n _)
      apply measure_mono
      rintro _ ⟨t, ht, rfl⟩
      change ε * g n ≤ |(height t : ℝ) - Real.log n / a + K * g n| at ht
      rcases le_abs.mp ht with hup | hlow
      · apply Or.inl
        refine ⟨t, ?_, rfl⟩
        change upper n ≤ (height t : ℝ)
        simp only [upper, max_eq_left huN, hu]
        dsimp [a, K, g] at hup ⊢
        nlinarith [hup]
      · apply Or.inr
        refine ⟨t, ?_, rfl⟩
        change (height t : ℝ) < lower n
        simp only [lower, max_eq_left hlN, hl]
        dsimp [a, K, g] at hlow ⊢
        nlinarith [hlow, mul_pos hε hgN]
    _ ≤ ((conditioned μ n (finiteTreeEvent fun t => upper n ≤ (height t : ℝ))) +
      (conditioned μ n (finiteTreeEvent fun t => (height t : ℝ) < lower n))).toReal :=
      ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
        ⟨conditioned_ne_top_secondOrder μ n _, conditioned_ne_top_secondOrder μ n _⟩)
        (measure_union_le _ _)
    _ = _ := ENNReal.toReal_add (conditioned_ne_top_secondOrder μ n _)
      (conditioned_ne_top_secondOrder μ n _)

end
end SubcriticalCauchy.Bienayme
