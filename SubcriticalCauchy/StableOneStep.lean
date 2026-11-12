module

public import SubcriticalCauchy.StableOneStepAux
public import SubcriticalCauchy.StableOneStepTail
public import SubcriticalCauchy.Centering

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The project one-step index-one Laplace exponent
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section

/-- The untruncated one-step Laplace transform of an offspring increment. -/
def oneStepLaplace (μ : Measure ℕ) (s : ℝ) : ℝ :=
  ∫ k, Real.exp (-s * offspringIncrement k) ∂μ

/-- Measurability of the rescaled (nonstrict) tail. -/
lemma oneStep_rescaledTail_measurable (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (n : ℕ) (r : ℝ) :
    Measurable (fun u : ℝ => (n : ℝ) * (incrementTail μ (u * r)).toReal) := by
  have ht : Antitone (fun x : ℝ => (incrementTail μ x).toReal) := by
    intro x y hxy
    exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono fun k hk => hxy.trans hk)
  exact measurable_const.mul (ht.measurable.comp (by fun_prop))

lemma oneStep_slopePos_measurable (s : ℝ) : Measurable (stableKernelSlopePos s) := by
  exact Measurable.indicator (by fun_prop) measurableSet_Ioo

lemma oneStep_slopeNeg_measurable (s : ℝ) : Measurable (stableKernelSlopeNeg s) := by
  exact Measurable.indicator (by fun_prop) measurableSet_Ici

/-- Above the truncation point, tail monotonicity gives a constant majorant. -/
lemma oneStep_negative_slope_tail_tendsto
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n : ℕ => ∫ u in Ioi 0, stableKernelSlopeNeg s u *
      ((n : ℝ) * (incrementTail μ (u * a n)).toReal)) atTop
      (𝓝 (∫ u in Ioi 0, stableKernelSlopeNeg s u * (1 / u))) := by
  have hat := scaling_tendsto_atTop μ hμ.to_literal ha
  apply tendsto_integral_filter_of_dominated_convergence
    (fun u => 2 * stableKernelSlopeNeg s u)
  · exact Eventually.of_forall fun n =>
      ((oneStep_slopeNeg_measurable s).mul
        (oneStep_rescaledTail_measurable μ n (a n))).aestronglyMeasurable
  · filter_upwards [hat.eventually_ge_atTop 0,
      ha.eventually (Iio_mem_nhds (show (1 : ℝ) < 2 by norm_num))] with n han hn
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (stableKernelSlopeNeg_nonneg hs)
      (mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg))]
    by_cases hu1 : 1 ≤ u
    · have hm : (incrementTail μ (u * a n)).toReal ≤ (incrementTail μ (a n)).toReal :=
        ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono fun k hk =>
          (show a n ≤ u * a n by nlinarith).trans hk)
      have ht := (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg n)).trans hn.le
      nlinarith [mul_le_mul_of_nonneg_left ht (stableKernelSlopeNeg_nonneg (u := u) hs)]
    · simp [stableKernelSlopeNeg, Set.indicator, hu1]
  · exact ((integrable_stableKernelSlopeNeg hs).const_mul 2).integrableOn
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (rescaled_incrementTail_tendsto μ hμ a ha hu).const_mul _

/-- The part below the fixed Potter threshold has vanishing integral. -/
lemma oneStep_positive_slope_small_integral_bound
    (μ : Measure ℕ) [IsProbabilityMeasure μ] {s R r : ℝ}
    (hs : 0 < s) (hR : 0 < R) (hr : 0 < r) (n : ℕ) :
    |∫ u in Ioi 0, if R ≤ u * r then 0 else stableKernelSlopePos s u *
      ((n : ℝ) * (incrementTail μ (u * r)).toReal)| ≤
        s ^ 2 * R ^ 2 * ((n : ℝ) / r ^ 2) := by
  let B := s ^ 2 * (R / r) * (n : ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb : Integrable ((Ioc (0 : ℝ) (R / r)).indicator (fun _ => B)) :=
    ((continuousOn_const : ContinuousOn (fun _ : ℝ => B) (Icc 0 (R / r))).integrableOn_Icc.mono_set Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc
  have hnorm : ∀ᵐ u ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖if R ≤ u * r then 0 else stableKernelSlopePos s u *
        ((n : ℝ) * (incrementTail μ (u * r)).toReal)‖ ≤
      (Ioc (0 : ℝ) (R / r)).indicator (fun _ => B) u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    by_cases h : R ≤ u * r
    · simp only [h, ↓reduceIte, norm_zero]
      exact indicator_nonneg (fun _ _ => hB) _
    · have huR : u ≤ R / r := (le_div_iff₀ hr).mpr (le_of_lt (lt_of_not_ge h))
      rw [ite_eq_right h, show (Ioc (0 : ℝ) (R / r)).indicator (fun _ => B) u = B from
        indicator_of_mem (show u ∈ Ioc (0 : ℝ) (R / r) from ⟨hu, huR⟩) _, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (stableKernelSlopePos_nonneg hs)
          (mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg))]
      have ht : (incrementTail μ (u * r)).toReal ≤ 1 := measureReal_le_one
      have hg := (stableKernelSlopePos_le_sq hs hu).trans
        (mul_le_mul_of_nonneg_left huR (sq_nonneg s))
      dsimp [B]
      calc
        _ ≤ (s ^ 2 * (R / r)) * ((n : ℝ) * 1) := by gcongr
        _ = _ := by ring
  have hh := norm_integral_le_of_norm_le hb.integrableOn hnorm
  rw [Real.norm_eq_abs] at hh
  calc
    _ ≤ ∫ u in Ioi 0, (Ioc (0 : ℝ) (R / r)).indicator (fun _ => B) u := hh
    _ = (R / r) * B := by
      rw [setIntegral_indicator measurableSet_Ioc]
      have heq : Ioi (0 : ℝ) ∩ Ioc 0 (R / r) = Ioc 0 (R / r) := by ext x; simp only [mem_inter_iff, mem_Ioi, mem_Ioc]; tauto
      rw [heq]
      simp [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (div_pos hR hr).le]
    _ = s ^ 2 * R ^ 2 * ((n : ℝ) / r ^ 2) := by dsimp [B]; ring

/-- Positive-slope convergence, separating the shrinking interval below Potter's threshold. -/
lemma oneStep_positive_slope_tail_tendsto
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n : ℕ => ∫ u in Ioi 0, stableKernelSlopePos s u *
      ((n : ℝ) * (incrementTail μ (u * a n)).toReal)) atTop
      (𝓝 (∫ u in Ioi 0, stableKernelSlopePos s u * (1 / u))) := by
  obtain ⟨C, R, hC, hR, hpot⟩ :=
    rescaled_incrementTail_shrinking_potter_bound μ hμ a ha
  have hat := scaling_tendsto_atTop μ hμ.to_literal ha
  let F : ℕ → ℝ → ℝ := fun n u => stableKernelSlopePos s u *
    ((n : ℝ) * (incrementTail μ (u * a n)).toReal)
  let H : ℕ → ℝ → ℝ := fun n u => if R ≤ u * a n then F n u else 0
  let E : ℕ → ℝ → ℝ := fun n u => if R ≤ u * a n then 0 else F n u
  have hFmeas : ∀ n, Measurable (F n) := fun n =>
    (oneStep_slopePos_measurable s).mul (oneStep_rescaledTail_measurable μ n (a n))
  have hHmeas : ∀ n, Measurable (H n) := fun n =>
    (hFmeas n).ite (measurableSet_le measurable_const (by fun_prop)) measurable_const
  have hEmeas : ∀ n, Measurable (E n) := fun n =>
    measurable_const.ite (measurableSet_le measurable_const (by fun_prop)) (hFmeas n)
  let B : ℝ → ℝ := (Ioo (0 : ℝ) 1).indicator
    (fun u => C * s ^ 2 * u ^ (-(1 / 2 : ℝ)))
  have hBint : Integrable B := by
    apply IntegrableOn.integrable_indicator _ measurableSet_Ioo
    exact ((intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr
      (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ))).const_mul _
  have hHlim : Tendsto (fun n => ∫ u in Ioi 0, H n u) atTop
      (𝓝 (∫ u in Ioi 0, stableKernelSlopePos s u * (1 / u))) := by
    apply tendsto_integral_filter_of_dominated_convergence B
    · exact Eventually.of_forall fun n => (hHmeas n).aestronglyMeasurable
    · filter_upwards [hpot] with n hn
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hB0 : 0 ≤ B u := indicator_nonneg (fun x _ => mul_nonneg (mul_nonneg hC.le (sq_nonneg s)) (Real.rpow_nonneg (le_of_lt (show 0 < x from ‹x ∈ Ioo (0 : ℝ) 1›.1)) _)) _
      by_cases hcut : R ≤ u * a n
      · dsimp [H]
        rw [ite_eq_left hcut]
        by_cases hu1 : u < 1
        · rw [show B u = C * s ^ 2 * u ^ (-(1 / 2 : ℝ)) from
            indicator_of_mem (show u ∈ Ioo (0 : ℝ) 1 from ⟨hu, hu1⟩) _]
          dsimp [F]
          rw [abs_of_nonneg (mul_nonneg (stableKernelSlopePos_nonneg hs)
            (mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg))]
          calc
            _ ≤ (s ^ 2 * u) * (C * u ^ (-(3 / 2 : ℝ))) := by
              exact mul_le_mul (stableKernelSlopePos_le_sq hs hu)
                (hn u hu hu1.le hcut)
                (mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg)
                (mul_nonneg (sq_nonneg _) hu.le)
            _ = C * s ^ 2 * u ^ (-(1 / 2 : ℝ)) := by
              rw [show (-(3 / 2 : ℝ)) = (-(1 / 2 : ℝ)) - 1 by ring,
                Real.rpow_sub_one hu.ne']
              field_simp [ne_of_gt hu]
        · simp only [F, stableKernelSlopePos, Set.indicator, mem_Ioo,
            not_and_or.mpr (Or.inr hu1), ↓reduceIte, zero_mul, abs_zero]
          simpa only [abs_zero] using hB0
      · simpa only [H, hcut, ↓reduceIte, norm_zero] using hB0
    · exact hBint.integrableOn
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      apply ((rescaled_incrementTail_tendsto μ hμ a ha hu).const_mul
        (stableKernelSlopePos s u)).congr'
      filter_upwards [(hat.const_mul_atTop hu).eventually_ge_atTop R] with n hn
      simp only [H, F, hn, ↓reduceIte]
  have hElim : Tendsto (fun n => ∫ u in Ioi 0, E n u) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun n : ℕ => s ^ 2 * R ^ 2 * ((n : ℝ) / (a n) ^ 2))
    · filter_upwards [hat.eventually_gt_atTop 0] with n hn
      simpa only [Real.norm_eq_abs] using oneStep_positive_slope_small_integral_bound μ hs hR hn n
    · simpa using (oneStep_nat_div_scale_sq_tendsto_zero μ hμ a ha).const_mul (s ^ 2 * R ^ 2)
  have hFi : ∀ n, IntegrableOn (F n) (Ioi 0) := by
    intro n
    apply ((integrable_stableKernelSlopePos s).const_mul (n : ℝ)).integrableOn.mono'
      (hFmeas n).aestronglyMeasurable
    filter_upwards [] with u
    dsimp [F]
    rw [abs_of_nonneg (mul_nonneg (stableKernelSlopePos_nonneg hs)
      (mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg))]
    have ht : (incrementTail μ (u * a n)).toReal ≤ 1 := measureReal_le_one
    nlinarith [mul_le_mul_of_nonneg_left ht
      (mul_nonneg (Nat.cast_nonneg n) (stableKernelSlopePos_nonneg (u := u) hs))]
  apply (show Tendsto (fun n => (∫ u in Ioi 0, H n u) + ∫ u in Ioi 0, E n u)
    atTop (𝓝 (∫ u in Ioi 0, stableKernelSlopePos s u * (1 / u))) by
      simpa using hHlim.add hElim).congr'
  filter_upwards [] with n
  have hHi : IntegrableOn (H n) (Ioi 0) :=
    (Integrable.mono (hFi n)) (hHmeas n).aestronglyMeasurable (Eventually.of_forall fun u => by
      dsimp [H]; split_ifs <;> simp)
  have hEi : IntegrableOn (E n) (Ioi 0) :=
    (Integrable.mono (hFi n)) (hEmeas n).aestronglyMeasurable (Eventually.of_forall fun u => by
      dsimp [E]; split_ifs <;> simp)
  rw [← integral_add hHi hEi]
  apply integral_congr_ae
  exact Eventually.of_forall fun u => by dsimp [H, E, F]; split_ifs <;> simp

/-- Layer cake for a nonnegative variable, including the kernel's jump at one. -/
lemma oneStep_kernel_layercake (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {f : ℕ → ℝ} (hf0 : ∀ k, 0 ≤ f k) {s : ℝ} (hs : 0 < s) :
    Integrable (fun k => stableKernel s (f k)) μ ∧
    (∫ k, stableKernel s (f k) ∂μ) =
      (∫ u in Ioi 0, stableKernelSlopePos s u * μ.real {k | u ≤ f k}) -
      (∫ u in Ioi 0, stableKernelSlopeNeg s u * μ.real {k | u ≤ f k}) -
      s * μ.real {k | 1 < f k} := by
  have hpi := integrable_stableKernelSlopePos s
  have hni := integrable_stableKernelSlopeNeg hs
  have hpb := fun (x : ℝ) (hx : 0 ≤ x) => abs_intervalIntegral_le_integral_of_nonneg hpi
    (fun _ => stableKernelSlopePos_nonneg hs) hx
  have hnb := fun (x : ℝ) (hx : 0 ≤ x) => abs_intervalIntegral_le_integral_of_nonneg hni
    (fun _ => stableKernelSlopeNeg_nonneg hs) hx
  have hp := integrable_primitive_comp_of_nonneg μ (measurable_of_countable _) hf0 hpi hpb
  have hn := integrable_primitive_comp_of_nonneg μ (measurable_of_countable _) hf0 hni hnb
  have hj : Integrable (fun k => if 1 < f k then s else 0) μ := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable s
    exact Eventually.of_forall fun k => by split_ifs <;> simp [abs_of_pos hs, hs.le]
  have heq : (fun k => stableKernel s (f k)) =
      (fun k => ((∫ t in 0..f k, stableKernelSlopePos s t) -
        (∫ t in 0..f k, stableKernelSlopeNeg s t)) - if 1 < f k then s else 0) := by
    funext k
    exact stableKernel_eq_primitive_pos_sub_neg s (f k) hs (hf0 k)
  constructor
  · rw [heq]
    exact (hp.sub hn).sub hj
  · have hsub := integral_sub (hp.sub hn) hj
    simp only [Pi.sub_apply] at hsub
    rw [heq, hsub, integral_sub hp hn,
      integral_primitive_tail_of_nonneg μ (measurable_of_countable _) hf0 hpi
        (fun _ => stableKernelSlopePos_nonneg hs) hpb,
      integral_primitive_tail_of_nonneg μ (measurable_of_countable _) hf0 hni
        (fun _ => stableKernelSlopeNeg_nonneg hs) hnb]
    congr 1
    calc
      (∫ k, (if 1 < f k then s else 0) ∂μ) = ∫ k in {k | 1 < f k}, s ∂μ := by
        exact integral_indicator (Set.to_countable _).measurableSet
      _ = _ := by simp [mul_comm]

/-- Exact tail representation of the positive-increment part. -/
lemma oneStep_scaled_positive_kernel (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    Integrable (fun k => stableKernel s (max (offspringIncrement k) 0 / r)) μ ∧
    (∫ k, stableKernel s (max (offspringIncrement k) 0 / r) ∂μ) =
      (∫ u in Ioi 0, stableKernelSlopePos s u * (incrementTail μ (u * r)).toReal) -
      (∫ u in Ioi 0, stableKernelSlopeNeg s u * (incrementTail μ (u * r)).toReal) -
      s * (strictIncrementTail μ r).toReal := by
  have h := oneStep_kernel_layercake μ (f := fun k => max (offspringIncrement k) 0 / r)
    (fun k => div_nonneg (le_max_right _ _) hr.le) hs
  refine ⟨h.1, h.2.trans ?_⟩
  have ht : ∀ u, 0 < u → μ.real {k | u ≤ max (offspringIncrement k) 0 / r} =
      (incrementTail μ (u * r)).toReal := by
    intro u hu
    congr 1
    ext k
    simp only [mem_ofPred_eq, le_div_iff₀ hr, offspringIncrement]
    rw [le_max_iff]
    have : ¬ u * r ≤ 0 := not_le.mpr (mul_pos hu hr)
    simp only [this, or_false]
  have hj : μ.real {k | 1 < max (offspringIncrement k) 0 / r} =
      (strictIncrementTail μ r).toReal := by
    congr 1
    ext k
    simp only [mem_ofPred_eq, lt_div_iff₀ hr, offspringIncrement, one_mul,
      lt_max_iff, not_lt.mpr hr.le, or_false]
  rw [hj]
  congr 1; congr 1 <;> apply integral_congr_ae <;>
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu <;> rw [ht u hu]

/-- The only negative increment contributes a second-order exponential remainder. -/
lemma oneStep_negative_remainder_tendsto
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n : ℕ => (n : ℝ) * (μ {0}).toReal *
      (Real.exp (s / a n) - 1 - s / a n)) atTop (𝓝 0) := by
  have hat := scaling_tendsto_atTop μ hμ.to_literal ha
  apply squeeze_zero' (g := fun n : ℕ =>
    s ^ 2 * Real.exp s * ((n : ℝ) / (a n) ^ 2))
  · filter_upwards [hat.eventually_ge_atTop 1] with n hn
    have harg : 0 ≤ s / a n := div_nonneg hs.le (zero_le_one.trans hn)
    have hrem : 0 ≤ Real.exp (s / a n) - 1 - s / a n := by
      linarith [Real.add_one_le_exp (s / a n)]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg) hrem
  · filter_upwards [hat.eventually_ge_atTop 1] with n hn
    have han : 0 < a n := zero_lt_one.trans_le hn
    have ht := exp_le_one_add_add_sq_mul_exp_max (s / a n)
    have harg : 0 ≤ s / a n := div_nonneg hs.le han.le
    have hargle : s / a n ≤ s := div_le_self hs.le hn
    rw [max_eq_left harg] at ht
    have hexp := Real.exp_le_exp.mpr hargle
    have hrem : Real.exp (s / a n) - 1 - s / a n ≤ (s / a n) ^ 2 * Real.exp s := by
      nlinarith [mul_le_mul_of_nonneg_left hexp (sq_nonneg (s / a n))]
    have hm : (μ {0}).toReal ≤ 1 := measureReal_le_one
    have hrem0 : 0 ≤ Real.exp (s / a n) - 1 - s / a n := by
      linarith [Real.add_one_le_exp (s / a n)]
    calc
      _ ≤ (n : ℝ) * 1 * ((s / a n) ^ 2 * Real.exp s) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _)) hrem hrem0
          (by positivity)
      _ = _ := by ring
  · simpa using (oneStep_nat_div_scale_sq_tendsto_zero μ hμ a ha).const_mul
      (s ^ 2 * Real.exp s)

lemma oneStep_compensated_kernel_identity {r s : ℝ} (hr : 1 ≤ r) (k : ℕ) :
    Real.exp (-(s / r) * offspringIncrement k) - 1 +
      (s / r) * (if |offspringIncrement k| ≤ r then offspringIncrement k else 0) =
    stableKernel s (max (offspringIncrement k) 0 / r) +
      if k = 0 then Real.exp (s / r) - 1 - s / r else 0 := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  by_cases hk : k = 0
  · subst k
    simp [offspringIncrement, stableKernel, hr]
    ring
  · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    have hx : 0 ≤ offspringIncrement k := by dsimp [offspringIncrement]; linarith
    have he : -(s / r) * offspringIncrement k = -s * (offspringIncrement k / r) := by ring
    simp only [hk, ↓reduceIte, add_zero, max_eq_left hx, abs_of_nonneg hx, stableKernel,
      div_le_one hr0, he]
    split_ifs <;> ring

lemma oneStep_compensated_integral_identity
    (μ : Measure ℕ) [IsProbabilityMeasure μ] {r s : ℝ} (hr : 1 ≤ r) (hs : 0 < s) :
    (∫ k, (Real.exp (-(s / r) * offspringIncrement k) - 1 +
      (s / r) * (if |offspringIncrement k| ≤ r then offspringIncrement k else 0)) ∂μ) =
    (∫ k, stableKernel s (max (offspringIncrement k) 0 / r) ∂μ) +
      (μ {0}).toReal * (Real.exp (s / r) - 1 - s / r) := by
  have hi := (oneStep_scaled_positive_kernel μ (zero_lt_one.trans_le hr) hs).1
  have hj : Integrable (fun k : ℕ => if k = 0 then Real.exp (s / r) - 1 - s / r else 0) μ := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable
      |Real.exp (s / r) - 1 - s / r|
    exact Eventually.of_forall fun k => by split_ifs <;> simp
  calc
    _ = ∫ k, (stableKernel s (max (offspringIncrement k) 0 / r) +
        if k = 0 then Real.exp (s / r) - 1 - s / r else 0) ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall (oneStep_compensated_kernel_identity hr)
    _ = _ := by
      rw [integral_add hi hj]
      congr 1
      have heq : (fun k : ℕ => if k = 0 then Real.exp (s / r) - 1 - s / r else 0) =
          ({0} : Set ℕ).indicator (fun _ => Real.exp (s / r) - 1 - s / r) := by
        funext k; simp [Set.indicator]
      rw [heq, integral_indicator (measurableSet_singleton 0)]
      simp [Measure.real]

/-- The one-step compensated Laplace exponent, with the audited absolute cutoff. -/
theorem oneStep_increment_laplace_exponent_tendsto
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      ∫ k, (Real.exp (-(s / a n) * offspringIncrement k) - 1 +
        (s / a n) * (if |offspringIncrement k| ≤ a n
          then offspringIncrement k else 0)) ∂μ)
      atTop (𝓝 (stableKernelIntegral s)) := by
  have hat := scaling_tendsto_atTop μ hμ.to_literal ha
  have hp := oneStep_positive_slope_tail_tendsto μ hμ a ha hs
  have hn := oneStep_negative_slope_tail_tendsto μ hμ a ha hs
  have hj := (rescaled_strictIncrementTail_tendsto μ hμ a ha zero_lt_one).const_mul s
  simp only [one_mul, div_one, mul_one] at hj
  have he := oneStep_negative_remainder_tendsto μ hμ a ha hs
  have hlim := ((hp.sub hn).sub hj).add he
  rw [add_zero, ← oneStep_stableKernelIntegral_layercake hs] at hlim
  apply hlim.congr'
  filter_upwards [hat.eventually_ge_atTop 1] with n han
  rw [oneStep_compensated_integral_identity μ han hs,
    (oneStep_scaled_positive_kernel μ (zero_lt_one.trans_le han) hs).2]
  simp only [mul_add, mul_sub]
  rw [← integral_const_mul, ← integral_const_mul]
  simp only [mul_assoc, mul_left_comm, mul_comm]

lemma oneStep_laplace_integrable (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {t : ℝ} (ht : 0 ≤ t) : Integrable (fun k => Real.exp (-t * offspringIncrement k)) μ := by
  apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable (Real.exp t)
  filter_upwards [] with k
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hx : -1 ≤ offspringIncrement k := by
    dsimp [offspringIncrement]; linarith [Nat.cast_nonneg (α := ℝ) k]
  nlinarith

/-- Algebraic centering form of the one-step Laplace exponent. -/
theorem oneStep_laplace_centering_tendsto
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n : ℕ => (n : ℝ) * (oneStepLaplace μ (s / a n) - 1) +
      s * centering μ a n / a n) atTop (𝓝 (stableKernelIntegral s)) := by
  have hat := scaling_tendsto_atTop μ hμ.to_literal ha
  have hm : offspringMean μ ≠ ⊤ := ne_top_of_lt (hμ.1.trans ENNReal.one_lt_top)
  apply (oneStep_increment_laplace_exponent_tendsto μ hμ a ha hs).congr'
  filter_upwards [hat.eventually_gt_atTop 0] with n han
  have hi := oneStep_laplace_integrable μ (div_nonneg hs.le han.le)
  have ht := integrable_truncatedIncrement μ hm (a n)
  have hadd := integral_add (hi.sub (integrable_const 1)) (ht.const_mul (s / a n))
  simp only [Pi.sub_apply] at hadd
  rw [hadd, integral_sub hi (integrable_const 1), integral_const_mul]
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul,
    oneStepLaplace, centering, truncatedIncrementMean]
  ring

end
end SubcriticalCauchy.Bienayme
