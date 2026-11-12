module

public import SubcriticalCauchy.StableLaplace
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section


private noncomputable def cutoffKernel (s r x : ℝ) : ℝ :=
  Real.exp (-s * x) - 1 + if x ≤ r then s * x else 0

private noncomputable def cutoffIntegral (s r : ℝ) : ℝ :=
  ∫ x in Set.Ioi 0, cutoffKernel s r x / x ^ 2

private lemma integrableOn_cutoffKernel (s : ℝ) (hs : 0 < s) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun x : ℝ => cutoffKernel s r x / x ^ 2) (Set.Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi hr.le, integrableOn_union]
  constructor
  · have hb : IntegrableOn (fun _ : ℝ => (|s| ^ 2 : ℝ)) (Set.Ioc 0 r) :=
      (integrableOn_const (C := |s| ^ 2) (hs := measure_Ioc_lt_top.ne) (hC := enorm_ne_top))
    apply hb.mono'
    · have hc : ContinuousOn (fun x : ℝ => (Real.exp (-s * x) - 1 + s * x) / x ^ 2)
          (Set.Ioc 0 r) := by
        apply ContinuousOn.div (by fun_prop) (by fun_prop)
        intro x hx
        exact pow_ne_zero _ (ne_of_gt hx.1)
      exact (hc.congr fun x hx => by simp [cutoffKernel, hx.2]).aestronglyMeasurable measurableSet_Ioc
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have hx0 : 0 < x := hx.1
      have hx1 : x ≤ r := hx.2
      have hlo : 0 ≤ Real.exp (-s * x) - 1 + s * x := by
        nlinarith [Real.add_one_le_exp (-s * x)]
      have hup : Real.exp (-s * x) - 1 + s * x ≤ s ^ 2 * x ^ 2 := by
        have h := exp_le_one_add_add_sq_mul_exp_max (-s * x)
        rw [show max (-s * x) 0 = 0 from max_eq_right (by nlinarith), Real.exp_zero, mul_one] at h
        nlinarith
      simp [cutoffKernel, hx1]
      rw [show -(s * x) = (-s) * x by ring, abs_of_nonneg hlo]
      exact (div_le_iff₀ (sq_pos_of_pos hx0)).mpr hup
  · have hp : IntegrableOn (fun x : ℝ => 2 * x ^ (-2 : ℝ)) (Set.Ioi r) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) hr).const_mul 2
    apply hp.mono'
    · have hc : ContinuousOn (fun x : ℝ => (Real.exp (-s * x) - 1) / x ^ 2) (Set.Ioi r) := by
        apply ContinuousOn.div (by fun_prop) (by fun_prop)
        intro x hx
        exact pow_ne_zero _ (ne_of_gt (hr.trans hx))
      exact (hc.congr fun x hx => by
        have hxr : r < x := hx
        simp [cutoffKernel, not_le.mpr hxr]).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hxr : r < x := hx
      have hx0 : 0 < x := hr.trans hxr
      simp [cutoffKernel, not_le.mpr hxr]
      rw [show -(s * x) = (-s) * x by ring]
      have he : Real.exp (-s * x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      have hrw : x ^ (-2 : ℝ) = (x ^ 2)⁻¹ := by
        rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hx0.le, Real.rpow_natCast]
      simp only [neg_mul]
      calc
        |Real.exp (-(s * x)) - 1| / x ^ 2 ≤ 2 / x ^ 2 := by
          apply div_le_div_of_nonneg_right _ (sq_pos_of_pos hx0).le
          calc
            |Real.exp (-(s * x)) - 1| ≤ Real.exp (-(s * x)) + 1 := by
              simpa [abs_of_pos (Real.exp_pos (-(s * x)))] using abs_sub (Real.exp (-(s * x))) 1
            _ ≤ 2 := by
              have he' : Real.exp (-(s * x)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
              linarith
        _ = 2 * (x ^ 2)⁻¹ := by ring

private lemma cutoffIntegral_eq (s : ℝ) (hs : 0 < s) :
    cutoffIntegral s 1 = s * cutoffIntegral 1 s := by
  have hscale := integral_comp_mul_left_Ioi'
    (fun x : ℝ => cutoffKernel 1 s x / x ^ 2) 0 hs
  rw [cutoffIntegral]
  calc
    (∫ x in Set.Ioi 0, cutoffKernel s 1 x / x ^ 2) =
        s * (s * ∫ x in Set.Ioi 0, cutoffKernel 1 s (s * x) / (s * x) ^ 2) := by
      rw [← integral_const_mul, ← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hx0 : 0 < x := hx
      have hsx : x ≤ 1 ↔ s * x ≤ s := by
        constructor
        · intro hx1
          simpa using mul_le_mul_of_nonneg_left hx1 hs.le
        · intro hx1
          have hx1' : s * x ≤ s * 1 := by simpa using hx1
          exact le_of_mul_le_mul_left hx1' hs 
      simp only [cutoffKernel]
      rw [if_congr hsx rfl rfl]
      field_simp
    _ = s * cutoffIntegral 1 s := by
      rw [smul_eq_mul, mul_zero] at hscale
      rw [hscale]
      rfl

private lemma cutoffIntegral_difference (r : ℝ) (hr : 0 < r) :
    cutoffIntegral 1 r - cutoffIntegral 1 1 = Real.log r := by
  rw [cutoffIntegral, cutoffIntegral, ← integral_sub (integrableOn_cutoffKernel 1 one_pos hr)
    (integrableOn_cutoffKernel 1 one_pos one_pos)]
  by_cases hr1 : 1 ≤ r
  · rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (s := Set.Ioc 1 r) (t := Set.Ioi 0)
      measurableSet_Ioi (fun x hx => (show (0 : ℝ) < 1 from one_pos).trans hx.1) (by
        intro x hx
        have hx0 : 0 < x := hx.1
        by_cases hx1 : 1 < x
        · have hxr : r < x := by
            by_contra h
            exact hx.2 ⟨hx1, le_of_not_gt h⟩
          simp [cutoffKernel, not_le.mpr hxr, not_le.mpr hx1]
        · by_cases hxle : x ≤ 1
          · have hxr : x ≤ r := hxle.trans hr1
            simp [cutoffKernel, hxle, hxr]
          · have hx1' : 1 < x := lt_of_not_ge hxle
            have hxnot : x ∉ Set.Ioc 1 r := hx.2
            have hxr : r < x := lt_of_not_ge (fun h => hxnot ⟨hx1', h⟩)
            simp [cutoffKernel, not_le.mpr hx1', not_le.mpr hxr])]
    calc
      (∫ x in Set.Ioc 1 r, cutoffKernel 1 r x / x ^ 2 - cutoffKernel 1 1 x / x ^ 2) =
          ∫ x in Set.Ioc 1 r, 1 / x := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro x hx
        have hx1 : 1 < x := hx.1
        have hxr : x ≤ r := hx.2
        simp [cutoffKernel, hxr, not_le.mpr hx1]
        field_simp [ne_of_gt (zero_lt_one.trans hx1)]
        ring
      _ = Real.log r := by
        rw [← intervalIntegral.integral_of_le hr1]
        simpa only [div_one] using integral_one_div_of_pos zero_lt_one (zero_lt_one.trans_le hr1)
  · have hr1' : r < 1 := lt_of_not_ge hr1
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (s := Set.Ioc r 1) (t := Set.Ioi 0)
      measurableSet_Ioi (fun x hx => hr.trans hx.1) (by
        intro x hx
        have hx0 : 0 < x := hx.1
        by_cases hxr : r < x
        · have hx1 : 1 < x := by
            by_contra h
            exact hx.2 ⟨hxr, le_of_not_gt h⟩
          simp [cutoffKernel, not_le.mpr hx1, not_le.mpr hxr]
        · by_cases hxle : x ≤ r
          · have hx1 : x ≤ 1 := hxle.trans hr1'.le
            simp [cutoffKernel, hxle, hx1]
          · have hxr' : x ≤ r := le_of_not_gt hxr
            have hx1 : x ≤ 1 := hxr'.trans hr1'.le
            simp [cutoffKernel, hxr', hx1])]
    calc
      (∫ x in Set.Ioc r 1, cutoffKernel 1 r x / x ^ 2 - cutoffKernel 1 1 x / x ^ 2) =
          -(∫ x in Set.Ioc r 1, 1 / x) := by
        rw [← integral_neg]
        apply setIntegral_congr_fun measurableSet_Ioc
        intro x hx
        have hxr : r < x := hx.1
        have hx1 : x ≤ 1 := hx.2
        simp [cutoffKernel, not_le.mpr hxr, hx1]
        field_simp [ne_of_gt (hr.trans hxr)]
        ring
      _ = Real.log r := by
        rw [← intervalIntegral.integral_of_le hr1'.le, integral_one_div_of_pos hr zero_lt_one]
        simp

/-- Normalization of the index-one stable kernel for every positive parameter. -/
theorem stableKernelIntegral_eq {s : ℝ} (hs : 0 < s) :
    stableKernelIntegral s =
      s * Real.log s + (Real.eulerMascheroniConstant - 1) * s := by
  have hc := cutoffIntegral_difference s hs
  calc
    stableKernelIntegral s = cutoffIntegral s 1 := rfl
    _ = s * cutoffIntegral 1 s := cutoffIntegral_eq s hs
    _ = s * (cutoffIntegral 1 s - cutoffIntegral 1 1) + s * stableKernelIntegral 1 := by
      change _ = _ + s * cutoffIntegral 1 1
      ring
    _ = s * Real.log s + s * (Real.eulerMascheroniConstant - 1) := by
      rw [hc, stableKernelIntegral_one]
    _ = s * Real.log s + (Real.eulerMascheroniConstant - 1) * s := by ring

end
end SubcriticalCauchy.Bienayme
