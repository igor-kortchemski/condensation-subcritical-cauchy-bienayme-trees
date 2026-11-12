module

public import SubcriticalCauchy.CauchyOneUnique
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.MeasureTheory.Measure.TightNormed
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
public import Mathlib.NumberTheory.Harmonic.GammaDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import SubcriticalCauchy.TruncatedExponentialAux
public import SubcriticalCauchy.StableKernel

/-!
# Laplace continuity and two-sided tightness

The truncation argument is ported from `scratch/bgw-ref/LaplaceContinuity.lean`
(BGW-formalization, same author, Apache 2.0). Tightness uses exponential tails,
so no finite first-moment or centering hypothesis is required.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace SubcriticalCauchy.Bienayme

noncomputable section

private lemma intervalIntegral_zero_one_eq_of_update
    {F G : ℝ → ℝ} (hzero : Tendsto F (𝓝[≠] 0) (𝓝 0))
    (hcont : ContinuousOn F (Set.Ioi 0))
    (hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt F (G x) x)
    (hG : IntervalIntegrable G volume 0 1) :
    ∫ x in (0 : ℝ)..1, G x = F 1 := by
  let U : ℝ → ℝ := Function.update F 0 0
  have hUzero : ContinuousAt U 0 := continuousAt_update_same.mpr hzero
  have hUcont : ContinuousOn U (Set.Icc 0 1) := by
    intro x hx
    by_cases hx0 : x = 0
    · subst x
      exact hUzero.continuousWithinAt
    · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
      apply ContinuousAt.continuousWithinAt
      apply (hcont.continuousAt (Ioi_mem_nhds hxpos)).congr_of_eventuallyEq
        ((eventually_ne_nhds hx0).mono fun y hy => Function.update_of_ne hy 0 F)
  have hUderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt U (G x) x := by
    intro x hx
    apply (hderiv x hx).congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hx.1.ne'] with y hy
    exact Function.update_of_ne hy 0 F
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le zero_le_one hUcont
    (fun x hx => (hUderiv x hx).hasDerivWithinAt) hG
  simpa [U, Function.update_of_ne zero_ne_one] using h

private lemma stable_g_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-y) - 1 + y) (1 - Real.exp (-x)) x := by
  convert ((hasDerivAt_neg x).exp.sub_const 1).add (hasDerivAt_id x) using 1
  · funext y
    simp only [Pi.add_apply, id_eq]
  · ring

private lemma integrable_stableKernel_unit :
    IntegrableOn (fun x : ℝ => (Real.exp (-x) - 1 + x) / x ^ 2) (Set.Ioc 0 1) := by
  have hb : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc 0 1) := (integrableOn_const (C := (1 : ℝ)) (hs := measure_Ioc_lt_top.ne) (hC := enorm_ne_top))
  apply hb.mono'
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioc
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx
    have hx0 : 0 < x := hx.1
    positivity
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx0 : 0 < x := hx.1
    have hx1 : x ≤ 1 := hx.2
    have hlo : 0 ≤ Real.exp (-x) - 1 + x := by
      linarith [Real.add_one_le_exp (-x)]
    have hup : Real.exp (-x) - 1 + x ≤ x ^ 2 := by
      have h := exp_le_one_add_add_sq_mul_exp_max (-x)
      rw [show max (-x) 0 = 0 from max_eq_right (by linarith), Real.exp_zero, mul_one] at h
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hlo (sq_nonneg x))]
    exact (div_le_one (sq_pos_of_pos hx0)).mpr hup

private lemma integrable_ein_unit :
    IntegrableOn (fun x : ℝ => (1 - Real.exp (-x)) / x) (Set.Ioc 0 1) := by
  have hb : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc 0 1) := (integrableOn_const (C := (1 : ℝ)) (hs := measure_Ioc_lt_top.ne) (hC := enorm_ne_top))
  apply hb.mono'
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioc
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx
    have hx0 : 0 < x := hx.1
    positivity
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx0 : 0 < x := hx.1
    have hlo : 0 ≤ 1 - Real.exp (-x) := by
      linarith [Real.exp_le_one_iff.mpr (by linarith : -x ≤ 0)]
    have hup : 1 - Real.exp (-x) ≤ x := by linarith [Real.add_one_le_exp (-x)]
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hlo hx0.le)]
    exact (div_le_one hx0).mpr hup

private lemma integral_stableKernel_unit_formula :
    (∫ x in (0 : ℝ)..1, (Real.exp (-x) - 1 + x) / x ^ 2) =
      -Real.exp (-1) + ∫ x in (0 : ℝ)..1, (1 - Real.exp (-x)) / x := by
  have hzero : Tendsto (fun x : ℝ => (Real.exp (-x) - 1 + x) / x) (𝓝[≠] 0) (𝓝 0) := by
    have h := (hasDerivAt_iff_tendsto_slope.mp (stable_g_hasDerivAt 0))
    convert h using 1
    · ext x
      simp [slope]
      ring
    · norm_num
  have hcont : ContinuousOn (fun x : ℝ => (Real.exp (-x) - 1 + x) / x) (Set.Ioi 0) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx
    exact ne_of_gt hx
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (fun y : ℝ => (Real.exp (-y) - 1 + y) / y)
        ((1 - Real.exp (-x)) / x - (Real.exp (-x) - 1 + x) / x ^ 2) x := by
    intro x hx
    have h := (stable_g_hasDerivAt x).div (hasDerivAt_id x) hx.1.ne'
    convert h using 1
    · funext y
      simp only [Pi.div_apply, id_eq]
    · dsimp [id]
      field_simp
  have hG : IntervalIntegrable (fun x : ℝ => (1 - Real.exp (-x)) / x -
      (Real.exp (-x) - 1 + x) / x ^ 2) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact (integrable_ein_unit.sub integrable_stableKernel_unit)
  have h := intervalIntegral_zero_one_eq_of_update hzero hcont hderiv hG
  have hsplit : (∫ x in (0 : ℝ)..1, (1 - Real.exp (-x)) / x) -
      ∫ x in (0 : ℝ)..1, (Real.exp (-x) - 1 + x) / x ^ 2 = Real.exp (-1) := by
    calc
      (∫ x in (0 : ℝ)..1, (1 - Real.exp (-x)) / x) -
          ∫ x in (0 : ℝ)..1, (Real.exp (-x) - 1 + x) / x ^ 2 =
          ∫ x in (0 : ℝ)..1, ((1 - Real.exp (-x)) / x -
            (Real.exp (-x) - 1 + x) / x ^ 2) :=
        (intervalIntegral.integral_sub
          ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 integrable_ein_unit)
          ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
            integrable_stableKernel_unit)).symm
      _ = (Real.exp (-1) - 1 + 1) / 1 := h
      _ = Real.exp (-1) := by norm_num
  linarith

private lemma integrableOn_exp_mul_log :
    IntegrableOn (fun x : ℝ => Real.exp (-x) * Real.log x) (Set.Ioi 0) := by
  apply Integrable.mono' (g := fun x : ℝ => (2 * x ^ (- (1 : ℝ) / 2) + x) * Real.exp (-x))
  · have hint := (integrableOn_rpow_mul_exp_neg_mul_rpow (s := -1 / 2) (p := 1) (b := 1)
      (by norm_num) one_pos one_pos).const_mul 2 |>.add
        (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := 1)
          (by norm_num) one_pos one_pos)
    convert hint using 1
    ext x
    simp [Pi.add_apply, neg_mul, Real.rpow_one, add_mul, mul_assoc]
  · fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hx
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos (-x))]
    rw [mul_comm (Real.exp (-x))]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos (-x)).le
    rw [abs_le]
    constructor
    · linarith [Real.neg_rpow_div_le_log hx0.le one_half_pos]
    · exact (Real.log_le_self hx0.le).trans (le_add_of_nonneg_left (by positivity))

private lemma integrableOn_exp_div_self_tail :
    IntegrableOn (fun x : ℝ => Real.exp (-x) / x) (Set.Ioi 1) := by
  apply (integrableOn_exp_neg_Ioi 1).mono'
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx
    exact ne_of_gt (zero_lt_one.trans hx)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : 1 < x := hx
    have hx0 : 0 < x := zero_lt_one.trans hx1
    rw [Real.norm_eq_abs, abs_of_pos (div_pos (Real.exp_pos _) hx0)]
    rw [div_le_iff₀ hx0]
    nlinarith [Real.exp_pos (-x)]

private lemma integrableOn_exp_mul_log_tail :
    IntegrableOn (fun x : ℝ => Real.exp (-x) * Real.log x) (Set.Ioi 1) :=
  integrableOn_exp_mul_log.mono_set (Set.Ioi_subset_Ioi zero_le_one)

private lemma integrableOn_stableKernel_tail :
    IntegrableOn (fun x : ℝ => (Real.exp (-x) - 1) / x ^ 2) (Set.Ioi 1) := by
    have hp : IntegrableOn (fun x : ℝ => 2 * x ^ (-2 : ℝ)) (Set.Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).const_mul 2
    apply hp.mono'
    · have hc : ContinuousOn (fun x : ℝ => (Real.exp (-x) - 1) / x ^ 2) (Set.Ioi 1) := by
        apply ContinuousOn.div (by fun_prop) (by fun_prop)
        intro x hx
        exact pow_ne_zero _ (ne_of_gt (zero_lt_one.trans hx))
      exact hc.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx1 : 1 < x := hx
      have hx0 : 0 < x := zero_lt_one.trans hx1
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (sq_pos_of_pos hx0)]
      have he : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have hr : x ^ (-2 : ℝ) = (x ^ 2)⁻¹ := by
        rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hx0.le, Real.rpow_natCast]
      rw [hr]
      calc
        |Real.exp (-x) - 1| / x ^ 2 ≤ 2 / x ^ 2 := by
          apply div_le_div_of_nonneg_right _ (sq_pos_of_pos hx0).le
          calc
            |Real.exp (-x) - 1| ≤ Real.exp (-x) + 1 := by
              simpa [abs_of_pos (Real.exp_pos (-x))] using abs_sub (Real.exp (-x)) 1
            _ ≤ 2 := by
              linarith
        _ = 2 * (x ^ 2)⁻¹ := by ring
private lemma integral_stableKernel_tail_formula :
    (∫ x in Set.Ioi 1, (Real.exp (-x) - 1) / x ^ 2) =
      (Real.exp (-1) - 1) - ∫ x in Set.Ioi 1, Real.exp (-x) / x := by
  have hI : IntegrableOn (fun x : ℝ => (Real.exp (-x) - 1) / x ^ 2) (Set.Ioi 1) := by
    have hp : IntegrableOn (fun x : ℝ => 2 * x ^ (-2 : ℝ)) (Set.Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).const_mul 2
    apply hp.mono'
    · have hc : ContinuousOn (fun x : ℝ => (Real.exp (-x) - 1) / x ^ 2) (Set.Ioi 1) := by
        apply ContinuousOn.div (by fun_prop) (by fun_prop)
        intro x hx
        exact pow_ne_zero _ (ne_of_gt (zero_lt_one.trans hx))
      exact hc.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx1 : 1 < x := hx
      have hx0 : 0 < x := zero_lt_one.trans hx1
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (sq_pos_of_pos hx0)]
      have he : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have hr : x ^ (-2 : ℝ) = (x ^ 2)⁻¹ := by
        rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hx0.le, Real.rpow_natCast]
      rw [hr]
      calc
        |Real.exp (-x) - 1| / x ^ 2 ≤ 2 / x ^ 2 := by
          apply div_le_div_of_nonneg_right _ (sq_pos_of_pos hx0).le
          calc
            |Real.exp (-x) - 1| ≤ Real.exp (-x) + 1 := by
              simpa [abs_of_pos (Real.exp_pos (-x))] using abs_sub (Real.exp (-x)) 1
            _ ≤ 2 := by linarith
        _ = 2 * (x ^ 2)⁻¹ := by ring
  have hderiv : ∀ x ∈ Set.Ici (1 : ℝ),
      HasDerivAt (fun y : ℝ => -(Real.exp (-y) - 1) / y)
        ((Real.exp (-x) - 1) / x ^ 2 + Real.exp (-x) / x) x := by
    intro x hx
    have hx0 : 0 < x := zero_lt_one.trans_le hx
    have hg : HasDerivAt (fun y : ℝ => Real.exp (-y) - 1) (-Real.exp (-x)) x := by
      convert (hasDerivAt_neg x).exp.sub_const 1 using 1 ; ring
    have h := hg.neg.div (hasDerivAt_id x) hx0.ne'
    convert h using 1
    · funext y
      simp only [Pi.neg_apply, Pi.div_apply, id_eq]
    · dsimp [id]
      field_simp
      ring
  have hlim : Tendsto (fun x : ℝ => -(Real.exp (-x) - 1) / x) atTop (𝓝 0) := by
    have h := (Real.tendsto_exp_neg_atTop_nhds_zero.sub_const 1).div_atTop tendsto_id
    convert h.neg using 1
    · ext x
      simp only [id_eq]
      ring
    · simp
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (hI.add integrableOn_exp_div_self_tail) hlim
  rw [integral_add hI integrableOn_exp_div_self_tail] at h
  norm_num at h
  linarith

private lemma integral_ein_log_unit_formula :
    (∫ x in (0 : ℝ)..1, (1 - Real.exp (-x)) / x) =
      -(∫ x in (0 : ℝ)..1, Real.exp (-x) * Real.log x) := by
  have hzero : Tendsto (fun x : ℝ => (1 - Real.exp (-x)) * Real.log x) (𝓝[≠] 0) (𝓝 0) := by
    have hg : HasDerivAt (fun y : ℝ => 1 - Real.exp (-y)) (Real.exp 0) 0 := by
      convert hasDerivAt_const (x := 0) (c := (1 : ℝ)) |>.sub ((hasDerivAt_neg 0).exp) using 1 ; ring
    have hs := hasDerivAt_iff_tendsto_slope.mp hg
    have hlog : Tendsto (fun x : ℝ => x * Real.log x) (𝓝[≠] 0) (𝓝 0) :=
      by simpa using (Real.continuous_mul_log.tendsto 0).mono_left nhdsWithin_le_nhds
    have h := hs.mul hlog
    simp only [mul_zero] at h
    convert h using 1
    · ext x
      by_cases hx : x = 0
      · subst x
        simp
      · simp [slope]
        field_simp
  have hcont : ContinuousOn (fun x : ℝ => (1 - Real.exp (-x)) * Real.log x) (Set.Ioi 0) := by
    apply ContinuousOn.mul (by fun_prop)
    apply ContinuousOn.log (by fun_prop)
    intro x hx
    exact ne_of_gt hx
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (fun y : ℝ => (1 - Real.exp (-y)) * Real.log y)
        (Real.exp (-x) * Real.log x + (1 - Real.exp (-x)) / x) x := by
    intro x hx
    have hg : HasDerivAt (fun y : ℝ => 1 - Real.exp (-y)) (Real.exp (-x)) x := by
      convert hasDerivAt_const (x := x) (c := (1 : ℝ)) |>.sub ((hasDerivAt_neg x).exp) using 1 ; ring
    convert hg.mul (Real.hasDerivAt_log hx.1.ne') using 1 ; field_simp
  have hG : IntervalIntegrable (fun x : ℝ => Real.exp (-x) * Real.log x +
      (1 - Real.exp (-x)) / x) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact (integrableOn_exp_mul_log.mono_set Set.Ioc_subset_Ioi_self).add integrable_ein_unit
  have h := intervalIntegral_zero_one_eq_of_update hzero hcont hderiv hG
  rw [intervalIntegral.integral_add
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
      (integrableOn_exp_mul_log.mono_set Set.Ioc_subset_Ioi_self))
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 integrable_ein_unit)] at h
  norm_num at h
  linarith

private lemma integral_exp_div_log_tail_formula :
    (∫ x in Set.Ioi 1, Real.exp (-x) / x) =
      ∫ x in Set.Ioi 1, Real.exp (-x) * Real.log x := by
  have hderiv : ∀ x ∈ Set.Ici (1 : ℝ),
      HasDerivAt (fun y : ℝ => -Real.exp (-y) * Real.log y)
        (Real.exp (-x) * Real.log x - Real.exp (-x) / x) x := by
    intro x hx
    have hx0 : 0 < x := zero_lt_one.trans_le hx
    convert ((hasDerivAt_neg x).exp.neg.mul (Real.hasDerivAt_log hx0.ne')) using 1
    simp only [Pi.neg_apply]
    ring
  have hexp : Tendsto (fun x : ℝ => Real.exp (-x) * Real.log x) atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun x : ℝ => Real.exp (-x) * x)
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      exact mul_nonneg (Real.exp_nonneg _) (Real.log_nonneg hx)
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      exact mul_le_mul_of_nonneg_left (Real.log_le_self (by positivity)) (Real.exp_nonneg _)
    · simpa [Real.rpow_one, mul_comm] using
        tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) 1 one_pos
  have hlim : Tendsto (fun x : ℝ => -Real.exp (-x) * Real.log x) atTop (𝓝 0) := by
    simpa using hexp.neg
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
    (integrableOn_exp_mul_log_tail.sub integrableOn_exp_div_self_tail) hlim
  rw [integral_sub integrableOn_exp_mul_log_tail integrableOn_exp_div_self_tail] at h
  norm_num at h
  linarith

private noncomputable def truncExp (s : ℝ) (k : ℕ) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x : ℝ => min (Real.exp (-s * x)) ((k : ℝ) + 1))
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).min continuous_const)
    ((k : ℝ) + 1) (fun x => by
      rw [Real.norm_of_nonneg (le_min (Real.exp_nonneg _) (by positivity))]
      exact min_le_right _ _)

private theorem truncExp_apply (s : ℝ) (k : ℕ) (x : ℝ) :
    truncExp s k x = min (Real.exp (-s * x)) ((k : ℝ) + 1) := rfl

private theorem truncExp_nonneg (s : ℝ) (k : ℕ) (x : ℝ) : 0 ≤ truncExp s k x := by
  rw [truncExp_apply]
  exact le_min (Real.exp_nonneg _) (by positivity)

private theorem exp_sub_trunc_le (s : ℝ) (k : ℕ) (x : ℝ) :
    Real.exp (-s * x) - truncExp s k x ≤ Real.exp (-(2 * s) * x) / ((k : ℝ) + 1) := by
  have hR : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hF2 : Real.exp (-(2 * s) * x) = Real.exp (-s * x) ^ 2 := by
    have h := Real.exp_nat_mul (-s * x) 2
    push_cast at h
    rw [← h]
    congr 1
    ring
  rw [hF2, truncExp_apply, le_div_iff₀ hR]
  set F := Real.exp (-s * x)
  set R := (k : ℝ) + 1
  rcases le_total F R with h | h
  · rw [min_eq_left h]
    simp only [sub_self, zero_mul]
    positivity
  · rw [min_eq_right h]
    nlinarith [sq_nonneg (F - R / 2), sq_nonneg R]

/-- Weak limits inherit the limiting negative Laplace transform, including integrability. -/
theorem laplace_eq_of_exponential_tendsto {Λ : ℝ → ℝ} {P : ℕ → ProbabilityMeasure ℝ}
    {Q : ProbabilityMeasure ℝ} (hPQ : Tendsto P atTop (𝓝 Q))
    (hL : ∀ s : ℝ, 0 < s → Tendsto
      (fun n => ∫ x, Real.exp (-s * x) ∂(P n : Measure ℝ)) atTop
      (𝓝 (Real.exp (Λ s))))
    {s : ℝ} (hs : 0 < s) :
    Integrable (fun x : ℝ => Real.exp (-s * x)) (Q : Measure ℝ) ∧
      ∫ x, Real.exp (-s * x) ∂(Q : Measure ℝ) = Real.exp (Λ s) := by
  have hint : ∀ t : ℝ, 0 < t →
      ∀ᶠ n in atTop, Integrable (fun x : ℝ => Real.exp (-t * x)) (P n : Measure ℝ) := by
    intro t ht
    filter_upwards [(hL t ht).eventually_ne (Real.exp_pos _).ne'] with n hn
    by_contra h
    exact hn (integral_undef h)
  let E := Real.exp (Λ s)
  let D := Real.exp (Λ (2 * s)) + 1
  have hD2 : ∀ᶠ n in atTop,
      ∫ x, Real.exp (-(2 * s) * x) ∂(P n : Measure ℝ) ≤ D :=
    ((hL (2 * s) (by positivity)).eventually
      (gt_mem_nhds (by simp [D] : Real.exp (Λ (2 * s)) < D))).mono fun n hn => hn.le
  have hconv : ∀ k : ℕ, Tendsto (fun n => ∫ x, truncExp s k x ∂(P n : Measure ℝ)) atTop
      (𝓝 (∫ x, truncExp s k x ∂(Q : Measure ℝ))) :=
    fun k => ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hPQ (truncExp s k)
  have hgint : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (k : ℕ), Integrable (truncExp s k) μ :=
    fun μ _ k => (truncExp s k).integrable μ
  have hup : ∀ k : ℕ, ∫ x, truncExp s k x ∂(Q : Measure ℝ) ≤ E := by
    intro k
    refine le_of_tendsto_of_tendsto (hconv k) (hL s hs) ?_
    filter_upwards [hint s hs] with n hn
    exact integral_mono (hgint _ k) hn (fun x => min_le_left _ _)
  have hlow : ∀ k : ℕ, E - D / ((k : ℝ) + 1) ≤ ∫ x, truncExp s k x ∂(Q : Measure ℝ) := by
    intro k
    refine le_of_tendsto_of_tendsto ((hL s hs).sub_const _) (hconv k) ?_
    filter_upwards [hint s hs, hint (2 * s) (by positivity), hD2] with n h1 h2 h3
    have hmono := integral_mono (h1.sub (hgint _ k)) (h2.div_const _) (exp_sub_trunc_le s k)
    simp only [Pi.sub_apply] at hmono
    rw [integral_sub h1 (hgint _ k), integral_div] at hmono
    have h4 : (∫ x, Real.exp (-(2 * s) * x) ∂(P n : Measure ℝ)) / ((k : ℝ) + 1) ≤
        D / ((k : ℝ) + 1) := div_le_div_of_nonneg_right h3 (by positivity)
    linarith
  have hFint : Integrable (fun x : ℝ => Real.exp (-s * x)) (Q : Measure ℝ) := by
    refine integrable_of_tendsto (G := fun k x => truncExp s k x) ?_ ?_ ?_
    · refine Eventually.of_forall fun x => ?_
      obtain ⟨N, hN⟩ := exists_nat_ge (Real.exp (-s * x))
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop N] with k hk
      have hk' : (N : ℝ) ≤ k := by exact_mod_cast hk
      rw [truncExp_apply, min_eq_left (by linarith)]
    · exact fun k => (truncExp s k).continuous.aestronglyMeasurable
    · refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := E)) ?_
      refine liminf_le_of_frequently_le' (Frequently.of_forall fun k => ?_)
      rw [← ofReal_integral_norm_eq_lintegral_enorm (hgint _ k)]
      apply ENNReal.ofReal_le_ofReal
      have hnorm : ∫ x, ‖truncExp s k x‖ ∂(Q : Measure ℝ) = ∫ x, truncExp s k x ∂(Q : Measure ℝ) :=
        integral_congr_ae (Eventually.of_forall fun x =>
          Real.norm_of_nonneg (truncExp_nonneg s k x))
      rw [hnorm]
      exact hup k
  have hmt := integral_tendsto_of_tendsto_of_monotone (μ := (Q : Measure ℝ))
    (f := fun k x => truncExp s k x) (F := fun x => Real.exp (-s * x))
    (fun k => hgint _ k) hFint
    (Eventually.of_forall fun x k l hkl => by
      simp only [truncExp_apply]
      refine min_le_min le_rfl ?_
      have h : (k : ℝ) ≤ l := by exact_mod_cast hkl
      linarith)
    (Eventually.of_forall fun x => by
      obtain ⟨N, hN⟩ := exists_nat_ge (Real.exp (-s * x))
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop N] with k hk
      have hk' : (N : ℝ) ≤ k := by exact_mod_cast hk
      rw [truncExp_apply, min_eq_left (by linarith)])
  have hlim0 : Tendsto (fun k : ℕ => D / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have hsq : Tendsto (fun k : ℕ => ∫ x, truncExp s k x ∂(Q : Measure ℝ)) atTop (𝓝 E) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds hlow hup
    simpa using (tendsto_const_nhds (x := E)).sub hlim0
  exact ⟨hFint, tendsto_nhds_unique hmt hsq⟩

/-- Laplace transforms factor over finite independent products. -/
theorem integral_exp_sum_pi {ι : Type*} [Fintype ι] (μ : ι → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] (c : ι → ℝ) (s : ℝ) :
    (∫ x : ι → ℝ, Real.exp (-s * ∑ i, c i * x i) ∂Measure.pi μ) =
      ∏ i, ∫ x, Real.exp (-s * c i * x) ∂μ i := by
  rw [show (fun x : ι → ℝ => Real.exp (-s * ∑ i, c i * x i)) =
    (fun x : ι → ℝ => ∏ i, Real.exp (-s * c i * x i)) by
      funext x
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring]
  exact integral_fintype_prod_eq_prod (fun i => Real.exp ∘ fun x : ℝ => -s * c i * x)

private lemma measureReal_lower_tail_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {s R : ℝ} (hs : 0 < s)
    (hint : Integrable (fun x : ℝ => Real.exp (-s * x)) μ) :
    μ.real {x : ℝ | x < -R} ≤ Real.exp (-s * R) * ∫ x, Real.exp (-s * x) ∂μ := by
  let f : ℝ → ℝ := fun x => Real.exp (-s * R) * Real.exp (-s * x)
  have hf : Integrable f μ := hint.const_mul _
  have hle : ∀ x ∈ {x : ℝ | x < -R}, 1 ≤ f x := by
    intro x hx
    dsimp [f]
    rw [← Real.exp_zero, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp at hx
    nlinarith
  have h := hf.measure_le_integral (Eventually.of_forall fun x => by positivity) hle
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  have hL : 0 ≤ ∫ x, Real.exp (-s * x) ∂μ :=
    integral_nonneg (fun x => (Real.exp_pos _).le)
  rw [show (∫ x, f x ∂μ) = Real.exp (-s * R) * ∫ x, Real.exp (-s * x) ∂μ by
    exact integral_const_mul _ _] at hr
  rw [ENNReal.toReal_ofReal (mul_nonneg (Real.exp_nonneg _) hL)] at hr
  simpa only [measureReal_def, integral_const_mul, f, neg_mul] using hr

private lemma integral_sq_one_sub_exp {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {s : ℝ} (hint : Integrable (fun x : ℝ => Real.exp (-s * x)) μ)
    (hint2 : Integrable (fun x : ℝ => Real.exp (-(2 * s) * x)) μ) :
    (∫ x, (1 - Real.exp (-s * x)) ^ 2 ∂μ) =
      1 - 2 * (∫ x, Real.exp (-s * x) ∂μ) + ∫ x, Real.exp (-(2 * s) * x) ∂μ := by
  have hconst : Integrable (fun _ : ℝ => (1 : ℝ)) μ := integrable_const 1
  have heq : (fun x : ℝ => (1 - Real.exp (-s * x)) ^ 2) =
      fun x : ℝ => 1 - 2 * Real.exp (-s * x) + Real.exp (-(2 * s) * x) := by
    funext x
    rw [show -(2 * s) * x = (-s * x) + (-s * x) by ring, Real.exp_add]
    ring
  rw [heq]
  calc
    (∫ x, 1 - 2 * Real.exp (-s * x) + Real.exp (-(2 * s) * x) ∂μ) =
        (∫ x, 1 - 2 * Real.exp (-s * x) ∂μ) +
          ∫ x, Real.exp (-(2 * s) * x) ∂μ := by
      apply integral_add
      · exact hconst.sub (hint.const_mul 2)
      · exact hint2
    _ = _ := by
      rw [integral_sub hconst (hint.const_mul 2), integral_const_mul]
      simp

private lemma measureReal_upper_tail_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {s R : ℝ} (hs : 0 < s) (hR : 0 < R)
    (hint : Integrable (fun x : ℝ => Real.exp (-s * x)) μ)
    (hint2 : Integrable (fun x : ℝ => Real.exp (-(2 * s) * x)) μ) :
    μ.real {x : ℝ | R < x} ≤
      (1 - 2 * (∫ x, Real.exp (-s * x) ∂μ) + ∫ x, Real.exp (-(2 * s) * x) ∂μ) /
        (1 - Real.exp (-s * R)) ^ 2 := by
  let C : ℝ := Real.exp (-s * R)
  have hC : C < 1 := by
    dsimp [C]
    exact Real.exp_lt_one_iff.mpr (by nlinarith)
  have hd : 0 < (1 - C) ^ 2 := sq_pos_of_pos (by linarith)
  let f : ℝ → ℝ := fun x => (1 - Real.exp (-s * x)) ^ 2 / (1 - C) ^ 2
  have hf : Integrable f μ := by
    have hsq : Integrable (fun x : ℝ => (1 - Real.exp (-s * x)) ^ 2) μ := by
      have h := ((integrable_const (1 : ℝ)).sub (hint.const_mul 2)).add hint2
      convert h using 1
      funext x
      simp only [Pi.add_apply, Pi.sub_apply]
      rw [show -(2 * s) * x = (-s * x) + (-s * x) by ring, Real.exp_add]
      ring
    exact hsq.div_const _
  have hle : ∀ x ∈ {x : ℝ | R < x}, 1 ≤ f x := by
    intro x hx
    dsimp [f]
    rw [le_div_iff₀ hd]
    have hE : Real.exp (-s * x) ≤ C := by
      apply Real.exp_le_exp.mpr
      dsimp at hx
      nlinarith
    nlinarith [sq_nonneg (Real.exp (-s * x) - C)]
  have h := hf.measure_le_integral (Eventually.of_forall fun x => by positivity) hle
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_ofReal (integral_nonneg_of_ae (Eventually.of_forall fun x => by positivity))] at hr
  change μ.real {x : ℝ | R < x} ≤ ∫ x, f x ∂μ at hr
  rw [show (∫ x, f x ∂μ) =
      (1 - 2 * (∫ x, Real.exp (-s * x) ∂μ) + ∫ x, Real.exp (-(2 * s) * x) ∂μ) /
        (1 - C) ^ 2 by
    dsimp [f]
    rw [integral_div, integral_sq_one_sub_exp hint hint2]] at hr
  exact hr

private lemma measureReal_norm_tail_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {s R : ℝ} (hs : 0 < s) (hR : 0 < R)
    (hint : Integrable (fun x : ℝ => Real.exp (-s * x)) μ)
    (hint2 : Integrable (fun x : ℝ => Real.exp (-(2 * s) * x)) μ) :
    μ.real {x : ℝ | R < ‖x‖} ≤ Real.exp (-s * R) * ∫ x, Real.exp (-s * x) ∂μ +
      (1 - 2 * (∫ x, Real.exp (-s * x) ∂μ) + ∫ x, Real.exp (-(2 * s) * x) ∂μ) /
        (1 - Real.exp (-s * R)) ^ 2 := by
  have hsub : {x : ℝ | R < ‖x‖} ⊆ {x : ℝ | x < -R} ∪ {x : ℝ | R < x} := by
    intro x hx
    change R < |x| at hx
    rcases abs_cases x with h | h
    · right
      change R < x
      rwa [h.1] at hx
    · left
      change x < -R
      rw [h.1] at hx
      linarith
  exact (measureReal_mono hsub (measure_ne_top μ _)).trans <|
    (measureReal_union_le _ _).trans <|
      add_le_add (measureReal_lower_tail_le hs hint) (measureReal_upper_tail_le hs hR hint hint2)

private lemma exists_eventual_norm_tail_bound {Λ : ℝ → ℝ} (hΛ0 : Λ 0 = 0)
    (hΛcont : ContinuousWithinAt (fun s => Real.exp (Λ s)) (Set.Ioi 0) 0)
    (P : ℕ → ProbabilityMeasure ℝ)
    (hL : ∀ s : ℝ, 0 < s → Tendsto
      (fun n => ∫ x, Real.exp (-s * x) ∂(P n : Measure ℝ)) atTop
      (𝓝 (Real.exp (Λ s))))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (R : ℝ), 0 < R ∧ ∀ n ≥ N, (P n : Measure ℝ).real {x | R < ‖x‖} ≤ ε := by
  have hmul : Tendsto (fun s : ℝ => 2 * s) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h : Continuous (fun s : ℝ => 2 * s) := by fun_prop
      convert (h.tendsto 0).mono_left nhdsWithin_le_nhds using 1 ; norm_num
    · filter_upwards [self_mem_nhdsWithin] with s hs
      change 0 < 2 * s
      change 0 < s at hs
      positivity
  have hF : Tendsto
      (fun s : ℝ => 1 - 2 * Real.exp (Λ s) + Real.exp (Λ (2 * s)))
      (𝓝[>] 0) (𝓝 0) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub (hΛcont.const_mul 2) |>.add
      ((show Tendsto (fun s => Real.exp (Λ s)) (𝓝[>] 0) (𝓝 (Real.exp (Λ 0))) from hΛcont).comp hmul)
    convert h using 1 <;> simp [hΛ0] ; ring
  have hE : Tendsto (fun s : ℝ => Real.exp (Λ s)) (𝓝[>] 0) (𝓝 1) := by
    have h0 : Real.exp (Λ 0) = 1 := by rw [hΛ0, Real.exp_zero]
    have hc : Tendsto (fun s : ℝ => Real.exp (Λ s)) (𝓝[>] 0) (𝓝 (Real.exp (Λ 0))) := hΛcont
    exact h0 ▸ hc
  have hnear : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s ∧
      |1 - 2 * Real.exp (Λ s) + Real.exp (Λ (2 * s))| < ε / 8 ∧
      1 / 2 < Real.exp (Λ s) ∧ Real.exp (Λ s) < 2 := by
    filter_upwards [self_mem_nhdsWithin,
      hF.eventually (Metric.ball_mem_nhds 0 (by positivity : 0 < ε / 8)),
      hE.eventually (Ioo_mem_nhds (by norm_num : (1 : ℝ) / 2 < 1) (by norm_num : (1 : ℝ) < 2))]
      with s hs hFs hEs
    refine ⟨hs, ?_, hEs⟩
    rw [Real.dist_eq, sub_zero] at hFs
    exact hFs
  obtain ⟨s, hs, hFs, hEs1, hEs2⟩ := hnear.exists
  let F : ℝ → ℝ := fun t => 1 - 2 * Real.exp (Λ t) + Real.exp (Λ (2 * t))
  have hFn : Tendsto (fun n => 1 - 2 * (∫ x, Real.exp (-s * x) ∂(P n : Measure ℝ)) +
      ∫ x, Real.exp (-(2 * s) * x) ∂(P n : Measure ℝ)) atTop (𝓝 (F s)) := by
    exact (tendsto_const_nhds.sub ((hL s hs).const_mul 2)).add (hL (2 * s) (by positivity))
  let L1 : ℕ → ℝ := fun n => ∫ x, Real.exp (-s * x) ∂(P n : Measure ℝ)
  let L2 : ℕ → ℝ := fun n => ∫ x, Real.exp (-(2 * s) * x) ∂(P n : Measure ℝ)
  have hint : ∀ t : ℝ, 0 < t → ∀ᶠ n in atTop,
      Integrable (fun x : ℝ => Real.exp (-t * x)) (P n : Measure ℝ) := by
    intro t ht
    filter_upwards [(hL t ht).eventually_ne (Real.exp_pos _).ne'] with n hn
    by_contra h
    exact hn (integral_undef h)
  have hRlim : Tendsto (fun R : ℝ => Real.exp (-s * R)) atTop (𝓝 0) := by
    simpa [Function.comp_def, neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_const_mul_atTop_of_pos hs).mpr tendsto_id)
  have hδ : 0 < min (1 / 4 : ℝ) (ε / 8) := lt_min (by norm_num) (by positivity)
  obtain ⟨R, hR, hCR⟩ : ∃ R : ℝ, 0 < R ∧ Real.exp (-s * R) < min (1 / 4) (ε / 8) := by
    have hev := (eventually_gt_atTop (0 : ℝ)).and
      (hRlim.eventually (Metric.ball_mem_nhds 0 hδ))
    rcases hev.exists with ⟨R, hR, hC⟩
    exact ⟨R, hR, by simpa [Real.dist_eq, sub_zero, abs_of_pos (Real.exp_pos _)] using hC⟩
  have hn : ∀ᶠ n in atTop, L1 n < 2 ∧
      |1 - 2 * L1 n + L2 n - F s| < ε / 8 := by
    filter_upwards [(hL s hs).eventually (Iio_mem_nhds hEs2),
      hFn.eventually (Metric.ball_mem_nhds (F s) (by positivity : 0 < ε / 8))] with n h1 h2
    exact ⟨h1, by simpa [Real.dist_eq, L1, L2] using h2⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((hint s hs).and ((hint (2 * s) (by positivity)).and hn))
  refine ⟨N, R, hR, fun n hn => ?_⟩
  have hi := hN n hn
  have htail := measureReal_norm_tail_le (μ := (P n : Measure ℝ)) hs hR hi.1 hi.2.1
  have hnum : 0 ≤ 1 - 2 * L1 n + L2 n := by
    rw [show 1 - 2 * L1 n + L2 n = ∫ x, (1 - Real.exp (-s * x)) ^ 2 ∂(P n : Measure ℝ) by
      exact (integral_sq_one_sub_exp hi.1 hi.2.1).symm]
    positivity
  have hnum_lt : 1 - 2 * L1 n + L2 n < ε / 4 := by
    have habs := hi.2.2.2
    rw [abs_lt] at habs
    have hF' : F s < ε / 8 := by
      have h := abs_lt.mp hFs
      exact h.2
    dsimp [F] at hF'
    linarith
  have hden : 1 / 2 ≤ (1 - Real.exp (-s * R)) ^ 2 := by
    have hC : Real.exp (-s * R) < 1 / 4 := lt_of_lt_of_le hCR (min_le_left _ _)
    nlinarith [Real.exp_pos (-s * R)]
  have hdenpos : 0 < (1 - Real.exp (-s * R)) ^ 2 := by nlinarith
  calc
    (P n : Measure ℝ).real {x | R < ‖x‖} ≤
        Real.exp (-s * R) * L1 n + (1 - 2 * L1 n + L2 n) /
          (1 - Real.exp (-s * R)) ^ 2 := htail
    _ ≤ Real.exp (-s * R) * 2 + (1 - 2 * L1 n + L2 n) / (1 / 2) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hi.2.2.1.le (Real.exp_nonneg _)
      · exact div_le_div₀ hnum le_rfl (by norm_num) hden
    _ ≤ ε := by
      have hC : Real.exp (-s * R) < ε / 8 := lt_of_lt_of_le hCR (min_le_right _ _)
      linarith

private lemma isTightMeasureSet_finite_prefix (P : ℕ → ProbabilityMeasure ℝ) (N : ℕ) :
    IsTightMeasureSet ((fun n => (P n : Measure ℝ)) '' {n | n < N}) := by
  induction N with
  | zero =>
      have hsub : ((fun n => (P n : Measure ℝ)) '' {n | n < 0}) ⊆ {(0 : Measure ℝ)} := by
        simp
      exact isTightMeasureSet_singleton.subset hsub
  | succ N ih =>
      apply (ih.union (isTightMeasureSet_singleton (μ := (P N : Measure ℝ)))).subset
      intro μ hμ
      rcases hμ with ⟨n, hn, rfl⟩
      simp only [Set.mem_ofPred_eq, Nat.lt_succ_iff_lt_or_eq] at hn
      rcases hn with hn | rfl
      · exact Or.inl ⟨n, hn, rfl⟩
      · exact Or.inr rfl

theorem isTightMeasureSet_range_of_exponential_laplace_limit
    {Λ : ℝ → ℝ} (hΛ0 : Λ 0 = 0)
    (hΛcont : ContinuousWithinAt (fun s => Real.exp (Λ s)) (Set.Ioi 0) 0)
    (P : ℕ → ProbabilityMeasure ℝ)
    (hL : ∀ s : ℝ, 0 < s → Tendsto
      (fun n => ∫ x, Real.exp (-s * x) ∂(P n : Measure ℝ)) atTop
      (𝓝 (Real.exp (Λ s)))) :
    IsTightMeasureSet (Set.range fun n => (P n : Measure ℝ)) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  by_cases hεtop : ε = ∞
  · subst ε
    exact ⟨∅, isCompact_empty, by simp⟩
  have hεr : 0 < ε.toReal / 2 :=
    half_pos (ENNReal.toReal_pos hε.ne' hεtop)
  have hhalf : ε / 2 = ENNReal.ofReal (ε.toReal / 2) := by
    simp [ENNReal.ofReal_div_of_pos, hεtop]
  have hhalfpos : 0 < ε / 2 := by
    rw [hhalf]
    exact ENNReal.ofReal_pos.mpr hεr
  have hhalfle : ε / 2 ≤ ε := by
    rw [hhalf, ← ENNReal.ofReal_toReal hεtop]
    apply ENNReal.ofReal_le_ofReal
    have hnonneg : 0 ≤ ε.toReal := ENNReal.toReal_nonneg
    rw [ENNReal.toReal_ofReal hnonneg]
    linarith
  obtain ⟨N, R, _hR, htail⟩ := exists_eventual_norm_tail_bound hΛ0 hΛcont P hL hεr
  let S₀ : Set (Measure ℝ) := (fun n => (P n : Measure ℝ)) '' {n | n < N}
  have hS₀ : IsTightMeasureSet S₀ := isTightMeasureSet_finite_prefix P N
  obtain ⟨K, hK, hKμ⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1 hS₀
    (ε / 2) hhalfpos
  refine ⟨K ∪ Metric.closedBall 0 R, hK.union (isCompact_closedBall _ _), ?_⟩
  rintro μ ⟨n, rfl⟩
  have hcomp : (Metric.closedBall (0 : ℝ) R)ᶜ = {x : ℝ | R < ‖x‖} := by
    ext x
    simp [Metric.mem_closedBall, dist_eq_norm]
  by_cases hn : n < N
  · rw [compl_union]
    exact (measure_mono Set.inter_subset_left).trans (hKμ _ ⟨n, hn, rfl⟩ |>.trans hhalfle)
  · have hn' : N ≤ n := Nat.le_of_not_gt hn
    rw [compl_union]
    apply (measure_mono Set.inter_subset_right).trans
    apply le_trans _ hhalfle
    rw [hcomp, ← ENNReal.ofReal_toReal (measure_ne_top (P n : Measure ℝ) _)]
    calc
      ENNReal.ofReal ((P n : Measure ℝ) {x : ℝ | R < ‖x‖}).toReal ≤
          ENNReal.ofReal (ε.toReal / 2) := by
        apply ENNReal.ofReal_le_ofReal
        exact htail n hn'
      _ = ε / 2 := hhalf.symm

/-- Normalization of the cutoff index-one kernel at `s = 1`. -/
theorem stableKernelIntegral_one :
    stableKernelIntegral 1 = Real.eulerMascheroniConstant - 1 := by
  have hlocal : (∫ x in Set.Ioc 0 1, stableKernel 1 x / x ^ 2) =
      -Real.exp (-1) + ∫ x in Set.Ioc 0 1, (1 - Real.exp (-x)) / x := by
    rw [← intervalIntegral.integral_of_le zero_le_one]
    rw [← intervalIntegral.integral_of_le zero_le_one]
    calc
      (∫ x in (0 : ℝ)..1, stableKernel 1 x / x ^ 2) =
          ∫ x in (0 : ℝ)..1, (Real.exp (-x) - 1 + x) / x ^ 2 := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx1 : x ≤ 1 := by
          have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by
            simpa [Set.uIcc_of_le zero_le_one] using hx
          exact hx'.2
        simp [stableKernel, hx1]
      _ = _ := integral_stableKernel_unit_formula
  have htail : (∫ x in Set.Ioi 1, stableKernel 1 x / x ^ 2) =
      (Real.exp (-1) - 1) - ∫ x in Set.Ioi 1, Real.exp (-x) / x := by
    calc
      (∫ x in Set.Ioi 1, stableKernel 1 x / x ^ 2) =
          ∫ x in Set.Ioi 1, (Real.exp (-x) - 1) / x ^ 2 := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        have hx1 : 1 < x := hx
        simp [stableKernel, not_le.mpr hx1]
      _ = _ := integral_stableKernel_tail_formula
  have hA : (∫ x in Set.Ioc 0 1, (1 - Real.exp (-x)) / x) =
      -(∫ x in Set.Ioc 0 1, Real.exp (-x) * Real.log x) := by
    rw [← intervalIntegral.integral_of_le zero_le_one, ← intervalIntegral.integral_of_le zero_le_one]
    exact integral_ein_log_unit_formula
  have hsplit : (∫ x in Set.Ioi 0, stableKernel 1 x / x ^ 2) =
      (∫ x in Set.Ioc 0 1, stableKernel 1 x / x ^ 2) +
        ∫ x in Set.Ioi 1, stableKernel 1 x / x ^ 2 := by
    rw [← intervalIntegral.integral_interval_add_Ioi'
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
        (integrable_stableKernel_unit.congr_fun (fun x hx => by simp [stableKernel, hx.2])
          measurableSet_Ioc))
      (integrableOn_stableKernel_tail.congr_fun (fun x hx => by
        have hx1 : 1 < x := hx
        simp [stableKernel, not_le.mpr hx1]) measurableSet_Ioi)]
    rw [intervalIntegral.integral_of_le zero_le_one]
  have hlogsplit : (∫ x in Set.Ioi 0, Real.exp (-x) * Real.log x) =
      (∫ x in Set.Ioc 0 1, Real.exp (-x) * Real.log x) +
        ∫ x in Set.Ioi 1, Real.exp (-x) * Real.log x := by
    rw [← intervalIntegral.integral_interval_add_Ioi'
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
        (integrableOn_exp_mul_log.mono_set Set.Ioc_subset_Ioi_self))
      integrableOn_exp_mul_log_tail]
    rw [intervalIntegral.integral_of_le zero_le_one]
  rw [stableKernelIntegral, hsplit, hlocal, htail, hA, integral_exp_div_log_tail_formula]
  have heuler := Real.eulerMascheroniConstant_eq_neg_integral_log
  rw [show (∫ t in Set.Ioi 0, Real.log t * Real.exp (-t)) =
      ∫ t in Set.Ioi 0, Real.exp (-t) * Real.log t by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    ring] at heuler
  rw [hlogsplit] at heuler
  linarith

end
end SubcriticalCauchy.Bienayme
