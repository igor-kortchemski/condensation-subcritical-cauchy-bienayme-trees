module

public import SubcriticalCauchy.CorrectionAsymptotics
public import SubcriticalCauchy.ExampleScales

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Tail asymptotics for Proposition 4.5

This module supplies the explicit slowly varying logarithmic scale used to pass
from the frozen local-tail hypothesis to the survival-correction hypothesis.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section

/-- Logarithms of affine-rescaled large arguments are asymptotic. -/
theorem tendsto_log_mul_add_div_log_add_atTop {a : ℝ} (ha : 0 < a) (b d : ℝ) :
    Tendsto (fun x : ℝ => Real.log (a * x + b) / Real.log (x + d)) atTop (𝓝 1) := by
  have hax : Tendsto (fun x : ℝ => a * x) atTop atTop := tendsto_id.const_mul_atTop ha
  have hxd : Tendsto (fun x : ℝ => x + d) atTop atTop :=
    tendsto_atTop_add_const_right _ d tendsto_id
  have hlogden : Tendsto (fun x : ℝ => Real.log (x + d)) atTop atTop :=
    Real.tendsto_log_atTop.comp hxd
  have h₁ : Tendsto (fun x : ℝ => Real.log (a * x + b) - Real.log (a * x))
      atTop (𝓝 0) := (Real.tendsto_log_comp_add_sub_log b).comp hax
  have h₂ : Tendsto (fun x : ℝ => Real.log (a * x) - Real.log x)
      atTop (𝓝 (Real.log a)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.log_mul ha.ne' hx.ne']
    ring
  have h₃ : Tendsto (fun x : ℝ => Real.log x - Real.log (x + d)) atTop (𝓝 0) := by
    simpa only [neg_sub, neg_zero] using (Real.tendsto_log_comp_add_sub_log d).neg
  have hraw := (h₁.add h₂).add h₃
  have hraw' : Tendsto (fun x : ℝ =>
      (Real.log (a * x + b) - Real.log (a * x)) +
        (Real.log (a * x) - Real.log x) + (Real.log x - Real.log (x + d)))
      atTop (𝓝 (Real.log a)) := by simpa only [zero_add, add_zero] using hraw
  have hsub : Tendsto (fun x : ℝ => Real.log (a * x + b) - Real.log (x + d))
      atTop (𝓝 (Real.log a)) := by
    apply hraw'.congr'
    filter_upwards [] with x
    ring
  have htrend := (tendsto_const_nhds (x := (1 : ℝ))).add (hsub.div_atTop hlogden)
  have hfinal : Tendsto (fun x : ℝ => Real.log (a * x + b) / Real.log (x + d))
      atTop (𝓝 (1 + 0)) := by
    apply htrend.congr'
    filter_upwards [hxd.eventually_gt_atTop 1] with x hx
    have hlog : Real.log (x + d) ≠ 0 := (Real.log_pos hx).ne'
    field_simp [hlog]
    ring
  simpa using hfinal

private noncomputable def p45LogScale (c β x : ℝ) : ℝ :=
  c / Real.log (x + Real.exp 1) ^ (1 + β)

private theorem p45_shiftedLog_pos {x : ℝ} (hx : 0 < x) :
    0 < Real.log (x + Real.exp 1) := by
  apply Real.log_pos
  have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
  linarith

private theorem p45LogScale_pos {c : ℝ} (hc : 0 < c) (β : ℝ)
    {x : ℝ} (hx : 0 < x) : 0 < p45LogScale c β x := by
  exact div_pos hc (Real.rpow_pos_of_pos (p45_shiftedLog_pos hx) _)

private theorem p45LogScale_measurable {c β : ℝ} (hβ : 0 < β) :
    Measurable (p45LogScale c β) := by
  apply Measurable.const_div
  exact (Real.continuous_rpow_const (by linarith : 0 ≤ 1 + β)).measurable.comp
    (Real.measurable_log.comp (measurable_id.add measurable_const))

private theorem p45LogScale_slowlyVarying {c β : ℝ} (hc : 0 < c) :
    IsSlowlyVaryingAtTop (p45LogScale c β) := by
  intro a ha
  have hlog := (tendsto_log_mul_add_div_log_add_atTop ha (Real.exp 1) (Real.exp 1)).inv₀
    one_ne_zero
  have hpow := hlog.rpow_const (p := 1 + β) (Or.inl (inv_ne_zero one_ne_zero))
  have hpow' : Tendsto (fun x : ℝ =>
      (Real.log (a * x + Real.exp 1) / Real.log (x + Real.exp 1))⁻¹ ^ (1 + β))
      atTop (𝓝 1) := by simpa using hpow
  apply hpow'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have h₁ := p45_shiftedLog_pos (mul_pos ha hx)
  have h₂ := p45_shiftedLog_pos hx
  dsimp only [p45LogScale, Pi.inv_apply]
  rw [Real.inv_rpow (by positivity : 0 ≤ Real.log (a * x + Real.exp 1) /
    Real.log (x + Real.exp 1)), Real.div_rpow h₁.le h₂.le]
  field_simp [hc.ne', (Real.rpow_pos_of_pos h₁ (1 + β)).ne',
    (Real.rpow_pos_of_pos h₂ (1 + β)).ne']

private theorem p45LogScale_div_logPower_nat {c β : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => p45LogScale c β n / (c / (Real.log n) ^ (1 + β)))
      atTop (𝓝 1) := by
  have hlog := ((tendsto_log_mul_add_div_log_add_atTop zero_lt_one (Real.exp 1) 0).comp
    tendsto_natCast_atTop_atTop).inv₀ one_ne_zero
  have hpow := hlog.rpow_const (p := 1 + β) (Or.inl (inv_ne_zero one_ne_zero))
  have hpow' : Tendsto (fun n : ℕ =>
      (Real.log (1 * (n : ℝ) + Real.exp 1) / Real.log ((n : ℝ) + 0))⁻¹ ^ (1 + β))
      atTop (𝓝 1) := by simpa using hpow
  apply hpow'.congr'
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
  have hn : (1 : ℝ) < n := by exact_mod_cast hn
  have h₁ : 0 < Real.log ((n : ℝ) + Real.exp 1) :=
    p45_shiftedLog_pos (by linarith)
  have h₂ : 0 < Real.log (n : ℝ) := Real.log_pos hn
  dsimp only [p45LogScale]
  simp only [one_mul, add_zero]
  rw [Real.inv_rpow (div_nonneg h₁.le h₂.le), Real.div_rpow h₁.le h₂.le]
  field_simp [hc.ne', (Real.rpow_pos_of_pos h₁ (1 + β)).ne',
    (Real.rpow_pos_of_pos h₂ (1 + β)).ne']


private theorem p45_local_asymp (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {c β : ℝ} (hc : 0 < c)
    (htail : Tendsto (fun n : ℕ =>
      (μ {n}).toReal / (c / ((n : ℝ) ^ 2 * Real.log n ^ (1 + β)))) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => (μ {n}).toReal / (p45LogScale c β n / (n : ℝ) ^ 2))
      atTop (𝓝 1) := by
  have hmul := htail.mul ((p45LogScale_div_logPower_nat (β := β) hc).inv₀ one_ne_zero)
  have hmul' : Tendsto (fun n : ℕ =>
      ((μ {n}).toReal / (c / ((n : ℝ) ^ 2 * Real.log n ^ (1 + β)))) *
        (p45LogScale c β n / (c / (Real.log n) ^ (1 + β)))⁻¹) atTop (𝓝 1) := by
    simpa only [one_mul, inv_one] using hmul
  apply hmul'.congr'
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h₁ : 0 < Real.log ((n : ℝ) + Real.exp 1) :=
    p45_shiftedLog_pos hn0
  have h₂ : 0 < Real.log (n : ℝ) := Real.log_pos hnR
  dsimp only [p45LogScale]
  field_simp [hc.ne', hn0.ne', (Real.rpow_pos_of_pos h₁ (1 + β)).ne',
    (Real.rpow_pos_of_pos h₂ (1 + β)).ne']

private theorem p45_log_floor_div_log_atTop :
    Tendsto (fun x : ℝ => Real.log (Nat.floor x) / Real.log x) atTop (𝓝 1) := by
  have hratio : Tendsto (fun x : ℝ => ((Nat.floor x : ℕ) : ℝ) / x) atTop (𝓝 1) :=
    tendsto_nat_floor_div_atTop
  have hzero := (hratio.log one_ne_zero).div_atTop Real.tendsto_log_atTop
  have htrend := (tendsto_const_nhds (x := (1 : ℝ))).add hzero
  have hfinal : Tendsto (fun x : ℝ => Real.log (Nat.floor x) / Real.log x)
      atTop (𝓝 (1 + 0)) := by
    apply htrend.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      tendsto_nat_floor_atTop.eventually_gt_atTop 0] with x hx hm
    have hx0 : 0 < x := by linarith
    have hmR : 0 < ((Nat.floor x : ℕ) : ℝ) := Nat.cast_pos.mpr hm
    rw [Real.log_div hmR.ne' hx0.ne']
    have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
    field_simp [hlog]
    ring
  simpa using hfinal


private theorem p45_ellStarReal_asymp {c β : ℝ} (hc : 0 < c) (hβ : 0 < β) :
    Tendsto (fun x : ℝ => ellStarReal (p45LogScale c β) x⁻¹ /
      (c / (β * Real.log x⁻¹ ^ β))) (𝓝[>] 0) (𝓝 1) := by
  have hnat := example23_i_ellStar (fun x hx => p45LogScale_pos hc β hx) hc hβ
    (p45LogScale_div_logPower_nat (β := β) hc)
  have hfloorNat : Tendsto (fun x : ℝ => Nat.floor x⁻¹) (𝓝[>] 0) atTop :=
    tendsto_nat_floor_atTop.comp tendsto_inv_nhdsGT_zero
  have hcomp := hnat.comp hfloorNat
  have hlogratio := (p45_log_floor_div_log_atTop.comp tendsto_inv_nhdsGT_zero).inv₀ one_ne_zero
  have hpow := hlogratio.rpow_const (p := β) (Or.inl (inv_ne_zero one_ne_zero))
  have hmul := hcomp.mul hpow
  have hmul' : Tendsto (fun x : ℝ =>
      (ellStarReal (p45LogScale c β) x⁻¹ /
        (c / (β * Real.log (Nat.floor x⁻¹) ^ β))) *
        (Real.log (Nat.floor x⁻¹) / Real.log x⁻¹)⁻¹ ^ β) (𝓝[>] 0) (𝓝 1) := by
    simpa only [Function.comp_def, ellStarReal, one_mul, Real.one_rpow, inv_one] using hmul
  apply hmul'.congr'
  have hloginv : Tendsto (fun x : ℝ => Real.log x⁻¹) (𝓝[>] 0) atTop :=
    Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  have hfloorReal : Tendsto (fun x : ℝ => ((Nat.floor x⁻¹ : ℕ) : ℝ))
      (𝓝[>] 0) atTop := tendsto_natCast_atTop_atTop.comp hfloorNat
  have hlogfloor : Tendsto (fun x : ℝ => Real.log (Nat.floor x⁻¹)) (𝓝[>] 0) atTop :=
    Real.tendsto_log_atTop.comp hfloorReal
  filter_upwards [hloginv.eventually_gt_atTop 0,
    hlogfloor.eventually_gt_atTop 0] with x hx hf
  rw [Real.inv_rpow (div_nonneg hf.le hx.le), Real.div_rpow hf.le hx.le]
  field_simp [hc.ne', hβ.ne', (Real.rpow_pos_of_pos hf β).ne',
    (Real.rpow_pos_of_pos hx β).ne']


/-- The survival-correction asymptotic implied by the logarithmic-power tail. -/
theorem survivalCorrection_asymp_of_tail (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) {c β : ℝ} (hc : 0 < c) (hβ : 0 < β)
    (htail : Tendsto (fun n : ℕ =>
      (μ {n}).toReal / (c / ((n : ℝ) ^ 2 * Real.log n ^ (1 + β)))) atTop (𝓝 1)) :
    Tendsto (fun x : ℝ => survivalCorrection μ x /
      (c / (β * Real.log x⁻¹ ^ β))) (𝓝[>] 0) (𝓝 1) := by
  have hcorr := survivalCorrection_div_ellStarReal_tendsto_one μ hμ.1
    (fun x hx => p45LogScale_pos hc β hx) (p45LogScale_measurable hβ).aemeasurable
    (p45LogScale_slowlyVarying (β := β) hc) (p45_local_asymp μ hc htail)
  have hell := p45_ellStarReal_asymp hc hβ
  have hmul := hcorr.mul hell
  have hmul' : Tendsto (fun x : ℝ =>
      (survivalCorrection μ x / ellStarReal (p45LogScale c β) x⁻¹) *
        (ellStarReal (p45LogScale c β) x⁻¹ / (c / (β * Real.log x⁻¹ ^ β))))
      (𝓝[>] 0) (𝓝 1) := by simpa only [one_mul] using hmul
  apply hmul'.congr'
  have hloginv : Tendsto (fun x : ℝ => Real.log x⁻¹) (𝓝[>] 0) atTop :=
    Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  have hmodel : ∀ᶠ x : ℝ in 𝓝[>] 0, 0 < c / (β * Real.log x⁻¹ ^ β) := by
    filter_upwards [hloginv.eventually_gt_atTop 0] with x hx
    exact div_pos hc (mul_pos hβ (Real.rpow_pos_of_pos hx β))
  have hratio : ∀ᶠ x : ℝ in 𝓝[>] 0,
      0 < ellStarReal (p45LogScale c β) x⁻¹ / (c / (β * Real.log x⁻¹ ^ β)) :=
    hell.eventually (lt_mem_nhds zero_lt_one)
  filter_upwards [hmodel, hratio] with x hm hr
  have he : ellStarReal (p45LogScale c β) x⁻¹ ≠ 0 :=
    ((div_pos_iff_of_pos_right hm).mp hr).ne'
  field_simp [he, hm.ne']

end
end SubcriticalCauchy.Bienayme
