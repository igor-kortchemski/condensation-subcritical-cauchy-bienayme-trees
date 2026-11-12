module

public import SubcriticalCauchy.BienaymeCorrection
public import SubcriticalCauchy.MeasurableHypothesis
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Tactic

/-!
# Recurrence estimates for the second-order height expansion

This module contains deterministic weighted Cesàro summation and the
normalized-survival form of Lemma 4.4(ii).  It deliberately does not import
any frozen statement file.
-/

@[expose] public section

open MeasureTheory Filter Finset
open scoped ENNReal Topology BigOperators

namespace SubcriticalCauchy.Bienayme

noncomputable section
open BGW BGW.LocallyFinite

/-- The geometrically normalized survival probability `u_n = Q_n / m^n`. -/
noncomputable def normalizedSurvival (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) : ℝ :=
  (survival μ n).toReal / (offspringMean μ).toReal ^ n

/-- Lemma 4.4(ii): the logarithm of the inverse normalized survival
probability is sublinear. -/
theorem log_inv_normalizedSurvival_div_nat (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) :
    Tendsto (fun n : ℕ => Real.log (1 / normalizedSurvival μ n) / (n : ℝ))
      atTop (𝓝 0) := by
  simpa only [normalizedSurvival] using
    survival_log_normalized_inv_div_nat μ (offspringMean_pos_of_paper μ hμ.to_literal) hμ.1

/-- A weighted Cesàro (Stolz) lemma, phrased directly for successive
increments.  The initial value and the ratio limit are both retained. -/
theorem tendsto_sum_weighted_of_tendsto_div_sub {u w : ℕ → ℝ} {A : ℝ}
    (hw : ∀ n, 0 < w n)
    (hwTop : Tendsto (fun n => ∑ k ∈ range n, w k) atTop atTop)
    (h : Tendsto (fun n => (u (n + 1) - u n) / w n) atTop (𝓝 A)) :
    Tendsto (fun n => u n / ∑ k ∈ range n, w k) atTop (𝓝 A) := by
  let e : ℕ → ℝ := fun n => u (n + 1) - u n - A * w n
  have he : e =o[atTop] w := by
    have hr : Tendsto (fun n => (u (n + 1) - u n) / w n - A) atTop (𝓝 0) := by
      simpa using h.sub (tendsto_const_nhds (x := A))
    have ho : (fun n => (u (n + 1) - u n) / w n - A) =o[atTop] fun _ => (1 : ℝ) :=
      (Asymptotics.isLittleO_one_iff ℝ).mpr hr
    have hm := (Asymptotics.isBigO_refl w atTop).mul_isLittleO ho
    apply hm.congr'
    · filter_upwards with n
      change w n * ((u (n + 1) - u n) / w n - A) =
        u (n + 1) - u n - A * w n
      field_simp [(hw n).ne']
    · filter_upwards with n
      simp
  have he' : Tendsto (fun n => (∑ k ∈ range n, e k) /
      (∑ k ∈ range n, w k)) atTop (𝓝 0) :=
    (he.sum_range (fun n => (hw n).le) hwTop).tendsto_div_nhds_zero
  have hinit : Tendsto (fun n : ℕ => u 0 / (∑ k ∈ range n, w k)) atTop (𝓝 0) := by
    exact hwTop.const_div_atTop (u 0)
  have hmain := (hinit.add he').add (tendsto_const_nhds (x := A))
  rw [zero_add, zero_add] at hmain
  apply hmain.congr'
  filter_upwards [hwTop.eventually_ne_atTop 0] with n hn
  have hse : (∑ k ∈ range n, e k) = u n - u 0 - A * ∑ k ∈ range n, w k := by
    have ht : (∑ x ∈ range n, u (x + 1)) - ∑ x ∈ range n, u x = u n - u 0 := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_range_sub u n
    simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum, ht]
  rw [hse]
  field_simp
  ring


/-- The shifted reciprocal partial sums are the real harmonic numbers. -/
theorem sum_inv_succ_eq_harmonic (n : ℕ) :
    (∑ k ∈ range n, ((k : ℝ) + 1)⁻¹) = (harmonic n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, harmonic_succ]
    push_cast
    ring

/-- The harmonic numbers are asymptotic to the natural logarithm. -/
theorem tendsto_harmonic_div_log :
    Tendsto (fun n : ℕ => (harmonic n : ℝ) / Real.log n) atTop (𝓝 1) := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hz : Tendsto (fun n : ℕ => ((harmonic n : ℝ) - Real.log n) / Real.log n)
      atTop (𝓝 0) := Real.tendsto_harmonic_sub_log.div_atTop hlog
  have hh := hz.add (tendsto_const_nhds (x := (1 : ℝ)))
  rw [zero_add] at hh
  apply hh.congr'
  filter_upwards [hlog.eventually_ne_atTop 0] with n hn
  field_simp
  ring

/-- The shifted reciprocal weights have divergent partial sums. -/
theorem tendsto_sum_inv_succ_atTop :
    Tendsto (fun n : ℕ => ∑ k ∈ range n, ((k : ℝ) + 1)⁻¹) atTop atTop := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hprod : Tendsto (fun n : ℕ =>
      ((harmonic n : ℝ) / Real.log n) * Real.log n) atTop atTop :=
    tendsto_harmonic_div_log.pos_mul_atTop zero_lt_one hlog
  apply hprod.congr'
  filter_upwards [hlog.eventually_ne_atTop 0] with n hn
  rw [← sum_inv_succ_eq_harmonic]
  field_simp

/-- `log (1 - x) / x → -1` as `x → 0` away from zero. -/
theorem tendsto_log_one_sub_div_nhdsWithin_zero :
    Tendsto (fun x : ℝ => Real.log (1 - x) / x) (𝓝[≠] 0) (𝓝 (-1)) := by
  have hd : HasDerivAt (fun x : ℝ => Real.log (1 - x)) (-1) 0 := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_log (show (1 : ℝ) - 0 ≠ 0 by norm_num)).comp 0
        ((hasDerivAt_const (x := (0 : ℝ)) 1).sub (hasDerivAt_id 0))
  simpa [div_eq_mul_inv, mul_comm] using hd.tendsto_slope_zero

/-- Partial sums of `(k+1)^(-β)` are asymptotic to
`n^(1-β)/(1-β)` when `0 < β < 1`. -/
theorem tendsto_sum_rpow_neg_div_rpow {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun n : ℕ => (∑ k ∈ range n, ((k : ℝ) + 1) ^ (-β)) /
      (n : ℝ) ^ (1 - β)) atTop (𝓝 (1 / (1 - β))) := by
  let p : ℝ := 1 - β
  have hp : 0 < p := sub_pos.mpr hβ1
  let f : ℝ → ℝ := fun x => (x + 1) ^ (-β)
  let I : ℕ → ℝ := fun n => (((n : ℝ) + 1) ^ p - 1) / p
  have hf (n : ℕ) : AntitoneOn f (Set.Icc (0 : ℝ) (0 + (n : ℝ))) := by
    intro x hx y hy hxy
    simp only [f]
    rw [Real.rpow_neg (add_nonneg hx.1 zero_le_one),
      Real.rpow_neg (add_nonneg hy.1 zero_le_one)]
    apply (inv_le_inv₀
      (Real.rpow_pos_of_pos (add_pos_of_nonneg_of_pos hy.1 zero_lt_one) _)
      (Real.rpow_pos_of_pos (add_pos_of_nonneg_of_pos hx.1 zero_lt_one) _)).2
    exact Real.rpow_le_rpow (add_nonneg hx.1 zero_le_one) (by linarith : x + 1 ≤ y + 1) hβ0.le
  have hIf (n : ℕ) : (∫ x in (0 : ℝ)..(0 + (n : ℝ)), f x) = I n := by
    simp only [f, I, zero_add]
    calc
      (∫ x in (0 : ℝ)..(n : ℝ), (x + 1) ^ (-β)) =
          ∫ x in (0 : ℝ) + 1..(n : ℝ) + 1, x ^ (-β) :=
        intervalIntegral.integral_comp_add_right (fun x : ℝ => x ^ (-β)) 1
      _ = (((n : ℝ) + 1) ^ p - 1) / p := by
        rw [integral_rpow (Or.inl (by linarith : (-1 : ℝ) < -β))]
        rw [show (-β + 1) = p by dsimp [p]; ring]
        norm_num [p]
  have hbounds (n : ℕ) : I n ≤ (∑ k ∈ range n, ((k : ℝ) + 1) ^ (-β)) ∧
      (∑ k ∈ range n, ((k : ℝ) + 1) ^ (-β)) ≤ I n + 1 := by
    have hlo := (hf n).integral_le_sum
    have hhi := (hf n).sum_le_integral
    rw [hIf] at hlo hhi
    constructor
    · simpa only [f, zero_add] using hlo
    · cases n with
      | zero => simp [I]
      | succ n =>
        rw [sum_range_succ']
        simp only [f, zero_add] at hhi ⊢
        rw [sum_range_succ] at hhi
        push_cast at hhi ⊢
        norm_num [f] at ⊢
        have hnonneg : 0 ≤ ((n : ℝ) + 1 + 1) ^ (-β) := Real.rpow_nonneg (by positivity) _
        linarith
  have hbase : Tendsto (fun n : ℕ => (((n : ℝ) + 1) / (n : ℝ))) atTop (𝓝 1) := by
    have hz : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 1
    have hh := (tendsto_const_nhds (x := (1 : ℝ))).add hz
    rw [add_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
    field_simp
  have hratio : Tendsto (fun n : ℕ => (((n : ℝ) + 1) ^ p) / ((n : ℝ) ^ p))
      atTop (𝓝 1) := by
    have hh := hbase.rpow (tendsto_const_nhds (x := p)) (Or.inl one_ne_zero)
    simp only [Real.one_rpow] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    rw [← Real.div_rpow (by positivity) (by positivity)]
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) ^ p)⁻¹) atTop (𝓝 0) := by
    have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ p) atTop atTop :=
      (tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop
    exact ht.inv_tendsto_atTop
  have hI : Tendsto (fun n : ℕ => I n / (n : ℝ) ^ p) atTop (𝓝 (1 / (1 - β))) := by
    have hh := (hratio.sub hinv).div_const p
    rw [sub_zero] at hh
    change Tendsto (fun n : ℕ => I n / (n : ℝ) ^ p) atTop (𝓝 (1 / p))
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hD : (n : ℝ) ^ p ≠ 0 := (Real.rpow_pos_of_pos hn0 _).ne'
    simp only [I]
    field_simp
  have hIupper : Tendsto (fun n : ℕ => (I n + 1) / (n : ℝ) ^ p)
      atTop (𝓝 (1 / (1 - β))) := by
    have hz : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ p) atTop (𝓝 0) := by
      simpa [one_div] using hinv
    have hh := hI.add hz
    rw [add_zero] at hh
    apply hh.congr'
    filter_upwards with n
    rw [add_div]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hI hIupper
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact div_le_div_of_nonneg_right (hbounds n).1
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact div_le_div_of_nonneg_right (hbounds n).2
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)

end
end SubcriticalCauchy.Bienayme
