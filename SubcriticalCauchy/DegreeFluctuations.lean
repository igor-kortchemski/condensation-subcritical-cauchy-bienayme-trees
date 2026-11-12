module

public import SubcriticalCauchy.DegreeFluctuationsAux
public import SubcriticalCauchy.SlowVariationRounding
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! # Maximal-degree transfers and the Fréchet extreme-value limit -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators

namespace SubcriticalCauchy.Bienayme

noncomputable section
open BGW BGW.LocallyFinite

local instance degreeFluctuationsMainPlaneTreeMeasurableSpace : MeasurableSpace PlaneTree := ⊤

local instance degreeFluctuationsMainIncrementLawProbability (μ : Measure ℕ)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (incrementLaw μ) := by
  unfold incrementLaw
  infer_instance

/-- The Fréchet distribution function with shape one and scale one. -/
def frechetCDF (u : ℝ) : ℝ := if 0 < u then Real.exp (-1 / u) else 0

/-- If `n * qₙ → t`, then `(1 - qₙ)^(n-1) → exp (-t)`.
The proof applies the standard exponential limit to the shifted sequence. -/
theorem tendsto_one_sub_pow_pred_exp {q : ℕ → ℝ} {t : ℝ}
    (hq : Tendsto (fun n : ℕ => (n : ℝ) * q n) atTop (𝓝 t)) :
    Tendsto (fun n : ℕ => (1 - q n) ^ (n - 1)) atTop (𝓝 (Real.exp (-t))) := by
  have hinv : Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hnratio : Tendsto (fun n : ℕ => (n : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hinv
    have h0 : Tendsto (fun n : ℕ => 1 - 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 1) := by
      simpa using h
    apply h0.congr'
    filter_upwards [] with n
    have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp [hn]
    ring
  have hqShift := hq.comp (tendsto_add_atTop_nat 1)
  have hmul := hqShift.mul hnratio
  have hmul0 : Tendsto (fun n : ℕ =>
      (((n + 1 : ℕ) : ℝ) * q (n + 1)) * ((n : ℝ) / ((n + 1 : ℕ) : ℝ)))
      atTop (𝓝 t) := by
    simpa only [Function.comp_def, mul_one, Nat.cast_add, Nat.cast_one] using hmul
  have hmul' : Tendsto (fun n : ℕ => (n : ℝ) * q (n + 1)) atTop (𝓝 t) := by
    apply hmul0.congr'
    filter_upwards [] with n
    have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp [hn]
  have hneg : Tendsto (fun n : ℕ => (n : ℝ) * (-q (n + 1))) atTop (𝓝 (-t)) := by
    simpa only [mul_neg] using hmul'.neg
  have hp := Real.tendsto_one_add_pow_exp_of_tendsto hneg
  apply (tendsto_add_atTop_iff_nat
    (f := fun n : ℕ => (1 - q n) ^ (n - 1)) 1).mp
  simpa only [Nat.add_sub_cancel, mul_one, sub_eq_add_neg] using hp

/-- Along any scale, the lattice strict upper tail at `u * aₙ` has the Fréchet
normalization `1/u`. -/
theorem nat_mul_incrementTail_floor_tendsto (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) {a : ℕ → ℝ}
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal) atTop (𝓝 1))
    {u : ℝ} (hu : 0 < u) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      (incrementTail μ ((⌊u * a n⌋₊ + 1 : ℕ) : ℝ)).toReal) atTop (𝓝 (1 / u)) := by
  obtain ⟨hm, L, hpos, hsv, hL, hlocal⟩ := hμ
  have hlit : IsSubcriticalCauchyOffspring μ := ⟨hm, L, hpos, hsv, hlocal⟩
  have hscale : Tendsto a atTop atTop := scaling_tendsto_atTop μ hlit ha
  let x : ℕ → ℝ := fun n => ((⌊u * a n⌋₊ + 1 : ℕ) : ℝ)
  let y : ℕ → ℝ := fun n => u * a n
  have hy : Tendsto y atTop atTop := hscale.const_mul_atTop hu
  have hxNat : Tendsto (fun n : ℕ => ⌊u * a n⌋₊ + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp (tendsto_nat_floor_atTop.comp hy)
  have hx : Tendsto x atTop atTop := tendsto_natCast_atTop_atTop.comp hxNat
  have hInvY : Tendsto (fun n : ℕ => 1 / y n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hy
  have hFloorRatio : Tendsto (fun n : ℕ => (⌊y n⌋₊ : ℝ) / y n) atTop (𝓝 1) :=
    tendsto_nat_floor_div_atTop.comp hy
  have hxrel : Tendsto (fun n : ℕ => x n / y n) atTop (𝓝 1) := by
    have h := hFloorRatio.add hInvY
    have h0 : Tendsto (fun n : ℕ => (⌊y n⌋₊ : ℝ) / y n + 1 / y n) atTop (𝓝 1) := by
      simpa using h
    apply h0.congr'
    filter_upwards [hy.eventually_gt_atTop 0] with n hyn
    have hy0 : y n ≠ 0 := hyn.ne'
    dsimp only [x, y]
    push_cast
    field_simp [hy0]
  have hydiv : Tendsto (fun n : ℕ => y n / a n) atTop (𝓝 u) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hscale.eventually_gt_atTop 0] with n han
    dsimp only [y]
    field_simp [han.ne']
  have hxdiv : Tendsto (fun n : ℕ => x n / a n) atTop (𝓝 u) := by
    have h := hxrel.mul hydiv
    have h0 : Tendsto (fun n : ℕ => (x n / y n) * (y n / a n)) atTop (𝓝 u) := by
      simpa only [one_mul] using h
    apply h0.congr'
    filter_upwards [hy.eventually_gt_atTop 0] with n hyn
    field_simp [hyn.ne']
  have hadiv : Tendsto (fun n : ℕ => a n / x n) atTop (𝓝 (1 / u)) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).div hxdiv hu.ne'
    apply h.congr'
    filter_upwards [hscale.eventually_gt_atTop 0, hx.eventually_gt_atTop 0] with n han hxn
    change 1 / (x n / a n) = a n / x n
    field_simp [han.ne', hxn.ne']
  have hLfixed : Tendsto (fun n : ℕ => L (u * a n) / L (a n)) atTop (𝓝 1) :=
    (hsv u hu).comp hscale
  have hLround : Tendsto (fun n : ℕ => L (x n) / L (y n)) atTop (𝓝 1) :=
    slowlyVarying_ratio_of_relative_tendsto_one_filter hpos hL hsv hy hxrel
  have hLratio : Tendsto (fun n : ℕ => L (x n) / L (a n)) atTop (𝓝 1) := by
    have h := hLround.mul hLfixed
    have h0 : Tendsto (fun n : ℕ => (L (x n) / L (y n)) * (L (y n) / L (a n)))
        atTop (𝓝 1) := by
      simpa only [y, one_mul] using h
    apply h0.congr'
    filter_upwards [hy.eventually_gt_atTop 0] with n hyn
    have hLy : L (y n) ≠ 0 := (hpos _ hyn).ne'
    field_simp [hLy]
  have hTx := (incrementTail_div_tendsto_one μ hm hpos hL hsv hlocal).comp hx
  have hTa := (incrementTail_div_tendsto_one μ hm hpos hL hsv hlocal).comp hscale
  have hTaInv : Tendsto (fun n : ℕ =>
      1 / ((incrementTail μ (a n)).toReal / (L (a n) / a n))) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Pi.div_def, one_div, div_one] using
      (tendsto_const_nhds (x := (1 : ℝ))).div hTa one_ne_zero
  have hprod := ((((ha.mul hTx).mul hTaInv).mul hLratio).mul hadiv)
  have hlim : Tendsto (fun n : ℕ =>
      (((((n : ℝ) * (incrementTail μ (a n)).toReal) *
        ((incrementTail μ (x n)).toReal / (L (x n) / x n))) *
        (1 / ((incrementTail μ (a n)).toReal / (L (a n) / a n)))) *
        (L (x n) / L (a n))) * (a n / x n)) atTop (𝓝 (1 / u)) := by
    simpa only [Function.comp_def, one_mul, mul_one] using hprod
  apply hlim.congr'
  filter_upwards [hscale.eventually_gt_atTop 0, hx.eventually_gt_atTop 0] with n han hxn
  have hTa0 : (incrementTail μ (a n)).toReal ≠ 0 :=
    (ENNReal.toReal_pos (incrementTail_pos μ hlit (a n)).ne' (measure_ne_top _ _)).ne'
  have hLa : L (a n) ≠ 0 := (hpos _ han).ne'
  have hLx : L (x n) ≠ 0 := (hpos _ hxn).ne'
  simp only [x] at hxn hLx ⊢
  field_simp [hTa0, hLa, hLx, han.ne', hxn.ne']


/-- U4.2: the maximum of `n - 1` independent increments, normalized by any
scale, converges to the standard Fréchet distribution function. -/
theorem incrementMaximum_le_tendsto_frechet (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) {a : ℕ → ℝ}
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal) atTop (𝓝 1))
    (u : ℝ) :
    Tendsto (fun n : ℕ => (Measure.pi fun _ : Fin (n - 1) => incrementLaw μ).real
      {x | ((incrementMaximum (List.ofFn x) : ℤ) : ℝ) ≤ u * a n}) atTop
      (𝓝 (frechetCDF u)) := by
  have hscale : Tendsto a atTop atTop := scaling_tendsto_atTop μ hμ.to_literal ha
  rcases lt_trichotomy u 0 with hu | hu | hu
  · have hy : Tendsto (fun n : ℕ => u * a n) atTop atBot :=
      hscale.const_mul_atTop_of_neg hu
    have hzero : Tendsto (fun n : ℕ =>
        (Measure.pi fun _ : Fin (n - 1) => incrementLaw μ).real
          {x | ((incrementMaximum (List.ofFn x) : ℤ) : ℝ) ≤ u * a n}) atTop (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [hy.eventually_lt_atBot (-1)] with n hn
      exact (pi_incrementMaximum_eq_zero_of_lt_neg_one μ (n - 1) (u * a n) hn).symm
    simpa [frechetCDF, not_lt_of_ge hu.le] using hzero
  · subst u
    let q : ℝ := (incrementLaw μ).real {z : ℤ | (0 : ℝ) < (z : ℝ)}
    have hqpos : 0 < q := by
      dsimp only [q]
      rw [incrementLaw_real_gt μ 0 le_rfl]
      simpa using ENNReal.toReal_pos (incrementTail_pos μ hμ.to_literal 1).ne'
        (measure_ne_top _ _)
    have hbase0 : 0 ≤ 1 - q := by
      rw [← incrementLaw_real_le μ 0]
      exact measureReal_nonneg
    have hbase1 : 1 - q < 1 := by linarith
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hbase0 hbase1
    have hpred : Tendsto (fun n : ℕ => (1 - q) ^ (n - 1)) atTop (𝓝 0) := by
      apply (tendsto_add_atTop_iff_nat (f := fun n : ℕ => (1 - q) ^ (n - 1)) 1).mp
      simpa only [Nat.add_sub_cancel] using hp
    have hlim : Tendsto (fun n : ℕ =>
        (Measure.pi fun _ : Fin (n - 1) => incrementLaw μ).real
          {x | ((incrementMaximum (List.ofFn x) : ℤ) : ℝ) ≤ 0 * a n}) atTop (𝓝 0) := by
      apply hpred.congr'
      filter_upwards [] with n
      simp only [zero_mul]
      rw [pi_incrementMaximum_le μ (n - 1) 0 le_rfl, incrementLaw_real_le μ 0]
    simpa [frechetCDF] using hlim
  · have hy : Tendsto (fun n : ℕ => u * a n) atTop atTop := hscale.const_mul_atTop hu
    have hq : Tendsto (fun n : ℕ => (n : ℝ) *
        (incrementLaw μ).real {z : ℤ | u * a n < (z : ℝ)}) atTop (𝓝 (1 / u)) := by
      apply (nat_mul_incrementTail_floor_tendsto μ hμ ha hu).congr'
      filter_upwards [hy.eventually_ge_atTop 0] with n hn
      rw [incrementLaw_real_gt μ _ hn]
    have hp := tendsto_one_sub_pow_pred_exp hq
    have hlim : Tendsto (fun n : ℕ =>
        (Measure.pi fun _ : Fin (n - 1) => incrementLaw μ).real
          {x | ((incrementMaximum (List.ofFn x) : ℤ) : ℝ) ≤ u * a n}) atTop
        (𝓝 (Real.exp (-(1 / u)))) := by
      apply hp.congr'
      filter_upwards [hy.eventually_ge_atTop 0] with n hn
      rw [pi_incrementMaximum_le μ (n - 1) (u * a n) hn, incrementLaw_real_le μ (u * a n)]
    simpa [frechetCDF, hu, neg_div] using hlim

/-- Corollary for the second-largest degree: one less than the second maximum
of the conditioned tree has the same Fréchet limit as the independent maximum. -/
theorem conditioned_secondMaxDegree_le_tendsto_frechet (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (hμ : IsMeasurableSubcriticalCauchyOffspring μ) {a : ℕ → ℝ}
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal) atTop (𝓝 1))
    (u : ℝ) :
    Tendsto (fun n : ℕ => (conditionedPlaneTreeLaw μ n).real
      {t | (secondMaxDegree t : ℝ) - 1 ≤ u * a n}) atTop (𝓝 (frechetCDF u)) := by
  let pT : ℕ → ℝ := fun n => (conditionedPlaneTreeLaw μ n).real
    {t | (secondMaxDegree t : ℝ) - 1 ≤ u * a n}
  let pI : ℕ → ℝ := fun n => (Measure.pi fun _ : Fin (n - 1) => incrementLaw μ).real
    {x | ((incrementMaximum (List.ofFn x) : ℤ) : ℝ) ≤ u * a n}
  have htv := conditioned_secondMaxDegree_tvDist μ hμ
  have habs : Tendsto (fun n : ℕ => |pT n - pI n|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun n => abs_nonneg (pT n - pI n)) ?_ htv
    filter_upwards [eventually_size_admissible μ hμ.to_literal] with n hsize
    let _ : IsProbabilityMeasure (conditionedPlaneTreeLaw μ n) :=
      conditionedPlaneTreeLaw_isProbability μ hsize
    let _ :
        IsProbabilityMeasure (conditionedSecondMaxDegreeLaw μ n) := by
      unfold conditionedSecondMaxDegreeLaw
      infer_instance
    let _ : IsProbabilityMeasure (incrementMaximumLaw μ n) := by
      unfold incrementMaximumLaw
      infer_instance
    have hTree : pT n = (conditionedSecondMaxDegreeLaw μ n).real
        {z : ℤ | (z : ℝ) ≤ u * a n} := by
      dsimp only [pT, conditionedSecondMaxDegreeLaw]
      rw [Measure.real, Measure.real,
        Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
      apply congrArg ENNReal.toReal
      apply measure_congr
      apply Eventually.of_forall
      intro t
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Int.cast_sub, Int.cast_natCast,
        Int.cast_one]
    have hIid : pI n = (incrementMaximumLaw μ n).real
        {z : ℤ | (z : ℝ) ≤ u * a n} := by
      dsimp only [pI, incrementMaximumLaw]
      rw [Measure.real, Measure.real,
        Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
      apply congrArg ENNReal.toReal
      rfl
    rw [hTree, hIid]
    exact abs_measureReal_sub_le_tvDist _ _ _
  have hdiff : Tendsto (fun n : ℕ => pT n - pI n) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    exact habs
  have hiid : Tendsto pI atTop (𝓝 (frechetCDF u)) := by
    exact incrementMaximum_le_tendsto_frechet μ hμ ha u
  have h := hdiff.add hiid
  simpa only [pT, sub_add_cancel, zero_add] using h

end
end SubcriticalCauchy.Bienayme
