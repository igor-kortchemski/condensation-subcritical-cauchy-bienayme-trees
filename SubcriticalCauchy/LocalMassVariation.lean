module

public import SubcriticalCauchy.MeasurableHypothesis
public import SubcriticalCauchy.MultiplicativeUniformSlowVariation
public import Mathlib.Analysis.SpecificLimits.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Relative perturbations of the actual offspring masses

Uniform slow variation and the local offspring asymptotic imply asymptotically
equal singleton masses at integer indices whose ratio tends to one. This is a
regular-variation input to the local window comparisons, not a local limit
theorem for sums or a one-big-jump estimate.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

theorem paper_mass_ratio_of_relative_tendsto_one
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ)
    {j k : ℕ → ℕ} (hj : Tendsto j atTop atTop) (hk : Tendsto k atTop atTop)
    (hr : Tendsto (fun n => (k n : ℝ) / (j n : ℝ)) atTop (𝓝 1)) :
    Tendsto (fun n => (μ {k n}).toReal / (μ {j n}).toReal) atTop (𝓝 1) := by
  obtain ⟨hm, L, hpos, hsv, hmeas, hlocal⟩ := hμ
  have hjR : Tendsto (fun n => (j n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hj
  have hkR : Tendsto (fun n => (k n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hk
  have hLrat : Tendsto (fun n => L (k n) / L (j n)) atTop (𝓝 1) := by
    have h := slowlyVarying_uniform_sequential hpos hmeas hsv hjR hr zero_lt_one
    apply h.congr'
    filter_upwards [hjR.eventually_gt_atTop 0] with n hn
    rw [div_mul_cancel₀ _ hn.ne']
  have hratio := (hlocal.comp hk).div (hlocal.comp hj) one_ne_zero
  have hinv := ((tendsto_const_nhds (x := (1 : ℝ))).div hr one_ne_zero).pow 2
  have htotal := (hratio.mul hLrat).mul hinv
  have heq : (fun n =>
      ((μ {k n}).toReal / (L (k n) / (k n : ℝ) ^ 2)) /
        ((μ {j n}).toReal / (L (j n) / (j n : ℝ) ^ 2)) *
          (L (k n) / L (j n)) * (1 / ((k n : ℝ) / (j n : ℝ))) ^ 2) =ᶠ[atTop]
      (fun n => (μ {k n}).toReal / (μ {j n}).toReal) := by
    filter_upwards [hjR.eventually_gt_atTop 0,
      hkR.eventually_gt_atTop 0,
      (hlocal.comp hj).eventually (lt_mem_nhds zero_lt_one)] with n hjn hkn hmass
    have hLjn := (hpos _ hjn).ne'
    have hLkn := (hpos _ hkn).ne'
    have hμjn : (μ {j n}).toReal ≠ 0 := by
      have hden : 0 < L (j n) / (j n : ℝ) ^ 2 :=
        div_pos (hpos _ hjn) (sq_pos_of_pos hjn)
      exact ((div_pos_iff_of_pos_right hden).mp hmass).ne'
    field_simp [hμjn, hLjn, hLkn, hjn.ne', hkn.ne']
  simpa only [one_div, div_one, one_mul, one_pow] using htotal.congr' heq

/-- The actual open-left, closed-right unit window for the increment `K-1`. -/
def incrementUnitWindow (μ : Measure ℕ) (x : ℝ) : ℝ≥0∞ :=
  μ {k : ℕ | x < (k : ℝ) - 1 ∧ (k : ℝ) - 1 ≤ x + 1}

theorem incrementUnitWindow_eq_mass_floor (μ : Measure ℕ) {x : ℝ} (hx : 0 ≤ x) :
    incrementUnitWindow μ x = μ {Nat.floor x + 2} := by
  unfold incrementUnitWindow
  congr 1
  ext k
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hlo, hhi⟩
    have h1 : ((Nat.floor x + 1 : ℕ) : ℝ) < (k : ℝ) := by
      push_cast
      linarith [Nat.floor_le hx]
    have h2 : (k : ℝ) < ((Nat.floor x + 3 : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.lt_floor_add_one x]
    have h1N : Nat.floor x + 1 < k := by exact_mod_cast h1
    have h2N : k < Nat.floor x + 3 := by exact_mod_cast h2
    omega
  · rintro rfl
    push_cast
    constructor <;> linarith [Nat.floor_le hx, Nat.lt_floor_add_one x]

theorem floor_add_two_div_tendsto {x : ℕ → ℝ} (hx : Tendsto x atTop atTop) :
    Tendsto (fun n => ((Nat.floor (x n) + 2 : ℕ) : ℝ) / x n) atTop (𝓝 1) := by
  have hfloor := tendsto_nat_floor_div_atTop.comp hx
  have htwo : Tendsto (fun n => (2 : ℝ) / x n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hx
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat, add_div, add_zero]
    using hfloor.add htwo

/-- Unit windows retain the singleton ratio under relatively vanishing shifts. -/
theorem paper_unitWindow_ratio_of_relative_tendsto_one
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ)
    {x y : ℕ → ℝ} (hx : Tendsto x atTop atTop) (hy : Tendsto y atTop atTop)
    (hr : Tendsto (fun n => y n / x n) atTop (𝓝 1)) :
    Tendsto (fun n => (incrementUnitWindow μ (y n)).toReal /
      (incrementUnitWindow μ (x n)).toReal) atTop (𝓝 1) := by
  let j (n : ℕ) := Nat.floor (x n) + 2
  let k (n : ℕ) := Nat.floor (y n) + 2
  have hj : Tendsto j atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right (Nat.floor (x n)) 2)
      (tendsto_nat_floor_atTop.comp hx)
  have hk : Tendsto k atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right (Nat.floor (y n)) 2)
      (tendsto_nat_floor_atTop.comp hy)
  have hindex : Tendsto (fun n => (k n : ℝ) / (j n : ℝ)) atTop (𝓝 1) := by
    have h := ((floor_add_two_div_tendsto hy).mul hr).div
      (floor_add_two_div_tendsto hx) one_ne_zero
    have heq : (fun n => (((k n : ℝ) / y n) * (y n / x n)) /
        ((j n : ℝ) / x n)) =ᶠ[atTop] (fun n => (k n : ℝ) / (j n : ℝ)) := by
      filter_upwards [hx.eventually_gt_atTop 0, hy.eventually_gt_atTop 0] with n hxn hyn
      have hjn : (j n : ℝ) ≠ 0 := by dsimp only [j]; positivity
      field_simp [hxn.ne', hyn.ne', hjn]
    simpa only [one_mul, div_one] using h.congr' heq
  have hmasses := paper_mass_ratio_of_relative_tendsto_one μ hμ hj hk hindex
  apply hmasses.congr'
  filter_upwards [hx.eventually_ge_atTop 0, hy.eventually_ge_atTop 0] with n hxn hyn
  rw [incrementUnitWindow_eq_mass_floor μ hxn, incrementUnitWindow_eq_mass_floor μ hyn]


end SubcriticalCauchy.Bienayme
