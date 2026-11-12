module

public import SubcriticalCauchy.LocalMassVariation

import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Uniform local offspring window comparisons

Relative perturbation limits for actual offspring unit-window probabilities
are uniform over all bases above a diverging lower bound. This supplies the
local mass-ratio inputs used in the one-big-jump application, without assuming
or proving the external local-deviation theorem for sums.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy

/-- A sequential relative-perturbation criterion yields uniformity on shrinking
relative windows, even over unbounded sets of basepoints. -/
theorem uniform_relative_tail_of_sequential {F : ℝ → ℝ}
    (hseq : ∀ {x y : ℕ → ℝ}, Tendsto x atTop atTop → Tendsto y atTop atTop →
      Tendsto (fun n => y n / x n) atTop (𝓝 1) →
      Tendsto (fun n => F (y n) / F (x n)) atTop (𝓝 1))
    {z d : ℕ → ℝ} (hz : Tendsto z atTop atTop) (hd : Tendsto d atTop (𝓝 0)) :
    ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ x y : ℝ,
      z n ≤ x → |y / x - 1| ≤ |d n| → |F y / F x - 1| < τ := by
  classical
  intro τ hτ
  by_contra hnot
  have hbad (N : ℕ) : ∃ (n : ℕ) (x y : ℝ),
      N ≤ n ∧ z n ≤ x ∧ |y / x - 1| ≤ |d n| ∧ τ ≤ |F y / F x - 1| := by
    by_contra hnone
    apply hnot
    refine eventually_atTop.mpr ⟨N, ?_⟩
    intro n hn x y hbase hrel
    by_contra herr
    exact hnone ⟨n, x, y, hn, hbase, hrel, le_of_not_gt herr⟩
  choose ns xs ys hN hbase hrel herr using hbad
  have hns : Tendsto ns atTop atTop := tendsto_atTop_mono hN tendsto_id
  have hxs : Tendsto xs atTop atTop := tendsto_atTop_mono hbase (hz.comp hns)
  have herror : Tendsto (fun n => |ys n / xs n - 1|) atTop (𝓝 0) :=
    squeeze_zero (fun _ => abs_nonneg _) hrel
      (by simpa only [abs_zero, Function.comp_def] using (hd.comp hns).abs)
  have hcoef : Tendsto (fun n => ys n / xs n) atTop (𝓝 1) :=
    tendsto_iff_dist_tendsto_zero.mpr (by simpa only [Real.dist_eq] using herror)
  have hys : Tendsto ys atTop atTop := by
    apply (hxs.atTop_mul_pos zero_lt_one hcoef).congr'
    filter_upwards [hxs.eventually_gt_atTop 0] with n hn
    field_simp
  have hratio := hseq hxs hys hcoef
  have hzero : Tendsto (fun n => |F (ys n) / F (xs n) - 1|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero] using (hratio.sub_const 1).abs
  obtain ⟨n, hn⟩ := (hzero.eventually (gt_mem_nhds hτ)).exists
  exact (not_lt_of_ge (herr n)) hn

namespace Bienayme

theorem incrementUnitWindow_eventually_pos
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hμ : IsSubcriticalCauchyOffspring μ) :
    ∀ᶠ x : ℝ in atTop, 0 < incrementUnitWindow μ x := by
  have hindex : Tendsto (fun x : ℝ => Nat.floor x + 2) atTop atTop :=
    tendsto_atTop_mono (fun x => Nat.le_add_right (Nat.floor x) 2) tendsto_nat_floor_atTop
  filter_upwards [hindex.eventually (eventually_mass_pos μ hμ), eventually_ge_atTop (0 : ℝ)]
    with x hmass hx
  rw [incrementUnitWindow_eq_mass_floor μ hx]
  exact hmass

theorem paper_unitWindow_uniform_relative_tail
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ)
    {z d : ℕ → ℝ} (hz : Tendsto z atTop atTop) (hd : Tendsto d atTop (𝓝 0)) :
    ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ x y : ℝ,
      z n ≤ x → |y / x - 1| ≤ |d n| →
        |(incrementUnitWindow μ y).toReal / (incrementUnitWindow μ x).toReal - 1| < τ :=
  uniform_relative_tail_of_sequential
    (fun hx hy hr => paper_unitWindow_ratio_of_relative_tendsto_one μ hμ hx hy hr) hz hd

theorem paper_unitWindow_uniform_additive_window
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ)
    {ε : ℝ} (hε : 0 < ε) {η : ℕ → ℝ}
    (hη : Tendsto (fun n : ℕ => η n / (n : ℝ)) atTop (𝓝 0)) :
    ∀ τ : ℝ, 0 < τ → ∀ᶠ n : ℕ in atTop, ∀ x u : ℝ,
      ε * n ≤ x → |u| ≤ |η n| →
        |(incrementUnitWindow μ (x + u)).toReal / (incrementUnitWindow μ x).toReal - 1| < τ := by
  intro τ hτ
  have hz : Tendsto (fun n : ℕ => ε * (n : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hε
  have hsmall : Tendsto (fun n : ℕ => (η n / (n : ℝ)) / ε) atTop (𝓝 0) := by
    simpa only [zero_div] using hη.div_const ε
  have hUC := paper_unitWindow_uniform_relative_tail μ hμ hz hsmall τ hτ
  filter_upwards [hUC, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  intro x u hbase hu
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hnpos
  have hxp : 0 < x := (mul_pos hε hnR).trans_le hbase
  apply hn x (x + u) hbase
  have hrel : (x + u) / x - 1 = u / x := by
    rw [add_div, div_self hxp.ne']
    ring
  rw [hrel, abs_div, abs_of_pos hxp]
  calc
    |u| / x ≤ |η n| / x := div_le_div_of_nonneg_right hu hxp.le
    _ ≤ |η n| / (ε * (n : ℝ)) :=
      div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos hε hnR) hbase
    _ = |(η n / (n : ℝ)) / ε| := by
      rw [abs_div, abs_div, abs_of_pos hnR, abs_of_pos hε, div_div,
        mul_comm (n : ℝ) ε]

/-- The actual unit-window probability after adding a fixed drift correction. -/
def centeredIncrementUnitWindow (μ : Measure ℕ) (γ x : ℝ) : ℝ≥0∞ :=
  μ {k : ℕ | x < (k : ℝ) - 1 + γ ∧ (k : ℝ) - 1 + γ ≤ x + 1}

theorem centeredIncrementUnitWindow_eq (μ : Measure ℕ) (γ x : ℝ) :
    centeredIncrementUnitWindow μ γ x = incrementUnitWindow μ (x - γ) := by
  unfold centeredIncrementUnitWindow incrementUnitWindow
  congr 1
  ext k
  simp only [Set.mem_ofPred_eq]
  constructor <;> rintro ⟨hlo, hhi⟩ <;> constructor <;> linarith

/-- The same uniform comparison holds for the actual centered increments. -/
theorem paper_centeredUnitWindow_uniform_additive_window
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (γ : ℝ)
    {ε : ℝ} (hε : 0 < ε) {η : ℕ → ℝ}
    (hη : Tendsto (fun n : ℕ => η n / (n : ℝ)) atTop (𝓝 0)) :
    ∀ τ : ℝ, 0 < τ → ∀ᶠ n : ℕ in atTop, ∀ x u : ℝ,
      ε * n ≤ x → |u| ≤ |η n| →
        |(centeredIncrementUnitWindow μ γ (x + u)).toReal /
          (centeredIncrementUnitWindow μ γ x).toReal - 1| < τ := by
  intro τ hτ
  have hγ : ∀ᶠ n : ℕ in atTop, γ ≤ (ε / 2) * n :=
    ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (half_pos hε)).eventually_ge_atTop γ
  filter_upwards [paper_unitWindow_uniform_additive_window μ hμ (half_pos hε) hη τ hτ, hγ]
    with n hn hγn x u hx hu
  rw [centeredIncrementUnitWindow_eq, centeredIncrementUnitWindow_eq]
  have hbase : (ε / 2) * (n : ℝ) ≤ x - γ := by linarith
  have harg : x + u - γ = x - γ + u := by ring
  rw [harg]
  exact hn (x - γ) u hbase hu

end Bienayme
end SubcriticalCauchy
