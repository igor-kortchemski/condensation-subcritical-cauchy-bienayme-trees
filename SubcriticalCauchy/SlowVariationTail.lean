module

public import SubcriticalCauchy.CriticalTail
public import SubcriticalCauchy.MeasurableHypothesis

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The integrated slowly varying tail at integer indices

The local offspring asymptotic and finite mean establish summability of the
actual series in the manuscript. The zero-index term is zero by real division,
and no monotonicity of the slowly varying function is assumed.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy

/-- The manuscript's integrated tail, starting at the integer `n`. -/
noncomputable def ellStar (L : ℝ → ℝ) (n : ℕ) : ℝ :=
  tailMass (fun k : ℕ => L k / (k : ℝ)) n

theorem localModel_over_nat_nonneg {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x) (n : ℕ) : 0 ≤ L n / (n : ℝ) := by
  cases n with
  | zero => simp
  | succ n => exact (div_pos (hpos _ (Nat.cast_pos.mpr (Nat.succ_pos _)))
      (Nat.cast_pos.mpr (Nat.succ_pos _))).le

theorem ellStar_pos {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hsum : Summable (fun k : ℕ => L k / (k : ℝ))) {n : ℕ} (hn : 1 ≤ n) :
    0 < ellStar L n := by
  apply tailMass_pos hsum (localModel_over_nat_nonneg hpos) _ hn
  intro k hk
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  exact div_pos (hpos _ hkR) hkR

theorem ellStar_tendsto_zero (L : ℝ → ℝ) :
    Tendsto (ellStar L) atTop (𝓝 0) := tailMass_tendsto_zero _

namespace Bienayme

/-- Finiteness of the integrated tail follows from the actual first moment.
Slow variation and measurability are unnecessary for this comparison. -/
theorem summable_localModel_over_nat
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ ≠ ∞)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1)) :
    Summable (fun k : ℕ => L k / (k : ℝ)) := by
  apply ((summable_offspringMean μ hm).mul_left 2).of_norm_bounded_eventually_nat
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    hlocal.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))] with n hn hr
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hden : 0 < L n / (n : ℝ) ^ 2 := div_pos (hpos _ hnR) (sq_pos_of_pos hnR)
  have hbound : L n / (n : ℝ) ^ 2 ≤ 2 * (μ {n}).toReal := by
    have hmul := (lt_div_iff₀ hden).mp hr
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (localModel_over_nat_nonneg hpos n)]
  calc
    L n / (n : ℝ) = (L n / (n : ℝ) ^ 2) * n := by field_simp
    _ ≤ (2 * (μ {n}).toReal) * n := mul_le_mul_of_nonneg_right hbound hnR.le
    _ = 2 * ((μ {n}).toReal * n) := mul_assoc _ _ _

end Bienayme
end SubcriticalCauchy
