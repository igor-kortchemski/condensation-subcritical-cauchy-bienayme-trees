module

public import SubcriticalCauchy.BienaymeCorrection
public import Mathlib.Algebra.Order.Ring.Pow

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The finite geometric kernel of the survival correction

Exact mass-series representation and elementary bounds for the actual
correction. These estimates precede the slowly varying tail comparison; no
Abelian asymptotic is assumed here.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

def correctionKernel (q : ℝ) (k : ℕ) : ℝ :=
  (k : ℝ) - ∑ j ∈ Finset.range k, (1 - q) ^ j

theorem correctionKernel_eq_sum (q : ℝ) (k : ℕ) :
    correctionKernel q k = ∑ j ∈ Finset.range k, (1 - (1 - q) ^ j) := by
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, correctionKernel]

theorem correctionKernel_bounds {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (k : ℕ) :
    0 ≤ correctionKernel q k ∧ correctionKernel q k ≤ (k : ℝ) := by
  have hsum0 : 0 ≤ ∑ j ∈ Finset.range k, (1 - q) ^ j :=
    Finset.sum_nonneg (fun _ _ => pow_nonneg (sub_nonneg.mpr hq1) _)
  have hsum1 : (∑ j ∈ Finset.range k, (1 - q) ^ j) ≤ (k : ℝ) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range k, (1 : ℝ) :=
        Finset.sum_le_sum (fun _ _ => pow_le_one₀ (sub_nonneg.mpr hq1) (by linarith))
      _ = k := by simp
  dsimp only [correctionKernel]
  constructor <;> linarith

theorem correctionKernel_le_mul_sq {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (k : ℕ) :
    correctionKernel q k ≤ q * (k : ℝ) ^ 2 := by
  rw [correctionKernel_eq_sum]
  calc
    _ ≤ ∑ _j ∈ Finset.range k, q * (k : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      have hber := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ -q) j
      have hjR : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Finset.mem_range.mp hj).le
      have hmul := mul_le_mul_of_nonneg_left hjR hq0
      simp only [← sub_eq_add_neg] at hber
      nlinarith
    _ = q * (k : ℝ) ^ 2 := by simp; ring

theorem correctionKernel_ge_sub_inv {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) (k : ℕ) :
    (k : ℝ) - 1 / q ≤ correctionKernel q k := by
  have hgeom := geom_sum_mul_neg (1 - q) k
  simp only [sub_sub_cancel] at hgeom
  have hp : 0 ≤ (1 - q) ^ k := pow_nonneg (sub_nonneg.mpr hq1) _
  have hsum : (∑ j ∈ Finset.range k, (1 - q) ^ j) ≤ 1 / q := by
    apply (le_div_iff₀ hq0).mpr
    linarith
  dsimp only [correctionKernel]
  linarith

theorem summable_correctionKernel_mass (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Summable (fun k : ℕ => (μ {k}).toReal * correctionKernel q k) :=
  (summable_offspringMean μ hm).of_nonneg_of_le
    (fun k => mul_nonneg ENNReal.toReal_nonneg (correctionKernel_bounds hq0 hq1 k).1)
    (fun k => mul_le_mul_of_nonneg_left (correctionKernel_bounds hq0 hq1 k).2
      ENNReal.toReal_nonneg)

theorem survivalCorrection_eq_tsum_massKernel (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    survivalCorrection μ q = ∑' k : ℕ, (μ {k}).toReal * correctionKernel q k := by
  calc
    survivalCorrection μ q = (∑' k : ℕ, (μ {k}).toReal * (k : ℝ)) -
        ∑' k : ℕ, (μ {k}).toReal * ∑ j ∈ Finset.range k, (1 - q) ^ j := by
      rw [survivalCorrection, offspringMean_eq_tsum, offspringSlope]
    _ = ∑' k : ℕ, ((μ {k}).toReal * (k : ℝ) -
        (μ {k}).toReal * ∑ j ∈ Finset.range k, (1 - q) ^ j) :=
      ((summable_offspringMean μ hm).tsum_sub (summable_offspringSlope μ hm q hq0 hq1)).symm
    _ = _ := by
      apply tsum_congr
      intro k
      dsimp only [correctionKernel]
      ring

end SubcriticalCauchy.Bienayme
