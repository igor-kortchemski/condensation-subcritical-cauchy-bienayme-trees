module

public import SubcriticalCauchy.CorrectionKernel
public import SubcriticalCauchy.FirstMomentTail

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Cutoff bounds for the actual survival correction

The correction is split into a finite prefix and a genuine summable tail.
The quadratic kernel bound controls its prefix, while the kernel's linear
lower bound captures the first moment beyond a large cutoff. These estimates
do not assume any slowly varying asymptotic.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace SubcriticalCauchy.Bienayme

/-- The actual summable correction series split at an arbitrary integer
cutoff, with its endpoint included in the tail. -/
theorem survivalCorrection_eq_prefix_add_tailMass
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ ≠ ∞)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ) :
    survivalCorrection μ q =
      (∑ k ∈ Finset.range N, (μ {k}).toReal * correctionKernel q k) +
        tailMass (fun k : ℕ => (μ {k}).toReal * correctionKernel q k) N := by
  calc
    survivalCorrection μ q =
        tailMass (fun k : ℕ => (μ {k}).toReal * correctionKernel q k) 0 := by
      rw [survivalCorrection_eq_tsum_massKernel μ hm hq0 hq1]
      simp only [tailMass, Nat.zero_add]
    _ = _ := by
      simpa only [Nat.zero_add] using
        tailMass_split (summable_correctionKernel_mass μ hm hq0 hq1) 0 N

/-- Below the cutoff the kernel is bounded quadratically; above it, the
correction is bounded by the actual first-moment tail. -/
theorem survivalCorrection_upper_cutoff
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ ≠ ∞)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ) :
    survivalCorrection μ q ≤ firstMomentTail μ N +
      q * ∑ k ∈ Finset.range N, (k : ℝ) * ((μ {k}).toReal * (k : ℝ)) := by
  have hprefix :
      (∑ k ∈ Finset.range N, (μ {k}).toReal * correctionKernel q k) ≤
        q * ∑ k ∈ Finset.range N, (k : ℝ) * ((μ {k}).toReal * (k : ℝ)) := by
    calc
      _ ≤ ∑ k ∈ Finset.range N,
          q * ((k : ℝ) * ((μ {k}).toReal * (k : ℝ))) := by
        apply Finset.sum_le_sum
        intro k _
        calc
          _ ≤ (μ {k}).toReal * (q * (k : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left (correctionKernel_le_mul_sq hq0 hq1 k)
              ENNReal.toReal_nonneg
          _ = _ := by ring
      _ = _ := by rw [Finset.mul_sum]
  have htail :
      tailMass (fun k : ℕ => (μ {k}).toReal * correctionKernel q k) N ≤
        firstMomentTail μ N := by
    apply (summable_tailMass (summable_correctionKernel_mass μ hm hq0 hq1) N).tsum_le_tsum
      _ (summable_tailMass (summable_offspringMean μ hm) N)
    intro j
    exact mul_le_mul_of_nonneg_left (correctionKernel_bounds hq0 hq1 (N + j)).2
      ENNReal.toReal_nonneg
  rw [survivalCorrection_eq_prefix_add_tailMass μ hm hq0 hq1 N]
  linarith

/-- When the cutoff is at least `M / q`, the entire first-moment tail beyond
it contributes at least the fraction `1 - 1/M` to the correction. -/
theorem survivalCorrection_lower_cutoff
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ ≠ ∞)
    {q M : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) (hM : 1 < M)
    (N : ℕ) (hcut : M / q ≤ (N : ℝ)) :
    (1 - 1 / M) * firstMomentTail μ N ≤ survivalCorrection μ q := by
  have hM0 : 0 < M := zero_lt_one.trans hM
  have hkernel (k : ℕ) (hnk : N ≤ k) :
      (1 - 1 / M) * (k : ℝ) ≤ correctionKernel q k := by
    have hNq : M ≤ (N : ℝ) * q := (div_le_iff₀ hq0).mp hcut
    have hNk : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hnk
    have hMk : M ≤ (k : ℝ) * q :=
      hNq.trans (mul_le_mul_of_nonneg_right hNk hq0.le)
    have hinv : 1 / q ≤ (k : ℝ) / M :=
      (div_le_div_iff₀ hq0 hM0).mpr (by simpa only [one_mul] using hMk)
    calc
      (1 - 1 / M) * (k : ℝ) = (k : ℝ) - (k : ℝ) / M := by ring
      _ ≤ (k : ℝ) - 1 / q := sub_le_sub_left hinv (k : ℝ)
      _ ≤ correctionKernel q k := correctionKernel_ge_sub_inv hq0 hq1 k
  have hbound := tailMass_mul_bounds (summable_offspringMean μ hm)
    (summable_correctionKernel_mass μ hm hq0.le hq1)
    (n := N) (a := 1 - 1 / M) (b := 1)
    (fun k hnk => show (1 - 1 / M) * ((μ {k}).toReal * (k : ℝ)) ≤
        (μ {k}).toReal * correctionKernel q k from by
      calc
        _ = (μ {k}).toReal * ((1 - 1 / M) * (k : ℝ)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hkernel k hnk) ENNReal.toReal_nonneg)
    (fun k _ => by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_left (correctionKernel_bounds hq0.le hq1 k).2
          ENNReal.toReal_nonneg)
  have hprefix : 0 ≤
      ∑ k ∈ Finset.range N, (μ {k}).toReal * correctionKernel q k :=
    Finset.sum_nonneg (fun k _ =>
      mul_nonneg ENNReal.toReal_nonneg (correctionKernel_bounds hq0.le hq1 k).1)
  have htail : (1 - 1 / M) * firstMomentTail μ N ≤
      tailMass (fun k : ℕ => (μ {k}).toReal * correctionKernel q k) N := hbound.1
  rw [survivalCorrection_eq_prefix_add_tailMass μ hm hq0.le hq1 N]
  linarith

end SubcriticalCauchy.Bienayme
