module

public import SubcriticalCauchy.Centering
public import SubcriticalCauchy.CriticalTail
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
Exact series representation of the signed increment tail. The cutoff
is the source's absolute cutoff. At thresholds at least one its negative
offspring-zero increment is excluded, and strictness gives floor(x)+2.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Signed first-moment mass of the actual increment `K-1`. The term at zero
is negative; it is retained in the summable sequence. -/
def weightedIncrementMass (μ : Measure ℕ) (k : ℕ) : ℝ :=
  (μ {k}).toReal * ((k : ℝ) - 1)

theorem summable_weightedIncrementMass (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) : Summable (weightedIncrementMass μ) := by
  have hp : Summable (fun k : ℕ => (μ {k}).toReal) := by
    simpa using summable_pgfReal μ 1 zero_le_one le_rfl
  apply ((summable_offspringMean μ hm).sub hp).congr
  intro k
  change (μ {k}).toReal * (k : ℝ) - (μ {k}).toReal =
    (μ {k}).toReal * ((k : ℝ) - 1)
  ring

/-- For `x≥1`, no negative increment passes the absolute tail cutoff.
The threshold is strict, including when `x` is an integer. -/
theorem abs_increment_gt_iff_floor_add_two_le {x : ℝ} (hx : 1 ≤ x) (k : ℕ) :
    x < |offspringIncrement k| ↔ ⌊x⌋₊ + 2 ≤ k := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  cases k with
  | zero => simp [offspringIncrement, not_lt.mpr hx]
  | succ k =>
    have hi : offspringIncrement (k + 1) = (k : ℝ) := by simp [offspringIncrement]
    rw [hi, abs_of_nonneg (Nat.cast_nonneg k), ← Nat.floor_lt hx0]
    omega

theorem tsum_ite_ge_eq_tailMass {V : ℕ → ℝ} (hV : Summable V) (N : ℕ) :
    (∑' k : ℕ, if N ≤ k then V k else 0) = tailMass V N := by
  let g (k : ℕ) := if N ≤ k then V k else 0
  have hg : Summable g := (hV.norm).of_norm_bounded (fun k => by
    by_cases hk : N ≤ k <;> simp [g, hk])
  have h := hg.sum_add_tsum_nat_add N
  have hzero : (∑ k ∈ Finset.range N, g k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp [g, not_le.mpr (Finset.mem_range.mp hk)]
  have htail : (∑' j : ℕ, g (j + N)) = tailMass V N := by
    change (∑' j : ℕ, g (j + N)) = ∑' j : ℕ, V (N + j)
    apply tsum_congr
    intro j
    change (if N ≤ j + N then V (j + N) else 0) = V (N + j)
    rw [ite_eq_left (Nat.le_add_left N j), Nat.add_comm]
  rw [hzero, zero_add, htail] at h
  exact h.symm

/-- The actual signed tail expectation is exactly a tail of the signed mass
series, with the source's strict absolute cutoff and the correct integer index. -/
theorem tailIncrementMean_eq_tailMass (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) {x : ℝ} (hx : 1 ≤ x) :
    tailIncrementMean μ x = tailMass (weightedIncrementMass μ) (⌊x⌋₊ + 2) := by
  calc
    tailIncrementMean μ x =
        ∑' k : ℕ, (μ {k}).toReal *
          (if x < |offspringIncrement k| then offspringIncrement k else 0) := by
      unfold tailIncrementMean
      simpa only [measureReal_def, smul_eq_mul] using
        integral_countable (integrable_tailIncrement μ hm x)
    _ = ∑' k : ℕ, if ⌊x⌋₊ + 2 ≤ k then weightedIncrementMass μ k else 0 := by
      apply tsum_congr
      intro k
      simp only [abs_increment_gt_iff_floor_add_two_le hx k]
      by_cases hk : ⌊x⌋₊ + 2 ≤ k <;>
        simp [hk, weightedIncrementMass, offspringIncrement]
    _ = _ := tsum_ite_ge_eq_tailMass (summable_weightedIncrementMass μ hm) _

end
end SubcriticalCauchy.Bienayme
