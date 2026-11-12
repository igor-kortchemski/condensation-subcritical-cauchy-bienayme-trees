module

public import SubcriticalCauchy.CriticalTail

import Mathlib.Tactic.Ring

/-!
# Weighted prefixes and sums of series tails

An exact finite identity expresses a sum of series tails as a weighted prefix
plus a terminal tail. Nonnegative summands then give the prefix-moment bound
used with truncated kernel estimates.
-/

@[expose] public section

namespace SubcriticalCauchy

/-- Finite summation by parts for the inclusive series tail. The identity is
valid for summable signed sequences. -/
theorem sum_tailMass_eq_weighted_prefix_add_tail {w : ℕ → ℝ}
    (hw : Summable w) (N : ℕ) :
    (∑ j ∈ Finset.range N, tailMass w (j + 1)) =
      (∑ k ∈ Finset.range N, (k : ℝ) * w k) + (N : ℝ) * tailMass w N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have htail : tailMass w N = w N + tailMass w (N + 1) := by
      simpa only [Finset.sum_range_one, Nat.add_zero] using tailMass_split hw N 1
    rw [htail]
    simp only [Nat.cast_succ]
    ring

/-- The weighted prefix over `k < N` is bounded by the sum of inclusive tails
at indices `1, …, N`. No positivity or summability of the tail sequence is
required beyond summability and nonnegativity of `w` itself. -/
theorem weighted_prefix_le_sum_tailMass {w : ℕ → ℝ}
    (hw : Summable w) (h0 : ∀ k : ℕ, 0 ≤ w k) (N : ℕ) :
    (∑ k ∈ Finset.range N, (k : ℝ) * w k) ≤
      ∑ j ∈ Finset.range N, tailMass w (j + 1) := by
  rw [sum_tailMass_eq_weighted_prefix_add_tail hw N]
  exact le_add_of_nonneg_right
    (mul_nonneg (Nat.cast_nonneg N) (tailMass_nonneg h0 N))

end SubcriticalCauchy
