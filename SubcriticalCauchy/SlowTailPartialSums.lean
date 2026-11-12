module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Floor.Semifield

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# A partial-sum bound for an antitone slowly varying sequence

The estimate follows by strong induction after splitting the sum in half.
Only the ratio at the factor `1 / 2` is needed. In particular the sequence
itself need not be summable, and there is no monotonicity assumption on any
underlying local-mass model.
-/

@[expose] public section

open Filter
open scoped Topology

namespace SubcriticalCauchy

/-- An antitone positive sequence with half-scale ratio tending to one has
partial sums bounded by a fixed constant times `n * A n`. -/
theorem slowTail_partial_sum_bound_of_half_ratio {A : ℕ → ℝ}
    (h0 : ∀ n : ℕ, 0 ≤ A n) (hpos : ∀ n : ℕ, 1 ≤ n → 0 < A n)
    (hanti : Antitone A)
    (hhalf : Tendsto (fun n : ℕ => A (n / 2) / A n) atTop (𝓝 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∑ j ∈ Finset.Icc 1 n, A j ≤ C * (n : ℝ) * A n := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (hhalf.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 3 / 2)))
  let N := max N₀ 2
  have hN2 : 2 ≤ N := le_max_right _ _
  have hAN : 0 < A N := hpos N (by omega)
  let C : ℝ := max 6 (A 1 / A N)
  have hC6 : 6 ≤ C := le_max_left _ _
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num) hC6
  have hCratio : A 1 / A N ≤ C := le_max_right _ _
  let S : ℕ → ℝ := fun n => ∑ j ∈ Finset.range n, A (j + 1)
  have hconst (n : ℕ) : S n ≤ (n : ℝ) * A 1 := by
    calc
      S n ≤ ∑ _j ∈ Finset.range n, A 1 := by
        apply Finset.sum_le_sum
        intro j _
        exact hanti (Nat.succ_pos j)
      _ = (n : ℝ) * A 1 := by simp
  have hbound : ∀ n : ℕ, S n ≤ C * (n : ℝ) * A n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [S]
      by_cases hnN : n < N
      · have hANn : A N ≤ A n := hanti hnN.le
        have hA1 : A 1 ≤ C * A n := by
          calc
            A 1 ≤ C * A N := (div_le_iff₀ hAN).mp hCratio
            _ ≤ C * A n := mul_le_mul_of_nonneg_left hANn hCpos.le
        calc
          S n ≤ (n : ℝ) * A 1 := hconst n
          _ ≤ (n : ℝ) * (C * A n) :=
            mul_le_mul_of_nonneg_left hA1 (Nat.cast_nonneg n)
          _ = C * (n : ℝ) * A n := by ring
      · have hNn : N ≤ n := le_of_not_gt hnN
        let m := n / 2
        have hmn : m < n := by dsimp [m]; omega
        have hmle : m ≤ n := hmn.le
        have h2m : 2 * m ≤ n := by dsimp [m]; omega
        have hnR : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        have h2mR : 2 * (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2m
        have hAn : 0 < A n := hpos n hn
        have hAm : A m ≤ (3 / 2 : ℝ) * A n := by
          apply le_of_lt
          apply (div_lt_iff₀ hAn).mp
          exact hN₀ n ((le_max_left _ _).trans hNn)
        have hsplit : S n = S m +
            ∑ j ∈ Finset.range (n - m), A (m + j + 1) := by
          have h := Finset.sum_range_add (fun j => A (j + 1)) m (n - m)
          rw [Nat.add_sub_of_le hmle] at h
          exact h
        have hrest : (∑ j ∈ Finset.range (n - m), A (m + j + 1)) ≤
            (n : ℝ) * A m := by
          calc
            (∑ j ∈ Finset.range (n - m), A (m + j + 1)) ≤
                ∑ _j ∈ Finset.range (n - m), A m := by
              apply Finset.sum_le_sum
              intro j _
              apply hanti
              omega
            _ = ((n - m : ℕ) : ℝ) * A m := by simp
            _ ≤ (n : ℝ) * A m := by
              apply mul_le_mul_of_nonneg_right _ (h0 m)
              exact_mod_cast Nat.sub_le n m
        have hcoef : (3 / 2 : ℝ) * (C * (m : ℝ) + (n : ℝ)) ≤ C * (n : ℝ) := by
          have hmul := mul_le_mul_of_nonneg_left h2mR hCpos.le
          have hmul' := mul_nonneg (sub_nonneg.mpr hC6) hnR
          nlinarith
        calc
          S n = S m + ∑ j ∈ Finset.range (n - m), A (m + j + 1) := hsplit
          _ ≤ C * (m : ℝ) * A m + (n : ℝ) * A m :=
            add_le_add (ih m hmn) hrest
          _ = (C * (m : ℝ) + (n : ℝ)) * A m := by ring
          _ ≤ (C * (m : ℝ) + (n : ℝ)) * ((3 / 2 : ℝ) * A n) :=
            mul_le_mul_of_nonneg_left hAm (by positivity)
          _ = ((3 / 2 : ℝ) * (C * (m : ℝ) + (n : ℝ))) * A n := by ring
          _ ≤ (C * (n : ℝ)) * A n := mul_le_mul_of_nonneg_right hcoef hAn.le
  refine ⟨C, hCpos, ?_⟩
  intro n _
  have hsum : (∑ j ∈ Finset.Icc 1 n, A j) = S n := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel, Nat.add_comm, S]
  rw [hsum]
  exact hbound n

/-- The usual floor-indexed slow-variation hypothesis supplies the half-scale
ratio needed by the partial-sum bound. -/
theorem slowTail_partial_sum_bound {A : ℕ → ℝ}
    (h0 : ∀ n : ℕ, 0 ≤ A n) (hpos : ∀ n : ℕ, 1 ≤ n → 0 < A n)
    (hanti : Antitone A)
    (hsv : ∀ c : ℝ, 0 < c →
      Tendsto (fun n : ℕ => A ⌊c * (n : ℝ)⌋₊ / A n) atTop (𝓝 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∑ j ∈ Finset.Icc 1 n, A j ≤ C * (n : ℝ) * A n := by
  apply slowTail_partial_sum_bound_of_half_ratio h0 hpos hanti
  have harg (n : ℕ) : ⌊(1 / 2 : ℝ) * (n : ℝ)⌋₊ = n / 2 := by
    rw [one_div_mul_eq_div]
    exact Nat.floor_div_eq_div n 2
  simpa only [harg] using hsv (1 / 2) (by norm_num)

end SubcriticalCauchy
