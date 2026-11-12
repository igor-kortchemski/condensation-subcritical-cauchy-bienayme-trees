module

public import SubcriticalCauchy.CyclicResidual
public import BGW.Tree.ForestCycle

import Lean.Elab.Tactic.Omega

/-! # Reversal and downward skip-free survival

The reversal identity below is pointwise, so it holds under every law, in
particular the finite iid offspring law. Time zero is included in comparisons
and excluded from the positive-time record predicate.
-/

@[expose] public section

open MeasureTheory

namespace SubcriticalCauchy.Bienayme

/-- Reversing exchanges a terminal weak record with nonnegative forward prefixes. -/
theorem reverse_terminal_record_iff (x : List ℤ) :
    (∀ i < x.length, prefixSum x.reverse i ≤ prefixSum x.reverse x.length) ↔
      ∀ j ≤ x.length, 0 ≤ prefixSum x j := by
  have hrev (i : ℕ) : prefixSum x.reverse i = (x.drop (x.length - i)).sum := by
    simp [prefixSum, List.take_reverse]
  have htotal : prefixSum x.reverse x.length = x.sum := by
    rw [hrev]
    simp
  rw [htotal]
  simp only [hrev]
  constructor
  · intro h j hj
    by_cases hj0 : j = 0
    · simp [hj0, prefixSum]
    · have hi : x.length - j < x.length := by omega
      have hh := h (x.length - j) hi
      have he : x.length - (x.length - j) = j := by omega
      rw [he] at hh
      have hs := List.sum_take_add_sum_drop x j
      dsimp [prefixSum]
      omega
  · intro h i hi
    have hh := h (x.length - i) (by omega)
    have hs := List.sum_take_add_sum_drop x (x.length - i)
    dsimp [prefixSum] at hh
    omega

/-- With jumps at least `-1`, survival is exactly avoidance of `-1`. -/
theorem nonnegative_prefix_iff_no_hit_neg_one (x : List ℤ)
    (hx : ∀ a ∈ x, -1 ≤ a) :
    (∀ j ≤ x.length, 0 ≤ prefixSum x j) ↔
      ∀ j ≤ x.length, prefixSum x j ≠ -1 := by
  constructor
  · intro h j hj he
    have := h j hj
    omega
  · intro h j hj
    by_contra hn
    have hb : (x.take j).sum ≤ (-1 : ℤ) := by
      change ¬ 0 ≤ (x.take j).sum at hn
      omega
    obtain ⟨l, hlj, hl, _⟩ := BGW.exists_first_sum_take_eq hx (by omega) hb
    exact h l (by omega) hl

/-- The no-hit event is exactly failure of the shared finite first-hit search. -/
theorem firstHit_neg_one_eq_none_iff (x : List ℤ) :
    firstHit? 1 x = none ↔ ∀ j ≤ x.length, prefixSum x j ≠ -1 := by
  unfold firstHit?
  rw [List.find?_eq_none]
  simp only [List.mem_range, Nat.cast_one, decide_eq_true_eq]
  constructor
  · intro h j hj
    exact h j (by omega)
  · intro h j hj
    exact h j (by omega)

/-- Finite reversal identity, including the no-hit formulation of `τ > k`.
No mean or subcriticality assumption is needed for this finite identity. -/
theorem iid_reversal_record_probability (μ : Measure ℕ) (k : ℕ) (hk : 1 ≤ k) :
    (Measure.pi (fun _ : Fin k => μ))
        {ω | 0 < k ∧ ∀ i < k,
          prefixSum (List.ofFn (fun j => (ω j : ℤ) - 1)).reverse i ≤
            prefixSum (List.ofFn (fun j => (ω j : ℤ) - 1)).reverse k} =
      (Measure.pi (fun _ : Fin k => μ))
        {ω | ∀ j ≤ k, 0 ≤ prefixSum (List.ofFn (fun i => (ω i : ℤ) - 1)) j} ∧
    (Measure.pi (fun _ : Fin k => μ))
        {ω | ∀ j ≤ k, 0 ≤ prefixSum (List.ofFn (fun i => (ω i : ℤ) - 1)) j} =
      (Measure.pi (fun _ : Fin k => μ))
        {ω | ∀ j ≤ k, prefixSum (List.ofFn (fun i => (ω i : ℤ) - 1)) j ≠ -1} := by
  constructor
  · congr 1
    ext ω
    have h := reverse_terminal_record_iff (List.ofFn (fun j : Fin k => (ω j : ℤ) - 1))
    simpa [List.length_ofFn, show 0 < k by omega] using h
  · congr 1
    ext ω
    have hx : ∀ a ∈ List.ofFn (fun j : Fin k => (ω j : ℤ) - 1), -1 ≤ a := by
      intro a ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      omega
    simpa using nonnegative_prefix_iff_no_hit_neg_one _ hx

end SubcriticalCauchy.Bienayme
