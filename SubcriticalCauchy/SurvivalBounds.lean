module

public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Deterministic bounds for a survival recurrence

This file formalizes the geometric-comparison argument in the proof of Lemma
`lem:bounds` (ii), manuscript lines 468–471. The results are conditional analytic
lemmas. BienaymeSurvivalRatio supplies the actual-law positivity and ratio limit
and applies this comparison to prove the paper's geometric lower bound.
This file alone does not prove the paper's lemma.
-/

@[expose] public section

open Filter
open scoped Topology

namespace SubcriticalCauchy

/-- An upper multiplicative recurrence with initial value one gives an upper
geometric bound at every index. -/
theorem geometric_upper_bound {q : ℕ → ℝ} {m : ℝ}
    (hm : 0 ≤ m) (hzero : q 0 = 1)
    (hstep : ∀ n, q (n + 1) ≤ m * q n) (n : ℕ) :
    q n ≤ m ^ n := by
  simpa only [hzero, mul_one] using
    le_geom hm n (fun k _ => hstep k)

/-- If a positive sequence has successive ratio tending to `m`, every positive
geometric rate strictly less than `m` is eventually a lower bound. -/
theorem eventually_pow_le_of_ratio {q : ℕ → ℝ} {m r : ℝ}
    (hq : ∀ n, 0 < q n) (hr : 0 < r) (hrm : r < m)
    (hratio : Tendsto (fun n => q (n + 1) / q n) atTop (𝓝 m)) :
    ∀ᶠ n in atTop, r ^ n ≤ q n := by
  obtain ⟨s, hrs, hsm⟩ := exists_between hrm
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hratio.eventually_const_le hsm)
  have hnormalized : Tendsto (fun n => q n / r ^ n) atTop atTop := by
    apply (tendsto_add_atTop_iff_nat N).1
    apply tendsto_atTop_of_geom_le
      (c := s / r) (div_pos (hq (0 + N)) (pow_pos hr (0 + N)))
      ((one_lt_div hr).2 hrs)
    intro n
    have hindex : n + 1 + N = n + N + 1 := by
      simp only [Nat.add_assoc, Nat.add_comm 1 N]
    have hstep : s * q (n + N) ≤ q (n + N + 1) :=
      (le_div_iff₀ (hq (n + N))).1 (hN (n + N) (Nat.le_add_left N n))
    rw [div_mul_div_comm, hindex, pow_succ']
    exact div_le_div_of_nonneg_right hstep
      (mul_nonneg hr.le (pow_nonneg hr.le _))
  filter_upwards [hnormalized.eventually_ge_atTop 1] with n hn
  exact (one_le_div (pow_pos hr n)).1 hn

/-- The deterministic geometric bounds used in Lemma `lem:bounds` (ii).
Subcriticality is not needed for this implication; it is required when using the
upper bound to deduce convergence to zero. -/
theorem geometric_bounds_of_ratio {q : ℕ → ℝ} {m : ℝ}
    (hm : 0 < m) (hq : ∀ n, 0 < q n) (hzero : q 0 = 1)
    (hstep : ∀ n, q (n + 1) ≤ m * q n)
    (hratio : Tendsto (fun n => q (n + 1) / q n) atTop (𝓝 m)) :
    (∀ n, q n ≤ m ^ n) ∧
      ∀ η : ℝ, 0 < η → η < m →
        ∀ᶠ n in atTop, (m - η) ^ n ≤ q n := by
  refine ⟨geometric_upper_bound hm.le hzero hstep, ?_⟩
  intro η hη hηm
  exact eventually_pow_le_of_ratio hq (sub_pos.mpr hηm)
    (sub_lt_self m hη) hratio

/-- Conditional recurrence form of the geometric bounds. The correction is
assumed to tend to zero along the sequence; no regular-variation or branching
process theorem is silently included in this hypothesis. -/
theorem geometric_bounds_of_recurrence {q : ℕ → ℝ} {m : ℝ} {ell : ℝ → ℝ}
    (hm : 0 < m) (hzero : q 0 = 1)
    (hnonneg : ∀ n, 0 ≤ ell (q n))
    (hlt : ∀ n, ell (q n) < m)
    (hrec : ∀ n, q (n + 1) = q n * (m - ell (q n)))
    (hell : Tendsto (fun n => ell (q n)) atTop (𝓝 0)) :
    (∀ n, q n ≤ m ^ n) ∧
      ∀ η : ℝ, 0 < η → η < m →
        ∀ᶠ n in atTop, (m - η) ^ n ≤ q n := by
  have hq : ∀ n, 0 < q n := by
    intro n
    induction n with
    | zero => simpa only [hzero] using (zero_lt_one : (0 : ℝ) < 1)
    | succ n ih =>
      rw [hrec n]
      exact mul_pos ih (sub_pos.mpr (hlt n))
  have hstep : ∀ n, q (n + 1) ≤ m * q n := by
    intro n
    rw [hrec n]
    calc
      q n * (m - ell (q n)) ≤ q n * m :=
        mul_le_mul_of_nonneg_left (sub_le_self m (hnonneg n)) (hq n).le
      _ = m * q n := mul_comm _ _
  have hratio : Tendsto (fun n => q (n + 1) / q n) atTop (𝓝 m) := by
    have heq : (fun n => q (n + 1) / q n) = (fun n => m - ell (q n)) := by
      funext n
      rw [hrec n]
      exact mul_div_cancel_left₀ _ (hq n).ne'
    rw [heq]
    simpa only [sub_zero] using (tendsto_const_nhds (x := m)).sub hell
  exact geometric_bounds_of_ratio hm hq hzero hstep hratio

/-- In the subcritical case the upper bound forces the sequence to zero. -/
theorem tendsto_zero_of_geometric_upper_bound {q : ℕ → ℝ} {m : ℝ}
    (hm : 0 ≤ m) (hm1 : m < 1) (hq : ∀ n, 0 ≤ q n)
    (hbound : ∀ n, q n ≤ m ^ n) : Tendsto q atTop (𝓝 0) := by
  exact squeeze_zero hq hbound (tendsto_pow_atTop_nhds_zero_of_lt_one hm hm1)

end SubcriticalCauchy
