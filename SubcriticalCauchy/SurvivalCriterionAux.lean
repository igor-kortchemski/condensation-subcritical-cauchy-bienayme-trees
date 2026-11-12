module

public import SubcriticalCauchy.BienaymeCorrection
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Data.Nat.Log

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# Elementary series lemmas for the survival criterion

This module contains the real-analysis input for the Heathcote--Seneta--Vere-Jones
criterion: finite-block comparisons for monotone sequences, independence of the
geometric sampling rate, and nonnegative Tonelli comparisons.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology BigOperators

namespace SubcriticalCauchy.Bienayme

/-- A nonnegative antitone sequence is summable when its sampling on every
`C`-th index is summable. The missing indices are controlled by blocks. -/
lemma summable_of_summable_mul_of_antitone {a : ℕ → ℝ} (ha : Antitone a)
    (ha0 : ∀ n, 0 ≤ a n) {C : ℕ} (hC : 0 < C)
    (hsub : Summable (fun n => a (C * n))) : Summable a := by
  have hblock : ∀ K : ℕ, (∑ n ∈ Finset.range (C * K), a n) ≤
      C * ∑ q ∈ Finset.range K, a (C * q) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, Finset.sum_range_succ]
      have hblock' : (∑ i ∈ Finset.range C, a (C * K + i)) ≤ C * a (C * K) := by
        calc
          (∑ i ∈ Finset.range C, a (C * K + i)) ≤ ∑ _i ∈ Finset.range C, a (C * K) := by
            apply Finset.sum_le_sum
            intro i hi
            exact ha (Nat.le_add_right _ _)
          _ = C * a (C * K) := by simp
      exact (add_le_add ih hblock').trans_eq (by ring)
  apply summable_of_sum_range_le (c := C * ∑' n, a (C * n)) ha0
  intro N
  calc
    (∑ n ∈ Finset.range N, a n) ≤ ∑ n ∈ Finset.range (C * N), a n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_mono (Nat.le_mul_of_pos_left N hC)
      · intro i hi hni
        exact ha0 i
    _ ≤ C * ∑ q ∈ Finset.range N, a (C * q) := hblock N
    _ ≤ C * ∑' n, a (C * n) :=
      mul_le_mul_of_nonneg_left
        (hsub.sum_le_tsum (Finset.range N) (fun i _ => ha0 _)) (Nat.cast_nonneg C)

/-- Sampling a nonnegative monotone function on geometric arguments gives the
same summability criterion at every rate in `(0,1)`. -/
lemma summable_geometric_comp_iff {f : ℝ → ℝ} {r s : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (hs0 : 0 < s) (hs1 : s < 1)
    (hf : MonotoneOn f (Set.Icc 0 1)) (hf0 : ∀ q ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f q) :
    Summable (fun n : ℕ => f (r ^ n)) ↔ Summable (fun n : ℕ => f (s ^ n)) := by
  have hpow01 (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (n : ℕ) : x ^ n ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨pow_nonneg hx0.le _, pow_le_one₀ hx0.le hx1.le⟩
  have forward (x y : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (hy0 : 0 < y) (hy1 : y < 1)
      (hx : Summable (fun n : ℕ => f (x ^ n))) : Summable (fun n : ℕ => f (y ^ n)) := by
    obtain ⟨C, hC⟩ := exists_pow_lt_of_lt_one hx0 hy1
    let D := C + 1
    have hD : 0 < D := Nat.zero_lt_succ C
    have hyD : y ^ D ≤ x := by
      calc
        y ^ D = y ^ C * y := by simp only [D, pow_succ]
        _ ≤ y ^ C := by
          have := pow_nonneg hy0.le C
          nlinarith
        _ ≤ x := hC.le
    have hpoint (n : ℕ) : f (y ^ (D * n)) ≤ f (x ^ n) := by
      apply hf (hpow01 y hy0 hy1 _) (hpow01 x hx0 hx1 _)
      rw [pow_mul]
      exact pow_le_pow_left₀ (pow_nonneg hy0.le _) hyD n
    have hsample : Summable (fun n : ℕ => f (y ^ (D * n))) :=
      hx.of_nonneg_of_le (fun n => hf0 _ (hpow01 y hy0 hy1 _)) hpoint
    apply summable_of_summable_mul_of_antitone (C := D) _
      (fun n => hf0 _ (hpow01 y hy0 hy1 n)) hD hsample
    intro m n hmn
    exact hf (hpow01 y hy0 hy1 _) (hpow01 y hy0 hy1 _)
      (pow_le_pow_of_le_one hy0.le hy1.le hmn)
  exact ⟨forward r s hr0 hr1 hs0 hs1, forward s r hs0 hs1 hr0 hr1⟩

/-- Tonelli for nonnegative real series, stated as an equivalence between the
two iterated sums. Finite-support rows and columns in the applications are
supplied separately. -/
lemma summable_tsum_swap_iff_of_nonneg (f : ℕ → ℕ → ℝ) (hf : ∀ j n, 0 ≤ f j n)
    (hrow : ∀ j, Summable (fun n => f j n)) (hcol : ∀ n, Summable (fun j => f j n)) :
    Summable (fun j => ∑' n, f j n) ↔ Summable (fun n => ∑' j, f j n) := by
  have hprod : Summable (fun p : ℕ × ℕ => f p.1 p.2) ↔
      Summable (fun p : ℕ × ℕ => f p.2 p.1) := by
    have he := (Equiv.prodComm ℕ ℕ).summable_iff (f := fun p : ℕ × ℕ => f p.1 p.2)
    change Summable (fun p : ℕ × ℕ => f p.2 p.1) ↔
      Summable (fun p : ℕ × ℕ => f p.1 p.2) at he
    exact he.symm
  have ha : Summable (fun p : ℕ × ℕ => f p.1 p.2) ↔ Summable (fun j => ∑' n, f j n) := by
    rw [summable_prod_of_nonneg (fun p => hf p.1 p.2)]
    exact and_iff_right hrow
  have hb : Summable (fun p : ℕ × ℕ => f p.2 p.1) ↔ Summable (fun n => ∑' j, f j n) := by
    rw [summable_prod_of_nonneg (fun p => hf p.2 p.1)]
    exact and_iff_right hcol
  exact ha.symm.trans (hprod.trans hb)


/-- The kernel obtained by expanding the survival correction in offspring tails. -/
def geometricKernel (j : ℕ) (x : ℝ) : ℝ := 1 - (1 - x) ^ j

lemma geometricKernel_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (j : ℕ) :
    0 ≤ geometricKernel j x :=
  sub_nonneg.mpr (pow_le_one₀ (sub_nonneg.mpr hx1) (by linarith))

lemma geometricKernel_le_one {x : ℝ} (_hx0 : 0 ≤ x) (hx1 : x ≤ 1) (j : ℕ) :
    geometricKernel j x ≤ 1 := by
  have := pow_nonneg (sub_nonneg.mpr hx1) j
  unfold geometricKernel
  linarith

lemma geometricKernel_le_mul {x : ℝ} (_hx0 : 0 ≤ x) (hx1 : x ≤ 1) (j : ℕ) :
    geometricKernel j x ≤ j * x := by
  have h := one_add_mul_sub_le_pow (a := 1 - x) (by linarith) j
  unfold geometricKernel
  norm_num at h ⊢
  nlinarith

lemma geometricKernel_mul_le {x : ℝ} (_hx0 : 0 ≤ x) (hx1 : x ≤ 1) (j : ℕ) :
    (j : ℝ) * x ≤ (1 + j * x) * geometricKernel j x := by
  have hbern : 1 + (j : ℝ) * x ≤ (1 + x) ^ j := by
    simpa using one_add_mul_le_pow (a := x) (by linarith) j
  have hprod : (1 + (j : ℝ) * x) * (1 - x) ^ j ≤ 1 := by
    calc
      (1 + (j : ℝ) * x) * (1 - x) ^ j ≤ (1 + x) ^ j * (1 - x) ^ j := by
        exact mul_le_mul_of_nonneg_right hbern (pow_nonneg (sub_nonneg.mpr hx1) j)
      _ = ((1 + x) * (1 - x)) ^ j := by rw [mul_pow]
      _ ≤ 1 := by
        apply pow_le_one₀
        · nlinarith [sq_nonneg x]
        · nlinarith [sq_nonneg x]
  unfold geometricKernel
  nlinarith

lemma geometricKernel_half_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (j : ℕ)
    (hjx : 1 ≤ (j : ℝ) * x) : 1 / 2 ≤ geometricKernel j x := by
  have h := geometricKernel_mul_le hx0 hx1 j
  nlinarith

lemma geometricKernel_monotone {x y : ℝ} (_hx0 : 0 ≤ x) (hy1 : y ≤ 1) (hxy : x ≤ y)
    (j : ℕ) : geometricKernel j x ≤ geometricKernel j y := by
  unfold geometricKernel
  apply sub_le_sub_left
  exact pow_le_pow_left₀ (sub_nonneg.mpr hy1) (sub_le_sub_left hxy 1) j

lemma geometricKernel_summable_half (j : ℕ) :
    Summable (fun n : ℕ => geometricKernel j ((1 / 2 : ℝ) ^ n)) := by
  by_cases hj : j = 0
  · subst j
    simp [geometricKernel]
  let N := Nat.log 2 j
  let g := fun n : ℕ => if n < N then 1 else 2 * (1 / 2 : ℝ) ^ (n - N)
  have hNlower : 2 ^ N ≤ j := Nat.pow_le_of_le_log hj le_rfl
  have hNupper : j < 2 ^ (N + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two j
  have hg : Summable g := by
    apply (summable_nat_add_iff N).mp
    have hh := summable_geometric_two.mul_left (2 : ℝ)
    apply hh.congr
    intro n
    simp only [g]
    simp only [show ¬ n + N < N by omega]
    congr 2
    omega
  apply hg.of_nonneg_of_le
  · intro n
    exact geometricKernel_nonneg (by positivity) (by norm_num [pow_le_one₀]) j
  · intro n
    simp only [g]
    split_ifs with hn
    · exact geometricKernel_le_one (by positivity) (by norm_num [pow_le_one₀]) j
    · calc
        geometricKernel j ((1 / 2 : ℝ) ^ n) ≤ j * (1 / 2 : ℝ) ^ n :=
          geometricKernel_le_mul (by positivity) (by norm_num [pow_le_one₀]) j
        _ ≤ 2 * (1 / 2 : ℝ) ^ (n - N) := by
          have hnN : N ≤ n := Nat.le_of_not_gt hn
          have hjratio : (j : ℝ) / (2 : ℝ) ^ N < 2 := by
            apply (div_lt_iff₀ (by positivity)).mpr
            exact_mod_cast (show j < 2 * 2 ^ N by simpa [pow_succ, mul_comm] using hNupper)
          have hpow : (1 / 2 : ℝ) ^ n = (1 / 2 : ℝ) ^ N * (1 / 2 : ℝ) ^ (n - N) := by
            conv_lhs => rw [show n = N + (n - N) by omega]
            rw [pow_add]
          rw [hpow]
          have hmid : (j : ℝ) * (1 / 2 : ℝ) ^ N < 2 := by
            rw [div_pow, one_pow]
            simpa [div_eq_mul_inv, mul_comm] using hjratio
          have hp : 0 < (1 / 2 : ℝ) ^ (n - N) := by positivity
          nlinarith

lemma geometricKernel_sum_half_lower {j : ℕ} (hj : 2 ≤ j) :
    (Nat.log 2 j + 1 : ℕ) / (2 : ℝ) ≤ ∑' n : ℕ, geometricKernel j ((1 / 2 : ℝ) ^ n) := by
  let N := Nat.log 2 j
  have hNlower : 2 ^ N ≤ j := Nat.pow_le_of_le_log (by omega) le_rfl
  have hsum := geometricKernel_summable_half j
  calc
    (N + 1 : ℕ) / (2 : ℝ) = ∑ _n ∈ Finset.range (N + 1), (1 / 2 : ℝ) := by simp; ring
    _ ≤ ∑ n ∈ Finset.range (N + 1), geometricKernel j ((1 / 2 : ℝ) ^ n) := by
      apply Finset.sum_le_sum
      intro n hn
      apply geometricKernel_half_le (by positivity) (by norm_num [pow_le_one₀]) j
      have hnN : n ≤ N := by have := Finset.mem_range.mp hn; omega
      have hp : 2 ^ n ≤ j := (Nat.pow_le_pow_right (by omega) hnN).trans hNlower
      have hratio : (1 : ℝ) ≤ (j : ℝ) / (2 : ℝ) ^ n := by
        apply (le_div_iff₀ (by positivity)).mpr
        have hp' : (2 : ℝ) ^ n ≤ j := by exact_mod_cast hp
        simpa using hp'
      simpa [div_pow, div_eq_mul_inv, mul_comm] using hratio
    _ ≤ ∑' n : ℕ, geometricKernel j ((1 / 2 : ℝ) ^ n) :=
      hsum.sum_le_tsum _ (fun n _ => geometricKernel_nonneg (by positivity)
        (by norm_num [pow_le_one₀]) j)

lemma geometricKernel_sum_half_upper {j : ℕ} (hj : 2 ≤ j) :
    (∑' n : ℕ, geometricKernel j ((1 / 2 : ℝ) ^ n)) ≤ Nat.log 2 j + 4 := by
  let N := Nat.log 2 j
  have hNlower : 2 ^ N ≤ j := Nat.pow_le_of_le_log (by omega) le_rfl
  have hNupper : j < 2 ^ (N + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two j
  have hsum := geometricKernel_summable_half j
  rw [← hsum.sum_add_tsum_nat_add N]
  have hhead : (∑ n ∈ Finset.range N, geometricKernel j ((1 / 2 : ℝ) ^ n)) ≤ N := by
    calc
      _ ≤ ∑ _n ∈ Finset.range N, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        exact geometricKernel_le_one (by positivity) (by norm_num [pow_le_one₀]) j
      _ = N := by simp
  have htailpoint (n : ℕ) : geometricKernel j ((1 / 2 : ℝ) ^ (n + N)) ≤
      2 * (1 / 2 : ℝ) ^ n := by
    calc
      _ ≤ j * (1 / 2 : ℝ) ^ (n + N) :=
        geometricKernel_le_mul (by positivity) (by norm_num [pow_le_one₀]) j
      _ ≤ _ := by
        have hjratio : (j : ℝ) / (2 : ℝ) ^ N < 2 := by
          apply (div_lt_iff₀ (by positivity)).mpr
          exact_mod_cast (show j < 2 * 2 ^ N by simpa [pow_succ, mul_comm] using hNupper)
        rw [add_comm n N, pow_add]
        have hmid : (j : ℝ) * (1 / 2 : ℝ) ^ N < 2 := by
          rw [div_pow, one_pow]
          simpa [div_eq_mul_inv, mul_comm] using hjratio
        have hp : 0 < (1 / 2 : ℝ) ^ n := by positivity
        nlinarith
  have htail : (∑' n : ℕ, geometricKernel j ((1 / 2 : ℝ) ^ (n + N))) ≤ 4 := by
    calc
      _ ≤ ∑' n : ℕ, 2 * (1 / 2 : ℝ) ^ n := by
        apply Summable.tsum_le_tsum htailpoint
        · exact hsum.comp_injective (add_left_injective N)
        · exact summable_geometric_two.mul_left 2
      _ = 4 := by rw [tsum_mul_left, tsum_geometric_two]; norm_num
  linarith

lemma geometricKernel_sum_half_comparable {j : ℕ} (hj : 2 ≤ j) :
    Real.log (j + 1) / (4 * Real.log 2) ≤
        (∑' n : ℕ, geometricKernel j ((1 / 2 : ℝ) ^ n)) ∧
      (∑' n : ℕ, geometricKernel j ((1 / 2 : ℝ) ^ n)) ≤
        5 * Real.log (j + 1) / Real.log 2 := by
  let N := Nat.log 2 j
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hNpos : 1 ≤ N := by
    apply Nat.le_log_of_pow_le Nat.one_lt_two
    exact_mod_cast hj
  have hNlower : 2 ^ N ≤ j := Nat.pow_le_of_le_log (by omega) le_rfl
  have hNupper : j < 2 ^ (N + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two j
  have hpowLower : (N : ℝ) * Real.log 2 ≤ Real.log j := by
    have hcast : (2 : ℝ) ^ N ≤ j := by exact_mod_cast hNlower
    calc
      (N : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ N) := (Real.log_pow 2 N).symm
      _ ≤ Real.log j := Real.log_le_log (by positivity) hcast
  have hlogUpper : Real.log j < (N + 1 : ℕ) * Real.log 2 := by
    have hcast : (j : ℝ) < 2 ^ (N + 1) := by exact_mod_cast hNupper
    calc
      Real.log j < Real.log ((2 : ℝ) ^ (N + 1)) := Real.log_lt_log (by positivity) hcast
      _ = (N + 1 : ℕ) * Real.log 2 := Real.log_pow 2 (N + 1)
  have hsquare : (j : ℝ) + 1 ≤ (j : ℝ) ^ 2 := by
    have hj' : (2 : ℝ) ≤ j := by exact_mod_cast hj
    nlinarith
  have hlogSucc : Real.log (j + 1) ≤ 2 * Real.log j := by
    calc
      Real.log (j + 1) ≤ Real.log ((j : ℝ) ^ 2) := Real.log_le_log (by positivity) hsquare
      _ = 2 * Real.log j := by rw [Real.log_pow]; push_cast; ring
  have hlow := geometricKernel_sum_half_lower hj
  have hupp := geometricKernel_sum_half_upper hj
  constructor
  · rw [div_le_iff₀ (by positivity)]
    calc
      Real.log (j + 1) ≤ 2 * Real.log j := hlogSucc
      _ ≤ 2 * ((N + 1 : ℕ) * Real.log 2) := by linarith
      _ = 4 * Real.log 2 * ((N + 1 : ℕ) / 2) := by ring
      _ ≤ (∑' n : ℕ, geometricKernel j ((1 / 2 : ℝ) ^ n)) * (4 * Real.log 2) := by
        have hlow' := hlow
        change (N + 1 : ℕ) / (2 : ℝ) ≤ _ at hlow'
        have hpos : 0 ≤ 4 * Real.log 2 := by positivity
        nlinarith
  · rw [le_div_iff₀ hlog2]
    calc
      (∑' n : ℕ, geometricKernel j ((1 / 2 : ℝ) ^ n)) * Real.log 2 ≤ (N + 4) * Real.log 2 := by
        exact mul_le_mul_of_nonneg_right hupp hlog2.le
      _ ≤ 5 * N * Real.log 2 := by
        have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
        nlinarith
      _ ≤ 5 * Real.log (j + 1) := by
        have hjpos : 0 < Real.log j := Real.log_pos (by exact_mod_cast (show 1 < j by omega))
        have hmono : Real.log (j : ℝ) ≤ Real.log (j + 1) :=
          Real.log_le_log (by positivity) (by linarith)
        have hs : 0 ≤ Real.log (j + 1) := by
          simpa using Real.log_natCast_nonneg (j + 1)
        nlinarith


lemma offspringTail_toReal_eq_tsum (μ : Measure ℕ) [IsProbabilityMeasure μ] (j : ℕ) :
    (μ (Set.Ioi j)).toReal = ∑' k : ℕ, if j < k then (μ {k}).toReal else 0 := by
  rw [offspringTail_eq_tsum, ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro k
    by_cases h : j < k <;> simp [h]
  · intro k
    by_cases h : j < k
    · simp only [h, ite_true]
      exact measure_ne_top μ {k}
    · simp [h]

/-- Geometric sampling of the correction is equivalent to a logarithmic tail sum. -/
lemma summable_survivalCorrection_half_iff_tail_log (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) :
    Summable (fun n : ℕ => survivalCorrection μ ((1 / 2 : ℝ) ^ n)) ↔
      Summable (fun j : ℕ => (μ (Set.Ioi j)).toReal * Real.log (j + 1)) := by
  let a : ℕ → ℝ := fun j => (μ (Set.Ioi j)).toReal
  let K : ℕ → ℕ → ℝ := fun j n => a j * geometricKernel j ((1 / 2 : ℝ) ^ n)
  have ha0 (j : ℕ) : 0 ≤ a j := ENNReal.toReal_nonneg
  have ha : Summable a := summable_offspringTail μ hm
  have hrow (j : ℕ) : Summable (K j) :=
    (geometricKernel_summable_half j).mul_left (a j)
  have hcol (n : ℕ) : Summable (fun j => K j n) := by
    apply ha.of_nonneg_of_le
    · intro j
      exact mul_nonneg (ha0 j) (geometricKernel_nonneg (by positivity)
        (by norm_num [pow_le_one₀]) j)
    · intro j
      simpa only [K, mul_one] using mul_le_mul_of_nonneg_left
        (geometricKernel_le_one (by positivity) (by norm_num [pow_le_one₀]) j) (ha0 j)
  have htonelli : Summable (fun j => ∑' n, K j n) ↔ Summable (fun n => ∑' j, K j n) :=
    summable_tsum_swap_iff_of_nonneg K (fun j n => mul_nonneg (ha0 j)
      (geometricKernel_nonneg (by positivity) (by norm_num [pow_le_one₀]) j)) hrow hcol
  have hcorr (n : ℕ) : (∑' j, K j n) = survivalCorrection μ ((1 / 2 : ℝ) ^ n) := by
    rw [survivalCorrection_eq_tsum_kernel μ hm (by positivity) (by norm_num [pow_le_one₀])]
    exact (tsum_congr fun j => rfl)
  have hleft (j : ℕ) : (∑' n, K j n) =
      a j * ∑' n, geometricKernel j ((1 / 2 : ℝ) ^ n) := tsum_mul_left
  rw [show Summable (fun n : ℕ => survivalCorrection μ ((1 / 2 : ℝ) ^ n)) ↔
      Summable (fun n => ∑' j, K j n) from summable_congr (fun n => (hcorr n).symm)]
  rw [← htonelli]
  simp_rw [hleft]
  let L : ℕ → ℝ := fun j => a j * Real.log (j + 1)
  let T : ℕ → ℝ := fun j => a j * ∑' n, geometricKernel j ((1 / 2 : ℝ) ^ n)
  change Summable T ↔ Summable L
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · intro h
    apply (summable_nat_add_iff 2).mp
    apply (((summable_nat_add_iff 2).mpr h).mul_left (4 * Real.log 2)).of_nonneg_of_le
    · intro j
      exact mul_nonneg (ha0 _) (by simpa using Real.log_natCast_nonneg (j + 2 + 1))
    · intro j
      have hb := mul_le_mul_of_nonneg_left (geometricKernel_sum_half_comparable (j := j + 2)
        (by omega)).1 (ha0 (j + 2))
      calc
        L (j + 2) = (4 * Real.log 2) * (a (j + 2) *
            (Real.log (j + 2 + 1) / (4 * Real.log 2))) := by
          dsimp [L]
          push_cast
          field_simp [hlog2.ne']
        _ ≤ (4 * Real.log 2) * T (j + 2) := by
          simpa only [T, Nat.cast_add, Nat.cast_ofNat] using
            mul_le_mul_of_nonneg_left hb (by positivity)
  · intro h
    apply (summable_nat_add_iff 2).mp
    apply (((summable_nat_add_iff 2).mpr h).mul_left (5 / Real.log 2)).of_nonneg_of_le
    · intro j
      exact mul_nonneg (ha0 _) (tsum_nonneg fun n => geometricKernel_nonneg (by positivity)
        (by norm_num [pow_le_one₀]) _)
    · intro j
      have hb := mul_le_mul_of_nonneg_left (geometricKernel_sum_half_comparable (j := j + 2)
        (by omega)).2 (ha0 (j + 2))
      calc
        T (j + 2) ≤ a (j + 2) * (5 * Real.log (j + 2 + 1) / Real.log 2) := by
          simpa only [T, Nat.cast_add, Nat.cast_ofNat] using hb
        _ = (5 / Real.log 2) * L (j + 2) := by
          dsimp [L]
          push_cast
          ring

lemma summable_tail_log_iff_mass_logSum (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    Summable (fun j : ℕ => (μ (Set.Ioi j)).toReal * Real.log (j + 1)) ↔
      Summable (fun k : ℕ => (μ {k}).toReal *
        ∑ j ∈ Finset.range k, Real.log (j + 1)) := by
  let p : ℕ → ℝ := fun k => (μ {k}).toReal
  let f : ℕ → ℕ → ℝ := fun j k => (if j < k then p k else 0) * Real.log (j + 1)
  have hp : Summable p := by
    simpa only [p, one_pow, mul_one] using summable_pgfReal μ 1 zero_le_one le_rfl
  have hrow (j : ℕ) : Summable (f j) := by
    apply (hp.mul_right (Real.log (j + 1))).of_nonneg_of_le
    · intro k
      exact mul_nonneg (by positivity) (by simpa using Real.log_natCast_nonneg (j + 1))
    · intro k
      by_cases hjk : j < k
      · simp [f, hjk]
      · simp only [f, hjk, ite_false, zero_mul]
        exact mul_nonneg ENNReal.toReal_nonneg (by simpa using Real.log_natCast_nonneg (j + 1))
  have hcol (k : ℕ) : Summable (fun j => f j k) := by
    apply summable_of_ne_finset_zero (s := Finset.range k)
    intro j hj
    simp only [Finset.mem_range, Nat.not_lt] at hj
    simp [f, Nat.not_lt.mpr hj]
  have hton := summable_tsum_swap_iff_of_nonneg f (fun j k => mul_nonneg (by positivity)
    (by simpa using Real.log_natCast_nonneg (j + 1))) hrow hcol
  have hleft (j : ℕ) : (∑' k, f j k) = (μ (Set.Ioi j)).toReal * Real.log (j + 1) := by
    rw [show (∑' k, f j k) = (∑' k : ℕ, if j < k then p k else 0) * Real.log (j + 1) by
      apply tsum_mul_right]
    rw [← offspringTail_toReal_eq_tsum]
  have hright (k : ℕ) : (∑' j, f j k) = p k * ∑ j ∈ Finset.range k, Real.log (j + 1) := by
    rw [tsum_eq_sum (s := Finset.range k) (fun j hj => by
      simp only [Finset.mem_range, Nat.not_lt] at hj
      simp [f, Nat.not_lt.mpr hj])]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp [f, Finset.mem_range.mp hj]
  rw [show Summable (fun j : ℕ => (μ (Set.Ioi j)).toReal * Real.log (j + 1)) ↔
      Summable (fun j => ∑' k, f j k) from summable_congr (fun j => (hleft j).symm)]
  rw [hton]
  exact summable_congr hright

lemma logSum_range_le_mul_log (k : ℕ) :
    (∑ j ∈ Finset.range k, Real.log (j + 1)) ≤ k * Real.log k := by
  by_cases hk : k = 0
  · subst k
    simp
  calc
    (∑ j ∈ Finset.range k, Real.log (j + 1)) ≤ ∑ _j ∈ Finset.range k, Real.log k := by
      apply Finset.sum_le_sum
      intro j hj
      apply Real.log_le_log (by positivity)
      have hjk : j + 1 ≤ k := Finset.mem_range.mp hj
      exact_mod_cast hjk
    _ = k * Real.log k := by simp

lemma mul_log_div_four_le_logSum_range {k : ℕ} (hk : 4 ≤ k) :
    (k : ℝ) * Real.log k / 4 ≤ ∑ j ∈ Finset.range k, Real.log (j + 1) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : 2 * Real.log 2 ≤ Real.log k := by
    have hcast : (4 : ℝ) ≤ k := by exact_mod_cast hk
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hcast
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      calc Real.log 4 = Real.log (2 ^ 2) := by norm_num
           _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
    linarith
  have hhalf : Real.log k / 2 ≤ Real.log ((k : ℝ) / 2) := by
    rw [Real.log_div (ne_of_gt hkpos) (by norm_num : (2 : ℝ) ≠ 0)]
    linarith
  have hnum : (k : ℝ) / 2 ≤ (k - k / 2 : ℕ) := by
    have hkn : k / 2 ≤ k := Nat.div_le_self k 2
    have hh : k ≤ 2 * (k - k / 2) := by omega
    have hc : (k : ℝ) ≤ 2 * (k - k / 2 : ℕ) := by exact_mod_cast hh
    linarith
  calc
    (k : ℝ) * Real.log k / 4 = ((k : ℝ) / 2) * (Real.log k / 2) := by ring
    _ ≤ (k - k / 2 : ℕ) * Real.log ((k : ℝ) / 2) := by
      exact mul_le_mul hnum hhalf (by positivity) (by positivity)
    _ = ∑ _j ∈ Finset.Ico (k / 2) k, Real.log ((k : ℝ) / 2) := by simp
    _ ≤ ∑ j ∈ Finset.Ico (k / 2) k, Real.log (j + 1) := by
      apply Finset.sum_le_sum
      intro j hj
      apply Real.log_le_log (by positivity)
      have hjlow : k / 2 ≤ j := (Finset.mem_Ico.mp hj).1
      have hh : k ≤ 2 * (j + 1) := by omega
      have hc : (k : ℝ) ≤ 2 * ((j + 1 : ℕ) : ℝ) := by exact_mod_cast hh
      push_cast at hc
      linarith
    _ ≤ ∑ j ∈ Finset.range k, Real.log (j + 1) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        exact Finset.mem_range.mpr (Finset.mem_Ico.mp hj).2
      · intro j hj hjk
        exact by simpa using Real.log_natCast_nonneg (j + 1)

lemma summable_mass_logSum_iff_mass_mul_log (μ : Measure ℕ) :
    Summable (fun k : ℕ => (μ {k}).toReal *
        ∑ j ∈ Finset.range k, Real.log (j + 1)) ↔
      Summable (fun k : ℕ => (k : ℝ) * Real.log k * (μ {k}).toReal) := by
  let L : ℕ → ℝ := fun k => (μ {k}).toReal * ∑ j ∈ Finset.range k, Real.log (j + 1)
  let B : ℕ → ℝ := fun k => (k : ℝ) * Real.log k * (μ {k}).toReal
  change Summable L ↔ Summable B
  constructor
  · intro hL
    apply (summable_nat_add_iff 4).mp
    apply ((summable_nat_add_iff 4).mpr hL).mul_left (4 : ℝ) |>.of_nonneg_of_le
    · intro j
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by simpa using Real.log_natCast_nonneg (j + 4))) ENNReal.toReal_nonneg
    · intro j
      have hb := mul_le_mul_of_nonneg_left (mul_log_div_four_le_logSum_range (k := j + 4) (by omega))
        (show 0 ≤ (μ {j + 4}).toReal from ENNReal.toReal_nonneg)
      dsimp [L, B]
      calc
        B (j + 4) = 4 * ((μ {j + 4}).toReal *
            (((j + 4 : ℕ) : ℝ) * Real.log ((j + 4 : ℕ) : ℝ) / 4)) := by
          dsimp [B]
          ring
        _ ≤ 4 * L (j + 4) := mul_le_mul_of_nonneg_left hb (by norm_num)
  · intro hB
    apply hB.of_nonneg_of_le
    · intro k
      exact mul_nonneg ENNReal.toReal_nonneg (Finset.sum_nonneg fun j _ => by simpa using Real.log_natCast_nonneg (j + 1))
    · intro k
      calc
        L k ≤ (μ {k}).toReal * (k * Real.log k) :=
          mul_le_mul_of_nonneg_left (logSum_range_le_mul_log k) ENNReal.toReal_nonneg
        _ = B k := by dsimp [B]; ring

lemma summable_survivalCorrection_half_iff_mass_mul_log (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (hm : offspringMean μ ≠ ∞) :
    Summable (fun n : ℕ => survivalCorrection μ ((1 / 2 : ℝ) ^ n)) ↔
      Summable (fun k : ℕ => (k : ℝ) * Real.log k * (μ {k}).toReal) :=
  (summable_survivalCorrection_half_iff_tail_log μ hm).trans
    ((summable_tail_log_iff_mass_logSum μ).trans (summable_mass_logSum_iff_mass_mul_log μ))

end SubcriticalCauchy.Bienayme
