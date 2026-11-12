module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Algebra.BigOperators.Field

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# A boundary estimate for an integrable tail of index minus one

Dyadic ratio limits imply that `n * T n` is negligible compared with the
summable tail of a nonnegative antitone sequence `T`. This is a pure analytic
helper. Its dyadic ratio hypothesis is not yet derived from the paper's
offspring asymptotics, and this file alone does not prove Lemma 2.2(i) or 4.4(i).
-/

@[expose] public section

open Filter
open scoped Topology

namespace SubcriticalCauchy

noncomputable section

/-- The tail beginning at `n`, with the endpoint included. -/
def tailMass (T : ℕ → ℝ) (n : ℕ) : ℝ := ∑' j : ℕ, T (n + j)

theorem summable_tailMass {T : ℕ → ℝ} (hT : Summable T) (n : ℕ) :
    Summable (fun j : ℕ => T (n + j)) := by
  simpa only [Nat.add_comm] using (summable_nat_add_iff n).mpr hT

theorem tailMass_nonneg {T : ℕ → ℝ} (h0 : ∀ n, 0 ≤ T n) (n : ℕ) :
    0 ≤ tailMass T n := tsum_nonneg (fun j => h0 (n + j))

theorem tailMass_pos {T : ℕ → ℝ} (hT : Summable T) (h0 : ∀ n, 0 ≤ T n)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < T n) {n : ℕ} (hn : 1 ≤ n) :
    0 < tailMass T n := by
  apply (summable_tailMass hT n).tsum_pos (fun j => h0 (n + j)) 0
  simpa only [Nat.add_zero] using hpos n hn

theorem tailMass_antitone {T : ℕ → ℝ} (hT : Summable T) (hanti : Antitone T) :
    Antitone (tailMass T) := by
  intro n m hnm
  apply (summable_tailMass hT m).tsum_le_tsum _ (summable_tailMass hT n)
  intro j
  exact hanti (Nat.add_le_add_right hnm j)

/-- Standard vanishing of series tails. In the applications below summability
ensures these tails are the genuine convergent series. -/
theorem tailMass_tendsto_zero (T : ℕ → ℝ) :
    Tendsto (tailMass T) atTop (𝓝 0) := by
  apply (_root_.tendsto_sum_nat_add T).congr'
  exact Eventually.of_forall (fun n =>
    tsum_congr (fun k => congrArg T (Nat.add_comm k n)))

theorem tailMass_split {T : ℕ → ℝ} (hT : Summable T) (n k : ℕ) :
    tailMass T n = (∑ j ∈ Finset.range k, T (n + j)) + tailMass T (n + k) := by
  have h := (summable_tailMass hT n).sum_add_tsum_nat_add k
  simpa only [tailMass, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.symm

/-- One dyadic block has at least its length times its endpoint value. -/
theorem tailMass_block_lower_bound {T : ℕ → ℝ} (hT : Summable T)
    (hanti : Antitone T) (n : ℕ) :
    (n : ℝ) * T (n + n) + tailMass T (n + n) ≤ tailMass T n := by
  have hb : (n : ℝ) * T (n + n) ≤ ∑ j ∈ Finset.range n, T (n + j) := by
    calc
      (n : ℝ) * T (n + n) = ∑ _j ∈ Finset.range n, T (n + n) := by simp
      _ ≤ ∑ j ∈ Finset.range n, T (n + j) := by
        apply Finset.sum_le_sum
        intro j hj
        exact hanti (Nat.add_le_add_left (Finset.mem_range.mp hj).le n)
  rw [tailMass_split hT n n]
  linarith

/-- Sum of endpoint lower bounds from the first `K` disjoint dyadic blocks. -/
def dyadicBlockSum (T : ℕ → ℝ) (K n : ℕ) : ℝ :=
  ∑ r ∈ Finset.range K, ((2 ^ r * n : ℕ) : ℝ) * T (2 ^ (r + 1) * n)

theorem dyadicBlockSum_succ (T : ℕ → ℝ) (K n : ℕ) :
    dyadicBlockSum T (K + 1) n = dyadicBlockSum T K n +
      ((2 ^ K * n : ℕ) : ℝ) * T (2 ^ (K + 1) * n) := by
  exact Finset.sum_range_succ _ _

theorem dyadicBlockSum_add_tail_le {T : ℕ → ℝ} (hT : Summable T)
    (hanti : Antitone T) (K n : ℕ) :
    dyadicBlockSum T K n + tailMass T (2 ^ K * n) ≤ tailMass T n := by
  induction K with
  | zero => simp [dyadicBlockSum]
  | succ K ih =>
    have heq : 2 ^ K * n + 2 ^ K * n = 2 ^ (K + 1) * n := by
      rw [pow_succ]
      ring
    have hb := tailMass_block_lower_bound hT hanti (2 ^ K * n)
    rw [heq] at hb
    rw [dyadicBlockSum_succ]
    linarith

theorem dyadicBlockSum_le_tail {T : ℕ → ℝ} (hT : Summable T)
    (h0 : ∀ n, 0 ≤ T n) (hanti : Antitone T) (K n : ℕ) :
    dyadicBlockSum T K n ≤ tailMass T n := by
  exact (le_add_of_nonneg_right (tailMass_nonneg h0 _)).trans
    (dyadicBlockSum_add_tail_le hT hanti K n)

/-- Every fixed finite family of normalized dyadic blocks contributes one half
per block in the limit. The family size is fixed before taking the limit. -/
theorem dyadicBlockSum_div_tendsto {T : ℕ → ℝ}
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < T n)
    (hratio : ∀ r : ℕ, Tendsto (fun n : ℕ => T (2 ^ r * n) / T n)
      atTop (𝓝 (((2 : ℝ) ^ r)⁻¹))) (K : ℕ) :
    Tendsto (fun n : ℕ => dyadicBlockSum T K n / ((n : ℝ) * T n))
      atTop (𝓝 ((K : ℝ) / 2)) := by
  have hterm (r : ℕ) : Tendsto
      (fun n : ℕ => (2 : ℝ) ^ r * (T (2 ^ (r + 1) * n) / T n))
      atTop (𝓝 ((1 : ℝ) / 2)) := by
    have h := (hratio (r + 1)).const_mul ((2 : ℝ) ^ r)
    have hval : (2 : ℝ) ^ r * ((2 : ℝ) ^ (r + 1))⁻¹ = (1 : ℝ) / 2 := by
      rw [pow_succ]
      field_simp
    simpa only [hval] using h
  have hs : Tendsto (fun n : ℕ => ∑ r ∈ Finset.range K,
      (2 : ℝ) ^ r * (T (2 ^ (r + 1) * n) / T n))
      atTop (𝓝 (∑ _r ∈ Finset.range K, (1 : ℝ) / 2)) := by
    apply tendsto_finsetSum
    intro r _
    exact hterm r
  have heq : (fun n : ℕ => ∑ r ∈ Finset.range K,
      (2 : ℝ) ^ r * (T (2 ^ (r + 1) * n) / T n)) =ᶠ[atTop]
      (fun n : ℕ => dyadicBlockSum T K n / ((n : ℝ) * T n)) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn)).ne'
    have hT0 : T n ≠ 0 := (hpos n hn).ne'
    rw [dyadicBlockSum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro r _
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    field_simp [hn0, hT0]
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one_div] using hs.congr' heq

/-- A summable antitone tail with index-minus-one dyadic ratios dominates its
single-scale contribution `n * T n` by an arbitrarily large factor. -/
theorem tailMass_div_mul_tendsto_atTop {T : ℕ → ℝ} (hT : Summable T)
    (h0 : ∀ n, 0 ≤ T n) (hpos : ∀ n : ℕ, 1 ≤ n → 0 < T n)
    (hanti : Antitone T)
    (hratio : ∀ r : ℕ, Tendsto (fun n : ℕ => T (2 ^ r * n) / T n)
      atTop (𝓝 (((2 : ℝ) ^ r)⁻¹))) :
    Tendsto (fun n : ℕ => tailMass T n / ((n : ℝ) * T n)) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  obtain ⟨K, hK⟩ := exists_nat_gt (2 * b)
  have hb : b < (K : ℝ) / 2 := by linarith
  filter_upwards [(dyadicBlockSum_div_tendsto hpos hratio K).eventually_const_le hb] with n hn
  exact hn.trans (div_le_div_of_nonneg_right (dyadicBlockSum_le_tail hT h0 hanti K n)
    (mul_nonneg (Nat.cast_nonneg n) (h0 n)))

/-- The integrable index-minus-one boundary estimate. This theorem is a generic
analytic implication, not yet a discharge of the paper's local-tail hypothesis. -/
theorem mul_tail_div_tailMass_tendsto_zero {T : ℕ → ℝ} (hT : Summable T)
    (h0 : ∀ n, 0 ≤ T n) (hpos : ∀ n : ℕ, 1 ≤ n → 0 < T n)
    (hanti : Antitone T)
    (hratio : ∀ r : ℕ, Tendsto (fun n : ℕ => T (2 ^ r * n) / T n)
      atTop (𝓝 (((2 : ℝ) ^ r)⁻¹))) :
    Tendsto (fun n : ℕ => ((n : ℝ) * T n) / tailMass T n) atTop (𝓝 0) := by
  simpa only [Function.comp_def, Pi.inv_apply, inv_div] using tendsto_inv_atTop_zero.comp
    (tailMass_div_mul_tendsto_atTop hT h0 hpos hanti hratio)

/-- Moving the tail endpoint by a fixed multiple loses at most that many copies
of its first term. -/
theorem tailMass_succ_mul_loss_bounds {T : ℕ → ℝ} (hT : Summable T)
    (h0 : ∀ n, 0 ≤ T n) (hanti : Antitone T) (k n : ℕ) :
    0 ≤ tailMass T n - tailMass T ((k + 1) * n) ∧
      tailMass T n - tailMass T ((k + 1) * n) ≤ ((k * n : ℕ) : ℝ) * T n := by
  have heq : (k + 1) * n = n + k * n := by ring
  have hdiff : tailMass T n - tailMass T ((k + 1) * n) =
      ∑ j ∈ Finset.range (k * n), T (n + j) := by
    rw [heq, tailMass_split hT n (k * n)]
    ring
  rw [hdiff]
  constructor
  · exact Finset.sum_nonneg (fun j _ => h0 (n + j))
  · calc
      _ ≤ ∑ _j ∈ Finset.range (k * n), T n :=
        Finset.sum_le_sum (fun j _ => hanti (Nat.le_add_right n j))
      _ = _ := by simp

/-- The primitive tail has ratio one at every positive integer scale. -/
theorem tailMass_succ_mul_div_tendsto_one {T : ℕ → ℝ} (hT : Summable T)
    (h0 : ∀ n, 0 ≤ T n) (hpos : ∀ n : ℕ, 1 ≤ n → 0 < T n)
    (hanti : Antitone T)
    (hratio : ∀ r : ℕ, Tendsto (fun n : ℕ => T (2 ^ r * n) / T n)
      atTop (𝓝 (((2 : ℝ) ^ r)⁻¹))) (k : ℕ) :
    Tendsto (fun n : ℕ => tailMass T ((k + 1) * n) / tailMass T n) atTop (𝓝 1) := by
  have hsmall := mul_tail_div_tailMass_tendsto_zero hT h0 hpos hanti hratio
  have hlim : Tendsto (fun n : ℕ => (k : ℝ) * (((n : ℝ) * T n) / tailMass T n))
      atTop (𝓝 0) := by simpa only [mul_zero] using hsmall.const_mul (k : ℝ)
  have heq (n : ℕ) (hn : 1 ≤ n) :
      1 - tailMass T ((k + 1) * n) / tailMass T n =
        (tailMass T n - tailMass T ((k + 1) * n)) / tailMass T n := by
    rw [sub_div, div_self (tailMass_pos hT h0 hpos hn).ne']
  have herr : Tendsto
      (fun n : ℕ => 1 - tailMass T ((k + 1) * n) / tailMass T n) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ hlim
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      rw [heq n hn]
      exact div_nonneg (tailMass_succ_mul_loss_bounds hT h0 hanti k n).1
        (tailMass_nonneg h0 n)
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      rw [heq n hn]
      calc
        _ ≤ (((k * n : ℕ) : ℝ) * T n) / tailMass T n :=
          div_le_div_of_nonneg_right (tailMass_succ_mul_loss_bounds hT h0 hanti k n).2
            (tailMass_nonneg h0 n)
        _ = (k : ℝ) * (((n : ℝ) * T n) / tailMass T n) := by
          rw [Nat.cast_mul]
          ring
  simpa only [sub_sub_cancel, sub_zero] using
    (tendsto_const_nhds (x := (1 : ℝ))).sub herr

theorem tailMass_mul_div_tendsto_one {T : ℕ → ℝ} (hT : Summable T)
    (h0 : ∀ n, 0 ≤ T n) (hpos : ∀ n : ℕ, 1 ≤ n → 0 < T n)
    (hanti : Antitone T)
    (hratio : ∀ r : ℕ, Tendsto (fun n : ℕ => T (2 ^ r * n) / T n)
      atTop (𝓝 (((2 : ℝ) ^ r)⁻¹))) {K : ℕ} (hK : 1 ≤ K) :
    Tendsto (fun n : ℕ => tailMass T (K * n) / tailMass T n) atTop (𝓝 1) := by
  cases K with
  | zero => simp at hK
  | succ k => simpa only [Nat.succ_eq_add_one] using
      tailMass_succ_mul_div_tendsto_one hT h0 hpos hanti hratio k

/-- Slow variation also holds along any asymptotically proportional index
sequence. Both bounding integer scales are fixed before taking the limit. -/
theorem tailMass_ratio_of_index_ratio {T : ℕ → ℝ} (hT : Summable T)
    (h0 : ∀ n, 0 ≤ T n) (hpos : ∀ n : ℕ, 1 ≤ n → 0 < T n)
    (hanti : Antitone T)
    (hratio : ∀ r : ℕ, Tendsto (fun n : ℕ => T (2 ^ r * n) / T n)
      atTop (𝓝 (((2 : ℝ) ^ r)⁻¹))) {M : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hM : Tendsto M atTop atTop)
    (hMr : Tendsto (fun n : ℕ => (M n : ℝ) / n) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => tailMass T (M n) / tailMass T n) atTop (𝓝 1) := by
  obtain ⟨K, hK⟩ := exists_nat_gt (max c (1 / c))
  have hKc : c < (K : ℝ) := (le_max_left _ _).trans_lt hK
  have hKi : 1 / c < (K : ℝ) := (le_max_right _ _).trans_lt hK
  have hKRpos : 0 < (K : ℝ) := hc.trans hKc
  have hKpos : 0 < K := Nat.cast_pos.mp hKRpos
  have hK1 : 1 ≤ K := hKpos
  have hsmall : 1 / (K : ℝ) < c := by
    apply (div_lt_iff₀ hKRpos).mpr
    simpa only [mul_comm] using (div_lt_iff₀ hc).mp hKi
  have hindices : ∀ᶠ n in atTop, M n ≤ K * n ∧ n ≤ K * M n := by
    filter_upwards [hMr.eventually_le_const hKc, hMr.eventually_const_le hsmall,
      eventually_ge_atTop (1 : ℕ)] with n hupper hlower hn
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn)
    constructor
    · exact_mod_cast (div_le_iff₀ hnR).mp hupper
    · have hr : (n : ℝ) ≤ (K : ℝ) * (M n : ℝ) := by
        calc
          (n : ℝ) = (K : ℝ) * ((1 / (K : ℝ)) * n) := by field_simp [hKRpos.ne']
          _ ≤ (K : ℝ) * (M n : ℝ) :=
            mul_le_mul_of_nonneg_left ((le_div_iff₀ hnR).mp hlower) hKRpos.le
      exact_mod_cast hr
  have hleft := tailMass_mul_div_tendsto_one hT h0 hpos hanti hratio hK1
  have hright : Tendsto (fun n : ℕ => tailMass T (M n) / tailMass T (K * M n))
      atTop (𝓝 1) := by
    have h := ((tailMass_mul_div_tendsto_one hT h0 hpos hanti hratio hK1).comp hM).inv₀
      (show (1 : ℝ) ≠ 0 from one_ne_zero)
    simpa only [Function.comp_def, Pi.inv_apply, inv_div, inv_one] using h
  have hbounds : ∀ᶠ n in atTop,
      tailMass T (K * n) / tailMass T n ≤ tailMass T (M n) / tailMass T n ∧
      tailMass T (M n) / tailMass T n ≤ tailMass T (M n) / tailMass T (K * M n) := by
    filter_upwards [hindices, hM.eventually_ge_atTop 1] with n hn hMn
    constructor
    · exact div_le_div_of_nonneg_right ((tailMass_antitone hT hanti) hn.1)
        (tailMass_nonneg h0 n)
    · have hKM : 1 ≤ K * M n := Nat.mul_pos hKpos
        (lt_of_lt_of_le Nat.zero_lt_one hMn)
      exact div_le_div_of_nonneg_left (tailMass_nonneg h0 (M n))
        (tailMass_pos hT h0 hpos hKM) ((tailMass_antitone hT hanti) hn.2)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hleft hright
    (hbounds.mono (fun _ h => h.1)) (hbounds.mono (fun _ h => h.2))

/-- The primitive tail is slowly varying in the usual floor-index sequence
sense. The underlying dyadic-tail hypothesis remains a separate source bridge. -/
theorem tailMass_floor_mul_div_tendsto_one {T : ℕ → ℝ} (hT : Summable T)
    (h0 : ∀ n, 0 ≤ T n) (hpos : ∀ n : ℕ, 1 ≤ n → 0 < T n)
    (hanti : Antitone T)
    (hratio : ∀ r : ℕ, Tendsto (fun n : ℕ => T (2 ^ r * n) / T n)
      atTop (𝓝 (((2 : ℝ) ^ r)⁻¹))) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => tailMass T ⌊c * n⌋₊ / tailMass T n) atTop (𝓝 1) := by
  apply tailMass_ratio_of_index_ratio hT h0 hpos hanti hratio hc
  · exact tendsto_nat_floor_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hc)
  · exact (tendsto_nat_floor_mul_div_atTop hc.le).comp tendsto_natCast_atTop_atTop

end
end SubcriticalCauchy
