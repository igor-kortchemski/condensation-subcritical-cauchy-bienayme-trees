module

public import SubcriticalCauchy.EquivalentTails
public import SubcriticalCauchy.SlowVariationRounding
public import Mathlib.Analysis.PSeries

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Analytic tail estimates for the increment law

This module proves the discrete Karamata estimate at index minus two. Uniform
slow variation controls initial blocks. Four-adic blocks give a geometric
remainder, so no monotonicity of the slowly varying function is needed.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section

abbrev incrementInvSq (n : ℕ) : ℝ := 1 / (n : ℝ) ^ 2
abbrev incrementTelescopeSq (n : ℕ) : ℝ := 1 / ((n : ℝ) * ((n : ℝ) + 1))

private theorem incrementTelescopeSq_nonneg (n : ℕ) : 0 ≤ incrementTelescopeSq n := by
  unfold incrementTelescopeSq
  positivity

private theorem incrementTelescopeSq_pos {n : ℕ} (hn : 1 ≤ n) : 0 < incrementTelescopeSq n := by
  unfold incrementTelescopeSq
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  positivity

private theorem summable_incrementInvSq : Summable incrementInvSq := by
  simpa only [incrementInvSq] using (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))

private theorem tailMass_incrementTelescopeSq {n : ℕ} (hn : 1 ≤ n) :
    tailMass incrementTelescopeSq n = 1 / (n : ℝ) := by
  have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  apply HasSum.tsum_eq
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun j => incrementTelescopeSq_nonneg (n + j))]
  have heq (m : ℕ) :
      (∑ j ∈ Finset.range m, incrementTelescopeSq (n + j)) =
        1 / (n : ℝ) - 1 / ((n + m : ℕ) : ℝ) := by
    have h := Finset.sum_range_sub' (fun j : ℕ => 1 / ((n + j : ℕ) : ℝ)) m
    convert h using 1
    · apply Finset.sum_congr rfl
      intro j _
      dsimp only [incrementTelescopeSq]
      push_cast
      field_simp
      ring
  simp_rw [heq]
  have hden : Tendsto (fun m : ℕ => ((n + m : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_add, add_comm] using
      (tendsto_atTop_add_const_right atTop (n : ℝ) tendsto_natCast_atTop_atTop)
  have hz : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ) / (n : ℝ))).sub
    (hz.div_atTop hden)

private theorem summable_incrementTelescopeSq : Summable incrementTelescopeSq := by
  apply summable_incrementInvSq.of_nonneg_of_le incrementTelescopeSq_nonneg
  intro n
  cases n with
  | zero => simp [incrementTelescopeSq, incrementInvSq]
  | succ n =>
    have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    dsimp only [incrementTelescopeSq, incrementInvSq]
    rw [div_le_div_iff₀ (mul_pos hn (by linarith)) (sq_pos_of_pos hn)]
    nlinarith

private theorem incrementInvSq_div_incrementTelescopeSq :
    Tendsto (fun n : ℕ => incrementInvSq n / incrementTelescopeSq n) atTop (𝓝 1) := by
  have hz : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h := (tendsto_const_nhds (x := (1 : ℝ))).add
    (hz.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ)))
  have heq : (fun n : ℕ => 1 + 1 / (n : ℝ)) =ᶠ[atTop]
      (fun n : ℕ => incrementInvSq n / incrementTelescopeSq n) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    dsimp only [incrementInvSq, incrementTelescopeSq]
    field_simp [hnR.ne']
  simpa only [add_zero] using h.congr' heq

/-- The usual inverse-square tail is asymptotic to `1 / n`. -/
theorem tailMass_incrementInvSq_div_tendsto_one :
    Tendsto (fun n : ℕ => tailMass incrementInvSq n / (1 / (n : ℝ))) atTop (𝓝 1) := by
  have h := tailMass_div_tendsto_one summable_incrementTelescopeSq summable_incrementInvSq
    incrementTelescopeSq_nonneg (fun _ hn => incrementTelescopeSq_pos hn) incrementInvSq_div_incrementTelescopeSq
  have heq : (fun n : ℕ => tailMass incrementInvSq n / tailMass incrementTelescopeSq n) =ᶠ[atTop]
      (fun n : ℕ => tailMass incrementInvSq n / (1 / (n : ℝ))) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    rw [tailMass_incrementTelescopeSq hn]
  exact h.congr' heq

private theorem incrementInvSq_nonneg (n : ℕ) : 0 ≤ incrementInvSq n := by
  unfold incrementInvSq
  positivity

private theorem tailMass_incrementInvSq_le_two_div :
    ∀ᶠ n : ℕ in atTop, tailMass incrementInvSq n ≤ 2 / (n : ℝ) := by
  have h := tailMass_incrementInvSq_div_tendsto_one.eventually
    (gt_mem_nhds (show (1 : ℝ) < 2 by norm_num))
  filter_upwards [h, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
  simpa only [mul_one_div] using ((div_lt_iff₀ (one_div_pos.mpr hnR)).mp hn).le

abbrev incrementLocalSq (L : ℝ → ℝ) (n : ℕ) : ℝ := L n / (n : ℝ) ^ 2

theorem summable_incrementLocalSq {μ : Measure ℕ} [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1)) : Summable (incrementLocalSq L) := by
  have hsum := summable_localModel_over_nat μ hm hpos hlocal
  apply hsum.of_nonneg_of_le
  · intro n
    cases n with
    | zero => simp [incrementLocalSq]
    | succ n =>
      have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      exact (div_pos (hpos _ hn) (sq_pos_of_pos hn)).le
  · intro n
    cases n with
    | zero => simp [incrementLocalSq]
    | succ n =>
      have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      dsimp only [incrementLocalSq]
      rw [div_le_div_iff₀ (sq_pos_of_pos hn) hn]
      have hLp := (hpos _ hn).le
      nlinarith [sq_nonneg (((n + 1 : ℕ) : ℝ) - 1)]

theorem incrementLocalSq_nonneg {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (n : ℕ) : 0 ≤ incrementLocalSq L n := by
  cases n with
  | zero => simp [incrementLocalSq]
  | succ n =>
    have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    exact (div_pos (hpos _ hn) (sq_pos_of_pos hn)).le

theorem incrementLocalSq_pos {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    {n : ℕ} (hn : 1 ≤ n) : 0 < incrementLocalSq L n := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  exact div_pos (hpos _ hnR) (sq_pos_of_pos hnR)

/-- The eventual four-adic growth bound used for all sufficiently large bases. -/
private theorem eventually_four_adic_bound {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L) :
    ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, N ≤ m → ∀ r : ℕ,
      L ((4 ^ r * m : ℕ) : ℝ) ≤ (2 : ℝ) ^ r * L m := by
  have hu := slowlyVarying_uniform_compact_tail hpos hL hsv
    (a := (1 : ℝ)) (b := (4 : ℝ)) zero_lt_one (by norm_num)
    (tendsto_natCast_atTop_atTop (R := ℝ)) 1 zero_lt_one
  filter_upwards [hu, eventually_ge_atTop (1 : ℕ)] with N hN hN1 m hm r
  induction r with
  | zero => simp
  | succ r ih =>
    have hbase : (N : ℝ) ≤ (4 ^ r * m : ℕ) := by
      exact_mod_cast hm.trans (Nat.le_mul_of_pos_left m (pow_pos (by omega) r))
    have hstep : L ((4 ^ (r + 1) * m : ℕ) : ℝ) ≤ 2 * L ((4 ^ r * m : ℕ) : ℝ) := by
      have hc := hN ((4 ^ r * m : ℕ) : ℝ) 4 hbase (by constructor <;> norm_num)
      rw [show (4 : ℝ) * ((4 ^ r * m : ℕ) : ℝ) = ((4 ^ (r + 1) * m : ℕ) : ℝ) by
        push_cast; ring] at hc
      have hmpos : (0 : ℝ) < ((4 ^ r * m : ℕ) : ℝ) := by
        exact_mod_cast (mul_pos (pow_pos (by omega) r) (by omega : 0 < m))
      have hLm : 0 < L ((4 ^ r * m : ℕ) : ℝ) := hpos _ hmpos
      have hlt : L ((4 ^ (r + 1) * m : ℕ) : ℝ) / L ((4 ^ r * m : ℕ) : ℝ) < (1 : ℝ) + 1 :=
        sub_lt_iff_lt_add.mp (abs_lt.mp hc).2
      exact ((div_lt_iff₀ hLm).mp (by norm_num at hlt ⊢; exact hlt)).le
    calc
      L ((4 ^ (r + 1) * m : ℕ) : ℝ) ≤ 2 * L ((4 ^ r * m : ℕ) : ℝ) := hstep
      _ ≤ 2 * ((2 : ℝ) ^ r * L m) := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (2 : ℝ) ^ (r + 1) * L m := by ring

private theorem eventually_tail_block_bound {μ : Measure ℕ} [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1)) :
    ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, N ≤ m →
      tailMass (incrementLocalSq L) m ≤ 4 * L m / (m : ℝ) +
        tailMass (incrementLocalSq L) (4 * m) := by
  have hu := slowlyVarying_uniform_compact_tail hpos hL hsv
    (a := (1 : ℝ)) (b := (4 : ℝ)) zero_lt_one (by norm_num)
    (tendsto_natCast_atTop_atTop (R := ℝ)) 1 zero_lt_one
  obtain ⟨Nref, href⟩ := eventually_atTop.mp tailMass_incrementInvSq_le_two_div
  filter_upwards [hu, eventually_ge_atTop Nref, eventually_ge_atTop (1 : ℕ)]
    with N hN hNref N1 m hNm
  have hm1 : 1 ≤ m := N1.trans hNm
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hLm : 0 < L m := hpos _ hmR
  have hterm (j : ℕ) (hj : j ∈ Finset.range (3 * m)) :
      incrementLocalSq L (m + j) ≤ 2 * L m * incrementInvSq (m + j) := by
    have hbase : (N : ℝ) ≤ (m : ℝ) := by exact_mod_cast hNm
    have hc : ((m + j : ℕ) : ℝ) / (m : ℝ) ∈ Set.Icc (1 : ℝ) 4 := by
      constructor
      · apply (le_div_iff₀ hmR).mpr
        simp only [one_mul]
        exact_mod_cast Nat.le_add_right m j
      · apply (div_le_iff₀ hmR).mpr
        have hj' := Finset.mem_range.mp hj
        have hjN : m + j ≤ 4 * m := by omega
        exact_mod_cast hjN
    have hr := hN (m : ℝ) (((m + j : ℕ) : ℝ) / (m : ℝ)) hbase hc
    rw [div_mul_cancel₀ _ hmR.ne'] at hr
    have hLupper : L ((m + j : ℕ) : ℝ) ≤ 2 * L m := by
      have hlt : L ((m + j : ℕ) : ℝ) / L m < (1 : ℝ) + 1 :=
        sub_lt_iff_lt_add.mp (abs_lt.mp hr).2
      exact ((div_lt_iff₀ hLm).mp (by norm_num at hlt ⊢; exact hlt)).le
    dsimp only [incrementLocalSq, incrementInvSq]
    calc
      L ((m + j : ℕ) : ℝ) / ((m + j : ℕ) : ℝ) ^ 2 ≤ (2 * L m) / ((m + j : ℕ) : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hLupper (sq_nonneg _)
      _ = 2 * L m * (1 / ((m + j : ℕ) : ℝ) ^ 2) := by ring
  have hsplit := tailMass_split (summable_incrementLocalSq (μ := μ) hm hpos hlocal) m (3 * m)
  rw [show m + 3 * m = 4 * m by ring] at hsplit
  have hsum : (∑ j ∈ Finset.range (3 * m), incrementLocalSq L (m + j)) ≤
      2 * L m * tailMass incrementInvSq m := by
    calc
      _ ≤ ∑ j ∈ Finset.range (3 * m), 2 * L m * incrementInvSq (m + j) :=
        Finset.sum_le_sum hterm
      _ = 2 * L m * (∑ j ∈ Finset.range (3 * m), incrementInvSq (m + j)) := by
        rw [Finset.mul_sum]
      _ ≤ 2 * L m * tailMass incrementInvSq m := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hLm.le)
        rw [tailMass_split summable_incrementInvSq m (3 * m)]
        have : 0 ≤ tailMass incrementInvSq (m + 3 * m) := tailMass_nonneg incrementInvSq_nonneg _
        linarith
  have hsum' : (∑ j ∈ Finset.range (3 * m), incrementLocalSq L (m + j)) ≤ 4 * L m / (m : ℝ) := by
    calc
      _ ≤ 2 * L m * tailMass incrementInvSq m := hsum
      _ ≤ 2 * L m * (2 / (m : ℝ)) :=
        mul_le_mul_of_nonneg_left (href m (hNref.trans hNm)) (mul_nonneg (by norm_num) hLm.le)
      _ = 4 * L m / (m : ℝ) := by ring
  rw [hsplit]
  linarith

/-- A uniform linear bound for the inverse-square slowly varying tail. -/
private theorem eventually_tailMass_incrementLocalSq_le {μ : Measure ℕ} [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1)) :
    ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, N ≤ m → ∀ r : ℕ,
      tailMass (incrementLocalSq L) (4 ^ r * m) ≤
        8 * ((1 : ℝ) / 2) ^ r * L m / (m : ℝ) := by
  have hs := summable_incrementLocalSq (μ := μ) hm hpos hlocal
  have hmain : ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, N ≤ m →
      tailMass (incrementLocalSq L) m ≤ 8 * L m / (m : ℝ) := by
    filter_upwards [eventually_tail_block_bound (μ := μ) hm hpos hL hsv hlocal,
      eventually_four_adic_bound hpos hL hsv, eventually_ge_atTop (1 : ℕ)]
      with N hblock hgrowth N1 m hNm
    have hm1 : 1 ≤ m := N1.trans hNm
    have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
    have hLm : 0 < L m := hpos _ hmR
    have hpartial (K : ℕ) : tailMass (incrementLocalSq L) m ≤
        8 * (1 - ((1 : ℝ) / 2) ^ K) * L m / (m : ℝ) +
          tailMass (incrementLocalSq L) (4 ^ K * m) := by
      induction K with
      | zero => simp
      | succ K ih =>
        have hb := hblock (4 ^ K * m) (hNm.trans (Nat.le_mul_of_pos_left m (pow_pos (by omega) K)))
        rw [show 4 * (4 ^ K * m) = 4 ^ (K + 1) * m by ring] at hb
        have hg := hgrowth m hNm K
        calc
          tailMass (incrementLocalSq L) m ≤
              8 * (1 - ((1 : ℝ) / 2) ^ K) * L m / (m : ℝ) +
                tailMass (incrementLocalSq L) (4 ^ K * m) := ih
          _ ≤ 8 * (1 - ((1 : ℝ) / 2) ^ K) * L m / (m : ℝ) +
                (4 * L ((4 ^ K * m : ℕ) : ℝ) / ((4 ^ K * m : ℕ) : ℝ) +
                  tailMass (incrementLocalSq L) (4 ^ (K + 1) * m)) := by linarith [hb]
          _ ≤ 8 * (1 - ((1 : ℝ) / 2) ^ K) * L m / (m : ℝ) +
                (4 * ((2 : ℝ) ^ K * L m) / ((4 ^ K * m : ℕ) : ℝ) +
                  tailMass (incrementLocalSq L) (4 ^ (K + 1) * m)) := by
            gcongr
          _ = 8 * (1 - ((1 : ℝ) / 2) ^ (K + 1)) * L m / (m : ℝ) +
                tailMass (incrementLocalSq L) (4 ^ (K + 1) * m) := by
            have hpow : (4 : ℝ) ^ K * ((1 : ℝ) / 2) ^ K = 2 ^ K := by
              rw [← mul_pow]
              norm_num
            push_cast
            field_simp [hmR.ne']
            ring_nf
            nlinarith [hpow]
    have hlim : Tendsto (fun K : ℕ =>
        8 * (1 - ((1 : ℝ) / 2) ^ K) * L m / (m : ℝ) +
          tailMass (incrementLocalSq L) (4 ^ K * m)) atTop (𝓝 (8 * L m / (m : ℝ))) := by
      have hpow : Tendsto (fun K : ℕ => ((1 : ℝ) / 2) ^ K) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      have hidx : Tendsto (fun K : ℕ => 4 ^ K * m) atTop atTop := by
        apply tendsto_atTop_mono (fun K => Nat.le_mul_of_pos_right (4 ^ K) hm1)
        exact tendsto_pow_atTop_atTop_of_one_lt (by omega)
      have htail := (tailMass_tendsto_zero (incrementLocalSq L)).comp hidx
      have hconst : Tendsto (fun K : ℕ =>
          8 * (1 - ((1 : ℝ) / 2) ^ K) * L m / (m : ℝ)) atTop
          (𝓝 (8 * L m / (m : ℝ))) := by
        convert ((tendsto_const_nhds (x := (8 : ℝ))).mul
          ((tendsto_const_nhds (x := (1 : ℝ))).sub hpow)).mul_const (L m) |>.div_const (m : ℝ) using 1
        all_goals simp
      simpa using hconst.add htail
    exact ge_of_tendsto hlim (Eventually.of_forall hpartial)
  filter_upwards [hmain, eventually_four_adic_bound hpos hL hsv, eventually_ge_atTop (1 : ℕ)]
    with N hN hgrowth N1 m hNm r
  have hm' : N ≤ 4 ^ r * m := hNm.trans (Nat.le_mul_of_pos_left m (pow_pos (by omega) r))
  have hbase := hN (4 ^ r * m) hm'
  have hm1 : 1 ≤ m := N1.trans hNm
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  calc
    tailMass (incrementLocalSq L) (4 ^ r * m) ≤ 8 * L ((4 ^ r * m : ℕ) : ℝ) / ((4 ^ r * m : ℕ) : ℝ) := hbase
    _ ≤ 8 * ((2 : ℝ) ^ r * L m) / ((4 ^ r * m : ℕ) : ℝ) := by
      gcongr
      exact hgrowth m hNm r
    _ = 8 * ((1 : ℝ) / 2) ^ r * L m / (m : ℝ) := by
      push_cast
      rw [div_pow, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
      field_simp [hmR.ne']
      ring


/-- Uniform comparison of an initial block with its inverse-square model. -/
private theorem eventually_initial_block_bounds {μ : Measure ℕ} [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1)) {K : ℕ} (hK : 1 ≤ K) (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ n : ℕ in atTop,
      (1 - τ) * L n * (tailMass incrementInvSq n - tailMass incrementInvSq (K * n)) ≤
        tailMass (incrementLocalSq L) n - tailMass (incrementLocalSq L) (K * n) ∧
      tailMass (incrementLocalSq L) n - tailMass (incrementLocalSq L) (K * n) ≤
        (1 + τ) * L n * (tailMass incrementInvSq n - tailMass incrementInvSq (K * n)) := by
  have hs := summable_incrementLocalSq (μ := μ) hm hpos hlocal
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hu := slowlyVarying_uniform_compact_tail hpos hL hsv
    (a := (1 : ℝ)) (b := (K : ℝ)) zero_lt_one (by exact_mod_cast hK)
    (tendsto_natCast_atTop_atTop (R := ℝ)) τ hτ
  filter_upwards [hu, eventually_ge_atTop (1 : ℕ)] with n hN hn
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hLn : 0 < L n := hpos _ hnR
  have hterm (j : ℕ) (hj : j ∈ Finset.range ((K - 1) * n)) :
      (1 - τ) * (L n * incrementInvSq (n + j)) ≤ incrementLocalSq L (n + j) ∧
      incrementLocalSq L (n + j) ≤ (1 + τ) * (L n * incrementInvSq (n + j)) := by
    have hbase : (n : ℝ) ≤ n := le_rfl
    have hc : ((n + j : ℕ) : ℝ) / (n : ℝ) ∈ Set.Icc (1 : ℝ) (K : ℝ) := by
      constructor
      · apply (le_div_iff₀ hnR).mpr
        simp only [one_mul]
        exact_mod_cast Nat.le_add_right n j
      · apply (div_le_iff₀ hnR).mpr
        have hjN : n + j ≤ K * n := by
          have hj' := Finset.mem_range.mp hj
          calc
            n + j ≤ n + (K - 1) * n := Nat.add_le_add_left hj'.le n
            _ = (1 + (K - 1)) * n := by ring
            _ = K * n := by congr 1; omega
        exact_mod_cast hjN
    have hr := hN (n : ℝ) (((n + j : ℕ) : ℝ) / (n : ℝ)) hbase hc
    rw [div_mul_cancel₀ _ hnR.ne'] at hr
    have hkR : (0 : ℝ) < ((n + j : ℕ) : ℝ) := by positivity
    have hmodel : 0 ≤ L n * incrementInvSq (n + j) :=
      mul_nonneg hLn.le (incrementInvSq_nonneg _)
    have hrewrite : incrementLocalSq L (n + j) =
        (L ((n + j : ℕ) : ℝ) / L n) * (L n * incrementInvSq (n + j)) := by
      dsimp only [incrementLocalSq, incrementInvSq]
      field_simp [hLn.ne']
    obtain ⟨hlo, hhi⟩ := abs_lt.mp hr
    rw [hrewrite]
    constructor
    · apply mul_le_mul_of_nonneg_right _ hmodel
      linarith
    · apply mul_le_mul_of_nonneg_right _ hmodel
      linarith
  have hsplit := tailMass_split hs n ((K - 1) * n)
  have hsplit0 := tailMass_split summable_incrementInvSq n ((K - 1) * n)
  have hend : n + (K - 1) * n = K * n := by
    calc
      n + (K - 1) * n = (1 + (K - 1)) * n := by ring
      _ = K * n := by congr 1; omega
  rw [hend] at hsplit hsplit0
  constructor
  · have hsum := Finset.sum_le_sum (fun j hj => (hterm j hj).1)
    simp_rw [← mul_assoc] at hsum
    rw [← Finset.mul_sum] at hsum
    calc
      _ = (1 - τ) * L n * (∑ j ∈ Finset.range ((K - 1) * n), incrementInvSq (n + j)) := by
        rw [hsplit0]
        ring
      _ ≤ _ := hsum
      _ = _ := by rw [hsplit]; ring
  · have hsum := Finset.sum_le_sum (fun j hj => (hterm j hj).2)
    simp_rw [← mul_assoc] at hsum
    rw [← Finset.mul_sum] at hsum
    calc
      _ = (∑ j ∈ Finset.range ((K - 1) * n), incrementLocalSq L (n + j)) := by
        rw [hsplit]
        ring
      _ ≤ _ := hsum
      _ = _ := by rw [hsplit0]; ring


private theorem tailMass_incrementInvSq_block_div_tendsto {K : ℕ} (hK : 1 ≤ K) :
    Tendsto (fun n : ℕ =>
      (tailMass incrementInvSq n - tailMass incrementInvSq (K * n)) / (1 / (n : ℝ)))
      atTop (𝓝 (1 - 1 / (K : ℝ))) := by
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hidx : Tendsto (fun n : ℕ => K * n) atTop atTop := by
    apply tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left n (by omega : 0 < K))
    exact tendsto_id
  have hfirst := tailMass_incrementInvSq_div_tendsto_one
  have hsecond0 := tailMass_incrementInvSq_div_tendsto_one.comp hidx
  have hsecond : Tendsto (fun n : ℕ => tailMass incrementInvSq (K * n) / (1 / (n : ℝ)))
      atTop (𝓝 (1 / (K : ℝ))) := by
    have hh := hsecond0.div_const (K : ℝ)
    have heq : (fun n : ℕ => (tailMass incrementInvSq (K * n) / (1 / ((K * n : ℕ) : ℝ))) / (K : ℝ)) =ᶠ[atTop]
        (fun n : ℕ => tailMass incrementInvSq (K * n) / (1 / (n : ℝ))) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
      push_cast
      field_simp [hKR.ne', hnR.ne']
    simpa only [Function.comp_def, one_div, inv_inv] using hh.congr' heq
  simpa only [sub_div] using hfirst.sub hsecond

private theorem initial_block_div_tendsto {μ : Measure ℕ} [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1)) {K : ℕ} (hK : 1 ≤ K) :
    Tendsto (fun n : ℕ =>
      (tailMass (incrementLocalSq L) n - tailMass (incrementLocalSq L) (K * n)) /
        (L n / (n : ℝ))) atTop (𝓝 (1 - 1 / (K : ℝ))) := by
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hc0 : 0 ≤ 1 - 1 / (K : ℝ) := by
    have : 1 / (K : ℝ) ≤ 1 := (div_le_iff₀ hKR).mpr (by simpa using (show (1 : ℝ) ≤ K by exact_mod_cast hK))
    linarith
  have hc1 : 1 - 1 / (K : ℝ) ≤ 1 := by
    have := one_div_pos.mpr hKR
    linarith
  have href := tailMass_incrementInvSq_block_div_tendsto hK
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := min (ε / 9) (1 / 4)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδε : 9 * δ ≤ ε := by
    have : δ ≤ ε / 9 := min_le_left _ _
    linarith
  have hδ1 : δ ≤ 1 / 4 := min_le_right _ _
  have hg := Metric.tendsto_nhds.mp href δ hδ
  filter_upwards [eventually_initial_block_bounds (μ := μ) hm hpos hL hsv hlocal hK δ hδ,
    hg, eventually_ge_atTop (1 : ℕ)] with n hb hg hn
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hLn : 0 < L n := hpos _ hnR
  have hd : 0 < L n / (n : ℝ) := div_pos hLn hnR
  let g := (tailMass incrementInvSq n - tailMass incrementInvSq (K * n)) / (1 / (n : ℝ))
  let B := (tailMass (incrementLocalSq L) n - tailMass (incrementLocalSq L) (K * n)) /
    (L n / (n : ℝ))
  have hlo : (1 - δ) * g ≤ B := by
    have h := div_le_div_of_nonneg_right hb.1 hd.le
    dsimp only [g, B]
    convert h using 1
    all_goals field_simp [hLn.ne', hnR.ne']
  have hhi : B ≤ (1 + δ) * g := by
    have h := div_le_div_of_nonneg_right hb.2 hd.le
    dsimp only [g, B]
    convert h using 1
    all_goals field_simp [hLn.ne', hnR.ne']
  change dist B (1 - 1 / (K : ℝ)) < ε
  change dist g (1 - 1 / (K : ℝ)) < δ at hg
  rw [Real.dist_eq] at hg ⊢
  have hg' := abs_lt.mp hg
  apply abs_lt.mpr
  constructor <;> nlinarith [hg'.1, hg'.2]

/-- The discrete Karamata tail estimate at index minus two. -/
theorem tailMass_incrementLocalSq_div_tendsto_one
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ ≠ ∞)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => tailMass (incrementLocalSq L) n / (L n / (n : ℝ)))
      atTop (𝓝 1) := by
  have hs : Summable (incrementLocalSq L) := summable_incrementLocalSq (μ := μ) hm hpos hlocal
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hp : Tendsto (fun r : ℕ => ((1 : ℝ) / 4) ^ (r + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
      (tendsto_add_atTop_nat 1)
  have hq0 : Tendsto (fun r : ℕ => ((1 : ℝ) / 2) ^ (r + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
      (tendsto_add_atTop_nat 1)
  have hq : Tendsto (fun r : ℕ => 8 * ((1 : ℝ) / 2) ^ (r + 1)) atTop (𝓝 0) := by
    simpa using hq0.const_mul (8 : ℝ)
  have hev : ∀ᶠ r : ℕ in atTop,
      ((1 : ℝ) / 4) ^ (r + 1) + 8 * ((1 : ℝ) / 2) ^ (r + 1) < ε / 4 := by
    have h := (hp.add hq).eventually (gt_mem_nhds (show (0 : ℝ) + 0 < ε / 4 by
      simpa only [add_zero] using (show (0 : ℝ) < ε / 4 by positivity)))
    simpa only [add_zero] using h
  obtain ⟨r, hrsum⟩ := hev.exists
  let K := 4 ^ (r + 1)
  have hK : 1 ≤ K := Nat.one_le_pow _ _ (by omega)
  have hKform : (1 : ℝ) / (K : ℝ) = ((1 : ℝ) / 4) ^ (r + 1) := by
    dsimp only [K]
    push_cast
    rw [div_pow]
    norm_num
  have hhead := (initial_block_div_tendsto (μ := μ) hm hpos hL hsv hlocal hK).eventually
    (Metric.ball_mem_nhds _ (show (0 : ℝ) < ε / 4 by positivity))
  have hrembound := eventually_tailMass_incrementLocalSq_le (μ := μ) hm hpos hL hsv hlocal
  filter_upwards [hhead, hrembound, eventually_ge_atTop (1 : ℕ)] with n hh hrem hn
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hLn : 0 < L n := hpos _ hnR
  have hd : 0 < L n / (n : ℝ) := div_pos hLn hnR
  have hremK := hrem n le_rfl (r + 1)
  have hnonneg : 0 ≤ tailMass (incrementLocalSq L) (K * n) / (L n / (n : ℝ)) := by
    apply div_nonneg _ hd.le
    apply tailMass_nonneg
    exact incrementLocalSq_nonneg hpos
  have hsmall : tailMass (incrementLocalSq L) (K * n) / (L n / (n : ℝ)) ≤
      8 * ((1 : ℝ) / 2) ^ (r + 1) := by
    apply (div_le_iff₀ hd).mpr
    simpa only [K, mul_div_assoc] using hremK
  have hdecomp : tailMass (incrementLocalSq L) n / (L n / (n : ℝ)) =
      (tailMass (incrementLocalSq L) n - tailMass (incrementLocalSq L) (K * n)) /
          (L n / (n : ℝ)) + tailMass (incrementLocalSq L) (K * n) / (L n / (n : ℝ)) := by
    ring
  have hh' : |(tailMass (incrementLocalSq L) n - tailMass (incrementLocalSq L) (K * n)) /
      (L n / (n : ℝ)) - (1 - 1 / (K : ℝ))| < ε / 4 := by
    simpa only [Real.dist_eq, Metric.mem_ball] using hh
  rw [Real.dist_eq, hdecomp]
  apply abs_lt.mpr
  have hp' := abs_lt.mp hh'
  have hK0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hKbound : 0 ≤ 1 / (K : ℝ) := by positivity
  have hqnonneg : 0 ≤ 8 * ((1 : ℝ) / 2) ^ (r + 1) := by positivity
  have hKsmall : 1 / (K : ℝ) < ε / 4 := by rw [hKform]; linarith
  have hpnonneg : 0 ≤ ((1 : ℝ) / 4) ^ (r + 1) := by positivity
  have hRsmall : 8 * ((1 : ℝ) / 2) ^ (r + 1) < ε / 4 := by linarith
  constructor <;> nlinarith


end
end SubcriticalCauchy.Bienayme
