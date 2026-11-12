module

public import SubcriticalCauchy.PaperRoute.BergerFukNagaevAux
public import SubcriticalCauchy.IncrementTailAsymptotics
public import SubcriticalCauchy.DeletedIncrements

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

@[expose] public section

open MeasureTheory Filter
open scoped Topology ENNReal BigOperators

namespace SubcriticalCauchy.Bienayme

private theorem fukNagaev_exponent_comparisons {z y B s : ℝ}
    (hy : 2 ≤ y) (hz : 0 ≤ z) (hBdef : B = y + 1) (hsdef : s = 3 * z / 4) :
    s / B ≤ z / y ∧ z / (2 * y) ≤ s / B := by
  have hy0 : 0 < y := by linarith
  have hB : 0 < B := by rw [hBdef]; linarith
  constructor
  · apply (div_le_div_iff₀ hB hy0).mpr
    calc
      s * y = z * (3 * y / 4) := by rw [hsdef]; ring
      _ ≤ z * B := mul_le_mul_of_nonneg_left (by rw [hBdef]; linarith) hz
  · apply (le_div_iff₀ hB).mpr
    calc
      z / (2 * y) * B = (z / y) * (B / 2) := by field_simp [hy0.ne']
      _ ≤ (z / y) * (3 * y / 4) :=
        mul_le_mul_of_nonneg_left (by rw [hBdef]; linarith) (div_nonneg hz hy0.le)
      _ = s := by rw [hsdef]; field_simp [hy0.ne']

private theorem fukNagaev_negative_rpow_comparison {R r u v : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (hu : 0 ≤ u) (huv : u ≤ v) :
    (1 + R) ^ (-v) ≤ (1 + r) ^ (-u) := by
  calc
    (1 + R) ^ (-v) ≤ (1 + R) ^ (-u) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (neg_le_neg huv)
    _ ≤ (1 + r) ^ (-u) := by
      rw [Real.rpow_def_of_pos (by linarith : 0 < 1 + R) (-u),
        Real.rpow_def_of_pos (by linarith : 0 < 1 + r) (-u)]
      apply Real.exp_le_exp.mpr
      have hlog : Real.log (1 + r) ≤ Real.log (1 + R) :=
        Real.log_le_log (by linarith) (by linarith : 1 + r ≤ 1 + R)
      have hl : 0 ≤ Real.log (1 + r) := Real.log_nonneg (by linarith)
      have h2 : Real.log (1 + R) * (-u) ≤ Real.log (1 + r) * (-u) := by
        have hh := mul_le_mul_of_nonpos_right hlog (neg_nonpos.mpr hu)
        convert hh using 1
      exact h2

theorem incrementSum_fukNagaev
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ < 1)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2)) atTop (𝓝 1))
    {a : ℕ → ℝ}
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal) atTop (𝓝 1)) :
    ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, j ≤ n →
      ∀ z y : ℝ, K * a n ≤ z → a n ≤ y → y ≤ z →
      ((Measure.pi fun _ : Fin j => incrementLaw μ)
          {x | z ≤ (∑ i, (x i : ℝ)) - j * truncatedIncrementMean μ (a n) ∧
               ∀ i, (x i : ℝ) ≤ y}).toReal
        ≤ Real.exp (z / y) * (1 + c * z / ((n : ℝ) * L y)) ^ (-(z / (2 * y))) := by
  obtain ⟨C, hC, A0, hA0⟩ := berger_annular_tail_le μ hm hpos hL hsv hlocal
  obtain ⟨D0, hD0, A1, hA1⟩ := berger_second_moment_real_le μ hm hpos hL hsv hlocal
  let D := D0 + 2
  have hD : 0 < D := by dsimp [D]; positivity
  let c := 3 / (4 * D)
  let K := 1 + 16 * (2 * C) ^ 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hat : Tendsto a atTop atTop := scaling_tendsto_atTop μ ⟨hm, L, hpos, hsv, hlocal⟩ ha
  have hscale : Tendsto (fun n : ℕ => (n : ℝ) * L (a n) / a n) atTop (𝓝 1) := by
    have h := (scaling_div_mul_tendsto_one μ hm hpos hL hsv hlocal ha).inv₀ one_ne_zero
    simpa only [Pi.inv_apply, inv_div, inv_one] using h
  have hs2 : ∀ᶠ n : ℕ in atTop, (n : ℝ) * L (a n) / a n < 2 :=
    (tendsto_order.1 hscale).2 2 (by norm_num)
  have hreal := berger_mul_slowlyVarying_atTop_real hpos hL hsv tendsto_id
  obtain ⟨A2, hA2⟩ := eventually_atTop.1 (hreal.eventually_ge_atTop 1)
  have hev : ∀ᶠ n : ℕ in atTop,
      max 2 (max A0 (max A1 A2)) ≤ a n ∧ (n : ℝ) * L (a n) / a n < 2 := by
    filter_upwards [hat.eventually_ge_atTop (max 2 (max A0 (max A1 A2))), hs2] with n hn hs
    exact ⟨hn, hs⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hev.and (eventually_ge_atTop 1))
  refine ⟨c, hc, K, hK, N, ?_⟩
  intro n hn j hjn z y hKz hay hyz
  have hna := (hN n hn).1.1
  have hn0 : 0 < n := (hN n hn).2
  have ha2 : 2 ≤ a n := (le_max_left _ _).trans hna
  have ha0 : 0 < a n := by linarith
  have haA0 : A0 ≤ a n := (le_max_left A0 (max A1 A2)).trans ((le_max_right 2 _).trans hna)
  have haA1 : A1 ≤ a n := (le_max_left A1 A2).trans ((le_max_right A0 _).trans ((le_max_right 2 _).trans hna))
  have haA2 : A2 ≤ a n := (le_max_right A1 A2).trans ((le_max_right A0 _).trans ((le_max_right 2 _).trans hna))
  have hy0 : 0 < y := ha0.trans_le hay
  have hy2 : 2 ≤ y := ha2.trans hay
  have hLy : 0 < L y := hpos _ hy0
  have hLa : 0 < L (a n) := hpos _ ha0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hz0 : 0 < z := by
    have hKa : 0 < K * a n := mul_pos hK ha0
    linarith
  have hyLy : 1 ≤ y * L y := hA2 y (haA2.trans hay)
  have hnLa : (n : ℝ) * L (a n) ≤ 2 * a n := by
    have hh := (hN n hn).1.2
    exact (div_le_iff₀ ha0).mp hh.le
  let Y := ⌊y⌋₊ + 2
  let B := y + 1
  let q := truncatedIncrementMean μ y + 1
  let V := D * y * L y
  let s := 3 * z / 4
  let R := s * B / ((n : ℝ) * V)
  let r := c * z / ((n : ℝ) * L y)
  let t := Real.log (1 + R) / B
  have hB : 0 < B := by dsimp [B]; linarith
  have hB2 : B ≤ 2 * y := by dsimp [B]; linarith
  have hV : 0 < V := by dsimp [V]; positivity
  have hs : 0 < s := by dsimp [s]; positivity
  have hR : 0 < R := by
    dsimp [R]
    exact div_pos (mul_pos hs hB) (mul_pos hnR hV)
  have hr : 0 < r := by dsimp [r]; positivity
  have ht : 0 ≤ t := by
    dsimp [t]
    exact div_nonneg (Real.log_nonneg (by linarith)) hB.le
  have hY : ∀ k : ℕ, k < Y → (k : ℝ) ≤ B := by
    intro k hk
    have hkk : k ≤ ⌊y⌋₊ + 1 := by dsimp [Y] at hk; omega
    have hkc : (k : ℝ) ≤ (⌊y⌋₊ + 1 : ℕ) := by exact_mod_cast hkk
    have hfl : ((⌊y⌋₊ + 1 : ℕ) : ℝ) ≤ B := by
      dsimp [B]
      norm_num only [Nat.cast_add, Nat.cast_one]
      exact add_le_add (Nat.floor_le hy0.le) le_rfl
    exact hkc.trans hfl
  have hcut : ∀ k : ℕ, (k < Y ↔ |offspringIncrement k| ≤ y) := by
    intro k
    have hg := abs_increment_gt_iff_floor_add_two_le (k := k) (show 1 ≤ y by linarith)
    dsimp [Y]
    rw [← not_lt, hg]
    exact lt_iff_not_ge
  have hqint : (∫ k : ℕ, (if k < Y then (k : ℝ) else 1) ∂μ) = q := by
    have hi : (fun k : ℕ => if k < Y then (k : ℝ) else 1) = fun k =>
        (if |offspringIncrement k| ≤ y then offspringIncrement k else 0) +
          1 := by
      funext k
      by_cases hk : k < Y
      · have hyk := (hcut k).mp hk
        rw [ite_eq_left hk, ite_eq_left hyk]
        simp [offspringIncrement]
      · have hyk : ¬ |offspringIncrement k| ≤ y := fun h => hk ((hcut k).mpr h)
        rw [ite_eq_right hk, ite_eq_right hyk]
        norm_num
    rw [hi, integral_add (integrable_truncatedIncrement μ (ne_top_of_lt hm) y)
      (integrable_const 1), integral_const]
    simp only [truncatedIncrementMean, q]
    simp
  have hq0 : 0 ≤ q := by
    rw [← hqint]
    refine integral_nonneg (fun k => ?_)
    split_ifs
    · exact Nat.cast_nonneg _
    · norm_num
  have hq1 : q ≤ 1 := by
    rw [← hqint]
    have hm1 : (offspringMean μ).toReal < 1 := by
      have hf := ne_top_of_lt hm
      simpa using (ENNReal.toReal_lt_toReal hf ENNReal.one_ne_top).mpr hm
    have hint : Integrable (fun k : ℕ => if k < Y then (k : ℝ) else 1) μ := by
      refine Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable ((Y : ℝ) + 1) ?_
      filter_upwards [] with k
      by_cases hk : k < Y
      · simp only [hk, ite_true, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg k : (0:ℝ) ≤ k)]
        have hkY : (k : ℝ) ≤ Y := by exact_mod_cast hk.le
        linarith
      · simp [hk]
    calc
      _ ≤ ∫ k : ℕ, (k : ℝ) ∂μ := by
        apply integral_mono hint (integrable_natCast μ (ne_top_of_lt hm))
        intro k
        by_cases hk : k < Y
        · simp [hk]
        · simp [hk, show 1 ≤ k by omega]
      _ = (offspringMean μ).toReal := integral_natCast μ
      _ ≤ 1 := hm1.le
  have hmoment : (∑ k ∈ Finset.range Y, (k : ℝ) ^ 2 * (μ {k}).toReal) + (1 ^ 2 + q ^ 2) ≤ V := by
    have hS := hA1 y (haA1.trans hay)
    have hYY : Finset.range Y = Finset.range (⌊y⌋₊ + 2) := rfl
    have hV0 : D0 * y * L y + 1 + q ^ 2 ≤ V := by
      have hq2 : q ^ 2 ≤ 1 := by nlinarith only [hq0, hq1]
      dsimp [V, D]
      nlinarith only [hq2, hyLy]
    rw [hYY]
    linarith
  have hmgf := berger_truncated_mgf_bennett_le μ Y 1 q t B (by norm_num) hq0 ht hB (by linarith) hqint hY
  have hmarkov := berger_pi_truncated_probability_le μ Y j 1 t s q (by norm_num)
    (by exact_mod_cast (show (1:ℕ) ≤ Y by dsimp [Y]; omega)) ht
  have hexp_nonneg : 0 ≤ Real.exp (t * B) - 1 - t * B := by
    linarith [Real.add_one_le_exp (t * B)]
  have htB : t * B = Real.log (1 + R) := by dsimp [t]; field_simp [hB.ne']
  have hMpow : (∫ k : ℕ, (if k < Y then Real.exp (t * ((k : ℝ) - q))
      else Real.exp (t * (1 - q))) ∂μ) ^ j ≤ Real.exp ((j : ℝ) * ((Real.exp (t * B) - 1 - t * B) / B ^ 2) * V) := by
    have hphi : (Real.exp (t * B) - 1 - t * B) / B ^ 2 ≤
        (Real.exp (t * B) - 1 - t * B) / B ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg B)
      have htB0 : 0 ≤ t * B := mul_nonneg ht hB.le
      linarith
    have hbaseV : (∫ k : ℕ, (if k < Y then Real.exp (t * ((k : ℝ) - q))
        else Real.exp (t * (1 - q))) ∂μ) ≤ 1 + ((Real.exp (t * B) - 1 - t * B) / B ^ 2) * V := by
      calc
        _ ≤ 1 + (Real.exp (t * B) - 1 - t * B) / B ^ 2 *
            ((∑ k ∈ Finset.range Y, (k : ℝ) ^ 2 * (μ {k}).toReal) + (1 ^ 2 + q ^ 2)) := hmgf
        _ ≤ 1 + ((Real.exp (t * B) - 1 - t * B) / B ^ 2) * V := by
          apply add_le_add le_rfl
          calc
            _ ≤ ((Real.exp (t * B) - 1 - t * B) / B ^ 2) *
                ((∑ k ∈ Finset.range Y, (k : ℝ) ^ 2 * (μ {k}).toReal) + (1 ^ 2 + q ^ 2)) :=
              mul_le_mul_of_nonneg_right hphi
                (add_nonneg (Finset.sum_nonneg (fun k _ => mul_nonneg (sq_nonneg _) ENNReal.toReal_nonneg))
                  (add_nonneg (sq_nonneg 1) (sq_nonneg q)))
            _ ≤ _ := mul_le_mul_of_nonneg_left hmoment
              (div_nonneg hexp_nonneg (sq_nonneg B))
    have hA : 0 ≤ ((Real.exp (t * B) - 1 - t * B) / B ^ 2) * V :=
      mul_nonneg (div_nonneg hexp_nonneg (sq_nonneg B)) hV.le
    have hbaseExp : 1 + ((Real.exp (t * B) - 1 - t * B) / B ^ 2) * V ≤
        Real.exp (((Real.exp (t * B) - 1 - t * B) / B ^ 2) * V) := by
      simpa only [add_comm] using Real.add_one_le_exp (((Real.exp (t * B) - 1 - t * B) / B ^ 2) * V)
    calc
      _ ≤ (1 + ((Real.exp (t * B) - 1 - t * B) / B ^ 2) * V) ^ j :=
        pow_le_pow_left₀ (by positivity) hbaseV j
      _ ≤ (Real.exp (((Real.exp (t * B) - 1 - t * B) / B ^ 2) * V)) ^ j :=
        pow_le_pow_left₀ (by positivity) hbaseExp j
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have htaildiff : truncatedIncrementMean μ y - truncatedIncrementMean μ (a n) =
      tailIncrementMean μ (a n) - tailIncrementMean μ y := by
    have h1 := truncated_add_tail_incrementMean μ (ne_top_of_lt hm) y
    have h2 := truncated_add_tail_incrementMean μ (ne_top_of_lt hm) (a n)
    linarith
  have hd0 : 0 ≤ truncatedIncrementMean μ y - truncatedIncrementMean μ (a n) := by
    unfold truncatedIncrementMean
    rw [← integral_sub (integrable_truncatedIncrement μ (ne_top_of_lt hm) y)
      (integrable_truncatedIncrement μ (ne_top_of_lt hm) (a n))]
    apply integral_nonneg
    intro k
    by_cases hk : |offspringIncrement k| ≤ a n
    · simp [hk, hk.trans hay]
    · simp only [hk, ite_false]
      split_ifs with hk'
      · cases k with
        | zero =>
            simp [offspringIncrement] at hk hk'
            linarith
        | succ k => simp [offspringIncrement]
      · simp
  have hnDelta : (n : ℝ) * (truncatedIncrementMean μ y - truncatedIncrementMean μ (a n)) ≤ z / 4 := by
    rw [htaildiff]
    have hann := hA0 (a n) y haA0 hay
    let w := Real.sqrt (z / a n)
    have hw : 0 ≤ w := Real.sqrt_nonneg _
    have hw2 : w ^ 2 = z / a n := Real.sq_sqrt (div_nonneg hz0.le ha0.le)
    have hya : Real.sqrt (y / a n) ≤ w := Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hyz ha0.le)
    have hmulnon : 0 ≤ (n : ℝ) * L (a n) := by positivity
    calc
      _ ≤ (n : ℝ) * (C * L (a n) * Real.sqrt (y / a n)) :=
        mul_le_mul_of_nonneg_left hann hnR.le
      _ = C * ((n : ℝ) * L (a n)) * Real.sqrt (y / a n) := by ring
      _ ≤ C * (2 * a n) * w := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hnLa hC.le) hya
          (Real.sqrt_nonneg _) (by positivity)
      _ ≤ z / 4 := by
        have hK0 : (8 * C) ^ 2 ≤ z / a n := by
          apply (le_div_iff₀ ha0).mpr
          dsimp [K] at hKz
          nlinarith [sq_nonneg C]
        have hw8 : 8 * C ≤ w :=
          (sq_le_sq₀ (by positivity) hw).mp (by rwa [hw2])
        have hwpos : 0 < w := (mul_pos (by norm_num) hC).trans_le hw8
        have hz_eq : z = (a n * w) * w := by
          calc
            z = z / a n * a n := (div_mul_cancel₀ z ha0.ne').symm
            _ = (a n * w) * w := by rw [← hw2]; ring
        have hzeq : z / w = a n * w := by
          rw [hz_eq]
          field_simp [hwpos.ne']
        have haw : a n * w ≤ z / (8 * C) := by
          rw [← hzeq]
          apply (div_le_div_iff₀ hwpos (by positivity)).mpr
          exact mul_le_mul_of_nonneg_left hw8 hz0.le
        calc
          C * (2 * a n) * w = 2 * C * (a n * w) := by ring
          _ ≤ 2 * C * (z / (8 * C)) :=
            mul_le_mul_of_nonneg_left haw (by positivity)
          _ = z / 4 := by field_simp; ring
  have hjDelta : 0 ≤ (n : ℝ) * (truncatedIncrementMean μ y - truncatedIncrementMean μ (a n)) -
      (j : ℝ) * (truncatedIncrementMean μ y - truncatedIncrementMean μ (a n)) := by
    have hh : (j : ℝ) ≤ n := by exact_mod_cast hjn
    rw [← sub_mul]
    exact mul_nonneg (sub_nonneg.mpr hh) hd0
  have hjcenter : s ≤ z - (j : ℝ) * (truncatedIncrementMean μ y - truncatedIncrementMean μ (a n)) := by
    have hjs : (j : ℝ) * (truncatedIncrementMean μ y - truncatedIncrementMean μ (a n)) ≤
        (n : ℝ) * (truncatedIncrementMean μ y - truncatedIncrementMean μ (a n)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hjn) hd0
    dsimp [s]
    linarith
  have hMpowN : (∫ k : ℕ, (if k < Y then Real.exp (t * ((k : ℝ) - q))
      else Real.exp (t * (1 - q))) ∂μ) ^ j ≤ Real.exp ((n : ℝ) * ((Real.exp (t * B) - 1 - t * B) / B ^ 2) * V) := by
    apply hMpow.trans (Real.exp_le_exp.mpr _)
    have hA : 0 ≤ ((Real.exp (t * B) - 1 - t * B) / B ^ 2) * V :=
      mul_nonneg (div_nonneg hexp_nonneg (sq_nonneg B)) hV.le
    have hh : (j : ℝ) ≤ n := by exact_mod_cast hjn
    convert mul_le_mul_of_nonneg_left hh hA using 1 <;> ring
  have hcount : ((Measure.pi fun _ : Fin j => μ)
      {ω : Fin j → ℕ | s ≤ (∑ i, (ω i : ℝ)) - q * j ∧ ∀ i, ω i < Y}).toReal ≤
        Real.exp (s / B) * (1 + R) ^ (-(s / B)) := by
    apply hmarkov.trans
    have hfactor : Real.exp (-t * s) * Real.exp ((n : ℝ) * ((Real.exp (t * B) - 1 - t * B) / B ^ 2) * V) ≤
        Real.exp (s / B) * (1 + R) ^ (-(s / B)) := by
      have hnV : (n : ℝ) * V = s * B / R := by
        dsimp [R]
        field_simp [hR.ne', mul_ne_zero hnR.ne' hV.ne']
      have hb : -t * s + (n : ℝ) * ((Real.exp (t * B) - 1 - t * B) / B ^ 2) * V ≤
          s / B + (Real.log (1 + R)) * (-(s / B)) := by
        have he : (n : ℝ) * ((Real.exp (t * B) - 1 - t * B) / B ^ 2) * V =
            (n : ℝ) * V / B ^ 2 * (Real.exp (t * B) - 1 - t * B) := by field_simp [hB.ne']
        have htprod : (-t) * s = -(t * B) * (s / B) := by
          dsimp [t]
          field_simp
        have hlog : 0 ≤ Real.log (1 + R) := Real.log_nonneg (by linarith)
        have hsmall : R - (1 + R) * Real.log (1 + R) ≤ R - R * Real.log (1 + R) := by
          calc
            R - (1 + R) * Real.log (1 + R) = R - R * Real.log (1 + R) -
                Real.log (1 + R) := by ring
            _ ≤ R - R * Real.log (1 + R) := sub_le_self _ hlog
        calc
          -t * s + (n : ℝ) * ((Real.exp (t * B) - 1 - t * B) / B ^ 2) * V =
              (s / (B * R)) * (R - (1 + R) * Real.log (1 + R)) := by
            rw [he, htB, Real.exp_log (by linarith), show 1 + R - 1 = R by ring,
              htprod, hnV]
            field_simp [hB.ne', hR.ne']
            rw [htB]
            ring
          _ ≤ (s / (B * R)) * (R - R * Real.log (1 + R)) :=
            mul_le_mul_of_nonneg_left hsmall (by positivity)
          _ = s / B + (Real.log (1 + R)) * (-(s / B)) := by
            field_simp [hB.ne', hR.ne']
            ring
      calc
        _ = Real.exp (-t * s + (n : ℝ) * ((Real.exp (t * B) - 1 - t * B) / B ^ 2) * V) :=
          (Real.exp_add _ _).symm
        _ ≤ Real.exp (s / B + (Real.log (1 + R)) * (-(s / B))) :=
          Real.exp_le_exp.mpr hb
        _ = Real.exp (s / B) * Real.exp ((Real.log (1 + R)) * (-(s / B))) := Real.exp_add _ _
        _ = _ := by rw [Real.rpow_def_of_pos (show 0 < 1 + R by linarith)]
    calc
      _ ≤ Real.exp (-t * s) * Real.exp ((n : ℝ) * ((Real.exp (t * B) - 1 - t * B) / B ^ 2) * V) :=
        mul_le_mul_of_nonneg_left hMpowN (Real.exp_pos _).le
      _ ≤ _ := hfactor
  let g : (Fin j → ℕ) → (Fin j → ℤ) := fun ω i => (ω i : ℤ) - 1
  have hpi : (Measure.pi fun _ : Fin j => incrementLaw μ) = (Measure.pi fun _ : Fin j => μ).map g := by
    dsimp [g, incrementLaw]
    exact (Measure.pi_map_pi (fun _ => (measurable_of_countable _).aemeasurable)).symm
  have hmeasure : ((Measure.pi fun _ : Fin j => incrementLaw μ)
      {x | z ≤ (∑ i, (x i : ℝ)) - j * truncatedIncrementMean μ (a n) ∧ ∀ i, (x i : ℝ) ≤ y}).toReal =
      ((Measure.pi fun _ : Fin j => μ)
        (g ⁻¹' {x | z ≤ (∑ i, (x i : ℝ)) - j * truncatedIncrementMean μ (a n) ∧
          ∀ i, (x i : ℝ) ≤ y})).toReal := by
    rw [hpi, Measure.map_apply (measurable_of_countable _) MeasurableSet.of_discrete]
  rw [hmeasure]
  have hsubset : g ⁻¹' {x | z ≤ (∑ i, (x i : ℝ)) - j * truncatedIncrementMean μ (a n) ∧
        ∀ i, (x i : ℝ) ≤ y} ⊆
      {ω : Fin j → ℕ | s ≤ (∑ i, (ω i : ℝ)) - q * j ∧ ∀ i, ω i < Y} := by
    intro ω hω
    change s ≤ (∑ i, (ω i : ℝ)) - q * j ∧ ∀ i, ω i < Y
    have hsum : (∑ i, ((g ω i : ℤ) : ℝ)) = (∑ i, (ω i : ℝ)) - j := by
      dsimp [g]
      simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring_nf
    have hsource : z ≤ (∑ i, (ω i : ℝ)) - j * truncatedIncrementMean μ (a n) := by
      have hh := hω.1
      change z ≤ (∑ i, ((g ω i : ℤ) : ℝ)) - j * truncatedIncrementMean μ (a n) at hh
      rw [hsum] at hh
      linarith
    have hdev : s ≤ (∑ i, (ω i : ℝ)) - q * j := by
      calc
        s ≤ z - (j : ℝ) * (truncatedIncrementMean μ y - truncatedIncrementMean μ (a n)) := hjcenter
        _ ≤ (∑ i, (ω i : ℝ)) - q * j := by
          have hh := sub_le_sub_right hsource
            ((j : ℝ) * (truncatedIncrementMean μ y - truncatedIncrementMean μ (a n)))
          dsimp [q] at *
          linarith
    refine ⟨hdev, ?_⟩
    intro i
    have hh := (hcut (ω i)).mpr ?_
    · exact hh
    · have hi := hω.2 i
      change ((g ω i : ℤ) : ℝ) ≤ y at hi
      dsimp [g] at hi
      have hile : offspringIncrement (ω i) ≤ y := by simpa [offspringIncrement] using hi
      rw [abs_le]
      constructor
      · have hnon : -1 ≤ offspringIncrement (ω i) := by
          simp [offspringIncrement]
        exact (neg_le_neg (show (1:ℝ) ≤ y by linarith)).trans hnon
      · exact hile
  apply (measureReal_mono hsubset).trans
  apply hcount.trans
  have hrR : r ≤ R := by
    have heq : R = (B / y) * r := by
      dsimp [R, r, c, s, V, D, B]
      field_simp
    rw [heq]
    have hBy : 1 ≤ B / y := (le_div_iff₀ hy0).mpr (by dsimp [B]; linarith)
    calc
      r = 1 * r := (one_mul r).symm
      _ ≤ (B / y) * r := mul_le_mul_of_nonneg_right hBy hr.le
      _ = (B / y) * r := rfl
  have hsb : s / B ≤ z / y := (fukNagaev_exponent_comparisons hy2 hz0.le rfl rfl).1
  have hsb2 : z / (2 * y) ≤ s / B := (fukNagaev_exponent_comparisons hy2 hz0.le rfl rfl).2
  have hpow : (1 + R) ^ (-(s / B)) ≤ (1 + r) ^ (-(z / (2 * y))) :=
    fukNagaev_negative_rpow_comparison hr hrR (by positivity) hsb2
  have hexp : Real.exp (s / B) ≤ Real.exp (z / y) := Real.exp_le_exp.mpr hsb
  exact mul_le_mul hexp hpow (Real.rpow_nonneg (by linarith) _) (Real.exp_pos _).le

end SubcriticalCauchy.Bienayme
