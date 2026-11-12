module

public import SubcriticalCauchy.PaperRoute.BergerTightAux
public import SubcriticalCauchy.PotterBounds
public import SubcriticalCauchy.CenteringTailSeries

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniform truncation tightness at the Berger scaling
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators

namespace SubcriticalCauchy.Bienayme

noncomputable section

attribute [local instance] Classical.propDecidable

local instance bergerTightMainIncrementLawIsProbability (μ : Measure ℕ)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (incrementLaw μ) := by
  unfold incrementLaw
  infer_instance

/-- The scaled increment tail is uniformly small at large multiples of the scale. -/
lemma bergerTight_scaled_tail_bound
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ < 1)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2)) atTop (𝓝 1))
    {a : ℕ → ℝ}
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal) atTop (𝓝 1)) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ n : ℕ in atTop, ∀ K : ℝ, 1 ≤ K →
      (n : ℝ) * (incrementTail μ (K * a n)).toReal ≤ D * K ^ (-(1 / 2) : ℝ) := by
  have hlit : IsSubcriticalCauchyOffspring μ := ⟨hm, ⟨L, hpos, hsv, hlocal⟩⟩
  have haTop := scaling_tendsto_atTop μ hlit ha
  have hscale := scaling_div_mul_tendsto_one μ hm hpos hL hsv hlocal ha
  have htailReal := incrementTail_div_tendsto_one μ hm hpos hL hsv hlocal
  obtain ⟨P, hP, R, hR, hp⟩ := potter_bounds hpos hL hsv (1 / 2) (by norm_num)
  obtain ⟨B, hB⟩ := eventually_atTop.mp
    (htailReal.eventually_le_const (by norm_num : (1 : ℝ) < 2))
  refine ⟨4 * P, by positivity, ?_⟩
  filter_upwards [haTop.eventually_ge_atTop (max 1 (max R B)),
    hscale.eventually_const_lt (by norm_num : (2 : ℝ)⁻¹ < 1),
    eventually_gt_atTop (0 : ℕ)] with n hna hnscale hn
  intro K hK
  have ha0 : 0 < a n := zero_lt_one.trans_le ((le_max_left 1 (max R B)).trans hna)
  have haR : R ≤ a n := (le_max_left R B).trans (le_max_right 1 (max R B)) |>.trans hna
  have haB : B ≤ a n := (le_max_right R B).trans (le_max_right 1 (max R B)) |>.trans hna
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hKa0 : 0 < K * a n := mul_pos hK0 ha0
  have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hLa0 : 0 < L (a n) := hpos _ ha0
  have hLKa0 : 0 < L (K * a n) := hpos _ hKa0
  have hscale0 : 0 < (n : ℝ) * L (a n) := mul_pos hn0 hLa0
  have hnorm : (n : ℝ) * L (a n) ≤ 2 * a n := by
    have hh := (le_div_iff₀ hscale0).mp hnscale.le
    nlinarith
  have htailK : (incrementTail μ (K * a n)).toReal /
      (L (K * a n) / (K * a n)) ≤ 2 :=
    hB (K * a n) (haB.trans (by nlinarith))
  have hT : (incrementTail μ (K * a n)).toReal ≤
      2 * (L (K * a n) / (K * a n)) := by
    have hh := (div_le_iff₀ (div_pos hLKa0 hKa0)).mp htailK
    nlinarith
  have hKa_le : a n ≤ K * a n := by nlinarith
  have hLratio : L (K * a n) / L (a n) ≤ P * K ^ (1 / 2 : ℝ) := by
    have hh := (hp (a n) (K * a n) haR hKa_le).2
    convert hh using 2 ; field_simp [ha0.ne']
  calc
    (n : ℝ) * (incrementTail μ (K * a n)).toReal
        ≤ (n : ℝ) * (2 * (L (K * a n) / (K * a n))) :=
      mul_le_mul_of_nonneg_left hT (Nat.cast_nonneg n)
    _ = 2 * ((n : ℝ) * L (a n) / a n) * (L (K * a n) / L (a n)) / K := by
      field_simp [hn0.ne', ha0.ne', hLa0.ne', hLKa0.ne', hK0.ne']
    _ ≤ 2 * 2 * (P * K ^ (1 / 2 : ℝ)) / K := by
      have hnorm' : (n : ℝ) * L (a n) / a n ≤ 2 := (div_le_iff₀ ha0).mpr (by nlinarith)
      have hnonneg : 0 ≤ (n : ℝ) * L (a n) / a n := div_nonneg hscale0.le ha0.le
      have hrnonneg : 0 ≤ L (K * a n) / L (a n) := div_nonneg hLKa0.le hLa0.le
      gcongr
    _ = 4 * P * (K ^ (1 / 2 : ℝ) / K) := by ring
    _ = 4 * P * K ^ (-(1 / 2) : ℝ) := by
      have hpow : K ^ (1 / 2 : ℝ) / K = K ^ (-(1 / 2) : ℝ) := by
        calc
          K ^ (1 / 2 : ℝ) / K = K ^ (1 / 2 : ℝ) / K ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = K ^ ((1 / 2 : ℝ) - 1) := (Real.rpow_sub hK0 _ _).symm
          _ = K ^ (-(1 / 2) : ℝ) := by norm_num
      rw [hpow]

/-- The change of truncated centers between two proportional cutoffs. -/
lemma bergerTight_mean_shift_bound
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ < 1)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2)) atTop (𝓝 1))
    {a : ℕ → ℝ}
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal) atTop (𝓝 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ K : ℝ, 1 ≤ K →
      (n : ℝ) * |truncatedIncrementMean μ (K * a n) - truncatedIncrementMean μ (a n)| ≤
        C * K * a n := by
  have hmfin : offspringMean μ ≠ ∞ := ne_top_of_lt (hm.trans ENNReal.one_lt_top)
  have hlit : IsSubcriticalCauchyOffspring μ := ⟨hm, ⟨L, hpos, hsv, hlocal⟩⟩
  have haTop := scaling_tendsto_atTop μ hlit ha
  have hscale := scaling_div_mul_tendsto_one μ hm hpos hL hsv hlocal ha
  obtain ⟨P, hP, R, hR, hp⟩ := potter_bounds hpos hL hsv 1 one_pos
  obtain ⟨Q, hQ⟩ := eventually_atTop.mp
    (hlocal.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 2)))
  refine ⟨8 * P, by positivity, ?_⟩
  filter_upwards [haTop.eventually_ge_atTop (max 1 (max R (Q : ℝ))),
    hscale.eventually_const_lt (by norm_num : (2 : ℝ)⁻¹ < 1),
    eventually_gt_atTop (0 : ℕ)] with n hna hnscale hn
  intro K hK
  let A := ⌊a n⌋₊ + 2
  let B := ⌊K * a n⌋₊ + 2
  let V := weightedIncrementMass μ
  have ha1 : 1 ≤ a n := (le_max_left 1 (max R (Q : ℝ))).trans hna
  have ha0 : 0 < a n := zero_lt_one.trans_le ha1
  have haR : R ≤ a n := (le_max_left R (Q : ℝ)).trans (le_max_right 1 (max R (Q : ℝ))) |>.trans hna
  have haQ : (Q : ℝ) ≤ a n :=
    (le_max_right R (Q : ℝ)).trans (le_max_right 1 (max R (Q : ℝ))) |>.trans hna
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hLa0 : 0 < L (a n) := hpos _ ha0
  have hscale0 : 0 < (n : ℝ) * L (a n) := mul_pos hn0 hLa0
  have hnorm : (n : ℝ) * L (a n) ≤ 2 * a n := by
    have hh := (le_div_iff₀ hscale0).mp hnscale.le
    nlinarith
  have hKa : a n ≤ K * a n := by nlinarith
  have hAB : A ≤ B := by exact Nat.add_le_add_right (Nat.floor_le_floor hKa) 2
  have hQA : Q ≤ A := by
    have hh : (Q : ℝ) < (A : ℝ) := by
      have hfloor : a n < (⌊a n⌋₊ + 1 : ℕ) := by
        simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (a n)
      exact lt_of_le_of_lt haQ (lt_trans hfloor (by exact_mod_cast (show ⌊a n⌋₊ + 1 < A by omega)))
    exact Nat.le_of_lt (by exact_mod_cast hh)
  have hVsum : Summable V := summable_weightedIncrementMass μ hmfin
  have hmean : truncatedIncrementMean μ (K * a n) - truncatedIncrementMean μ (a n) =
      ∑ j ∈ Finset.range (B - A), V (A + j) := by
    have hsplit := tailMass_split hVsum A (B - A)
    rw [Nat.add_sub_cancel' hAB] at hsplit
    have hta := truncated_add_tail_incrementMean μ hmfin (a n)
    have htK := truncated_add_tail_incrementMean μ hmfin (K * a n)
    calc
      truncatedIncrementMean μ (K * a n) - truncatedIncrementMean μ (a n) =
          tailIncrementMean μ (a n) - tailIncrementMean μ (K * a n) := by linarith
      _ = tailMass V A - tailMass V B := by
        rw [tailIncrementMean_eq_tailMass μ hmfin ha1,
          tailIncrementMean_eq_tailMass μ hmfin (ha1.trans hKa)]
      _ = ∑ j ∈ Finset.range (B - A), V (A + j) := by linarith
  have hterm (j : ℕ) (hj : j ∈ Finset.range (B - A)) :
      0 ≤ V (A + j) ∧ V (A + j) ≤ 2 * P * L (a n) / a n := by
    let k := A + j
    have hk0 : 0 < (k : ℝ) := by
      have : 2 ≤ k := by dsimp [k, A]; omega
      positivity
    have hkQ : Q ≤ k := hQA.trans (Nat.le_add_right A j)
    have hkR : a n ≤ (k : ℝ) := by
      have hfloor : a n < (⌊a n⌋₊ + 1 : ℕ) := by
        simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (a n)
      exact le_of_lt (hfloor.trans_le (by exact_mod_cast (show ⌊a n⌋₊ + 1 ≤ k by omega)))
    have hmass : (k : ℝ) ^ 2 * (μ {k}).toReal ≤ 2 * L k := by
      have hh := (div_lt_iff₀ (div_pos (hpos _ hk0) (sq_pos_of_pos hk0))).mp (hQ k hkQ)
      calc
        (k : ℝ) ^ 2 * (μ {k}).toReal ≤ (k : ℝ) ^ 2 * (2 * (L k / (k : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hh.le (sq_nonneg _)
        _ = 2 * L k := by field_simp
    have hLk : L (k : ℝ) ≤ P * ((k : ℝ) / a n) * L (a n) := by
      have hh := (hp (a n) k haR hkR).2
      rw [Real.rpow_one] at hh
      exact (div_le_iff₀ hLa0).mp hh
    have hnonneg : 0 ≤ V k := by
      dsimp [V, weightedIncrementMass]
      apply mul_nonneg ENNReal.toReal_nonneg
      have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
      linarith
    refine ⟨hnonneg, ?_⟩
    have hdiv : L (k : ℝ) / (k : ℝ) ≤ P * L (a n) / a n := by
      apply (div_le_div_iff₀ hk0 ha0).mpr
      calc
        L (k : ℝ) * a n ≤ (P * ((k : ℝ) / a n) * L (a n)) * a n :=
          mul_le_mul_of_nonneg_right hLk ha0.le
        _ = P * L (a n) * k := by field_simp [ha0.ne']
    dsimp [V, weightedIncrementMass]
    have hid : (μ {k}).toReal * ((k : ℝ) - 1) ≤ (k : ℝ) ^ 2 * (μ {k}).toReal / k := by
      apply (le_div_iff₀ hk0).mpr
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
      nlinarith [ENNReal.toReal_nonneg (a := μ {k})]
    calc
      (μ {k}).toReal * ((k : ℝ) - 1) ≤ (k : ℝ) ^ 2 * (μ {k}).toReal / k := hid
      _ ≤ (2 * L k) / k := div_le_div_of_nonneg_right hmass hk0.le
      _ = 2 * (L k / k) := by ring
      _ ≤ 2 * (P * L (a n) / a n) := by gcongr
      _ = 2 * P * L (a n) / a n := by ring
  have hsum_nonneg : 0 ≤ ∑ j ∈ Finset.range (B - A), V (A + j) :=
    Finset.sum_nonneg fun j hj => (hterm j hj).1
  have hsum_le : (∑ j ∈ Finset.range (B - A), V (A + j)) ≤ 4 * P * K * L (a n) := by
    have hcard : ((B - A : ℕ) : ℝ) ≤ (K + 1) * a n := by
      rw [Nat.cast_sub hAB]
      have hfloorA : a n < (⌊a n⌋₊ + 1 : ℕ) := by
        simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (a n)
      have hfloorB : (⌊K * a n⌋₊ : ℝ) ≤ K * a n :=
        Nat.floor_le (mul_nonneg hK0.le ha0.le)
      dsimp [A, B]
      push_cast
      nlinarith
    calc
      (∑ j ∈ Finset.range (B - A), V (A + j))
          ≤ ∑ _j ∈ Finset.range (B - A), 2 * P * L (a n) / a n :=
        Finset.sum_le_sum fun j hj => (hterm j hj).2
      _ = ((B - A : ℕ) : ℝ) * (2 * P * L (a n) / a n) := by simp
      _ ≤ ((K + 1) * a n) * (2 * P * L (a n) / a n) := by
        gcongr
      _ = 2 * P * (K + 1) * L (a n) := by field_simp [ha0.ne']
      _ ≤ 4 * P * K * L (a n) := by
        have hh := mul_nonneg hP.le (mul_nonneg (sub_nonneg.mpr hK) hLa0.le)
        nlinarith
  rw [hmean, abs_of_nonneg hsum_nonneg]
  calc
    (n : ℝ) * ∑ j ∈ Finset.range (B - A), V (A + j)
        ≤ (n : ℝ) * (4 * P * K * L (a n)) := by gcongr
    _ = 4 * P * K * ((n : ℝ) * L (a n)) := by ring
    _ ≤ 4 * P * K * (2 * a n) := by gcongr
    _ = 8 * P * K * a n := by ring

/-- The product of a diverging argument and a measurable slowly varying function diverges. -/
lemma bergerTight_mul_slowlyVarying_atTop {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L) {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) :
    Tendsto (fun n => a n * L (a n)) atTop atTop := by
  obtain ⟨C, hC, N, hN, hcomp⟩ := sqrt_potter_comparison hpos hL hsv
  let D := L N * Real.sqrt N / C
  have hD : 0 < D := div_pos (mul_pos (hpos N hN) (Real.sqrt_pos.mpr hN)) hC
  have hmain : Tendsto (fun n => D * Real.sqrt (a n)) atTop atTop := by
    simpa only [Function.comp_def, mul_comm] using
      (Real.tendsto_sqrt_atTop.comp ha).atTop_mul_const hD
  apply tendsto_atTop_mono' atTop _ hmain
  filter_upwards [ha.eventually_ge_atTop N] with n hn
  have h := hcomp N (a n) le_rfl hn
  have hDle : D ≤ L (a n) * Real.sqrt (a n) := by
    exact (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using h)
  calc
    D * Real.sqrt (a n) ≤ (L (a n) * Real.sqrt (a n)) * Real.sqrt (a n) :=
      mul_le_mul_of_nonneg_right hDle (Real.sqrt_nonneg _)
    _ = L (a n) * (Real.sqrt (a n) * Real.sqrt (a n)) := by ring
    _ = a n * L (a n) := by rw [Real.mul_self_sqrt (hN.le.trans hn)]; ring

/-- The scaling relation implies `n / aₙ² → 0`. -/
lemma bergerTight_nat_div_sq_tendsto_zero
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ < 1)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2)) atTop (𝓝 1))
    {a : ℕ → ℝ}
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => (n : ℝ) / (a n) ^ 2) atTop (𝓝 0) := by
  have hlit : IsSubcriticalCauchyOffspring μ := ⟨hm, ⟨L, hpos, hsv, hlocal⟩⟩
  have hat := scaling_tendsto_atTop μ hlit ha
  have hratio := scaling_div_mul_tendsto_one μ hm hpos hL hsv hlocal ha
  have hrecip : Tendsto (fun n : ℕ => (n : ℝ) * L (a n) / a n) atTop (𝓝 1) := by
    simpa only [div_eq_mul_inv, mul_inv_rev, inv_inv, inv_one] using hratio.inv₀ one_ne_zero
  have hinv : Tendsto (fun n : ℕ => (a n * L (a n))⁻¹) atTop (𝓝 0) :=
    (bergerTight_mul_slowlyVarying_atTop hpos hL hsv hat).inv_tendsto_atTop
  have hprod : Tendsto
      (fun n : ℕ => ((n : ℝ) * L (a n) / a n) * (a n * L (a n))⁻¹) atTop (𝓝 0) := by
    simpa only [one_mul] using hrecip.mul hinv
  apply hprod.congr'
  filter_upwards [hat.eventually_gt_atTop 0] with n han
  have hLa : 0 < L (a n) := hpos _ han
  field_simp [han.ne', hLa.ne']

/-- Truncated second moments have at most quadratic growth at the Berger scale. -/
lemma bergerTight_second_moment_bound
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ < 1)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2)) atTop (𝓝 1))
    {a : ℕ → ℝ}
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal) atTop (𝓝 1)) :
    ∃ V : ℝ, 0 < V ∧ ∀ᶠ n : ℕ in atTop, ∀ K : ℝ, 1 ≤ K →
      (n : ℝ) * (∫ z, (bergerTrunc (K * a n) z) ^ 2 ∂incrementLaw μ) ≤
        V * K ^ 2 * a n ^ 2 := by
  have hlit : IsSubcriticalCauchyOffspring μ := ⟨hm, ⟨L, hpos, hsv, hlocal⟩⟩
  have haTop := scaling_tendsto_atTop μ hlit ha
  have hscale := scaling_div_mul_tendsto_one μ hm hpos hL hsv hlocal ha
  obtain ⟨D, M, hD⟩ := truncated_second_moment_le μ hm hpos hL hsv hlocal
  let D₁ := |D| + 1
  obtain ⟨P, hP, R, hR, hp⟩ := potter_bounds hpos hL hsv 1 one_pos
  refine ⟨1 + 18 * P * D₁, by dsimp [D₁]; positivity, ?_⟩
  filter_upwards [haTop.eventually_ge_atTop (max 1 (max R (M : ℝ))),
    hscale.eventually_const_lt (by norm_num : (2 : ℝ)⁻¹ < 1),
    (bergerTight_nat_div_sq_tendsto_zero μ hm hpos hL hsv hlocal ha).eventually_le_const
      zero_lt_one] with n hna hnscale hn_sq
  intro K hK
  let y := ⌈K * a n + 1⌉₊
  have ha1 : 1 ≤ a n := (le_max_left 1 (max R (M : ℝ))).trans hna
  have ha0 : 0 < a n := zero_lt_one.trans_le ha1
  have haR : R ≤ a n := (le_max_left R (M : ℝ)).trans (le_max_right 1 (max R (M : ℝ))) |>.trans hna
  have haM : (M : ℝ) ≤ a n :=
    (le_max_right R (M : ℝ)).trans (le_max_right 1 (max R (M : ℝ))) |>.trans hna
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hLa0 : 0 < L (a n) := hpos _ ha0
  have hnorm : (n : ℝ) * L (a n) ≤ 2 * a n := by
    have hn0 : (n : ℝ) > 0 := by
      by_contra hn
      have hnzero : n = 0 := by exact_mod_cast (le_antisymm (le_of_not_gt hn) (Nat.cast_nonneg n))
      subst n
      norm_num at hnscale
    have hh := (le_div_iff₀ (mul_pos hn0 hLa0)).mp hnscale.le
    nlinarith
  have hna_le : (n : ℝ) ≤ a n ^ 2 := by
    have hh := (div_le_iff₀ (sq_pos_of_pos ha0)).mp hn_sq
    nlinarith
  have hay : a n ≤ (y : ℝ) := by
    have hceil : K * a n + 1 ≤ (y : ℝ) := Nat.le_ceil _
    nlinarith
  have hyM : M ≤ y := by exact_mod_cast haM.trans hay
  have hy0 : 0 < (y : ℝ) := ha0.trans_le hay
  have hLy0 : 0 < L y := hpos _ hy0
  have hy_le : (y : ℝ) ≤ 3 * K * a n := by
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ K * a n + 1 by positivity)
    change (y : ℝ) < K * a n + 1 + 1 at hceil
    nlinarith
  have hLy : L y ≤ 3 * P * K * L (a n) := by
    have hh := (hp (a n) y haR hay).2
    rw [Real.rpow_one] at hh
    have hh' := (div_le_iff₀ hLa0).mp hh
    have hydiv : (y : ℝ) / a n ≤ 3 * K := (div_le_iff₀ ha0).mpr (by nlinarith)
    calc
      L y ≤ P * ((y : ℝ) / a n) * L (a n) := hh'
      _ ≤ P * (3 * K) * L (a n) := by gcongr
      _ = 3 * P * K * L (a n) := by ring
  have hD' : (∑ k ∈ Finset.range (y + 1), (k : ℝ) ^ 2 * (μ {k}).toReal) ≤ D₁ * y * L y := by
    apply (hD y hyM).trans
    have hyle : D * (y : ℝ) * L y ≤ D₁ * (y : ℝ) * L y := by
      have hdle : D ≤ D₁ := by dsimp [D₁]; linarith [le_abs_self D]
      gcongr
    exact hyle
  have hsecond : (∫ z, (bergerTrunc (K * a n) z) ^ 2 ∂incrementLaw μ) ≤
      1 + D₁ * (y : ℝ) * L y := by
    apply (bergerTrunc_integral_sq_le_sum μ (r := K * a n) (by nlinarith)).trans
    simpa only [y, add_comm] using add_le_add_left hD' (1 : ℝ)
  apply (mul_le_mul_of_nonneg_left hsecond (Nat.cast_nonneg n)).trans
  have hn1 : (n : ℝ) ≤ K ^ 2 * a n ^ 2 := by
    calc
      (n : ℝ) ≤ a n ^ 2 := hna_le
      _ ≤ K ^ 2 * a n ^ 2 := by
        have hKsq : (1 : ℝ) ≤ K ^ 2 := by nlinarith [sq_nonneg K]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hKsq (sq_nonneg (a n))
  calc
    (n : ℝ) * (1 + D₁ * (y : ℝ) * L y) = (n : ℝ) + D₁ * ((n : ℝ) * (y : ℝ) * L y) := by ring
    _ ≤ K ^ 2 * a n ^ 2 + 18 * P * D₁ * K ^ 2 * a n ^ 2 := by
      have hmain : (n : ℝ) * (y : ℝ) * L y ≤ 18 * P * K ^ 2 * a n ^ 2 := by
        calc
          (n : ℝ) * (y : ℝ) * L y ≤ (n : ℝ) * (3 * K * a n) * (3 * P * K * L (a n)) := by
            gcongr
          _ = 9 * P * K ^ 2 * a n * ((n : ℝ) * L (a n)) := by ring
          _ ≤ 9 * P * K ^ 2 * a n * (2 * a n) := by gcongr
          _ = 18 * P * K ^ 2 * a n ^ 2 := by ring
      have hD0 : 0 ≤ D₁ := by dsimp [D₁]; positivity
      nlinarith [mul_le_mul_of_nonneg_left hmain hD0]
    _ = (1 + 18 * P * D₁) * K ^ 2 * a n ^ 2 := by ring

/-- Tightness of the maximum, uniformly over all initial blocks. -/
theorem incrementMax_tight_scale
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ < 1)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2)) atTop (𝓝 1))
    {a : ℕ → ℝ}
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal) atTop (𝓝 1)) :
    ∀ τ : ℝ, 0 < τ → ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, j ≤ n →
      ((Measure.pi fun _ : Fin j => incrementLaw μ)
          {x | ∃ i, K * a n < (x i : ℝ)}).toReal ≤ τ := by
  obtain ⟨D, hD, hbound⟩ := bergerTight_scaled_tail_bound μ hm hpos hL hsv hlocal ha
  intro τ hτ
  have htend : Tendsto (fun K : ℝ => D * K ^ (-(1 / 2) : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul D
  have hev : ∀ᶠ K : ℝ in atTop, 1 ≤ K ∧ D * K ^ (-(1 / 2) : ℝ) ≤ τ :=
    (eventually_ge_atTop 1).and (htend.eventually_le_const hτ)
  obtain ⟨K, hK, hKτ⟩ := hev.exists
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbound
  refine ⟨K, zero_lt_one.trans_le hK, N, ?_⟩
  intro n hn j hj
  calc
    ((Measure.pi fun _ : Fin j => incrementLaw μ) {x | ∃ i, K * a n < (x i : ℝ)}).toReal
        ≤ (j : ℝ) * (incrementTail μ (K * a n)).toReal := incrementMax_measure_le μ j _
    _ ≤ (n : ℝ) * (incrementTail μ (K * a n)).toReal := by
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hj) ENNReal.toReal_nonneg
    _ ≤ D * K ^ (-(1 / 2) : ℝ) := hN n hn K hK
    _ ≤ τ := hKτ

/-- Tightness of the centered increment sums, uniformly over all initial blocks. -/
theorem incrementSum_tight_scale
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ < 1)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2)) atTop (𝓝 1))
    {a : ℕ → ℝ}
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal) atTop (𝓝 1)) :
    ∀ τ : ℝ, 0 < τ → ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, j ≤ n →
      ((Measure.pi fun _ : Fin j => incrementLaw μ)
          {x | K * a n < |(∑ i, (x i : ℝ)) - j * truncatedIncrementMean μ (a n)|}).toReal ≤ τ := by
  obtain ⟨D, hD, hDb⟩ := bergerTight_scaled_tail_bound μ hm hpos hL hsv hlocal ha
  obtain ⟨C, hC, hCb⟩ := bergerTight_mean_shift_bound μ hm hpos hL hsv hlocal ha
  obtain ⟨V, hV, hVb⟩ := bergerTight_second_moment_bound μ hm hpos hL hsv hlocal ha
  have hlit : IsSubcriticalCauchyOffspring μ := ⟨hm, ⟨L, hpos, hsv, hlocal⟩⟩
  have haTop := scaling_tendsto_atTop μ hlit ha
  intro τ hτ
  have htendK : Tendsto (fun K : ℝ => D * K ^ (-(1 / 2) : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul D
  have hevK : ∀ᶠ K : ℝ in atTop, 1 ≤ K ∧ D * K ^ (-(1 / 2) : ℝ) ≤ τ / 2 :=
    (eventually_ge_atTop 1).and (htendK.eventually_le_const (half_pos hτ))
  obtain ⟨K, hK, hKτ⟩ := hevK.exists
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have htendq : Tendsto (fun q : ℝ => V * K ^ 2 / q ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num : 2 ≠ 0))
  have hevq : ∀ᶠ q : ℝ in atTop, 0 < q ∧ V * K ^ 2 / q ^ 2 ≤ τ / 2 :=
    (eventually_gt_atTop 0).and (htendq.eventually_le_const (half_pos hτ))
  obtain ⟨q, hq, hqτ⟩ := hevq.exists
  have hevN : ∀ᶠ n : ℕ in atTop,
      ((∀ R : ℝ, 1 ≤ R → (n : ℝ) * (incrementTail μ (R * a n)).toReal ≤
          D * R ^ (-(1 / 2) : ℝ)) ∧
        (∀ R : ℝ, 1 ≤ R → (n : ℝ) *
          |truncatedIncrementMean μ (R * a n) - truncatedIncrementMean μ (a n)| ≤ C * R * a n)) ∧
        ((∀ R : ℝ, 1 ≤ R → (n : ℝ) *
          (∫ z, (bergerTrunc (R * a n) z) ^ 2 ∂incrementLaw μ) ≤ V * R ^ 2 * a n ^ 2) ∧
          1 ≤ a n) :=
    (hDb.and hCb).and (hVb.and (haTop.eventually_ge_atTop 1))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevN
  refine ⟨C * K + q, by positivity, N, ?_⟩
  intro n hn j hj
  obtain ⟨⟨hDn, hCn⟩, hVn, han⟩ := hN n hn
  have ha0 : 0 < a n := zero_lt_one.trans_le han
  have hr : 1 ≤ K * a n := one_le_mul_of_one_le_of_one_le hK han
  have hmeanj : (j : ℝ) *
      |truncatedIncrementMean μ (K * a n) - truncatedIncrementMean μ (a n)| ≤
        (C * K) * a n := by
    calc
      (j : ℝ) * |truncatedIncrementMean μ (K * a n) - truncatedIncrementMean μ (a n)|
          ≤ (n : ℝ) * |truncatedIncrementMean μ (K * a n) - truncatedIncrementMean μ (a n)| := by
            gcongr
      _ ≤ C * K * a n := hCn K hK
      _ = (C * K) * a n := by ring
  have hsub := bergerTight_bad_event_subset j (K * a n) (C * K) q (a n)
    (truncatedIncrementMean μ (a n)) (truncatedIncrementMean μ (K * a n)) hr hmeanj
  have hmax : ((Measure.pi fun _ : Fin j => incrementLaw μ)
      {x | ∃ i, K * a n < (x i : ℝ)}).toReal ≤ τ / 2 := by
    calc
      ((Measure.pi fun _ : Fin j => incrementLaw μ) {x | ∃ i, K * a n < (x i : ℝ)}).toReal
          ≤ (j : ℝ) * (incrementTail μ (K * a n)).toReal := incrementMax_measure_le μ j _
      _ ≤ (n : ℝ) * (incrementTail μ (K * a n)).toReal := by
        exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hj) ENNReal.toReal_nonneg
      _ ≤ D * K ^ (-(1 / 2) : ℝ) := hDn K hK
      _ ≤ τ / 2 := hKτ
  have hvar : variance (fun x : Fin j → ℤ => ∑ i, bergerTrunc (K * a n) (x i))
      (Measure.pi fun _ : Fin j => incrementLaw μ) ≤ V * K ^ 2 * a n ^ 2 := by
    calc
      variance (fun x : Fin j → ℤ => ∑ i, bergerTrunc (K * a n) (x i))
          (Measure.pi fun _ : Fin j => incrementLaw μ)
          ≤ (j : ℝ) * ∫ z, (bergerTrunc (K * a n) z) ^ 2 ∂incrementLaw μ :=
        bergerTrunc_sum_variance_le μ j (zero_le_one.trans hr)
      _ ≤ (n : ℝ) * ∫ z, (bergerTrunc (K * a n) z) ^ 2 ∂incrementLaw μ := by
        apply mul_le_mul_of_nonneg_right _ (integral_nonneg fun _ => sq_nonneg _)
        exact_mod_cast hj
      _ ≤ V * K ^ 2 * a n ^ 2 := hVn K hK
  have hcheb : ((Measure.pi fun _ : Fin j => incrementLaw μ)
      {x | q * a n ≤ |∑ i, bergerTrunc (K * a n) (x i) -
        (j : ℝ) * truncatedIncrementMean μ (K * a n)|}).toReal ≤ τ / 2 := by
    calc
      ((Measure.pi fun _ : Fin j => incrementLaw μ)
          {x | q * a n ≤ |∑ i, bergerTrunc (K * a n) (x i) -
            (j : ℝ) * truncatedIncrementMean μ (K * a n)|}).toReal
          ≤ (variance (fun x : Fin j → ℤ => ∑ i, bergerTrunc (K * a n) (x i))
            (Measure.pi fun _ : Fin j => incrementLaw μ)) / (q * a n) ^ 2 :=
        bergerTight_chebyshev μ j hr (mul_pos hq ha0)
      _ ≤ (V * K ^ 2 * a n ^ 2) / (q * a n) ^ 2 := by gcongr
      _ = V * K ^ 2 / q ^ 2 := by field_simp [hq.ne', ha0.ne']
      _ ≤ τ / 2 := hqτ
  calc
    ((Measure.pi fun _ : Fin j => incrementLaw μ)
        {x | (C * K + q) * a n < |(∑ i, (x i : ℝ)) -
          j * truncatedIncrementMean μ (a n)|}).toReal
        ≤ ((Measure.pi fun _ : Fin j => incrementLaw μ)
          ({x | ∃ i, K * a n < (x i : ℝ)} ∪
          {x | q * a n ≤ |∑ i, bergerTrunc (K * a n) (x i) -
            (j : ℝ) * truncatedIncrementMean μ (K * a n)|})).toReal := by
            exact measureReal_mono hsub (by finiteness)
    _ ≤ ((Measure.pi fun _ : Fin j => incrementLaw μ)
          {x | ∃ i, K * a n < (x i : ℝ)}).toReal +
        ((Measure.pi fun _ : Fin j => incrementLaw μ)
          {x | q * a n ≤ |∑ i, bergerTrunc (K * a n) (x i) -
            (j : ℝ) * truncatedIncrementMean μ (K * a n)|}).toReal :=
      measureReal_union_le _ _
    _ ≤ τ / 2 + τ / 2 := add_le_add hmax hcheb
    _ = τ := by ring

end
end SubcriticalCauchy.Bienayme
