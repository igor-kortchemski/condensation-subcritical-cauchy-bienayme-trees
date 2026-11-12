module

public import SubcriticalCauchy.IncrementTailAsymptotics
public import SubcriticalCauchy.TruncatedExponential
public import SubcriticalCauchy.StableOneStepAux
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring


/-!
# Tail estimates for the one-step stable Laplace exponent
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section

/-- Rescaling the argument of the increment tail by a fixed positive factor. -/
theorem rescaled_incrementTail_tendsto
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) {u : ℝ} (hu : 0 < u) :
    Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (u * a n)).toReal)
      atTop (𝓝 (1 / u)) := by
  obtain ⟨hm, L, hpos, hsv, hL, hlocal⟩ := hμ
  let hlit : IsSubcriticalCauchyOffspring μ := ⟨hm, L, hpos, hsv, hlocal⟩
  have hat : Tendsto a atTop atTop := scaling_tendsto_atTop μ hlit ha
  have huat : Tendsto (fun n => u * a n) atTop atTop := hat.const_mul_atTop hu
  have hTu := (incrementTail_div_tendsto_one μ hm hpos hL hsv hlocal).comp huat
  have hTa := (incrementTail_div_tendsto_one μ hm hpos hL hsv hlocal).comp hat
  have hTaInv : Tendsto (fun n : ℕ =>
      1 / ((incrementTail μ (a n)).toReal / (L (a n) / a n))) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Pi.div_def, one_div, div_one] using
      (tendsto_const_nhds (x := (1 : ℝ))).div hTa one_ne_zero
  have hLratio : Tendsto (fun n : ℕ => L (u * a n) / L (a n)) atTop (𝓝 1) :=
    (hsv u hu).comp hat
  have hratio : Tendsto (fun n : ℕ => a n / (u * a n)) atTop (𝓝 (1 / u)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hat.eventually_gt_atTop 0] with n han
    have hua : 0 < u * a n := mul_pos hu han
    field_simp [han.ne', hua.ne', hu.ne']
  have hprod := ((((ha.mul hTu).mul hTaInv).mul hLratio).mul hratio)
  have hlim : Tendsto (fun n : ℕ =>
      (((((n : ℝ) * (incrementTail μ (a n)).toReal) *
        ((incrementTail μ (u * a n)).toReal / (L (u * a n) / (u * a n)))) *
        (1 / ((incrementTail μ (a n)).toReal / (L (a n) / a n)))) *
        (L (u * a n) / L (a n))) * (a n / (u * a n))) atTop (𝓝 (1 / u)) := by
    simpa only [Function.comp_def, one_mul, mul_one] using hprod
  apply hlim.congr'
  filter_upwards [hat.eventually_gt_atTop 0] with n han
  have hua : 0 < u * a n := mul_pos hu han
  have hTa0 : (incrementTail μ (a n)).toReal ≠ 0 :=
    (ENNReal.toReal_pos (incrementTail_pos μ hlit (a n)).ne' (measure_ne_top _ _)).ne'
  have hTu0 : (incrementTail μ (u * a n)).toReal ≠ 0 :=
    (ENNReal.toReal_pos (incrementTail_pos μ hlit (u * a n)).ne' (measure_ne_top _ _)).ne'
  have hLa : L (a n) ≠ 0 := (hpos _ han).ne'
  have hLua : L (u * a n) ≠ 0 := (hpos _ hua).ne'
  field_simp [hTa0, hTu0, hLa, hLua, han.ne', hua.ne', hu.ne']

/-- Crude inverse-square tail bound using the second moment up to `Nat.ceil a`.
The remaining upper tail is left unscaled. -/
lemma incrementTail_le_secondMoment_add_tail
    (μ : Measure ℕ) [IsProbabilityMeasure μ] {a u : ℝ} (ha : 0 < a) (hu : 0 < u) :
    (incrementTail μ (u * a)).toReal ≤
      (∑ k ∈ Finset.range (⌈a⌉₊ + 1), (k : ℝ) ^ 2 * (μ {k}).toReal) /
          (u * a) ^ 2 + (incrementTail μ a).toReal := by
  let c : ℝ := u * a
  let Y : ℕ := ⌈a⌉₊
  let A : ℕ → ℝ := fun k => if k < Y + 1 then (k : ℝ) ^ 2 else 0
  let B : ℕ → ℝ := fun k => if a ≤ (k : ℝ) - 1 then c ^ 2 else 0
  let F : ℕ → ℝ := fun k => if k < Y + 1 then (k : ℝ) ^ 2 else c ^ 2
  have hc : 0 < c := mul_pos hu ha
  have hB : 0 ≤ (Y : ℝ) ^ 2 := sq_nonneg _
  have hbound (k : ℕ) :
      ‖F k‖ ≤ max ((Y : ℝ) ^ 2) (c ^ 2) ∧
      ‖A k + B k‖ ≤ 2 * max ((Y : ℝ) ^ 2) (c ^ 2) := by
    constructor
    · simp only [F, Real.norm_eq_abs]
      split_ifs with hk
      · rw [abs_of_nonneg (sq_nonneg _)]
        apply le_trans _ (le_max_left _ _)
        exact pow_le_pow_left₀ (Nat.cast_nonneg _)
          (by exact_mod_cast Nat.le_of_lt_succ hk) 2
      · exact abs_of_nonneg (sq_nonneg _) |>.le.trans (le_max_right _ _)
    · have hA : ‖A k‖ ≤ max ((Y : ℝ) ^ 2) (c ^ 2) := by
        simp only [A, Real.norm_eq_abs]
        split_ifs with hk
        · rw [abs_of_nonneg (sq_nonneg _)]
          exact (pow_le_pow_left₀ (Nat.cast_nonneg _)
            (by exact_mod_cast Nat.le_of_lt_succ hk) 2).trans (le_max_left _ _)
        · simp [sq_nonneg]
      have hB' : ‖B k‖ ≤ max ((Y : ℝ) ^ 2) (c ^ 2) := by
        simp only [B, Real.norm_eq_abs]
        split_ifs <;> simp [sq_nonneg]
      exact (norm_add_le _ _).trans (add_le_add hA hB' |>.trans_eq (by ring))
  have hF : Integrable F μ := Integrable.of_bound
    (measurable_of_countable _).aestronglyMeasurable _ (Eventually.of_forall (fun k => (hbound k).1))
  have hAB : Integrable (fun k => A k + B k) μ := Integrable.of_bound
    (measurable_of_countable _).aestronglyMeasurable _ (Eventually.of_forall (fun k => (hbound k).2))
  have hA : Integrable A μ := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable
      (max ((Y : ℝ) ^ 2) (c ^ 2))
    exact Eventually.of_forall (fun k => by
      simp only [A, Real.norm_eq_abs]
      split_ifs with hk
      · rw [abs_of_nonneg (sq_nonneg _)]
        exact (pow_le_pow_left₀ (Nat.cast_nonneg _)
          (by exact_mod_cast Nat.le_of_lt_succ hk) 2).trans (le_max_left _ _)
      · simp [sq_nonneg])
  have hBint : Integrable B μ := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable
      (max ((Y : ℝ) ^ 2) (c ^ 2))
    exact Eventually.of_forall (fun k => by
      simp only [B, Real.norm_eq_abs]
      split_ifs <;> simp [sq_nonneg])
  have hFG : ∀ k, F k ≤ A k + B k := by
    intro k
    simp only [F, A, B]
    by_cases hk : k < Y + 1
    · simp only [hk, ite_true]
      exact le_add_of_nonneg_right (by split_ifs <;> positivity)
    · have hka : a ≤ (k : ℝ) - 1 := by
        have hyk : Y + 1 ≤ k := Nat.le_of_not_gt hk
        have hceil : a ≤ (Y : ℝ) := Nat.le_ceil a
        have hkR : ((Y + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hyk
        push_cast at hkR
        linarith
      simp [hk, hka]
  have hsubset : {k : ℕ | u * a ≤ (k : ℝ) - 1} ⊆ {k : ℕ | c ^ 2 ≤ F k} := by
    intro k hk
    change c ^ 2 ≤ F k
    change u * a ≤ (k : ℝ) - 1 at hk
    simp only [F]
    split_ifs with hky
    · have hk1 : 1 ≤ k := by
        by_contra hn
        have : k = 0 := Nat.eq_zero_of_not_pos hn
        subst k
        norm_num at hk
        linarith
      have hkc : c ≤ (k : ℝ) := by dsimp [c]; linarith
      exact pow_le_pow_left₀ hc.le hkc 2
    · exact le_rfl
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := F) (Eventually.of_forall (fun k => by
      simp only [F]
      split_ifs <;> positivity)) hF (c ^ 2)
  have hfirst : c ^ 2 * (incrementTail μ (u * a)).toReal ≤ ∫ k, F k ∂μ := by
    apply le_trans _ hmarkov
    exact mul_le_mul_of_nonneg_left (measureReal_mono hsubset) (sq_nonneg _)
  have hsecond : (∫ k, F k ∂μ) ≤ ∫ k, (A k + B k) ∂μ :=
    integral_mono hF hAB hFG
  have hAint : (∫ k, A k ∂μ) =
      ∑ k ∈ Finset.range (Y + 1), (k : ℝ) ^ 2 * (μ {k}).toReal := by
    rw [integral_countable hA]
    rw [tsum_eq_sum (s := Finset.range (Y + 1))]
    · apply Finset.sum_congr rfl
      intro k hk
      simp only [A, Finset.mem_range] at hk ⊢
      simp only [hk, ite_true, smul_eq_mul, Measure.real]
      ring
    · intro k hk
      simp only [A]
      have hky : ¬ k < Y + 1 := by simpa using hk
      simp [hky]
  have hBint_eq : (∫ k, B k ∂μ) = c ^ 2 * (incrementTail μ a).toReal := by
    have hBeq : B = fun k => c ^ 2 *
        Set.indicator {k : ℕ | a ≤ (k : ℝ) - 1} (fun _ => (1 : ℝ)) k := by
      funext k
      by_cases hk : a ≤ (k : ℝ) - 1 <;> simp [B, Set.indicator, hk]
    rw [hBeq, integral_const_mul, integral_indicator (Set.to_countable _).measurableSet,
      setIntegral_const]
    simp [incrementTail, Measure.real, mul_comm]
  rw [integral_add hA hBint, hAint, hBint_eq] at hsecond
  have htotal := hfirst.trans hsecond
  have hh : (incrementTail μ (u * a)).toReal ≤
      ((∑ k ∈ Finset.range (Y + 1), (k : ℝ) ^ 2 * (μ {k}).toReal) +
        c ^ 2 * (incrementTail μ a).toReal) / c ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos hc)).mpr (by simpa [mul_comm] using htotal)
  apply hh.trans_eq
  dsimp [c, Y]
  field_simp [hc.ne']


/-- Uniform polynomial majorant for the rescaled tail above scale one. -/
lemma rescaled_incrementTail_large_bound
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, 1 ≤ u →
      (n : ℝ) * (incrementTail μ (u * a n)).toReal ≤ C * u ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨hm, L, hpos, hsv, hL, hlocal⟩ := hμ
  let hlit : IsSubcriticalCauchyOffspring μ := ⟨hm, L, hpos, hsv, hlocal⟩
  obtain ⟨C, hC, R, hR, hpot⟩ := potter_bounds hpos hL hsv (1 / 2) (by norm_num)
  obtain ⟨X, hX⟩ := eventually_atTop.mp
    ((incrementTail_div_tendsto_one μ hm hpos hL hsv hlocal).eventually
      (Iio_mem_nhds (show (1 : ℝ) < 2 by norm_num)))
  refine ⟨8 * C, by positivity, ?_⟩
  have hat : Tendsto a atTop atTop := scaling_tendsto_atTop μ hlit ha
  have hTa := (incrementTail_div_tendsto_one μ hm hpos hL hsv hlocal).comp hat
  have hTaInv : Tendsto (fun n : ℕ =>
      1 / ((incrementTail μ (a n)).toReal / (L (a n) / a n))) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Pi.div_def, one_div, div_one] using
      (tendsto_const_nhds (x := (1 : ℝ))).div hTa one_ne_zero
  filter_upwards [ha.eventually (Iio_mem_nhds (show (1 : ℝ) < 2 by norm_num)),
    hTaInv.eventually (Iio_mem_nhds (show (1 : ℝ) < 2 by norm_num)),
    hat.eventually_ge_atTop R, hat.eventually_ge_atTop (max 1 X)] with n han hTainv haR ha1X
  have ha1 : 1 ≤ a n := (le_max_left _ _).trans ha1X
  have haX : X ≤ a n := (le_max_right _ _).trans ha1X
  intro u hu
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have hua0 : 0 < u * a n := mul_pos hu0 (zero_lt_one.trans_le ha1)
  have hau : a n ≤ u * a n := by nlinarith [zero_lt_one.trans_le ha1]
  have hTu2 : (incrementTail μ (u * a n)).toReal / (L (u * a n) / (u * a n)) < 2 :=
    hX _ (haX.trans hau)
  have htuprod : (n : ℝ) * (incrementTail μ (u * a n)).toReal =
      (((((n : ℝ) * (incrementTail μ (a n)).toReal) *
        ((incrementTail μ (u * a n)).toReal / (L (u * a n) / (u * a n)))) *
        (1 / ((incrementTail μ (a n)).toReal / (L (a n) / a n)))) *
        (L (u * a n) / L (a n))) * (a n / (u * a n)) := by
    have hTa0 : (incrementTail μ (a n)).toReal ≠ 0 :=
      (ENNReal.toReal_pos (incrementTail_pos μ hlit (a n)).ne' (measure_ne_top _ _)).ne'
    have hTu0 : (incrementTail μ (u * a n)).toReal ≠ 0 :=
      (ENNReal.toReal_pos (incrementTail_pos μ hlit (u * a n)).ne' (measure_ne_top _ _)).ne'
    have hLa : L (a n) ≠ 0 := (hpos _ (zero_lt_one.trans_le ha1)).ne'
    have hLua : L (u * a n) ≠ 0 := (hpos _ hua0).ne'
    field_simp [hTa0, hTu0, hLa, hLua, hua0.ne', hu0.ne']
  have hp := (hpot (a n) (u * a n) haR hau).2
  have hfactor : (u * a n) / a n = u := by field_simp [hu0.ne', (zero_lt_one.trans_le ha1).ne']
  rw [hfactor] at hp
  have hInv : 0 < 1 / ((incrementTail μ (a n)).toReal / (L (a n) / a n)) := by
    apply div_pos zero_lt_one
    apply div_pos (ENNReal.toReal_pos (incrementTail_pos μ hlit (a n)).ne' (measure_ne_top _ _))
    exact div_pos (hpos _ (zero_lt_one.trans_le ha1)) (zero_lt_one.trans_le ha1)
  have hTailNonneg : 0 ≤ (incrementTail μ (u * a n)).toReal / (L (u * a n) / (u * a n)) :=
    div_nonneg ENNReal.toReal_nonneg (div_pos (hpos _ hua0) hua0).le
  have hLnonneg : 0 ≤ L (u * a n) / L (a n) := div_nonneg (hpos _ hua0).le (hpos _ (zero_lt_one.trans_le ha1)).le
  have hanonneg : 0 ≤ (n : ℝ) * (incrementTail μ (a n)).toReal := mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg
  have hgrid : a n / (u * a n) = 1 / u := by field_simp [hu0.ne', (zero_lt_one.trans_le ha1).ne']
  rw [htuprod]
  calc
    (((((n : ℝ) * (incrementTail μ (a n)).toReal) *
        ((incrementTail μ (u * a n)).toReal / (L (u * a n) / (u * a n)))) *
        (1 / ((incrementTail μ (a n)).toReal / (L (a n) / a n)))) *
        (L (u * a n) / L (a n))) * (a n / (u * a n))
      ≤ ((((2 * 2) * 2) * (C * u ^ (1 / 2 : ℝ))) * (1 / u)) := by
        rw [hgrid]
        gcongr
    _ = (8 * C) * u ^ (-(1 / 2 : ℝ)) := by
      have hr : u ^ (1 / 2 : ℝ) * (1 / u) = u ^ (-(1 / 2 : ℝ)) := by
        rw [show 1 / u = u ^ (-1 : ℝ) by simp [Real.rpow_neg_one], ← Real.rpow_add hu0]
        norm_num
      calc
        2 * 2 * 2 * (C * u ^ (1 / 2 : ℝ)) * (1 / u) =
            8 * C * (u ^ (1 / 2 : ℝ) * (1 / u)) := by ring
        _ = (8 * C) * u ^ (-(1 / 2 : ℝ)) := by rw [hr]


/-- Uniform inverse-square majorant for the rescaled tail below scale one. -/
lemma rescaled_incrementTail_small_bound
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, 0 < u → u ≤ 1 →
      (n : ℝ) * (incrementTail μ (u * a n)).toReal ≤ C / u ^ 2 := by
  obtain ⟨hm, L, hpos, hsv, hL, hlocal⟩ := hμ
  let hlit : IsSubcriticalCauchyOffspring μ := ⟨hm, L, hpos, hsv, hlocal⟩
  obtain ⟨K, N, hsecond⟩ := truncated_second_moment_le μ hm hpos hL hsv hlocal
  have hat : Tendsto a atTop atTop := scaling_tendsto_atTop μ hlit ha
  have hceilTop : Tendsto (fun n => ⌈a n⌉₊) atTop atTop := tendsto_nat_ceil_atTop.comp hat
  have hceilRatio : Tendsto (fun n => (⌈a n⌉₊ : ℝ) / a n) atTop (𝓝 1) :=
    tendsto_nat_ceil_div_atTop.comp hat
  have hLratio : Tendsto (fun n => L (⌈a n⌉₊) / L (a n)) atTop (𝓝 1) :=
    slowlyVarying_ratio_of_relative_tendsto_one_filter hpos hL hsv hat hceilRatio
  have hsd := scaling_div_mul_tendsto_one μ hm hpos hL hsv hlocal ha
  have hnorm0 := (tendsto_const_nhds (x := (1 : ℝ))).div hsd one_ne_zero
  have hnorm0' : Tendsto (fun n : ℕ => 1 / (a n / ((n : ℝ) * L (a n)))) atTop (𝓝 1) := by
    simpa only [Pi.div_def, div_one] using hnorm0
  have hnorm : Tendsto (fun n : ℕ => (n : ℝ) * L (a n) / a n) atTop (𝓝 1) := by
    apply hnorm0'.congr'
    filter_upwards [hat.eventually_gt_atTop 0, eventually_gt_atTop (0 : ℕ)] with n han hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hLa : L (a n) ≠ 0 := (hpos _ han).ne'
    field_simp [han.ne', hn0.ne', hLa]
  have hprod := (hnorm.mul hceilRatio).mul hLratio
  refine ⟨2 * |K| + 2, by positivity, ?_⟩
  have hp2 := hprod.eventually (Iio_mem_nhds (show (1 : ℝ) * 1 * 1 < 2 by norm_num))
  filter_upwards [hceilTop.eventually_ge_atTop N, hat.eventually_gt_atTop 0, hp2,
    ha.eventually (Iio_mem_nhds (show (1 : ℝ) < 2 by norm_num))] with n hN han hp hanorm
  intro u hu hu1
  have hmoment := incrementTail_le_secondMoment_add_tail μ (a := a n) (u := u) han hu
  have hmbound := hsecond ⌈a n⌉₊ hN
  have hL0 : 0 < L (a n) := hpos _ han
  have hceil0 : 0 < (⌈a n⌉₊ : ℝ) := by
    have : 0 < ⌈a n⌉₊ := Nat.ceil_pos.mpr han
    exact_mod_cast this
  have hprodnonneg : 0 ≤ ((n : ℝ) * L (a n) / a n) * ((⌈a n⌉₊ : ℝ) / a n) *
      (L (⌈a n⌉₊) / L (a n)) := by
    have hLceil : 0 < L (⌈a n⌉₊) := hpos _ hceil0
    positivity
  have hnormalized : (n : ℝ) *
        (∑ k ∈ Finset.range (⌈a n⌉₊ + 1), (k : ℝ) ^ 2 * (μ {k}).toReal) / (a n) ^ 2 ≤
      |K| * (((n : ℝ) * L (a n) / a n) * ((⌈a n⌉₊ : ℝ) / a n) *
        (L (⌈a n⌉₊) / L (a n))) := by
    have hmassnonneg : 0 ≤ ∑ k ∈ Finset.range (⌈a n⌉₊ + 1),
        (k : ℝ) ^ 2 * (μ {k}).toReal := Finset.sum_nonneg (fun _ _ => by positivity)
    have hmul : (n : ℝ) * (∑ k ∈ Finset.range (⌈a n⌉₊ + 1),
        (k : ℝ) ^ 2 * (μ {k}).toReal) ≤
        (n : ℝ) * (K * (⌈a n⌉₊ : ℝ) * L (⌈a n⌉₊)) :=
      mul_le_mul_of_nonneg_left hmbound (Nat.cast_nonneg _)
    calc
      (n : ℝ) * (∑ k ∈ Finset.range (⌈a n⌉₊ + 1),
          (k : ℝ) ^ 2 * (μ {k}).toReal) / (a n) ^ 2
          ≤ ((n : ℝ) * (K * (⌈a n⌉₊ : ℝ) * L (⌈a n⌉₊))) / (a n) ^ 2 :=
        div_le_div_of_nonneg_right hmul (sq_nonneg _)
      _ = K * (((n : ℝ) * L (a n) / a n) * ((⌈a n⌉₊ : ℝ) / a n) *
          (L (⌈a n⌉₊) / L (a n))) := by
        field_simp [han.ne', hL0.ne']
      _ ≤ |K| * (((n : ℝ) * L (a n) / a n) * ((⌈a n⌉₊ : ℝ) / a n) *
          (L (⌈a n⌉₊) / L (a n))) :=
        mul_le_mul_of_nonneg_right (le_abs_self K) hprodnonneg
  have hmain : (n : ℝ) * (incrementTail μ (u * a n)).toReal ≤
      (2 * |K|) / u ^ 2 + 2 := by
    have hmul := mul_le_mul_of_nonneg_left hmoment (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have hsplit : (n : ℝ) * (incrementTail μ (u * a n)).toReal ≤
        ((n : ℝ) * (∑ k ∈ Finset.range (⌈a n⌉₊ + 1),
          (k : ℝ) ^ 2 * (μ {k}).toReal) / (a n) ^ 2) / u ^ 2 +
        (n : ℝ) * (incrementTail μ (a n)).toReal := by
      convert hmul using 1; field_simp [hu.ne']
    have hfirst : ((n : ℝ) * (∑ k ∈ Finset.range (⌈a n⌉₊ + 1),
        (k : ℝ) ^ 2 * (μ {k}).toReal) / (a n) ^ 2) / u ^ 2 ≤
        (2 * |K|) / u ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg u)
      exact hnormalized.trans (by simpa [mul_comm] using mul_le_mul_of_nonneg_left hp.le (abs_nonneg K))
    linarith
  have htwo : (2 : ℝ) ≤ 2 / u ^ 2 := by
    have hu2 : u ^ 2 ≤ 1 := by nlinarith [sq_nonneg u]
    exact (le_div_iff₀ (sq_pos_of_pos hu)).mpr (by nlinarith)
  calc
    (n : ℝ) * (incrementTail μ (u * a n)).toReal ≤ (2 * |K|) / u ^ 2 + 2 := hmain
    _ ≤ (2 * |K|) / u ^ 2 + 2 / u ^ 2 := by linarith
    _ = (2 * |K| + 2) / u ^ 2 := by ring





/-- The strict increment tail `P(X > x)`, kept separate from the project's `P(X ≥ x)`. -/
def strictIncrementTail (μ : Measure ℕ) (x : ℝ) : ℝ≥0∞ := μ {k : ℕ | x < (k : ℝ) - 1}

lemma strictIncrementTail_antitone (μ : Measure ℕ) : Antitone (strictIncrementTail μ) := by
  intro x y hxy
  exact measure_mono (fun k hk => hxy.trans_lt hk)

lemma incrementTail_strict_gap_le_atom (μ : Measure ℕ) [IsProbabilityMeasure μ] (x : ℝ) :
    (incrementTail μ x).toReal - (strictIncrementTail μ x).toReal ≤
      (μ {⌈x + 1⌉₊}).toReal := by
  have hset : {k : ℕ | x ≤ (k : ℝ) - 1} ⊆
      {k : ℕ | x < (k : ℝ) - 1} ∪ ({⌈x + 1⌉₊} : Set ℕ) := by
    intro k hk
    by_cases hk' : x < (k : ℝ) - 1
    · exact Or.inl hk'
    · right
      have hkEq : (k : ℝ) - 1 = x := le_antisymm (le_of_not_gt hk') hk
      have hkEq' : (k : ℝ) = x + 1 := by linarith
      apply Set.mem_singleton_iff.mpr
      apply Nat.le_antisymm
      · calc
          k = ⌈(k : ℝ)⌉₊ := by simp
          _ ≤ ⌈x + 1⌉₊ := Nat.ceil_mono hkEq'.le
      · apply Nat.ceil_le.mpr
        rw [← hkEq']
  have hmono := measureReal_mono hset (μ := μ)
  have hunion : (μ.real ({k : ℕ | x < (k : ℝ) - 1} ∪ ({⌈x + 1⌉₊} : Set ℕ))) ≤
      (strictIncrementTail μ x).toReal + (μ {⌈x + 1⌉₊}).toReal := by
    simpa only [strictIncrementTail, Measure.real] using
      (measureReal_union_le (μ := μ) {k : ℕ | x < (k : ℝ) - 1} ({⌈x + 1⌉₊} : Set ℕ))
  apply sub_le_iff_le_add.mpr
  exact hmono.trans (hunion.trans_eq (add_comm _ _))

lemma rescaled_incrementAtom_tendsto_zero
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) {u : ℝ} (hu : 0 < u) :
    Tendsto (fun n : ℕ => (n : ℝ) * (μ {⌈u * a n + 1⌉₊}).toReal) atTop (𝓝 0) := by
  obtain ⟨hm, L, hpos, hsv, hL, hlocal⟩ := hμ
  let hlit : IsSubcriticalCauchyOffspring μ := ⟨hm, L, hpos, hsv, hlocal⟩
  let j : ℕ → ℕ := fun n => ⌈u * a n + 1⌉₊
  have hat : Tendsto a atTop atTop := scaling_tendsto_atTop μ hlit ha
  have huat : Tendsto (fun n => u * a n) atTop atTop := hat.const_mul_atTop hu
  have hx : Tendsto (fun n => u * a n + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 huat
  have hjTop : Tendsto j atTop atTop := tendsto_nat_ceil_atTop.comp hx
  have hc : Tendsto (fun n => ((j n : ℕ) : ℝ) / (u * a n + 1)) atTop (𝓝 1) :=
    tendsto_nat_ceil_div_atTop.comp hx
  have hxrel : Tendsto (fun n => (u * a n + 1) / (u * a n)) atTop (𝓝 1) := by
    have hi : Tendsto (fun n : ℕ => 1 / (u * a n)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop huat
    have hh := (tendsto_const_nhds (x := (1 : ℝ))).add hi
    apply (by simpa using hh : Tendsto (fun n : ℕ => 1 + 1 / (u * a n)) atTop (𝓝 1)).congr'
    filter_upwards [hat.eventually_gt_atTop 0, huat.eventually_gt_atTop 0] with n hna hn
    have ha0 : a n ≠ 0 := hna.ne'
    field_simp [ha0, hn.ne', hu.ne']
  have hjRatio : Tendsto (fun n => ((j n : ℕ) : ℝ) / (u * a n)) atTop (𝓝 1) := by
    have h := hc.mul hxrel
    apply (by simpa [mul_comm] using h : Tendsto (fun n : ℕ =>
      (((j n : ℕ) : ℝ) / (u * a n + 1)) * ((u * a n + 1) / (u * a n))) atTop (𝓝 1)).congr'
    filter_upwards [huat.eventually_gt_atTop 0] with n hn
    have hn1 : 0 < u * a n + 1 := by linarith
    field_simp [hn.ne', hn1.ne']
  have hLratio : Tendsto (fun n => L (j n) / L (u * a n)) atTop (𝓝 1) :=
    slowlyVarying_ratio_of_relative_tendsto_one_filter hpos hL hsv huat hjRatio
  have hLaRatio : Tendsto (fun n => L (u * a n) / L (a n)) atTop (𝓝 1) :=
    (hsv u hu).comp hat
  have hLj : Tendsto (fun n => L (j n) / L (a n)) atTop (𝓝 1) := by
    have hh := hLratio.mul hLaRatio
    apply (show Tendsto (fun n : ℕ => (L (j n) / L (u * a n)) *
      (L (u * a n) / L (a n))) atTop (𝓝 1) by simpa using hh).congr'
    filter_upwards [huat.eventually_gt_atTop 0] with n hn
    have hua : L (u * a n) ≠ 0 := (hpos _ hn).ne'
    field_simp [hua]
  have hlocalj := hlocal.comp hjTop
  have hsd := scaling_div_mul_tendsto_one μ hm hpos hL hsv hlocal ha
  have hnorm0 := (tendsto_const_nhds (x := (1 : ℝ))).div hsd one_ne_zero
  have hnorm : Tendsto (fun n : ℕ => (n : ℝ) * L (a n) / a n) atTop (𝓝 1) := by
    apply (show Tendsto (fun n : ℕ => 1 / (a n / ((n : ℝ) * L (a n)))) atTop (𝓝 1) by
      simpa only [Pi.div_def, div_one] using hnorm0).congr'
    filter_upwards [hat.eventually_gt_atTop 0, eventually_gt_atTop (0 : ℕ)] with n han hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hLa : L (a n) ≠ 0 := (hpos _ han).ne'
    field_simp [han.ne', hn0.ne', hLa]
  have hAjRatio : Tendsto (fun n : ℕ => a n / (j n : ℝ)) atTop (𝓝 (1 / u)) := by
    have hh : Tendsto (fun n : ℕ => (1 / u) * ((j n : ℝ) / (u * a n))⁻¹)
        atTop (𝓝 ((1 / u) * 1⁻¹)) := (hjRatio.inv₀ one_ne_zero).const_mul (1 / u)
    apply (by simpa using hh : Tendsto (fun n : ℕ => (1 / u) * ((j n : ℝ) / (u * a n))⁻¹)
      atTop (𝓝 (1 / u))).congr'
    filter_upwards [huat.eventually_gt_atTop 0] with n hn
    field_simp [hn.ne', hu.ne']
  have hinv : Tendsto (fun n : ℕ => 1 / a n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hat
  have hprod := ((((hnorm.mul hlocalj).mul hLj).mul (hAjRatio.pow 2)).mul hinv)
  have hlim : Tendsto (fun n : ℕ =>
      (((((n : ℝ) * L (a n) / a n) * ((μ {j n}).toReal / (L (j n) / (j n : ℝ) ^ 2))) *
      (L (j n) / L (a n))) * ((a n / (j n : ℝ)) ^ 2)) * (1 / a n)) atTop (𝓝 0) := by
    convert hprod using 1 <;> norm_num
  apply hlim.congr'
  filter_upwards [hat.eventually_gt_atTop 0, hjTop.eventually_gt_atTop 0, huat.eventually_gt_atTop 0]
    with n han hjn huan
  have hj0 : (0 : ℝ) < (j n : ℝ) := by exact_mod_cast hjn
  have hLj0 : L (j n) ≠ 0 := (hpos _ hj0).ne'
  have hLa0 : L (a n) ≠ 0 := (hpos _ han).ne'
  dsimp [j]
  have hLceil : L ⌈u * a n + 1⌉₊ = L (j n) := rfl
  rw [← hLceil] at hLj0
  field_simp [han.ne', hj0.ne', hLj0, hLa0, huan.ne', hu.ne']
  have hLj0' : L ⌈a n * u + 1⌉₊ ≠ 0 := by convert hLj0 using 1; ring
  field_simp [hLj0']

lemma rescaled_strictIncrementTail_tendsto
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) {u : ℝ} (hu : 0 < u) :
    Tendsto (fun n : ℕ => (n : ℝ) * (strictIncrementTail μ (u * a n)).toReal)
      atTop (𝓝 (1 / u)) := by
  have hnon := rescaled_incrementTail_tendsto μ hμ a ha hu
  have hgap : Tendsto (fun n : ℕ => (n : ℝ) *
      ((incrementTail μ (u * a n)).toReal - (strictIncrementTail μ (u * a n)).toReal))
      atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun n : ℕ => (n : ℝ) * (μ {⌈u * a n + 1⌉₊}).toReal)
    · exact Eventually.of_forall fun n => by
        have h0 := ENNReal.toReal_nonneg (a := incrementTail μ (u * a n))
        have h1 := ENNReal.toReal_mono (measure_ne_top μ _)
          (show strictIncrementTail μ (u * a n) ≤ incrementTail μ (u * a n) from
            measure_mono (fun k hk => by
              change u * a n < (k : ℝ) - 1 at hk
              exact hk.le))
        dsimp [incrementTail, strictIncrementTail]
        exact mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr h1)
    · filter_upwards [] with n
      exact mul_le_mul_of_nonneg_left (incrementTail_strict_gap_le_atom μ (u * a n))
        (Nat.cast_nonneg n)
    · exact rescaled_incrementAtom_tendsto_zero μ hμ a ha hu
  have h := hnon.sub hgap
  apply (show Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (u * a n)).toReal -
      (n : ℝ) * ((incrementTail μ (u * a n)).toReal -
        (strictIncrementTail μ (u * a n)).toReal)) atTop (𝓝 (1 / u)) by
      convert h using 1; simp).congr'
  filter_upwards [] with n
  ring

lemma oneStep_nat_div_scale_sq_tendsto_zero
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => (n : ℝ) / (a n) ^ 2) atTop (𝓝 0) := by
  obtain ⟨hm, L, hpos, hsv, hL, hlocal⟩ := hμ
  let hlit : IsSubcriticalCauchyOffspring μ := ⟨hm, L, hpos, hsv, hlocal⟩
  have hat : Tendsto a atTop atTop := scaling_tendsto_atTop μ hlit ha
  have hsd := scaling_div_mul_tendsto_one μ hm hpos hL hsv hlocal ha
  have hnorm0 := (tendsto_const_nhds (x := (1 : ℝ))).div hsd one_ne_zero
  have hnorm : Tendsto (fun n : ℕ => (n : ℝ) * L (a n) / a n) atTop (𝓝 1) := by
    apply (show Tendsto (fun n : ℕ => 1 / (a n / ((n : ℝ) * L (a n)))) atTop (𝓝 1) by
      simpa only [Pi.div_def, div_one] using hnorm0).congr'
    filter_upwards [hat.eventually_gt_atTop 0, eventually_gt_atTop (0 : ℕ)] with n han hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hLa : L (a n) ≠ 0 := (hpos _ han).ne'
    field_simp [han.ne', hn0.ne', hLa]
  have hceilTop : Tendsto (fun n => ⌈a n⌉₊) atTop atTop := tendsto_nat_ceil_atTop.comp hat
  have hceilRatio : Tendsto (fun n => (⌈a n⌉₊ : ℝ) / a n) atTop (𝓝 1) :=
    tendsto_nat_ceil_div_atTop.comp hat
  have hLratio : Tendsto (fun n => L (⌈a n⌉₊) / L (a n)) atTop (𝓝 1) :=
    slowlyVarying_ratio_of_relative_tendsto_one_filter hpos hL hsv hat hceilRatio
  have hnatTop : Tendsto (fun n : ℕ => (⌈a n⌉₊ : ℝ) * L (⌈a n⌉₊)) atTop atTop :=
    (natCast_mul_tendsto_atTop_of_potter hpos hL hsv).comp hceilTop
  have hpair : Tendsto (fun n : ℕ => (a n / (⌈a n⌉₊ : ℝ)) *
      (L (a n) / L (⌈a n⌉₊))) atTop (𝓝 1) := by
    have hh := (hceilRatio.inv₀ one_ne_zero).mul (hLratio.inv₀ one_ne_zero)
    simpa using hh
  have haLtop0 : Tendsto (fun n : ℕ =>
      ((⌈a n⌉₊ : ℝ) * L (⌈a n⌉₊)) *
        ((a n / (⌈a n⌉₊ : ℝ)) * (L (a n) / L (⌈a n⌉₊)))) atTop atTop :=
    hnatTop.atTop_mul_pos zero_lt_one hpair
  have haLtop : Tendsto (fun n : ℕ => a n * L (a n)) atTop atTop := by
    apply haLtop0.congr'
    filter_upwards [hat.eventually_gt_atTop 0, hceilTop.eventually_gt_atTop 0] with n han hcn
    have ha0 : (⌈a n⌉₊ : ℝ) ≠ 0 := by exact_mod_cast hcn.ne'
    have hLj : L (⌈a n⌉₊) ≠ 0 := (hpos _ (by exact_mod_cast hcn)).ne'
    field_simp [ha0, hLj]
  have hzero := hnorm.div_atTop haLtop
  apply hzero.congr'
  filter_upwards [hat.eventually_gt_atTop 0] with n han
  have hLa : L (a n) ≠ 0 := (hpos _ han).ne'
  field_simp [han.ne', hLa]

lemma strictIncrementTail_toReal_le (μ : Measure ℕ) [IsProbabilityMeasure μ] (x : ℝ) :
    (strictIncrementTail μ x).toReal ≤ (incrementTail μ x).toReal :=
  ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (fun k hk => by
    change x < (k : ℝ) - 1 at hk
    exact hk.le))

/-- A Potter majorant for the rescaled tail on shrinking factors bounded below
by an arbitrary fixed threshold. -/
lemma rescaled_incrementTail_shrinking_potter_bound
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) :
    ∃ C R : ℝ, 0 < C ∧ 0 < R ∧ ∀ᶠ n : ℕ in atTop, ∀ u : ℝ,
      0 < u → u ≤ 1 → R ≤ u * a n →
      (n : ℝ) * (incrementTail μ (u * a n)).toReal ≤ C * u ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨hm, L, hpos, hsv, hL, hlocal⟩ := hμ
  let hlit : IsSubcriticalCauchyOffspring μ := ⟨hm, L, hpos, hsv, hlocal⟩
  obtain ⟨C, hC, R, hR, hpot⟩ := potter_bounds hpos hL hsv (1 / 2) (by norm_num)
  obtain ⟨X, hX⟩ := eventually_atTop.mp
    ((incrementTail_div_tendsto_one μ hm hpos hL hsv hlocal).eventually
      (Iio_mem_nhds (show (1 : ℝ) < 2 by norm_num)))
  let D := max R X
  have hD : 0 < D := lt_max_of_lt_left hR
  refine ⟨8 * C, D, by positivity, hD, ?_⟩
  have hat : Tendsto a atTop atTop := scaling_tendsto_atTop μ hlit ha
  have hTa := (incrementTail_div_tendsto_one μ hm hpos hL hsv hlocal).comp hat
  have hTaInv : Tendsto (fun n : ℕ =>
      1 / ((incrementTail μ (a n)).toReal / (L (a n) / a n))) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Pi.div_def, one_div, div_one] using
      (tendsto_const_nhds (x := (1 : ℝ))).div hTa one_ne_zero
  filter_upwards [ha.eventually (Iio_mem_nhds (show (1 : ℝ) < 2 by norm_num)),
    hTaInv.eventually (Iio_mem_nhds (show (1 : ℝ) < 2 by norm_num)),
    hat.eventually_ge_atTop D, hat.eventually_ge_atTop 1] with n han hTainv haD ha1
  intro u hu hu1 huaD
  have haD0 : 1 ≤ a n := ha1
  have ha0 : 0 < a n := zero_lt_one.trans_le ha1
  have hua0 : 0 < u * a n := mul_pos hu ha0
  have hau : u * a n ≤ a n := by nlinarith
  have huX : X ≤ u * a n := (le_max_right R X).trans huaD
  have huR : R ≤ u * a n := (le_max_left R X).trans huaD
  have hTu2 : (incrementTail μ (u * a n)).toReal / (L (u * a n) / (u * a n)) < 2 := hX _ huX
  have htuprod : (n : ℝ) * (incrementTail μ (u * a n)).toReal =
      (((((n : ℝ) * (incrementTail μ (a n)).toReal) *
        ((incrementTail μ (u * a n)).toReal / (L (u * a n) / (u * a n)))) *
        (1 / ((incrementTail μ (a n)).toReal / (L (a n) / a n)))) *
        (L (u * a n) / L (a n))) * (a n / (u * a n)) := by
    have hTa0 : (incrementTail μ (a n)).toReal ≠ 0 :=
      (ENNReal.toReal_pos (incrementTail_pos μ hlit (a n)).ne' (measure_ne_top _ _)).ne'
    have hTu0 : (incrementTail μ (u * a n)).toReal ≠ 0 :=
      (ENNReal.toReal_pos (incrementTail_pos μ hlit (u * a n)).ne' (measure_ne_top _ _)).ne'
    have hLa : L (a n) ≠ 0 := (hpos _ ha0).ne'
    have hLua : L (u * a n) ≠ 0 := (hpos _ hua0).ne'
    field_simp [hTa0, hTu0, hLa, hLua, hua0.ne', hu.ne']
  have hp0 := (hpot (u * a n) (a n) huR hau).1
  have hfactor : a n / (u * a n) = 1 / u := by field_simp [ha0.ne', hu.ne']
  rw [hfactor] at hp0
  have hLup : L (u * a n) / L (a n) ≤ C * u ^ (-(1 / 2 : ℝ)) := by
    have hq : 0 < (1 / u) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
    have huq : 0 < C⁻¹ * (1 / u) ^ (-(1 / 2 : ℝ)) := mul_pos (inv_pos.mpr hC) hq
    have hLya : L (u * a n) ≠ 0 := (hpos _ hua0).ne'
    have hLa : L (a n) ≠ 0 := (hpos _ ha0).ne'
    have hLdiv : 0 < L (a n) / L (u * a n) := div_pos (hpos _ ha0) (hpos _ hua0)
    have hh' := (inv_le_inv₀ hLdiv huq).mpr hp0
    have hinv : L (u * a n) / L (a n) = (L (a n) / L (u * a n))⁻¹ := by
      field_simp [hLya, hLa]
    have hpow : ((1 / u) ^ (-(1 / 2 : ℝ)))⁻¹ = u ^ (-(1 / 2 : ℝ)) := by
      simp [Real.rpow_neg_eq_inv_rpow, inv_inv, one_div]
      rw [Real.inv_rpow hu.le]
    rw [hinv]
    calc
      (L (a n) / L (u * a n))⁻¹ ≤ (C⁻¹ * (1 / u) ^ (-(1 / 2 : ℝ)))⁻¹ := hh'
      _ = C * u ^ (-(1 / 2 : ℝ)) := by rw [mul_inv, inv_inv, hpow]
  have hInv : 0 < 1 / ((incrementTail μ (a n)).toReal / (L (a n) / a n)) := by
    apply div_pos zero_lt_one
    exact div_pos (ENNReal.toReal_pos (incrementTail_pos μ hlit (a n)).ne'
      (measure_ne_top _ _)) (div_pos (hpos _ ha0) ha0)
  have hTailNonneg : 0 ≤ (incrementTail μ (u * a n)).toReal / (L (u * a n) / (u * a n)) :=
    div_nonneg ENNReal.toReal_nonneg (div_pos (hpos _ hua0) hua0).le
  have hLnonneg : 0 ≤ L (u * a n) / L (a n) :=
    div_nonneg (hpos _ hua0).le (hpos _ ha0).le
  rw [htuprod]
  have hgrid := hfactor
  rw [hgrid]
  calc
    (((((n : ℝ) * (incrementTail μ (a n)).toReal) *
        ((incrementTail μ (u * a n)).toReal / (L (u * a n) / (u * a n)))) *
        (1 / ((incrementTail μ (a n)).toReal / (L (a n) / a n)))) *
        (L (u * a n) / L (a n))) * (1 / u)
      ≤ ((((2 * 2) * 2) * (C * u ^ (-(1 / 2 : ℝ)))) * (1 / u)) := by gcongr
    _ = (8 * C) * u ^ (-(3 / 2 : ℝ)) := by
      rw [show (1 : ℝ) / u = u ^ (-1 : ℝ) by simp [Real.rpow_neg_one]]
      rw [show (-(3 / 2 : ℝ)) = (-(1 / 2 : ℝ)) + (-1 : ℝ) by ring, Real.rpow_add hu]
      ring

end
end SubcriticalCauchy.Bienayme
