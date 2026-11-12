module

public import SubcriticalCauchy.DegreeFluctuationsAux
public import SubcriticalCauchy.Centering
public import SubcriticalCauchy.IncrementTailAsymptotics
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Deterministic and total-variation helpers for Corollary 4.1 -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators

namespace SubcriticalCauchy.Bienayme

noncomputable section
open BGW BGW.LocallyFinite

/-- Expectations of functions bounded by one differ by at most the unhalved
total-variation distance on a countable probability space. -/
theorem bounded_integral_sub_le_tvDist
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {g : α → ℝ} (hg : ∀ x, |g x| ≤ 1) :
    |∫ x, g x ∂P - ∫ x, g x ∂Q| ≤ tvDist P Q := by
  have hP : Integrable g P :=
    Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hg x)
  have hQ : Integrable g Q :=
    Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hg x)
  rw [integral_countable hP, integral_countable hQ]
  have hsP : Summable fun z => P.real {z} := by
    apply ENNReal.summable_toReal
    rw [show (∑' z, P {z}) = 1 by
      simpa using P.tsum_indicator_apply_singleton Set.univ MeasurableSet.univ]
    simp
  have hsQ : Summable fun z => Q.real {z} := by
    apply ENNReal.summable_toReal
    rw [show (∑' z, Q {z}) = 1 by
      simpa using Q.tsum_indicator_apply_singleton Set.univ MeasurableSet.univ]
    simp
  have hsPg : Summable fun z => P.real {z} * g z :=
    hsP.of_norm_bounded (fun z => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg measureReal_nonneg]
      simpa only [one_mul, mul_one] using
        mul_le_mul_of_nonneg_left (hg z) measureReal_nonneg)
  have hsQg : Summable fun z => Q.real {z} * g z :=
    hsQ.of_norm_bounded (fun z => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg measureReal_nonneg]
      simpa only [one_mul, mul_one] using
        mul_le_mul_of_nonneg_left (hg z) measureReal_nonneg)
  simp only [smul_eq_mul]
  rw [← hsPg.tsum_sub hsQg, tvDist_eq_tsum_abs]
  have hsDiff := hsPg.sub hsQg
  calc
    |∑' z, (P.real {z} * g z - Q.real {z} * g z)| ≤
        ∑' z, |P.real {z} * g z - Q.real {z} * g z| := by
      simpa only [Real.norm_eq_abs] using
        (norm_tsum_le_tsum_norm
          (f := fun z => P.real {z} * g z - Q.real {z} * g z) hsDiff.abs)
    _ ≤ ∑' z, |P.real {z} - Q.real {z}| := by
      apply hsDiff.abs.tsum_le_tsum _ (hsP.sub hsQ).abs
      intro z
      rw [← sub_mul, abs_mul]
      simpa only [one_mul, mul_one] using mul_le_mul_of_nonneg_left (hg z)
        (abs_nonneg (P.real {z} - Q.real {z}))

/-- Scaled version of `bounded_integral_sub_le_tvDist`. -/
theorem bounded_integral_sub_le_mul_tvDist
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {g : α → ℝ} {M : ℝ} (hM : 0 < M) (hg : ∀ x, |g x| ≤ M) :
    |∫ x, g x ∂P - ∫ x, g x ∂Q| ≤ M * tvDist P Q := by
  have hscaled := bounded_integral_sub_le_tvDist P Q (g := fun x => g x / M)
    (fun x => by
      rw [abs_div, abs_of_pos hM, div_le_one hM]
      exact hg x)
  have heq : (∫ x, g x ∂P) - (∫ x, g x ∂Q) =
      M * ((∫ x, g x / M ∂P) - (∫ x, g x / M ∂Q)) := by
    simp only [integral_div]
    field_simp [hM.ne']
  rw [heq, abs_mul, abs_of_pos hM]
  exact mul_le_mul_of_nonneg_left hscaled hM.le

private theorem natCast_pred_tendsto_atTop :
    Tendsto (fun n : ℕ => ((n - 1 : ℕ) : ℝ)) atTop atTop := by
  apply (tendsto_add_atTop_iff_nat
    (f := fun n : ℕ => ((n - 1 : ℕ) : ℝ)) 1).mp
  simpa only [Nat.add_sub_cancel] using
    (tendsto_natCast_atTop_atTop (R := ℝ))

private theorem natCast_div_pred_tendsto_one :
    Tendsto (fun n : ℕ => (n : ℝ) / ((n - 1 : ℕ) : ℝ)) atTop (𝓝 1) := by
  have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / ((n - 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop natCast_pred_tendsto_atTop
  have h := (tendsto_const_nhds (x := (1 : ℝ))).add hinv
  have heq : (fun n : ℕ => 1 + 1 / ((n - 1 : ℕ) : ℝ)) =ᶠ[atTop]
      (fun n : ℕ => (n : ℝ) / ((n - 1 : ℕ) : ℝ)) := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
    have hn0 : ((n - 1 : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (show n - 1 ≠ 0 by omega)
    field_simp [hn0]
    norm_cast
    omega
  simpa only [add_zero] using h.congr' heq

private theorem scaled_incrementTail_pred (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a (n - 1))).toReal)
      atTop (𝓝 1) := by
  have hprev : Tendsto (fun n : ℕ =>
      ((n - 1 : ℕ) : ℝ) * (incrementTail μ (a (n - 1))).toReal) atTop (𝓝 1) := by
    apply (tendsto_add_atTop_iff_nat (f := fun n : ℕ =>
      ((n - 1 : ℕ) : ℝ) * (incrementTail μ (a (n - 1))).toReal) 1).mp
    simpa only [Nat.add_sub_cancel] using ha
  have hprod := hprev.mul natCast_div_pred_tendsto_one
  have heq : (fun n : ℕ =>
      (((n - 1 : ℕ) : ℝ) * (incrementTail μ (a (n - 1))).toReal) *
        ((n : ℝ) / ((n - 1 : ℕ) : ℝ))) =ᶠ[atTop]
      (fun n : ℕ => (n : ℝ) * (incrementTail μ (a (n - 1))).toReal) := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
    have hn0 : ((n - 1 : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (show n - 1 ≠ 0 by omega)
    field_simp [hn0]
  simpa only [one_mul] using hprod.congr' heq

private theorem incrementTail_pred_div_tendsto_one
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) :
    Tendsto (fun n : ℕ =>
      (incrementTail μ (a (n - 1))).toReal / (incrementTail μ (a n)).toReal)
      atTop (𝓝 1) := by
  have h := (scaled_incrementTail_pred μ a ha).div ha one_ne_zero
  have heq : (fun n : ℕ =>
      ((n : ℝ) * (incrementTail μ (a (n - 1))).toReal) /
        ((n : ℝ) * (incrementTail μ (a n)).toReal)) =ᶠ[atTop]
      (fun n : ℕ =>
        (incrementTail μ (a (n - 1))).toReal / (incrementTail μ (a n)).toReal) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have hcurr := (ENNReal.toReal_pos
      (incrementTail_pos μ hμ.to_literal (a n)).ne' (measure_ne_top _ _)).ne'
    field_simp [hn0, hcurr]
  simpa only [div_one] using h.congr' heq

private theorem incrementTail_const_mul_div_tendsto (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (hμ : IsMeasurableSubcriticalCauchyOffspring μ)
    (a : ℕ → ℝ) (haTop : Tendsto a atTop atTop) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ =>
      (incrementTail μ (c * a n)).toReal / (incrementTail μ (a n)).toReal)
      atTop (𝓝 (1 / c)) := by
  obtain ⟨hm, L, hpos, hsv, hmeas, hlocal⟩ := hμ
  have hcurr := (incrementTail_div_tendsto_one μ hm hpos hmeas hsv hlocal).comp haTop
  have hscaled := (incrementTail_div_tendsto_one μ hm hpos hmeas hsv hlocal).comp
    (haTop.const_mul_atTop hc)
  have hL := (hsv c hc).comp haTop
  have hcurrInv : Tendsto (fun n : ℕ =>
      (L (a n) / a n) / (incrementTail μ (a n)).toReal) atTop (𝓝 1) := by
    simpa only [Pi.div_def, one_div, inv_div, div_one, Function.comp_def] using
      (tendsto_const_nhds (x := (1 : ℝ))).div hcurr one_ne_zero
  have hprod := hscaled.mul (hL.const_mul (1 / c)) |>.mul hcurrInv
  have heq : (fun n : ℕ =>
      ((incrementTail μ (c * a n)).toReal / (L (c * a n) / (c * a n))) *
        ((1 / c) * (L (c * a n) / L (a n))) *
        ((L (a n) / a n) / (incrementTail μ (a n)).toReal)) =ᶠ[atTop]
      (fun n : ℕ =>
        (incrementTail μ (c * a n)).toReal / (incrementTail μ (a n)).toReal) := by
    filter_upwards [haTop.eventually_gt_atTop 0] with n han
    have hca : 0 < c * a n := mul_pos hc han
    have hLc : 0 < L (c * a n) := hpos _ hca
    have hLa : 0 < L (a n) := hpos _ han
    have hTc : (incrementTail μ (c * a n)).toReal ≠ 0 :=
      (ENNReal.toReal_pos (incrementTail_pos μ ⟨hm, ⟨L, hpos, hsv, hlocal⟩⟩
        (c * a n)).ne' (measure_ne_top _ _)).ne'
    have hTa : (incrementTail μ (a n)).toReal ≠ 0 :=
      (ENNReal.toReal_pos (incrementTail_pos μ ⟨hm, ⟨L, hpos, hsv, hlocal⟩⟩
        (a n)).ne' (measure_ne_top _ _)).ne'
    field_simp [hc.ne', han.ne', hLc.ne', hLa.ne', hTc, hTa]
  simpa only [Function.comp_def, one_mul, inv_one, mul_one] using hprod.congr' heq

/-- Adjacent values of every source-normalized scale have asymptotic ratio one. -/
theorem scaling_pred_div_tendsto_one
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => a (n - 1) / a n) atTop (𝓝 1) := by
  have haTop := scaling_tendsto_atTop μ hμ.to_literal ha
  have hprevTop : Tendsto (fun n : ℕ => a (n - 1)) atTop atTop := by
    apply (tendsto_add_atTop_iff_nat (f := fun n : ℕ => a (n - 1)) 1).mp
    simpa only [Nat.add_sub_cancel] using haTop
  have htail := incrementTail_pred_div_tendsto_one μ hμ a ha
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro d hd
    by_cases hd0 : 0 < d
    · have hd1 : 1 < 1 / d := (one_lt_one_div hd0) hd
      let m := (1 + 1 / d) / 2
      have hm₁ : 1 < m := by dsimp [m]; linarith
      have hm₂ : m < 1 / d := by dsimp [m]; linarith
      have hfixed := incrementTail_const_mul_div_tendsto μ hμ a haTop hd0
      by_contra hev
      have hfreq : ∃ᶠ n in atTop, a (n - 1) / a n ≤ d := by
        simpa only [not_lt] using not_eventually.mp hev
      obtain ⟨n, hnle, hpos, hprev, hcurr⟩ := (hfreq.and_eventually
        (haTop.eventually_gt_atTop 0 |>.and
          (htail.eventually (Iio_mem_nhds hm₁) |>.and
            (hfixed.eventually (Ioi_mem_nhds hm₂))))).exists
      have huv : a (n - 1) ≤ d * a n := (div_le_iff₀ hpos).mp hnle
      have htailmono : (incrementTail μ (d * a n)).toReal ≤
          (incrementTail μ (a (n - 1))).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) (incrementTail_antitone μ huv)
      have hTpos : 0 < (incrementTail μ (a n)).toReal :=
        ENNReal.toReal_pos (incrementTail_pos μ hμ.to_literal _).ne' (measure_ne_top _ _)
      have hle := (div_le_div_iff_of_pos_right hTpos).mpr htailmono
      linarith
    · filter_upwards [haTop.eventually_gt_atTop 0, hprevTop.eventually_gt_atTop 0]
        with n han hprev
      have hratio : 0 < a (n - 1) / a n := div_pos hprev han
      linarith
  · intro c hc
    have hc0 : 0 < c := zero_lt_one.trans hc
    have hcinv : 1 / c < 1 := (div_lt_one hc0).mpr hc
    let m := (1 + 1 / c) / 2
    have hm₁ : 1 / c < m := by dsimp [m]; linarith
    have hm₂ : m < 1 := by dsimp [m]; linarith
    have hfixed := incrementTail_const_mul_div_tendsto μ hμ a haTop hc0
    by_contra hev
    have hfreq : ∃ᶠ n in atTop, c ≤ a (n - 1) / a n := by
      simpa only [not_lt] using not_eventually.mp hev
    obtain ⟨n, hnle, hpos, hprev, hcurr⟩ := (hfreq.and_eventually
      (haTop.eventually_gt_atTop 0 |>.and
        (htail.eventually (Ioi_mem_nhds hm₂) |>.and
          (hfixed.eventually (Iio_mem_nhds hm₁))))).exists
    have huv : c * a n ≤ a (n - 1) := (le_div_iff₀ hpos).mp hnle
    have htailmono : (incrementTail μ (a (n - 1))).toReal ≤
        (incrementTail μ (c * a n)).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (incrementTail_antitone μ huv)
    have hTpos : 0 < (incrementTail μ (a n)).toReal :=
      ENNReal.toReal_pos (incrementTail_pos μ hμ.to_literal _).ne' (measure_ne_top _ _)
    have hle := (div_le_div_iff_of_pos_right hTpos).mpr htailmono
    linarith

private theorem incrementTail_add_one_div_tendsto_one
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (haTop : Tendsto a atTop atTop) :
    Tendsto (fun n : ℕ =>
      (incrementTail μ (a n + 1)).toReal / (incrementTail μ (a n)).toReal)
      atTop (𝓝 1) := by
  have htailpos : ∀ᶠ n in atTop, 0 < (incrementTail μ (a n)).toReal :=
    Eventually.of_forall fun _ => ENNReal.toReal_pos
      (incrementTail_pos μ hμ.to_literal _).ne' (measure_ne_top _ _)
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro d hd
    by_cases hd0 : 0 < d
    · let c := 2 / (d + 1)
      have hc0 : 0 < c := by dsimp [c]; positivity
      have hc1 : 1 < c := by
        dsimp [c]
        exact (one_lt_div (by positivity)).mpr (by linarith)
      have hdc : d < 1 / c := by
        dsimp [c]
        field_simp [hc0.ne']
        nlinarith
      have hfixed := incrementTail_const_mul_div_tendsto μ hμ a haTop hc0
      filter_upwards [hfixed.eventually (Ioi_mem_nhds hdc),
        haTop.eventually_ge_atTop (1 / (c - 1)), htailpos] with n hn hbig hT
      have hca : a n + 1 ≤ c * a n := by
        have hden : 0 < c - 1 := sub_pos.mpr hc1
        have hh := (div_le_iff₀ hden).mp hbig
        nlinarith
      have hmono : (incrementTail μ (c * a n)).toReal ≤
          (incrementTail μ (a n + 1)).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) (incrementTail_antitone μ hca)
      exact hn.trans_le ((div_le_div_iff_of_pos_right hT).mpr hmono)
    · filter_upwards [htailpos] with n hT
      have hratio : 0 < (incrementTail μ (a n + 1)).toReal /
          (incrementTail μ (a n)).toReal := div_pos
        (ENNReal.toReal_pos (incrementTail_pos μ hμ.to_literal _).ne'
          (measure_ne_top _ _)) hT
      linarith
  · intro b hb
    filter_upwards [htailpos] with n hT
    have hmono : (incrementTail μ (a n + 1)).toReal ≤
        (incrementTail μ (a n)).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _)
        (incrementTail_antitone μ (by linarith))
    calc
      _ ≤ (incrementTail μ (a n)).toReal / (incrementTail μ (a n)).toReal :=
        (div_le_div_iff_of_pos_right hT).mpr hmono
      _ = 1 := div_self hT.ne'
      _ < b := hb

private theorem scaled_incrementTail_add_one
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n + 1)).toReal)
      atTop (𝓝 1) := by
  have haTop := scaling_tendsto_atTop μ hμ.to_literal ha
  have hprod := ha.mul (incrementTail_add_one_div_tendsto_one μ hμ a haTop)
  have heq : (fun n : ℕ =>
      ((n : ℝ) * (incrementTail μ (a n)).toReal) *
        ((incrementTail μ (a n + 1)).toReal / (incrementTail μ (a n)).toReal)) =ᶠ[atTop]
      (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n + 1)).toReal) := by
    filter_upwards [] with n
    have hT := (ENNReal.toReal_pos
      (incrementTail_pos μ hμ.to_literal (a n)).ne' (measure_ne_top _ _)).ne'
    field_simp [hT]
  simpa only [one_mul] using hprod.congr' heq

private noncomputable def cutoffTailGap (μ : Measure ℕ) (r s : ℝ) : ℝ :=
  ((incrementTail μ r).toReal - (incrementTail μ (r + 1)).toReal) +
    ((incrementTail μ s).toReal - (incrementTail μ (s + 1)).toReal) +
    |(incrementTail μ r).toReal - (incrementTail μ s).toReal|

private theorem cutoffTailGap_nonneg (μ : Measure ℕ) [IsProbabilityMeasure μ] {r s : ℝ} :
    0 ≤ cutoffTailGap μ r s := by
  have hr : (incrementTail μ (r + 1)).toReal ≤ (incrementTail μ r).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (incrementTail_antitone μ (by linarith))
  have hs : (incrementTail μ (s + 1)).toReal ≤ (incrementTail μ s).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (incrementTail_antitone μ (by linarith))
  dsimp only [cutoffTailGap]
  positivity

private theorem abs_truncatedIncrementMean_sub_le
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ ≠ ∞)
    {r s : ℝ} (hr : 1 ≤ r) (hs : 1 ≤ s) :
    |truncatedIncrementMean μ r - truncatedIncrementMean μ s| ≤
      (r + s) * cutoffTailGap μ r s := by
  let X : ℕ → ℝ := offspringIncrement
  let E : Set ℕ := {k | min r s < |X k| ∧ |X k| ≤ max r s}
  let A : Set ℕ := {k | min r s ≤ X k}
  let B : Set ℕ := {k | max r s + 1 ≤ X k}
  have hmin : 1 ≤ min r s := le_min hr hs
  have hpoint (k : ℕ) :
      |(if |X k| ≤ r then X k else 0) - (if |X k| ≤ s then X k else 0)| ≤
        (r + s) * E.indicator (fun _ => (1 : ℝ)) k := by
    by_cases hrk : |X k| ≤ r
    · by_cases hsk : |X k| ≤ s
      · simp only [hrk, hsk, ite_true, sub_self, abs_zero]
        exact mul_nonneg (by linarith) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
      · have hsr : s ≤ r := by
          exact (lt_of_not_ge hsk).le.trans hrk
        have hkE : k ∈ E := by
          constructor
          · rw [min_eq_right hsr]
            exact lt_of_not_ge hsk
          · rw [max_eq_left hsr]
            exact hrk
        simp [hrk, hsk, hkE]
        linarith [abs_nonneg (X k)]
    · by_cases hsk : |X k| ≤ s
      · have hrs : r ≤ s := by
          exact (lt_of_not_ge hrk).le.trans hsk
        have hkE : k ∈ E := by
          constructor
          · rw [min_eq_left hrs]
            exact lt_of_not_ge hrk
          · rw [max_eq_right hrs]
            exact hsk
        simp [hrk, hsk, hkE]
        linarith [abs_nonneg (X k)]
      · simp only [hrk, hsk, ite_false, sub_self, abs_zero]
        exact mul_nonneg (by linarith) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  have hleft : Integrable (fun k =>
      |(if |X k| ≤ r then X k else 0) - (if |X k| ≤ s then X k else 0)|) μ := by
    exact ((integrable_truncatedIncrement μ hm r).sub
      (integrable_truncatedIncrement μ hm s)).abs
  have hright : Integrable (fun k => (r + s) * E.indicator (fun _ => (1 : ℝ)) k) μ := by
    exact ((integrable_const (1 : ℝ)).indicator (Set.to_countable E).measurableSet).const_mul _
  have hEA : E ⊆ A \ B := by
    intro k hk
    have hX : 0 ≤ X k := by
      by_contra hneg
      have hneg' : X k < 0 := lt_of_not_ge hneg
      have hk1 := hk.1
      rw [abs_of_neg hneg'] at hk1
      dsimp only [X, offspringIncrement] at hk1
      nlinarith
    have habs : |X k| = X k := abs_of_nonneg hX
    constructor
    · change min r s ≤ X k
      rw [← habs]
      exact hk.1.le
    · change ¬max r s + 1 ≤ X k
      rw [← habs]
      linarith [hk.2]
  have hBA : B ⊆ A := by
    intro k hk
    change min r s ≤ X k
    change max r s + 1 ≤ X k at hk
    exact min_le_max.trans (by linarith)
  calc
    |truncatedIncrementMean μ r - truncatedIncrementMean μ s| =
        |∫ k, ((if |X k| ≤ r then X k else 0) -
          (if |X k| ≤ s then X k else 0)) ∂μ| := by
      rw [integral_sub (integrable_truncatedIncrement μ hm r)
        (integrable_truncatedIncrement μ hm s)]
      rfl
    _ ≤ ∫ k, |(if |X k| ≤ r then X k else 0) -
        (if |X k| ≤ s then X k else 0)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ k, (r + s) * E.indicator (fun _ => (1 : ℝ)) k ∂μ :=
      integral_mono_ae hleft hright (Eventually.of_forall hpoint)
    _ = (r + s) * μ.real E := by
      rw [integral_const_mul,
        show E.indicator (fun _ : ℕ => (1 : ℝ)) = E.indicator 1 from rfl,
        integral_indicator_one (Set.to_countable E).measurableSet]
    _ ≤ (r + s) * μ.real (A \ B) := by
      exact mul_le_mul_of_nonneg_left (measureReal_mono hEA (measure_ne_top _ _))
        (by linarith)
    _ = (r + s) * ((incrementTail μ (min r s)).toReal -
        (incrementTail μ (max r s + 1)).toReal) := by
      rw [measureReal_sdiff hBA (Set.to_countable B).measurableSet (measure_ne_top _ _)]
      rfl
    _ ≤ (r + s) * cutoffTailGap μ r s := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      rcases le_total r s with hrs | hsr
      · rw [min_eq_left hrs, max_eq_right hrs]
        have htail : (incrementTail μ s).toReal ≤ (incrementTail μ r).toReal :=
          ENNReal.toReal_mono (measure_ne_top _ _) (incrementTail_antitone μ hrs)
        dsimp only [cutoffTailGap]
        rw [abs_of_nonneg (sub_nonneg.mpr htail)]
        have hgap : (incrementTail μ (r + 1)).toReal ≤ (incrementTail μ r).toReal :=
          ENNReal.toReal_mono (measure_ne_top _ _) (incrementTail_antitone μ (by linarith))
        linarith
      · rw [min_eq_right hsr, max_eq_left hsr]
        have htail : (incrementTail μ r).toReal ≤ (incrementTail μ s).toReal :=
          ENNReal.toReal_mono (measure_ne_top _ _) (incrementTail_antitone μ hsr)
        dsimp only [cutoffTailGap]
        rw [abs_of_nonpos (sub_nonpos.mpr htail)]
        have hgap : (incrementTail μ (s + 1)).toReal ≤ (incrementTail μ s).toReal :=
          ENNReal.toReal_mono (measure_ne_top _ _) (incrementTail_antitone μ (by linarith))
        linarith

/-- Adjacent source centerings differ by `o(a_n)`. -/
theorem centering_pred_sub_div_tendsto_zero
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) :
    Tendsto (fun n : ℕ =>
      (centering μ a n - centering μ a (n - 1)) / a n) atTop (𝓝 0) := by
  have hfin : offspringMean μ ≠ ∞ :=
    ne_top_of_lt (hμ.1.trans ENNReal.one_lt_top)
  have haTop := scaling_tendsto_atTop μ hμ.to_literal ha
  have hprevTop : Tendsto (fun n : ℕ => a (n - 1)) atTop atTop := by
    apply (tendsto_add_atTop_iff_nat (f := fun n : ℕ => a (n - 1)) 1).mp
    simpa only [Nat.add_sub_cancel] using haTop
  have hprev := scaled_incrementTail_pred μ a ha
  have hprevAdd := scaled_incrementTail_add_one μ hμ (fun n => a (n - 1)) hprev
  have hadd := scaled_incrementTail_add_one μ hμ a ha
  have hDbase := ((hprev.sub hprevAdd).add (ha.sub hadd)).add ((hprev.sub ha).abs)
  have hD : Tendsto (fun n : ℕ =>
      (n : ℝ) * cutoffTailGap μ (a (n - 1)) (a n)) atTop (𝓝 0) := by
    have heq : (fun n : ℕ =>
        (((n : ℝ) * (incrementTail μ (a (n - 1))).toReal) -
          (n : ℝ) * (incrementTail μ (a (n - 1) + 1)).toReal) +
        (((n : ℝ) * (incrementTail μ (a n)).toReal) -
          (n : ℝ) * (incrementTail μ (a n + 1)).toReal) +
        |((n : ℝ) * (incrementTail μ (a (n - 1))).toReal) -
          (n : ℝ) * (incrementTail μ (a n)).toReal|) =ᶠ[atTop]
        (fun n : ℕ => (n : ℝ) * cutoffTailGap μ (a (n - 1)) (a n)) := by
      filter_upwards [] with n
      dsimp only [cutoffTailGap]
      have habs : |(n : ℝ) * (incrementTail μ (a (n - 1))).toReal -
          (n : ℝ) * (incrementTail μ (a n)).toReal| =
          (n : ℝ) * |(incrementTail μ (a (n - 1))).toReal -
            (incrementTail μ (a n)).toReal| := by
        rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
      rw [habs]
      ring
    simpa only [sub_self, zero_add, add_zero, abs_zero] using hDbase.congr' heq
  have hfactor := (scaling_pred_div_tendsto_one μ hμ a ha).add_const 1
  have hprod := hfactor.mul hD
  have hprod0 : Tendsto (fun n => (a (n - 1) / a n + 1) *
      ((n : ℝ) * cutoffTailGap μ (a (n - 1)) (a n))) atTop (𝓝 0) := by
    simpa only [one_add_one_eq_two, mul_zero] using hprod
  have hshellAbs : Tendsto (fun n : ℕ =>
      |(n : ℝ) * (truncatedIncrementMean μ (a n) -
        truncatedIncrementMean μ (a (n - 1))) / a n|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) _ hprod0
    filter_upwards [haTop.eventually_ge_atTop 1, hprevTop.eventually_ge_atTop 1]
      with n han hprevn
    have hb := abs_truncatedIncrementMean_sub_le μ hfin hprevn han
    rw [abs_sub_comm] at hb
    calc
      |(n : ℝ) * (truncatedIncrementMean μ (a n) -
          truncatedIncrementMean μ (a (n - 1))) / a n| =
          ((n : ℝ) / a n) * |truncatedIncrementMean μ (a n) -
            truncatedIncrementMean μ (a (n - 1))| := by
        rw [abs_div, abs_mul, abs_of_nonneg (Nat.cast_nonneg n),
          abs_of_pos (lt_of_lt_of_le zero_lt_one han)]
        ring
      _ ≤ ((n : ℝ) / a n) * ((a (n - 1) + a n) *
          cutoffTailGap μ (a (n - 1)) (a n)) :=
        mul_le_mul_of_nonneg_left hb (div_nonneg (Nat.cast_nonneg n) (by linarith))
      _ = (a (n - 1) / a n + 1) *
          ((n : ℝ) * cutoffTailGap μ (a (n - 1)) (a n)) := by
        have ha0 : a n ≠ 0 := by linarith
        field_simp [ha0]
  have hshell : Tendsto (fun n : ℕ =>
      (n : ℝ) * (truncatedIncrementMean μ (a n) -
        truncatedIncrementMean μ (a (n - 1))) / a n) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    exact hshellAbs
  have hmean := (truncatedIncrementMean_tendsto μ hfin hprevTop).div_atTop haTop
  have hsum := hshell.add hmean
  have heq : (fun n : ℕ =>
      (n : ℝ) * (truncatedIncrementMean μ (a n) -
        truncatedIncrementMean μ (a (n - 1))) / a n +
      truncatedIncrementMean μ (a (n - 1)) / a n) =ᶠ[atTop]
      (fun n : ℕ => (centering μ a n - centering μ a (n - 1)) / a n) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ), haTop.eventually_gt_atTop 0] with n hn han
    have hn1 : 1 ≤ n := hn
    have ha0 : a n ≠ 0 := han.ne'
    unfold centering
    rw [Nat.cast_sub hn1]
    push_cast
    field_simp [ha0]
    ring
  simpa only [zero_add, add_zero] using hsum.congr' heq

end
end SubcriticalCauchy.Bienayme
