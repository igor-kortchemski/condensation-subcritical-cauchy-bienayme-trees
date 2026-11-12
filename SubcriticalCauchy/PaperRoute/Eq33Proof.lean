module

public import SubcriticalCauchy.PaperRoute.Defs
public import SubcriticalCauchy.PaperRoute.BergerTight
public import SubcriticalCauchy.RefinedCentering
public import SubcriticalCauchy.IncrementTailAsymptotics
public import SubcriticalCauchy.LocalMassWindows

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Helpers for `SubcriticalCauchy.PaperRoute.Statements` (Eq33Proof)

The three deterministic/local parts of (3.3), and its tightness part conditional
on the increment-sum tightness input proved in `BergerTight`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section

/-- The scaling ratio in (3.3). -/
theorem paper_eq33_scale (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ < 1) (L : ℝ → ℝ) (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hsv : IsSlowlyVaryingAtTop L) (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2)) atTop (𝓝 1))
    (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => a n / ((n : ℝ) * ellStarReal L (a n))) atTop (𝓝 0) := by
  have hliteral : IsSubcriticalCauchyOffspring μ := ⟨hm, L, hpos, hsv, hlocal⟩
  have hat : Tendsto a atTop atTop := scaling_tendsto_atTop μ hliteral ha
  have hsum := summable_localModel_over_nat μ (ne_top_of_lt (hm.trans ENNReal.one_lt_top)) hpos hlocal
  have hscale := scaling_div_mul_tendsto_one μ hm hpos hL hsv hlocal ha
  have hsmall := (localModel_div_ellStarReal_tendsto_zero hpos hL hsv hsum).comp hat
  have hprod := hscale.mul hsmall
  have heq : (fun n : ℕ => a n / ((n : ℝ) * L (a n)) *
      ((fun x : ℝ => L x / ellStarReal L x) ∘ a) n) =ᶠ[atTop]
      (fun n : ℕ => a n / ((n : ℝ) * ellStarReal L (a n))) := by
    filter_upwards [hat.eventually_gt_atTop 0, eventually_gt_atTop (0 : ℕ)] with n han hn
    have hLn := (hpos _ han).ne'
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    dsimp only [Function.comp_def]
    field_simp
  simpa only [one_mul] using hprod.congr' heq

/-- The centering ratio in (3.3). -/
theorem paper_eq33_centering (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ < 1) (L : ℝ → ℝ) (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hsv : IsSlowlyVaryingAtTop L) (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2)) atTop (𝓝 1))
    (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => (centering μ a n + (1 - (offspringMean μ).toReal) * n) /
      ((n : ℝ) * ellStarReal L (a n))) atTop (𝓝 (-1)) := by
  have hliteral : IsSubcriticalCauchyOffspring μ := ⟨hm, L, hpos, hsv, hlocal⟩
  have hat : Tendsto a atTop atTop := scaling_tendsto_atTop μ hliteral ha
  have hfin : offspringMean μ ≠ ∞ := ne_top_of_lt (hm.trans ENNReal.one_lt_top)
  have h := (centering_shift_ratio_tendsto_one μ hfin hpos hL hsv hlocal hat).neg
  simpa only [neg_mul, div_neg, neg_div, neg_neg, mul_comm (1 - (offspringMean μ).toReal)] using h

/-- The centered law of a unit interval, as an offspring-mass window. -/
theorem centeredIncrementLaw_ioc (μ : Measure ℕ) (x : ℝ) :
    centeredIncrementLaw μ (Set.Ioc x (x + 1)) =
      centeredIncrementUnitWindow μ (1 - (offspringMean μ).toReal) x := by
  rw [centeredIncrementLaw, incrementLaw,
    Measure.map_map (by fun_prop) (measurable_of_countable _),
    Measure.map_apply (by fun_prop) measurableSet_Ioc]
  unfold centeredIncrementUnitWindow
  congr 1
  ext k
  simp only [Set.mem_preimage, Set.mem_Ioc, Set.mem_ofPred_eq, Function.comp_apply]
  push_cast
  rfl

/-- The uniform additive-window clause in (3.3). -/
theorem paper_eq33_window (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ < 1) (L : ℝ → ℝ) (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hsv : IsSlowlyVaryingAtTop L) (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2)) atTop (𝓝 1))
    (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal) atTop (𝓝 1)) :
    ∀ ε > 0, ∀ A > 0, ∀ τ > 0, ∀ᶠ n : ℕ in atTop, ∀ x y : ℝ, ε * n ≤ x →
      |y| ≤ A * ((n : ℝ) * ellStarReal L (a n)) →
      |1 - (centeredIncrementLaw μ (Set.Ioc (x - y) (x - y + 1))).toReal /
          (centeredIncrementLaw μ (Set.Ioc x (x + 1))).toReal| ≤ τ := by
  have hμ : IsMeasurableSubcriticalCauchyOffspring μ := ⟨hm, L, hpos, hsv, hL, hlocal⟩
  have hell : Tendsto (fun n : ℕ => ellStarReal L (a n)) atTop (𝓝 0) := by
    have hliteral : IsSubcriticalCauchyOffspring μ := ⟨hm, L, hpos, hsv, hlocal⟩
    exact (ellStarReal_tendsto_zero L).comp (scaling_tendsto_atTop μ hliteral ha)
  intro ε hε A hA τ hτ
  have hη : Tendsto
      (fun n : ℕ => (A * ((n : ℝ) * ellStarReal L (a n))) / (n : ℝ)) atTop (𝓝 0) := by
    have h := hell.const_mul A
    have heq : (fun n : ℕ => A * ellStarReal L (a n)) =ᶠ[atTop]
        (fun n : ℕ => (A * ((n : ℝ) * ellStarReal L (a n))) / (n : ℝ)) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      field_simp
    simpa only [mul_zero] using h.congr' heq
  have hwindow := paper_centeredUnitWindow_uniform_additive_window μ hμ
    (1 - (offspringMean μ).toReal) hε hη τ hτ
  filter_upwards [hwindow] with n hn
  intro x y hx hy
  rw [centeredIncrementLaw_ioc, centeredIncrementLaw_ioc]
  have hy' : |-y| ≤ |A * ((n : ℝ) * ellStarReal L (a n))| := by
    rw [abs_neg, abs_of_nonneg (mul_nonneg hA.le
      (mul_nonneg (Nat.cast_nonneg _) (ellStarReal_pos hpos
        (summable_localModel_over_nat μ (ne_top_of_lt (hm.trans ENNReal.one_lt_top)) hpos hlocal) _).le))]
    exact hy
  have h := hn x (-y) hx hy'
  rw [show x + -y = x - y by ring] at h
  rw [abs_sub_comm]
  exact h.le

/-- Tightness of the centered sums, from the increment-sum tightness input. -/
theorem paper_eq33_tight (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ < 1) (L : ℝ → ℝ) (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hsv : IsSlowlyVaryingAtTop L) (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2)) atTop (𝓝 1))
    (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal) atTop (𝓝 1))
    (htight : ∀ τ : ℝ, 0 < τ → ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ j : ℕ, j ≤ n →
      ((Measure.pi fun _ : Fin j => incrementLaw μ)
          {x | K * a n < |(∑ i, (x i : ℝ)) - j * truncatedIncrementMean μ (a n)|}).toReal ≤ τ) :
    ∀ τ > 0, ∃ K : ℝ, ∀ᶠ n : ℕ in atTop,
      ((Measure.pi fun _ : Fin n => centeredIncrementLaw μ)
        {y | K * ((n : ℝ) * ellStarReal L (a n)) < |∑ i, y i|}).toReal ≤ τ := by
  let incrementLaw_isProbability : IsProbabilityMeasure (incrementLaw μ) := by
    unfold incrementLaw
    infer_instance
  have hliteral : IsSubcriticalCauchyOffspring μ := ⟨hm, L, hpos, hsv, hlocal⟩
  have hat : Tendsto a atTop atTop := scaling_tendsto_atTop μ hliteral ha
  have hsum := summable_localModel_over_nat μ (ne_top_of_lt (hm.trans ENNReal.one_lt_top)) hpos hlocal
  have hscale := paper_eq33_scale μ hm L hpos hsv hL hlocal a ha
  have hcenter := paper_eq33_centering μ hm L hpos hsv hL hlocal a ha
  have ha_le : ∀ᶠ n : ℕ in atTop, a n ≤ (n : ℝ) * ellStarReal L (a n) := by
    have hlt := hscale.eventually (Iio_mem_nhds zero_lt_one)
    filter_upwards [hlt, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
    have hb : 0 < (n : ℝ) * ellStarReal L (a n) :=
      mul_pos (Nat.cast_pos.mpr hnpos) (ellStarReal_pos hpos hsum _)
    exact ((div_lt_one hb).mp hn).le
  have hdrift : ∀ᶠ n : ℕ in atTop,
      |centering μ a n + (1 - (offspringMean μ).toReal) * n| ≤
        2 * ((n : ℝ) * ellStarReal L (a n)) := by
    have habs : Tendsto (fun n : ℕ => |(centering μ a n +
        (1 - (offspringMean μ).toReal) * n) / ((n : ℝ) * ellStarReal L (a n))|)
        atTop (𝓝 1) := by simpa only [abs_neg, abs_one] using hcenter.abs
    have hlt := habs.eventually (Iio_mem_nhds one_lt_two)
    filter_upwards [hlt, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
    have hb : 0 < (n : ℝ) * ellStarReal L (a n) :=
      mul_pos (Nat.cast_pos.mpr hnpos) (ellStarReal_pos hpos hsum _)
    rw [abs_div, abs_of_pos hb] at hn
    exact ((div_lt_iff₀ hb).mp hn).le
  intro τ hτ
  obtain ⟨K, hK, N, hN⟩ := htight τ hτ
  refine ⟨K + 2, ?_⟩
  filter_upwards [eventually_ge_atTop N, ha_le, hdrift] with n hnN han hdriftn
  have hmap : (Measure.pi fun _ : Fin n => incrementLaw μ).map
      (fun x i => (x i : ℝ) + (1 - (offspringMean μ).toReal)) =
      (Measure.pi fun _ : Fin n => centeredIncrementLaw μ) := by
    simpa only [centeredIncrementLaw] using
      (Measure.pi_map_pi (μ := fun _ : Fin n => incrementLaw μ)
        (f := fun (_ : Fin n) (k : ℤ) => (k : ℝ) + (1 - (offspringMean μ).toReal))
        (fun (_ : Fin n) => show AEMeasurable
          (fun k : ℤ => (k : ℝ) + (1 - (offspringMean μ).toReal)) (incrementLaw μ) from
            Measurable.aemeasurable (by fun_prop)))
  rw [← hmap, Measure.map_apply (by fun_prop) (measurableSet_lt measurable_const (by fun_prop))]
  apply le_trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)) (hN n hnN n le_rfl)
  intro x hx
  change K * a n < |(∑ i, (x i : ℝ)) - centering μ a n|
  by_contra hnot
  have hdev : |(∑ i, (x i : ℝ)) - centering μ a n| ≤ K * a n := le_of_not_gt hnot
  have hKnonneg : 0 ≤ K := hK.le
  have hKa : K * a n ≤ K * ((n : ℝ) * ellStarReal L (a n)) :=
    mul_le_mul_of_nonneg_left han hKnonneg
  have hsum_eq : (∑ i, ((x i : ℝ) + (1 - (offspringMean μ).toReal))) =
      ((∑ i, (x i : ℝ)) - centering μ a n) +
        (centering μ a n + (1 - (offspringMean μ).toReal) * n) := by
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hbound : |∑ i, ((x i : ℝ) + (1 - (offspringMean μ).toReal))| ≤
      (K + 2) * ((n : ℝ) * ellStarReal L (a n)) := by
    rw [hsum_eq]
    calc
      |((∑ i, (x i : ℝ)) - centering μ a n) +
          (centering μ a n + (1 - (offspringMean μ).toReal) * n)| ≤
        |(∑ i, (x i : ℝ)) - centering μ a n| +
          |centering μ a n + (1 - (offspringMean μ).toReal) * n| := abs_add_le _ _
      _ ≤ K * ((n : ℝ) * ellStarReal L (a n)) +
          2 * ((n : ℝ) * ellStarReal L (a n)) := add_le_add (hdev.trans hKa) hdriftn
      _ = (K + 2) * ((n : ℝ) * ellStarReal L (a n)) := by ring
  exact (not_lt_of_ge hbound) hx

/-- Condition (3.3), conditional on the separate increment-sum tightness input. -/
theorem paper_eq33_of_tight (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ < 1) (L : ℝ → ℝ) (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hsv : IsSlowlyVaryingAtTop L) (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2)) atTop (𝓝 1))
    (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal) atTop (𝓝 1))
    (htight : ∀ τ : ℝ, 0 < τ → ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ j : ℕ, j ≤ n →
      ((Measure.pi fun _ : Fin j => incrementLaw μ)
          {x | K * a n < |(∑ i, (x i : ℝ)) - j * truncatedIncrementMean μ (a n)|}).toReal ≤ τ) :
    (∀ τ > 0, ∃ K : ℝ, ∀ᶠ n : ℕ in atTop,
        ((Measure.pi fun _ : Fin n => centeredIncrementLaw μ)
          {y | K * ((n : ℝ) * ellStarReal L (a n)) < |∑ i, y i|}).toReal ≤ τ) ∧
      Tendsto (fun n : ℕ => a n / ((n : ℝ) * ellStarReal L (a n))) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => (centering μ a n + (1 - (offspringMean μ).toReal) * n) /
          ((n : ℝ) * ellStarReal L (a n))) atTop (𝓝 (-1)) ∧
      ∀ ε > 0, ∀ A > 0, ∀ τ > 0, ∀ᶠ n : ℕ in atTop, ∀ x y : ℝ, ε * n ≤ x →
        |y| ≤ A * ((n : ℝ) * ellStarReal L (a n)) →
        |1 - (centeredIncrementLaw μ (Set.Ioc (x - y) (x - y + 1))).toReal /
            (centeredIncrementLaw μ (Set.Ioc x (x + 1))).toReal| ≤ τ := by
  exact ⟨paper_eq33_tight μ hm L hpos hsv hL hlocal a ha htight,
    paper_eq33_scale μ hm L hpos hsv hL hlocal a ha,
    paper_eq33_centering μ hm L hpos hsv hL hlocal a ha,
    paper_eq33_window μ hm L hpos hsv hL hlocal a ha⟩

end

end SubcriticalCauchy.Bienayme
