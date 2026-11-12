module

public import SubcriticalCauchy.CenteringTailSeries
public import SubcriticalCauchy.EquivalentTails
public import SubcriticalCauchy.SlowVariationRounding

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The refined centering asymptotic

The local mass asymptotic gives equivalence of two summable series. Comparing
their genuine tails proves the refined centering directly, with the strict
absolute cutoff and the floor-plus-two endpoint retained. This bypasses the
source's intermediate asymptotic for the increment tail probability.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

theorem weightedIncrementMass_local_ratio
    (μ : Measure ℕ) {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => weightedIncrementMass μ n / (L n / (n : ℝ)))
      atTop (𝓝 1) := by
  have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hfactor : Tendsto (fun n : ℕ => ((n : ℝ) - 1) / n) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hinv
    have heq : (fun n : ℕ => 1 - 1 / (n : ℝ)) =ᶠ[atTop]
        (fun n : ℕ => ((n : ℝ) - 1) / n) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      field_simp
    simpa only [sub_zero] using h.congr' heq
  have hprod := hlocal.mul hfactor
  have heq : (fun n : ℕ => ((μ {n}).toReal / (L n / (n : ℝ) ^ 2)) *
      (((n : ℝ) - 1) / n)) =ᶠ[atTop]
      (fun n : ℕ => weightedIncrementMass μ n / (L n / (n : ℝ))) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hLn := (hpos _ hnR).ne'
    dsimp only [weightedIncrementMass]
    field_simp [hnR.ne', hLn]
  simpa only [one_mul] using hprod.congr' heq

theorem tailIncrementMean_div_ellStarReal_tendsto_one
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ ≠ ∞)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hfixed : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1)) :
    Tendsto (fun x : ℝ => tailIncrementMean μ x / ellStarReal L x) atTop (𝓝 1) := by
  have hsum := summable_localModel_over_nat μ hm hpos hlocal
  have htail := tailMass_div_tendsto_one hsum (summable_weightedIncrementMass μ hm)
    (localModel_over_nat_nonneg hpos)
    (fun n hn => div_pos (hpos _ (Nat.cast_pos.mpr (by omega)))
      (Nat.cast_pos.mpr (by omega)))
    (weightedIncrementMass_local_ratio μ hpos hlocal)
  have hN : Tendsto (fun x : ℝ => Nat.floor x) atTop atTop := tendsto_nat_floor_atTop
  have hJ : Tendsto (fun x : ℝ => Nat.floor x + 2) atTop atTop :=
    tendsto_atTop_mono (fun x => Nat.le_add_right (Nat.floor x) 2) hN
  have hJN : Tendsto (fun x : ℝ => ((Nat.floor x + 2 : ℕ) : ℝ) / (Nat.floor x : ℝ))
      atTop (𝓝 1) := by
    have hzero : Tendsto (fun x : ℝ => (2 : ℝ) / (Nat.floor x : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hN)
    have h := (tendsto_const_nhds (x := (1 : ℝ))).add hzero
    have heq : (fun x : ℝ => 1 + 2 / (Nat.floor x : ℝ)) =ᶠ[atTop]
        (fun x : ℝ => ((Nat.floor x + 2 : ℕ) : ℝ) / (Nat.floor x : ℝ)) := by
      filter_upwards [hN.eventually_gt_atTop 0] with x hx
      have hnR : (Nat.floor x : ℝ) ≠ 0 := (Nat.cast_pos.mpr hx).ne'
      push_cast
      field_simp
    simpa only [add_zero] using h.congr' heq
  have hprimitive := ellStar_ratio_of_index_ratio hpos hL hfixed hsum zero_lt_one hN hJ hJN
  have hfirst : Tendsto (fun x : ℝ =>
      tailMass (weightedIncrementMass μ) (Nat.floor x + 2) / ellStar L (Nat.floor x + 2))
      atTop (𝓝 1) := by
    simpa only [Function.comp_def, ellStar] using htail.comp hJ
  have hprod := hfirst.mul hprimitive
  have heq : (fun x : ℝ =>
      (tailMass (weightedIncrementMass μ) (Nat.floor x + 2) / ellStar L (Nat.floor x + 2)) *
        (ellStar L (Nat.floor x + 2) / ellStar L (Nat.floor x))) =ᶠ[atTop]
      (fun x : ℝ => tailIncrementMean μ x / ellStarReal L x) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    rw [tailIncrementMean_eq_tailMass μ hm hx]
    have hJne := (ellStar_pos_all hpos hsum (Nat.floor x + 2)).ne'
    have hNne := (ellStar_pos_all hpos hsum (Nat.floor x)).ne'
    dsimp only [ellStarReal]
    field_simp [hJne, hNne]
  simpa only [one_mul] using hprod.congr' heq

/-- The refined asymptotic in Lemma 2.2(ii), for any diverging cutoff. -/
theorem centering_shift_ratio_tendsto_one
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ ≠ ∞)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hfixed : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1)) {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) :
    Tendsto (fun n : ℕ =>
      (centering μ a n + (n : ℝ) * (1 - (offspringMean μ).toReal)) /
        (-(n : ℝ) * ellStarReal L (a n))) atTop (𝓝 1) := by
  have hsum := summable_localModel_over_nat μ hm hpos hlocal
  have h := (tailIncrementMean_div_ellStarReal_tendsto_one μ hm hpos hL hfixed hlocal).comp ha
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  dsimp only [Function.comp_def]
  rw [centering_shift_eq_tail μ hm a n]
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have htail := (ellStarReal_pos hpos hsum (a n)).ne'
  field_simp

/-- A single local-asymptotic witness works for every source-normalized scale. -/
theorem paper_centering_asymptotics
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) :
    ∃ L : ℝ → ℝ, (∀ x : ℝ, 0 < x → 0 < L x) ∧ IsSlowlyVaryingAtTop L ∧
      AEMeasurable L (volume.restrict (Set.Ioi 0)) ∧
      Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2)) atTop (𝓝 1) ∧
      ∀ a : ℕ → ℝ,
        Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal) atTop (𝓝 1) →
        (Tendsto (fun n : ℕ =>
          (centering μ a n + (n : ℝ) * (1 - (offspringMean μ).toReal)) /
            (-(n : ℝ) * ellStarReal L (a n))) atTop (𝓝 1)) ∧
        Tendsto (fun n : ℕ => centering μ a n /
          (-(n : ℝ) * (1 - (offspringMean μ).toReal))) atTop (𝓝 1) := by
  obtain ⟨hm, L, hpos, hsv, hmeas, hlocal⟩ := hμ
  have hliteral : IsSubcriticalCauchyOffspring μ := ⟨hm, L, hpos, hsv, hlocal⟩
  refine ⟨L, hpos, hsv, hmeas, hlocal, ?_⟩
  intro a ha
  have hfin := ne_top_of_lt (hm.trans ENNReal.one_lt_top)
  have hat := scaling_tendsto_atTop μ hliteral ha
  exact ⟨centering_shift_ratio_tendsto_one μ hfin hpos hmeas hsv hlocal hat,
    centering_ratio_tendsto_one μ hm hat⟩

end SubcriticalCauchy.Bienayme
