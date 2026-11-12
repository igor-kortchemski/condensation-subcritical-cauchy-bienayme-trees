module

public import SubcriticalCauchy.EquivalentTails
public import SubcriticalCauchy.SlowVariationPrimitive

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# The actual first-moment tail of the offspring law

The local offspring-mass asymptotic transfers directly to the first-moment
tail. This avoids an intermediate regular-variation theorem for the ordinary
offspring tail. Nonnegativity makes the first-moment tail antitone even when
its individual terms are not monotone.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

/-- The actual first moment contributed by offspring values at least `n`. -/
noncomputable def firstMomentTail (μ : Measure ℕ) (n : ℕ) : ℝ :=
  tailMass (fun k : ℕ => (μ {k}).toReal * (k : ℝ)) n

theorem firstMomentTail_nonneg (μ : Measure ℕ) (n : ℕ) :
    0 ≤ firstMomentTail μ n :=
  tailMass_nonneg (fun k => mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg k)) n

theorem firstMomentTail_antitone (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) : Antitone (firstMomentTail μ) :=
  tailMass_antitone_of_nonneg (summable_offspringMean μ hm)
    (fun k => mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg k))

/-- The actual first-moment tail is asymptotic to the manuscript's integrated
tail. Positivity, the local mass asymptotic, and finite mean suffice here;
slow variation and measurability are not used in this series comparison. -/
theorem firstMomentTail_div_ellStar_tendsto_one
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ ≠ ∞)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => firstMomentTail μ n / ellStar L n) atTop (𝓝 1) := by
  have hsum := summable_localModel_over_nat μ hm hpos hlocal
  have hratio : Tendsto
      (fun n : ℕ => ((μ {n}).toReal * (n : ℝ)) / (L n / (n : ℝ)))
      atTop (𝓝 1) := by
    apply hlocal.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hLn : L (n : ℝ) ≠ 0 := (hpos _ hnR).ne'
    field_simp [hnR.ne', hLn]
  apply tailMass_div_tendsto_one hsum (summable_offspringMean μ hm)
    (localModel_over_nat_nonneg hpos) _ hratio
  intro n hn
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn)
  exact div_pos (hpos _ hnR) hnR

/-- The local mass model forces arbitrarily large positive offspring values,
so every first-moment tail is strictly positive, including the zero-index tail.
This is obtained from the proved tail equivalence and antitonicity. -/
theorem firstMomentTail_pos_of_local
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ ≠ ∞)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1)) (n : ℕ) :
    0 < firstMomentTail μ n := by
  have hsum := summable_localModel_over_nat μ hm hpos hlocal
  have hratio := firstMomentTail_div_ellStar_tendsto_one μ hm hpos hlocal
  have hlarge : ∀ᶠ k : ℕ in atTop, 0 < firstMomentTail μ k := by
    filter_upwards [hratio.eventually_const_lt zero_lt_one] with k hk
    exact (div_pos_iff_of_pos_right (ellStar_pos_all hpos hsum k)).mp hk
  obtain ⟨N, hN⟩ := eventually_atTop.mp hlarge
  exact (hN (max N n) (le_max_left _ _)).trans_le
    (firstMomentTail_antitone μ hm (le_max_right _ _))

/-- Slow variation transfers to the actual first-moment tail along arbitrary
proportional index maps and arbitrary filters. Both indices tend to infinity;
no monotonicity of the index maps is required. -/
theorem firstMomentTail_ratio_of_index_ratio
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ ≠ ∞)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hfixed : ∀ a : ℝ, 0 < a →
      Tendsto (fun x : ℝ => L (a * x) / L x) atTop (𝓝 1))
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1))
    {ι : Type*} {l : Filter ι} {N M : ι → ℕ} {c : ℝ} (hc : 0 < c)
    (hN : Tendsto N l atTop) (hM : Tendsto M l atTop)
    (hMN : Tendsto (fun i : ι => (M i : ℝ) / (N i : ℝ)) l (𝓝 c)) :
    Tendsto (fun i : ι => firstMomentTail μ (M i) / firstMomentTail μ (N i))
      l (𝓝 1) := by
  have hsum := summable_localModel_over_nat μ hm hpos hlocal
  have hratio := firstMomentTail_div_ellStar_tendsto_one μ hm hpos hlocal
  have hleft := hratio.comp hM
  have hmiddle := ellStar_ratio_of_index_ratio hpos hL hfixed hsum hc hN hM hMN
  have hright : Tendsto
      (fun i : ι => ellStar L (N i) / firstMomentTail μ (N i)) l (𝓝 1) := by
    have h := (hratio.comp hN).inv₀ (show (1 : ℝ) ≠ 0 from one_ne_zero)
    simpa only [Function.comp_def, Pi.inv_apply, inv_div, inv_one] using h
  have hprod : Tendsto (fun i : ι =>
      (firstMomentTail μ (M i) / ellStar L (M i)) *
        (ellStar L (M i) / ellStar L (N i)) *
        (ellStar L (N i) / firstMomentTail μ (N i))) l (𝓝 1) := by
    simpa only [Function.comp_def, one_mul] using (hleft.mul hmiddle).mul hright
  apply hprod.congr'
  filter_upwards [] with i
  have hEM := (ellStar_pos_all hpos hsum (M i)).ne'
  have hEN := (ellStar_pos_all hpos hsum (N i)).ne'
  have hAN := (firstMomentTail_pos_of_local μ hm hpos hlocal (N i)).ne'
  field_simp [hEM, hEN, hAN]

theorem firstMomentTail_floor_mul_div_tendsto_one
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ ≠ ∞)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hfixed : ∀ a : ℝ, 0 < a →
      Tendsto (fun x : ℝ => L (a * x) / L x) atTop (𝓝 1))
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1)) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => firstMomentTail μ ⌊c * n⌋₊ / firstMomentTail μ n)
      atTop (𝓝 1) := by
  apply firstMomentTail_ratio_of_index_ratio μ hm hpos hL hfixed hlocal hc tendsto_id
  · exact tendsto_nat_floor_atTop.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop hc)
  · exact (tendsto_nat_floor_mul_div_atTop hc.le).comp tendsto_natCast_atTop_atTop

end SubcriticalCauchy.Bienayme
