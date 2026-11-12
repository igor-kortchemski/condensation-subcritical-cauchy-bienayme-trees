module

public import SubcriticalCauchy.BienaymeSurvivalRatio
public import SubcriticalCauchy.BienaymeForestHeight
public import SubcriticalCauchy.LogarithmicThreshold
public import Mathlib.MeasureTheory.Measure.Real

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Logarithmic height concentration for independent forests

For positive subcritical mean `m`, the maximum of a linear number of independent
trees lies between `(1-ε) log n / log (1/m)` and `(1+ε) log n / log (1/m)` with
probability tending to one. These are actual product-law statements. The transfer
to the size-conditioned tree remains a separate mathematical obligation.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section

/-- The source's real logarithmic threshold. Values at zero and one are harmless
totalizations; every limit below uses only sufficiently large indices. -/
def logarithmicHeightThreshold (m c : ℝ) (n : ℕ) : ℝ :=
  c / Real.log (1 / m) * Real.log n

theorem logarithmicHeightThreshold_eq (m c : ℝ) (n : ℕ) :
    logarithmicHeightThreshold m c n = c * Real.log n / Real.log (1 / m) := by
  unfold logarithmicHeightThreshold
  ring

theorem log_inv_mean_pos {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) :
    0 < Real.log (1 / m) := Real.log_pos ((one_lt_div hm0).mpr hm1)

theorem logarithmic_exponent {m c : ℝ} (hm0 : 0 < m) (hm1 : m < 1) :
    1 + (c / Real.log (1 / m)) * Real.log m = 1 - c := by
  have hlog : Real.log m ≠ 0 := (Real.log_neg hm0 hm1).ne
  simp only [one_div, Real.log_inv]
  field_simp
  ring

/-- The auxiliary rate chosen at manuscript lines 479–481 exists. The limit
proofs below use the logarithmic rate directly, rather than this witness. -/
theorem exists_eta_log_exponent {m ε : ℝ} (hm0 : 0 < m) (hm1 : m < 1)
    (hε0 : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η < m ∧
      ε / 2 ≤ 1 - (1 - ε) * Real.log (m - η) / Real.log m := by
  have hlog : Real.log m ≠ 0 := (Real.log_neg hm0 hm1).ne
  let f (η : ℝ) := 1 - (1 - ε) * Real.log (m - η) / Real.log m
  have hc : ContinuousAt f 0 := by
    exact continuousAt_const.sub ((continuousAt_const.mul
      ((continuousAt_const.sub continuousAt_id).log (by simpa using hm0.ne'))).div_const _)
  have hf0 : f 0 = ε := by
    dsimp [f]
    rw [sub_zero, mul_div_cancel_right₀ _ hlog]
    ring
  have he : ∀ᶠ η in 𝓝 (0 : ℝ), ε / 2 < f η :=
    hc.eventually (lt_mem_nhds (by rw [hf0]; linarith))
  have hall : ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 < η ∧ η < m ∧ ε / 2 < f η := by
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hm0).filter_mono
      nhdsWithin_le_nhds, he.filter_mono nhdsWithin_le_nhds] with η hpos hlt hexp
    exact ⟨hpos, hlt, hexp⟩
  obtain ⟨η, hpos, hlt, hexp⟩ := hall.exists
  exact ⟨η, hpos, hlt, hexp.le⟩

/-- The upper logarithmic threshold has a vanishing expected number of survivors. -/
theorem survival_log_upper_tendsto_zero (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm0 : 0 < offspringMean μ) (hm1 : offspringMean μ < 1)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      (survival μ ⌈logarithmicHeightThreshold (offspringMean μ).toReal (1 + ε) n⌉₊).toReal)
      atTop (𝓝 0) := by
  have hfin := ne_top_of_lt (hm1.trans ENNReal.one_lt_top)
  have hmR0 : 0 < (offspringMean μ).toReal := ENNReal.toReal_pos hm0.ne' hfin
  have hmR1 : (offspringMean μ).toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hfin ENNReal.one_ne_top).mpr hm1
  apply product_ceil_log_tendsto_zero (survival_toReal_pos μ hm0)
    (div_pos (by linarith) (log_inv_mean_pos hmR0 hmR1)) _
    (survival_log_div_nat_tendsto μ hm0 hm1)
  rw [logarithmic_exponent hmR0 hmR1]
  linarith

/-- The lower logarithmic threshold has a diverging expected number of survivors. -/
theorem survival_log_lower_tendsto_atTop (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm0 : 0 < offspringMean μ) (hm1 : offspringMean μ < 1)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      (survival μ ⌈logarithmicHeightThreshold (offspringMean μ).toReal (1 - ε) n⌉₊).toReal)
      atTop atTop := by
  have hfin := ne_top_of_lt (hm1.trans ENNReal.one_lt_top)
  have hmR0 : 0 < (offspringMean μ).toReal := ENNReal.toReal_pos hm0.ne' hfin
  have hmR1 : (offspringMean μ).toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hfin ENNReal.one_ne_top).mpr hm1
  apply product_ceil_log_tendsto_atTop (survival_toReal_pos μ hm0)
    (div_pos (sub_pos.mpr hε1) (log_inv_mean_pos hmR0 hmR1)) _
    (survival_log_div_nat_tendsto μ hm0 hm1)
  rw [logarithmic_exponent hmR0 hmR1]
  linarith

theorem forest_log_upper_tendsto_one (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm0 : 0 < offspringMean μ) (hm1 : offspringMean μ < 1)
    {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (forestLaw μ ⌊δ * n⌋₊
      (forestBelowReal ⌊δ * n⌋₊
        (logarithmicHeightThreshold (offspringMean μ).toReal (1 + ε) n))).toReal)
      atTop (𝓝 1) :=
  forestBelowReal_floor_tendsto_one μ _ hδ (survival_log_upper_tendsto_zero μ hm0 hm1 hε)

theorem forest_log_lower_tendsto_zero (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm0 : 0 < offspringMean μ) (hm1 : offspringMean μ < 1)
    {δ ε : ℝ} (hδ : 0 < δ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun n : ℕ => (forestLaw μ ⌊δ * n⌋₊
      (forestBelowReal ⌊δ * n⌋₊
        (logarithmicHeightThreshold (offspringMean μ).toReal (1 - ε) n))).toReal)
      atTop (𝓝 0) :=
  forestBelowReal_floor_tendsto_zero μ _ hδ
    (survival_log_lower_tendsto_atTop μ hm0 hm1 hε0 hε1)

/-- The largest component height is in `[lower,upper)`: every component lies below
`upper` and at least one reaches `lower`. In particular, the empty forest fails it. -/
def forestHeightBand (k : ℕ) (lower upper : ℝ) : Set (Fin k → BGW.LocallyFinite.Tree) :=
  forestBelowReal k upper ∩ (forestBelowReal k lower)ᶜ

theorem measurableSet_forestHeightBand (k : ℕ) (lower upper : ℝ) :
    MeasurableSet (forestHeightBand k lower upper) :=
  (measurableSet_forestBelow k ⌈upper⌉₊).inter (measurableSet_forestBelow k ⌈lower⌉₊).compl

theorem finite_forestHeightBand_iff (k : ℕ) (lower upper : ℝ)
    (F : Fin k → BGW.PlaneTree) :
    (fun i => (F i).toLocallyFinite) ∈ forestHeightBand k lower upper ↔
      (∀ i, (height (F i) : ℝ) < upper) ∧ ∃ i, lower ≤ (height (F i) : ℝ) := by
  simp only [forestHeightBand, Set.mem_inter_iff, Set.mem_compl_iff,
    finite_forestBelowReal_iff, not_forall, not_lt]

/-- First-order logarithmic concentration of the maximum height of a linear
number of actual independent Bienaymé trees. -/
theorem forest_log_band_tendsto_one (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm0 : 0 < offspringMean μ) (hm1 : offspringMean μ < 1)
    {δ ε : ℝ} (hδ : 0 < δ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun n : ℕ => (forestLaw μ ⌊δ * n⌋₊
      (forestHeightBand ⌊δ * n⌋₊
        (logarithmicHeightThreshold (offspringMean μ).toReal (1 - ε) n)
        (logarithmicHeightThreshold (offspringMean μ).toReal (1 + ε) n))).toReal)
      atTop (𝓝 1) := by
  let lo (n : ℕ) := forestBelowReal ⌊δ * n⌋₊
    (logarithmicHeightThreshold (offspringMean μ).toReal (1 - ε) n)
  let hi (n : ℕ) := forestBelowReal ⌊δ * n⌋₊
    (logarithmicHeightThreshold (offspringMean μ).toReal (1 + ε) n)
  let ν (n : ℕ) := forestLaw μ ⌊δ * n⌋₊
  have hmeas_hi (n : ℕ) : MeasurableSet (hi n) := measurableSet_forestBelow _ _
  have hmeas_lo (n : ℕ) : MeasurableSet (lo n) := measurableSet_forestBelow _ _
  have hhi := forest_log_upper_tendsto_one μ hm0 hm1 hδ.le hε0
  have hlo := forest_log_lower_tendsto_zero μ hm0 hm1 hδ hε0 hε1
  have hhic : Tendsto (fun n => (ν n (hi n)ᶜ).toReal) atTop (𝓝 0) := by
    have heq (n : ℕ) : (ν n (hi n)ᶜ).toReal = 1 - (ν n (hi n)).toReal := by
      rw [measure_compl (hmeas_hi n) (measure_ne_top _ _),
        measure_univ, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
        ENNReal.toReal_one]
    simp_rw [heq]
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hhi
  have hbad : Tendsto (fun n => (ν n ((hi n)ᶜ ∪ lo n)).toReal) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) _ (by simpa using hhic.add hlo)
    intro n
    exact measureReal_union_le (μ := ν n) _ _
  have heq (n : ℕ) : (ν n (hi n ∩ (lo n)ᶜ)).toReal =
      1 - (ν n ((hi n)ᶜ ∪ lo n)).toReal := by
    have hset : hi n ∩ (lo n)ᶜ = ((hi n)ᶜ ∪ lo n)ᶜ := by simp
    rw [hset, measure_compl
      ((hmeas_hi n).compl.union (hmeas_lo n))
      (measure_ne_top _ _), measure_univ,
      ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
  change Tendsto (fun n => (ν n (hi n ∩ (lo n)ᶜ)).toReal) atTop (𝓝 1)
  simp_rw [heq]
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hbad

end
end SubcriticalCauchy.Bienayme
