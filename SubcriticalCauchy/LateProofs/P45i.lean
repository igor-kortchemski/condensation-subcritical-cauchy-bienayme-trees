module

public import SubcriticalCauchy.FiniteTreeEvent
public import SubcriticalCauchy.HeightSecondOrder
public import SubcriticalCauchy.LateProofs.P45Tail

/-!
# Proof helpers for the frozen statement of Proposition 4.5(i) (`paper_height_second_order_log`)

Owned helper module for one registered hole of `SubcriticalCauchy.Proposition45`. It is
imported by the frozen statement file, which must not change except inside its
holes; add the proof and any further imports here. It must not import
`SubcriticalCauchy.Proposition45`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

/-- We specialize `survivalCorrection_asymp_of_tail` to the frozen `β = 1` tail. -/
theorem survivalCorrection_log_asymp_of_tail (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (c : ℝ) (hc : 0 < c)
    (htail : Tendsto (fun n : ℕ =>
      (μ {n}).toReal / (c / ((n : ℝ) ^ 2 * Real.log n ^ 2))) atTop (𝓝 1)) :
    Tendsto (fun x : ℝ => survivalCorrection μ x /
      (c / (1 * Real.log x⁻¹ ^ (1 : ℝ)))) (𝓝[>] 0) (𝓝 1) := by
  have htail' : Tendsto (fun n : ℕ => (μ {n}).toReal /
      (c / ((n : ℝ) ^ 2 * Real.log n ^ (1 + (1 : ℝ))))) atTop (𝓝 1) := by
    simpa only [show 1 + (1 : ℝ) = 2 by norm_num, Real.rpow_two] using htail
  have h := survivalCorrection_asymp_of_tail μ hμ hc zero_lt_one htail'
  simpa only [one_mul, Real.rpow_one] using h

end SubcriticalCauchy.Bienayme
