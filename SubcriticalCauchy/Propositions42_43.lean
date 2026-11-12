module

public import SubcriticalCauchy.FiniteTreeEvent
public import SubcriticalCauchy.MeasurableHypothesis
public import SubcriticalCauchy.BienaymeForestHeight
public import SubcriticalCauchy.BienaymeHeight
public import SubcriticalCauchy.AttachedSlots
public import Mathlib.MeasureTheory.Measure.TotalVariation.Defs
public import SubcriticalCauchy.PropProofs.P42
public import SubcriticalCauchy.PropProofs.P43i
public import SubcriticalCauchy.PropProofs.P43ii

/-!
# Propositions 4.2 and 4.3 — frozen statements

Approved by the author on 10 November 2026 under the measurable slow-variation
convention, with the `leaf` padding of `SubcriticalCauchy.AttachedSlots`, and
frozen: this file may change only inside its three registered `sorry` holes,
filled with proof text only. Proofs go in the helper modules
`SubcriticalCauchy.PropProofs.P42`, `P43i` and `P43ii`, already imported here.

`forestLaw μ k` is the law of `k` independent unconditioned Bienaymé trees.
Mathlib's `tvDist` is twice the paper's distance. For real thresholds,
`Q_h = P(H ≥ h) = survival μ ⌈h⌉₊`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section
open BGW BGW.LocallyFinite

/-- Proposition 4.2: for every `δ ∈ [0, 1 - m)`, the first `⌊δ n⌋` subtrees of
the maximal vertex are asymptotically independent Bienaymé trees. -/
theorem paper_attached_forest_tvDist (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1 - (offspringMean μ).toReal) :
    Tendsto (fun n : ℕ =>
        tvDist (attachedSlotsLaw μ n ⌊δ * n⌋₊) (forestLaw μ ⌊δ * n⌋₊))
      atTop (𝓝 0) := by
  exact attached_forest_tvDist μ hμ δ hδ0 hδ1

/-- Proposition 4.3(i): if `h_n → ∞` and `n Q_{h_n} → ∞`, then
`P(H(T_n) ≥ h_n) → 1`. -/
theorem paper_height_lower (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (h : ℕ → ℝ)
    (hpos : ∀ n, 0 < h n) (hh : Tendsto h atTop atTop)
    (hQ : Tendsto (fun n : ℕ => (n : ℝ) * (survival μ ⌈h n⌉₊).toReal) atTop atTop) :
    Tendsto (fun n : ℕ => conditioned μ n (finiteTreeEvent fun t => h n ≤ (height t : ℝ)))
      atTop (𝓝 1) := by
  exact height_lower_of_attached_tvDist μ hμ h hpos hh hQ
    (fun δ hδ0 hδ1 => paper_attached_forest_tvDist μ hμ δ hδ0 hδ1)

/-- Proposition 4.3(ii): if `h_n → ∞` and `n Q_{h_n} → 0`, then
`P(H(T_n) < h_n) → 1`. -/
theorem paper_height_upper (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (h : ℕ → ℝ)
    (hpos : ∀ n, 0 < h n) (hh : Tendsto h atTop atTop)
    (hQ : Tendsto (fun n : ℕ => (n : ℝ) * (survival μ ⌈h n⌉₊).toReal) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => conditioned μ n (finiteTreeEvent fun t => (height t : ℝ) < h n))
      atTop (𝓝 1) := by
  exact height_upper μ hμ h hpos hh hQ

end
end SubcriticalCauchy.Bienayme
