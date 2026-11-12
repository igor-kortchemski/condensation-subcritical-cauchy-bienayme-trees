module

public import SubcriticalCauchy.OffspringHypothesis
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The author-clarified measurable slow-variation convention

On 1 November 2026 the author selected the standard measurable convention for
the main statements. The literal ratio-only hypothesis remains unchanged in
OffspringHypothesis. This predicate adds Lebesgue measurability on the positive
half-line, with no stable-domain, uniform-convergence, or moment conclusions.

An a.e. Borel representative must not silently replace `L`: its pointwise ratios
and integer values require their own justification.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

/-- The accepted main-statement version of `H_mu^loc`. The regularity is
Lebesgue measurability on the positive half-line; slow variation stays pointwise. -/
def IsMeasurableSubcriticalCauchyOffspring (μ : Measure ℕ) : Prop :=
  offspringMean μ < 1 ∧ ∃ L : ℝ → ℝ,
    (∀ x : ℝ, 0 < x → 0 < L x) ∧ IsSlowlyVaryingAtTop L ∧
      AEMeasurable L (volume.restrict (Set.Ioi 0)) ∧
        Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2)) atTop (𝓝 1)

theorem IsMeasurableSubcriticalCauchyOffspring.to_literal {μ : Measure ℕ}
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) : IsSubcriticalCauchyOffspring μ := by
  obtain ⟨hm, L, hpos, hsv, _, hratio⟩ := hμ
  exact ⟨hm, L, hpos, hsv, hratio⟩

end SubcriticalCauchy.Bienayme
