module

public import SubcriticalCauchy.FiniteTreeEvent
public import SubcriticalCauchy.MeasurableHypothesis
public import SubcriticalCauchy.BienaymeHeight
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import SubcriticalCauchy.LateProofs.P45i
public import SubcriticalCauchy.LateProofs.P45ii

/-!
# Proposition 4.5 — frozen statements

Approved by the author on 10 November 2026 (with the correction R10), and
frozen: this file may change only inside its two registered `sorry` holes,
filled with proof text only. Proofs go in the helper modules
`SubcriticalCauchy.LateProofs.P45i` and `P45ii`, already imported here; they
must not import this file.

Second-order height asymptotics when `L(n) ~ c / (log n)^{1+β}`. The tail
hypothesis is stated on `μ` itself, `μ_n ~ c / (n² (log n)^{1+β})`, which is
equivalent to `L(n) ~ c/(log n)^{1+β}` for the slowly varying `L` of the
hypothesis (all such `L` are equivalent along the integers).

Write `m = offspringMean μ` and `a = log(1/m)`.

**Correction R10.** For `β ∈ (0,1)` the paper's coefficient is
`c / ((1-β) β m a^{1+β})`; the correct one is `c / ((1-β) β m a²)`
(the factor `h^{1-β} ~ (log n / a)^{1-β}` contributes `a^{-(1-β)}`). Part (i),
`β = 1`, is as in the paper.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section
open BGW BGW.LocallyFinite

/-- Proposition 4.5(i): `β = 1`. -/
theorem paper_height_second_order_log (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (c : ℝ) (hc : 0 < c)
    (htail : Tendsto (fun n : ℕ =>
        (μ {n}).toReal / (c / ((n : ℝ) ^ 2 * Real.log n ^ 2))) atTop (𝓝 1))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => conditioned μ n (finiteTreeEvent fun t =>
        ε * Real.log (Real.log n) ≤
          |(height t : ℝ) - Real.log n / Real.log (1 / (offspringMean μ).toReal) +
            c / ((offspringMean μ).toReal * Real.log (1 / (offspringMean μ).toReal) ^ 2) *
              Real.log (Real.log n)|))
      atTop (𝓝 0) := by
  exact height_second_order_log_of_survivalCorrection μ hμ hc
    (survivalCorrection_log_asymp_of_tail μ hμ c hc htail) hε

/-- Proposition 4.5(ii), corrected (R10): `0 < β < 1`. -/
theorem paper_height_second_order_pow (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (c β : ℝ) (hc : 0 < c)
    (hβ0 : 0 < β) (hβ1 : β < 1)
    (htail : Tendsto (fun n : ℕ =>
        (μ {n}).toReal / (c / ((n : ℝ) ^ 2 * Real.log n ^ (1 + β)))) atTop (𝓝 1))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => conditioned μ n (finiteTreeEvent fun t =>
        ε * Real.log n ^ (1 - β) ≤
          |(height t : ℝ) - Real.log n / Real.log (1 / (offspringMean μ).toReal) +
            c / ((1 - β) * β * (offspringMean μ).toReal *
                Real.log (1 / (offspringMean μ).toReal) ^ 2) *
              Real.log n ^ (1 - β)|))
      atTop (𝓝 0) := by
  exact height_second_order_pow_of_survivalCorrection μ hμ hc hβ0 hβ1
    (survivalCorrection_asymp_of_tail μ hμ hc hβ0 htail) hε

end
end SubcriticalCauchy.Bienayme
