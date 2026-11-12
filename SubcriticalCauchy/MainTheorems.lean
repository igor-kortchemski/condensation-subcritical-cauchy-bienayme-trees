module

public import SubcriticalCauchy.MeasurableHypothesis
public import SubcriticalCauchy.FiniteTreeEvent
public import SubcriticalCauchy.DegreeStatistics
public import SubcriticalCauchy.AttachedForestHeight
public import SubcriticalCauchy.BienaymeHeight
public import SubcriticalCauchy.MainProofs.M1
public import SubcriticalCauchy.MainProofs.M2
public import SubcriticalCauchy.MainProofs.M3
public import SubcriticalCauchy.MainProofs.M4
public import SubcriticalCauchy.MainProofs.M5

/-!
# Theorem 1.1 — frozen statements

Approved by the author on 10 November 2026 under the measurable slow-variation
convention, and frozen: this file may change only inside its five registered
`sorry` holes, filled with proof text only. Proofs go in the helper modules
`SubcriticalCauchy.MainProofs.M1` … `M5`, already imported here.

`conditioned μ n` is the actual Bienaymé law conditioned to have `n` vertices
(the zero measure at a null size; under the hypothesis every large `n` is
admissible, `eventually_size_admissible`).
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section
open BGW BGW.LocallyFinite

/-- Theorem 1.1(i), first part: `Δ(T_n) / (n(1-m)) → 1` in probability. -/
theorem main_maxDegree_condensation (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => conditioned μ n (finiteTreeEvent fun t =>
        ε < |(maxDegree t : ℝ) / ((n : ℝ) * (1 - (offspringMean μ).toReal)) - 1|))
      atTop (𝓝 0) := by
  exact (ENNReal.tendsto_toReal_zero_iff (fun n => by
      unfold conditioned
      finiteness)).mp
    (main_maxDegree_condensation_real μ hμ ε hε)

/-- Theorem 1.1(i), second part: `Δ²(T_n) / n → 0` in probability. The second
maximum counts multiplicity (`secondMaxDegree`). -/
theorem main_secondMaxDegree_negligible (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => conditioned μ n (finiteTreeEvent fun t =>
        ε < (secondMaxDegree t : ℝ) / n))
      atTop (𝓝 0) := by
  exact (ENNReal.tendsto_toReal_zero_iff (fun n => by
      unfold conditioned
      finiteness)).mp
    (main_secondMaxDegree_negligible_real μ hμ ε hε)

/-- Theorem 1.1(ii): the height of the first (lexicographic) maximal-degree
vertex converges in law to a geometric variable. -/
theorem main_maxDegreeDepth_geometric (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (j : ℕ) :
    Tendsto (fun n : ℕ => conditioned μ n (finiteTreeEvent fun t => maxDegreeDepth t = j))
      atTop (𝓝 (ENNReal.ofReal
        ((1 - (offspringMean μ).toReal) * (offspringMean μ).toReal ^ j))) := by
  exact main_maxDegreeDepth_geometric_proof μ hμ j

/-- Theorem 1.1(iii)(a): `H(T_n) / log n → 1 / log(1/m)` in probability. -/
theorem main_height_log (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => conditioned μ n (finiteTreeEvent fun t =>
        ε < |(height t : ℝ) / Real.log n - 1 / Real.log (1 / (offspringMean μ).toReal)|))
      atTop (𝓝 0) := by
  exact main_height_log_proof μ hμ ε hε

/-- Theorem 1.1(iii)(b): the centred heights `H(T_n) - log n / log(1/m)`,
`n ≥ 1`, form a tight family iff `∑ (n log n) μ_n < ∞`. -/
theorem main_height_tight_iff (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) :
    (∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ n : ℕ, 1 ≤ n →
        conditioned μ n (finiteTreeEvent fun t =>
          K < |(height t : ℝ) - Real.log n / Real.log (1 / (offspringMean μ).toReal)|)
          ≤ ENNReal.ofReal ε) ↔
      Summable (fun k : ℕ => (k : ℝ) * Real.log k * (μ {k}).toReal) := by
  exact main_height_tight_iff_proof μ hμ

end
end SubcriticalCauchy.Bienayme
