module

public import SubcriticalCauchy.ClassificationDefs
public import SubcriticalCauchy.ClassificationProof

/-!
# The five-case classification (U2.5), corrected — frozen statement

Source: `subcritical_cauchy_final_arxiv.tex`, Section 2.2, lines 215–223.
Approved by the author on 11 November 2026 ("Approve"), and frozen: this file
may change only inside its registered `sorry` hole, filled with proof text only.
Definitions are in `SubcriticalCauchy.ClassificationDefs` (frozen whole); the
proof goes in `SubcriticalCauchy.ClassificationProof` (already imported here),
which must not import this file.

**Correction.** The hypothesis `ν_0 > 0` is added; it is necessary (with
`ν_n = 6/(π² n²)` for `n ≥ 1` and `ν_0 = 0` no case applies) and, given the heavy
tail, sufficient. In cases (b)–(e) the law `μ` keeps the heavy tail of `ν`, so
`μ = ν`; in (a) it may be a light-tailed tilt of `ν`. Conventions: `offspringMean`
and the second moment `∑ k² μ_k` are taken in `ℝ≥0∞`; slow variation is the
approved measurable convention.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section

/-- U2.5, corrected (`ν_0 > 0`): a heavy-tailed offspring law with
`ν_n ∼ L(n)/n^{1+α}`, `α ≥ 0`, is equivalent to an offspring law `μ` of one of
the five kinds (a) critical with finite variance; (b) critical with infinite
variance and `α ∈ (1,2]`; (c) critical with `α = 1`; (d) subcritical with
`α > 1`; (e) subcritical with `α = 1`. In (b)–(e) the law `μ` keeps the heavy
tail of `ν` (so `μ = ν`); in (a) it may be a light-tailed tilt of `ν`. -/
theorem paper_heavyTail_classification (ν : Measure ℕ) [IsProbabilityMeasure ν]
    (hν0 : 0 < ν {0}) (α : ℝ) (hα : 0 ≤ α) {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : HasHeavyTail ν α L) :
    ∃ μ : Measure ℕ, IsProbabilityMeasure μ ∧ IsTiltEquivalent μ ν ∧
      ((offspringMean μ = 1 ∧ ∑' k : ℕ, (k : ℝ≥0∞) ^ 2 * μ {k} < ∞) ∨
        (offspringMean μ = 1 ∧ ∑' k : ℕ, (k : ℝ≥0∞) ^ 2 * μ {k} = ∞ ∧ 1 < α ∧ α ≤ 2 ∧
          HasHeavyTail μ α L) ∨
        (offspringMean μ = 1 ∧ α = 1 ∧ HasHeavyTail μ α L) ∨
        (offspringMean μ < 1 ∧ 1 < α ∧ HasHeavyTail μ α L) ∨
        (offspringMean μ < 1 ∧ α = 1 ∧ HasHeavyTail μ α L)) := by
  exact paper_heavyTail_classification_proof ν hν0 α hα hpos hL hsv hlocal

end
end SubcriticalCauchy.Bienayme
