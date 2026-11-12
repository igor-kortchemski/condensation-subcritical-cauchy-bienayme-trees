module

public import SubcriticalCauchy.MeasurableHypothesis
public import SubcriticalCauchy.MaximumSwapLaw
public import SubcriticalCauchy.DeletedIncrements
public import Mathlib.MeasureTheory.Measure.TotalVariation.Defs
public import SubcriticalCauchy.MainProofs.Theorem31

/-!
# Theorem 3.1 — frozen statement

Approved by the author on 10 November 2026 under the measurable slow-variation
convention, and frozen: this file may change only inside its registered
`sorry` hole, filled with proof text only. The proof goes in the helper module
`SubcriticalCauchy.MainProofs.Theorem31`, already imported here.

`bridgeCountsLaw μ n` is the law of `n` iid offspring counts conditioned on
summing to `n - 1`, that is of the increments `X_i = ξ_i - 1` conditioned on
`W_n = -1` (zero measure at a null size). `deletedIncrements` deletes the first
maximal count and returns the other increments in their original order.
Mathlib's `tvDist` takes values in `[0, 2]`, twice the paper's normalization.
The laws live on `ℤ^{n-1}` rather than the paper's `ℝ^{n-1}`; both are carried
by `ℤ^{n-1}`, which embeds measurably, so the total variation is the same.
At a null size the conditioned law is zero and `tvDist` equals `1`; under the
hypothesis only finitely many sizes are null.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section

/-- Theorem 3.1: conditionally on `W_n = -1`, the increments left after deleting
the first maximal one are asymptotically iid in total variation. -/
theorem paper_deleted_maximum_tvDist (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) :
    Tendsto (fun n : ℕ => tvDist ((MaximumSwapLaw.bridgeCountsLaw μ n).map (deletedIncrements n))
        (Measure.pi fun _ : Fin (n - 1) => incrementLaw μ))
      atTop (𝓝 0) := by
  exact deleted_maximum_tvDist μ hμ

end
end SubcriticalCauchy.Bienayme
