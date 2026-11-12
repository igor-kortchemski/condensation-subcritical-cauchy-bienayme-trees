module

public import SubcriticalCauchy.MaximumSwapLaw
public import SubcriticalCauchy.DeleteMaximum

/-!
# Increments left after deleting the first maximum

Shared definitions for Theorem 3.1. `incrementLaw μ` is the law of one increment
`X = ξ - 1`, and `deletedIncrements n ω` lists, as a vector of length `n - 1`,
the increments of the counts `ω` after deleting the first maximal count, in
their original order. The vector has no junk entries: for `n ≥ 1` the deleted
word has length exactly `n - 1`.
-/

@[expose] public section

open MeasureTheory

namespace SubcriticalCauchy.Bienayme

noncomputable section

/-- The law of one increment `X = ξ - 1`. -/
def incrementLaw (μ : Measure ℕ) : Measure ℤ := μ.map (fun k : ℕ => (k : ℤ) - 1)

/-- The `n - 1` increments left after deleting the first maximum, as a vector. -/
def deletedIncrements (n : ℕ) (ω : Fin n → ℕ) : Fin (n - 1) → ℤ :=
  fun i => (deletedMaximumWord (List.ofFn ω)).getD i 0

end
end SubcriticalCauchy.Bienayme
