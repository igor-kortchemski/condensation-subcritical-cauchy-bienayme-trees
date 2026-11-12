module

public import SubcriticalCauchy.MaxDegree
public import SubcriticalCauchy.AttachedForestHeight
public import SubcriticalCauchy.BienaymeBridgeStatistics
public import SubcriticalCauchy.DeletedIncrements

/-!
# The cyclic residual word — shared interface for M3, Propositions 4.2–4.3

Coordinator-owned shared definitions (10 November 2026), following
`docs/blueprint/CODING_INTERFACE.md`. Conventions: `PlaneTree` addresses use
zero-based child indices; `degrees` and `increments` are in root-first
preorder; the maximal vertex is the lexicographically first maximizer.

* `firstMaxIndex ds` is the preorder index of the first maximal degree.
* `cyclicResidual x` is the increment word read cyclically right after the
  first maximal increment, with that increment removed (length `x.length - 1`).
* `prefixSum x k` is the sum of the first `k` letters.
* `weakRecordCount x` counts the positive times `k ≤ x.length` at which the
  walk is at least as high as at every earlier time (weak ascending records,
  time zero excluded).
* `firstHit? d x` is the first time the walk of `x` equals `-d`, if any.
* `lastZero x` is the last time `k ≤ x.length` at which the walk is `0`.
* `exteriorSize t` is the number of vertices outside the fringe of the
  maximal vertex.
* `deletionWithPosition n ω` records the preorder position of the first
  maximal count together with the deleted increments; `uniformInsertionPosition n`
  is the uniform law on `{0, …, n - 1}`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace SubcriticalCauchy.Bienayme

noncomputable section
open BGW

/-- Preorder index of the first maximal degree. -/
def firstMaxIndex (ds : List ℕ) : ℕ :=
  ds.idxOf (listMaxDegree ds)

/-- The increment word read cyclically after the first maximal increment,
which is removed. -/
def cyclicResidual (x : List ℤ) : List ℤ :=
  (x.rotate (firstMaxIndex (wordDegrees x) + 1)).take (x.length - 1)

/-- Partial sum of the first `k` letters. -/
def prefixSum (x : List ℤ) (k : ℕ) : ℤ :=
  (x.take k).sum

/-- Number of weak ascending records at positive times. -/
def weakRecordCount (x : List ℤ) : ℕ :=
  ((Finset.range (x.length + 1)).filter fun k =>
    0 < k ∧ ∀ i < k, prefixSum x i ≤ prefixSum x k).card

/-- First time the walk of `x` equals `-d`, if any. -/
def firstHit? (d : ℕ) (x : List ℤ) : Option ℕ :=
  (List.range (x.length + 1)).find? (fun k => decide (prefixSum x k = -(d : ℤ)))

/-- Last time the walk of `x` is at zero (`0` if only at time zero). -/
def lastZero (x : List ℤ) : ℕ :=
  ((Finset.range (x.length + 1)).filter fun k => prefixSum x k = 0).sup id

/-- Number of vertices outside the fringe of the maximal vertex. -/
def exteriorSize (t : PlaneTree) : ℕ :=
  t.size - (maxDegreeFringe t).size

/-- The uniform law on `{0, …, n - 1}` (zero measure for `n = 0`). -/
def uniformInsertionPosition (n : ℕ) : Measure ℕ :=
  (n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (i : ℕ)

/-- Position of the first maximal count, with the deleted increments. -/
def deletionWithPosition (n : ℕ) (ω : Fin n → ℕ) : ℕ × (Fin (n - 1) → ℤ) :=
  (firstMaxIndex (List.ofFn ω), deletedIncrements n ω)

end
end SubcriticalCauchy.Bienayme
