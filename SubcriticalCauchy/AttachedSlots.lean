module

public import SubcriticalCauchy.MaxDegree
public import SubcriticalCauchy.BienaymeTilting

/-!
# Attached slots of the maximal vertex — frozen definitions

Approved by the author on 10 November 2026 with Proposition 4.2, and frozen
whole: this file is read only, byte for byte.

`attachedSlotsTree k t` lists the first `k` child subtrees of the first
maximal-degree vertex of `t`, in order. **Convention:** the paper pads absent
slots with the empty tree; `BGW.LocallyFinite.Tree` has no empty tree, so an
absent slot is padded here by the one-vertex tree `leaf`. Absent slots occur
only when `Δ(T_n) < k`, whose probability tends to zero for `k = ⌊δ n⌋`,
`δ < 1 - m` (M1), so the limit statement is unaffected.

`attachedSlotsLaw μ n k` is the law of these slots under the conditioned tree:
the conditioned law charges only finite trees, each the image of a unique
plane tree, so it is the sum of the atoms.
-/

@[expose] public section

open MeasureTheory

namespace SubcriticalCauchy.Bienayme

noncomputable section
open BGW BGW.LocallyFinite

/-- The first `k` child subtrees of the maximal vertex, padded by `leaf`. -/
def attachedSlotsTree (k : ℕ) (t : PlaneTree) : Fin k → Tree :=
  fun i => ((attachedChild t (i.val + 1)).getD PlaneTree.leaf).toLocallyFinite

/-- Law of the first `k` attached subtrees under the conditioned tree. -/
def attachedSlotsLaw (μ : Measure ℕ) [IsProbabilityMeasure μ] (n k : ℕ) :
    Measure (Fin k → Tree) :=
  Measure.sum fun t : PlaneTree =>
    conditioned μ n {t.toLocallyFinite} • Measure.dirac (attachedSlotsTree k t)

end
end SubcriticalCauchy.Bienayme
