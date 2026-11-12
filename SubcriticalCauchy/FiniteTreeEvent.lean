module

public import SubcriticalCauchy.BienaymeTilting

/-!
# Events of finite trees on the locally finite carrier

`finiteTreeEvent P` is the set of locally finite trees that are finite plane
trees satisfying `P`. The embedding is injective and its range is the set of
finite trees, so the conditioned law reads `P` on the actual finite tree.
Approved by the author with the key statements on 10 November 2026.
-/

@[expose] public section

namespace SubcriticalCauchy.Bienayme

open BGW BGW.LocallyFinite

/-- The event that the (finite) tree satisfies `P`, on the locally finite carrier. -/
def finiteTreeEvent (P : PlaneTree → Prop) : Set Tree :=
  PlaneTree.toLocallyFinite '' {t : PlaneTree | P t}

end SubcriticalCauchy.Bienayme
