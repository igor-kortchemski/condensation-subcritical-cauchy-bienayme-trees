module

public import SubcriticalCauchy.MaxDegree
public import SubcriticalCauchy.BienaymeHeight

/-!
# Deterministic height comparisons for the selected attached forest

A fringe subtree's height plus its root depth is bounded by the full height.
The selected vertex's children contribute one further edge. These are lower
bounds for full height; they do not control branches outside the selected fringe.
-/

@[expose] public section

namespace SubcriticalCauchy.Bienayme

noncomputable section

local instance : DecidableEq BGW.PlaneTree := Classical.typeDecidableEq _

theorem vertex_length_le_height {t : BGW.PlaneTree} {u : List ℕ}
    (hu : t.IsVertex u) : u.length ≤ height t :=
  Finset.le_sup (f := List.length) (List.mem_toFinset.mpr
    ((BGW.PlaneTree.mem_vertices_iff t u).mpr hu))

/-- Root depth is added to the re-rooted fringe height. -/
theorem height_fringe_add_le {t s : BGW.PlaneTree} {u : List ℕ}
    (h : t.fringe? u = some s) : u.length + height s ≤ height t := by
  obtain ⟨v, hv, hheight⟩ := Finset.exists_mem_eq_sup s.vertices.toFinset
    (vertices_nonempty s) List.length
  have hvertex : s.IsVertex v := (BGW.PlaneTree.mem_vertices_iff s v).mp
    (List.mem_toFinset.mp hv)
  have htv : t.IsVertex (u ++ v) :=
    (BGW.PlaneTree.isVertex_append_iff t u v).mpr ⟨s, h, hvertex⟩
  change u.length + s.vertices.toFinset.sup List.length ≤ height t
  simpa only [List.length_append, ← hheight] using vertex_length_le_height htv

/-- Graph distance from the root to the selected maximal-degree vertex. -/
def maxDegreeDepth (t : BGW.PlaneTree) : ℕ := (maxDegreeVertex t).length

theorem maxDegreeDepth_le_height (t : BGW.PlaneTree) : maxDegreeDepth t ≤ height t :=
  vertex_length_le_height (maxDegreeVertex_isVertex t)

theorem attachedChild_height_add_le {t s : BGW.PlaneTree} {i : ℕ}
    (h : attachedChild t i = some s) : maxDegreeDepth t + 1 + height s ≤ height t := by
  have hf : t.fringe? (maxDegreeVertex t ++ [i - 1]) = some s := by
    rw [fringe_maxDegreeVertex_child, h]
  simpa only [List.length_append, List.length_singleton, maxDegreeDepth] using
    height_fringe_add_le hf

theorem attachedForest_mem_height_add_le {t s : BGW.PlaneTree}
    (hs : s ∈ attachedForest t) : maxDegreeDepth t + 1 + height s ≤ height t := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hs
  apply attachedChild_height_add_le (i := j + 1)
  simpa only [attachedChild, Nat.add_sub_cancel] using hj

/-- Maximum component height, with zero for the empty attached forest. -/
def attachedForestHeight (t : BGW.PlaneTree) : ℕ := (attachedForest t).toFinset.sup height

theorem attachedForestHeight_le_height (t : BGW.PlaneTree) :
    attachedForestHeight t ≤ height t := by
  unfold attachedForestHeight
  apply Finset.sup_le
  intro s hs
  have h := attachedForest_mem_height_add_le (List.mem_toFinset.mp hs)
  omega

/-- The stronger depth-shifted bound needs an actual child component. -/
theorem depth_add_one_add_attachedForestHeight_le (t : BGW.PlaneTree)
    (hne : (attachedForest t).toFinset.Nonempty) :
    maxDegreeDepth t + 1 + attachedForestHeight t ≤ height t := by
  obtain ⟨s, hs, hheight⟩ := Finset.exists_mem_eq_sup (attachedForest t).toFinset hne height
  change maxDegreeDepth t + 1 + (attachedForest t).toFinset.sup height ≤ height t
  rw [hheight]
  exact attachedForest_mem_height_add_le (List.mem_toFinset.mp hs)

end
end SubcriticalCauchy.Bienayme
