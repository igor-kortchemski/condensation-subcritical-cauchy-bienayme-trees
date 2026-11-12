module

public import BGW.Tree.DFS
public import BGW.Tree.Fringe
public import BGW.Tree.LocallyFinite
public import Mathlib.Data.List.Lex
public import Mathlib.Data.Finset.Max


/-!
# The lexicographically first maximal-degree vertex and its attached forest

All statistics here use the finite BGW carrier underlying the constructed law.
Addresses use zero-based child indices. Positive-address conversion preserves
lexicographic order, so the selected vertex has the paper's tie convention.
Absent child slots are `none`, distinguished from a present leaf.
-/

@[expose] public section

namespace SubcriticalCauchy.Bienayme

noncomputable section

/-- Outdegree at a vertex address. The zero default at invalid addresses never
enters vertex selection; lookup success is proved for every selected address. -/
def degreeAt (t : BGW.PlaneTree) (u : List ℕ) : ℕ :=
  ((t.fringe? u).map BGW.PlaneTree.rootDegree).getD 0

theorem degreeAt_of_fringe {t s : BGW.PlaneTree} {u : List ℕ}
    (h : t.fringe? u = some s) : degreeAt t u = s.rootDegree := by
  simp [degreeAt, h]

/-- Largest outdegree, counting actual vertex occurrences. -/
def maxDegree (t : BGW.PlaneTree) : ℕ := t.vertices.toFinset.sup (degreeAt t)

theorem degreeAt_le_maxDegree {t : BGW.PlaneTree} {u : List ℕ}
    (hu : t.IsVertex u) : degreeAt t u ≤ maxDegree t :=
  Finset.le_sup (f := degreeAt t) (by simpa [BGW.PlaneTree.mem_vertices_iff] using hu)

theorem vertices_nonempty (t : BGW.PlaneTree) : t.vertices.toFinset.Nonempty :=
  ⟨[], List.mem_toFinset.mpr ((BGW.PlaneTree.mem_vertices_iff t []).mpr
    ⟨t, BGW.PlaneTree.fringe?_nil t⟩)⟩

theorem map_degreeAt_vertices (t : BGW.PlaneTree) :
    t.vertices.map (degreeAt t) = t.degrees := by
  have h := congrArg (List.map (fun a : Option ℕ => a.getD 0))
    (BGW.PlaneTree.map_fringe?_vertices_rootDegree t)
  change t.vertices.map (fun u => ((t.fringe? u).map BGW.PlaneTree.rootDegree).getD 0) = t.degrees
  simpa [List.map_map, Function.comp_def] using h

/-- The vertex maximum agrees with the maximum of the depth-first degree list. -/
theorem maxDegree_eq_degrees_sup (t : BGW.PlaneTree) :
    maxDegree t = t.degrees.toFinset.sup id := by
  rw [← map_degreeAt_vertices]
  apply le_antisymm
  · apply Finset.sup_le
    intro u hu
    exact Finset.le_sup (f := id) (List.mem_toFinset.mpr
      (List.mem_map_of_mem (List.mem_toFinset.mp hu)))
  · apply Finset.sup_le
    intro d hd
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hd)
    exact Finset.le_sup (f := degreeAt t) (List.mem_toFinset.mpr hu)

def maximalVertices (t : BGW.PlaneTree) : Finset (List ℕ) :=
  t.vertices.toFinset.filter (fun u => degreeAt t u = maxDegree t)

theorem maximalVertices_nonempty (t : BGW.PlaneTree) : (maximalVertices t).Nonempty := by
  obtain ⟨u, hu, heq⟩ := Finset.exists_mem_eq_sup t.vertices.toFinset
    (vertices_nonempty t) (degreeAt t)
  exact ⟨u, Finset.mem_filter.mpr ⟨hu, heq.symm⟩⟩

/-- First maximal-degree vertex in lexicographic order, including prefix order. -/
def maxDegreeVertex (t : BGW.PlaneTree) : List ℕ :=
  (maximalVertices t).min' (maximalVertices_nonempty t)

theorem maxDegreeVertex_mem (t : BGW.PlaneTree) :
    maxDegreeVertex t ∈ maximalVertices t := Finset.min'_mem _ _

theorem maxDegreeVertex_isVertex (t : BGW.PlaneTree) : t.IsVertex (maxDegreeVertex t) :=
  (BGW.PlaneTree.mem_vertices_iff t (maxDegreeVertex t)).mp
    (List.mem_toFinset.mp (Finset.mem_filter.mp (maxDegreeVertex_mem t)).1)

theorem degreeAt_maxDegreeVertex (t : BGW.PlaneTree) :
    degreeAt t (maxDegreeVertex t) = maxDegree t :=
  (Finset.mem_filter.mp (maxDegreeVertex_mem t)).2

theorem maxDegreeVertex_le {t : BGW.PlaneTree} {u : List ℕ}
    (hu : t.IsVertex u) (hdeg : degreeAt t u = maxDegree t) : maxDegreeVertex t ≤ u := by
  have hmem : u ∈ t.vertices.toFinset := List.mem_toFinset.mpr
    ((BGW.PlaneTree.mem_vertices_iff t u).mpr hu)
  exact Finset.min'_le (maximalVertices t) u (Finset.mem_filter.mpr ⟨hmem, hdeg⟩)

theorem maxDegreeVertex_unique {t : BGW.PlaneTree} {u : List ℕ}
    (hu : t.IsVertex u) (hdeg : degreeAt t u = maxDegree t)
    (hfirst : ∀ v, t.IsVertex v → degreeAt t v = maxDegree t → u ≤ v) :
    u = maxDegreeVertex t := by
  exact le_antisymm (hfirst _ (maxDegreeVertex_isVertex t) (degreeAt_maxDegreeVertex t))
    (maxDegreeVertex_le hu hdeg)

theorem positiveAddress_lt_iff (u v : List ℕ) :
    BGW.PlaneTree.positiveAddress u < BGW.PlaneTree.positiveAddress v ↔ u < v := by
  induction u generalizing v with
  | nil => cases v <;> simp [BGW.PlaneTree.positiveAddress]
  | cons a u ih =>
    cases v with
    | nil => simp [BGW.PlaneTree.positiveAddress]
    | cons b v => simpa only [BGW.PlaneTree.positiveAddress, List.map_cons,
        List.cons_lt_cons_iff, Nat.succ_lt_succ_iff, Nat.succ_inj] using
        (show a < b ∨ a = b ∧ BGW.PlaneTree.positiveAddress u <
          BGW.PlaneTree.positiveAddress v ↔ a < b ∨ a = b ∧ u < v from by rw [ih])

theorem positiveAddress_le_iff (u v : List ℕ) :
    BGW.PlaneTree.positiveAddress u ≤ BGW.PlaneTree.positiveAddress v ↔ u ≤ v := by
  simpa only [not_lt] using not_congr (positiveAddress_lt_iff v u)

/-- The selected fringe is an actual subtree, obtained from lookup success. -/
def maxDegreeFringe (t : BGW.PlaneTree) : BGW.PlaneTree :=
  Classical.choose (maxDegreeVertex_isVertex t)

theorem fringe_maxDegreeVertex (t : BGW.PlaneTree) :
    t.fringe? (maxDegreeVertex t) = some (maxDegreeFringe t) :=
  Classical.choose_spec (maxDegreeVertex_isVertex t)

theorem rootDegree_maxDegreeFringe (t : BGW.PlaneTree) :
    (maxDegreeFringe t).rootDegree = maxDegree t := by
  rw [← degreeAt_of_fringe (fringe_maxDegreeVertex t), degreeAt_maxDegreeVertex]

/-- The ordered subtrees rooted at children of the selected vertex. -/
def attachedForest (t : BGW.PlaneTree) : BGW.PlaneForest := (maxDegreeFringe t).children

theorem length_attachedForest (t : BGW.PlaneTree) : (attachedForest t).length = maxDegree t :=
  rootDegree_maxDegreeFringe t

/-- Source child slot `i`, with one-based indexing for `i ≥ 1`. -/
def attachedChild (t : BGW.PlaneTree) (i : ℕ) : Option BGW.PlaneTree :=
  (attachedForest t)[i - 1]?

theorem fringe_maxDegreeVertex_child (t : BGW.PlaneTree) (i : ℕ) :
    t.fringe? (maxDegreeVertex t ++ [i - 1]) = attachedChild t i := by
  rw [BGW.PlaneTree.fringe?_append, fringe_maxDegreeVertex]
  simp [BGW.PlaneTree.fringe?_cons, attachedChild, attachedForest]

theorem attachedChild_eq_none_iff (t : BGW.PlaneTree) {i : ℕ} (hi : 1 ≤ i) :
    attachedChild t i = none ↔ maxDegree t < i := by
  simp only [attachedChild, List.getElem?_eq_none_iff, length_attachedForest]
  omega

/-- Slots in the source's interval `[j,k]`, retaining absent slots beyond the
degree. The source-facing characterizations use `1 ≤ j ≤ k`. -/
def attachedForestSlice (t : BGW.PlaneTree) (j k : ℕ) : List (Option BGW.PlaneTree) :=
  List.ofFn (fun i : Fin (k + 1 - j) => attachedChild t (j + i.val))

@[simp] theorem length_attachedForestSlice (t : BGW.PlaneTree) (j k : ℕ) :
    (attachedForestSlice t j k).length = k + 1 - j := by simp [attachedForestSlice]

theorem getElem_attachedForestSlice (t : BGW.PlaneTree) (j k i : ℕ)
    (hi : i < k + 1 - j) :
    (attachedForestSlice t j k)[i]'(by simpa only [length_attachedForestSlice] using hi) = attachedChild t (j + i) := by
  simp [attachedForestSlice]

theorem attachedForestSlice_slot_present (t : BGW.PlaneTree) {j k i : ℕ}
    (hj : 1 ≤ j) (hk : k ≤ maxDegree t) (hi : i < k + 1 - j) :
    (attachedForestSlice t j k)[i]'(by simpa only [length_attachedForestSlice] using hi) ≠ none := by
  rw [getElem_attachedForestSlice t j k i hi]
  intro hnone
  have hlt := (attachedChild_eq_none_iff t (i := j + i) (by omega)).mp hnone
  omega

end
end SubcriticalCauchy.Bienayme
