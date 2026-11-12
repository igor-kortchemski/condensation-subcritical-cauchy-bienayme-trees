module

public import SubcriticalCauchy.PlaneTree
public import Mathlib.Data.Set.Finite.List

/-!
# Finiteness at a fixed tree size

There are finitely many finite rooted ordered trees with a prescribed number
of vertices. This supplies the finiteness needed for size-conditioned offspring
weight sums, without assuming a probability law on all finite trees.
-/

public section

namespace SubcriticalCauchy.PlaneTree

private theorem child_size_le_sum {t : PlaneTree} {children : List PlaneTree}
    (ht : t ∈ children) : t.size ≤ (children.map size).sum := by
  induction children with
  | nil => simp at ht
  | cons u children ih =>
    simp only [List.mem_cons] at ht
    simp only [List.map_cons, List.sum_cons]
    rcases ht with rfl | ht
    · omega
    · have h := ih ht
      omega

private theorem children_length_le_sum (children : List PlaneTree) :
    children.length ≤ (children.map size).sum := by
  induction children with
  | nil => simp
  | cons t children ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    have ht := t.size_pos
    omega

/-- Only finitely many plane trees have at most a prescribed number of vertices. -/
theorem finite_size_le (n : ℕ) : Set.Finite {t : PlaneTree | t.size ≤ n} := by
  induction n with
  | zero =>
    have heq : {t : PlaneTree | t.size ≤ 0} = ∅ := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact not_le_of_gt t.size_pos
    rw [heq]
    exact Set.finite_empty
  | succ n ih =>
    let : Finite {t : PlaneTree // t.size ≤ n} := ih
    let f : List {t : PlaneTree // t.size ≤ n} → PlaneTree :=
      fun children => .node (children.map Subtype.val)
    refine ((List.finite_length_le {t : PlaneTree // t.size ≤ n} n).image f).subset ?_
    rintro ⟨children⟩ hsize
    change (PlaneTree.node children).size ≤ n + 1 at hsize
    rw [size_node] at hsize
    have hsum : (children.map size).sum ≤ n := by omega
    have hchildren (t : PlaneTree) (ht : t ∈ children) : t.size ≤ n :=
      le_trans (child_size_le_sum ht) hsum
    have hlength : children.length ≤ n :=
      le_trans (children_length_le_sum children) hsum
    let bounded : List {t : PlaneTree // t.size ≤ n} :=
      children.attach.map fun t => ⟨t.val, hchildren t.val t.property⟩
    refine ⟨bounded, ?_, ?_⟩
    · change bounded.length ≤ n
      simpa [bounded] using hlength
    · change PlaneTree.node (bounded.map Subtype.val) = PlaneTree.node children
      congr 1
      simp [bounded, List.map_map]

/-- Only finitely many plane trees have a given positive or zero size. -/
theorem finite_size_eq (n : ℕ) : Set.Finite {t : PlaneTree | t.size = n} :=
  (finite_size_le n).subset fun _ ht => le_of_eq ht

end SubcriticalCauchy.PlaneTree
