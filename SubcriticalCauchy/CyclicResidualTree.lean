module

public import SubcriticalCauchy.CyclicResidualTreeAux
public import SubcriticalCauchy.PreorderHeight

/-! # Deterministic identities for cyclic residual tree words -/

@[expose] public section

namespace SubcriticalCauchy.Bienayme

open BGW

noncomputable section

/-- Lexicographic and preorder tie breaking select the same maximal vertex. -/
theorem firstMaxIndex_degrees (t : PlaneTree) :
    firstMaxIndex t.degrees = t.vertices.idxOf (maxDegreeVertex t) := by
  rw [firstMaxIndex, ← maxDegree_eq_listMaxDegree, ← degreeAt_maxDegreeVertex t,
    ← map_degreeAt_vertices]
  apply idxOf_map_eq_idxOf_of_first (degreeAt t) (vertices_pairwise_lt t)
    ((PlaneTree.mem_vertices_iff _ _).mpr (maxDegreeVertex_isVertex t))
  intro u hu hdeg
  apply maxDegreeVertex_le ((PlaneTree.mem_vertices_iff _ _).mp hu)
  exact hdeg.trans (degreeAt_maxDegreeVertex t)

/-- Removing one letter after a cyclic rotation leaves all other vertices. -/
theorem length_cyclicResidual_tree (t : PlaneTree) :
    (cyclicResidual t.increments).length = t.size - 1 := by
  simp [cyclicResidual, List.length_take]

/-- The residual's total displacement is minus the removed outdegree. -/
theorem sum_cyclicResidual_tree (t : PlaneTree) :
    (cyclicResidual t.increments).sum = -(maxDegree t : ℤ) := by
  have hj := firstMaxIndex_degrees_lt t
  have hji : firstMaxIndex t.degrees < t.increments.length := by simpa using hj
  rw [cyclicResidual, wordDegrees_increments, sum_rotate_take_pred _ hji,
    PlaneTree.sum_increments]
  have hget : t.degrees[firstMaxIndex t.degrees] = listMaxDegree t.degrees :=
    List.getElem_idxOf hj
  have hmax : listMaxDegree t.degrees = maxDegree t :=
    (maxDegree_eq_listMaxDegree t).symm
  simp only [PlaneTree.increments, List.getElem_map]
  rw [hget, hmax]
  omega

theorem height_le_exteriorSize_add (t : PlaneTree) :
    height t ≤ exteriorSize t + 1 + attachedForestHeight t := by
  classical
  have hg := height_graft_le_add (t.cut (maxDegreeVertex t)) (maxDegreeFringe t)
    (maxDegreeVertex t)
  rw [PlaneTree.graft_cut (fringe_maxDegreeVertex t)] at hg
  have hsize := PlaneTree.size_graft_add (fringe_maxDegreeVertex t) PlaneTree.leaf
  have hcut := height_lt_size (t.cut (maxDegreeVertex t))
  have hspos := PlaneTree.size_pos (maxDegreeFringe t)
  have hcutBound : height (t.cut (maxDegreeVertex t)) ≤ exteriorSize t := by
    change height (t.graft (maxDegreeVertex t) PlaneTree.leaf) <
      (t.graft (maxDegreeVertex t) PlaneTree.leaf).size at hcut
    simp only [PlaneTree.size_leaf] at hsize
    unfold exteriorSize
    change height (t.graft (maxDegreeVertex t) PlaneTree.leaf) ≤ _
    omega
  have hfringe : height (maxDegreeFringe t) ≤ 1 + attachedForestHeight t := by
    conv_lhs => rw [← PlaneTree.node_children (maxDegreeFringe t)]
    apply height_node_le_of_children
    intro s hs
    have hm : height s ≤ attachedForestHeight t :=
      Finset.le_sup (f := height) (List.mem_toFinset.mpr hs)
    omega
  omega

theorem size_attachedForest (t : PlaneTree) :
    (attachedForest t).size = (maxDegreeFringe t).size - 1 := by
  have h := PlaneTree.size_node (maxDegreeFringe t).children
  rw [PlaneTree.node_children] at h
  change ((maxDegreeFringe t).children.map PlaneTree.size).sum = _
  omega

theorem cyclicResidual_tree_split (t : PlaneTree) :
    ∃ a b : List ℤ, cyclicResidual t.increments =
      PlaneForest.increments (attachedForest t) ++ b ++ a ∧
      t.increments = a ++ (maxDegreeFringe t).increments ++ b := by
  obtain ⟨a, b, heq, hidx⟩ := fringe_increments_split (fringe_maxDegreeVertex t)
  obtain ⟨ha, hva⟩ := List.getElem?_eq_some_iff.mp hidx
  have hindex : t.vertices.idxOf (maxDegreeVertex t) = a.length := by
    rw [← hva]
    exact t.nodup_vertices.idxOf_getElem _ ha
  have hj : firstMaxIndex t.degrees = a.length := (firstMaxIndex_degrees t).trans hindex
  have hf : (maxDegreeFringe t).increments = ((maxDegree t : ℤ) - 1) ::
      PlaneForest.increments (attachedForest t) := by
    conv_lhs => rw [← PlaneTree.node_children (maxDegreeFringe t), PlaneTree.increments_node]
    rw [← rootDegree_maxDegreeFringe]
    rfl
  refine ⟨a, b, ?_, heq⟩
  rw [cyclicResidual, wordDegrees_increments,
    rotate_take_pred_eq _ (by simpa using firstMaxIndex_degrees_lt t), hj, heq, hf]
  simp [List.drop_append, List.append_assoc]

theorem take_firstHit_eq_attachedForest (t : PlaneTree) :
    (cyclicResidual t.increments).take ((maxDegreeFringe t).size - 1) =
      PlaneForest.increments (attachedForest t) := by
  obtain ⟨a, b, heq, _⟩ := cyclicResidual_tree_split t
  rw [heq, ← size_attachedForest, ← PlaneForest.length_increments]
  simp [List.append_assoc]

theorem firstHit_cyclicResidual_tree (t : PlaneTree) :
    firstHit? (maxDegree t) (cyclicResidual t.increments) =
      some ((maxDegreeFringe t).size - 1) := by
  obtain ⟨a, b, heq, _⟩ := cyclicResidual_tree_split t
  rw [heq, List.append_assoc, ← length_attachedForest, ← size_attachedForest]
  exact firstHit_forest_increments_append _ _

theorem cyclicResidual_take_attachedForest_split (t : PlaneTree) (k : ℕ) :
    ∃ b : List ℤ, cyclicResidual t.increments =
      PlaneForest.increments ((attachedForest t).take k) ++ b := by
  obtain ⟨a, b, heq, _⟩ := cyclicResidual_tree_split t
  have hf := congrArg PlaneForest.increments (List.take_append_drop k (attachedForest t))
  simp only [PlaneForest.increments, List.map_append, List.flatten_append] at hf
  change PlaneForest.increments ((attachedForest t).take k) ++
    PlaneForest.increments ((attachedForest t).drop k) =
    PlaneForest.increments (attachedForest t) at hf
  refine ⟨PlaneForest.increments ((attachedForest t).drop k) ++ b ++ a, ?_⟩
  rw [heq, ← hf]
  simp [List.append_assoc]

theorem firstHit_cyclicResidual_take_attachedForest (t : PlaneTree) {k : ℕ}
    (hk : k ≤ maxDegree t) :
    firstHit? k (cyclicResidual t.increments) =
      some (PlaneForest.size ((attachedForest t).take k)) := by
  obtain ⟨b, hb⟩ := cyclicResidual_take_attachedForest_split t k
  have hlen : ((attachedForest t).take k).length = k := by
    simp [List.length_take, length_attachedForest, Nat.min_eq_left hk]
  have hh := firstHit_forest_increments_append ((attachedForest t).take k) b
  rw [hlen] at hh
  rw [hb]
  exact hh

theorem take_firstHit_eq_attachedForest_take (t : PlaneTree) (k : ℕ) :
    (cyclicResidual t.increments).take (PlaneForest.size ((attachedForest t).take k)) =
      PlaneForest.increments ((attachedForest t).take k) := by
  obtain ⟨b, hb⟩ := cyclicResidual_take_attachedForest_split t k
  rw [hb, ← PlaneForest.length_increments]
  exact List.take_left

/-- The last zero in reverse time counts the vertices outside the selected fringe. -/
theorem exteriorSize_eq_lastZero (t : PlaneTree) :
    exteriorSize t = lastZero (cyclicResidual t.increments).reverse := by
  rw [lastZero_reverse_eq_of_firstHit (sum_cyclicResidual_tree t)
    (firstHit_cyclicResidual_tree t), length_cyclicResidual_tree]
  have hp := PlaneTree.size_pos (maxDegreeFringe t)
  unfold exteriorSize
  omega

/-- Reading any final segment of a tree word backwards stays strictly negative. -/
theorem prefixSum_reverse_tree_drop_negative (t : PlaneTree) (j : ℕ) {k : ℕ}
    (hk : 0 < k) (hkl : k ≤ (t.increments.drop j).reverse.length) :
    prefixSum (t.increments.drop j).reverse k < 0 := by
  have hk' : k ≤ t.increments.length - j := by simpa using hkl
  have hkt : k ≤ t.increments.length := by omega
  have hp : prefixSum t.increments.reverse k < 0 := by
    have hh := prefixSum_reverse_forest_negative [t] hk (by simpa [PlaneForest.increments] using hkt)
    simpa [PlaneForest.increments] using hh
  rw [List.reverse_drop]
  simpa only [prefixSum, List.take_take, Nat.min_eq_left hk'] using hp

/-- Reversed weak records count the ancestors of the first maximal-degree vertex. -/
theorem maxDegreeDepth_eq_weakRecordCount (t : PlaneTree) :
    maxDegreeDepth t = weakRecordCount (cyclicResidual t.increments).reverse := by
  have hj := firstMaxIndex_degrees_lt t
  have hji : firstMaxIndex t.degrees < t.increments.length := by simpa using hj
  rw [cyclicResidual, wordDegrees_increments, rotate_take_pred_eq _ hji,
    List.reverse_append, weakRecordCount_append_of_negative]
  · rw [firstMaxIndex_degrees]
    exact preorder_height_eq_weakRecordCount (maxDegreeVertex_isVertex t)
  · intro k hk hkl
    exact prefixSum_reverse_tree_drop_negative t _ hk hkl

end
end SubcriticalCauchy.Bienayme
