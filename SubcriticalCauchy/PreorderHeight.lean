module

public import SubcriticalCauchy.CyclicResidualTreeAux

/-! # Lexicographic order of the preorder vertex enumeration -/

@[expose] public section

namespace SubcriticalCauchy.Bienayme
open BGW

/-- Preorder visits valid addresses in strictly increasing lexicographic order. -/
theorem vertices_pairwise_lt (t : PlaneTree) : t.vertices.Pairwise (· < ·) := by
  induction t with
  | node ts ih =>
    rw [PlaneTree.vertices_node, List.pairwise_cons]
    constructor
    · intro u hu
      obtain ⟨b, hb, hu⟩ := List.mem_flatten.mp hu
      obtain ⟨i, _, rfl⟩ := List.mem_mapIdx.mp hb
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hu
      simp
    · rw [List.pairwise_flatten]
      constructor
      · intro b hb
        obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.mp hb
        rw [List.pairwise_map]
        exact (ih _ (List.getElem_mem hi)).imp (fun h => by
          simpa only [List.cons_lt_cons_iff, lt_self_iff_false, true_and, false_or] using h)
      · rw [List.pairwise_iff_getElem]
        intro i j hi hj hij u hu v hv
        simp only [List.getElem_mapIdx] at hu hv
        obtain ⟨a, _, rfl⟩ := List.mem_map.mp hu
        obtain ⟨b, _, rfl⟩ := List.mem_map.mp hv
        exact List.cons_lt_cons_iff.mpr (Or.inl hij)

/-- In a sorted enumeration, the least point of a fiber is its first occurrence. -/
theorem idxOf_map_eq_idxOf_of_first {α β : Type*} [LinearOrder α] [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) {l : List α} {a : α} (hs : l.Pairwise (· < ·)) (ha : a ∈ l)
    (hfirst : ∀ b ∈ l, f b = f a → a ≤ b) :
    (l.map f).idxOf (f a) = l.idxOf a := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    obtain ⟨hbl, htail⟩ := List.pairwise_cons.mp hs
    by_cases hba : b = a
    · subst b
      simp
    · have hal : a ∈ l := (List.mem_cons.mp ha).resolve_left (Ne.symm hba)
      have hfa : f b ≠ f a := by
        intro heq
        exact (not_le_of_gt (hbl _ hal)) (hfirst b (by simp) heq)
      simpa [List.idxOf_cons, hba, hfa] using
        ih htail hal (fun c hc => hfirst c (by simp [hc]))

noncomputable section

local instance : DecidableEq PlaneTree := Classical.typeDecidableEq _

theorem height_node_le_of_children (ts : List PlaneTree) (B : ℕ)
    (h : ∀ s ∈ ts, 1 + height s ≤ B) : height (PlaneTree.node ts) ≤ B := by
  apply Finset.sup_le
  intro u hu
  have hu' := List.mem_toFinset.mp hu
  rw [PlaneTree.vertices_node] at hu'
  rcases List.mem_cons.mp hu' with rfl | hu'
  · simp
  · obtain ⟨b, hb, hu⟩ := List.mem_flatten.mp hu'
    obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.mp hb
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    have hvh := vertex_length_le_height ((PlaneTree.mem_vertices_iff _ _).mp hv)
    have hs := h _ (List.getElem_mem hi)
    simp only [List.length_cons]
    omega

theorem child_height_add_one_le (t : PlaneTree) {j : ℕ} (hj : j < t.children.length) :
    1 + height t.children[j] ≤ height t := by
  have hf : t.fringe? [j] = some t.children[j] := by simp [hj]
  simpa using height_fringe_add_le hf

theorem height_graft_le_add (t s : PlaneTree) (u : List ℕ) :
    height (t.graft u s) ≤ height t + height s := by
  induction u generalizing t with
  | nil => simp
  | cons i u ih =>
    rw [PlaneTree.graft_cons]
    apply height_node_le_of_children
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ha
    have hj' : j < t.children.length := by simpa using hj
    have hb := child_height_add_one_le t hj'
    by_cases hij : i = j
    · subst i
      rw [List.getElem_modify_eq]
      have hg := ih t.children[j]
      omega
    · rw [List.getElem_modify_ne _ _ hij]
      omega

theorem vertex_length_lt_size {t : PlaneTree} {u : List ℕ}
    (hu : t.IsVertex u) : u.length < t.size := by
  induction t generalizing u with
  | node ts ih =>
    have huv := (PlaneTree.mem_vertices_iff _ _).mpr hu
    rw [PlaneTree.vertices_node] at huv
    rcases List.mem_cons.mp huv with rfl | huv
    · simp [PlaneTree.size_node]
    · obtain ⟨b, hb, huv⟩ := List.mem_flatten.mp huv
      obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.mp hb
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp huv
      have hvh := ih _ (List.getElem_mem hi) ((PlaneTree.mem_vertices_iff _ _).mp hv)
      have hs : ts[i].size ≤ (ts.map PlaneTree.size).sum :=
        List.le_sum_of_mem (List.mem_map_of_mem (List.getElem_mem hi))
      simp only [List.length_cons, PlaneTree.size_node]
      omega

theorem height_lt_size (t : PlaneTree) : height t < t.size := by
  obtain ⟨u, hu, heq⟩ := Finset.exists_mem_eq_sup t.vertices.toFinset (vertices_nonempty t) List.length
  rw [height, heq]
  exact vertex_length_lt_size ((PlaneTree.mem_vertices_iff _ _).mp (List.mem_toFinset.mp hu))


theorem fringe_increments_split_with_height {t s : BGW.PlaneTree} {u : List ℕ}
    (h : t.fringe? u = some s) :
    ∃ a b : List ℤ, t.increments = a ++ s.increments ++ b ∧
      t.vertices[a.length]? = some u ∧ weakRecordCount a.reverse = u.length := by
  induction u generalizing t with
  | nil =>
    have ht : t = s := by simpa using h
    subst t
    refine ⟨[], [], by simp, ?_, ?_⟩
    · cases s with | node ts => simp
    · simp [weakRecordCount]
  | cons i u ih =>
    cases hc : t.children[i]? with
    | none => simp [hc] at h
    | some r =>
      have hr : r.fringe? u = some s := by simpa [hc] using h
      obtain ⟨a, b, heq, hidx, hrec⟩ := ih hr
      obtain ⟨hi, hri⟩ := List.getElem?_eq_some_iff.mp hc
      let xs := t.children.map BGW.PlaneTree.increments
      let vs := t.children.mapIdx fun j r => r.vertices.map (j :: ·)
      have hx : xs.flatten = (xs.take i).flatten ++ r.increments ++ (xs.drop (i + 1)).flatten := by
        have hs := flatten_split_at xs (i := i) (by simpa [xs] using hi)
        have he : xs[i]'(by simpa [xs] using hi) = r.increments := by
          dsimp only [xs]
          rw [List.getElem_map, hri]
        rw [he] at hs
        exact hs
      have hv : vs.flatten = (vs.take i).flatten ++ r.vertices.map (i :: ·) ++ (vs.drop (i + 1)).flatten := by
        have hs := flatten_split_at vs (i := i) (by simpa [vs] using hi)
        have he : vs[i]'(by simpa [vs] using hi) = r.vertices.map (i :: ·) := by
          dsimp only [vs]
          rw [List.getElem_mapIdx, hri]
        rw [he] at hs
        exact hs
      have hlen := preorder_prefix_blocks_length t.children i
      change (vs.take i).flatten.length = (xs.take i).flatten.length at hlen
      let q := (xs.take i).flatten
      let A := ((t.rootDegree : ℤ) - 1) :: (q ++ a)
      let B := b ++ (xs.drop (i + 1)).flatten
      have hfull : t.increments = A ++ s.increments ++ B := by
        conv_lhs => rw [← BGW.PlaneTree.node_children t, BGW.PlaneTree.increments_node]
        change (_ :: xs.flatten) = _
        rw [hx, heq]
        simp [A, B, q, List.append_assoc, BGW.PlaneTree.rootDegree]
      refine ⟨A, B, hfull, ?_, ?_⟩
      · conv_lhs => rw [← BGW.PlaneTree.node_children t, BGW.PlaneTree.vertices_node]
        change ([] :: vs.flatten)[A.length]? = _
        dsimp only [A, q]
        rw [List.length_cons, List.getElem?_cons_succ, hv, List.length_append, ← hlen]
        simp only [List.append_assoc, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
        have hia : a.length < r.vertices.length := by
          by_contra hh
          rw [List.getElem?_eq_none (by omega)] at hidx
          contradiction
        rw [List.getElem?_append_left (by simpa using hia), List.getElem?_map, hidx]
        rfl
      · have hnonneg : ∀ k ≤ A.length, 0 ≤ prefixSum A k := by
          have hlt : A.length < t.increments.length := by
            rw [hfull]
            simp only [List.length_append, BGW.PlaneTree.length_increments]
            have hs := BGW.PlaneTree.size_pos s
            omega
          intro k hk
          have hp := t.sum_take_increments_nonneg (lt_of_le_of_lt hk hlt)
          rw [hfull, List.append_assoc, List.take_append_of_le_length hk] at hp
          exact hp
        have hq : q = BGW.PlaneForest.increments (t.children.take i) := by
          simp [q, xs, BGW.PlaneForest.increments]
        change weakRecordCount (((t.rootDegree : ℤ) - 1) :: (q ++ a)).reverse = _
        rw [weakRecordCount_reverse_cons _ _ hnonneg, List.reverse_append,
          weakRecordCount_append_of_negative]
        · simp [hrec]
        · intro k hk hkl
          rw [hq]
          apply prefixSum_reverse_forest_negative _ hk
          simpa only [hq, List.length_reverse] using hkl

theorem preorder_height_eq_weakRecordCount {t : BGW.PlaneTree} {u : List ℕ}
    (hu : t.IsVertex u) :
    u.length = weakRecordCount (t.increments.take (t.vertices.idxOf u)).reverse := by
  obtain ⟨s, hs⟩ := hu
  obtain ⟨a, b, heq, hidx, hrec⟩ := fringe_increments_split_with_height hs
  obtain ⟨ha, hva⟩ := List.getElem?_eq_some_iff.mp hidx
  have hj : t.vertices.idxOf u = a.length := by
    rw [← hva]
    exact t.nodup_vertices.idxOf_getElem _ ha
  rw [hj, heq, List.append_assoc, List.take_left]
  exact hrec.symm


end
end SubcriticalCauchy.Bienayme
