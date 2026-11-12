module

public import SubcriticalCauchy.CyclicResidual

/-! # List identities used by cyclic residual tree coding -/

@[expose] public section

namespace SubcriticalCauchy.Bienayme
open BGW
noncomputable section

/-- A rotation followed by deletion of its last letter skips the chosen letter. -/
theorem rotate_take_pred_eq (x : List ℤ) {j : ℕ} (hj : j < x.length) :
    (x.rotate (j + 1)).take (x.length - 1) = x.drop (j + 1) ++ x.take j := by
  rw [List.rotate_eq_drop_append_take (by omega), List.take_append,
    List.take_of_length_le (by simp; omega), List.take_take]
  congr 1
  congr 1
  simp only [List.length_drop]
  omega

/-- Sum of the word obtained by reading cyclically after a deleted letter. -/
theorem sum_rotate_take_pred (x : List ℤ) {j : ℕ} (hj : j < x.length) :
    ((x.rotate (j + 1)).take (x.length - 1)).sum = x.sum - x[j] := by
  rw [rotate_take_pred_eq x hj, List.sum_append]
  have hsplit := List.sum_take_add_sum_drop x (j + 1)
  rw [List.take_succ_eq_append_getElem hj, List.sum_append, List.sum_singleton] at hsplit
  omega

/-- The first maximal degree occurs at a genuine preorder position. -/
theorem firstMaxIndex_degrees_lt (t : PlaneTree) :
    firstMaxIndex t.degrees < t.degrees.length := by
  apply List.idxOf_lt_length_of_mem
  rw [← maxDegree_eq_listMaxDegree, ← map_degreeAt_vertices]
  exact List.mem_map.mpr ⟨maxDegreeVertex t,
    (PlaneTree.mem_vertices_iff _ _).mpr (maxDegreeVertex_isVertex t),
    degreeAt_maxDegreeVertex t⟩

theorem flatten_split_at {α : Type*} (bs : List (List α)) {i : ℕ} (hi : i < bs.length) :
    bs.flatten = (bs.take i).flatten ++ bs[i] ++ (bs.drop (i + 1)).flatten := by
  conv_lhs => rw [← List.take_append_drop i bs, List.flatten_append,
    List.drop_eq_getElem_cons (by simpa using hi), List.flatten_cons]
  simp only [List.append_assoc]

theorem preorder_prefix_blocks_length (ts : List PlaneTree) (i : ℕ) :
    (((ts.mapIdx fun j s => s.vertices.map (j :: ·)).take i).flatten).length =
      (((ts.map PlaneTree.increments).take i).flatten).length := by
  simp only [List.length_flatten]
  congr 1
  apply List.ext_getElem (by simp)
  intro j hj hj'
  simp

theorem fringe_increments_split {t s : PlaneTree} {u : List ℕ}
    (h : t.fringe? u = some s) :
    ∃ a b : List ℤ, t.increments = a ++ s.increments ++ b ∧
      t.vertices[a.length]? = some u := by
  induction u generalizing t with
  | nil =>
    have ht : t = s := by simpa using h
    subst t
    refine ⟨[], [], by simp, ?_⟩
    cases s with | node ts => simp
  | cons i u ih =>
    cases hc : t.children[i]? with
    | none => simp [hc] at h
    | some r =>
      have hr : r.fringe? u = some s := by simpa [hc] using h
      obtain ⟨a, b, heq, hidx⟩ := ih hr
      obtain ⟨hi, hri⟩ := List.getElem?_eq_some_iff.mp hc
      let xs := t.children.map PlaneTree.increments
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
      refine ⟨((t.rootDegree : ℤ) - 1) :: ((xs.take i).flatten ++ a),
        b ++ (xs.drop (i + 1)).flatten, ?_, ?_⟩
      · conv_lhs => rw [← PlaneTree.node_children t, PlaneTree.increments_node]
        change (_ :: xs.flatten) = _
        rw [hx, heq]
        simp [List.append_assoc, PlaneTree.rootDegree]
      · conv_lhs => rw [← PlaneTree.node_children t, PlaneTree.vertices_node]
        change ([] :: vs.flatten)[_]? = _
        rw [List.length_cons, List.getElem?_cons_succ, hv, List.length_append]
        rw [← hlen]
        simp only [List.append_assoc, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
        have hia : a.length < r.vertices.length := by
          by_contra hh
          rw [List.getElem?_eq_none (by omega)] at hidx
          contradiction
        rw [List.getElem?_append_left (by simpa using hia), List.getElem?_map, hidx]
        rfl
theorem sum_take_forest_increments_gt (F : PlaneForest) {i : ℕ}
    (hi : i < (PlaneForest.increments F).length) :
    -(F.length : ℤ) < prefixSum (PlaneForest.increments F) i := by
  induction F generalizing i with
  | nil => simp [PlaneForest.increments] at hi
  | cons t F ih =>
    change i < (t.increments ++ PlaneForest.increments F).length at hi
    change -((F.length + 1 : ℕ) : ℤ) < (List.take i (t.increments ++ PlaneForest.increments F)).sum
    by_cases hit : i < t.increments.length
    · rw [List.take_append_of_le_length (Nat.le_of_lt hit)]
      have hp := t.sum_take_increments_nonneg hit
      simp only [Int.natCast_add, Int.natCast_one]
      omega
    · have hle : t.increments.length ≤ i := by omega
      have htail : i - t.increments.length < (PlaneForest.increments F).length := by
        simp only [List.length_append] at hi
        omega
      have hp := ih htail
      rw [List.take_append, List.take_of_length_le hle, List.sum_append, t.sum_increments]
      simp only [Int.natCast_add, Int.natCast_one]
      unfold prefixSum at hp
      omega

theorem firstHit_eq_some_iff (d : ℕ) (x : List ℤ) (n : ℕ) :
    firstHit? d x = some n ↔ n ≤ x.length ∧ prefixSum x n = -(d : ℤ) ∧
      ∀ j < n, prefixSum x j ≠ -(d : ℤ) := by
  simp only [firstHit?, List.find?_eq_some_iff_getElem, List.length_range,
    List.getElem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨hp, i, hi, heq, hprev⟩
    subst i
    exact ⟨by omega, hp, by simpa using hprev⟩
  · rintro ⟨hn, hp, hprev⟩
    exact ⟨hp, n, by omega, rfl, by simpa using hprev⟩

theorem firstHit_forest_increments_append (F : PlaneForest) (x : List ℤ) :
    firstHit? F.length (PlaneForest.increments F ++ x) = some F.size := by
  rw [firstHit_eq_some_iff]
  refine ⟨by simp, ?_, ?_⟩
  · rw [prefixSum, ← PlaneForest.length_increments F, List.take_left,
      PlaneForest.sum_increments]
  · intro j hj
    have hj' : j < (PlaneForest.increments F).length := by simpa using hj
    have hp := sum_take_forest_increments_gt F hj'
    rw [prefixSum, List.take_append_of_le_length (Nat.le_of_lt hj')]
    exact ne_of_gt hp

theorem prefixSum_reverse (x : List ℤ) (k : ℕ) :
    prefixSum x.reverse k = x.sum - prefixSum x (x.length - k) := by
  rw [prefixSum, List.take_reverse, List.sum_reverse]
  have h := List.sum_take_add_sum_drop x (x.length - k)
  unfold prefixSum
  omega

theorem lastZero_reverse_eq_of_firstHit {x : List ℤ} {d n : ℕ}
    (hsum : x.sum = -(d : ℤ)) (hhit : firstHit? d x = some n) :
    lastZero x.reverse = x.length - n := by
  obtain ⟨hn, hp, hprev⟩ := (firstHit_eq_some_iff d x n).mp hhit
  apply le_antisymm
  · apply Finset.sup_le
    intro k hk
    obtain ⟨hklen, hkzero⟩ := Finset.mem_filter.mp hk
    have hkl : k ≤ x.length := by simpa using (Finset.mem_range.mp hklen)
    rw [prefixSum_reverse, hsum] at hkzero
    have hkp : prefixSum x (x.length - k) = -(d : ℤ) := by omega
    have hge : n ≤ x.length - k := by
      by_contra h
      exact hprev _ (by omega) hkp
    change k ≤ x.length - n
    omega
  · apply Finset.le_sup (f := id)
    apply Finset.mem_filter.mpr
    constructor
    · simp only [List.length_reverse, Finset.mem_range]
      omega
    · rw [prefixSum_reverse, Nat.sub_sub_self hn, hp, hsum]
      omega

theorem prefixSum_append_of_le (x y : List ℤ) {k : ℕ} (hk : k ≤ x.length) :
    prefixSum (x ++ y) k = prefixSum x k := by
  exact congrArg List.sum (List.take_append_of_le_length hk)

theorem prefixSum_append_of_ge (x y : List ℤ) {k : ℕ} (hk : x.length ≤ k) :
    prefixSum (x ++ y) k = x.sum + prefixSum y (k - x.length) := by
  simp only [prefixSum, List.take_append, List.take_of_length_le hk, List.sum_append]

theorem weakRecordCount_append_of_negative (x y : List ℤ)
    (hy : ∀ k, 0 < k → k ≤ y.length → prefixSum y k < 0) :
    weakRecordCount (x ++ y) = weakRecordCount x := by
  unfold weakRecordCount
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range, List.length_append]
  by_cases hk : k ≤ x.length
  · have hbound : (k < x.length + y.length + 1) ↔ k < x.length + 1 := by omega
    rw [hbound]
    apply and_congr_right
    intro _
    apply and_congr_right
    intro _
    apply forall_congr'
    intro i
    apply imp_congr_right
    intro hi
    rw [prefixSum_append_of_le _ _ (by omega), prefixSum_append_of_le _ _ hk]
  · constructor
    · rintro ⟨hkl, hpos, hrec⟩
      have hc := hrec x.length (by omega)
      rw [prefixSum_append_of_le _ _ le_rfl, prefixSum, List.take_length,
        prefixSum_append_of_ge _ _ (by omega)] at hc
      have hn := hy (k - x.length) (by omega) (by omega)
      omega
    · rintro ⟨hkl, _⟩
      omega
theorem weakRecordCount_append_singleton (x : List ℤ) (a : ℤ)
    (ha : ∀ i ≤ x.length, prefixSum x i ≤ x.sum + a) :
    weakRecordCount (x ++ [a]) = weakRecordCount x + 1 := by
  have hprefix : ∀ k ≤ x.length, prefixSum (x ++ [a]) k = prefixSum x k :=
    fun k hk => prefixSum_append_of_le x [a] hk
  have hr : 0 < x.length + 1 ∧ ∀ i < x.length + 1,
      prefixSum (x ++ [a]) i ≤ prefixSum (x ++ [a]) (x.length + 1) := by
    refine ⟨by omega, ?_⟩
    intro i hi
    rw [hprefix i (by omega)]
    have hh : prefixSum (x ++ [a]) (x.length + 1) = x.sum + a := by
      simp [prefixSum, List.take_of_length_le]
    rw [hh]
    exact ha i (by omega)
  have hf : (Finset.range (x.length + 1)).filter (fun k =>
      0 < k ∧ ∀ i < k, prefixSum (x ++ [a]) i ≤ prefixSum (x ++ [a]) k) =
      (Finset.range (x.length + 1)).filter (fun k =>
      0 < k ∧ ∀ i < k, prefixSum x i ≤ prefixSum x k) := by
    apply Finset.filter_congr
    intro k hk
    have hk' : k ≤ x.length := by have := Finset.mem_range.mp hk; omega
    rw [hprefix k hk']
    apply and_congr_right
    intro _
    apply forall_congr'
    intro i
    apply imp_congr_right
    intro hi
    rw [hprefix i (by omega)]
  unfold weakRecordCount
  rw [List.length_append, List.length_singleton, Finset.range_add_one,
    Finset.filter_insert, ite_eq_left hr, Finset.card_insert_of_notMem]
  · rw [hf]
  · simp only [Finset.mem_filter, Finset.mem_range]
    omega

theorem prefixSum_reverse_forest_negative (F : BGW.PlaneForest) {k : ℕ}
    (hk : 0 < k) (hkl : k ≤ (BGW.PlaneForest.increments F).length) :
    prefixSum (BGW.PlaneForest.increments F).reverse k < 0 := by
  rw [prefixSum_reverse, BGW.PlaneForest.sum_increments]
  have hp := sum_take_forest_increments_gt F (i := (BGW.PlaneForest.increments F).length - k)
    (by omega)
  omega

theorem weakRecordCount_reverse_cons (a : ℤ) (x : List ℤ)
    (hx : ∀ k ≤ (a :: x).length, 0 ≤ prefixSum (a :: x) k) :
    weakRecordCount (a :: x).reverse = weakRecordCount x.reverse + 1 := by
  rw [List.reverse_cons]
  apply weakRecordCount_append_singleton
  intro i hi
  have hp : prefixSum (a :: x).reverse i ≤ (a :: x).sum := by
    rw [prefixSum_reverse]
    have hh := hx ((a :: x).length - i) (Nat.sub_le _ _)
    omega
  rw [List.reverse_cons, prefixSum_append_of_le _ _ hi] at hp
  simpa [List.sum_reverse, List.sum_cons, add_comm] using hp


end
end SubcriticalCauchy.Bienayme
