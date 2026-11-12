module

public import SubcriticalCauchy.DegreeStatistics
public import SubcriticalCauchy.BienaymeBridgeStatistics


/-!
# Deleting the first maximum from an offspring word

The list erasure removes the first occurrence and preserves all other entries in
order. The increment conversion casts to integers before subtracting one.
Under the bridge endpoint constraint the deleted maximum count is minus the sum
of the remaining increments. This is deterministic input, not the one-big-jump
total-variation theorem.
-/

@[expose] public section

namespace SubcriticalCauchy.Bienayme

theorem listMaxDegree_mem {ds : List ℕ} (hne : ds ≠ []) : listMaxDegree ds ∈ ds := by
  have hs : ds.toFinset.Nonempty := by
    obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil ds hne
    exact ⟨d, List.mem_toFinset.mpr hd⟩
  obtain ⟨d, hd, heq⟩ := Finset.exists_mem_eq_sup ds.toFinset hs id
  change ds.toFinset.sup id ∈ ds
  rw [heq]
  exact List.mem_toFinset.mp hd

/-- Delete exactly the first occurrence of the maximum count. -/
def deleteMaxCounts (ds : List ℕ) : List ℕ := ds.erase (listMaxDegree ds)

theorem deleteMaxCounts_first {ds : List ℕ} (hne : ds ≠ []) :
    ∃ pre post : List ℕ, listMaxDegree ds ∉ pre ∧
      ds = pre ++ listMaxDegree ds :: post ∧ deleteMaxCounts ds = pre ++ post :=
  List.exists_erase_eq (listMaxDegree_mem hne)

theorem length_deleteMaxCounts {ds : List ℕ} (hne : ds ≠ []) :
    (deleteMaxCounts ds).length = ds.length - 1 :=
  List.length_erase_of_mem (listMaxDegree_mem hne)

theorem sum_deleteMaxCounts {ds : List ℕ} (hne : ds ≠ []) :
    listMaxDegree ds + (deleteMaxCounts ds).sum = ds.sum := by
  obtain ⟨pre, post, _, hds, herase⟩ := deleteMaxCounts_first hne
  have hsum := congrArg List.sum hds
  simp only [List.sum_append, List.sum_cons] at hsum
  rw [herase, List.sum_append]
  omega

/-- The remaining source increments, in their original relative order. -/
def deletedMaximumWord (ds : List ℕ) : List ℤ :=
  (deleteMaxCounts ds).map (fun d : ℕ => (d : ℤ) - 1)

/-- Count erasure is exactly first-maximum erasure on the valid increment word. -/
theorem deletedMaximumWord_eq_erase (ds : List ℕ) :
    deletedMaximumWord ds =
      (ds.map (fun d : ℕ => (d : ℤ) - 1)).erase ((listMaxDegree ds : ℤ) - 1) := by
  unfold deletedMaximumWord deleteMaxCounts
  apply List.map_erase (f := fun d : ℕ => (d : ℤ) - 1)
  intro a b hab
  change (a : ℤ) - 1 = (b : ℤ) - 1 at hab
  omega

theorem length_deletedMaximumWord {ds : List ℕ} (hne : ds ≠ []) :
    (deletedMaximumWord ds).length = ds.length - 1 := by
  simp only [deletedMaximumWord, List.length_map, length_deleteMaxCounts hne]

theorem sum_count_increments (ds : List ℕ) :
    (ds.map (fun d : ℕ => (d : ℤ) - 1)).sum = (ds.sum : ℤ) - (ds.length : ℤ) := by
  induction ds with
  | nil => simp
  | cons d ds ih => simp only [List.map_cons, List.sum_cons, List.length_cons,
      Nat.cast_add, Nat.cast_one, ih]; omega

/-- Exact maximum/remainder relation at the source's bridge endpoint `-1`. -/
theorem maxDegree_eq_neg_deleted_sum {ds : List ℕ} (hbridge : ds.sum + 1 = ds.length) :
    (listMaxDegree ds : ℤ) = -(deletedMaximumWord ds).sum := by
  have hne : ds ≠ [] := by intro hz; simp [hz] at hbridge
  have hsum := sum_deleteMaxCounts hne
  have hlen := length_deleteMaxCounts hne
  rw [deletedMaximumWord, sum_count_increments]
  omega

theorem maxDegree_tree_eq_neg_deleted_sum (t : BGW.PlaneTree) :
    (maxDegree t : ℤ) = -(deletedMaximumWord t.degrees).sum := by
  rw [maxDegree_eq_listMaxDegree]
  apply maxDegree_eq_neg_deleted_sum
  simpa only [BGW.PlaneTree.length_degrees] using BGW.PlaneTree.sum_degrees_add_one t

/-- Integer maximum with the lower increment endpoint as the empty convention. -/
def incrementMaximum (x : List ℤ) : ℤ := x.foldr max (-1)

theorem incrementMaximum_count_word (ds : List ℕ) :
    incrementMaximum (ds.map (fun d : ℕ => (d : ℤ) - 1)) = (listMaxDegree ds : ℤ) - 1 := by
  induction ds with
  | nil => simp [incrementMaximum, listMaxDegree]
  | cons d ds ih =>
    simp only [List.map_cons, incrementMaximum, List.foldr_cons] at ih ⊢
    rw [ih]
    simp only [listMaxDegree, List.toFinset_cons, Finset.sup_insert, id_eq]
    omega

theorem incrementMaximum_deleted_word (ds : List ℕ) :
    incrementMaximum (deletedMaximumWord ds) = (listSecondMaxDegree ds : ℤ) - 1 :=
  incrementMaximum_count_word (deleteMaxCounts ds)

end SubcriticalCauchy.Bienayme
