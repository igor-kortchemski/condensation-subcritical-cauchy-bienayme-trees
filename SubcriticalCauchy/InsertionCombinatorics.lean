module

public import SubcriticalCauchy.DeletedIncrements
public import Mathlib.Data.List.InsertIdx
public import Mathlib.Data.List.GetD

/-!
# Insertion of a strict maximum in a finite count vector

These deterministic lemmas identify first-maximum deletion with removal of an
inserted entry which strictly exceeds every residual entry.
-/

@[expose] public section

namespace SubcriticalCauchy.Bienayme

/-- `Fin.insertNth` is list insertion after conversion with `List.ofFn`. -/
theorem List.ofFn_insertNth {m : ℕ} (i : Fin (m + 1)) (r : ℕ) (z : Fin m → ℕ) :
    List.ofFn (Fin.insertNth i r z) = (List.ofFn z).insertIdx i r := by
  induction m with
  | zero =>
      have hi : i = 0 := Fin.eq_zero i
      subst i
      simp
  | succ m ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · obtain ⟨a, z, rfl⟩ := Fin.exists_cons z
        rw [Fin.insertNth_succ_cons]
        simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
        simpa only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_succ,
          List.insertIdx_succ_cons] using congrArg (List.cons a) (ih j z)

theorem listMaxDegree_le_of_forall {ds : List ℕ} {r : ℕ} (h : ∀ d ∈ ds, d ≤ r) :
    listMaxDegree ds ≤ r := by
  apply Finset.sup_le
  intro d hd
  exact h d (List.mem_toFinset.mp hd)

/-- An entry strictly larger than every residual entry is the maximum after
insertion. -/
theorem listMaxDegree_insertNth {m : ℕ} (i : Fin (m + 1)) (r : ℕ) (z : Fin m → ℕ)
    (hr : ∀ j, z j < r) :
    listMaxDegree (List.ofFn (Fin.insertNth i r z)) = r := by
  apply le_antisymm
  · apply listMaxDegree_le_of_forall
    intro d hd
    rw [List.ofFn_insertNth] at hd
    rcases List.eq_or_mem_of_mem_insertIdx hd with rfl | hd
    · exact le_rfl
    · obtain ⟨j, _, rfl⟩ := List.mem_ofFn.mp hd
      exact (hr j).le
  · apply Finset.le_sup (f := id)
    apply List.mem_toFinset.mpr
    rw [List.ofFn_insertNth]
    apply (List.mem_insertIdx (Nat.le_of_lt_succ (by simpa using i.isLt))).mpr
    exact Or.inl rfl

/-- Erasing the strict maximum after insertion recovers the residual vector. -/
theorem deleteMaxCounts_insertNth {m : ℕ} (i : Fin (m + 1)) (r : ℕ) (z : Fin m → ℕ)
    (hr : ∀ j, z j < r) :
    deleteMaxCounts (List.ofFn (Fin.insertNth i r z)) = List.ofFn z := by
  rw [deleteMaxCounts, listMaxDegree_insertNth i r z hr]
  rw [List.ofFn_insertNth]
  induction m with
  | zero =>
      have hi : i = 0 := Fin.eq_zero i
      subst i
      simp
  | succ m ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · obtain ⟨a, z, rfl⟩ := Fin.exists_cons z
        have ha : a ≠ r := ne_of_lt (hr 0)
        simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
        have hih := ih j z (fun k => hr k.succ)
        simpa [ha] using congrArg (List.cons a) hih

/-- First-maximum deletion of a strict-maximum insertion returns precisely the
residual increment vector. -/
theorem deletedIncrements_insertNth {m : ℕ} (i : Fin (m + 1)) (r : ℕ) (z : Fin m → ℕ)
    (hr : ∀ j, z j < r) :
    deletedIncrements (m + 1) (Fin.insertNth i r z) = fun j => (z j : ℤ) - 1 := by
  funext j
  have hj : (j : ℕ) < m := by simp
  simp only [deletedIncrements, deletedMaximumWord,
    deleteMaxCounts_insertNth i r z hr, List.map_ofFn]
  rw [List.getD_eq_getElem (l := List.ofFn ((fun d : ℕ => (d : ℤ) - 1) ∘ z))
    (n := (j : ℕ)) (d := 0) (by simp)]
  simp

/-- The insertion position is determined by the inserted strict maximum and
the residual vector. -/
theorem insertNth_injective_left_of_lt {m : ℕ} (r : ℕ) (z : Fin m → ℕ)
    (hr : ∀ j, z j < r) :
    Function.Injective (fun i : Fin (m + 1) => Fin.insertNth i r z) := by
  intro i j hij
  by_contra hne
  obtain ⟨k, rfl⟩ := (Fin.eq_self_or_eq_succAbove i j).resolve_left (fun h => hne h.symm)
  have h := congrFun hij (i.succAbove k)
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove] at h
  exact (ne_of_gt (hr k)) h.symm

/-- Inserting at the length of a prefix is the same as appending the entry
between that prefix and the suffix. -/
theorem List.insertIdx_length_append (pre post : List ℕ) (r : ℕ) :
    (pre ++ post).insertIdx pre.length r = pre ++ r :: post := by
  induction pre with
  | nil => simp
  | cons a pre ih => simp [ih]

/-- Every vector with a prescribed deleted residual increment word is obtained
by inserting its first maximum at some position. -/
theorem exists_insertNth_of_deletedIncrements {m : ℕ} (ω : Fin (m + 1) → ℕ) (z : Fin m → ℕ)
    (hres : deletedIncrements (m + 1) ω = fun j => (z j : ℤ) - 1) :
    ∃ i : Fin (m + 1), ω = Fin.insertNth i (listMaxDegree (List.ofFn ω)) z := by
  have hne : List.ofFn ω ≠ [] := by simp
  obtain ⟨pre, post, _, hword, hdelete⟩ := deleteMaxCounts_first hne
  have hlen : (deletedMaximumWord (List.ofFn ω)).length = m := by
    rw [length_deletedMaximumWord hne]
    simp
  have hdelList : deletedMaximumWord (List.ofFn ω) =
      List.ofFn (fun j => (z j : ℤ) - 1) := by
    apply List.ext_getElem (hlen.trans (by simp))
    intro k hk₁ hk₂
    have hk : k < m := hlen ▸ hk₁
    have h := congrFun hres ⟨k, hk⟩
    simpa only [deletedIncrements, Nat.add_sub_cancel, List.getD_eq_getElem _ _ hk₁,
      List.getD_eq_getElem _ _ hk₂, List.getElem_ofFn] using h
  have hinc : Function.Injective (fun d : ℕ => (d : ℤ) - 1) := by
    intro a b hab
    change (a : ℤ) - 1 = (b : ℤ) - 1 at hab
    omega
  have hmaps : (pre ++ post).map (fun d : ℕ => (d : ℤ) - 1) =
      (List.ofFn z).map (fun d : ℕ => (d : ℤ) - 1) := by
    calc
      _ = deletedMaximumWord (List.ofFn ω) := by rw [deletedMaximumWord, hdelete]
      _ = List.ofFn (fun j => (z j : ℤ) - 1) := hdelList
      _ = _ := by simp only [List.map_ofFn, Function.comp_def]
  have hresidual : pre ++ post = List.ofFn z := hinc.list_map hmaps
  have hlength : pre.length + 1 + post.length = m + 1 := by
    have h := congrArg List.length hword
    simp only [List.length_ofFn, List.length_append, List.length_cons] at h
    omega
  have hi : pre.length < m + 1 := by omega
  refine ⟨⟨pre.length, hi⟩, ?_⟩
  apply List.ofFn_injective
  rw [List.ofFn_insertNth, ← hresidual, List.insertIdx_length_append]
  exact hword

/-- Equality of residual increment vectors is equivalent, after applying the
injective map on lists, to equality of the deleted count lists. -/
theorem deleteMaxCounts_eq_ofFn_of_deletedIncrements {m : ℕ} (ω : Fin (m + 1) → ℕ)
    (z : Fin m → ℕ)
    (hres : deletedIncrements (m + 1) ω = fun j => (z j : ℤ) - 1) :
    deleteMaxCounts (List.ofFn ω) = List.ofFn z := by
  have hne : List.ofFn ω ≠ [] := by simp
  have hlen : (deletedMaximumWord (List.ofFn ω)).length = m := by
    rw [length_deletedMaximumWord hne]
    simp
  have hdelList : deletedMaximumWord (List.ofFn ω) =
      List.ofFn (fun j => (z j : ℤ) - 1) := by
    apply List.ext_getElem (hlen.trans (by simp))
    intro k hk₁ hk₂
    have hk : k < m := hlen ▸ hk₁
    have h := congrFun hres ⟨k, hk⟩
    simpa only [deletedIncrements, Nat.add_sub_cancel, List.getD_eq_getElem _ _ hk₁,
      List.getD_eq_getElem _ _ hk₂, List.getElem_ofFn] using h
  have hinc : Function.Injective (fun d : ℕ => (d : ℤ) - 1) := by
    intro a b hab
    change (a : ℤ) - 1 = (b : ℤ) - 1 at hab
    omega
  apply hinc.list_map
  calc
    _ = deletedMaximumWord (List.ofFn ω) := rfl
    _ = List.ofFn (fun j => (z j : ℤ) - 1) := hdelList
    _ = _ := by simp only [List.map_ofFn, Function.comp_def]

end SubcriticalCauchy.Bienayme
