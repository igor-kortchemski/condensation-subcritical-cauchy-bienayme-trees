module

public import SubcriticalCauchy.MaxDegree
public import Mathlib.Data.List.Rotate
public import Mathlib.Data.Finset.Dedup

/-!
# Largest and second-largest degree statistics

The second largest degree removes exactly one maximum, retaining multiplicity
at a tied maximum. Empty and singleton lists have second value zero. Both
statistics are invariant under permutations, hence under cyclic rotation.
-/

@[expose] public section

namespace SubcriticalCauchy.Bienayme

/-- Largest natural count in a word, with value zero for an empty word. -/
def listMaxDegree (ds : List ℕ) : ℕ := ds.toFinset.sup id

/-- Second largest count, retaining multiplicities. A missing second entry has
value zero. -/
def listSecondMaxDegree (ds : List ℕ) : ℕ := listMaxDegree (ds.erase (listMaxDegree ds))

theorem listMaxDegree_perm {ds es : List ℕ} (h : ds.Perm es) :
    listMaxDegree ds = listMaxDegree es := by
  unfold listMaxDegree
  rw [List.toFinset_eq_of_perm _ _ h]

theorem listSecondMaxDegree_perm {ds es : List ℕ} (h : ds.Perm es) :
    listSecondMaxDegree ds = listSecondMaxDegree es := by
  unfold listSecondMaxDegree
  rw [listMaxDegree_perm h]
  exact listMaxDegree_perm (h.erase _)

theorem listMaxDegree_rotate (ds : List ℕ) (i : ℕ) :
    listMaxDegree (ds.rotate i) = listMaxDegree ds :=
  listMaxDegree_perm (List.rotate_perm ds i)

theorem listSecondMaxDegree_rotate (ds : List ℕ) (i : ℕ) :
    listSecondMaxDegree (ds.rotate i) = listSecondMaxDegree ds :=
  listSecondMaxDegree_perm (List.rotate_perm ds i)

theorem listSecondMaxDegree_le (ds : List ℕ) : listSecondMaxDegree ds ≤ listMaxDegree ds := by
  unfold listSecondMaxDegree listMaxDegree
  apply Finset.sup_le
  intro d hd
  exact Finset.le_sup (f := id) (List.mem_toFinset.mpr
    (List.mem_of_mem_erase (List.mem_toFinset.mp hd)))

@[simp] theorem listSecondMaxDegree_nil : listSecondMaxDegree [] = 0 := by
  simp [listSecondMaxDegree, listMaxDegree]

@[simp] theorem listSecondMaxDegree_singleton (d : ℕ) : listSecondMaxDegree [d] = 0 := by
  simp [listSecondMaxDegree, listMaxDegree]

theorem listSecondMaxDegree_eq_zero_of_length_le_one {ds : List ℕ} (h : ds.length ≤ 1) :
    listSecondMaxDegree ds = 0 := by
  cases ds with
  | nil => exact listSecondMaxDegree_nil
  | cons d ds =>
    cases ds with
    | nil => exact listSecondMaxDegree_singleton d
    | cons e es => simp at h

/-- The second largest tree outdegree; multiplicity is preserved at ties. -/
def secondMaxDegree (t : BGW.PlaneTree) : ℕ := listSecondMaxDegree t.degrees

theorem maxDegree_eq_listMaxDegree (t : BGW.PlaneTree) :
    maxDegree t = listMaxDegree t.degrees := maxDegree_eq_degrees_sup t

theorem secondMaxDegree_le_maxDegree (t : BGW.PlaneTree) : secondMaxDegree t ≤ maxDegree t := by
  rw [maxDegree_eq_listMaxDegree]
  exact listSecondMaxDegree_le t.degrees

end SubcriticalCauchy.Bienayme
