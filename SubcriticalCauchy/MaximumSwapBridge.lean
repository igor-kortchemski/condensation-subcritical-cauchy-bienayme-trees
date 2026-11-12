module

public import SubcriticalCauchy.DeleteMaximum
public import Mathlib.Data.List.Rotate

set_option autoImplicit false

/-!
Deterministic bridge between ordered first-maximum deletion and
swapping the first maximum with the last coordinate. No law invariance or
one-big-jump conclusion is asserted here.
-/

@[expose] public section

namespace SubcriticalCauchy.Bienayme.MaximumSwapBridge

section Generic

variable {α : Type*} [DecidableEq α]

/-- Keep the first matching entry fixed and change only its strict suffix. -/
def mapAfterFirst (a : α) (f : List α → List α) : List α → List α
  | [] => []
  | x :: xs => if x = a then x :: f xs else x :: mapAfterFirst a f xs

theorem mapAfterFirst_append {a : α} {pre : List α} (f : List α → List α)
    (post : List α) (hpre : a ∉ pre) :
    mapAfterFirst a f (pre ++ a :: post) = pre ++ a :: f post := by
  induction pre with
  | nil => simp [mapAfterFirst]
  | cons x pre ih =>
    have hxa : x ≠ a := by intro h; subst x; exact hpre (by simp)
    have hp : a ∉ pre := fun h => hpre (by simp [h])
    simp only [List.cons_append, mapAfterFirst, ite_eq_right hxa]
    exact congrArg (List.cons x) (ih hp)

theorem mapAfterFirst_left_inv (a : α) (e : List α ≃ List α) (xs : List α) :
    mapAfterFirst a e.symm (mapAfterFirst a e xs) = xs := by
  induction xs with
  | nil => simp [mapAfterFirst]
  | cons x xs ih =>
    by_cases hxa : x = a
    · simp [mapAfterFirst, hxa]
    · simp [mapAfterFirst, hxa, ih]

theorem mapAfterFirst_perm (a : α) (f : List α → List α)
    (hf : ∀ xs, (f xs).Perm xs) (xs : List α) : (mapAfterFirst a f xs).Perm xs := by
  induction xs with
  | nil => simp [mapAfterFirst]
  | cons x xs ih =>
    by_cases hxa : x = a
    · simpa only [mapAfterFirst, ite_eq_left hxa] using (hf xs).cons x
    · simpa only [mapAfterFirst, ite_eq_right hxa] using ih.cons x

theorem mapAfterFirst_idxOf (a : α) (f : List α → List α) (xs : List α) :
    (mapAfterFirst a f xs).idxOf a = xs.idxOf a := by
  induction xs with
  | nil => simp [mapAfterFirst]
  | cons x xs ih =>
    by_cases hxa : x = a
    · subst x
      simp [mapAfterFirst]
    · simp only [mapAfterFirst, ite_eq_right hxa, List.idxOf_cons_ne _ hxa, ih]

/-- Left rotation by one, with inverse right rotation by one. -/
def rotateOneEquiv : List α ≃ List α where
  toFun xs := xs.rotate 1
  invFun xs := xs.rotate (xs.length - 1)
  left_inv xs := by
    by_cases hx : xs = []
    · subst xs; simp
    · have hn : 1 + (xs.length - 1) = xs.length := by
        have hp := List.length_pos_iff.mpr hx
        omega
      simp only [List.length_rotate, List.rotate_rotate, hn, List.rotate_length]
  right_inv xs := by
    by_cases hx : xs = []
    · subst xs; simp
    · have hn : xs.length - 1 + 1 = xs.length := by
        have hp := List.length_pos_iff.mpr hx
        omega
      simp only [List.rotate_rotate, hn, List.rotate_length]

/-- Swap a head entry with the final entry of its suffix; a singleton is fixed. -/
def swapHeadLast (a : α) (post : List α) : List α :=
  match post.reverse with
  | [] => [a]
  | z :: zs => z :: (zs.reverse ++ [a])

omit [DecidableEq α] in
theorem swapHeadLast_append (a z : α) (mid : List α) :
    swapHeadLast a (mid ++ [z]) = z :: (mid ++ [a]) := by
  simp [swapHeadLast]

omit [DecidableEq α] in
theorem swapHeadLast_rotate (a : α) (post : List α) :
    swapHeadLast a (post.rotate 1) = post ++ [a] := by
  cases post with
  | nil => simp [swapHeadLast]
  | cons z zs => simp [swapHeadLast]

/-- Find the first matching entry and swap it with the last list entry. -/
def swapFirstLast (a : α) : List α → List α
  | [] => []
  | x :: xs => if x = a then swapHeadLast x xs else x :: swapFirstLast a xs

theorem swapFirstLast_append {a : α} {pre : List α} (post : List α)
    (hpre : a ∉ pre) :
    swapFirstLast a (pre ++ a :: post) = pre ++ swapHeadLast a post := by
  induction pre with
  | nil => simp [swapFirstLast]
  | cons x pre ih =>
    have hxa : x ≠ a := by intro h; subst x; exact hpre (by simp)
    have hp : a ∉ pre := fun h => hpre (by simp [h])
    simp only [List.cons_append, swapFirstLast, ite_eq_right hxa]
    exact congrArg (List.cons x) (ih hp)

end Generic

/-- Rotate precisely the suffix strictly after the first maximum. -/
def rotateAfterFirstMax (ds : List ℕ) : List ℕ :=
  mapAfterFirst (listMaxDegree ds) rotateOneEquiv ds

def unrotateAfterFirstMax (ds : List ℕ) : List ℕ :=
  mapAfterFirst (listMaxDegree ds) rotateOneEquiv.symm ds

theorem rotateAfterFirstMax_perm (ds : List ℕ) : (rotateAfterFirstMax ds).Perm ds :=
  mapAfterFirst_perm _ _ (fun xs => List.rotate_perm xs 1) ds

theorem unrotateAfterFirstMax_perm (ds : List ℕ) : (unrotateAfterFirstMax ds).Perm ds :=
  mapAfterFirst_perm _ _ (fun xs => List.rotate_perm xs (xs.length - 1)) ds

theorem rotateAfterFirstMax_max (ds : List ℕ) :
    listMaxDegree (rotateAfterFirstMax ds) = listMaxDegree ds :=
  listMaxDegree_perm (rotateAfterFirstMax_perm ds)

theorem unrotateAfterFirstMax_max (ds : List ℕ) :
    listMaxDegree (unrotateAfterFirstMax ds) = listMaxDegree ds :=
  listMaxDegree_perm (unrotateAfterFirstMax_perm ds)

theorem rotateAfterFirstMax_length (ds : List ℕ) :
    (rotateAfterFirstMax ds).length = ds.length := (rotateAfterFirstMax_perm ds).length_eq

theorem rotateAfterFirstMax_idxOf (ds : List ℕ) :
    (rotateAfterFirstMax ds).idxOf (listMaxDegree (rotateAfterFirstMax ds)) =
      ds.idxOf (listMaxDegree ds) := by
  rw [rotateAfterFirstMax_max]
  exact mapAfterFirst_idxOf _ _ ds

theorem unrotate_rotateAfterFirstMax (ds : List ℕ) :
    unrotateAfterFirstMax (rotateAfterFirstMax ds) = ds := by
  unfold unrotateAfterFirstMax
  rw [rotateAfterFirstMax_max]
  exact mapAfterFirst_left_inv _ rotateOneEquiv ds

theorem rotate_unrotateAfterFirstMax (ds : List ℕ) :
    rotateAfterFirstMax (unrotateAfterFirstMax ds) = ds := by
  unfold rotateAfterFirstMax
  rw [unrotateAfterFirstMax_max]
  exact mapAfterFirst_left_inv _ rotateOneEquiv.symm ds

def maximumSuffixRotationEquiv : List ℕ ≃ List ℕ where
  toFun := rotateAfterFirstMax
  invFun := unrotateAfterFirstMax
  left_inv := unrotate_rotateAfterFirstMax
  right_inv := rotate_unrotateAfterFirstMax

/-- The genuine first-maximum/last-coordinate swap used by Armendáriz–Loulakis. -/
def swapFirstMaxToLast (ds : List ℕ) : List ℕ := swapFirstLast (listMaxDegree ds) ds

/-- Swapping after the suffix rotation is exactly ordered deletion followed by
the maximum, including tied maxima and a maximum already at the final position. -/
theorem swap_rotate_eq_delete_append {ds : List ℕ} (hne : ds ≠ []) :
    swapFirstMaxToLast (rotateAfterFirstMax ds) = deleteMaxCounts ds ++ [listMaxDegree ds] := by
  obtain ⟨pre, post, hpre, hds, hdel⟩ := deleteMaxCounts_first hne
  let m := listMaxDegree ds
  change m ∉ pre at hpre
  change ds = pre ++ m :: post at hds
  have hrot : rotateAfterFirstMax ds = pre ++ m :: post.rotate 1 := by
    change mapAfterFirst m (fun xs => xs.rotate 1) ds = _
    rw [hds, mapAfterFirst_append _ _ hpre]
  calc
    swapFirstMaxToLast (rotateAfterFirstMax ds) =
        swapFirstLast m (rotateAfterFirstMax ds) := by
      rw [swapFirstMaxToLast, rotateAfterFirstMax_max]
    _ = pre ++ post ++ [m] := by
      rw [hrot, swapFirstLast_append _ hpre, swapHeadLast_rotate]
      simp only [List.append_assoc]
    _ = deleteMaxCounts ds ++ [listMaxDegree ds] := by rw [hdel]

theorem take_swap_rotate_eq_delete {ds : List ℕ} (hne : ds ≠ []) :
    (swapFirstMaxToLast (rotateAfterFirstMax ds)).take (ds.length - 1) = deleteMaxCounts ds := by
  rw [swap_rotate_eq_delete_append hne, ← length_deleteMaxCounts hne]
  exact List.take_left

end SubcriticalCauchy.Bienayme.MaximumSwapBridge
