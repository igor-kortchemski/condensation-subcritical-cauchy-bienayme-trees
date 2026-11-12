module

public import SubcriticalCauchy.BienaymeSurvival
public import BGW.Tree.LocallyFinite

/-!
# Identification with finite-tree height

Height is the largest length of a vertex address, hence the largest graph
distance from the root. The finite-tree embedding preserves this height event.
This supplies the finite-tree interpretation of the survival probabilities.
-/

@[expose] public section

namespace SubcriticalCauchy.Bienayme

open BGW.LocallyFinite

/-- The maximal root-to-vertex distance in a finite rooted ordered tree. -/
def height (t : BGW.PlaneTree) : ℕ := t.vertices.toFinset.sup List.length

theorem not_extinctBy_toLocallyFinite_iff (t : BGW.PlaneTree) (n : ℕ) :
    t.toLocallyFinite ∉ extinctBy n ↔ ∃ u ∈ t.vertices, n ≤ u.length := by
  change (¬ ∀ u, Present t.toLocallyFinite u → u.length < n) ↔ _
  push Not
  constructor
  · rintro ⟨u, hu, hlen⟩
    obtain ⟨v, rfl⟩ := BGW.PlaneTree.exists_positiveAddress_of_present hu
    refine ⟨v, (BGW.PlaneTree.mem_vertices_iff t v).mpr
      ((BGW.PlaneTree.present_toLocallyFinite t v).mp hu), ?_⟩
    simpa [BGW.PlaneTree.positiveAddress] using hlen
  · rintro ⟨u, hu, hlen⟩
    refine ⟨BGW.PlaneTree.positiveAddress u,
      (BGW.PlaneTree.present_toLocallyFinite t u).mpr
        ((BGW.PlaneTree.mem_vertices_iff t u).mp hu), ?_⟩
    simpa [BGW.PlaneTree.positiveAddress] using hlen

/-- Survival through generation `n` is exactly finite-tree height at least `n`. -/
theorem toLocallyFinite_mem_survivalEvent_iff (t : BGW.PlaneTree) (n : ℕ) :
    t.toLocallyFinite ∈ survivalEvent n ↔ n ≤ height t := by
  rw [survivalEvent_eq_compl_extinctBy, Set.mem_compl_iff,
    not_extinctBy_toLocallyFinite_iff]
  by_cases hn : n = 0
  · subst n
    constructor
    · intro _; exact Nat.zero_le _
    · intro _
      exact ⟨[], (BGW.PlaneTree.mem_vertices_iff t []).mpr ⟨t, rfl⟩, by simp⟩
  · rw [height, Finset.le_sup_iff (Nat.pos_of_ne_zero hn)]
    simp only [List.mem_toFinset]

end SubcriticalCauchy.Bienayme
