module

public import SubcriticalCauchy.CyclicResidual
public import SubcriticalCauchy.DeletedMaximumDensity

/-!
# Deterministic and finite-mass helpers for deletion with its position

A strict maximum inserted at a specified position is the unique bridge preimage
of the corresponding positioned residual word.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace SubcriticalCauchy.Bienayme

noncomputable section

/-- Insertion of a strict maximum records its insertion position as the first
maximum index. -/
theorem firstMaxIndex_insertNth {m : ℕ} (i : Fin (m + 1)) (r : ℕ) (z : Fin m → ℕ)
    (hr : ∀ j, z j < r) :
    firstMaxIndex (List.ofFn (Fin.insertNth i r z)) = (i : ℕ) := by
  rw [firstMaxIndex, listMaxDegree_insertNth i r z hr, List.ofFn_insertNth]
  induction m with
  | zero =>
      have hi : i = 0 := Fin.eq_zero i
      subst i
      simp
  | succ m ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · obtain ⟨a, z, rfl⟩ := Fin.exists_cons z
        simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_succ,
          List.insertIdx_succ_cons]
        change List.idxOf r (a :: (List.ofFn z).insertIdx (j : ℕ) r) = (j : ℕ) + 1
        have ha : a ≠ r := ne_of_lt (hr 0)
        rw [List.idxOf_cons_ne (a := r) (b := a) _ ha]
        exact congrArg Nat.succ (ih j z (fun k => hr k.succ))

/-- The positioned strict-maximum residual has exactly one bridge preimage. -/
theorem deletionWithPosition_succ_preimage {m : ℕ} (i : Fin (m + 1))
    (z : Fin m → ℕ) (r : ℕ) (hr : ∀ j, z j < r)
    (hrsum : r + ∑ j, z j = m) :
    BGW.countBridges (m + 1) ∩
        deletionWithPosition (m + 1) ⁻¹' {((i : ℕ), fun j => (z j : ℤ) - 1)} =
      {Fin.insertNth i r z} := by
  ext ω
  constructor
  · rintro ⟨hbridge, hpos⟩
    have hdel : deletedIncrements (m + 1) ω = fun j => (z j : ℤ) - 1 :=
      (congrArg Prod.snd hpos)
    have hpre := deletedIncrements_succ_preimage z r hr hrsum
    have hmem : ω ∈ Set.range (fun j : Fin (m + 1) => Fin.insertNth j r z) := by
      rw [← hpre]
      exact ⟨hbridge, hdel⟩
    obtain ⟨j, rfl⟩ := hmem
    have hij : j = i := by
      apply Fin.ext
      have hj := congrArg Prod.fst hpos
      change firstMaxIndex (List.ofFn (Fin.insertNth j r z)) = (i : ℕ) at hj
      rw [firstMaxIndex_insertNth j r z hr] at hj
      exact hj
    subst j
    simp
  · intro hω
    rw [Set.mem_singleton_iff] at hω
    subst ω
    have hpre := deletedIncrements_succ_preimage z r hr hrsum
    have hbasic : Fin.insertNth i r z ∈ BGW.countBridges (m + 1) ∩
        deletedIncrements (m + 1) ⁻¹' {fun j => (z j : ℤ) - 1} := by
      rw [hpre]
      exact ⟨i, rfl⟩
    refine ⟨hbasic.1, ?_⟩
    apply Prod.ext
    · exact firstMaxIndex_insertNth i r z hr
    · exact hbasic.2

/-- The uniform insertion law gives each allowed position mass `1 / n`. -/
theorem uniformInsertionPosition_succ_atom {m : ℕ} (i : Fin (m + 1)) :
    uniformInsertionPosition (m + 1) {(i : ℕ)} = ((m + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
  simp only [uniformInsertionPosition, Measure.smul_apply, Measure.coe_finsetSum,
    Finset.sum_apply, Measure.dirac_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Ne.symm (Fin.val_ne_iff.mpr hji)]
  · simp

/-- The uniform insertion law is a probability measure in positive length. -/
theorem uniformInsertionPosition_succ_isProbability (m : ℕ) :
    IsProbabilityMeasure (uniformInsertionPosition (m + 1)) := by
  constructor
  simp only [uniformInsertionPosition, Measure.smul_apply, Measure.coe_finsetSum,
    Finset.sum_apply, Measure.dirac_apply, Set.mem_univ, Set.indicator_of_mem,
    Pi.one_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    smul_eq_mul]
  simpa using ENNReal.inv_mul_cancel (a := ((m + 1 : ℕ) : ℝ≥0∞)) (by simp) (by simp)

end
end SubcriticalCauchy.Bienayme
