module

public import SubcriticalCauchy.InsertionCombinatorics

/-!
# Atom of the deleted-maximum law on strict-maximum residual vectors

On residual vectors whose missing count is a strict maximum, the preimages of
first-maximum deletion are precisely the insertions of that missing count.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SubcriticalCauchy.Bienayme

noncomputable section

/-- Atoms of the iid increment law. -/
theorem pi_incrementLaw_atom (μ : Measure ℕ) [IsProbabilityMeasure μ] {k : ℕ}
    (z : Fin k → ℕ) :
    (Measure.pi fun _ : Fin k => incrementLaw μ) {fun i => (z i : ℤ) - 1} =
      ∏ i, μ {z i} := by
  let _ : IsProbabilityMeasure (incrementLaw μ) := by
    unfold incrementLaw
    infer_instance
  have hatom (a : ℕ) : incrementLaw μ {(a : ℤ) - 1} = μ {a} := by
    rw [incrementLaw, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
    congr 1
    ext b
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    omega
  rw [Measure.pi_singleton]
  apply Finset.prod_congr rfl
  intro i _
  exact hatom (z i)

/-- The strict-maximum insertion vectors are exactly the bridge preimages of a
given residual increment vector. -/
theorem deletedIncrements_succ_preimage {m : ℕ} (z : Fin m → ℕ) (r : ℕ)
    (hr : ∀ j, z j < r) (hrsum : r + ∑ j, z j = m) :
    BGW.countBridges (m + 1) ∩
        deletedIncrements (m + 1) ⁻¹' {fun j => (z j : ℤ) - 1} =
      Set.range (fun i : Fin (m + 1) => Fin.insertNth i r z) := by
  ext ω
  constructor
  · rintro ⟨hbridge, hdel⟩
    have hne : List.ofFn ω ≠ [] := by simp
    have hmax : listMaxDegree (List.ofFn ω) = r := by
      have hsum := sum_deleteMaxCounts hne
      rw [deleteMaxCounts_eq_ofFn_of_deletedIncrements ω z hdel] at hsum
      simp only [List.sum_ofFn] at hsum
      change (∑ i, ω i) + 1 = m + 1 at hbridge
      omega
    obtain ⟨i, hi⟩ := exists_insertNth_of_deletedIncrements ω z hdel
    refine ⟨i, ?_⟩
    rw [← hmax]
    exact hi.symm
  · rintro ⟨i, rfl⟩
    constructor
    · change (∑ j, Fin.insertNth i r z j) + 1 = m + 1
      rw [Fin.sum_insertNth]
      omega
    · exact deletedIncrements_insertNth i r z hr

/-- The size-`m + 1` form of the insertion density. -/
theorem deletedIncrements_succ_law_atom (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {m : ℕ} (z : Fin m → ℕ) (hz : ∑ i, z i < m)
    (hmax : ∀ i, z i < m - ∑ i, z i) :
    ((MaximumSwapLaw.bridgeCountsLaw μ (m + 1)).map (deletedIncrements (m + 1)))
        {fun i => (z i : ℤ) - 1} =
      ((m + 1 : ℕ) : ℝ≥0∞) * μ {m - ∑ i, z i} * (∏ i, μ {z i}) /
        Measure.pi (fun _ : Fin (m + 1) => μ) (BGW.countBridges (m + 1)) := by
  let r := m - ∑ i, z i
  have hrsum : r + ∑ i, z i = m := by
    dsimp [r]
    omega
  have hpre := deletedIncrements_succ_preimage z r hmax hrsum
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  rw [MaximumSwapLaw.bridgeCountsLaw,
    cond_apply (Set.to_countable (BGW.countBridges (m + 1))).measurableSet, hpre,
    BGW.pi_eq_tsum_indicator μ (Set.range (fun i : Fin (m + 1) => Fin.insertNth i r z))]
  have hinj := insertNth_injective_left_of_lt r z hmax
  have hweight (i : Fin (m + 1)) :
      (∏ j, μ {Fin.insertNth (α := fun _ => ℕ) i r z j}) = μ {r} * ∏ j, μ {z j} := by
    rw [← Fin.prod_insertNth (M := ℝ≥0∞) i (μ {r}) (fun j => μ {z j})]
    apply Finset.prod_congr rfl
    intro j _
    refine Fin.succAboveCases i ?_ (fun k => ?_) j <;> simp
  have hrange : Function.support
      (Set.indicator (Set.range (fun i : Fin (m + 1) => Fin.insertNth i r z))
        (fun ω => ∏ j, μ {ω j})) ⊆
      Set.range (fun i : Fin (m + 1) => Fin.insertNth i r z) := by
    intro ω hω
    by_contra hnot
    exact hω (Set.indicator_of_notMem hnot _)
  rw [← hinj.tsum_eq hrange]
  simp
  simp only [hweight, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ENNReal.div_eq_inv_mul]
  dsimp [r]
  simp only [Nat.cast_add, Nat.cast_one]
  ring

/-- Insertion density: on residual vectors whose missing count is a strict
maximum, the deleted-maximum law has an explicit density. -/
theorem deletedIncrements_law_atom (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {n : ℕ} (z : Fin (n - 1) → ℕ) (hz : ∑ i, z i < n - 1)
    (hmax : ∀ i, z i < n - 1 - ∑ i, z i) :
    ((MaximumSwapLaw.bridgeCountsLaw μ n).map (deletedIncrements n))
        {fun i => (z i : ℤ) - 1} =
      (n : ℝ≥0∞) * μ {n - 1 - ∑ i, z i} * (∏ i, μ {z i}) /
        Measure.pi (fun _ : Fin n => μ) (BGW.countBridges n) := by
  cases n with
  | zero => simp at hz
  | succ m =>
      simp only [Nat.add_sub_cancel] at *
      exact deletedIncrements_succ_law_atom μ z hz hmax

end
end SubcriticalCauchy.Bienayme
