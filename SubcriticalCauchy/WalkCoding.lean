module

public import SubcriticalCauchy.ExplorationLaw
public import SubcriticalCauchy.BienaymeBridgeStatistics

import Mathlib.Tactic.Ring

/-!
# Łukasiewicz coding and the Vervaat transform

The finite Łukasiewicz excursion and bridge codings of a Bienaymé tree,
including the totalized decoders on arbitrary words.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace SubcriticalCauchy.Bienayme

noncomputable section

attribute [local instance] Classical.propDecidable

open BGW BGW.LocallyFinite

/-- Decode an integer increment word, with the one-vertex tree as the
totalization when parsing fails. -/
def decodeTree (xs : List ℤ) : Tree :=
  ((PlaneTree.ofIncrements? xs).getD PlaneTree.leaf).toLocallyFinite

/-- Offspring-count words whose Łukasiewicz path is a tree excursion. -/
def excursionWords (n : ℕ) : Set (Fin n → ℕ) :=
  {ω | IsTreeExcursion (stepWord ω)}

@[simp] theorem decodeTree_increments (t : PlaneTree) :
    decodeTree t.increments = t.toLocallyFinite := by
  simp [decodeTree]

theorem finiteVertices_decodeTree (xs : List ℤ) : FiniteVertices (decodeTree xs) :=
  PlaneTree.finiteVertices_toLocallyFinite _

theorem exists_tree_decode_of_isTreeExcursion {xs : List ℤ} (hx : IsTreeExcursion xs) :
    ∃ t : PlaneTree, t.increments = xs ∧ decodeTree xs = t.toLocallyFinite := by
  obtain ⟨t, ht, -⟩ := (PlaneTree.isTreeExcursion_iff_existsUnique xs).mp hx
  exact ⟨t, ht, by rw [← ht, decodeTree_increments]⟩

private theorem rotate_rotate_complement' {α : Type*} (l : List α) {i : ℕ}
    (hi : i < l.length) : (l.rotate i).rotate ((l.length - i) % l.length) = l := by
  rw [List.rotate_rotate]
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simp
  · rw [Nat.mod_eq_of_lt (by omega), show i + (l.length - i) = l.length by omega,
      List.rotate_length]

/-- The tree decoded from the unique excursion rotation of a bridge word.
On non-bridge words, and hence when no such rotation exists, the result is the
one-vertex tree. -/
def vervaatTree (n : ℕ) (ω : Fin n → ℕ) : Tree :=
  if h : ∃ i, i < n ∧ IsTreeExcursion ((stepWord ω).rotate i) then
    decodeTree ((stepWord ω).rotate (Nat.find h))
  else PlaneTree.leaf.toLocallyFinite

theorem finiteVertices_vervaatTree (n : ℕ) (ω : Fin n → ℕ) :
    FiniteVertices (vervaatTree n ω) := by
  by_cases h : ∃ i, i < n ∧ IsTreeExcursion ((stepWord ω).rotate i)
  · rw [vervaatTree, dite_eq_left h]
    exact finiteVertices_decodeTree _
  · rw [vervaatTree, dite_eq_right h]
    exact PlaneTree.finiteVertices_toLocallyFinite _

/-- Vervaat decoding undoes every cyclic shift of a finite tree code. -/
theorem vervaatTree_countsOfWord_rotated_increments {n : ℕ}
    (t : PlaneTree) (ht : t.size = n) (i : Fin n) :
    vervaatTree n (countsOfWord n (t.increments.rotate i)) = t.toLocallyFinite := by
  let x := t.increments.rotate (i : ℕ)
  have hstep : stepWord (countsOfWord n x) = x :=
    stepWord_countsOfWord_rotated_increments t ht i
  have hx : x ∈ bridgeWords n := by
    exact (PlaneTree.shiftEquiv n (⟨t, ht⟩, i)).2
  have hex : ∃ j, j < n ∧ IsTreeExcursion (x.rotate j) :=
    (exists_unique_rotate_isTreeExcursion hx).exists
  have hj := Nat.find_spec hex
  let k := (n - (i : ℕ)) % n
  have hk : k < n := Nat.mod_lt _ (Fin.pos i)
  have hi : (i : ℕ) < t.increments.length := by
    rw [PlaneTree.length_increments, ht]
    exact i.isLt
  have hcancel : x.rotate k = t.increments := by
    have h := rotate_rotate_complement' t.increments hi
    rw [PlaneTree.length_increments, ht] at h
    exact h
  have hjk : Nat.find hex = k :=
    (exists_unique_rotate_isTreeExcursion hx).unique hj ⟨hk, by
      rw [hcancel]
      exact PlaneTree.isTreeExcursion_increments t⟩
  change vervaatTree n (countsOfWord n x) = t.toLocallyFinite
  unfold vervaatTree
  rw [hstep, dite_eq_left hex, hjk, hcancel, decodeTree_increments]

/-- A measure on trees supported on finite trees is determined by its atoms
at the embedded finite plane trees. -/
private theorem measure_eq_of_finiteTree_atoms {ν η : Measure Tree}
    (hν : ν {T | FiniteVertices T}ᶜ = 0) (hη : η {T | FiniteVertices T}ᶜ = 0)
    (hatom : ∀ t : PlaneTree, ν {t.toLocallyFinite} = η {t.toLocallyFinite}) : ν = η := by
  ext A hA
  let F : Set Tree := {T | FiniteVertices T}
  have hF : MeasurableSet F := measurableSet_finiteVertices
  have hdecomp : A = (A ∩ F) ∪ (A ∩ Fᶜ) := by
    ext T
    by_cases hT : T ∈ F <;> simp_all
  have hdisj : Disjoint (A ∩ F) (A ∩ Fᶜ) := by
    apply Set.disjoint_left.mpr
    intro T hT hT'
    exact hT'.2 hT.2
  have hν' : ν (A ∩ Fᶜ) = 0 := measure_mono_null Set.inter_subset_right hν
  have hη' : η (A ∩ Fᶜ) = 0 := measure_mono_null Set.inter_subset_right hη
  rw [hdecomp, measure_union hdisj (hA.inter hF.compl),
    measure_union hdisj (hA.inter hF.compl), hν', hη']
  simp only [add_zero]
  have hAF : A ∩ F = ⋃ t : PlaneTree, A ∩ {t.toLocallyFinite} := by
    rw [show F = Set.range PlaneTree.toLocallyFinite from range_toLocallyFinite.symm,
      Set.range_eq_iUnion, Set.inter_iUnion]
  have hdisj' : Pairwise (fun s t : PlaneTree =>
      Disjoint (A ∩ {s.toLocallyFinite}) (A ∩ {t.toLocallyFinite})) := by
    intro s t hst
    exact (pairwise_disjoint_singleton_toLocallyFinite hst).mono
      Set.inter_subset_right Set.inter_subset_right
  rw [hAF, measure_iUnion hdisj' (fun t => hA.inter (measurableSet_singleton _)),
    measure_iUnion hdisj' (fun t => hA.inter (measurableSet_singleton _))]
  apply tsum_congr
  intro t
  by_cases ht : t.toLocallyFinite ∈ A
  · rw [Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr ht), hatom]
  · rw [Set.inter_singleton_eq_empty.mpr ht, measure_empty, measure_empty]

private theorem map_infiniteTrees_eq_zero {α : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] (ν : Measure α) (f : α → Tree)
    (hf : ∀ a, FiniteVertices (f a)) : ν.map f {T | FiniteVertices T}ᶜ = 0 := by
  rw [Measure.map_apply (measurable_of_countable _) measurableSet_finiteVertices.compl]
  have hempty : f ⁻¹' {T | FiniteVertices T}ᶜ = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro a ha
    exact ha (hf a)
  rw [hempty, measure_empty]

private theorem conditioned_infiniteTrees_eq_zero (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (n : ℕ) : conditioned μ n {T | FiniteVertices T}ᶜ = 0 := by
  rw [conditioned, cond_apply (measurableSet_sizeEvent n)]
  have hempty : sizeEvent n ∩ {T | FiniteVertices T}ᶜ = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro T hT
    exact hT.2 hT.1.1
  rw [hempty, measure_empty, mul_zero]

/-- Atoms of the decoded conditional excursion law. -/
theorem map_cond_excursionWords_singleton (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (n : ℕ) (t : PlaneTree) :
    ((Measure.pi fun _ : Fin n => μ)[|excursionWords n]).map
      (fun ω => decodeTree (stepWord ω)) {t.toLocallyFinite} =
      conditioned μ n {t.toLocallyFinite} := by
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
    cond_apply (Set.to_countable _).measurableSet]
  unfold conditioned
  have hmass : (Measure.pi fun _ : Fin n => μ) (excursionWords n) =
      bienaymeLaw μ (sizeEvent n) := pi_treeExcursion_eq_sizeEvent μ n
  by_cases ht : t.size = n
  · have hstep : stepWord (countsOfWord n t.increments) = t.increments := by
      apply stepWord_countsOfWord
      · simpa using ht
      · exact fun _ h => PlaneTree.neg_one_le_increment t h
    have hweight : (∏ i, μ {countsOfWord n t.increments i}) =
        PlaneTree.weight (fun d => μ {d}) t := by
      rw [← walkWeight_stepWord (fun d => μ {d}) (countsOfWord n t.increments),
        hstep, PlaneTree.walkWeight_increments]
    have hpre : excursionWords n ∩
        (fun ω => decodeTree (stepWord ω)) ⁻¹' {t.toLocallyFinite} =
        {countsOfWord n t.increments} := by
      ext ω
      constructor
      · intro hω
        obtain ⟨s, hs, hdecode⟩ := exists_tree_decode_of_isTreeExcursion hω.1
        have hst : s = t := PlaneTree.toLocallyFinite_injective
          (hdecode.symm.trans hω.2)
        subst s
        rw [Set.mem_singleton_iff, hs, countsOfWord_stepWord]
      · intro hω
        rw [Set.mem_singleton_iff] at hω
        subst ω
        refine ⟨?_, ?_⟩
        · change IsTreeExcursion (stepWord (countsOfWord n t.increments))
          rw [hstep]
          exact PlaneTree.isTreeExcursion_increments t
        · change decodeTree (stepWord (countsOfWord n t.increments)) = t.toLocallyFinite
          rw [hstep, decodeTree_increments]
    rw [hpre, Measure.pi_singleton, hmass, hweight,
      cond_sizeEvent_singleton, ite_eq_left ht, ENNReal.div_eq_inv_mul]
  · have hempty : excursionWords n ∩
        (fun ω => decodeTree (stepWord ω)) ⁻¹' {t.toLocallyFinite} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      obtain ⟨s, hs, hdecode⟩ := exists_tree_decode_of_isTreeExcursion hω.1
      have hst : s = t := PlaneTree.toLocallyFinite_injective
        (hdecode.symm.trans hω.2)
      apply ht
      rw [← hst, ← PlaneTree.length_increments, hs]
      simp [stepWord]
    rw [hempty, measure_empty, mul_zero, cond_sizeEvent_singleton, ite_eq_right ht]

/-- **Excursion conditioning.** Independent offspring counts conditioned to
form a finite Łukasiewicz excursion decode to the size-conditioned Bienaymé
law. No nonzero-size or admissibility hypothesis is needed. -/
theorem map_cond_excursionWords_decodeTree (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (n : ℕ) :
    ((Measure.pi fun _ : Fin n => μ)[|excursionWords n]).map
      (fun ω => decodeTree (stepWord ω)) = conditioned μ n := by
  apply measure_eq_of_finiteTree_atoms
  · exact map_infiniteTrees_eq_zero _ _ (fun ω => finiteVertices_decodeTree (stepWord ω))
  · exact conditioned_infiniteTrees_eq_zero μ n
  · exact map_cond_excursionWords_singleton μ n

/-- Atoms of the Vervaat transform of the conditional bridge law. -/
theorem map_cond_countBridges_vervaatTree_singleton (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (n : ℕ) (t : PlaneTree) :
    ((Measure.pi fun _ : Fin n => μ)[|countBridges n]).map (vervaatTree n)
      {t.toLocallyFinite} = conditioned μ n {t.toLocallyFinite} := by
  by_cases ht : t.size = n
  · rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
      cond_pi_countBridges_apply_eq_tsum, ENNReal.tsum_prod']
    rw [tsum_eq_single (⟨t, ht⟩ : {s : PlaneTree // s.size = n})]
    · have hn : n ≠ 0 := by
        rw [← ht]
        exact (PlaneTree.size_pos t).ne'
      let a : ℝ≥0∞ := conditioned μ n {t.toLocallyFinite}
      change (∑' _i : Fin n, (n : ℝ≥0∞)⁻¹ * a *
        Set.indicator (vervaatTree n ⁻¹' {t.toLocallyFinite}) 1
          (countsOfWord n (t.increments.rotate _))) = a
      simp only [Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff,
        vervaatTree_countsOfWord_rotated_increments t ht, ite_true, Pi.one_apply, mul_one]
      calc
        (∑' _i : Fin n, (n : ℝ≥0∞)⁻¹ * a) =
            (n : ℝ≥0∞) * ((n : ℝ≥0∞)⁻¹ * a) := by
          rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
        _ = a := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel (by exact_mod_cast hn)
            (ENNReal.natCast_ne_top n), one_mul]
    · intro s hs
      have hst : s.1 ≠ t := fun h => hs (Subtype.ext h)
      have hst' : s.1.toLocallyFinite ≠ t.toLocallyFinite :=
        fun h => hst (PlaneTree.toLocallyFinite_injective h)
      simp [vervaatTree_countsOfWord_rotated_increments s.1 s.2, hst']
  · rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
      cond_pi_countBridges_apply_eq_tsum]
    have hzero : ∀ q : {s : PlaneTree // s.size = n} × Fin n,
        (n : ℝ≥0∞)⁻¹ * (bienaymeLaw μ)[|sizeEvent n] {q.1.1.toLocallyFinite} *
          Set.indicator (vervaatTree n ⁻¹' {t.toLocallyFinite}) 1
            (countsOfWord n (q.1.1.increments.rotate q.2)) = 0 := by
      intro q
      have hne : q.1.1.toLocallyFinite ≠ t.toLocallyFinite := by
        intro h
        have hq := PlaneTree.toLocallyFinite_injective h
        apply ht
        rw [← hq, q.1.2]
      simp [vervaatTree_countsOfWord_rotated_increments q.1.1 q.1.2, hne]
    rw [tsum_congr hzero, tsum_zero]
    change 0 = (bienaymeLaw μ)[|sizeEvent n] {t.toLocallyFinite}
    rw [cond_sizeEvent_singleton, ite_eq_right ht]

/-- **Vervaat (bridge) conditioning.** The unique excursion rotation of the
Łukasiewicz bridge, decoded to a tree, has the size-conditioned Bienaymé law. -/
theorem map_cond_countBridges_vervaatTree (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (n : ℕ) :
    ((Measure.pi fun _ : Fin n => μ)[|countBridges n]).map (vervaatTree n) =
      conditioned μ n := by
  apply measure_eq_of_finiteTree_atoms
  · exact map_infiniteTrees_eq_zero _ _ (finiteVertices_vervaatTree n)
  · exact conditioned_infiniteTrees_eq_zero μ n
  · exact map_cond_countBridges_vervaatTree_singleton μ n

end
end SubcriticalCauchy.Bienayme
