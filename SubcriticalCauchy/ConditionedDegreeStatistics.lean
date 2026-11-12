module

public import SubcriticalCauchy.DegreeStatistics
public import SubcriticalCauchy.BienaymeBridgeStatistics

/-!
# Exact degree-statistic laws under size conditioning

These specialize the rotation/permutation-invariant bridge law to the largest
and second-largest degrees, separately and jointly. All events use the actual
size-conditioned Bienaymé law; no value is assigned on infinite trees.
The asymptotic one-big-jump comparison is not part of these identities.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace SubcriticalCauchy.Bienayme

noncomputable section
open BGW BGW.LocallyFinite

/-- Finite trees whose two leading degrees lie in a prescribed set. -/
def finiteDegreePairEvent (A : Set (ℕ × ℕ)) : Set Tree :=
  PlaneTree.toLocallyFinite '' {t | (maxDegree t, secondMaxDegree t) ∈ A}

theorem finiteDegreePairEvent_eq (A : Set (ℕ × ℕ)) :
    finiteDegreePairEvent A = finiteDegreeEvent
      (fun ds => (listMaxDegree ds, listSecondMaxDegree ds) ∈ A) := by
  simp only [finiteDegreePairEvent, finiteDegreeEvent, maxDegree_eq_listMaxDegree,
    secondMaxDegree]

theorem measurableSet_finiteDegreePairEvent (A : Set (ℕ × ℕ)) :
    MeasurableSet (finiteDegreePairEvent A) := by
  rw [finiteDegreePairEvent_eq]
  exact measurableSet_finiteDegreeEvent _

theorem conditioned_degree_pair_event (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : n ≠ 0) (A : Set (ℕ × ℕ)) :
    conditioned μ n (finiteDegreePairEvent A) =
      (Measure.pi fun _ : Fin n => μ)[|countBridges n]
        {ω | (listMaxDegree (List.ofFn ω), listSecondMaxDegree (List.ofFn ω)) ∈ A} := by
  rw [finiteDegreePairEvent_eq]
  apply (bridge_degree_permutation_event μ hn _ _).symm
  intro ds es hperm
  rw [listMaxDegree_perm hperm, listSecondMaxDegree_perm hperm]

/-- Largest-degree event law, with the same offspring counts as the bridge. -/
theorem conditioned_maxDegree_event (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : n ≠ 0) (A : Set ℕ) :
    conditioned μ n (PlaneTree.toLocallyFinite '' {t | maxDegree t ∈ A}) =
      (Measure.pi fun _ : Fin n => μ)[|countBridges n]
        {ω | listMaxDegree (List.ofFn ω) ∈ A} := by
  have h := conditioned_degree_pair_event μ hn (Prod.fst ⁻¹' A)
  simpa only [finiteDegreePairEvent, Set.mem_preimage, Prod.fst] using h

/-- Second-largest-degree event law. Tied maxima retain their multiplicity. -/
theorem conditioned_secondMaxDegree_event (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : n ≠ 0) (A : Set ℕ) :
    conditioned μ n (PlaneTree.toLocallyFinite '' {t | secondMaxDegree t ∈ A}) =
      (Measure.pi fun _ : Fin n => μ)[|countBridges n]
        {ω | listSecondMaxDegree (List.ofFn ω) ∈ A} := by
  have h := conditioned_degree_pair_event μ hn (Prod.snd ⁻¹' A)
  simpa only [finiteDegreePairEvent, Set.mem_preimage, Prod.snd] using h

end
end SubcriticalCauchy.Bienayme
