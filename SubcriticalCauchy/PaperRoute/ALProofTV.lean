module

public import Mathlib.MeasureTheory.Measure.TotalVariation.Defs

/-! A setwise bound controls total variation. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace SubcriticalCauchy.ArmendarizLoulakis

noncomputable section

/-- If every measurable set has measure difference at most `η` in absolute value,
then the Mathlib total-variation distance is at most `2η`.  Finite equal-mass
measures are allowed; the equal-mass hypothesis is used only through its real form. -/
theorem al_tvDist_le_of_forall_set {α : Type*} [MeasurableSpace α]
    (Q R : Measure α) [IsFiniteMeasure Q] [IsFiniteMeasure R] (η : ℝ)
    (hQR : ∀ s : Set α, MeasurableSet s → |Q.real s - R.real s| ≤ η) :
    tvDist Q R ≤ 2 * η := by
  classical
  rw [tvDist_eq_iSup_finPartition_abs]
  refine ciSup_le fun P => ?_
  let V : SignedMeasure α := Q.toSignedMeasure - R.toSignedMeasure
  have hV (s : Set α) (hs : MeasurableSet s) : V s = Q.real s - R.real s := by
    simp only [V, Measure.toSignedMeasure_sub_apply hs, Measure.real]
  have hdisj : (P.parts : Set (Subtype (MeasurableSet (α := α)))).PairwiseDisjoint
      (fun p => (p : Set α)) := by
    intro a ha b hb hab
    simpa [disjoint_iff, Subtype.ext_iff] using P.disjoint ha hb hab
  have hsum (s : Finset (Subtype (MeasurableSet (α := α)))) (hs : s ⊆ P.parts) :
      V (⋃ p ∈ s, (p : Set α)) = ∑ p ∈ s, V p := by
    apply V.of_biUnion_finset
    · exact hdisj.subset (by simpa using hs)
    · exact fun p _ => p.property
  let pos : Finset (Subtype (MeasurableSet (α := α))) :=
    P.parts.filter fun p => 0 ≤ V (p : Set α)
  let neg : Finset (Subtype (MeasurableSet (α := α))) :=
    P.parts.filter fun p => ¬0 ≤ V (p : Set α)
  have hpos : (∑ p ∈ pos, |Q.real (p : Set α) - R.real (p : Set α)|) =
      V (⋃ p ∈ pos, (p : Set α)) := by
    calc
      _ = ∑ p ∈ pos, V p := by
        apply Finset.sum_congr rfl
        intro p hp
        have hp' : 0 ≤ V p := (Finset.mem_filter.mp hp).2
        rw [← hV (p : Set α) p.property, abs_of_nonneg hp']
      _ = _ := (hsum pos (Finset.filter_subset _ _)).symm
  have hneg : (∑ p ∈ neg, |Q.real (p : Set α) - R.real (p : Set α)|) =
      -V (⋃ p ∈ neg, (p : Set α)) := by
    calc
      _ = ∑ p ∈ neg, -V p := by
        apply Finset.sum_congr rfl
        intro p hp
        have hp' : V p < 0 := lt_of_not_ge (Finset.mem_filter.mp hp).2
        rw [← hV (p : Set α) p.property, abs_of_neg hp']
      _ = -(∑ p ∈ neg, V p) := by rw [Finset.sum_neg_distrib]
      _ = _ := by rw [← hsum neg (Finset.filter_subset _ _)]
  have hpos_bound : V (⋃ p ∈ pos, (p : Set α)) ≤ η := by
    have hm : MeasurableSet (⋃ p ∈ pos, (p : Set α)) :=
      Finset.measurableSet_biUnion _ fun p _ => p.property
    exact (le_abs_self _).trans (by simpa [hV _ hm] using hQR _ hm)
  have hneg_bound : -V (⋃ p ∈ neg, (p : Set α)) ≤ η := by
    have hm : MeasurableSet (⋃ p ∈ neg, (p : Set α)) :=
      Finset.measurableSet_biUnion _ fun p _ => p.property
    exact (neg_le_abs _).trans (by simpa [hV _ hm] using hQR _ hm)
  rw [← Finset.sum_filter_add_sum_filter_not P.parts (fun p => 0 ≤ V p)]
  change (∑ p ∈ pos, |Q.real (p : Set α) - R.real (p : Set α)|) +
      (∑ p ∈ neg, |Q.real (p : Set α) - R.real (p : Set α)|) ≤ 2 * η
  rw [hpos, hneg]
  linarith

/-- Specialization to probability measures. -/
theorem al_tvDist_le_of_forall_set_prob {α : Type*} [MeasurableSpace α]
    (Q R : Measure α) [IsProbabilityMeasure Q] [IsProbabilityMeasure R] (η : ℝ)
    (hQR : ∀ s : Set α, MeasurableSet s → |Q.real s - R.real s| ≤ η) :
    tvDist Q R ≤ 2 * η :=
  al_tvDist_le_of_forall_set Q R η hQR

end
end SubcriticalCauchy.ArmendarizLoulakis
