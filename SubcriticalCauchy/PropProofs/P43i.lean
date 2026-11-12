module

public import SubcriticalCauchy.AttachedSlots
public import SubcriticalCauchy.FiniteTreeEvent
public import SubcriticalCauchy.MeasurableHypothesis
public import SubcriticalCauchy.AttachedForestHeight
public import SubcriticalCauchy.BienaymeForestHeight
public import Mathlib.MeasureTheory.Measure.TotalVariation.Defs
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

/-!
# Proof helpers for the frozen statement of Proposition 4.3(i) (`paper_height_lower`)

Owned helper module for one registered hole of
`SubcriticalCauchy.Propositions42_43`. It is imported by the frozen statement
file, which must not change except inside its holes; add the proof and any
further imports here.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section
open BGW BGW.LocallyFinite

attribute [local instance] Classical.propDecidable

private theorem measurableSet_finiteTreeEvent_p43i (P : PlaneTree → Prop) :
    MeasurableSet (finiteTreeEvent P) :=
  ((Set.to_countable {t : PlaneTree | P t}).image
    PlaneTree.toLocallyFinite).measurableSet

private theorem toLocallyFinite_mem_finiteTreeEvent_iff_p43i
    (P : PlaneTree → Prop) (t : PlaneTree) :
    t.toLocallyFinite ∈ finiteTreeEvent P ↔ P t := by
  constructor
  · rintro ⟨s, hs, hst⟩
    have hst' : s = t := PlaneTree.toLocallyFinite_injective hst
    simpa only [hst', Set.mem_ofPred_eq] using hs
  · intro ht
    exact ⟨t, ht, rfl⟩

/-- The finite-atom formula, summed over all plane trees rather than a size
subtype. Atoms of the wrong size vanish. -/
private theorem conditioned_apply_eq_tsum_plane (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (n : ℕ) (A : Set Tree) (hA : MeasurableSet A) :
    conditioned μ n A =
      ∑' t : PlaneTree, conditioned μ n {t.toLocallyFinite} *
        (if t.toLocallyFinite ∈ A then 1 else 0) := by
  classical
  let f (t : PlaneTree) : ℝ≥0∞ := conditioned μ n {t.toLocallyFinite} *
    (if t.toLocallyFinite ∈ A then 1 else 0)
  change conditioned μ n A = ∑' t : PlaneTree, f t
  change (bienaymeLaw μ (sizeEvent n))⁻¹ *
      (bienaymeLaw μ).restrict (sizeEvent n) A = _
  rw [restrict_sizeEvent_apply μ n A hA, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro t
  dsimp only [f]
  have hat : conditioned μ n {t.toLocallyFinite} =
      if t.size = n then
        PlaneTree.weight (fun k => μ {k}) t / bienaymeLaw μ (sizeEvent n) else 0 :=
    cond_sizeEvent_singleton μ n t
  rw [hat]
  by_cases ht : t.size = n
  · simp only [ht, ↓reduceIte, ENNReal.div_eq_inv_mul, mul_assoc]
  · simp only [ht, ↓reduceIte, zero_mul, mul_zero]

private theorem attachedSlotsLaw_apply_p43i (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (n k : ℕ) (B : Set (Fin k → Tree))
    (hB : MeasurableSet B) :
    attachedSlotsLaw μ n k B =
      ∑' t : PlaneTree, conditioned μ n {t.toLocallyFinite} *
        (if attachedSlotsTree k t ∈ B then 1 else 0) := by
  classical
  rw [attachedSlotsLaw, Measure.sum_apply _ hB]
  apply tsum_congr
  intro t
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hB,
    Set.indicator_apply, Pi.one_apply, mul_ite, mul_one, mul_zero]

private theorem attachedSlotsLaw_isProbability_p43i (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (n k : ℕ)
    (hn : bienaymeLaw μ (sizeEvent n) ≠ 0) :
    IsProbabilityMeasure (attachedSlotsLaw μ n k) := by
  let _ : IsProbabilityMeasure (conditioned μ n) := conditioned_isProbability μ n hn
  refine ⟨?_⟩
  rw [attachedSlotsLaw_apply_p43i μ n k Set.univ MeasurableSet.univ]
  simp only [Set.mem_univ, ↓reduceIte, mul_one]
  have hsum := (conditioned_apply_eq_tsum_plane μ n Set.univ MeasurableSet.univ).symm
  simp only [Set.mem_univ, ↓reduceIte, mul_one] at hsum
  exact hsum.trans measure_univ

private theorem abs_measureReal_sub_le_tvDist_p43i {α : Type*}
    [MeasurableSpace α] (P Q : Measure α) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (A : Set α) (hA : MeasurableSet A) :
    |P.real A - Q.real A| ≤ tvDist P Q := by
  have h := VectorMeasure.enorm_measure_le_variation
    (P.toSignedMeasure - Q.toSignedMeasure) A
  rw [Measure.toSignedMeasure_sub_apply hA] at h
  have h' : ‖P.real A - Q.real A‖ₑ ≤ etvDist P Q := by
    rw [etvDist_eq_etvDist_toSignedMeasure, VectorMeasure.etvDist]
    exact h.trans (measure_mono (Set.subset_univ A))
  have hr := ENNReal.toReal_mono (etvDist_ne_top P Q) h'
  simpa [tvDist, Real.norm_eq_abs] using hr

private theorem measureReal_le_add_tvDist_p43i {α : Type*}
    [MeasurableSpace α] (P Q : Measure α) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (A : Set α) (hA : MeasurableSet A) :
    P.real A ≤ Q.real A + tvDist P Q := by
  have h := (abs_le.mp (abs_measureReal_sub_le_tvDist_p43i P Q A hA)).2
  linarith

/-- If a finite tree is low, every attached slot is low. Absent slots are leaves
and therefore have height zero. -/
private theorem attachedSlotsTree_mem_forestBelowReal {k : ℕ} (t : PlaneTree)
    {a : ℝ} (ha : 0 < a) (ht : (height t : ℝ) < a) :
    attachedSlotsTree k t ∈ forestBelowReal k a := by
  change (fun i : Fin k =>
    (((attachedChild t (i.val + 1)).getD PlaneTree.leaf).toLocallyFinite)) ∈
      forestBelowReal k a
  rw [finite_forestBelowReal_iff]
  intro i
  generalize hchild : attachedChild t (i.val + 1) = child
  cases child with
  | none =>
      simp [height, ha]
  | some s =>
      have hs := attachedChild_height_add_le hchild
      simp only [Option.getD_some]
      exact lt_of_le_of_lt (by exact_mod_cast Nat.le_trans (Nat.le_add_left (height s)
        (maxDegreeDepth t + 1)) hs) ht

private theorem conditioned_height_lt_le_attachedSlotsLaw (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (n k : ℕ) {a : ℝ} (ha : 0 < a) :
    conditioned μ n (finiteTreeEvent fun t => (height t : ℝ) < a) ≤
      attachedSlotsLaw μ n k (forestBelowReal k a) := by
  classical
  rw [conditioned_apply_eq_tsum_plane μ n _ (measurableSet_finiteTreeEvent_p43i _),
    forestBelowReal, attachedSlotsLaw_apply_p43i μ n k _
      (measurableSet_forestBelow k ⌈a⌉₊)]
  apply ENNReal.tsum_le_tsum
  intro t
  by_cases ht : (height t : ℝ) < a
  · have hslots := attachedSlotsTree_mem_forestBelowReal (k := k) t ha ht
    change attachedSlotsTree k t ∈ forestBelow k ⌈a⌉₊ at hslots
    simp [toLocallyFinite_mem_finiteTreeEvent_iff_p43i, ht, hslots]
  · simp [toLocallyFinite_mem_finiteTreeEvent_iff_p43i, ht]

private theorem conditioned_height_ge_eq_compl (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (n : ℕ) (a : ℝ) :
    conditioned μ n (finiteTreeEvent fun t => a ≤ (height t : ℝ)) =
      conditioned μ n (finiteTreeEvent fun t => (height t : ℝ) < a)ᶜ := by
  classical
  rw [conditioned_apply_eq_tsum_plane μ n _ (measurableSet_finiteTreeEvent_p43i _),
    conditioned_apply_eq_tsum_plane μ n _
      (measurableSet_finiteTreeEvent_p43i _).compl]
  apply tsum_congr
  intro t
  by_cases ht : (height t : ℝ) < a
  · have hnot : ¬ a ≤ (height t : ℝ) := by linarith
    simp [toLocallyFinite_mem_finiteTreeEvent_iff_p43i, ht, hnot]
  · have hge : a ≤ (height t : ℝ) := by linarith
    simp [toLocallyFinite_mem_finiteTreeEvent_iff_p43i, ht, hge]

/-- Proposition 4.3(i), with the Proposition 4.2 comparison supplied as a
hypothesis so that this helper remains independent of the frozen statement file. -/
theorem height_lower_of_attached_tvDist (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (h : ℕ → ℝ)
    (hpos : ∀ n, 0 < h n) (hh : Tendsto h atTop atTop)
    (hQ : Tendsto (fun n : ℕ => (n : ℝ) * (survival μ ⌈h n⌉₊).toReal) atTop atTop)
    (hP42 : ∀ δ : ℝ, 0 ≤ δ → δ < 1 - (offspringMean μ).toReal →
      Tendsto (fun n : ℕ => tvDist (attachedSlotsLaw μ n ⌊δ * n⌋₊)
        (forestLaw μ ⌊δ * n⌋₊)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => conditioned μ n (finiteTreeEvent fun t => h n ≤ (height t : ℝ)))
      atTop (𝓝 1) := by
  have _ : Tendsto h atTop atTop := hh
  have hfin : offspringMean μ ≠ ∞ := ne_top_of_lt (hμ.1.trans ENNReal.one_lt_top)
  have hmreal : (offspringMean μ).toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hfin ENNReal.one_ne_top).mpr hμ.1
  have hm : 0 < 1 - (offspringMean μ).toReal := by linarith
  let δ : ℝ := (1 - (offspringMean μ).toReal) / 2
  have hδ : 0 < δ := div_pos hm (by norm_num)
  have hδ1 : δ < 1 - (offspringMean μ).toReal := by
    dsimp only [δ]
    linarith
  have hforest := forestBelowReal_floor_tendsto_zero μ h hδ hQ
  have htv := hP42 δ hδ.le hδ1
  have hbound : ∀ᶠ n in atTop,
      (conditioned μ n (finiteTreeEvent fun t => (height t : ℝ) < h n)).toReal ≤
        (forestLaw μ ⌊δ * n⌋₊ (forestBelowReal ⌊δ * n⌋₊ (h n))).toReal +
          tvDist (attachedSlotsLaw μ n ⌊δ * n⌋₊) (forestLaw μ ⌊δ * n⌋₊) := by
    filter_upwards [eventually_size_admissible μ hμ.to_literal] with n hn
    let _ : IsProbabilityMeasure (conditioned μ n) := conditioned_isProbability μ n hn
    let _ : IsProbabilityMeasure (attachedSlotsLaw μ n ⌊δ * n⌋₊) :=
      attachedSlotsLaw_isProbability_p43i μ n _ hn
    calc
      (conditioned μ n (finiteTreeEvent fun t => (height t : ℝ) < h n)).toReal ≤
          (attachedSlotsLaw μ n ⌊δ * n⌋₊
            (forestBelowReal ⌊δ * n⌋₊ (h n))).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _)
          (conditioned_height_lt_le_attachedSlotsLaw μ n _ (hpos n))
      _ ≤ _ := measureReal_le_add_tvDist_p43i _ _ _
        (measurableSet_forestBelow _ _)
  have hlow : Tendsto
      (fun n : ℕ => (conditioned μ n
        (finiteTreeEvent fun t => (height t : ℝ) < h n)).toReal) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hbound
    simpa using hforest.add htv
  have hreal : Tendsto
      (fun n : ℕ => (conditioned μ n
        (finiteTreeEvent fun t => h n ≤ (height t : ℝ))).toReal) atTop (𝓝 1) := by
    have hc := (tendsto_const_nhds (x := (1 : ℝ))).sub hlow
    simp only [sub_zero] at hc
    apply hc.congr'
    filter_upwards [eventually_size_admissible μ hμ.to_literal] with n hn
    let _ : IsProbabilityMeasure (conditioned μ n) := conditioned_isProbability μ n hn
    rw [conditioned_height_ge_eq_compl μ n (h n),
      measure_compl (measurableSet_finiteTreeEvent_p43i _) (measure_ne_top _ _),
      measure_univ, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
      ENNReal.toReal_one]
  have he := ENNReal.tendsto_ofReal hreal
  simp only [ENNReal.ofReal_one] at he
  apply he.congr'
  filter_upwards [eventually_size_admissible μ hμ.to_literal] with n hn
  let _ : IsProbabilityMeasure (conditioned μ n) := conditioned_isProbability μ n hn
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

end
end SubcriticalCauchy.Bienayme
