module

public import SubcriticalCauchy.WalkExplorationAux
public import SubcriticalCauchy.WalkRecords
public import SubcriticalCauchy.ExpectedProgeny
public import Mathlib.Data.Fin.Tuple.Take

/-! # Stopped offspring words and tree excursions

The first passage is the existing `walkFirstPassage`, whose value on nonhitting
paths is zero. Negative drift removes those paths almost surely.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section

/-- The walk reaches each negative level almost surely under subcriticality. -/
theorem iid_walk_hits_negative_level_ae (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ < 1) (d : ℕ) :
    ∀ᵐ ω ∂iidOffspringLaw μ, ∃ k, walkSum ω k = -(d : ℤ) := by
  have hfin := ne_top_of_lt (hm.trans ENNReal.one_lt_top)
  have hmR : (offspringMean μ).toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hfin ENNReal.one_ne_top).mpr hm
  filter_upwards [walkAverage_ae_tendsto μ hfin] with ω hω
  exact exists_walkSum_eq_of_negative_drift ω (sub_neg.mpr hmR) hω d

/-- Prefix sums of the finite offspring word are the actual infinite walk. -/
theorem prefixSum_stepWord_prefix (ω : ℕ → ℕ) {n k : ℕ} (hk : k ≤ n) :
    prefixSum (BGW.stepWord (fun i : Fin n => ω i)) k = walkSum ω k := by
  unfold prefixSum BGW.stepWord
  rw [← Fin.ofFn_take_eq_take_ofFn hk]
  simp only [Fin.take, List.sum_ofFn]
  exact (Finset.sum_range (n := k) (fun i : ℕ => (ω i : ℤ) - 1)).symm

/-- Before an attained first hit, every prefix is nonnegative. -/
theorem walkSum_nonneg_before_firstPassage (ω : ℕ → ℕ)
    {i : ℕ} (hi : i < walkFirstPassage ω 1) :
    0 ≤ walkSum ω i := by
  have hno (j : ℕ) (hj : j ≤ i) : walkSum ω j ≠ -1 := by
    intro he
    have := walkFirstPassage_le ω 1 j (by simpa using he)
    omega
  have hx : ∀ a ∈ BGW.stepWord (fun j : Fin i => ω j), -1 ≤ a := by
    intro a ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    omega
  have hp := (nonnegative_prefix_iff_no_hit_neg_one _ hx).mpr
    (fun j hj => by
      simp only [BGW.stepWord, List.length_ofFn] at hj
      rw [prefixSum_stepWord_prefix ω hj]
      exact hno j hj)
  simpa only [List.length_ofFn, prefixSum_stepWord_prefix ω le_rfl] using hp i (by simp [BGW.stepWord])

/-- The word stopped at an attained first hit is a tree excursion. -/
theorem isTreeExcursion_firstPassage (ω : ℕ → ℕ)
    (h : ∃ k, walkSum ω k = -1) :
    BGW.IsTreeExcursion
      (BGW.stepWord (fun i : Fin (walkFirstPassage ω 1) => ω i)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    omega
  · have hs := walkFirstPassage_spec ω 1 (by simpa using h)
    simpa [← finiteWalkSum_eq_stepWord_sum, finiteWalkSum_prefix] using hs
  · intro i hi
    have hi' : i < walkFirstPassage ω 1 := by simpa [BGW.stepWord] using hi
    change prefixSum _ i ≥ 0
    rw [prefixSum_stepWord_prefix ω hi'.le]
    exact walkSum_nonneg_before_firstPassage ω hi'

/-- The attained stopped word decodes uniquely, with size equal to passage time. -/
theorem existsUnique_tree_firstPassage (ω : ℕ → ℕ)
    (h : ∃ k, walkSum ω k = -1) :
    ∃! t : BGW.PlaneTree,
      t.increments = BGW.stepWord (fun i : Fin (walkFirstPassage ω 1) => ω i) :=
  (BGW.PlaneTree.isTreeExcursion_iff_existsUnique _).mp (isTreeExcursion_firstPassage ω h)

/-- Finite iid excursion words have exactly the tree-size mass. No drift
assumption is needed for this finite statement. -/
theorem pi_treeExcursion_eq_sizeEvent (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) :
    (Measure.pi (fun _ : Fin n => μ)) {ω | BGW.IsTreeExcursion (BGW.stepWord ω)} =
      BGW.LocallyFinite.bienaymeLaw μ (BGW.LocallyFinite.sizeEvent n) := by
  classical
  rw [BGW.LocallyFinite.bienaymeLaw_sizeEvent_eq_tsum_excursions]
  have hrange : Function.support
      (Set.indicator {x : List ℤ | BGW.IsTreeExcursion x ∧ x.length = n}
        (BGW.walkWeight fun d => μ {d})) ⊆ Set.range (BGW.stepWord (n := n)) := by
    intro x hx
    by_contra hn
    apply hx
    exact Set.indicator_of_notMem (fun h => hn (BGW.exists_stepWord_eq_of_entries h.2 h.1.1)) _
  rw [← BGW.stepWord_injective.tsum_eq hrange]
  rw [← Measure.tsum_indicator_apply_singleton (Measure.pi fun _ : Fin n => μ) _
    (Set.to_countable _).measurableSet]
  apply tsum_congr
  intro ω
  by_cases h : BGW.IsTreeExcursion (BGW.stepWord ω)
  · rw [Set.indicator_of_mem (s := {ω | BGW.IsTreeExcursion (BGW.stepWord ω)}) h, Set.indicator_of_mem (s := {x : List ℤ | BGW.IsTreeExcursion x ∧ x.length = n})
      (show BGW.IsTreeExcursion (BGW.stepWord ω) ∧ (BGW.stepWord ω).length = n from
        ⟨h, by simp [BGW.stepWord]⟩), Measure.pi_singleton, BGW.walkWeight_stepWord]
  · rw [Set.indicator_of_notMem (s := {ω | BGW.IsTreeExcursion (BGW.stepWord ω)}) h, Set.indicator_of_notMem (s := {x : List ℤ | BGW.IsTreeExcursion x ∧ x.length = n})
      (show ¬ (BGW.IsTreeExcursion (BGW.stepWord ω) ∧ (BGW.stepWord ω).length = n) from
        fun hx => h hx.1)]

/-- On hitting paths, specifying the first-passage time is the finite excursion
condition, including the empty-word boundary case. -/
theorem walkFirstPassage_eq_iff_treeExcursion (ω : ℕ → ℕ)
    (h : ∃ k, walkSum ω k = -1) (n : ℕ) :
    walkFirstPassage ω 1 = n ↔
      BGW.IsTreeExcursion (BGW.stepWord (fun i : Fin n => ω i)) := by
  constructor
  · rintro rfl
    exact isTreeExcursion_firstPassage ω h
  · intro hx
    have hn : walkSum ω n = -1 := by
      simpa only [← finiteWalkSum_eq_stepWord_sum, finiteWalkSum_prefix] using hx.2.1
    apply le_antisymm (walkFirstPassage_le ω 1 n (by simpa using hn))
    by_contra hlt
    have ht : walkFirstPassage ω 1 < n := by omega
    have hp := hx.2.2 (walkFirstPassage ω 1) (by simpa [BGW.stepWord] using ht)
    change 0 ≤ prefixSum _ _ at hp
    rw [prefixSum_stepWord_prefix ω ht.le, walkFirstPassage_spec ω 1 (by simpa using h)] at hp
    norm_num at hp

/-- The first hitting time has the tree-size distribution under the actual
infinite iid law. The zero totalization has mass zero under subcriticality. -/
theorem iid_walkFirstPassage_eq_sizeEvent (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ < 1) (n : ℕ) :
    iidOffspringLaw μ {ω | walkFirstPassage ω 1 = n} =
      BGW.LocallyFinite.bienaymeLaw μ (BGW.LocallyFinite.sizeEvent n) := by
  calc
    _ = iidOffspringLaw μ
        {ω | BGW.IsTreeExcursion (BGW.stepWord (fun i : Fin n => ω i))} := by
      apply measure_congr
      filter_upwards [iid_walk_hits_negative_level_ae μ hm 1] with ω hω
      exact propext (walkFirstPassage_eq_iff_treeExcursion ω (by simpa using hω) n)
    _ = (Measure.pi (fun _ : Fin n => μ))
        {ω | BGW.IsTreeExcursion (BGW.stepWord ω)} :=
      iidOffspringLaw_prefix_event μ n {ω | BGW.IsTreeExcursion (BGW.stepWord ω)}
    _ = _ := pi_treeExcursion_eq_sizeEvent μ n

/-- The discrete layer-cake identity for an arbitrary measurable natural-valued
random variable. This keeps the `k = 0` term in the tail sum. -/
theorem lintegral_nat_eq_tsum_tail {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (X : Ω → ℕ) (hX : Measurable X) :
    (∫⁻ ω, (X ω : ℝ≥0∞) ∂ν) = ∑' k : ℕ, ν {ω | k < X ω} := by
  classical
  have hpoint (ω : Ω) : (X ω : ℝ≥0∞) =
      ∑' k : ℕ, {ω | k < X ω}.indicator (fun _ => (1 : ℝ≥0∞)) ω := by
    rw [tsum_eq_sum (s := Finset.range (X ω))]
    · calc
        (X ω : ℝ≥0∞) = ∑ _k ∈ Finset.range (X ω), (1 : ℝ≥0∞) := by simp
        _ = _ := Finset.sum_congr rfl fun k hk =>
          (Set.indicator_of_mem (s := {ω | k < X ω}) (Finset.mem_range.mp hk) (fun _ => (1 : ℝ≥0∞))).symm
    · intro k hk
      exact Set.indicator_of_notMem (by simpa using hk) _
  simp_rw [hpoint]
  rw [lintegral_tsum]
  · apply tsum_congr
    intro k
    exact lintegral_indicator_one (measurableSet_lt measurable_const hX)
  · intro k
    exact (measurable_const.indicator (measurableSet_lt measurable_const hX)).aemeasurable

/-- Atom expansion for a measurable natural-valued random variable. -/
theorem lintegral_nat_eq_tsum_atoms {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (X : Ω → ℕ) (hX : Measurable X) :
    (∫⁻ ω, (X ω : ℝ≥0∞) ∂ν) = ∑' n : ℕ, (n : ℝ≥0∞) * ν {ω | X ω = n} := by
  classical
  have hpoint (ω : Ω) : (X ω : ℝ≥0∞) =
      ∑' n : ℕ, {ω | X ω = n}.indicator (fun _ => (n : ℝ≥0∞)) ω := by
    rw [tsum_eq_single (X ω)]
    · simp
    · intro n hn
      exact Set.indicator_of_notMem (by simpa [eq_comm] using hn) _
  simp_rw [hpoint]
  rw [lintegral_tsum]
  · apply tsum_congr
    intro n
    rw [lintegral_indicator (measurableSet_eq_fun hX measurable_const)]
    simp
  · intro n
    exact (measurable_const.indicator (measurableSet_eq_fun hX measurable_const)).aemeasurable

/-- Generation-based expected progeny, expressed through the finite size atoms. -/
theorem lintegral_totalProgeny_eq_tsum_sizeEvent (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (hm : offspringMean μ < 1) :
    (∫⁻ T, totalProgeny T ∂BGW.LocallyFinite.bienaymeLaw μ) =
      ∑' n : ℕ, (n : ℝ≥0∞) *
        BGW.LocallyFinite.bienaymeLaw μ (BGW.LocallyFinite.sizeEvent n) := by
  classical
  calc
    _ = ∫⁻ T, ∑' n : ℕ, (BGW.LocallyFinite.sizeEvent n).indicator
        (fun _ => (n : ℝ≥0∞)) T ∂BGW.LocallyFinite.bienaymeLaw μ := by
      apply lintegral_congr_ae
      filter_upwards [ae_finite_of_subcritical μ hm] with T hT
      rw [totalProgeny_eq_ncard T hT, tsum_eq_single {u | BGW.LocallyFinite.Present T u}.ncard]
      · simp [BGW.LocallyFinite.sizeEvent, hT]
      · intro n hn
        exact Set.indicator_of_notMem (fun hx => hn hx.2.symm) _
    _ = _ := by
      rw [lintegral_tsum]
      · apply tsum_congr
        intro n
        rw [lintegral_indicator (BGW.LocallyFinite.measurableSet_sizeEvent n)]
        simp
      · intro n
        exact (measurable_const.indicator (BGW.LocallyFinite.measurableSet_sizeEvent n)).aemeasurable

/-- Expected first hitting time of `-1`, with exactly the paper's real mean. -/
theorem lintegral_iid_walkFirstPassage_one (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ < 1) :
    (∫⁻ ω, (walkFirstPassage ω 1 : ℝ≥0∞) ∂iidOffspringLaw μ) =
      ENNReal.ofReal (1 / (1 - (offspringMean μ).toReal)) := by
  rw [lintegral_nat_eq_tsum_atoms _ _ (measurable_walkFirstPassage 1)]
  simp_rw [iid_walkFirstPassage_eq_sizeEvent μ hm]
  rw [← lintegral_totalProgeny_eq_tsum_sizeEvent μ hm,
    lintegral_totalProgeny_subcritical μ hm]

/-- The survival tail sum of the first hit, including time zero. -/
theorem tsum_iid_walkFirstPassage_one_tail (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ < 1) :
    (∑' k : ℕ, iidOffspringLaw μ {ω | k < walkFirstPassage ω 1}) =
      ENNReal.ofReal (1 / (1 - (offspringMean μ).toReal)) := by
  rw [← lintegral_nat_eq_tsum_tail _ _ (measurable_walkFirstPassage 1)]
  exact lintegral_iid_walkFirstPassage_one μ hm

/-- Full equality of the first-passage and total-progeny distributions,
expressed on arbitrary subsets of the extended nonnegative reals. -/
theorem iid_walkFirstPassage_mem_eq_totalProgeny (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ < 1) (A : Set ℝ≥0∞) :
    iidOffspringLaw μ {ω | (walkFirstPassage ω 1 : ℝ≥0∞) ∈ A} =
      BGW.LocallyFinite.bienaymeLaw μ {T | totalProgeny T ∈ A} := by
  let I := {n : ℕ // (n : ℝ≥0∞) ∈ A}
  have hx : {ω : ℕ → ℕ | (walkFirstPassage ω 1 : ℝ≥0∞) ∈ A} =
      ⋃ n : I, {ω | walkFirstPassage ω 1 = n.val} := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨⟨walkFirstPassage ω 1, h⟩, rfl⟩
    · rintro ⟨n, hn⟩
      rw [hn]
      exact n.property
  have hy : {T | totalProgeny T ∈ A} =ᵐ[BGW.LocallyFinite.bienaymeLaw μ]
      ⋃ n : I, BGW.LocallyFinite.sizeEvent n.val := by
    filter_upwards [ae_finite_of_subcritical μ hm] with T hT
    apply propext
    simp only [Set.mem_iUnion]
    constructor
    · intro h
      rw [totalProgeny_eq_ncard T hT] at h
      exact ⟨⟨{u | BGW.LocallyFinite.Present T u}.ncard, h⟩, hT, rfl⟩
    · rintro ⟨n, hn⟩
      rw [totalProgeny_eq_ncard T hT, hn.2]
      exact n.property
  have hdX : Pairwise (fun n m : I => Disjoint
      {ω : ℕ → ℕ | walkFirstPassage ω 1 = n.val}
      {ω : ℕ → ℕ | walkFirstPassage ω 1 = m.val}) := by
    intro n m hnm
    apply Set.disjoint_left.mpr
    intro ω hn hm'
    exact hnm (Subtype.ext (hn.symm.trans hm'))
  have hdY : Pairwise (fun n m : I => Disjoint
      (BGW.LocallyFinite.sizeEvent n.val) (BGW.LocallyFinite.sizeEvent m.val)) := by
    intro n m hnm
    apply Set.disjoint_left.mpr
    intro T hn hm'
    exact hnm (Subtype.ext (hn.2.symm.trans hm'.2))
  rw [hx, measure_congr hy, measure_iUnion hdX
    (fun _ => measurableSet_eq_fun (measurable_walkFirstPassage 1) measurable_const),
    measure_iUnion hdY (fun n => BGW.LocallyFinite.measurableSet_sizeEvent n.val)]
  exact tsum_congr fun n => iid_walkFirstPassage_eq_sizeEvent μ hm n.val

end
end SubcriticalCauchy.Bienayme
