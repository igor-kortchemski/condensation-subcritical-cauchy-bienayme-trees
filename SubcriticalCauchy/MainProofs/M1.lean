module

public import SubcriticalCauchy.ConditionedDegreeStatistics
public import SubcriticalCauchy.Theorem31
public import SubcriticalCauchy.DeletedMaximumDensity
public import SubcriticalCauchy.TotalVariationTypical
public import SubcriticalCauchy.OffspringWalk

/-!
# Proof helpers for the frozen statement M1

Owned helper module for the registered hole of M1. It is imported by the
frozen statement file, which must not change except inside its holes; add
the proof and any further imports here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators

namespace SubcriticalCauchy.Bienayme

noncomputable section
open BGW BGW.LocallyFinite

/-- Event probabilities differ by at most the total variation distance. -/
theorem abs_measureReal_sub_le_tvDist {α : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] (P Q : Measure α) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (A : Set α) :
    |P.real A - Q.real A| ≤ tvDist P Q := by
  rw [tvDist_eq_tsum_abs]
  have hP : Summable fun z => P.real {z} := by
    apply ENNReal.summable_toReal
    rw [show (∑' z, P {z}) = 1 by
      simpa using P.tsum_indicator_apply_singleton Set.univ MeasurableSet.univ]
    simp
  have hQ : Summable fun z => Q.real {z} := by
    apply ENNReal.summable_toReal
    rw [show (∑' z, Q {z}) = 1 by
      simpa using Q.tsum_indicator_apply_singleton Set.univ MeasurableSet.univ]
    simp
  have hdiff : P.real A - Q.real A =
      ∑' z, A.indicator (fun z => P.real {z} - Q.real {z}) z := by
    rw [← tsum_indicator_measureReal P A, ← tsum_indicator_measureReal Q A,
      ← (hP.indicator A).tsum_sub (hQ.indicator A)]
    apply tsum_congr
    intro z
    by_cases hz : z ∈ A <;> simp [Set.indicator, hz]
  rw [hdiff, ← Real.norm_eq_abs]
  calc
    ‖∑' z, A.indicator (fun z => P.real {z} - Q.real {z}) z‖ ≤
        ∑' z, ‖A.indicator (fun z => P.real {z} - Q.real {z}) z‖ :=
      norm_tsum_le_tsum_norm ((hP.sub hQ).indicator A |>.abs)
    _ ≤ ∑' z, |P.real {z} - Q.real {z}| := by
      apply (((hP.sub hQ).indicator A).abs).tsum_le_tsum _ (hP.sub hQ).abs
      intro z
      by_cases hz : z ∈ A <;> simp [Set.indicator, hz]

/-- One-sided version of the event-wise total variation comparison. -/
theorem measureReal_le_add_tvDist {α : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] (P Q : Measure α) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (A : Set α) :
    P.real A ≤ Q.real A + tvDist P Q := by
  have h := (abs_le.mp (abs_measureReal_sub_le_tvDist P Q A)).2
  linarith

/-- The iid increment law is the coordinatewise pushforward of the iid count law. -/
theorem pi_incrementLaw_eq_map (μ : Measure ℕ) [IsProbabilityMeasure μ] (k : ℕ) :
    (Measure.pi fun _ : Fin k => incrementLaw μ) =
      (Measure.pi fun _ : Fin k => μ).map (fun z i => (z i : ℤ) - 1) := by
  symm
  simpa only [incrementLaw] using
    (Measure.pi_map_pi (μ := fun _ : Fin k => μ)
      (f := fun _ : Fin k => fun z : ℕ => (z : ℤ) - 1)
      (fun _ => (measurable_of_countable _).aemeasurable))

/-- The vector of deleted increments reconstructs the deleted word exactly. -/
theorem ofFn_deletedIncrements {n : ℕ} (hn : n ≠ 0) (ω : Fin n → ℕ) :
    List.ofFn (deletedIncrements n ω) = deletedMaximumWord (List.ofFn ω) := by
  have hne : List.ofFn ω ≠ [] := by
    simp only [ne_eq, List.ofFn_eq_nil_iff]
    exact hn
  apply List.ext_getElem
  · simp only [List.length_ofFn, length_deletedMaximumWord hne]
  · intro i hi₁ hi₂
    simp only [List.getElem_ofFn, deletedIncrements]
    exact List.getD_eq_getElem _ _ hi₂

end
end SubcriticalCauchy.Bienayme

namespace SubcriticalCauchy.Bienayme

noncomputable section
open BGW BGW.LocallyFinite

/-- On a bridge, the maximum degree is minus the sum of the deleted increments. -/
theorem maxDegree_eq_deletedIncrements_sum {n : ℕ} (hn : n ≠ 0) (ω : Fin n → ℕ)
    (hω : ω ∈ countBridges n) :
    (listMaxDegree (List.ofFn ω) : ℝ) =
      -((List.ofFn (deletedIncrements n ω)).sum : ℝ) := by
  have hbridge : (List.ofFn ω).sum + 1 = (List.ofFn ω).length := by
    change (∑ i, ω i) + 1 = n at hω
    simpa only [List.sum_ofFn, List.length_ofFn] using hω
  have h := maxDegree_eq_neg_deleted_sum hbridge
  rw [ofFn_deletedIncrements hn]
  exact_mod_cast h

/-- The iid increment condensation event is bounded by the count weak-law event. -/
theorem pi_incrementLaw_condensation_event_le (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {ε : ℝ} (hm : 0 < 1 - (offspringMean μ).toReal) {n : ℕ} (_hn : n ≠ 0) :
    (Measure.pi fun _ : Fin (n - 1) => incrementLaw μ).real
        {x | ε < |-((List.ofFn x).sum : ℝ) /
          ((n : ℝ) * (1 - (offspringMean μ).toReal)) - 1|} ≤
      (Measure.pi fun _ : Fin (n - 1) => μ).real
        {z | ε * (1 - (offspringMean μ).toReal) ≤
          |finitePreviousWalkAverage n z - (1 - (offspringMean μ).toReal)|} := by
  rw [pi_incrementLaw_eq_map]
  change (((Measure.pi fun _ : Fin (n - 1) => μ).map
    (fun z i => (z i : ℤ) - 1))
      {x | ε < |-((List.ofFn x).sum : ℝ) /
        ((n : ℝ) * (1 - (offspringMean μ).toReal)) - 1|}).toReal ≤ _
  rw [Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
  apply measureReal_mono _ (measure_ne_top _ _)
  intro z hz
  have hsum : (List.ofFn (fun i => (z i : ℤ) - 1)).sum = finiteWalkSum z := by
    simp only [List.sum_ofFn, finiteWalkSum]
  change ε < |-((List.ofFn (fun i => (z i : ℤ) - 1)).sum : ℝ) /
    ((n : ℝ) * (1 - (offspringMean μ).toReal)) - 1| at hz
  rw [hsum] at hz
  have hd : 1 - (offspringMean μ).toReal ≠ 0 := ne_of_gt hm
  have halg : -(finiteWalkSum z : ℝ) /
        ((n : ℝ) * (1 - (offspringMean μ).toReal)) - 1 =
      (finitePreviousWalkAverage n z - (1 - (offspringMean μ).toReal)) /
        (1 - (offspringMean μ).toReal) := by
    rw [sub_div, finitePreviousWalkAverage, div_div, div_self hd]
  rw [halg, abs_div, lt_div_iff₀ (abs_pos.mpr hd), abs_of_pos hm] at hz
  exact hz.le

/-- Real-valued form of Theorem 1.1(i), first part. -/
theorem main_maxDegree_condensation_real (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (conditioned μ n (finiteTreeEvent fun t =>
      ε < |(maxDegree t : ℝ) / ((n : ℝ) * (1 - (offspringMean μ).toReal)) - 1|)).toReal)
      atTop (𝓝 0) := by
  have hfin : offspringMean μ ≠ ∞ := ne_top_of_lt (hμ.1.trans ENNReal.one_lt_top)
  have hm : 0 < 1 - (offspringMean μ).toReal := by
    have hmean : (offspringMean μ).toReal < 1 := by
      simpa using (ENNReal.toReal_lt_toReal hfin ENNReal.one_ne_top).mpr hμ.1
    linarith
  have hweak := finitePreviousWalkAverage_deviation_tendsto_zero μ hfin
    (mul_pos hε hm)
  have htv := paper_deleted_maximum_tvDist μ hμ
  apply squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) ?_
    (by simpa using hweak.add htv)
  filter_upwards [eventually_size_admissible μ hμ.to_literal, eventually_gt_atTop (0 : ℕ)]
    with n hsize hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  let B := MaximumSwapLaw.bridgeCountsLaw μ n
  let P := B.map (deletedIncrements n)
  let Q := Measure.pi fun _ : Fin (n - 1) => incrementLaw μ
  let _ : IsProbabilityMeasure (incrementLaw μ) := by
    unfold incrementLaw
    infer_instance
  let A : Set (Fin (n - 1) → ℤ) :=
    {x | ε < |-((List.ofFn x).sum : ℝ) /
      ((n : ℝ) * (1 - (offspringMean μ).toReal)) - 1|}
  let _ : IsProbabilityMeasure B := by
    exact BGW.isProbabilityMeasure_cond_pi_countBridges μ hn0 hsize
  let _ : IsProbabilityMeasure P := by
    dsimp only [P]
    infer_instance
  let _ : IsProbabilityMeasure Q := by
    dsimp only [Q]
    infer_instance
  have hcond : (conditioned μ n (finiteTreeEvent fun t =>
      ε < |(maxDegree t : ℝ) / ((n : ℝ) * (1 - (offspringMean μ).toReal)) - 1|)) =
      P A := by
    have hc := conditioned_maxDegree_event μ hn0
      {d : ℕ | ε < |(d : ℝ) / ((n : ℝ) * (1 - (offspringMean μ).toReal)) - 1|}
    calc
      _ = B {ω | listMaxDegree (List.ofFn ω) ∈
          {d : ℕ | ε < |(d : ℝ) /
            ((n : ℝ) * (1 - (offspringMean μ).toReal)) - 1|}} := by
        simpa only [B, MaximumSwapLaw.bridgeCountsLaw, finiteTreeEvent, Set.mem_ofPred_eq] using hc
      _ = P A := by
        dsimp only [P]
        rw [Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
        apply measure_congr
        filter_upwards [ProbabilityTheory.ae_cond_mem (μ := Measure.pi fun _ : Fin n => μ)
          (Set.to_countable (countBridges n)).measurableSet] with ω hω
        apply propext
        dsimp only [A, Set.mem_preimage, Set.mem_ofPred_eq]
        rw [maxDegree_eq_deletedIncrements_sum hn0 ω hω]
        rfl
  change (conditioned μ n (finiteTreeEvent fun t =>
    ε < |(maxDegree t : ℝ) / ((n : ℝ) * (1 - (offspringMean μ).toReal)) - 1|)).toReal ≤ _
  rw [hcond]
  calc
    P.real A ≤ Q.real A + tvDist P Q := measureReal_le_add_tvDist P Q A
    _ ≤ _ := add_le_add (pi_incrementLaw_condensation_event_le μ hm hn0) (le_refl _)

end
end SubcriticalCauchy.Bienayme
