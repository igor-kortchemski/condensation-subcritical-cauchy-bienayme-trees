module

public import SubcriticalCauchy.MainProofs.M1
public import SubcriticalCauchy.OffspringMaximum

/-!
# Proof helpers for the frozen statement M2

Owned helper module for the registered hole of M2. It is imported by the
frozen statement file, which must not change except inside its holes; add
the proof and any further imports here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators

namespace SubcriticalCauchy.Bienayme

noncomputable section
open BGW BGW.LocallyFinite

/-- The second-largest count is one more than the largest deleted increment. -/
theorem secondMaxDegree_eq_incrementMaximum {n : ℕ} (hn : n ≠ 0) (ω : Fin n → ℕ) :
    (listSecondMaxDegree (List.ofFn ω) : ℝ) =
      ((incrementMaximum (List.ofFn (deletedIncrements n ω)) + 1 : ℤ) : ℝ) := by
  have h := incrementMaximum_deleted_word (List.ofFn ω)
  have hZ : (listSecondMaxDegree (List.ofFn ω) : ℤ) =
      incrementMaximum (deletedMaximumWord (List.ofFn ω)) + 1 := by
    omega
  rw [ofFn_deletedIncrements hn]
  exact_mod_cast hZ

/-- The iid increment second-maximum event is bounded by the count weak-law event. -/
theorem pi_incrementLaw_secondMaximum_event_le (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (ε : ℝ) (n : ℕ) :
    (Measure.pi fun _ : Fin (n - 1) => incrementLaw μ).real
        {x | ε < ((incrementMaximum (List.ofFn x) + 1 : ℤ) : ℝ) / (n : ℝ)} ≤
      (Measure.pi fun _ : Fin (n - 1) => μ).real
        {z | ε ≤ finitePreviousMaximumAverage n z} := by
  rw [pi_incrementLaw_eq_map]
  change (((Measure.pi fun _ : Fin (n - 1) => μ).map
    (fun z i => (z i : ℤ) - 1))
      {x | ε < ((incrementMaximum (List.ofFn x) + 1 : ℤ) : ℝ) / (n : ℝ)}).toReal ≤ _
  rw [Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
  apply measureReal_mono _ (measure_ne_top _ _)
  intro z hz
  have h : incrementMaximum (List.ofFn (fun i => (z i : ℤ) - 1)) =
      (listMaxDegree (List.ofFn z) : ℤ) - 1 := by
    simpa only [List.map_ofFn, Function.comp_def] using
      incrementMaximum_count_word (List.ofFn z)
  have hmax : incrementMaximum (List.ofFn (fun i => (z i : ℤ) - 1)) + 1 =
      (listMaxDegree (List.ofFn z) : ℤ) := by
    omega
  change ε < ((incrementMaximum (List.ofFn (fun i => (z i : ℤ) - 1)) + 1 : ℤ) : ℝ) /
    (n : ℝ) at hz
  change ε ≤ (listMaxDegree (List.ofFn z) : ℝ) / (n : ℝ)
  rw [hmax] at hz
  exact hz.le

/-- Real-valued form of Theorem 1.1(i), second part. -/
theorem main_secondMaxDegree_negligible_real (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (conditioned μ n (finiteTreeEvent fun t =>
      ε < (secondMaxDegree t : ℝ) / n)).toReal) atTop (𝓝 0) := by
  have hfin : offspringMean μ ≠ ∞ := ne_top_of_lt (hμ.1.trans ENNReal.one_lt_top)
  have hweak := finitePreviousMaximumAverage_deviation_tendsto_zero μ hfin hε
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
    {x | ε < ((incrementMaximum (List.ofFn x) + 1 : ℤ) : ℝ) / (n : ℝ)}
  let _ : IsProbabilityMeasure B := by
    exact BGW.isProbabilityMeasure_cond_pi_countBridges μ hn0 hsize
  let _ : IsProbabilityMeasure P := by
    dsimp only [P]
    infer_instance
  let _ : IsProbabilityMeasure Q := by
    dsimp only [Q]
    infer_instance
  have hcond : (conditioned μ n (finiteTreeEvent fun t =>
      ε < (secondMaxDegree t : ℝ) / n)) = P A := by
    have hc := conditioned_secondMaxDegree_event μ hn0
      {d : ℕ | ε < (d : ℝ) / (n : ℝ)}
    calc
      _ = B {ω | listSecondMaxDegree (List.ofFn ω) ∈
          {d : ℕ | ε < (d : ℝ) / (n : ℝ)}} := by
        simpa only [B, MaximumSwapLaw.bridgeCountsLaw, finiteTreeEvent,
          Set.mem_ofPred_eq, secondMaxDegree] using hc
      _ = P A := by
        dsimp only [P]
        rw [Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
        apply measure_congr
        apply Eventually.of_forall
        intro ω
        apply propext
        change (ε < (listSecondMaxDegree (List.ofFn ω) : ℝ) / (n : ℝ)) ↔ _
        dsimp only [A, Set.mem_preimage, Set.mem_ofPred_eq]
        rw [secondMaxDegree_eq_incrementMaximum hn0]
        rfl
  change (conditioned μ n (finiteTreeEvent fun t =>
    ε < (secondMaxDegree t : ℝ) / n)).toReal ≤ _
  rw [hcond]
  calc
    P.real A ≤ Q.real A + tvDist P Q := measureReal_le_add_tvDist P Q A
    _ ≤ _ := add_le_add (pi_incrementLaw_secondMaximum_event_le μ ε n) (le_refl _)

end
end SubcriticalCauchy.Bienayme
