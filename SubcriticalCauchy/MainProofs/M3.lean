module

public import SubcriticalCauchy.FiniteTreeEvent
public import SubcriticalCauchy.M3Transfer
public import SubcriticalCauchy.WeakRecordRenewal

/-!
# Proof helpers for the frozen statement M3

Owned helper module for the registered hole of M3. It is imported by the
frozen statement file, which must not change except inside its holes; add
the proof and any further imports here.
-/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Topology
namespace SubcriticalCauchy.Bienayme
noncomputable section
variable [MeasurableSpace (List ℤ)] [MeasurableSingletonClass (List ℤ)]

theorem iid_incrementWord_records_tendsto (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ < 1) (j : ℕ) :
    Tendsto (fun n : ℕ =>
      ((Measure.pi fun _ : Fin (n - 1) => incrementLaw μ).map List.ofFn)
        {x | weakRecordCount x.reverse = j}) atTop
      (𝓝 (ENNReal.ofReal ((1 - (offspringMean μ).toReal) *
        (offspringMean μ).toReal ^ j))) := by
  have ht := (iid_reversed_weakRecordCount_geometric_tendsto μ hm j).comp
    (tendsto_sub_atTop_nat 1)
  convert ht using 1
  funext n
  have hp : (Measure.pi fun _ : Fin (n - 1) => incrementLaw μ) =
      (Measure.pi fun _ : Fin (n - 1) => μ).map (fun z i => (z i : ℤ) - 1) := by
    symm
    simpa only [incrementLaw] using
      (Measure.pi_map_pi (μ := fun _ : Fin (n - 1) => μ)
        (f := fun _ : Fin (n - 1) => fun z : ℕ => (z : ℤ) - 1)
        (fun _ => (measurable_of_countable _).aemeasurable))
  rw [Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet,
    hp, Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
  rfl

omit [MeasurableSpace (List ℤ)] [MeasurableSingletonClass (List ℤ)] in
/-- Event probabilities transfer under vanishing TV, allowing null initial laws. -/
theorem event_tendsto_of_tvDist {α : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] (P Q : ℕ → Measure α) (A : Set α) (r : ℝ≥0∞)
    (hr : r ≠ ∞)
    (hP : ∀ᶠ n in atTop, IsProbabilityMeasure (P n))
    (hQ : ∀ᶠ n in atTop, IsProbabilityMeasure (Q n))
    (ht : Tendsto (fun n => tvDist (P n) (Q n)) atTop (𝓝 0))
    (hq : Tendsto (fun n => Q n A) atTop (𝓝 r)) :
    Tendsto (fun n => P n A) atTop (𝓝 r) := by
  have hqr := (ENNReal.tendsto_toReal hr).comp hq
  have hbounds : ∀ᶠ n in atTop,
      (Q n).real A - tvDist (P n) (Q n) ≤ (P n).real A ∧
      (P n).real A ≤ (Q n).real A + tvDist (P n) (Q n) := by
    filter_upwards [hP, hQ] with n hp hq
    let _ := hp
    let _ := hq
    have ha := abs_le.mp (abs_measureReal_sub_le_tvDist (P n) (Q n) A)
    constructor <;> linarith
  have hpr : Tendsto (fun n => (P n).real A) atTop (𝓝 r.toReal) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (by simpa [Measure.real] using hqr.sub ht) (by simpa [Measure.real] using hqr.add ht)
      (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2)
  have hh := ENNReal.tendsto_ofReal hpr
  rw [ENNReal.ofReal_toReal hr] at hh
  apply hh.congr'
  filter_upwards [hP] with n hp
  let _ := hp
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)
end
end SubcriticalCauchy.Bienayme

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Topology
namespace SubcriticalCauchy.Bienayme
open BGW
noncomputable section
variable [MeasurableSpace (List ℤ)] [MeasurableSingletonClass (List ℤ)]

theorem bridge_cyclicResidual_records_geometric (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (j : ℕ) :
    Tendsto (fun n : ℕ => (MaximumSwapLaw.bridgeCountsLaw μ n)
      {ω | weakRecordCount (cyclicResidual (stepWord ω)).reverse = j})
      atTop (𝓝 (ENNReal.ofReal
        ((1 - (offspringMean μ).toReal) * (offspringMean μ).toReal ^ j))) := by
  let _ : IsProbabilityMeasure (incrementLaw μ) := by
    unfold incrementLaw
    infer_instance
  have hh := event_tendsto_of_tvDist
    (fun n => (MaximumSwapLaw.bridgeCountsLaw μ n).map (fun ω => cyclicResidual (stepWord ω)))
    (fun n => (Measure.pi fun _ : Fin (n - 1) => incrementLaw μ).map List.ofFn)
    {x | weakRecordCount x.reverse = j}
    (ENNReal.ofReal ((1 - (offspringMean μ).toReal) * (offspringMean μ).toReal ^ j))
    (by simp) ?_ (Eventually.of_forall fun _ => inferInstance)
    (cyclicResidual_bridge_tvDist μ hμ) (iid_incrementWord_records_tendsto μ hμ.1 j)
  · apply hh.congr'
    exact Eventually.of_forall fun n => by
      dsimp only
      rw [Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
      rfl
  · filter_upwards [eventually_size_admissible μ hμ.to_literal,
      eventually_gt_atTop (0 : ℕ)] with n hsize hn
    let _ : IsProbabilityMeasure (MaximumSwapLaw.bridgeCountsLaw μ n) :=
      BGW.isProbabilityMeasure_cond_pi_countBridges μ (Nat.ne_of_gt hn) hsize
    infer_instance
end
end SubcriticalCauchy.Bienayme


namespace SubcriticalCauchy.Bienayme
open MeasureTheory Filter ProbabilityTheory BGW
open scoped ENNReal Topology
noncomputable section

/-- Proof of the frozen M3 statement, through the cyclic residual law. -/
theorem main_maxDegreeDepth_geometric_proof (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (j : ℕ) :
    Tendsto (fun n : ℕ => conditioned μ n (finiteTreeEvent fun t => maxDegreeDepth t = j))
      atTop (𝓝 (ENNReal.ofReal
        ((1 - (offspringMean μ).toReal) * (offspringMean μ).toReal ^ j))) := by
  let _ : MeasurableSpace (List ℤ) := ⊤
  let _ : MeasurableSingletonClass (List ℤ) := ⟨fun _ => trivial⟩
  let r := ENNReal.ofReal ((1 - (offspringMean μ).toReal) * (offspringMean μ).toReal ^ j)
  let A : Set (List ℤ) := {x | weakRecordCount x.reverse = j}
  let p : ℕ → ℝ≥0∞ := fun n =>
    conditioned μ n (finiteIncrementEvent fun x => cyclicResidual x ∈ A)
  let q : ℕ → ℝ≥0∞ := fun n =>
    MaximumSwapLaw.bridgeCountsLaw μ n {ω | cyclicResidual (stepWord ω) ∈ A}
  let d : ℕ → ℝ := fun n =>
    (conditioned μ n).real (finiteIncrementEvent fun x => ¬ uniqueWordMaximum x)
  have hq : Tendsto q atTop (𝓝 r) := by
    simpa only [q, r, A, Set.mem_ofPred_eq] using
      bridge_cyclicResidual_records_geometric μ hμ j
  have hd : Tendsto d atTop (𝓝 0) := by
    simpa only [d, Measure.real, finiteIncrementEvent, finiteTreeEvent] using
      conditioned_nonunique_maximum_tendsto_zero μ hμ
  have hb : ∀ᶠ n in atTop, |(p n).toReal - (q n).toReal| ≤ d n := by
    filter_upwards [eventually_gt_atTop (0 : ℕ),
      eventually_size_admissible μ hμ.to_literal] with n hn hsize
    simpa only [p, q, d, Measure.real] using
      conditioned_cyclicResidual_event_error_le μ (Nat.ne_of_gt hn) hsize A
  have hqr := (ENNReal.tendsto_toReal (show r ≠ ∞ by simp [r])).comp hq
  have hpr : Tendsto (fun n => (p n).toReal) atTop (𝓝 r.toReal) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (by simpa using hqr.sub hd) (by simpa using hqr.add hd)
    · exact hb.mono fun n h => by have := (abs_le.mp h).1; linarith
    · exact hb.mono fun n h => by have := (abs_le.mp h).2; linarith
  have hp : Tendsto p atTop (𝓝 r) := by
    have hh := ENNReal.tendsto_ofReal hpr
    rw [ENNReal.ofReal_toReal (show r ≠ ∞ by simp [r])] at hh
    apply hh.congr'
    filter_upwards [eventually_size_admissible μ hμ.to_literal] with n hsize
    let _ : IsProbabilityMeasure (conditioned μ n) := conditioned_isProbability μ n hsize
    exact ENNReal.ofReal_toReal (measure_ne_top _ _)
  apply hp.congr'
  exact Eventually.of_forall fun n => by
    simp only [p, A, Set.mem_ofPred_eq, finiteIncrementEvent, finiteTreeEvent,
      maxDegreeDepth_eq_weakRecordCount]
end
end SubcriticalCauchy.Bienayme
