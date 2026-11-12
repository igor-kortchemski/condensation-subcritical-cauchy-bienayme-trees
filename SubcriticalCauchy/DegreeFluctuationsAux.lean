module

public import SubcriticalCauchy.PropProofs.P42Aux
public import SubcriticalCauchy.MainProofs.M2
public import SubcriticalCauchy.IncrementTailAsymptotics

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! # Maximal-degree laws and their transfer through the deleted-increment bridge -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators

namespace SubcriticalCauchy.Bienayme

noncomputable section
open BGW BGW.LocallyFinite

local instance degreeFluctuationsPlaneTreeMeasurableSpace : MeasurableSpace PlaneTree := ⊤

local instance incrementLaw_isProbability (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (incrementLaw μ) := by
  unfold incrementLaw
  infer_instance

/-- The integer-valued law of the largest degree of the conditioned plane tree. -/
def conditionedMaxDegreeLaw (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) : Measure ℤ :=
  (conditionedPlaneTreeLaw μ n).map (fun t => (maxDegree t : ℤ))

/-- The integer-valued law of one less than the second-largest degree. -/
def conditionedSecondMaxDegreeLaw (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) :
    Measure ℤ :=
  (conditionedPlaneTreeLaw μ n).map (fun t => (secondMaxDegree t : ℤ) - 1)

/-- The law of minus the sum of `n - 1` independent increments. -/
def incrementSumLaw (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) : Measure ℤ :=
  (Measure.pi fun _ : Fin (n - 1) => incrementLaw μ).map (fun x => -∑ i, x i)

/-- The law of the maximum of `n - 1` independent increments. -/
def incrementMaximumLaw (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) : Measure ℤ :=
  (Measure.pi fun _ : Fin (n - 1) => incrementLaw μ).map
    (fun x => incrementMaximum (List.ofFn x))

private theorem map_conditionedPlaneTreeLaw_event {α : Type*} [MeasurableSpace α]
    [Countable α] [MeasurableSingletonClass α]
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) (f : PlaneTree → α)
    (hf : Measurable f) (A : Set α) :
    ((conditionedPlaneTreeLaw μ n).map f) A =
      conditioned μ n (PlaneTree.toLocallyFinite '' (f ⁻¹' A)) := by
  have hA : MeasurableSet A := (Set.to_countable A).measurableSet
  have hpre : PlaneTree.toLocallyFinite ⁻¹'
      (PlaneTree.toLocallyFinite '' (f ⁻¹' A)) = f ⁻¹' A := by
    ext t
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨s, hs, hts⟩
      rwa [PlaneTree.toLocallyFinite_injective hts] at hs
    · exact fun ht => ⟨t, ht, rfl⟩
  rw [Measure.map_apply hf hA]
  calc
    (conditionedPlaneTreeLaw μ n) (f ⁻¹' A) =
        ((conditionedPlaneTreeLaw μ n).map PlaneTree.toLocallyFinite)
          (PlaneTree.toLocallyFinite '' (f ⁻¹' A)) := by
      rw [Measure.map_apply measurableEmbedding_toLocallyFinite.measurable
        ((Set.to_countable _).image PlaneTree.toLocallyFinite).measurableSet, hpre]
    _ = conditioned μ n (PlaneTree.toLocallyFinite '' (f ⁻¹' A)) := by
      rw [conditionedPlaneTreeLaw_map_toLocallyFinite]

/-- On a bridge, the conditioned maximum-degree law is the pushforward of the
remaining increments by minus their sum. -/
theorem conditionedMaxDegreeLaw_eq_deleted_map (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : n ≠ 0) :
    conditionedMaxDegreeLaw μ n =
      ((MaximumSwapLaw.bridgeCountsLaw μ n).map (deletedIncrements n)).map
        (fun x => -∑ i, x i) := by
  let B := MaximumSwapLaw.bridgeCountsLaw μ n
  ext A hA
  rw [conditionedMaxDegreeLaw, map_conditionedPlaneTreeLaw_event μ n _
    (measurable_of_countable _) A]
  change conditioned μ n (PlaneTree.toLocallyFinite ''
    {t | (maxDegree t : ℤ) ∈ A}) = _
  have hc := conditioned_maxDegree_event μ hn {d : ℕ | (d : ℤ) ∈ A}
  calc
    _ = B {ω | (listMaxDegree (List.ofFn ω) : ℤ) ∈ A} := by
      simpa only [B, MaximumSwapLaw.bridgeCountsLaw, Set.mem_ofPred_eq] using hc
    _ = _ := by
      rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
        Measure.map_apply (measurable_of_countable _) hA]
      apply measure_congr
      have hmem : ∀ᵐ ω ∂B, ω ∈ countBridges n := by
        exact ProbabilityTheory.ae_cond_mem
          (μ := Measure.pi fun _ : Fin n => μ) (s := countBridges n)
          (Set.to_countable _).measurableSet
      filter_upwards [hmem] with ω hω
      have hreal := maxDegree_eq_deletedIncrements_sum hn ω hω
      have hint : (listMaxDegree (List.ofFn ω) : ℤ) =
          -(List.ofFn (deletedIncrements n ω)).sum := by
        exact_mod_cast hreal
      simp only [Set.mem_preimage, Function.comp_apply]
      rw [hint]
      simp only [List.sum_ofFn]

/-- The conditioned second-maximum law is the pushforward of the remaining
increments by their maximum. -/
theorem conditionedSecondMaxDegreeLaw_eq_deleted_map (μ : Measure ℕ)
    [IsProbabilityMeasure μ] {n : ℕ} (hn : n ≠ 0) :
    conditionedSecondMaxDegreeLaw μ n =
      ((MaximumSwapLaw.bridgeCountsLaw μ n).map (deletedIncrements n)).map
        (fun x => incrementMaximum (List.ofFn x)) := by
  let B := MaximumSwapLaw.bridgeCountsLaw μ n
  ext A hA
  rw [conditionedSecondMaxDegreeLaw, map_conditionedPlaneTreeLaw_event μ n _
    (measurable_of_countable _) A]
  change conditioned μ n (PlaneTree.toLocallyFinite ''
    {t | (secondMaxDegree t : ℤ) - 1 ∈ A}) = _
  have hc := conditioned_secondMaxDegree_event μ hn
    {d : ℕ | (d : ℤ) - 1 ∈ A}
  calc
    _ = B {ω | (listSecondMaxDegree (List.ofFn ω) : ℤ) - 1 ∈ A} := by
      simpa only [B, MaximumSwapLaw.bridgeCountsLaw, Set.mem_ofPred_eq] using hc
    _ = _ := by
      rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
        Measure.map_apply (measurable_of_countable _) hA]
      apply measure_congr
      apply Eventually.of_forall
      intro ω
      simp only [Set.mem_preimage, Function.comp_apply]
      change ((listSecondMaxDegree (List.ofFn ω) : ℤ) - 1 ∈ A) = _
      have h := incrementMaximum_deleted_word (List.ofFn ω)
      have hint : (listSecondMaxDegree (List.ofFn ω) : ℤ) - 1 =
          incrementMaximum (List.ofFn (deletedIncrements n ω)) := by
        rw [ofFn_deletedIncrements hn]
        omega
      rw [hint]

/-- U4.1(a): the largest conditioned-tree degree and minus the sum of the
independent increments are asymptotically indistinguishable in total variation. -/
theorem conditioned_maxDegree_tvDist (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) :
    Tendsto (fun n : ℕ => tvDist (conditionedMaxDegreeLaw μ n) (incrementSumLaw μ n))
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ => tvDist_nonneg) ?_
    (paper_deleted_maximum_tvDist μ hμ)
  filter_upwards [eventually_size_admissible μ hμ.to_literal, eventually_gt_atTop (0 : ℕ)]
    with n hsize hn
  let B := MaximumSwapLaw.bridgeCountsLaw μ n
  let P := B.map (deletedIncrements n)
  let Q := Measure.pi fun _ : Fin (n - 1) => incrementLaw μ
  let _ : IsProbabilityMeasure B :=
    BGW.isProbabilityMeasure_cond_pi_countBridges μ (Nat.ne_of_gt hn) hsize
  let _ : IsProbabilityMeasure P := by dsimp only [P]; infer_instance
  let _ : IsProbabilityMeasure Q := by dsimp only [Q]; infer_instance
  rw [conditionedMaxDegreeLaw_eq_deleted_map μ (Nat.ne_of_gt hn)]
  exact tvDist_map_le P Q (fun x => -∑ i, x i) (measurable_of_countable _)

/-- U4.1(b): one less than the second-largest conditioned-tree degree and the
maximum of the independent increments are asymptotically indistinguishable. -/
theorem conditioned_secondMaxDegree_tvDist (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) :
    Tendsto (fun n : ℕ => tvDist (conditionedSecondMaxDegreeLaw μ n)
      (incrementMaximumLaw μ n)) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ => tvDist_nonneg) ?_
    (paper_deleted_maximum_tvDist μ hμ)
  filter_upwards [eventually_size_admissible μ hμ.to_literal, eventually_gt_atTop (0 : ℕ)]
    with n hsize hn
  let B := MaximumSwapLaw.bridgeCountsLaw μ n
  let P := B.map (deletedIncrements n)
  let Q := Measure.pi fun _ : Fin (n - 1) => incrementLaw μ
  let _ : IsProbabilityMeasure B :=
    BGW.isProbabilityMeasure_cond_pi_countBridges μ (Nat.ne_of_gt hn) hsize
  let _ : IsProbabilityMeasure P := by dsimp only [P]; infer_instance
  let _ : IsProbabilityMeasure Q := by dsimp only [Q]; infer_instance
  rw [conditionedSecondMaxDegreeLaw_eq_deleted_map μ (Nat.ne_of_gt hn)]
  exact tvDist_map_le P Q (fun x => incrementMaximum (List.ofFn x))
    (measurable_of_countable _)


/-- A real upper bound on the fold maximum is exactly a bound on every entry,
together with the empty-word lower endpoint `-1`. -/
theorem incrementMaximum_le_iff (xs : List ℤ) (y : ℝ) :
    ((incrementMaximum xs : ℤ) : ℝ) ≤ y ↔
      ((-1 : ℝ) ≤ y) ∧ ∀ z ∈ xs, (z : ℝ) ≤ y := by
  induction xs with
  | nil => simp [incrementMaximum]
  | cons z zs ih =>
      change ((List.foldr max (-1) zs : ℤ) : ℝ) ≤ y ↔ _ at ih
      simp only [incrementMaximum, List.foldr_cons, Int.cast_max, max_le_iff,
        List.mem_cons]
      rw [ih]
      aesop

/-- For a nonnegative threshold, the maximum event in a finite independent
increment product is an exact coordinate rectangle. -/
theorem pi_incrementMaximum_le (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (n : ℕ) (y : ℝ) (hy : 0 ≤ y) :
    (Measure.pi fun _ : Fin n => incrementLaw μ).real
        {x | ((incrementMaximum (List.ofFn x) : ℤ) : ℝ) ≤ y} =
      ((incrementLaw μ).real {z : ℤ | (z : ℝ) ≤ y}) ^ n := by
  have hset : {x : Fin n → ℤ | ((incrementMaximum (List.ofFn x) : ℤ) : ℝ) ≤ y} =
      Set.univ.pi (fun _ : Fin n => {z : ℤ | (z : ℝ) ≤ y}) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies]
    rw [incrementMaximum_le_iff]
    constructor
    · exact fun h i => h.2 _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
    · intro h
      exact ⟨by linarith, fun z hz => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
        exact h i⟩
  rw [Measure.real, Measure.real, hset, Measure.pi_pi, ENNReal.toReal_prod]
  simp

/-- Below the increment endpoint `-1`, the maximum event is empty, including
for the empty word. -/
theorem pi_incrementMaximum_eq_zero_of_lt_neg_one (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (n : ℕ) (y : ℝ) (hy : y < -1) :
    (Measure.pi fun _ : Fin n => incrementLaw μ).real
        {x | ((incrementMaximum (List.ofFn x) : ℤ) : ℝ) ≤ y} = 0 := by
  have hset : {x : Fin n → ℤ | ((incrementMaximum (List.ofFn x) : ℤ) : ℝ) ≤ y} = ∅ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rw [incrementMaximum_le_iff]
    rintro ⟨hneg, _⟩
    linarith
  rw [hset]
  simp

/-- For a nonnegative `y`, the strict increment tail is the non-strict
`incrementTail` at the integer threshold `⌊y⌋₊ + 1`. -/
theorem incrementLaw_real_gt (μ : Measure ℕ) [IsProbabilityMeasure μ] (y : ℝ)
    (hy : 0 ≤ y) :
    (incrementLaw μ).real {z : ℤ | y < (z : ℝ)} =
      (incrementTail μ ((⌊y⌋₊ + 1 : ℕ) : ℝ)).toReal := by
  rw [Measure.real, incrementLaw,
    Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
  apply congrArg ENNReal.toReal
  rw [incrementTail]
  congr 1
  ext k
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Int.cast_sub, Int.cast_natCast,
    Int.cast_one]
  let z : ℤ := (k : ℤ) - 1
  have hz : (k : ℝ) - 1 = (z : ℝ) := by simp [z]
  rw [hz]
  push_cast
  rw [natCast_floor_eq_intCast_floor hy, ← Int.floor_lt]
  constructor
  · intro h
    exact_mod_cast (show ⌊y⌋ + 1 ≤ (k : ℤ) - 1 by omega)
  · intro h
    have h' : ⌊y⌋ + 1 ≤ (k : ℤ) - 1 := by exact_mod_cast h
    omega

/-- The non-strict increment CDF is one minus the strict tail. -/
theorem incrementLaw_real_le (μ : Measure ℕ) [IsProbabilityMeasure μ] (y : ℝ) :
    (incrementLaw μ).real {z : ℤ | (z : ℝ) ≤ y} =
      1 - (incrementLaw μ).real {z : ℤ | y < (z : ℝ)} := by
  have hset : {z : ℤ | y < (z : ℝ)} = {z : ℤ | (z : ℝ) ≤ y}ᶜ := by
    ext z
    simp [not_le]
  have h := probReal_add_probReal_compl (μ := incrementLaw μ)
    (Set.to_countable {z : ℤ | (z : ℝ) ≤ y}).measurableSet
  rw [← hset] at h
  linarith

end
end SubcriticalCauchy.Bienayme
