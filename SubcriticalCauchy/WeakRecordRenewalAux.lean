module

public import SubcriticalCauchy.WalkExplorationAux
public import SubcriticalCauchy.CyclicResidual
public import Mathlib.MeasureTheory.Integral.Indicator
public import Mathlib.Data.Set.Finite.Lattice

/-! # Pathwise finiteness and stabilization of weak records

Time zero is excluded; the comparison at time zero is included. No restriction
on upward overshoots is imposed.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme
noncomputable section

/-- All positive weak ascending record times of the infinite offspring walk. -/
def weakRecordTimes (ω : ℕ → ℕ) : Set ℕ :=
  {k | 0 < k ∧ ∀ i < k, walkSum ω i ≤ walkSum ω k}

/-- Total number of positive weak records, retaining infinity. -/
def infiniteWeakRecordCount (ω : ℕ → ℕ) : ℝ≥0∞ :=
  ∑' k : ℕ, (weakRecordTimes ω).indicator (fun _ => (1 : ℝ≥0∞)) k

/-- Negative speed forces all weak records into a finite initial interval. -/
theorem weakRecordTimes_finite_of_negative_drift (ω : ℕ → ℕ) {a : ℝ} (ha : a < 0)
    (hω : Tendsto (fun n => walkAverage n ω) atTop (𝓝 a)) :
    (weakRecordTimes ω).Finite := by
  have hneg := hω.eventually (eventually_lt_nhds ha)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hneg
  apply (Finset.range N).finite_toSet.subset
  intro k hk
  have hzero := hk.2 0 hk.1
  have hsum : 0 ≤ walkSum ω k := by simpa [walkSum] using hzero
  have hkN : k < N := by
    by_contra hn
    have hav := hN k (by omega)
    have hnonneg : 0 ≤ walkAverage k ω := div_nonneg (by exact_mod_cast hsum) (Nat.cast_nonneg _)
    exact (not_lt_of_ge hnonneg) hav
  exact Finset.mem_range.mpr hkN

/-- The total record-time set is almost surely finite under subcriticality. -/
theorem iid_weakRecordTimes_finite_ae (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ < 1) :
    ∀ᵐ ω ∂iidOffspringLaw μ, (weakRecordTimes ω).Finite := by
  have hfin := ne_top_of_lt (hm.trans ENNReal.one_lt_top)
  have hmR : (offspringMean μ).toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hfin ENNReal.one_ne_top).mpr hm
  filter_upwards [walkAverage_ae_tendsto μ hfin] with ω hω
  exact weakRecordTimes_finite_of_negative_drift ω (sub_neg.mpr hmR) hω

/-- The extended count agrees with finite cardinality whenever the set is finite. -/
theorem infiniteWeakRecordCount_eq_ncard (ω : ℕ → ℕ) (h : (weakRecordTimes ω).Finite) :
    infiniteWeakRecordCount ω = ((weakRecordTimes ω).ncard : ℝ≥0∞) := by
  rw [infiniteWeakRecordCount, tsum_eq_sum (s := h.toFinset)]
  · rw [Set.ncard_eq_toFinset_card _ h]
    calc
      _ = ∑ _k ∈ h.toFinset, (1 : ℝ≥0∞) := Finset.sum_congr rfl fun k hk =>
        Set.indicator_of_mem (h.mem_toFinset.mp hk) _
      _ = _ := by simp
  · intro k hk
    exact Set.indicator_of_notMem (by simpa using hk) _

/-- In particular the extended count really is finite almost surely. -/
theorem iid_infiniteWeakRecordCount_lt_top_ae (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ < 1) :
    ∀ᵐ ω ∂iidOffspringLaw μ, infiniteWeakRecordCount ω < ∞ := by
  filter_upwards [iid_weakRecordTimes_finite_ae μ hm] with ω hω
  rw [infiniteWeakRecordCount_eq_ncard ω hω]
  exact ENNReal.natCast_lt_top _

/-- Measurability of each individual record event. -/
theorem measurableSet_weakRecordTime (k : ℕ) :
    MeasurableSet {ω : ℕ → ℕ | k ∈ weakRecordTimes ω} := by
  have h : MeasurableSet {ω : ℕ → ℕ | ∀ i < k, walkSum ω i ≤ walkSum ω k} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun (_ : i < k) =>
      measurableSet_le (measurable_walkSum i) (measurable_walkSum k)
  by_cases hk : 0 < k
  · simpa only [weakRecordTimes, Set.mem_ofPred_eq, hk, true_and] using h
  · simp only [weakRecordTimes, Set.mem_ofPred_eq, hk, false_and, Set.ofPred_false,
      MeasurableSet.empty]

@[fun_prop] theorem measurable_infiniteWeakRecordCount : Measurable infiniteWeakRecordCount := by
  unfold infiniteWeakRecordCount
  exact Measurable.tsum fun k =>
    measurable_const.indicator (measurableSet_weakRecordTime k)

/-- Splitting an offspring walk at a deterministic time retains the overshoot. -/
theorem walkSum_add_shift (ω : ℕ → ℕ) (q k : ℕ) :
    walkSum ω (q + k) = walkSum ω q + walkSum (fun i => ω (q + i)) k := by
  simp only [walkSum, Finset.sum_range_add]

/-- After any weak ascending record, future weak records are exactly those of
the shifted walk. Its starting height cancels; it need not be zero. -/
theorem weakRecordTime_add_iff_shift (ω : ℕ → ℕ) {q k : ℕ}
    (hq : q ∈ weakRecordTimes ω) (hk : 0 < k) :
    q + k ∈ weakRecordTimes ω ↔ k ∈ weakRecordTimes (fun i => ω (q + i)) := by
  constructor
  · intro h
    refine ⟨hk, fun i hi => ?_⟩
    have hh := h.2 (q + i) (by omega)
    rw [walkSum_add_shift, walkSum_add_shift] at hh
    omega
  · intro h
    refine ⟨by omega, fun i hi => ?_⟩
    rw [walkSum_add_shift]
    by_cases hiq : i < q
    · have hpast := hq.2 i hiq
      have hfuture := h.2 0 hk
      change 0 ≤ walkSum (fun i => ω (q + i)) k at hfuture
      omega
    · have he : i = q + (i - q) := by omega
      rw [he, walkSum_add_shift]
      have hfuture := h.2 (i - q) (by omega)
      omega

/-- Atom probabilities converge when natural-valued random variables eventually
agree almost surely with an extended-valued random variable. -/
theorem tendsto_measure_nat_eq_of_ae_eventually_cast_eq {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsFiniteMeasure ν] (f : ℕ → Ω → ℕ) (F : Ω → ℝ≥0∞)
    (hf : ∀ n, Measurable (f n)) (hF : Measurable F)
    (h : ∀ᵐ ω ∂ν, ∀ᶠ n : ℕ in atTop, (f n ω : ℝ≥0∞) = F ω) (j : ℕ) :
    Tendsto (fun n => ν {ω | f n ω = j}) atTop (𝓝 (ν {ω | F ω = (j : ℝ≥0∞)})) := by
  apply tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
    (μ := ν) (A := {ω | F ω = (j : ℝ≥0∞)})
    (As := fun n => {ω | f n ω = j}) atTop
    (measurableSet_eq_fun hF measurable_const)
    (fun n => measurableSet_eq_fun (hf n) measurable_const)
  filter_upwards [h] with ω hω
  filter_upwards [hω] with n hn
  constructor
  · intro he
    exact hn.symm.trans (congrArg (fun k : ℕ => (k : ℝ≥0∞)) he)
  · intro he
    exact Nat.cast_injective (hn.trans he)

end
end SubcriticalCauchy.Bienayme

namespace SubcriticalCauchy.Bienayme
noncomputable section
open ProbabilityTheory

/-- The fresh offspring sequence following time `q`. -/
def recordTail (q : ℕ) (ω : ℕ → ℕ) : ℕ → ℕ := fun i => ω (q + i)

@[fun_prop] theorem measurable_recordTail (q : ℕ) : Measurable (recordTail q) :=
  measurable_pi_iff.mpr fun i => measurable_pi_apply (q + i)

/-- A deterministic shift preserves the infinite iid offspring law. -/
theorem iidOffspringLaw_map_recordTail (μ : Measure ℕ) [IsProbabilityMeasure μ] (q : ℕ) :
    (iidOffspringLaw μ).map (recordTail q) = iidOffspringLaw μ := by
  exact Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => μ)
    (f := fun i => q + i) (by intro i j h; change q + i = q + j at h; omega)

/-- Independence of all coordinates before `q` and the entire fresh tail. -/
theorem iid_prefix_indep_recordTail (μ : Measure ℕ) [IsProbabilityMeasure μ] (q : ℕ) :
    IndepFun (fun (ω : ℕ → ℕ) (i : Fin q) => ω i) (recordTail q) (iidOffspringLaw μ) := by
  let S : Set ℕ := {i | i < q}
  let T : Set ℕ := {i | q ≤ i}
  have hd : Disjoint S T := Set.disjoint_left.mpr (by intro i hi ht; dsimp [S, T] at hi ht; omega)
  have hi := (iid_coordinates_independent μ).indepFun_set S T hd
    (fun i => measurable_pi_apply i)
  let a : (S → ℕ) → (Fin q → ℕ) := fun x i => x ⟨i.val, i.isLt⟩
  let b : (T → ℕ) → (ℕ → ℕ) := fun x i => x ⟨q + i, by dsimp [T]; omega⟩
  have ha : Measurable a := measurable_pi_iff.mpr fun i => measurable_pi_apply _
  have hb : Measurable b := measurable_pi_iff.mpr fun i => measurable_pi_apply _
  exact hi.comp ha hb

/-- Fixed-time prefix/tail factorization for an arbitrary measurable tail event. -/
theorem iid_prefix_recordTail_factorization (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (q : ℕ) (A : Set (Fin q → ℕ)) (B : Set (ℕ → ℕ)) (hB : MeasurableSet B) :
    iidOffspringLaw μ (((fun ω (i : Fin q) => ω i) ⁻¹' A) ∩ (recordTail q ⁻¹' B)) =
      iidOffspringLaw μ ((fun ω (i : Fin q) => ω i) ⁻¹' A) * iidOffspringLaw μ B := by
  rw [(iid_prefix_indep_recordTail μ q).measure_inter_preimage_eq_mul A B
    (Set.to_countable A).measurableSet hB]
  rw [← Measure.map_apply (measurable_recordTail q) hB, iidOffspringLaw_map_recordTail]

/-- The event that `q` is the first positive weak record. -/
def firstWeakRecordEvent (q : ℕ) : Set (ℕ → ℕ) :=
  {ω | q ∈ weakRecordTimes ω ∧ ∀ i < q, i ∉ weakRecordTimes ω}

theorem measurableSet_firstWeakRecordEvent (q : ℕ) : MeasurableSet (firstWeakRecordEvent q) := by
  have hn : MeasurableSet {ω : ℕ → ℕ | ∀ i < q, i ∉ weakRecordTimes ω} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun (_ : i < q) =>
      (measurableSet_weakRecordTime i).compl
  exact (measurableSet_weakRecordTime q).inter hn

/-- Record predicates through `q` depend only on the first `q` coordinates. -/
theorem weakRecordTime_congr_prefix {ω η : ℕ → ℕ} {q k : ℕ}
    (h : ∀ i < q, ω i = η i) (hk : k ≤ q) :
    k ∈ weakRecordTimes ω ↔ k ∈ weakRecordTimes η := by
  have hs (j : ℕ) (hj : j ≤ q) : walkSum ω j = walkSum η j := by
    unfold walkSum
    apply Finset.sum_congr rfl
    intro i hi
    rw [h i (lt_of_lt_of_le (Finset.mem_range.mp hi) hj)]
  change (0 < k ∧ ∀ i < k, walkSum ω i ≤ walkSum ω k) ↔ _
  rw [hs k hk]
  constructor
  · rintro ⟨hp, hh⟩
    exact ⟨hp, fun i hi => by simpa only [hs i (hi.le.trans hk)] using hh i hi⟩
  · rintro ⟨hp, hh⟩
    exact ⟨hp, fun i hi => by simpa only [hs i (hi.le.trans hk)] using hh i hi⟩

/-- First-record events are finite-prefix events. -/
theorem firstWeakRecordEvent_eq_prefix_preimage (q : ℕ) :
    ∃ A : Set (Fin q → ℕ), firstWeakRecordEvent q =
      (fun ω (i : Fin q) => ω i) ⁻¹' A := by
  let extend : (Fin q → ℕ) → (ℕ → ℕ) := fun v i => if hi : i < q then v ⟨i, hi⟩ else 0
  refine ⟨{v | extend v ∈ firstWeakRecordEvent q}, ?_⟩
  ext ω
  have h : ∀ i < q, ω i = extend (fun i : Fin q => ω i) i := by
    intro i hi
    simp [extend, hi]
  change (q ∈ weakRecordTimes ω ∧ ∀ i < q, i ∉ weakRecordTimes ω) ↔ _
  constructor
  · rintro ⟨hq, hn⟩
    exact ⟨(weakRecordTime_congr_prefix h le_rfl).mp hq,
      fun i hi => mt (weakRecordTime_congr_prefix h hi.le).mpr (hn i hi)⟩
  · rintro ⟨hq, hn⟩
    exact ⟨(weakRecordTime_congr_prefix h le_rfl).mpr hq,
      fun i hi => mt (weakRecordTime_congr_prefix h hi.le).mp (hn i hi)⟩

/-- First-record / fresh-tail factorization, with the actual infinite iid law. -/
theorem iid_firstWeakRecord_tail_factorization (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (q : ℕ) (B : Set (ℕ → ℕ)) (hB : MeasurableSet B) :
    iidOffspringLaw μ (firstWeakRecordEvent q ∩ (recordTail q ⁻¹' B)) =
      iidOffspringLaw μ (firstWeakRecordEvent q) * iidOffspringLaw μ B := by
  obtain ⟨A, hA⟩ := firstWeakRecordEvent_eq_prefix_preimage q
  rw [hA]
  exact iid_prefix_recordTail_factorization μ q A B hB

end
end SubcriticalCauchy.Bienayme

namespace SubcriticalCauchy.Bienayme
noncomputable section

/-- Zero count is exactly absence of any positive weak record. -/
theorem infiniteWeakRecordCount_eq_zero_iff (ω : ℕ → ℕ) :
    infiniteWeakRecordCount ω = 0 ↔ weakRecordTimes ω = ∅ := by
  classical
  rw [infiniteWeakRecordCount, ENNReal.tsum_eq_zero]
  constructor
  · intro h
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro k hk
    have hh := h k
    rw [Set.indicator_of_mem hk] at hh
    exact one_ne_zero hh
  · intro h k
    simp [h]

/-- Every path with a nonzero count has a first positive weak record. -/
theorem exists_firstWeakRecordEvent_of_count_ne_zero (ω : ℕ → ℕ)
    (hω : infiniteWeakRecordCount ω ≠ 0) : ∃ q, ω ∈ firstWeakRecordEvent q := by
  classical
  have hex : ∃ q, q ∈ weakRecordTimes ω := by
    by_contra hn
    apply hω
    apply (infiniteWeakRecordCount_eq_zero_iff ω).mpr
    exact Set.eq_empty_iff_forall_notMem.mpr (not_exists.mp hn)
  exact ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩

/-- Distinct first-record times are disjoint events. -/
theorem firstWeakRecordEvent_pairwise_disjoint : Pairwise (fun q k =>
    Disjoint (firstWeakRecordEvent q) (firstWeakRecordEvent k)) := by
  intro q k hqk
  apply Set.disjoint_left.mpr
  intro ω hq hk
  rcases lt_or_gt_of_ne hqk with h | h
  · exact hk.2 q h hq.1
  · exact hq.2 k h hk.1

/-- At the first weak record the entire extended count renews. The overshoot
is retained in the walk splitting identity and cancels in record comparisons. -/
theorem infiniteWeakRecordCount_first_record (ω : ℕ → ℕ) {q : ℕ}
    (hq : ω ∈ firstWeakRecordEvent q) :
    infiniteWeakRecordCount ω = 1 + infiniteWeakRecordCount (recordTail q ω) := by
  classical
  let f : ℕ → ℝ≥0∞ := (weakRecordTimes ω).indicator (fun _ => 1)
  let g : ℕ → ℝ≥0∞ := (weakRecordTimes (recordTail q ω)).indicator (fun _ => 1)
  have hz : ∑ i ∈ Finset.range q, f i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact Set.indicator_of_notMem (hq.2 i (Finset.mem_range.mp hi)) _
  have hfq : f q = 1 := Set.indicator_of_mem hq.1 _
  have hg0 : g 0 = 0 := by simp [g, weakRecordTimes]
  have hp : (∑' k, f k) = ∑' k, f (k + q) := by
    have hh : (∑ i ∈ Finset.range q, f i) + (∑' k, f (k + q)) = ∑' k, f k :=
      Summable.sum_add_tsum_nat_add' (f := f) (k := q) ENNReal.summable
    rw [hz, zero_add] at hh
    exact hh.symm
  have ht : (∑' k, f (k + q)) = 1 + ∑' k, f (k + 1 + q) := by
    rw [tsum_eq_zero_add' ENNReal.summable]
    simp only [zero_add, hfq]
  have hg : (∑' k, g k) = ∑' k, g (k + 1) := by
    rw [tsum_eq_zero_add' ENNReal.summable, hg0, zero_add]
  have hs (k : ℕ) : f (k + 1 + q) = g (k + 1) := by
    have he := weakRecordTime_add_iff_shift ω hq.1 (Nat.zero_lt_succ k)
    change (weakRecordTimes ω).indicator (fun _ => (1 : ℝ≥0∞)) (k + 1 + q) =
      (weakRecordTimes (recordTail q ω)).indicator (fun _ => 1) (k + 1)
    simp only [Set.indicator_apply, show k + 1 + q = q + (k + 1) by omega]
    rw [he]
    rfl
  change (∑' k, f k) = 1 + ∑' k, g k
  rw [hp, ht, hg]
  exact congrArg (fun x : ℝ≥0∞ => 1 + x) (tsum_congr hs)

end
end SubcriticalCauchy.Bienayme
