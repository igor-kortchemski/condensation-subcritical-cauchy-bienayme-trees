module

public import SubcriticalCauchy.ExplorationLaw
public import SubcriticalCauchy.WeakRecordRenewalAux
public import Mathlib.Data.Fin.Rev

/-! # Finite-horizon approximation of the infinite weak-record count

The coupling here uses forward prefixes of a single iid sequence. Reversal
will be used only through equality of finite-dimensional laws.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme
noncomputable section

/-- The shared list statistic is exactly the number of infinite-walk record
 times in the finite horizon. -/
theorem weakRecordCount_prefix_eq (ω : ℕ → ℕ) (N : ℕ) :
    weakRecordCount (BGW.stepWord (fun i : Fin N => ω i)) =
      (by classical exact ((Finset.range (N + 1)).filter fun k => k ∈ weakRecordTimes ω).card) := by
  classical
  unfold weakRecordCount
  simp only [BGW.stepWord, List.length_ofFn]
  congr 1
  apply Finset.filter_congr
  intro k hk
  have hkN : k ≤ N := by have := Finset.mem_range.mp hk; omega
  change (0 < k ∧ ∀ i < k, prefixSum (BGW.stepWord (fun i : Fin N => ω i)) i ≤
    prefixSum (BGW.stepWord (fun i : Fin N => ω i)) k) ↔ _
  rw [prefixSum_stepWord_prefix ω hkN]
  constructor
  · rintro ⟨hpos, h⟩
    refine ⟨hpos, fun i hi => ?_⟩
    simpa only [prefixSum_stepWord_prefix ω (hi.le.trans hkN)] using h i hi
  · rintro ⟨hpos, h⟩
    refine ⟨hpos, fun i hi => ?_⟩
    simpa only [prefixSum_stepWord_prefix ω (hi.le.trans hkN)] using h i hi

/-- Forward finite-prefix counts eventually equal the total count on every
path with finitely many weak records. -/
theorem weakRecordCount_prefix_eventually_eq (ω : ℕ → ℕ)
    (hω : (weakRecordTimes ω).Finite) :
    ∀ᶠ N : ℕ in atTop,
      (weakRecordCount (BGW.stepWord (fun i : Fin N => ω i)) : ℝ≥0∞) =
        infiniteWeakRecordCount ω := by
  classical
  obtain ⟨K, hK⟩ := hω.bddAbove
  filter_upwards [eventually_ge_atTop K] with N hN
  rw [weakRecordCount_prefix_eq, infiniteWeakRecordCount_eq_ncard ω hω,
    Set.ncard_eq_toFinset_card _ hω]
  have hs : ((Finset.range (N + 1)).filter fun k => k ∈ weakRecordTimes ω) = hω.toFinset := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Set.Finite.mem_toFinset]
    exact ⟨fun h => h.2, fun hk => ⟨by have := hK hk; omega, hk⟩⟩
  rw [hs]

/-- Almost-sure stabilization applies to forward counts. It does not assert
pathwise stabilization of reversed prefixes on this same sample. -/
theorem iid_weakRecordCount_prefix_eventually_eq_ae (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (hm : offspringMean μ < 1) :
    ∀ᵐ ω ∂iidOffspringLaw μ, ∀ᶠ N : ℕ in atTop,
      (weakRecordCount (BGW.stepWord (fun i : Fin N => ω i)) : ℝ≥0∞) =
        infiniteWeakRecordCount ω := by
  filter_upwards [iid_weakRecordTimes_finite_ae μ hm] with ω hω
  exact weakRecordCount_prefix_eventually_eq ω hω

/-- Coordinate reversal reverses the increment word exactly. -/
theorem stepWord_rev {N : ℕ} (ω : Fin N → ℕ) :
    BGW.stepWord (fun i => ω i.rev) = (BGW.stepWord ω).reverse := by
  apply List.ext_getElem
  · simp [BGW.stepWord]
  · intro i hi hj
    simp [BGW.stepWord, Fin.rev, List.getElem_reverse, Nat.sub_sub, Nat.add_comm]

/-- Coordinate reversal as the product measurable equivalence. -/
theorem piCongrLeft_rev_apply {N : ℕ} (ω : Fin N → ℕ) :
    MeasurableEquiv.piCongrLeft (fun _ : Fin N => ℕ) Fin.revPerm ω =
      (fun i => ω i.rev) := by
  funext i
  simpa only [Fin.revPerm_apply, Fin.rev_rev] using
    MeasurableEquiv.piCongrLeft_apply_apply Fin.revPerm (β := fun _ : Fin N => ℕ) ω i.rev

/-- Reversal preserves the iid record-count distribution at each finite horizon. -/
theorem pi_weakRecordCount_reverse (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (N j : ℕ) :
    (Measure.pi (fun _ : Fin N => μ))
        {ω | weakRecordCount (BGW.stepWord ω).reverse = j} =
      (Measure.pi (fun _ : Fin N => μ))
        {ω | weakRecordCount (BGW.stepWord ω) = j} := by
  have hp := measurePreserving_piCongrLeft (α := fun _ : Fin N => ℕ)
    (fun _ : Fin N => μ) (Fin.revPerm (n := N))
  have he := hp.measure_preimage
    ((Set.to_countable {ω : Fin N → ℕ | weakRecordCount (BGW.stepWord ω) = j}).measurableSet.nullMeasurableSet)
  convert he using 1
  congr 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, piCongrLeft_rev_apply, stepWord_rev]

/-- Finite-prefix counts converge in law to the actual total record count.
This does not yet identify that limiting law as geometric. -/
theorem iid_weakRecordCount_prefix_probability_tendsto (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (hm : offspringMean μ < 1) (j : ℕ) :
    Tendsto (fun N : ℕ => (Measure.pi (fun _ : Fin N => μ))
      {ω | weakRecordCount (BGW.stepWord ω) = j}) atTop
      (𝓝 (iidOffspringLaw μ {ω | infiniteWeakRecordCount ω = (j : ℝ≥0∞)})) := by
  have hp : ∀ N : ℕ, Measurable (fun (ω : ℕ → ℕ) (i : Fin N) => ω i) :=
    fun _ => measurable_pi_iff.mpr fun i => measurable_pi_apply (i : ℕ)
  have hc (N : ℕ) : Measurable
      (fun ω : ℕ → ℕ => weakRecordCount (BGW.stepWord (fun i : Fin N => ω i))) :=
    (measurable_of_countable (fun v : Fin N → ℕ => weakRecordCount (BGW.stepWord v))).comp (hp N)
  have ht := tendsto_measure_nat_eq_of_ae_eventually_cast_eq (iidOffspringLaw μ)
    (fun N ω => weakRecordCount (BGW.stepWord (fun i : Fin N => ω i)))
    infiniteWeakRecordCount hc measurable_infiniteWeakRecordCount
    (iid_weakRecordCount_prefix_eventually_eq_ae μ hm) j
  apply ht.congr'
  exact Eventually.of_forall fun N =>
    iidOffspringLaw_prefix_event μ N {ω | weakRecordCount (BGW.stepWord ω) = j}

/-- The reversed finite iid list statistic has the same distributional limit.
No almost-sure convergence of reversed prefixes of one fixed sample is used. -/
theorem iid_reversed_weakRecordCount_probability_tendsto (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (hm : offspringMean μ < 1) (j : ℕ) :
    Tendsto (fun N : ℕ => (Measure.pi (fun _ : Fin N => μ))
      {ω | weakRecordCount (List.ofFn (fun i => (ω i : ℤ) - 1)).reverse = j}) atTop
      (𝓝 (iidOffspringLaw μ {ω | infiniteWeakRecordCount ω = (j : ℝ≥0∞)})) := by
  change Tendsto (fun N : ℕ => (Measure.pi (fun _ : Fin N => μ))
    {ω | weakRecordCount (BGW.stepWord ω).reverse = j}) _ _
  simp_rw [pi_weakRecordCount_reverse]
  exact iid_weakRecordCount_prefix_probability_tendsto μ hm j

/-- On paths that hit `-1`, the first hit exceeds `k` exactly when all
prefixes through `k` are nonnegative. -/
theorem walkFirstPassage_gt_iff_nonnegative (ω : ℕ → ℕ)
    (h : ∃ n, walkSum ω n = -1) (k : ℕ) :
    k < walkFirstPassage ω 1 ↔ ∀ i ≤ k, 0 ≤ walkSum ω i := by
  constructor
  · intro hk i hi
    exact walkSum_nonneg_before_firstPassage ω (hi.trans_lt hk)
  · intro hp
    by_contra hn
    have ht : walkFirstPassage ω 1 ≤ k := by omega
    have := hp _ ht
    rw [walkFirstPassage_spec ω 1 (by simpa using h)] at this
    norm_num at this

/-- The finite-prefix marginal transfers the terminal reversal identity to
positive-time weak records of the actual infinite walk. -/
theorem iid_weakRecordTime_probability_eq_tail (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ < 1) (k : ℕ) (hk : 1 ≤ k) :
    iidOffspringLaw μ {ω | k ∈ weakRecordTimes ω} =
      iidOffspringLaw μ {ω | k < walkFirstPassage ω 1} := by
  let A : Set (Fin k → ℕ) := {ω | 0 < k ∧ ∀ i < k,
    prefixSum (BGW.stepWord ω) i ≤ prefixSum (BGW.stepWord ω) k}
  let B : Set (Fin k → ℕ) := {ω | 0 < k ∧ ∀ i < k,
    prefixSum (BGW.stepWord ω).reverse i ≤ prefixSum (BGW.stepWord ω).reverse k}
  have hA : (Measure.pi (fun _ : Fin k => μ)) A =
      (Measure.pi (fun _ : Fin k => μ)) B := by
    have hp := measurePreserving_piCongrLeft (α := fun _ : Fin k => ℕ)
      (fun _ : Fin k => μ) (Fin.revPerm (n := k))
    have he := hp.measure_preimage (Set.to_countable A).measurableSet.nullMeasurableSet
    have hs : (MeasurableEquiv.piCongrLeft (fun _ : Fin k => ℕ) Fin.revPerm) ⁻¹' A = B := by
      ext ω
      simp only [Set.mem_preimage, piCongrLeft_rev_apply]
      change (0 < k ∧ ∀ i < k,
        prefixSum (BGW.stepWord (fun j => ω j.rev)) i ≤
          prefixSum (BGW.stepWord (fun j => ω j.rev)) k) ↔ _
      rw [stepWord_rev]
      rfl
    rw [hs] at he
    exact he.symm
  calc
    _ = iidOffspringLaw μ ((fun ω (i : Fin k) => ω i) ⁻¹' A) := by
      congr 1
      ext ω
      change (0 < k ∧ ∀ i < k, walkSum ω i ≤ walkSum ω k) ↔ _
      dsimp [A]
      rw [prefixSum_stepWord_prefix ω le_rfl]
      constructor
      · rintro ⟨hpos, hi⟩
        exact ⟨hpos, fun i hik => by simpa only [prefixSum_stepWord_prefix ω hik.le] using hi i hik⟩
      · rintro ⟨hpos, hi⟩
        exact ⟨hpos, fun i hik => by simpa only [prefixSum_stepWord_prefix ω hik.le] using hi i hik⟩
    _ = (Measure.pi (fun _ : Fin k => μ)) A := iidOffspringLaw_prefix_event μ k A
    _ = (Measure.pi (fun _ : Fin k => μ)) B := hA
    _ = (Measure.pi (fun _ : Fin k => μ))
        {ω | ∀ j ≤ k, 0 ≤ prefixSum (BGW.stepWord ω) j} :=
      (iid_reversal_record_probability μ k hk).1
    _ = iidOffspringLaw μ {ω | ∀ j ≤ k, 0 ≤ walkSum ω j} := by
      rw [← iidOffspringLaw_prefix_event μ k {ω | ∀ j ≤ k, 0 ≤ prefixSum (BGW.stepWord ω) j}]
      congr 1
      ext ω
      change (∀ j ≤ k, 0 ≤ prefixSum (BGW.stepWord (fun i : Fin k => ω i)) j) ↔ _
      constructor
      · intro h j hj
        simpa only [prefixSum_stepWord_prefix ω hj] using h j hj
      · intro h j hj
        simpa only [prefixSum_stepWord_prefix ω hj] using h j hj
    _ = _ := by
      apply measure_congr
      filter_upwards [iid_walk_hits_negative_level_ae μ hm 1] with ω hω
      exact propext (walkFirstPassage_gt_iff_nonnegative ω (by simpa using hω) k).symm

/-- Tonelli's formula for the actual total count of weak record times. -/
theorem lintegral_infiniteWeakRecordCount_eq_tsum (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    (∫⁻ ω, infiniteWeakRecordCount ω ∂iidOffspringLaw μ) =
      ∑' k : ℕ, iidOffspringLaw μ {ω | k ∈ weakRecordTimes ω} := by
  unfold infiniteWeakRecordCount
  rw [lintegral_tsum]
  · exact tsum_congr fun k => lintegral_indicator_one (measurableSet_weakRecordTime k)
  · intro k
    exact (measurable_const.indicator (measurableSet_weakRecordTime k)).aemeasurable

/-- The expected total record count plus one is the expected first passage.
This identifies the mean without assuming the geometric renewal law. -/
theorem lintegral_infiniteWeakRecordCount_add_one (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ < 1) :
    (∫⁻ ω, infiniteWeakRecordCount ω ∂iidOffspringLaw μ) + 1 =
      ENNReal.ofReal (1 / (1 - (offspringMean μ).toReal)) := by
  have hz : iidOffspringLaw μ {ω | 0 < walkFirstPassage ω 1} = 1 := by
    have hae : ∀ᵐ ω ∂iidOffspringLaw μ, 0 < walkFirstPassage ω 1 := by
      filter_upwards [iid_walk_hits_negative_level_ae μ hm 1] with ω hω
      have hs := walkFirstPassage_spec ω 1 hω
      by_contra hn
      have ht : walkFirstPassage ω 1 = 0 := by omega
      simp [ht, walkSum] at hs
    simpa only [measure_univ] using (ae_iff_measure_eq
      (measurableSet_lt measurable_const (measurable_walkFirstPassage 1)).nullMeasurableSet).mp hae
  rw [lintegral_infiniteWeakRecordCount_eq_tsum,
    tsum_eq_zero_add' ENNReal.summable]
  have hzero : iidOffspringLaw μ {ω | 0 ∈ weakRecordTimes ω} = 0 := by
    simp [weakRecordTimes]
  rw [hzero, zero_add]
  simp_rw [iid_weakRecordTime_probability_eq_tail μ hm _ (Nat.succ_le_succ (Nat.zero_le _))]
  rw [add_comm, ← hz]
  have ht := tsum_iid_walkFirstPassage_one_tail μ hm
  rw [tsum_eq_zero_add' ENNReal.summable] at ht
  exact ht

end
end SubcriticalCauchy.Bienayme

namespace SubcriticalCauchy.Bienayme
noncomputable section

/-- Probability of at least one positive-time weak record. -/
def weakRecordReturnProbability (μ : Measure ℕ) [IsProbabilityMeasure μ] : ℝ≥0∞ :=
  iidOffspringLaw μ {ω | infiniteWeakRecordCount ω ≠ 0}

theorem measurableSet_weakRecordReturn : MeasurableSet
    {ω : ℕ → ℕ | infiniteWeakRecordCount ω ≠ 0} := by
  simpa only [← Set.compl_ofPred] using
    (measurableSet_eq_fun measurable_infiniteWeakRecordCount measurable_const).compl

/-- The return event is partitioned by its first positive weak record. -/
theorem weakRecordReturn_eq_iUnion_first :
    {ω : ℕ → ℕ | infiniteWeakRecordCount ω ≠ 0} = ⋃ q, firstWeakRecordEvent q := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · exact exists_firstWeakRecordEvent_of_count_ne_zero ω
  · rintro ⟨q, hq⟩ he
    have hh := (infiniteWeakRecordCount_eq_zero_iff ω).mp he
    have hmem := hq.1
    rw [hh] at hmem
    exact hmem

/-- The total probability of all first-record events is the return probability. -/
theorem weakRecordReturnProbability_eq_tsum (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    weakRecordReturnProbability μ = ∑' q, iidOffspringLaw μ (firstWeakRecordEvent q) := by
  rw [weakRecordReturnProbability, weakRecordReturn_eq_iUnion_first,
    measure_iUnion firstWeakRecordEvent_pairwise_disjoint measurableSet_firstWeakRecordEvent]

/-- The zero atom is the no-return probability. -/
theorem iid_infiniteWeakRecordCount_zero (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    iidOffspringLaw μ {ω | infiniteWeakRecordCount ω = 0} = 1 - weakRecordReturnProbability μ := by
  have hs : {ω : ℕ → ℕ | infiniteWeakRecordCount ω = 0} =
      {ω | infiniteWeakRecordCount ω ≠ 0}ᶜ := by ext ω; simp
  rw [hs, measure_compl measurableSet_weakRecordReturn (measure_ne_top _ _), measure_univ]
  rfl

/-- Renewal of every finite count atom. Arbitrary overshoots are covered by
`infiniteWeakRecordCount_first_record`. -/
theorem iid_infiniteWeakRecordCount_succ (μ : Measure ℕ) [IsProbabilityMeasure μ] (j : ℕ) :
    iidOffspringLaw μ {ω | infiniteWeakRecordCount ω = ((j + 1 : ℕ) : ℝ≥0∞)} =
      weakRecordReturnProbability μ *
        iidOffspringLaw μ {ω | infiniteWeakRecordCount ω = (j : ℝ≥0∞)} := by
  classical
  let B : Set (ℕ → ℕ) := {ω | infiniteWeakRecordCount ω = (j : ℝ≥0∞)}
  have hB : MeasurableSet B := measurableSet_eq_fun measurable_infiniteWeakRecordCount measurable_const
  have hs : {ω | infiniteWeakRecordCount ω = ((j + 1 : ℕ) : ℝ≥0∞)} =
      ⋃ q, firstWeakRecordEvent q ∩ (recordTail q ⁻¹' B) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · intro he
      have hn : infiniteWeakRecordCount ω ≠ 0 := by rw [he]; simp
      obtain ⟨q, hq⟩ := exists_firstWeakRecordEvent_of_count_ne_zero ω hn
      refine ⟨q, hq, ?_⟩
      have hh : 1 + infiniteWeakRecordCount (recordTail q ω) = 1 + (j : ℝ≥0∞) := by
        rw [← infiniteWeakRecordCount_first_record ω hq, he]
        simp [add_comm]
      exact (ENNReal.add_right_inj ENNReal.one_ne_top).mp hh
    · rintro ⟨q, hq, ht⟩
      rw [infiniteWeakRecordCount_first_record ω hq]
      change infiniteWeakRecordCount (recordTail q ω) = (j : ℝ≥0∞) at ht
      rw [ht]
      simp [add_comm]
  rw [hs, measure_iUnion
    (fun q k hqk => (firstWeakRecordEvent_pairwise_disjoint hqk).mono
      Set.inter_subset_left Set.inter_subset_left)
    (fun q => (measurableSet_firstWeakRecordEvent q).inter
      (hB.preimage (measurable_recordTail q)))]
  simp_rw [iid_firstWeakRecord_tail_factorization μ _ B hB]
  rw [ENNReal.tsum_mul_right, ← weakRecordReturnProbability_eq_tsum]

/-- The finite atoms of the total record count are geometric with the actual
return probability. Subcriticality is not needed for this renewal identity. -/
theorem iid_infiniteWeakRecordCount_geometric_return (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (j : ℕ) :
    iidOffspringLaw μ {ω | infiniteWeakRecordCount ω = (j : ℝ≥0∞)} =
      (1 - weakRecordReturnProbability μ) * weakRecordReturnProbability μ ^ j := by
  induction j with
  | zero => simpa using iid_infiniteWeakRecordCount_zero μ
  | succ j ih =>
    rw [iid_infiniteWeakRecordCount_succ, ih, pow_succ]
    ac_rfl

end
end SubcriticalCauchy.Bienayme

namespace SubcriticalCauchy.Bienayme
noncomputable section

/-- Atom expansion for an extended-valued variable that is a natural number
almost surely. The added constant also permits expansion of its mean plus one. -/
theorem lintegral_add_const_eq_tsum_nat_atoms {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (F : Ω → ℝ≥0∞) (hF : Measurable F)
    (hnat : ∀ᵐ ω ∂ν, ∃ n : ℕ, F ω = (n : ℝ≥0∞)) (a : ℝ≥0∞) :
    (∫⁻ ω, F ω + a ∂ν) =
      ∑' n : ℕ, ((n : ℝ≥0∞) + a) * ν {ω | F ω = (n : ℝ≥0∞)} := by
  classical
  calc
    _ = ∫⁻ ω, ∑' n : ℕ, {ω | F ω = (n : ℝ≥0∞)}.indicator
        (fun _ => (n : ℝ≥0∞) + a) ω ∂ν := by
      apply lintegral_congr_ae
      filter_upwards [hnat] with ω hω
      obtain ⟨n, hn⟩ := hω
      rw [tsum_eq_single n]
      · rw [Set.indicator_of_mem (s := {ω | F ω = (n : ℝ≥0∞)}) hn, hn]
      · intro k hkn
        apply Set.indicator_of_notMem
        intro hk
        exact hkn (Nat.cast_injective (hk.symm.trans hn))
    _ = _ := by
      rw [lintegral_tsum]
      · apply tsum_congr
        intro n
        rw [lintegral_indicator (measurableSet_eq_fun hF measurable_const)]
        simp
      · intro n
        exact (measurable_const.indicator (measurableSet_eq_fun hF measurable_const)).aemeasurable

end
end SubcriticalCauchy.Bienayme

namespace SubcriticalCauchy.Bienayme
noncomputable section

/-- Renewal of the mean, obtained from the finite-atom recurrence and almost
sure finiteness. No weighted geometric-series identity is assumed. -/
theorem iid_infiniteWeakRecordCount_mean_renewal (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ < 1) :
    (∫⁻ ω, infiniteWeakRecordCount ω ∂iidOffspringLaw μ) =
      weakRecordReturnProbability μ *
        ((∫⁻ ω, infiniteWeakRecordCount ω ∂iidOffspringLaw μ) + 1) := by
  let E : ℝ≥0∞ := ∫⁻ ω, infiniteWeakRecordCount ω ∂iidOffspringLaw μ
  let p : ℕ → ℝ≥0∞ := fun n => iidOffspringLaw μ {ω | infiniteWeakRecordCount ω = (n : ℝ≥0∞)}
  have hnat : ∀ᵐ ω ∂iidOffspringLaw μ, ∃ n : ℕ, infiniteWeakRecordCount ω = (n : ℝ≥0∞) := by
    filter_upwards [iid_weakRecordTimes_finite_ae μ hm] with ω hω
    exact ⟨(weakRecordTimes ω).ncard, infiniteWeakRecordCount_eq_ncard ω hω⟩
  have h0 : E = ∑' n : ℕ, (n : ℝ≥0∞) * p n := by
    simpa only [add_zero] using lintegral_add_const_eq_tsum_nat_atoms (iidOffspringLaw μ)
      infiniteWeakRecordCount measurable_infiniteWeakRecordCount hnat 0
  have h1 : E + 1 = ∑' n : ℕ, ((n : ℝ≥0∞) + 1) * p n := by
    have hh := lintegral_add_const_eq_tsum_nat_atoms (iidOffspringLaw μ)
      infiniteWeakRecordCount measurable_infiniteWeakRecordCount hnat 1
    rw [lintegral_add_left measurable_infiniteWeakRecordCount, lintegral_const,
      measure_univ, mul_one] at hh
    exact hh
  have hp (n : ℕ) : p (n + 1) = weakRecordReturnProbability μ * p n :=
    iid_infiniteWeakRecordCount_succ μ n
  change E = weakRecordReturnProbability μ * (E + 1)
  calc
    E = ∑' n : ℕ, (n : ℝ≥0∞) * p n := h0
    _ = ∑' n : ℕ, ((n : ℝ≥0∞) + 1) * p (n + 1) := by
      rw [tsum_eq_zero_add' ENNReal.summable]
      simp only [Nat.cast_zero, zero_mul, zero_add, Nat.cast_add, Nat.cast_one]
    _ = weakRecordReturnProbability μ * ∑' n : ℕ, ((n : ℝ≥0∞) + 1) * p n := by
      simp_rw [hp]
      rw [← ENNReal.tsum_mul_left]
      exact tsum_congr fun n => by ac_rfl
    _ = weakRecordReturnProbability μ * (E + 1) :=
      congrArg (fun x : ℝ≥0∞ => weakRecordReturnProbability μ * x) h1.symm

/-- The record-return probability is the offspring mean. The identification
uses the proved renewal and exploration mean identities. -/
theorem weakRecordReturnProbability_eq_offspringMean (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ < 1) : weakRecordReturnProbability μ = offspringMean μ := by
  let E : ℝ≥0∞ := ∫⁻ ω, infiniteWeakRecordCount ω ∂iidOffspringLaw μ
  have hmean : E + 1 = ENNReal.ofReal (1 / (1 - (offspringMean μ).toReal)) :=
    lintegral_infiniteWeakRecordCount_add_one μ hm
  have hrenew : E = weakRecordReturnProbability μ * (E + 1) :=
    iid_infiniteWeakRecordCount_mean_renewal μ hm
  have hEfin : E ≠ ∞ := (ENNReal.add_ne_top.mp
    (show E + 1 ≠ ∞ by rw [hmean]; exact ENNReal.ofReal_ne_top)).1
  have hmfin : offspringMean μ ≠ ∞ := ne_top_of_lt (hm.trans ENNReal.one_lt_top)
  have hmR : (offspringMean μ).toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hmfin ENNReal.one_ne_top).mpr hm
  have hγpos : 0 < 1 - (offspringMean μ).toReal := sub_pos.mpr hmR
  have hmeanR : E.toReal + 1 = 1 / (1 - (offspringMean μ).toReal) := by
    have hh := congrArg ENNReal.toReal hmean
    rw [ENNReal.toReal_add hEfin ENNReal.one_ne_top, ENNReal.toReal_one,
      ENNReal.toReal_ofReal (le_of_lt (one_div_pos.mpr hγpos))] at hh
    exact hh
  have hrenewR : E.toReal = (weakRecordReturnProbability μ).toReal * (E.toReal + 1) := by
    have hh := congrArg ENNReal.toReal hrenew
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_add hEfin ENNReal.one_ne_top,
      ENNReal.toReal_one] using hh
  have hprod : (E.toReal + 1) * (1 - (offspringMean μ).toReal) = 1 :=
    (eq_div_iff (ne_of_gt hγpos)).mp hmeanR
  have heq : (weakRecordReturnProbability μ).toReal * (E.toReal + 1) =
      (offspringMean μ).toReal * (E.toReal + 1) := by
    nlinarith only [hrenewR, hprod]
  have hX : E.toReal + 1 ≠ 0 := ne_of_gt (by positivity)
  have hrR : (weakRecordReturnProbability μ).toReal = (offspringMean μ).toReal :=
    mul_right_cancel₀ hX heq
  exact (ENNReal.toReal_eq_toReal_iff'
    (show weakRecordReturnProbability μ ≠ ∞ from measure_ne_top _ _) hmfin).mp hrR

/-- The total positive-time weak record count has the paper's geometric law. -/
theorem iid_infiniteWeakRecordCount_geometric (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ < 1) (j : ℕ) :
    iidOffspringLaw μ {ω | infiniteWeakRecordCount ω = (j : ℝ≥0∞)} =
      ENNReal.ofReal ((1 - (offspringMean μ).toReal) * (offspringMean μ).toReal ^ j) := by
  have hmfin : offspringMean μ ≠ ∞ := ne_top_of_lt (hm.trans ENNReal.one_lt_top)
  have hmR : (offspringMean μ).toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hmfin ENNReal.one_ne_top).mpr hm
  rw [iid_infiniteWeakRecordCount_geometric_return, weakRecordReturnProbability_eq_offspringMean μ hm]
  rw [ENNReal.ofReal_mul (sub_nonneg.mpr hmR.le),
    ENNReal.ofReal_sub 1 ENNReal.toReal_nonneg,
    ENNReal.ofReal_pow ENNReal.toReal_nonneg j, ENNReal.ofReal_one,
    ENNReal.ofReal_toReal hmfin]

/-- Geometric finite-horizon form for M3, with exactly the shared reversed-list
statistic and the finite iid offspring law. -/
theorem iid_reversed_weakRecordCount_geometric_tendsto (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (hm : offspringMean μ < 1) (j : ℕ) :
    Tendsto (fun N : ℕ => (Measure.pi (fun _ : Fin N => μ))
      {ω | weakRecordCount (List.ofFn (fun i => (ω i : ℤ) - 1)).reverse = j}) atTop
      (𝓝 (ENNReal.ofReal ((1 - (offspringMean μ).toReal) * (offspringMean μ).toReal ^ j))) := by
  have hh := iid_reversed_weakRecordCount_probability_tendsto μ hm j
  rw [iid_infiniteWeakRecordCount_geometric μ hm j] at hh
  exact hh

end
end SubcriticalCauchy.Bienayme
