module

public import SubcriticalCauchy.M3Transfer
public import SubcriticalCauchy.WeakRecordRenewal
public import Mathlib.MeasureTheory.Measure.Continuity

/-!
# Infinite-walk tail estimate for exterior tightness

The last zero of a finite reversed word is dominated by the last nonnegative
time of the infinite offspring walk.  Negative drift makes the latter finite
almost surely; continuity from above gives convergence of its tail
probabilities, uniformly over the finite word lengths.
-/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

open BGW
noncomputable section

/-- A last zero exceeds `K` exactly when some zero prefix time exceeds `K`. -/
theorem lastZero_gt_iff (x : List ℤ) (K : ℕ) :
    K < lastZero x ↔ ∃ j : ℕ, K < j ∧ j ≤ x.length ∧ prefixSum x j = 0 := by
  classical
  let s := (Finset.range (x.length + 1)).filter fun k => prefixSum x k = 0
  have hs : s.Nonempty := ⟨0, Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (Nat.zero_lt_succ _), by simp [prefixSum]⟩⟩
  constructor
  · intro h
    obtain ⟨j, hj, hsup⟩ := Finset.exists_mem_eq_sup s hs id
    have hjs : lastZero x = j := by simpa [lastZero, s] using hsup
    obtain ⟨hjrange, hzero⟩ := Finset.mem_filter.mp hj
    exact ⟨j, hjs ▸ h, by have := Finset.mem_range.mp hjrange; omega, hzero⟩
  · rintro ⟨j, hK, hj, hzero⟩
    apply lt_of_lt_of_le hK
    exact Finset.le_sup (f := id) (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), hzero⟩)

/-- Positive and zero times of the infinite offspring walk. -/
def nonnegativeWalkTimes (ω : ℕ → ℕ) : Set ℕ := {j | 0 ≤ walkSum ω j}

/-- The part of the nonnegative walk-time set after time `K`. -/
def walkNonnegativeTail (K : ℕ) : Set (ℕ → ℕ) :=
  {ω | ∃ j : ℕ, K < j ∧ 0 ≤ walkSum ω j}

/-- Negative drift confines all nonnegative walk times to an initial segment. -/
theorem nonnegativeWalkTimes_finite_of_negative_drift (ω : ℕ → ℕ) {a : ℝ}
    (ha : a < 0) (hω : Tendsto (fun n => walkAverage n ω) atTop (𝓝 a)) :
    (nonnegativeWalkTimes ω).Finite := by
  have hneg := hω.eventually (eventually_lt_nhds ha)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hneg
  apply (Finset.range N).finite_toSet.subset
  intro j hj
  have hsum : 0 ≤ walkSum ω j := hj
  have hjN : j < N := by
    by_contra hn
    have hav := hN j (by omega)
    have hnonneg : 0 ≤ walkAverage j ω :=
      div_nonneg (by exact_mod_cast hsum) (Nat.cast_nonneg _)
    exact (not_lt_of_ge hnonneg) hav
  exact Finset.mem_range.mpr hjN

/-- Subcriticality makes the nonnegative walk-time set almost surely finite. -/
theorem iid_nonnegativeWalkTimes_finite_ae (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ < 1) :
    ∀ᵐ ω ∂iidOffspringLaw μ, (nonnegativeWalkTimes ω).Finite := by
  have hfin := ne_top_of_lt (hm.trans ENNReal.one_lt_top)
  have hmR : (offspringMean μ).toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hfin ENNReal.one_ne_top).mpr hm
  filter_upwards [walkAverage_ae_tendsto μ hfin] with ω hω
  exact nonnegativeWalkTimes_finite_of_negative_drift ω (sub_neg.mpr hmR) hω

theorem measurableSet_walkNonnegativeTail (K : ℕ) :
    MeasurableSet (walkNonnegativeTail K) := by
  unfold walkNonnegativeTail
  simp only [Set.ofPred_exists]
  refine MeasurableSet.iUnion fun j => ?_
  by_cases hj : K < j
  · simp only [hj, true_and]
    exact measurableSet_le measurable_const (measurable_walkSum j)
  · simp [hj]

/-- The probability of a nonnegative walk time after `K` tends to zero. -/
theorem iid_walkNonnegativeTail_real_tendsto_zero
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ < 1) :
    Tendsto (fun K => (iidOffspringLaw μ).real (walkNonnegativeTail K))
      atTop (𝓝 0) := by
  have hanti : Antitone walkNonnegativeTail := by
    intro K L hKL ω hω
    obtain ⟨j, hj, hsum⟩ := hω
    exact ⟨j, lt_of_le_of_lt hKL hj, hsum⟩
  have hsub : (⋂ K, walkNonnegativeTail K) ⊆
      {ω | ¬ (nonnegativeWalkTimes ω).Finite} := by
    intro ω hω hfin
    apply Set.infinite_of_forall_exists_gt (s := nonnegativeWalkTimes ω) _ hfin
    intro K
    obtain ⟨j, hj, hsum⟩ := Set.mem_iInter.mp hω K
    exact ⟨j, hsum, hj⟩
  have hnull : iidOffspringLaw μ {ω | ¬ (nonnegativeWalkTimes ω).Finite} = 0 := by
    simpa only [ae_iff] using iid_nonnegativeWalkTimes_finite_ae μ hm
  have hinter : iidOffspringLaw μ (⋂ K, walkNonnegativeTail K) = 0 :=
    measure_mono_null hsub hnull
  have hcont := tendsto_measure_iInter_atTop
    (μ := iidOffspringLaw μ) (s := walkNonnegativeTail)
    (fun K => (measurableSet_walkNonnegativeTail K).nullMeasurableSet)
    hanti ⟨0, measure_ne_top _ _⟩
  rw [hinter] at hcont
  have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hcont
  simpa only [Function.comp_def, Measure.real, ENNReal.toReal_zero] using hreal

/-- Reversal preserves the law of the finite last-zero statistic. -/
theorem pi_lastZero_reverse_real (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (N K : ℕ) :
    (Measure.pi (fun _ : Fin N => μ)).real
        {ω | K < lastZero (BGW.stepWord ω).reverse} =
      (Measure.pi (fun _ : Fin N => μ)).real
        {ω | K < lastZero (BGW.stepWord ω)} := by
  apply congrArg ENNReal.toReal
  have hp := measurePreserving_piCongrLeft (α := fun _ : Fin N => ℕ)
    (fun _ : Fin N => μ) (Fin.revPerm (n := N))
  have he := hp.measure_preimage
    (Set.to_countable {ω : Fin N → ℕ | K < lastZero (BGW.stepWord ω)}).measurableSet.nullMeasurableSet
  convert he using 1
  congr 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, piCongrLeft_rev_apply, stepWord_rev]

/-- The finite iid reversed-word event is bounded by the infinite walk tail,
with no loss depending on the word length. -/
theorem pi_increment_lastZero_reverse_real_le_tail
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (N K : ℕ) :
    (Measure.pi (fun _ : Fin N => incrementLaw μ)).real
        {x | K < lastZero (List.ofFn x).reverse} ≤
      (iidOffspringLaw μ).real (walkNonnegativeTail K) := by
  have hinc :
      (Measure.pi (fun _ : Fin N => incrementLaw μ)).real
          {x | K < lastZero (List.ofFn x).reverse} =
        (Measure.pi (fun _ : Fin N => μ)).real
          {ω | K < lastZero (BGW.stepWord ω).reverse} := by
    rw [pi_incrementLaw_eq_map]
    rw [Measure.real, Measure.real, Measure.map_apply
      (measurable_of_countable _) (Set.to_countable _).measurableSet]
    simp only [Set.preimage_ofPred_eq, BGW.stepWord]
  rw [hinc, pi_lastZero_reverse_real]
  rw [Measure.real, ← iidOffspringLaw_prefix_event μ N
    {ω | K < lastZero (BGW.stepWord ω)}, ← Measure.real]
  apply measureReal_mono _ (measure_ne_top _ _)
  intro ω hω
  change K < lastZero (BGW.stepWord (fun i : Fin N => ω i)) at hω
  obtain ⟨j, hK, hjN, hzero⟩ := (lastZero_gt_iff _ _).mp hω
  refine ⟨j, hK, ?_⟩
  rw [← prefixSum_stepWord_prefix (n := N) ω (by simpa [BGW.stepWord] using hjN), hzero]

end
end SubcriticalCauchy.Bienayme
