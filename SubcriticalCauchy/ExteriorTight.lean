module

public import SubcriticalCauchy.ExteriorTightAux

/-!
# Tightness of the exterior size

The conditioned cyclic residual is compared with the iid increment word by
`M3Transfer`.  The remaining estimate is the uniform infinite-walk tail bound
proved in `ExteriorTightAux`.
-/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

open BGW BGW.LocallyFinite
noncomputable section

local instance exteriorTightInst1 : MeasurableSpace (List ℤ) := ⊤
local instance exteriorTightInst2 : MeasurableSingletonClass (List ℤ) := ⟨fun _ => trivial⟩

/-- At admissible positive sizes, the exterior-size event is bounded by an
infinite-walk tail and the two transfer errors. -/
theorem exteriorSize_conditioned_le_tail_add_errors
    (μ : Measure ℕ) [IsProbabilityMeasure μ] {n : ℕ} (hn : n ≠ 0)
    (hsize : bienaymeLaw μ (sizeEvent n) ≠ 0) (K : ℕ) :
    (conditioned μ n).real (finiteTreeEvent fun t => K < exteriorSize t) ≤
      (iidOffspringLaw μ).real (walkNonnegativeTail K) +
        tvDist
          ((MaximumSwapLaw.bridgeCountsLaw μ n).map
            (fun ω => cyclicResidual (stepWord ω)))
          ((Measure.pi fun _ : Fin (n - 1) => incrementLaw μ).map List.ofFn) +
        (conditioned μ n).real (finiteIncrementEvent fun x => ¬ uniqueWordMaximum x) := by
  let A : Set (List ℤ) := {x | K < lastZero x.reverse}
  let B := (MaximumSwapLaw.bridgeCountsLaw μ n).map
    (fun ω => cyclicResidual (stepWord ω))
  let Q := (Measure.pi fun _ : Fin (n - 1) => incrementLaw μ).map List.ofFn
  let _ : IsProbabilityMeasure (MaximumSwapLaw.bridgeCountsLaw μ n) :=
    BGW.isProbabilityMeasure_cond_pi_countBridges μ hn hsize
  let _ : IsProbabilityMeasure (incrementLaw μ) := by
    unfold incrementLaw
    infer_instance
  have htree : finiteTreeEvent (fun t => K < exteriorSize t) =
      finiteIncrementEvent (fun x => cyclicResidual x ∈ A) := by
    ext T
    constructor
    · rintro ⟨t, ht, rfl⟩
      change K < exteriorSize t at ht
      refine ⟨t, ?_, rfl⟩
      change K < lastZero (cyclicResidual t.increments).reverse
      simpa only [exteriorSize_eq_lastZero] using ht
    · rintro ⟨t, ht, rfl⟩
      refine ⟨t, ?_, rfl⟩
      change K < exteriorSize t
      change K < lastZero (cyclicResidual t.increments).reverse at ht
      simpa only [exteriorSize_eq_lastZero] using ht
  have hB : B.real A = (MaximumSwapLaw.bridgeCountsLaw μ n).real
      {ω | cyclicResidual (stepWord ω) ∈ A} := by
    dsimp only [B]
    rw [Measure.real, Measure.real, Measure.map_apply
      (measurable_of_countable _) (Set.to_countable _).measurableSet]
    rfl
  have hQ : Q.real A = (Measure.pi fun _ : Fin (n - 1) => incrementLaw μ).real
      {x | K < lastZero (List.ofFn x).reverse} := by
    dsimp only [Q, A]
    rw [Measure.real, Measure.real, Measure.map_apply
      (measurable_of_countable _) (Set.to_countable _).measurableSet]
    rfl
  have hQtail : Q.real A ≤ (iidOffspringLaw μ).real (walkNonnegativeTail K) := by
    rw [hQ]
    exact pi_increment_lastZero_reverse_real_le_tail μ (n - 1) K
  have htv := measureReal_le_add_tvDist B Q A
  have herr := conditioned_cyclicResidual_event_error_le μ hn hsize A
  rw [htree]
  rw [hB] at htv
  have herr' := (abs_le.mp herr).2
  dsimp only [B, Q] at htv
  linarith

/-- The exterior size is tight under the size-conditioned laws. -/
theorem exteriorSize_tight (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ᶠ n in atTop,
      (conditioned μ n).real (finiteTreeEvent fun t => K < exteriorSize t) ≤ ε := by
  let δ := ε / 3
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have htail := iid_walkNonnegativeTail_real_tendsto_zero μ hμ.1
  have hKev : ∀ᶠ K : ℕ in atTop,
      (iidOffspringLaw μ).real (walkNonnegativeTail K) < δ :=
    htail.eventually (Iio_mem_nhds hδ)
  obtain ⟨K, hKall⟩ := eventually_atTop.mp hKev
  have hK := hKall K le_rfl
  have htv := cyclicResidual_bridge_tvDist μ hμ
  have htve : ∀ᶠ n : ℕ in atTop,
      tvDist
        ((MaximumSwapLaw.bridgeCountsLaw μ n).map
          (fun ω => cyclicResidual (stepWord ω)))
        ((Measure.pi fun _ : Fin (n - 1) => incrementLaw μ).map List.ofFn) < δ :=
    htv.eventually (Iio_mem_nhds hδ)
  have hie := conditioned_nonunique_maximum_tendsto_zero μ hμ
  have hiee : ∀ᶠ n : ℕ in atTop,
      (conditioned μ n).real (finiteTreeEvent fun t => ¬ uniqueWordMaximum t.increments) < δ :=
    hie.eventually (Iio_mem_nhds hδ)
  refine ⟨K, ?_⟩
  filter_upwards [htve, hiee, eventually_gt_atTop (0 : ℕ),
    eventually_size_admissible μ hμ.to_literal] with n htvn hien hn hsize
  have hb := exteriorSize_conditioned_le_tail_add_errors μ (Nat.ne_of_gt hn) hsize K
  change (conditioned μ n).real (finiteIncrementEvent fun x => ¬ uniqueWordMaximum x) < δ at hien
  dsimp [δ] at hK htvn hien
  linarith

end
end SubcriticalCauchy.Bienayme
