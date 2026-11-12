module

import SubcriticalCauchy
import BGW
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
Reproducible transitive axiom audit for the visible project namespace.
Run after `lake build` with `lake env lean scripts/AxiomAudit.lean`.
This uses Lean's axiom collector, the same mechanism as `#print axioms`.
It is not independent kernel replay or a statement-fidelity check.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names : Array Name := env.constants.fold (init := #[]) fun acc name _ =>
    if (`SubcriticalCauchy).isPrefixOf name || (`BGW).isPrefixOf name then acc.push name else acc
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in names.qsort Name.lt do
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "{name} depends on disallowed axiom {axiomName}"
  logInfo m!"Axiom audit passed: {names.size} project and vendored BGW declarations; allowed axioms: {allowed}"

#print axioms SubcriticalCauchy.PlaneTree.weight_tilt
#print axioms SubcriticalCauchy.PlaneTree.finite_size_eq
#print axioms SubcriticalCauchy.conditionedTreeOfPMF_tilt
#print axioms SubcriticalCauchy.geometric_bounds_of_recurrence
#print axioms SubcriticalCauchy.tendsto_one_sub_pow_of_mul_tendsto_atTop
#print axioms SubcriticalCauchy.TiltingCounterexample.critical_equivalence_boundary_counterexample
#print axioms SubcriticalCauchy.Bienayme.conditioned_tilt_of_pos
#print axioms SubcriticalCauchy.Bienayme.survival_succ
#print axioms SubcriticalCauchy.Bienayme.survival_toReal_succ
#print axioms SubcriticalCauchy.Bienayme.survival_le_mean_pow
#print axioms SubcriticalCauchy.Bienayme.ae_finite_of_subcritical
#print axioms SubcriticalCauchy.Bienayme.toLocallyFinite_mem_survivalEvent_iff
#print axioms SubcriticalCauchy.Bienayme.survival_pos
#print axioms SubcriticalCauchy.Bienayme.survival_ratio_tendsto
#print axioms SubcriticalCauchy.Bienayme.survival_geometric_bounds
#print axioms SubcriticalCauchy.Bienayme.survival_log_normalized_inv_div_nat
#print axioms SubcriticalCauchy.Bienayme.forestBelow_mass
#print axioms SubcriticalCauchy.Bienayme.forest_height_bounds
#print axioms SubcriticalCauchy.Bienayme.forestBelowReal_tendsto_one
#print axioms SubcriticalCauchy.Bienayme.forestBelowReal_tendsto_zero
#print axioms SubcriticalCauchy.Bienayme.forestBelowReal_floor_tendsto_one
#print axioms SubcriticalCauchy.Bienayme.forestBelowReal_floor_tendsto_zero
#print axioms SubcriticalCauchy.tendsto_log_product_ceil_log
#print axioms SubcriticalCauchy.Bienayme.exists_eta_log_exponent
#print axioms SubcriticalCauchy.Bienayme.survival_log_upper_tendsto_zero
#print axioms SubcriticalCauchy.Bienayme.survival_log_lower_tendsto_atTop
#print axioms SubcriticalCauchy.Bienayme.finite_forestHeightBand_iff
#print axioms SubcriticalCauchy.Bienayme.forest_log_band_tendsto_one
#print axioms SubcriticalCauchy.Bienayme.maxDegreeVertex_unique
#print axioms SubcriticalCauchy.Bienayme.positiveAddress_le_iff
#print axioms SubcriticalCauchy.Bienayme.attachedForestSlice_slot_present
#print axioms SubcriticalCauchy.Bienayme.height_fringe_add_le
#print axioms SubcriticalCauchy.Bienayme.conditioned_degree_pair_event
#print axioms SubcriticalCauchy.Bienayme.survivalCorrection_eq_tsum_tail
#print axioms SubcriticalCauchy.Bienayme.paper_survivalCorrection
#print axioms SubcriticalCauchy.Bienayme.eventually_size_admissible
#print axioms SubcriticalCauchy.Bienayme.finiteWalkAverage_deviation_tendsto_zero
#print axioms SubcriticalCauchy.Bienayme.finitePreviousWalkAverage_deviation_tendsto_zero
#print axioms SubcriticalCauchy.Bienayme.scaling_div_nat_tendsto_zero
#print axioms SubcriticalCauchy.Bienayme.paper_centering_ratio_tendsto_one
#print axioms SubcriticalCauchy.mul_tail_div_tailMass_tendsto_zero
#print axioms SubcriticalCauchy.tailMass_floor_mul_div_tendsto_one
#print axioms SubcriticalCauchy.Bienayme.maxDegree_eq_neg_deleted_sum
#print axioms SubcriticalCauchy.Bienayme.incrementMaximum_deleted_word
#print axioms SubcriticalCauchy.Bienayme.finiteWalk_driftRatio_deviation_tendsto_zero
#print axioms SubcriticalCauchy.Bienayme.finiteMaximumAverage_deviation_tendsto_zero
#print axioms SubcriticalCauchy.Bienayme.finitePreviousMaximumAverage_deviation_tendsto_zero
#print axioms SubcriticalCauchy.Bienayme.IsMeasurableSubcriticalCauchyOffspring.to_literal
#print axioms SubcriticalCauchy.SupercriticalTiltingCounterexample.supercritical_equivalence_counterexample
#print axioms SubcriticalCauchy.additive_uniform_sequential
#print axioms SubcriticalCauchy.quasiMeasurePreserving_exp_positive
#print axioms SubcriticalCauchy.slowlyVarying_uniform_sequential
#print axioms SubcriticalCauchy.slowlyVarying_uniform_additive_window
#print axioms SubcriticalCauchy.slowlyVarying_uniform_compact_tail
#print axioms SubcriticalCauchy.centered_lattice_window_neg_one
#print axioms SubcriticalCauchy.Bienayme.paper_centering_uniform_windows
#print axioms SubcriticalCauchy.Bienayme.paper_unitWindow_ratio_of_relative_tendsto_one
#print axioms SubcriticalCauchy.Bienayme.paper_centeredUnitWindow_uniform_additive_window
#print axioms SubcriticalCauchy.Bienayme.MaximumSwapLaw.bridgeCountsLaw_map_rotation
#print axioms SubcriticalCauchy.Bienayme.MaximumSwapLaw.swap_take_event_eq_delete_event
#print axioms SubcriticalCauchy.Bienayme.summable_localModel_over_nat
#print axioms SubcriticalCauchy.localModel_div_ellStar_tendsto_zero
#print axioms SubcriticalCauchy.ellStarReal_slowlyVarying
#print axioms SubcriticalCauchy.ellStar_ceil_div_floor_tendsto_one
#print axioms SubcriticalCauchy.Bienayme.paper_integratedTail_properties
#print axioms SubcriticalCauchy.tailMass_div_tendsto_one
#print axioms SubcriticalCauchy.Bienayme.tailIncrementMean_eq_tailMass
#print axioms SubcriticalCauchy.Bienayme.paper_centering_asymptotics
