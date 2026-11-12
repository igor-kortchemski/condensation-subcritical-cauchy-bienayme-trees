module

public import SubcriticalCauchy.MaximumSwapBridge
public import Mathlib.Data.Vector.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Map

set_option autoImplicit false

/-!
Actual-law bridge: a multiset-preserving bijection rotates the suffix
after the first maximum. Its invariance under the conditioned iid count law
identifies swap-to-last residuals with ordered maximum deletion, including ties.
No asymptotic or one-big-jump result is asserted.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SubcriticalCauchy.Bienayme.MaximumSwapLaw

noncomputable section

attribute [local instance] Classical.propDecidable

open BGW MaximumSwapBridge

/-- Restrict the length-preserving list bijection to a fixed-length vector. -/
def vectorRotationEquiv (n : ℕ) : List.Vector ℕ n ≃ List.Vector ℕ n where
  toFun v := ⟨rotateAfterFirstMax v.1, (rotateAfterFirstMax_length v.1).trans v.2⟩
  invFun v := ⟨unrotateAfterFirstMax v.1, (unrotateAfterFirstMax_perm v.1).length_eq.trans v.2⟩
  left_inv v := Subtype.ext (unrotate_rotateAfterFirstMax v.1)
  right_inv v := Subtype.ext (rotate_unrotateAfterFirstMax v.1)

/-- The actual bijection of finite offspring-count vectors. -/
def countRotationEquiv (n : ℕ) : (Fin n → ℕ) ≃ (Fin n → ℕ) :=
  (Equiv.vectorEquivFin ℕ n).symm.trans
    ((vectorRotationEquiv n).trans (Equiv.vectorEquivFin ℕ n))

theorem ofFn_vector_get {n : ℕ} (v : List.Vector ℕ n) :
    List.ofFn v.get = v.toList := by
  have h := congrArg List.Vector.toList (List.Vector.ofFn_get v)
  simpa only [List.Vector.toList_ofFn] using h

theorem ofFn_countRotationEquiv {n : ℕ} (ω : Fin n → ℕ) :
    List.ofFn (countRotationEquiv n ω) = rotateAfterFirstMax (List.ofFn ω) := by
  change List.ofFn ((vectorRotationEquiv n (List.Vector.ofFn ω)).get) = _
  rw [ofFn_vector_get]
  change rotateAfterFirstMax (List.Vector.ofFn ω).toList = _
  rw [List.Vector.toList_ofFn]

theorem countRotationEquiv_perm {n : ℕ} (ω : Fin n → ℕ) :
    (List.ofFn (countRotationEquiv n ω)).Perm (List.ofFn ω) := by
  rw [ofFn_countRotationEquiv]
  exact rotateAfterFirstMax_perm _

theorem countRotationEquiv_sum {n : ℕ} (ω : Fin n → ℕ) :
    (∑ i, countRotationEquiv n ω i) = ∑ i, ω i := by
  simpa only [List.sum_ofFn] using (countRotationEquiv_perm ω).sum_eq

theorem countRotationEquiv_prod (μ : Measure ℕ) {n : ℕ} (ω : Fin n → ℕ) :
    (∏ i, μ {countRotationEquiv n ω i}) = ∏ i, μ {ω i} := by
  have h := ((countRotationEquiv_perm ω).map (fun k : ℕ => μ {k})).prod_eq
  simpa only [List.map_ofFn, List.prod_ofFn, Function.comp_def] using h

theorem countRotationEquiv_mem_bridge {n : ℕ} (ω : Fin n → ℕ) :
    countRotationEquiv n ω ∈ countBridges n ↔ ω ∈ countBridges n := by
  change (∑ i, countRotationEquiv n ω i) + 1 = n ↔ (∑ i, ω i) + 1 = n
  rw [countRotationEquiv_sum]

/-- The existing actual conditional iid law, with its null-event convention. -/
def bridgeCountsLaw (μ : Measure ℕ) (n : ℕ) : Measure (Fin n → ℕ) :=
  (Measure.pi fun _ : Fin n => μ)[|countBridges n]

theorem bridgeCountsLaw_atom_rotation (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {n : ℕ} (ω : Fin n → ℕ) :
    bridgeCountsLaw μ n {countRotationEquiv n ω} = bridgeCountsLaw μ n {ω} := by
  unfold bridgeCountsLaw
  rw [cond_pi_countBridges_singleton, cond_pi_countBridges_singleton]
  by_cases hω : ω ∈ countBridges n
  · rw [Set.indicator_of_mem ((countRotationEquiv_mem_bridge ω).mpr hω),
      Set.indicator_of_mem hω, countRotationEquiv_prod]
  · rw [Set.indicator_of_notMem (fun h => hω ((countRotationEquiv_mem_bridge ω).mp h)),
      Set.indicator_of_notMem hω]

/-- On a countable measurable space, an atom-preserving bijection preserves the
entire measure. This does not assume that the bijection is a fixed permutation. -/
theorem map_equiv_eq_of_atoms {α : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] (e : α ≃ α) (ν : Measure α)
    (hmass : ∀ a, ν {e a} = ν {a}) : ν.map e = ν := by
  apply Measure.ext_of_singleton
  intro a
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton a)]
  have hpre : e ⁻¹' {a} = {e.symm a} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      apply e.injective
      simpa only [e.apply_symm_apply] using h
    · intro h
      rw [h]
      exact e.apply_symm_apply a
  rw [hpre]
  simpa only [e.apply_symm_apply] using (hmass (e.symm a)).symm

/-- The data-dependent suffix rotation preserves the actual conditional iid law.
No admissibility premise is needed: the null-size conditional law is zero. -/
theorem bridgeCountsLaw_map_rotation (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) :
    (bridgeCountsLaw μ n).map (countRotationEquiv n) = bridgeCountsLaw μ n :=
  map_equiv_eq_of_atoms (countRotationEquiv n) _ (bridgeCountsLaw_atom_rotation μ)

theorem bridgeCountsLaw_rotation_event (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (n : ℕ) (A : Set (Fin n → ℕ)) :
    bridgeCountsLaw μ n {ω | countRotationEquiv n ω ∈ A} = bridgeCountsLaw μ n A := by
  have hA : MeasurableSet A := (Set.to_countable A).measurableSet
  calc
    _ = ((bridgeCountsLaw μ n).map (countRotationEquiv n)) A :=
      (Measure.map_apply (measurable_of_countable _) hA).symm
    _ = _ := congrArg (fun ν : Measure (Fin n → ℕ) => ν A) (bridgeCountsLaw_map_rotation μ n)

/-- Swapping the first maximum with the last coordinate and retaining the first
`n-1` coordinates has the same law as ordered first-maximum deletion. The event
predicate is arbitrary and need not be permutation invariant. -/
theorem swap_take_event_eq_delete_event (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : n ≠ 0) (Q : List ℕ → Prop) :
    bridgeCountsLaw μ n {ω | Q ((swapFirstMaxToLast (List.ofFn ω)).take (n - 1))} =
      bridgeCountsLaw μ n {ω | Q (deleteMaxCounts (List.ofFn ω))} := by
  let A : Set (Fin n → ℕ) := {ω | Q ((swapFirstMaxToLast (List.ofFn ω)).take (n - 1))}
  have hinv := bridgeCountsLaw_rotation_event μ n A
  have hpre : {ω : Fin n → ℕ | countRotationEquiv n ω ∈ A} =
      {ω | Q (deleteMaxCounts (List.ofFn ω))} := by
    ext ω
    change Q ((swapFirstMaxToLast (List.ofFn (countRotationEquiv n ω))).take (n - 1)) ↔ _
    rw [ofFn_countRotationEquiv]
    have hne : List.ofFn ω ≠ [] := by
      intro h
      have hlen := congrArg List.length h
      simp only [List.length_ofFn, List.length_nil] at hlen
      exact hn hlen
    have hd : (swapFirstMaxToLast (rotateAfterFirstMax (List.ofFn ω))).take (n - 1) =
        deleteMaxCounts (List.ofFn ω) := by
      simpa only [List.length_ofFn] using take_swap_rotate_eq_delete hne
    rw [hd]
    rfl
  rw [hpre] at hinv
  exact hinv.symm

/-- A pushforward-measure formulation, valid for any chosen measurable structure
on residual count lists. In particular it gives their discrete laws. -/
theorem map_swap_take_eq_map_delete [MeasurableSpace (List ℕ)]
    (μ : Measure ℕ) [IsProbabilityMeasure μ] {n : ℕ} (hn : n ≠ 0) :
    (bridgeCountsLaw μ n).map (fun ω => (swapFirstMaxToLast (List.ofFn ω)).take (n - 1)) =
      (bridgeCountsLaw μ n).map (fun ω => deleteMaxCounts (List.ofFn ω)) := by
  ext A hA
  rw [Measure.map_apply (measurable_of_countable _) hA,
    Measure.map_apply (measurable_of_countable _) hA]
  exact swap_take_event_eq_delete_event μ hn (fun ds => ds ∈ A)

end
end SubcriticalCauchy.Bienayme.MaximumSwapLaw
