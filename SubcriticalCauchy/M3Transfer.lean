module

public import SubcriticalCauchy.DeletionPositionLaw
public import SubcriticalCauchy.CyclicResidualTree
public import SubcriticalCauchy.FiniteTreeEvent
public import SubcriticalCauchy.MainProofs.M2

/-! # Transfer of the positioned deletion law under cyclic rotation -/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme
open BGW
noncomputable section

section ListLaws

variable [MeasurableSpace (List ℤ)] [MeasurableSingletonClass (List ℤ)]

omit [MeasurableSingletonClass (List ℤ)] in
/-- Every fixed rotation preserves the iid increment-word law. -/
theorem iid_incrementWord_rotate (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (N k : ℕ) :
    (Measure.pi fun _ : Fin N => incrementLaw μ).map
        (fun x => (List.ofFn x).rotate k) =
      (Measure.pi fun _ : Fin N => incrementLaw μ).map List.ofFn := by
  let _ : IsProbabilityMeasure (incrementLaw μ) := by
    unfold incrementLaw
    infer_instance
  cases N with
  | zero =>
    congr 1
  | succ N =>
    let e : Equiv.Perm (Fin (N + 1)) := Equiv.addRight (Fin.ofNat (N + 1) k)
    have hp := measurePreserving_piCongrLeft
      (α := fun _ : Fin (N + 1) => ℤ) (fun _ => incrementLaw μ) e.symm
    have he (x : Fin (N + 1) → ℤ) :
        List.ofFn (MeasurableEquiv.piCongrLeft
          (fun _ : Fin (N + 1) => ℤ) e.symm x) = (List.ofFn x).rotate k := by
      apply List.ext_getElem
      · simp
      · intro i hi hj
        simp only [List.length_ofFn] at hi
        rw [List.getElem_ofFn, List.getElem_rotate, List.getElem_ofFn]
        have hh := MeasurableEquiv.piCongrLeft_apply_apply e.symm
          (β := fun _ : Fin (N + 1) => ℤ) x (e ⟨i, hi⟩)
        simp only [Equiv.symm_apply_apply] at hh
        rw [hh]
        apply congrArg x
        apply Fin.ext
        simp [e, Fin.val_add, Nat.add_mod, Nat.mod_eq_of_lt hi]
    calc
      _ = ((Measure.pi fun _ : Fin (N + 1) => incrementLaw μ).map
          (MeasurableEquiv.piCongrLeft (fun _ : Fin (N + 1) => ℤ) e.symm)).map
            List.ofFn := by
        rw [Measure.map_map (measurable_of_countable _) (MeasurableEquiv.measurable _)]
        congr 1
        funext x
        exact (he x).symm
      _ = _ := by rw [hp.map_eq]

omit [MeasurableSingletonClass (List ℤ)] in
/-- An independent position, with any probability law, can be used to rotate
an iid increment word without changing its law. -/
theorem independent_rotate_iid_incrementWord (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (N : ℕ) (U : Measure ℕ) [IsProbabilityMeasure U] :
    (U.prod (Measure.pi fun _ : Fin N => incrementLaw μ)).map
        (fun p => (List.ofFn p.2).rotate p.1) =
      (Measure.pi fun _ : Fin N => incrementLaw μ).map List.ofFn := by
  let _ : IsProbabilityMeasure (incrementLaw μ) := by
    unfold incrementLaw
    infer_instance
  ext A hA
  rw [Measure.map_apply (measurable_of_countable _) hA,
    Measure.prod_apply ((measurable_of_countable _) hA)]
  have he (k : ℕ) :
      (Measure.pi fun _ : Fin N => incrementLaw μ)
          {x | (List.ofFn x).rotate k ∈ A} =
        ((Measure.pi fun _ : Fin N => incrementLaw μ).map List.ofFn) A := by
    rw [← iid_incrementWord_rotate μ N k,
      Measure.map_apply (measurable_of_countable _) hA]
    rfl
  change (∫⁻ k, (Measure.pi fun _ : Fin N => incrementLaw μ)
    {x | (List.ofFn x).rotate k ∈ A} ∂U) = _
  simp_rw [he]
  simp

omit [MeasurableSingletonClass (List ℤ)] in
/-- The rotated positioned deletion is asymptotically an iid word in TV.
This law-level statement does not require any maximum-tie convention. -/
theorem rotated_deletionWithPosition_tvDist
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) :
    Tendsto (fun n : ℕ => tvDist
      (((MaximumSwapLaw.bridgeCountsLaw μ n).map (deletionWithPosition n)).map
        (fun p => (List.ofFn p.2).rotate p.1))
      ((Measure.pi fun _ : Fin (n - 1) => incrementLaw μ).map List.ofFn))
      atTop (𝓝 0) := by
  have ht := deletionWithPosition_tvDist μ hμ
  apply squeeze_zero' (Eventually.of_forall fun _ => tvDist_nonneg) ?_ ht
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    eventually_size_admissible μ hμ.to_literal] with n hn hsize
  let _ : IsProbabilityMeasure (MaximumSwapLaw.bridgeCountsLaw μ n) :=
    BGW.isProbabilityMeasure_cond_pi_countBridges μ (Nat.ne_of_gt hn) hsize
  let _ : IsProbabilityMeasure (incrementLaw μ) := by
    unfold incrementLaw
    infer_instance
  let _ : IsProbabilityMeasure (uniformInsertionPosition n) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    exact uniformInsertionPosition_succ_isProbability m
  rw [← independent_rotate_iid_incrementWord μ (n - 1) (uniformInsertionPosition n)]
  exact tvDist_map_le _ _ _ (measurable_of_countable _)

end ListLaws

theorem cyclicResidual_stepWord {n : ℕ} (hn : n ≠ 0) (ω : Fin n → ℕ) :
    cyclicResidual (stepWord ω) =
      (List.ofFn (deletedIncrements n ω)).rotate (firstMaxIndex (List.ofFn ω)) := by
  have hne : List.ofFn ω ≠ [] := by simpa using hn
  obtain ⟨pre, post, hpre, hword, hdel⟩ := deleteMaxCounts_first hne
  have hi : firstMaxIndex (List.ofFn ω) = pre.length := by
    unfold firstMaxIndex
    conv_lhs => arg 2; rw [hword]
    rw [List.idxOf_append_of_notMem hpre, List.idxOf_cons_self, Nat.add_zero]
  have hx : stepWord ω = pre.map (fun d : ℕ => (d : ℤ) - 1) ++
      ((listMaxDegree (List.ofFn ω) : ℤ) - 1) ::
        post.map (fun d : ℕ => (d : ℤ) - 1) := by
    have hh := congrArg (List.map (fun d : ℕ => (d : ℤ) - 1)) hword
    simpa only [List.map_ofFn, Function.comp_def, List.map_append, List.map_cons, stepWord] using hh
  rw [cyclicResidual, wordDegrees_stepWord, hi,
    ofFn_deletedIncrements hn ω, deletedMaximumWord, hdel, List.map_append]
  have hj : pre.length < (stepWord ω).length := by rw [hx]; simp
  rw [rotate_take_pred_eq _ hj, hx]
  have hd : (pre.map (fun d : ℕ => (d : ℤ) - 1)).drop (pre.length + 1) = [] :=
    List.drop_eq_nil_of_le (by simp)
  have ht : (pre.map (fun d : ℕ => (d : ℤ) - 1)).take pre.length =
      pre.map (fun d : ℕ => (d : ℤ) - 1) := by
    simpa only [List.length_map] using (List.take_length (l := pre.map (fun d : ℕ => (d : ℤ) - 1)))
  simp only [List.drop_append, List.length_map, hd, List.nil_append,
    Nat.add_sub_cancel_left, List.drop_succ_cons, List.drop_zero,
    List.take_append, ht, Nat.sub_self, List.take_zero, List.append_nil]
  simpa only [List.length_map] using (List.rotate_append_length_eq
    (pre.map (fun d : ℕ => (d : ℤ) - 1)) (post.map (fun d : ℕ => (d : ℤ) - 1))).symm

def uniqueWordMaximum (x : List ℤ) : Prop :=
  (wordDegrees x).count (listMaxDegree (wordDegrees x)) = 1

theorem uniqueWordMaximum_rotate (x : List ℤ) (k : ℕ) :
    uniqueWordMaximum (x.rotate k) ↔ uniqueWordMaximum x := by
  unfold uniqueWordMaximum
  rw [wordDegrees_rotate, listMaxDegree_perm (List.rotate_perm _ _),
    (List.rotate_perm _ _).count_eq]

theorem cyclicResidual_rotate_one_unique (x : List ℤ) (hu : uniqueWordMaximum x) :
    cyclicResidual (x.rotate 1) = cyclicResidual x := by
  have hmax : listMaxDegree (wordDegrees (x.rotate 1)) = listMaxDegree (wordDegrees x) := by
    rw [wordDegrees_rotate]
    exact listMaxDegree_perm (List.rotate_perm _ _)
  cases x with
  | nil => simp [uniqueWordMaximum, wordDegrees] at hu
  | cons a xs =>
    let M := listMaxDegree (wordDegrees (a :: xs))
    have hds : wordDegrees (a :: xs) = (a + 1).toNat :: wordDegrees xs := rfl
    by_cases ha : (a + 1).toNat = M
    · have hn : M ∉ wordDegrees xs := by
        change (wordDegrees (a :: xs)).count M = 1 at hu
        rw [hds, ha, List.count_cons_self] at hu
        exact List.count_eq_zero.mp (by omega)
      have hi : firstMaxIndex (wordDegrees ((a :: xs).rotate 1)) = xs.length := by
        rw [firstMaxIndex, hmax]
        change List.idxOf M (wordDegrees ((a :: xs).rotate 1)) = _
        simp only [List.rotate_cons_succ, List.rotate_zero, wordDegrees, List.map_append,
          List.map_singleton]
        change M ∉ xs.map (fun z => (z + 1).toNat) at hn
        rw [List.idxOf_append_of_notMem hn]
        simp [ha]
      have hi0 : firstMaxIndex (wordDegrees (a :: xs)) = 0 := by
        change List.idxOf M ((a + 1).toNat :: wordDegrees xs) = 0
        simp [ha]
      rw [cyclicResidual, hi, cyclicResidual, hi0]
      simp only [List.rotate_cons_succ, List.rotate_zero, List.length_append,
        Nat.add_sub_cancel, List.length_cons]
      rw [show xs.length + 1 = (xs ++ [a]).length by simp, List.rotate_length]
      simp
    · have hm : M ∈ wordDegrees xs := by
        have hm := listMaxDegree_mem (ds := wordDegrees (a :: xs)) (by simp [hds])
        rw [hds, List.mem_cons] at hm
        exact hm.resolve_left (Ne.symm ha)
      have hi : firstMaxIndex (wordDegrees ((a :: xs).rotate 1)) =
          (wordDegrees xs).idxOf M := by
        rw [firstMaxIndex, hmax]
        change List.idxOf M (wordDegrees ((a :: xs).rotate 1)) = _
        simp only [List.rotate_cons_succ, List.rotate_zero, wordDegrees, List.map_append,
          List.map_singleton]
        exact List.idxOf_append_of_mem hm
      have hi0 : firstMaxIndex (wordDegrees (a :: xs)) = (wordDegrees xs).idxOf M + 1 := by
        change List.idxOf M ((a + 1).toNat :: wordDegrees xs) = _
        exact List.idxOf_cons_ne _ ha
      simp only [cyclicResidual, hi, hi0, List.length_rotate, List.rotate_rotate]
      congr 2
      omega

theorem cyclicResidual_rotate_unique (x : List ℤ) (hu : uniqueWordMaximum x) (k : ℕ) :
    cyclicResidual (x.rotate k) = cyclicResidual x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← List.rotate_rotate, cyclicResidual_rotate_one_unique _
      ((uniqueWordMaximum_rotate x k).mpr hu), ih]

theorem conditioned_cyclicResidual_unique_event
    (μ : Measure ℕ) [IsProbabilityMeasure μ] {n : ℕ} (hn : n ≠ 0)
    (A : Set (List ℤ)) :
    (Measure.pi fun _ : Fin n => μ)[|BGW.countBridges n]
        {ω | uniqueWordMaximum (stepWord ω) ∧ cyclicResidual (stepWord ω) ∈ A} =
      conditioned μ n (finiteIncrementEvent fun x =>
        uniqueWordMaximum x ∧ cyclicResidual x ∈ A) := by
  apply conditioned_bridge_rotation_invariant_event μ hn
    (fun x => uniqueWordMaximum x ∧ cyclicResidual x ∈ A)
  intro x i
  by_cases hu : uniqueWordMaximum x
  · rw [cyclicResidual_rotate_unique x hu i, uniqueWordMaximum_rotate]
  · simp [uniqueWordMaximum_rotate, hu]

theorem uniqueWordMaximum_of_second_lt (x : List ℤ)
    (hs : listSecondMaxDegree (wordDegrees x) < listMaxDegree (wordDegrees x)) :
    uniqueWordMaximum x := by
  let ds := wordDegrees x
  have hne : ds ≠ [] := by
    intro h
    simp [ds, h, listMaxDegree] at hs
  have hm := listMaxDegree_mem hne
  have hn : listMaxDegree ds ∉ ds.erase (listMaxDegree ds) := by
    intro hmem
    have hle : listMaxDegree ds ≤ listSecondMaxDegree ds :=
      Finset.le_sup (f := id) (List.mem_toFinset.mpr hmem)
    exact (not_le_of_gt hs) hle
  have hc := List.count_eq_zero.mpr hn
  rw [List.count_erase_self] at hc
  unfold uniqueWordMaximum
  change ds.count (listMaxDegree ds) = 1
  have hp := List.count_pos_iff.mpr hm
  omega


/-- The cyclic residual of the conditioned bridge converges to the iid word
law in total variation. No restriction on ties is needed for this step. -/
theorem cyclicResidual_bridge_tvDist [MeasurableSpace (List ℤ)]
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) :
    Tendsto (fun n : ℕ => tvDist
      ((MaximumSwapLaw.bridgeCountsLaw μ n).map (fun ω => cyclicResidual (stepWord ω)))
      ((Measure.pi fun _ : Fin (n - 1) => incrementLaw μ).map List.ofFn))
      atTop (𝓝 0) := by
  apply (rotated_deletionWithPosition_tvDist μ hμ).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  congr 2
  funext ω
  exact (cyclicResidual_stepWord (Nat.ne_of_gt hn) ω).symm

end
end SubcriticalCauchy.Bienayme

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Topology
namespace SubcriticalCauchy.Bienayme
open BGW BGW.LocallyFinite
noncomputable section

theorem conditioned_nonunique_maximum_tendsto_zero (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (hμ : IsMeasurableSubcriticalCauchyOffspring μ) :
    Tendsto (fun n : ℕ => (conditioned μ n (finiteTreeEvent fun t =>
      ¬ uniqueWordMaximum t.increments)).toReal) atTop (𝓝 0) := by
  have hfin : offspringMean μ ≠ ∞ := ne_top_of_lt (hμ.1.trans ENNReal.one_lt_top)
  have hc : 0 < 1 - (offspringMean μ).toReal := by
    have hm : (offspringMean μ).toReal < 1 := by
      simpa using (ENNReal.toReal_lt_toReal hfin ENNReal.one_ne_top).mpr hμ.1
    linarith
  let c := 1 - (offspringMean μ).toReal
  have h₁ := main_maxDegree_condensation_real μ hμ (1 / 2) (by norm_num)
  have h₂ := main_secondMaxDegree_negligible_real μ hμ (c / 4) (by dsimp [c]; positivity)
  apply squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) ?_
    (by simpa using h₁.add h₂)
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    eventually_size_admissible μ hμ.to_literal] with n hn hsize
  let _ : IsProbabilityMeasure (conditioned μ n) := conditioned_isProbability μ n hsize
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let E := finiteTreeEvent fun t =>
    (1 / 2 : ℝ) < |(maxDegree t : ℝ) / ((n : ℝ) * c) - 1|
  let F := finiteTreeEvent fun t => c / 4 < (secondMaxDegree t : ℝ) / n
  have hsub : (finiteTreeEvent fun t => ¬ uniqueWordMaximum t.increments) ⊆ E ∪ F := by
    rintro T ⟨t, ht, rfl⟩
    by_cases hE : (1 / 2 : ℝ) < |(maxDegree t : ℝ) / ((n : ℝ) * c) - 1|
    · exact Or.inl ⟨t, hE, rfl⟩
    by_cases hF : c / 4 < (secondMaxDegree t : ℝ) / n
    · exact Or.inr ⟨t, hF, rfl⟩
    have hc' : 0 < c := hc
    have ha := (abs_le.mp (le_of_not_gt hE)).1
    have hmax : (n : ℝ) * c / 2 ≤ maxDegree t := by
      have hh : (1 / 2 : ℝ) ≤ (maxDegree t : ℝ) / ((n : ℝ) * c) := by linarith
      have hh' := (le_div_iff₀ (mul_pos hnR hc')).mp hh
      linarith
    have hsecond : (secondMaxDegree t : ℝ) ≤ (n : ℝ) * c / 4 := by
      have hh := (div_le_iff₀ hnR).mp (le_of_not_gt hF)
      linarith
    have hlt : secondMaxDegree t < maxDegree t := by
      have : (secondMaxDegree t : ℝ) < maxDegree t := by nlinarith
      exact_mod_cast this
    have hu : uniqueWordMaximum t.increments := by
      apply uniqueWordMaximum_of_second_lt
      rw [wordDegrees_increments, ← maxDegree_eq_listMaxDegree]
      exact hlt
    exact False.elim (ht hu)
  have hb : (conditioned μ n).real (finiteTreeEvent fun t =>
      ¬ uniqueWordMaximum t.increments) ≤ (conditioned μ n).real E +
        (conditioned μ n).real F := by
    calc
      _ ≤ (conditioned μ n).real (E ∪ F) :=
        measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ (conditioned μ n).real E + (conditioned μ n).real F := measureReal_union_le _ _
  simpa only [Measure.real, E, F, c, one_div] using hb

/-- The error in the tree-to-bridge residual event is bounded by the tie mass. -/
theorem conditioned_cyclicResidual_event_error_le
    (μ : Measure ℕ) [IsProbabilityMeasure μ] {n : ℕ} (hn : n ≠ 0)
    (hsize : bienaymeLaw μ (sizeEvent n) ≠ 0) (A : Set (List ℤ)) :
    |(conditioned μ n).real (finiteIncrementEvent fun x => cyclicResidual x ∈ A) -
      (MaximumSwapLaw.bridgeCountsLaw μ n).real {ω | cyclicResidual (stepWord ω) ∈ A}| ≤
      (conditioned μ n).real (finiteIncrementEvent fun x => ¬ uniqueWordMaximum x) := by
  let B := MaximumSwapLaw.bridgeCountsLaw μ n
  let C := conditioned μ n
  let _ : IsProbabilityMeasure B := BGW.isProbabilityMeasure_cond_pi_countBridges μ hn hsize
  let _ : IsProbabilityMeasure C := conditioned_isProbability μ n hsize
  let E := finiteIncrementEvent fun x => cyclicResidual x ∈ A
  let G := finiteIncrementEvent fun x => uniqueWordMaximum x ∧ cyclicResidual x ∈ A
  let D := finiteIncrementEvent fun x => ¬ uniqueWordMaximum x
  let E' : Set (Fin n → ℕ) := {ω | cyclicResidual (stepWord ω) ∈ A}
  let G' : Set (Fin n → ℕ) := {ω | uniqueWordMaximum (stepWord ω) ∧ cyclicResidual (stepWord ω) ∈ A}
  let D' : Set (Fin n → ℕ) := {ω | ¬ uniqueWordMaximum (stepWord ω)}
  have hG : B.real G' = C.real G := by
    simpa only [B, C, G', G, Measure.real, MaximumSwapLaw.bridgeCountsLaw] using
      congrArg ENNReal.toReal (conditioned_cyclicResidual_unique_event μ hn A)
  have hD : B.real D' = C.real D := by
    have hh := conditioned_bridge_rotation_invariant_event μ hn
      (fun x => ¬ uniqueWordMaximum x) (by intro x i; rw [uniqueWordMaximum_rotate])
    simpa only [B, C, D', D, Measure.real, MaximumSwapLaw.bridgeCountsLaw] using
      congrArg ENNReal.toReal hh
  have hGE : G ⊆ E := by
    rintro T ⟨t, ht, rfl⟩
    exact ⟨t, ht.2, rfl⟩
  have hEGD : E ⊆ G ∪ D := by
    rintro T ⟨t, ht, rfl⟩
    by_cases hu : uniqueWordMaximum t.increments
    · exact Or.inl ⟨t, ⟨hu, ht⟩, rfl⟩
    · exact Or.inr ⟨t, hu, rfl⟩
  have hcg : C.real G ≤ C.real E := measureReal_mono hGE (measure_ne_top _ _)
  have hce : C.real E ≤ C.real G + C.real D :=
    (measureReal_mono hEGD (measure_ne_top _ _)).trans (measureReal_union_le _ _)
  have hbg : B.real G' ≤ B.real E' :=
    measureReal_mono (fun _ h => h.2) (measure_ne_top _ _)
  have hbe : B.real E' ≤ B.real G' + B.real D' := by
    have hsub : E' ⊆ G' ∪ D' := by
      intro ω h
      by_cases hu : uniqueWordMaximum (stepWord ω)
      · exact Or.inl ⟨hu, h⟩
      · exact Or.inr hu
    exact (measureReal_mono hsub (measure_ne_top _ _)).trans (measureReal_union_le _ _)
  change |C.real E - B.real E'| ≤ C.real D
  rw [hG] at hbg hbe
  rw [hD] at hbe
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The residual event probabilities of tree and bridge differ by a vanishing
amount, uniformly over any sequence of events. -/
theorem conditioned_cyclicResidual_event_difference_tendsto_zero
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (A : ℕ → Set (List ℤ)) :
    Tendsto (fun n : ℕ =>
      |(conditioned μ n).real (finiteIncrementEvent fun x => cyclicResidual x ∈ A n) -
        (MaximumSwapLaw.bridgeCountsLaw μ n).real
          {ω | cyclicResidual (stepWord ω) ∈ A n}|) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_
    (conditioned_nonunique_maximum_tendsto_zero μ hμ)
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    eventually_size_admissible μ hμ.to_literal] with n hn hsize
  simpa only [Measure.real, finiteIncrementEvent, finiteTreeEvent] using
    conditioned_cyclicResidual_event_error_le μ (Nat.ne_of_gt hn) hsize (A n)

end
end SubcriticalCauchy.Bienayme
