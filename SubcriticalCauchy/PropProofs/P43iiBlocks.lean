module

public import SubcriticalCauchy.PropProofs.P42Aux

/-!
# Complete residual excursion blocks and their heights

This module bounds the height below the distinguished vertex by a residual-word
event, then transfers that event to the first blocks of the infinite iid walk.
-/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Topology BigOperators

namespace SubcriticalCauchy.Bienayme

noncomputable section
open BGW BGW.LocallyFinite

local instance p43iiBlocksInst1 : MeasurableSpace PlaneTree := ⊤
local instance p43iiBlocksInst2 : MeasurableSpace PlaneForest := ⊤
local instance p43iiBlocksInst3 : MeasurableSpace (List ℤ) := ⊤

/-- Maximum component height of a finite ordered forest. -/
def planeForestHeight (F : PlaneForest) : ℕ := by
  classical
  exact F.toFinset.sup height

theorem planeForestHeight_le_of_prefix {F G : PlaneForest} (h : F <+: G) :
    planeForestHeight F ≤ planeForestHeight G := by
  classical
  apply Finset.sup_le
  intro t ht
  exact Finset.le_sup (f := height)
    (List.mem_toFinset.mpr (h.subset (List.mem_toFinset.mp ht)))

/-- Some complete excursion block of a finite word has height at least `g`. -/
def listHasBlockHeight (g : ℕ) (x : List ℤ) : Prop :=
  ∃ k ≤ x.length, g ≤ planeForestHeight (decodedListForest k x)

theorem maxDegree_le_size_pred (t : PlaneTree) : maxDegree t ≤ t.size - 1 := by
  rw [maxDegree_eq_degrees_sup]
  apply Finset.sup_le
  intro d hd
  have hdmem : d ∈ t.degrees := List.mem_toFinset.mp hd
  have hle : d ≤ t.degrees.sum := by
    exact List.single_le_sum (fun _ _ => Nat.zero_le _) d hdmem
  have hs := PlaneTree.sum_degrees_add_one t
  change d ≤ t.size - 1
  omega

/-- The attached forest is itself one of the complete residual block forests. -/
theorem attachedForestHeight_le_listHasBlockHeight (t : PlaneTree) (g : ℕ)
    (hg : g ≤ attachedForestHeight t) :
    listHasBlockHeight g (cyclicResidual t.increments) := by
  refine ⟨maxDegree t, ?_, ?_⟩
  · rw [length_cyclicResidual_tree]
    exact maxDegree_le_size_pred t
  · have hd := decodedListForest_cyclicResidual t (k := maxDegree t) le_rfl
    have htake : (attachedForest t).take (maxDegree t) = attachedForest t := by
      rw [← length_attachedForest t]
      exact List.take_of_length_le le_rfl
    rw [htake] at hd
    change g ≤ planeForestHeight (attachedForest t) at hg
    rwa [hd]


/-- Attaining a farther negative level forces an earlier first passage through
every intermediate level. -/
theorem walkFirstPassage_le_of_le_of_hit (ω : ℕ → ℕ) {k N : ℕ} (h : k ≤ N)
    (hN : ∃ j, walkSum ω j = -(N : ℤ)) :
    walkFirstPassage ω k ≤ walkFirstPassage ω N := by
  let q := walkFirstPassage ω N
  have hsumN : walkSum ω q = -(N : ℤ) := walkFirstPassage_spec ω N hN
  have hsteps : ∀ a ∈ BGW.stepWord (fun i : Fin q => ω i), -1 ≤ a := by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    dsimp only [BGW.stepWord]
    omega
  have hb : ((BGW.stepWord (fun i : Fin q => ω i)).take q).sum ≤ -(k : ℤ) := by
    change prefixSum (BGW.stepWord (fun i : Fin q => ω i)) q ≤ -(k : ℤ)
    rw [prefixSum_stepWord_prefix ω le_rfl, hsumN]
    exact neg_le_neg (by exact_mod_cast h)
  obtain ⟨j, hjq, hj, _⟩ := BGW.exists_first_sum_take_eq hsteps
    (v := -(k : ℤ)) (by omega) hb
  apply le_trans (walkFirstPassage_le ω k j ?_) hjq
  rw [← prefixSum_stepWord_prefix ω hjq]
  exact hj

/-- On hitting paths, the first block forests grow by prefix. -/
theorem decodedWalkForest_prefix_of_le (ω : ℕ → ℕ) {k N : ℕ} (h : k ≤ N)
    (hk : ∃ j, walkSum ω j = -(k : ℤ)) (hN : ∃ j, walkSum ω j = -(N : ℤ)) :
    decodedWalkForest k ω <+: decodedWalkForest N ω := by
  obtain ⟨G, hGlen, hGdecode, hGinc⟩ := exists_decodedWalkForest N ω hN
  have hp := walkFirstPassage_le_of_le_of_hit ω h hN
  have htake : stoppedForestWord k ω = (stoppedForestWord N ω).take
      (walkFirstPassage ω k) := by
    unfold stoppedForestWord BGW.stepWord
    rw [← Fin.ofFn_take_eq_take_ofFn hp]
    apply congrArg List.ofFn
    funext i
    simp
  have hklen : k ≤ G.length := h.trans_eq hGlen.symm
  have htakelen : (G.take k).length = k := by simp [List.length_take, Nat.min_eq_left hklen]
  have hsplit : PlaneForest.increments G = PlaneForest.increments (G.take k) ++
      PlaneForest.increments (G.drop k) := by
    have he := congrArg PlaneForest.increments (List.take_append_drop k G)
    simpa only [PlaneForest.increments, List.map_append, List.flatten_append] using he.symm
  have hfirst := firstHit_stepWord_prefix ω hk hp
  change firstHit? k (stoppedForestWord N ω) = some (walkFirstPassage ω k) at hfirst
  rw [← hGinc] at hfirst
  have hfirstG := firstHit_forest_increments_append (G.take k)
    (PlaneForest.increments (G.drop k))
  rw [htakelen, ← hsplit] at hfirstG
  rw [hfirstG] at hfirst
  have hpEq : walkFirstPassage ω k = PlaneForest.size (G.take k) := Option.some.inj hfirst.symm
  have hstopped : stoppedForestWord k ω = PlaneForest.increments (G.take k) := by
    rw [htake, ← hGinc, hpEq, hsplit, ← PlaneForest.length_increments]
    exact List.take_left
  rw [hGdecode, decodedWalkForest, hstopped, decodeForestWord_increments]
  exact List.take_prefix k G

/-- A tall complete block in a finite prefix gives a tall tree among the first
`N` infinite-walk blocks, assuming that the infinite walk reaches `-N`. -/
theorem iidFirstBlocks_mem_compl_of_listHasBlockHeight {g N : ℕ} (hg : 0 < g)
    (ω : ℕ → ℕ) (hN : ∃ j, walkSum ω j = -(N : ℤ))
    (hblock : listHasBlockHeight g (BGW.stepWord (fun i : Fin N => ω i))) :
    iidFirstBlocks N ω ∈ (forestBelow N g)ᶜ := by
  classical
  obtain ⟨k, hkN, hk⟩ := hblock
  have hhit : firstHit? k (BGW.stepWord (fun i : Fin N => ω i)) ≠ none := by
    intro hnone
    have hz : planeForestHeight (decodedListForest k
        (BGW.stepWord (fun i : Fin N => ω i))) = 0 := by
      simp [decodedListForest, hnone, decodeForestWord, wordDegrees, planeForestHeight]
    omega
  cases hh : firstHit? k (BGW.stepWord (fun i : Fin N => ω i)) with
  | none => exact (hhit hh).elim
  | some p =>
      have hp := (firstHit_eq_some_iff k
        (BGW.stepWord (fun i : Fin N => ω i)) p).mp hh
      have hpN : p ≤ N := by simpa [BGW.stepWord] using hp.1
      have hsum : walkSum ω p = -(k : ℤ) := by
        rw [← prefixSum_stepWord_prefix ω hpN]
        exact hp.2.1
      have hkHit : ∃ j, walkSum ω j = -(k : ℤ) := ⟨p, hsum⟩
      have hpassN : walkFirstPassage ω k ≤ N :=
        (walkFirstPassage_le ω k p hsum).trans hpN
      have hdecode := decodedListForest_stepWord_eq ω hkHit hpassN
      rw [hdecode] at hk
      have hkN' : k ≤ N := by simpa [BGW.stepWord] using hkN
      have hprefix := decodedWalkForest_prefix_of_le ω hkN' hkHit hN
      have hkNTall : g ≤ planeForestHeight (decodedWalkForest N ω) :=
        hk.trans (planeForestHeight_le_of_prefix hprefix)
      obtain ⟨G, hGlen, hGdecode, hGinc⟩ := exists_decodedWalkForest N ω hN
      rw [hGdecode] at hkNTall
      change g ≤ G.toFinset.sup height at hkNTall
      obtain ⟨t, htG, ht⟩ := (Finset.le_sup_iff (a := g) (s := G.toFinset) (f := height)
        hg).mp hkNTall
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp htG)
      have hiN : i < N := by omega
      rw [Set.mem_compl_iff]
      intro hbelow
      have hnot := (mem_forestBelow N g (iidFirstBlocks N ω)).mp hbelow ⟨i, hiN⟩
      apply hnot
      have hvalue : iidFirstBlocks N ω ⟨i, hiN⟩ = (G[i]'hi).toLocallyFinite := by
        simp [iidFirstBlocks, planeForestToTrees, hGdecode, hi]
      rw [hvalue]
      exact (toLocallyFinite_mem_survivalEvent_iff _ _).mpr ht


/-- The residual-block event on a finite iid increment word is the finite
prefix of the corresponding event on the infinite iid walk. -/
theorem iid_blockHeight_finite_law (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (g N : ℕ) :
    ((Measure.pi (fun _ : Fin N => incrementLaw μ)).map List.ofFn).real
        {x | listHasBlockHeight g x} =
      (iidOffspringLaw μ).real
        {ω | listHasBlockHeight g (BGW.stepWord (fun i : Fin N => ω i))} := by
  let f : (Fin N → ℕ) → List ℤ := fun ω => BGW.stepWord ω
  let F : (ℕ → ℕ) → List ℤ := fun ω => BGW.stepWord (fun i : Fin N => ω i)
  have hpi : (Measure.pi fun _ : Fin N => incrementLaw μ) =
      (Measure.pi fun _ : Fin N => μ).map (fun z i => (z i : ℤ) - 1) := by
    symm
    simpa only [incrementLaw] using
      (Measure.pi_map_pi (μ := fun _ : Fin N => μ)
        (f := fun _ : Fin N => fun z : ℕ => (z : ℤ) - 1)
        (fun _ => (measurable_of_countable _).aemeasurable))
  have hfinmeas : Measurable f := (measurable_of_countable f)
  have hprefix : Measurable (fun (ω : ℕ → ℕ) (i : Fin N) => ω i) :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply (i : ℕ)
  have hFmeas : Measurable F :=
    (measurable_of_countable (fun w : Fin N → ℕ => BGW.stepWord w)).comp hprefix
  have hblockmeas : MeasurableSet {ω : ℕ → ℕ | listHasBlockHeight g (F ω)} := by
    have hkmeas (k : ℕ) : Measurable (fun ω : ℕ → ℕ =>
        planeForestHeight (decodedListForest k (F ω))) := by
      have hd : Measurable (fun ω : ℕ → ℕ => decodedListForest k (F ω)) := by
        exact (measurable_of_countable (fun w : Fin N → ℕ =>
          decodedListForest k (BGW.stepWord w))).comp hprefix
      exact (measurable_of_countable (fun G : PlaneForest => planeForestHeight G)).comp hd
    rw [show {ω : ℕ → ℕ | listHasBlockHeight g (F ω)} =
        ⋃ k : Fin (N + 1), {ω : ℕ → ℕ |
          g ≤ planeForestHeight (decodedListForest k.val (F ω))} by
      ext ω
      constructor
      · rintro ⟨k, hk, hkt⟩
        have hkN : k ≤ N := by simpa only [F, BGW.stepWord, List.length_ofFn] using hk
        exact Set.mem_iUnion.mpr ⟨⟨k, Nat.lt_succ_of_le hkN⟩, hkt⟩
      · intro hω
        obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hω
        exact ⟨k.val, by simpa only [F, BGW.stepWord, List.length_ofFn] using
          Nat.le_of_lt_succ k.isLt, hk⟩]
    exact MeasurableSet.iUnion fun k => measurableSet_le measurable_const (hkmeas k.val)
  have hlaw : ((Measure.pi (fun _ : Fin N => incrementLaw μ)).map List.ofFn) =
      (iidOffspringLaw μ).map F := by
    calc
      ((Measure.pi (fun _ : Fin N => incrementLaw μ)).map List.ofFn) =
          (Measure.pi (fun _ : Fin N => μ)).map f := by
        rw [hpi, Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
        simp only [Function.comp_def, f, BGW.stepWord]
      _ = ((iidOffspringLaw μ).map (fun (ω : ℕ → ℕ) (i : Fin N) => ω i)).map f := by
        rw [iidOffspringLaw_map_prefix]
      _ = (iidOffspringLaw μ).map F := by
        rw [Measure.map_map hfinmeas hprefix]
        simp only [Function.comp_def, f, F]
  rw [Measure.real, Measure.real, hlaw, Measure.map_apply hFmeas
    (Set.to_countable _).measurableSet]
  rfl

/-- The finite iid residual-block probability is bounded by the independent
forest height tail. -/
theorem iid_blockHeight_real_le_forest (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ < 1) {g N : ℕ} (hg : 0 < g) :
    ((Measure.pi (fun _ : Fin N => incrementLaw μ)).map List.ofFn).real
        {x | listHasBlockHeight g x} ≤
      (forestLaw μ N (forestBelow N g)ᶜ).toReal := by
  rw [iid_blockHeight_finite_law]
  have hle : (iidOffspringLaw μ).real
      {ω | listHasBlockHeight g (BGW.stepWord (fun i : Fin N => ω i))} ≤
      (iidOffspringLaw μ).real (iidFirstBlocks N ⁻¹' (forestBelow N g)ᶜ) := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [iid_walk_hits_negative_level_ae μ hm N] with ω hω
    exact fun hblock => iidFirstBlocks_mem_compl_of_listHasBlockHeight hg ω hω hblock
  apply hle.trans_eq
  change (iidOffspringLaw μ).real (iidFirstBlocks N ⁻¹' (forestBelow N g)ᶜ) =
    (forestLaw μ N).real (forestBelow N g)ᶜ
  rw [← iid_firstBlocks_law μ hm N, Measure.real, Measure.real,
    Measure.map_apply (measurable_iidFirstBlocks N) (measurableSet_forestBelow N g).compl]

/-- Standalone block-height bound for the conditioned tree.  The attached
forest is contained in the complete excursion blocks of the residual word. -/
theorem conditioned_attachedForestHeight_real_le
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ < 1)
    {n : ℕ} (hn : n ≠ 0)
    (hsize : bienaymeLaw μ (sizeEvent n) ≠ 0) {g : ℕ} (hg : 0 < g) :
    (conditioned μ n).real (finiteTreeEvent fun t => g ≤ attachedForestHeight t) ≤
      (forestLaw μ (n - 1) (forestBelow (n - 1) g)ᶜ).toReal +
        tvDist
          ((MaximumSwapLaw.bridgeCountsLaw μ n).map
            (fun ω => cyclicResidual (stepWord ω)))
          ((Measure.pi fun _ : Fin (n - 1) => incrementLaw μ).map List.ofFn) +
        (conditioned μ n).real
          (finiteTreeEvent fun t => ¬ uniqueWordMaximum t.increments) := by
  let A : Set (List ℤ) := {x | listHasBlockHeight g x}
  let RB := (MaximumSwapLaw.bridgeCountsLaw μ n).map
    (fun ω => cyclicResidual (stepWord ω))
  let W := (Measure.pi fun _ : Fin (n - 1) => incrementLaw μ).map List.ofFn
  let _ : IsProbabilityMeasure (MaximumSwapLaw.bridgeCountsLaw μ n) :=
    BGW.isProbabilityMeasure_cond_pi_countBridges μ hn hsize
  let _ : IsProbabilityMeasure (incrementLaw μ) := by
    unfold incrementLaw
    infer_instance
  let _ : IsProbabilityMeasure (conditioned μ n) := conditioned_isProbability μ n hsize
  have hsub : finiteTreeEvent (fun t => g ≤ attachedForestHeight t) ⊆
      finiteIncrementEvent (fun x => cyclicResidual x ∈ A) := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨t, attachedForestHeight_le_listHasBlockHeight t g ht, rfl⟩
  have hB : RB.real A = (MaximumSwapLaw.bridgeCountsLaw μ n).real
      {ω | cyclicResidual (stepWord ω) ∈ A} := by
    dsimp only [RB]
    rw [Measure.real, Measure.real, Measure.map_apply
      (measurable_of_countable _) (Set.to_countable _).measurableSet]
    rfl
  have hW : W.real A ≤ (forestLaw μ (n - 1) (forestBelow (n - 1) g)ᶜ).toReal := by
    exact iid_blockHeight_real_le_forest μ hm hg
  have htv := measureReal_le_add_tvDist RB W A
  have herr := conditioned_cyclicResidual_event_error_le μ hn hsize A
  have hle := measureReal_mono hsub (measure_ne_top (conditioned μ n) _)
  rw [hB] at htv
  have herr' := (abs_le.mp herr).2
  change (conditioned μ n).real (finiteIncrementEvent fun x => cyclicResidual x ∈ A) -
      (MaximumSwapLaw.bridgeCountsLaw μ n).real
        {ω | cyclicResidual (stepWord ω) ∈ A} ≤
    (conditioned μ n).real (finiteTreeEvent fun t => ¬ uniqueWordMaximum t.increments) at herr'
  dsimp only [RB, W, A] at hW htv herr' hle ⊢
  linarith

end
end SubcriticalCauchy.Bienayme
