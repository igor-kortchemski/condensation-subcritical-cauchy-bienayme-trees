module

public import SubcriticalCauchy.ExplorationLaw
public import SubcriticalCauchy.BienaymeForestHeight
public import BGW.LocallyFinite.ForestWalkLaw
public import SubcriticalCauchy.CyclicResidualTreeAux

/-!
# Law of the first excursions of the subcritical offspring walk

The first `k` excursions are read from the word stopped at the first passage to
`-k`.  On paths which hit that level, the stopped word is a forest code.  Its
finite cylinders therefore have exactly the product weights of independent
Bienaymé trees.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology BigOperators

namespace SubcriticalCauchy.Bienayme

noncomputable section
open BGW BGW.LocallyFinite

local instance blockLawInst1 : MeasurableSpace PlaneForest := ⊤

/-- The offspring word stopped at the first visit to `-k`. -/
def stoppedForestWord (k : ℕ) (ω : ℕ → ℕ) : List ℤ :=
  BGW.stepWord (fun i : Fin (walkFirstPassage ω k) => ω i)

/-- Total decoder for an integer word, with the empty forest as failure value. -/
def decodeForestWord (x : List ℤ) : PlaneForest :=
  (PlaneForest.ofDegrees? (wordDegrees x)).getD []

/-- The forest formed by the first `k` excursions, totalized by the empty forest. -/
def decodedWalkForest (k : ℕ) (ω : ℕ → ℕ) : PlaneForest :=
  decodeForestWord (stoppedForestWord k ω)

/-- Convert a list of at least `k` plane trees to a padded `k`-tree forest. -/
def planeForestToTrees (k : ℕ) (F : PlaneForest) : Fin k → Tree :=
  fun i => (F[i.val]?.getD PlaneTree.leaf).toLocallyFinite

/-- The first `k` excursion trees on the locally finite carrier. -/
def iidFirstBlocks (k : ℕ) (ω : ℕ → ℕ) : Fin k → Tree :=
  planeForestToTrees k (decodedWalkForest k ω)

@[simp] theorem wordDegrees_forest_increments (F : PlaneForest) :
    wordDegrees (PlaneForest.increments F) = PlaneForest.degrees F := by
  induction F with
  | nil => rfl
  | cons t F ih =>
      change wordDegrees (t.increments ++ PlaneForest.increments F) =
        t.degrees ++ PlaneForest.degrees F
      rw [show wordDegrees (t.increments ++ PlaneForest.increments F) =
        wordDegrees t.increments ++ wordDegrees (PlaneForest.increments F) by
          simp [wordDegrees]]
      rw [wordDegrees_increments, ih]

@[simp] theorem decodeForestWord_increments (F : PlaneForest) :
    decodeForestWord (PlaneForest.increments F) = F := by
  simp [decodeForestWord, wordDegrees_forest_increments]

/-- On hitting paths, a stopped word has first-passage time `n` exactly when
that length-`n` word is a `k`-tree forest code. -/
theorem walkFirstPassage_eq_iff_forestCode (k : ℕ) (ω : ℕ → ℕ)
    (h : ∃ j, walkSum ω j = -(k : ℤ)) (n : ℕ) :
    walkFirstPassage ω k = n ↔
      BGW.IsForestCode k (BGW.stepWord (fun i : Fin n => ω i)) := by
  constructor
  · rintro rfl
    have hge : ∀ a ∈ BGW.stepWord (fun i : Fin (walkFirstPassage ω k) => ω i),
        -1 ≤ a := by
      intro a ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      omega
    refine ⟨hge, ?_, ?_⟩
    · have hs := walkFirstPassage_spec ω k h
      simpa [← finiteWalkSum_eq_stepWord_sum, finiteWalkSum_prefix] using hs
    · intro i hi
      have hi' : i < walkFirstPassage ω k := by simpa [BGW.stepWord] using hi
      by_contra hle
      have hle' : ((BGW.stepWord (fun j : Fin (walkFirstPassage ω k) => ω j)).take i).sum ≤
          -(k : ℤ) := le_of_not_gt hle
      obtain ⟨j, hji, hj, _⟩ := BGW.exists_first_sum_take_eq hge
        (show -(k : ℤ) ≤ 0 by omega) hle'
      have hjn : j ≤ walkFirstPassage ω k := hji.trans hi'.le
      have hw : walkSum ω j = -(k : ℤ) := by
        rw [← prefixSum_stepWord_prefix ω hjn]
        exact hj
      have := walkFirstPassage_le ω k j hw
      omega
  · intro hx
    have hn : walkSum ω n = -k := by
      simpa only [← finiteWalkSum_eq_stepWord_sum, finiteWalkSum_prefix] using hx.2.1
    apply le_antisymm (walkFirstPassage_le ω k n (by simpa using hn))
    by_contra hlt
    have ht : walkFirstPassage ω k < n := by omega
    have hp := hx.2.2 (walkFirstPassage ω k) (by simpa [BGW.stepWord] using ht)
    change -(k : ℤ) < prefixSum _ _ at hp
    rw [prefixSum_stepWord_prefix ω ht.le, walkFirstPassage_spec ω k h] at hp
    exact lt_irrefl _ hp

/-- The stopped word is a forest code whenever the level is attained. -/
theorem isForestCode_stoppedForestWord (k : ℕ) (ω : ℕ → ℕ)
    (h : ∃ j, walkSum ω j = -(k : ℤ)) :
    BGW.IsForestCode k (stoppedForestWord k ω) := by
  exact (walkFirstPassage_eq_iff_forestCode k ω h (walkFirstPassage ω k)).mp rfl

/-- On hitting paths the stopped decoder produces a `k`-component forest with
exactly the stopped word as code. -/
theorem exists_decodedWalkForest (k : ℕ) (ω : ℕ → ℕ)
    (h : ∃ j, walkSum ω j = -(k : ℤ)) :
    ∃ F : PlaneForest, F.length = k ∧ decodedWalkForest k ω = F ∧
      PlaneForest.increments F = stoppedForestWord k ω := by
  rcases k with _ | k
  · refine ⟨[], rfl, ?_, ?_⟩
    · simp [decodedWalkForest, stoppedForestWord, walkFirstPassage_zero,
        decodeForestWord, BGW.stepWord, wordDegrees]
    · simp [stoppedForestWord, walkFirstPassage_zero, BGW.stepWord,
      PlaneForest.increments]
  · obtain ⟨F, ⟨hlen, hinc⟩, _⟩ :=
      (PlaneForest.isForestCode_iff_existsUnique (Nat.succ_pos k)
        (stoppedForestWord (k + 1) ω)).mp (isForestCode_stoppedForestWord (k + 1) ω h)
    refine ⟨F, hlen, ?_, hinc⟩
    rw [decodedWalkForest, ← hinc, decodeForestWord_increments]

/-- A forest code determines the decoded forest. -/
theorem decodedWalkForest_eq_of_increments {F : PlaneForest} {k : ℕ} {ω : ℕ → ℕ}
    (hinc : PlaneForest.increments F = stoppedForestWord k ω) :
    decodedWalkForest k ω = F := by
  rw [decodedWalkForest, ← hinc, decodeForestWord_increments]

@[simp] theorem iidFirstBlocks_of_decodedForest {F : PlaneForest} {k : ℕ} {ω : ℕ → ℕ}
    (hF : decodedWalkForest k ω = F) :
    iidFirstBlocks k ω = planeForestToTrees k F := by
  simp [iidFirstBlocks, hF]

/-- The decoder into plane forests is measurable. -/
theorem measurable_decodedWalkForest (k : ℕ) : Measurable (decodedWalkForest k) := by
  apply measurable_to_countable'
  intro F
  have hset : decodedWalkForest k ⁻¹' {F} = ⋃ n : ℕ,
      {ω | walkFirstPassage ω k = n} ∩
        (fun ω : ℕ → ℕ => (fun i : Fin n => ω i)) ⁻¹'
          {w | decodeForestWord (BGW.stepWord w) = F} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion,
      Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro h
      refine ⟨walkFirstPassage ω k, rfl, ?_⟩
      exact h
    · rintro ⟨n, hn, h⟩
      subst n
      exact h
  rw [hset]
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.inter
  · exact measurableSet_eq_fun (measurable_walkFirstPassage k) measurable_const
  · have hp : Measurable (fun (ω : ℕ → ℕ) (i : Fin n) => ω i) :=
      measurable_pi_iff.mpr fun i => measurable_pi_apply (i : ℕ)
    exact ((measurable_of_countable
      (fun w : Fin n → ℕ => decodeForestWord (BGW.stepWord w))).comp hp)
      (measurableSet_singleton F)

/-- The locally finite forest-valued stopped decoder is measurable. -/
theorem measurable_iidFirstBlocks (k : ℕ) : Measurable (iidFirstBlocks k) := by
  exact (measurable_of_countable (planeForestToTrees k)).comp
    (measurable_decodedWalkForest k)


/-- Every genuine forest word is a forest code. -/
theorem isForestCode_forest_increments (F : PlaneForest) :
    BGW.IsForestCode F.length (PlaneForest.increments F) := by
  refine ⟨?_, PlaneForest.sum_increments F, ?_⟩
  · induction F with
    | nil => simp [PlaneForest.increments]
    | cons t F ih =>
        intro a ha
        simp only [PlaneForest.increments, List.map_cons, List.flatten_cons,
          List.mem_append] at ha
        rcases ha with ha | ha
        · exact PlaneTree.neg_one_le_increment t ha
        · exact ih a ha
  · intro i hi
    exact sum_take_forest_increments_gt F (by simpa using hi)

@[simp] theorem planeForestToTrees_ofFn {k : ℕ} (F : Fin k → PlaneTree) :
    planeForestToTrees k (List.ofFn F) = fun i => (F i).toLocallyFinite := by
  funext i
  simp [planeForestToTrees]

/-- Equality of padded finite-tree forests implies equality of their underlying
lists when both have exactly `k` components. -/
theorem planeForestToTrees_inj_of_length {k : ℕ} {F G : PlaneForest}
    (hF : F.length = k) (hG : G.length = k)
    (h : planeForestToTrees k F = planeForestToTrees k G) : F = G := by
  apply List.ext_getElem (hF.trans hG.symm)
  intro i hiF hiG
  have hik : i < k := by omega
  have he := congrFun h ⟨i, hik⟩
  simp only [planeForestToTrees, List.getElem?_eq_getElem, hiF, hiG,
    Option.getD_some] at he
  exact PlaneTree.toLocallyFinite_injective he

/-- On a path hitting `-k`, selecting a given finite forest is exactly the
cylinder given by its Łukasiewicz word. -/
theorem iidFirstBlocks_eq_ofFn_iff {k : ℕ} (ω : ℕ → ℕ)
    (h : ∃ j, walkSum ω j = -(k : ℤ)) (F : Fin k → PlaneTree) :
    iidFirstBlocks k ω = (fun i => (F i).toLocallyFinite) ↔
      BGW.stepWord (fun i : Fin (PlaneForest.size (List.ofFn F)) => ω i) =
        PlaneForest.increments (List.ofFn F) := by
  constructor
  · intro hout
    obtain ⟨G, hlen, hdecode, hinc⟩ := exists_decodedWalkForest k ω h
    have hGF : G = List.ofFn F := by
      apply planeForestToTrees_inj_of_length hlen (by simp)
      calc
        planeForestToTrees k G = iidFirstBlocks k ω :=
          (iidFirstBlocks_of_decodedForest hdecode).symm
        _ = (fun i => (F i).toLocallyFinite) := hout
        _ = planeForestToTrees k (List.ofFn F) := (planeForestToTrees_ofFn F).symm
    rw [hGF] at hinc
    have hn : walkFirstPassage ω k = PlaneForest.size (List.ofFn F) := by
      have hh := congrArg List.length hinc
      simpa only [PlaneForest.length_increments, stoppedForestWord,
        BGW.stepWord, List.length_ofFn] using hh.symm
    rw [← hn]
    exact hinc.symm
  · intro hc
    have hcode : BGW.IsForestCode k
        (BGW.stepWord (fun i : Fin (PlaneForest.size (List.ofFn F)) => ω i)) := by
      rw [hc]
      simpa using isForestCode_forest_increments (List.ofFn F)
    have hn := (walkFirstPassage_eq_iff_forestCode k ω h
      (PlaneForest.size (List.ofFn F))).mpr hcode
    have hinc : PlaneForest.increments (List.ofFn F) = stoppedForestWord k ω := by
      rw [stoppedForestWord, hn]
      exact hc.symm
    have hd := decodedWalkForest_eq_of_increments hinc
    rw [iidFirstBlocks_of_decodedForest hd, planeForestToTrees_ofFn]

/-- The atom of a finite forest under the stopped iid walk is the product of
its Bienaymé tree atoms. -/
theorem iid_firstBlocks_atom (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ < 1) (k : ℕ) (F : Fin k → PlaneTree) :
    iidOffspringLaw μ {ω | iidFirstBlocks k ω = fun i => (F i).toLocallyFinite} =
      ∏ i, bienaymeLaw μ {(F i).toLocallyFinite} := by
  let N := PlaneForest.size (List.ofFn F)
  let A : Set (Fin N → ℕ) :=
    {w | BGW.stepWord w = PlaneForest.increments (List.ofFn F)}
  have heq : {ω | iidFirstBlocks k ω = fun i => (F i).toLocallyFinite} =ᵐ[iidOffspringLaw μ]
      (fun ω (i : Fin N) => ω i) ⁻¹' A := by
    filter_upwards [iid_walk_hits_negative_level_ae μ hm k] with ω hω
    exact propext (iidFirstBlocks_eq_ofFn_iff ω hω F)
  rw [measure_congr heq, iidOffspringLaw_prefix_event μ N A]
  have hge : ∀ a ∈ PlaneForest.increments (List.ofFn F), -1 ≤ a :=
    (isForestCode_forest_increments (List.ofFn F)).1
  obtain ⟨w, hw⟩ := BGW.exists_stepWord_eq_of_entries
    (n := N) (x := PlaneForest.increments (List.ofFn F)) (by simp [N]) hge
  have hA : A = {w} := by
    ext w'
    simp only [A, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact ⟨fun h => BGW.stepWord_injective (h.trans hw.symm), fun h => by simpa [h] using hw⟩
  rw [hA, Measure.pi_singleton, ← BGW.walkWeight_stepWord (fun d => μ {d}) w, hw,
    PlaneForest.walkWeight_increments]
  simp only [List.map_ofFn, List.prod_ofFn]
  apply Finset.prod_congr rfl
  intro i _
  exact (bienaymeLaw_toLocallyFinite μ (F i)).symm

/-- Measure of a set as the sum of atoms indexed by a countable range which
carries almost all mass. -/
theorem measure_eq_tsum_atoms_of_ae_range {α β : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable β] (f : β → α) (hf : Function.Injective f)
    (P : Measure α) (hP : ∀ᵐ x ∂P, x ∈ Set.range f) (A : Set α) (hA : MeasurableSet A) :
    P A = ∑' b, (f ⁻¹' A).indicator (fun b => P {f b}) b := by
  have hdecomp : A ∩ Set.range f = ⋃ b : β, A ∩ {f b} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_range, Set.mem_iUnion, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hA', b, rfl⟩
      exact ⟨b, hA', rfl⟩
    · rintro ⟨b, hA', rfl⟩
      exact ⟨hA', b, rfl⟩
  have hdisj : Pairwise (fun b c : β => Disjoint (A ∩ {f b}) (A ∩ {f c})) := by
    intro b c hbc
    apply Set.disjoint_left.mpr
    rintro x ⟨_, hx⟩ ⟨_, hx'⟩
    apply hbc
    apply hf
    rw [show f b = x from hx.symm, show f c = x from hx'.symm]
  have hmeas (b : β) : MeasurableSet (A ∩ {f b}) := hA.inter (measurableSet_singleton _)
  calc
    P A = P (A ∩ Set.range f) := by
      apply measure_congr
      filter_upwards [hP] with x hx
      simp [hx]
    _ = P (⋃ b : β, A ∩ {f b}) := by rw [hdecomp]
    _ = ∑' b, P (A ∩ {f b}) := measure_iUnion hdisj hmeas
    _ = ∑' b, (f ⁻¹' A).indicator (fun b => P {f b}) b := by
      apply tsum_congr
      intro b
      by_cases hb : f b ∈ A <;> simp [Set.indicator, hb]

/-- **Block law.** The first `k` excursions of the subcritical iid offspring
walk have exactly the law of `k` independent Bienaymé trees. -/
theorem iid_firstBlocks_law (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ < 1) (k : ℕ) :
    (iidOffspringLaw μ).map (iidFirstBlocks k) = forestLaw μ k := by
  let f : (Fin k → PlaneTree) → (Fin k → Tree) := fun F i => (F i).toLocallyFinite
  have hf : Function.Injective f := by
    intro F G h
    funext i
    exact PlaneTree.toLocallyFinite_injective (congrFun h i)
  have hP : ∀ᵐ G ∂((iidOffspringLaw μ).map (iidFirstBlocks k)), G ∈ Set.range f := by
    change ∀ᵐ G ∂((iidOffspringLaw μ).map (iidFirstBlocks k)), ∃ F, f F = G
    rw [ae_map_iff (measurable_iidFirstBlocks k).aemeasurable
      (Set.countable_range f).measurableSet]
    apply Filter.Eventually.of_forall
    intro ω
    refine ⟨fun i => ((decodedWalkForest k ω)[i.val]?.getD PlaneTree.leaf), ?_⟩
    funext i
    rfl
  have hQ : ∀ᵐ G ∂forestLaw μ k, G ∈ Set.range f := by
    have hfin : ∀ i : Fin k, ∀ᵐ T ∂bienaymeLaw μ, FiniteVertices T :=
      fun _ => ae_finite_of_subcritical μ hm
    have hall : ∀ᵐ G ∂forestLaw μ k, ∀ i, FiniteVertices (G i) := by
      rw [forestLaw]
      exact eventually_all.2 fun i => (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin k => bienaymeLaw μ) (i := i)).eventually (hfin i)
    filter_upwards [hall] with G hG
    choose F hF using fun i => (exists_toLocallyFinite_iff (G i)).mpr (hG i)
    exact ⟨F, funext hF⟩
  ext A hA
  have hAtomP (F : Fin k → PlaneTree) :
      ((iidOffspringLaw μ).map (iidFirstBlocks k)) {f F} =
        ∏ i, bienaymeLaw μ {(F i).toLocallyFinite} := by
    rw [Measure.map_apply (measurable_iidFirstBlocks k) (measurableSet_singleton _)]
    exact iid_firstBlocks_atom μ hm k F
  have hAtomQ (F : Fin k → PlaneTree) :
      forestLaw μ k {f F} = ∏ i, bienaymeLaw μ {(F i).toLocallyFinite} := by
    rw [forestLaw, Measure.pi_singleton]
  calc
    ((iidOffspringLaw μ).map (iidFirstBlocks k)) A =
        ∑' F, (f ⁻¹' A).indicator (fun F => ((iidOffspringLaw μ).map (iidFirstBlocks k)) {f F}) F :=
      measure_eq_tsum_atoms_of_ae_range f hf _ hP A hA
    _ = ∑' F, (f ⁻¹' A).indicator (fun F => forestLaw μ k {f F}) F := by
      apply tsum_congr
      intro F
      simp only [hAtomP, hAtomQ]
    _ = forestLaw μ k A := (measure_eq_tsum_atoms_of_ae_range f hf _ hQ A hA).symm

end
end SubcriticalCauchy.Bienayme
