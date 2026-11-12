module

public import SubcriticalCauchy.PropProofs.BlockLaw
public import SubcriticalCauchy.CyclicResidualTree
public import SubcriticalCauchy.M3Transfer
public import SubcriticalCauchy.MainProofs.M1
public import SubcriticalCauchy.AttachedSlots

/-! # Total-variation assembly for Proposition 4.2 -/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Topology BigOperators

namespace SubcriticalCauchy.Bienayme

noncomputable section
open BGW BGW.LocallyFinite

local instance p42AuxInst1 : MeasurableSpace PlaneTree := ⊤
local instance p42AuxInst2 : MeasurableSpace PlaneForest := ⊤
local instance p42AuxInst3 : MeasurableSpace (List ℤ) := ⊤

/-- Cut a finite increment word at its first visit to `-k` and decode the
resulting forest. -/
def decodedListForest (k : ℕ) (x : List ℤ) : PlaneForest :=
  decodeForestWord (x.take ((firstHit? k x).getD 0))

/-- The first `k` finite trees encoded by a finite increment word. -/
def listFirstBlocks (k : ℕ) (x : List ℤ) : PlaneForest := decodedListForest k x

/-- The first `k` attached subtrees are a function of the cyclic residual,
whenever those slots are present. -/
theorem decodedListForest_cyclicResidual (t : PlaneTree) {k : ℕ}
    (hk : k ≤ maxDegree t) :
    decodedListForest k (cyclicResidual t.increments) = (attachedForest t).take k := by
  rw [decodedListForest, firstHit_cyclicResidual_take_attachedForest t hk,
    Option.getD_some, take_firstHit_eq_attachedForest_take, decodeForestWord_increments]

/-- Event probabilities differ by at most the total variation distance, on any
measurable carrier. -/
theorem abs_measureReal_sub_le_tvDist_general {α : Type*} [MeasurableSpace α]
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (A : Set α) (hA : MeasurableSet A) :
    |P.real A - Q.real A| ≤ tvDist P Q := by
  let V := P.toSignedMeasure - Q.toSignedMeasure
  have htop : V.variation Set.univ ≠ ∞ := by
    change (VectorMeasure.etvDist P.toSignedMeasure Q.toSignedMeasure) ≠ ∞
    rw [← etvDist_eq_etvDist_toSignedMeasure]
    exact etvDist_ne_top P Q
  have htopA : V.variation A ≠ ∞ :=
    ne_top_of_le_ne_top htop (measure_mono (Set.subset_univ A))
  have hv := VectorMeasure.norm_measure_le_variation (μ := V) (E := A) htopA
  rw [Measure.toSignedMeasure_sub_apply hA, Real.norm_eq_abs] at hv
  apply hv.trans
  rw [tvDist, etvDist_eq_etvDist_toSignedMeasure]
  exact measureReal_mono (Set.subset_univ A) htop

/-- Real masses of fibers of a countable-codomain map sum to the total mass. -/
theorem tsum_measureReal_fiber {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [Countable β] [MeasurableSingletonClass β]
    (P : Measure α) [IsFiniteMeasure P] (f : α → β) (hf : Measurable f) :
    (∑' b, P.real (f ⁻¹' {b})) = P.real Set.univ := by
  have h := tsum_measure_preimage_singleton (μ := P)
    (Set.countable_univ : (Set.univ : Set β).Countable)
    (fun b _ => hf (measurableSet_singleton b))
  simp only [Set.preimage_univ] at h
  have h' : (∑' b : β, P (f ⁻¹' {b})) = P Set.univ :=
    ((Equiv.Set.univ β).tsum_eq (fun b : β => P (f ⁻¹' {b}))).symm.trans h
  change (∑' b : β, (P (f ⁻¹' {b})).toReal) = (P Set.univ).toReal
  rw [← h', ENNReal.tsum_toReal_eq]
  exact fun _ => measure_ne_top _ _

/-- Two pushforwards of one probability measure differ by at most twice the
mass of an event on which the two functions agree. -/
theorem tvDist_map_le_of_eqOn {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [Countable β] [MeasurableSingletonClass β]
    (P : Measure α) [IsProbabilityMeasure P] (f g : α → β)
    (hf : Measurable f) (hg : Measurable g) (E : Set α) (hE : MeasurableSet E)
    (hfg : Set.EqOn f g E) :
    tvDist (P.map f) (P.map g) ≤ 2 * P.real Eᶜ := by
  let R := P.restrict Eᶜ
  have hsumf : Summable (fun b => R.real (f ⁻¹' {b})) := by
    apply ENNReal.summable_toReal
    have h := tsum_measure_preimage_singleton (μ := R)
      (Set.countable_univ : (Set.univ : Set β).Countable)
      (fun b _ => hf (measurableSet_singleton b))
    simp only [Set.preimage_univ] at h
    have h' : (∑' b : β, R (f ⁻¹' {b})) = R Set.univ :=
      ((Equiv.Set.univ β).tsum_eq (fun b : β => R (f ⁻¹' {b}))).symm.trans h
    rw [h']
    exact measure_ne_top _ _
  have hsumg : Summable (fun b => R.real (g ⁻¹' {b})) := by
    apply ENNReal.summable_toReal
    have h := tsum_measure_preimage_singleton (μ := R)
      (Set.countable_univ : (Set.univ : Set β).Countable)
      (fun b _ => hg (measurableSet_singleton b))
    simp only [Set.preimage_univ] at h
    have h' : (∑' b : β, R (g ⁻¹' {b})) = R Set.univ :=
      ((Equiv.Set.univ β).tsum_eq (fun b : β => R (g ⁻¹' {b}))).symm.trans h
    rw [h']
    exact measure_ne_top _ _
  have hbound (b : β) :
      |(P.map f).real {b} - (P.map g).real {b}| ≤
        R.real (f ⁻¹' {b}) + R.real (g ⁻¹' {b}) := by
    have hfb : MeasurableSet (f ⁻¹' {b}) := hf (measurableSet_singleton b)
    have hgb : MeasurableSet (g ⁻¹' {b}) := hg (measurableSet_singleton b)
    have hinter : f ⁻¹' {b} ∩ E = g ⁻¹' {b} ∩ E := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
      exact and_congr_left fun hx => by rw [hfg hx]
    have hsplitf := measureReal_inter_add_sdiff (μ := P) (s := f ⁻¹' {b}) hE
    have hsplitg := measureReal_inter_add_sdiff (μ := P) (s := g ⁻¹' {b}) hE
    have hreal (A : Set α) (hA : MeasurableSet A) :
        R.real A = P.real (A \ E) := by
      change (P.restrict Eᶜ A).toReal = (P (A \ E)).toReal
      rw [Measure.restrict_apply hA]
      congr 2
    change |((P.map f) {b}).toReal - ((P.map g) {b}).toReal| ≤ _
    rw [Measure.map_apply hf (measurableSet_singleton b),
      Measure.map_apply hg (measurableSet_singleton b)]
    change |P.real (f ⁻¹' {b}) - P.real (g ⁻¹' {b})| ≤ _
    rw [hreal (f ⁻¹' {b}) hfb, hreal (g ⁻¹' {b}) hgb]
    rw [← hsplitf, ← hsplitg, hinter]
    have heq :
        P.real (g ⁻¹' {b} ∩ E) + P.real (f ⁻¹' {b} \ E) -
          (P.real (g ⁻¹' {b} ∩ E) + P.real (g ⁻¹' {b} \ E)) =
        P.real (f ⁻¹' {b} \ E) - P.real (g ⁻¹' {b} \ E) := by ring
    rw [heq]
    calc
      |P.real (f ⁻¹' {b} \ E) - P.real (g ⁻¹' {b} \ E)| ≤
          |P.real (f ⁻¹' {b} \ E)| + |P.real (g ⁻¹' {b} \ E)| := abs_sub _ _
      _ = P.real (f ⁻¹' {b} \ E) + P.real (g ⁻¹' {b} \ E) := by
        rw [abs_of_nonneg measureReal_nonneg, abs_of_nonneg measureReal_nonneg]
  have habs : Summable (fun b => |(P.map f).real {b} - (P.map g).real {b}|) :=
    (hsumf.add hsumg).of_norm_bounded (fun b => by
      simpa only [Real.norm_eq_abs, abs_abs] using hbound b)
  rw [tvDist_eq_tsum_abs]
  calc
    (∑' b, |(P.map f).real {b} - (P.map g).real {b}|) ≤
        ∑' b, (R.real (f ⁻¹' {b}) + R.real (g ⁻¹' {b})) := by
      exact habs.tsum_le_tsum hbound (hsumf.add hsumg)
    _ = (∑' b, R.real (f ⁻¹' {b})) + ∑' b, R.real (g ⁻¹' {b}) :=
      hsumf.tsum_add hsumg
    _ = R.real Set.univ + R.real Set.univ := by
      rw [tsum_measureReal_fiber R f hf, tsum_measureReal_fiber R g hg]
    _ = 2 * P.real Eᶜ := by
      rw [Measure.real, Measure.real, Measure.restrict_apply MeasurableSet.univ]
      simp only [Set.univ_inter]
      ring

/-- The conditioned law transported to the countable type of finite plane trees. -/
def conditionedPlaneTreeLaw (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) :
    Measure PlaneTree :=
  Measure.sum fun t : PlaneTree => conditioned μ n {t.toLocallyFinite} • Measure.dirac t

/-- At admissible sizes the transported conditioned law is a probability measure. -/
theorem conditionedPlaneTreeLaw_isProbability (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {n : ℕ} (hsize : bienaymeLaw μ (sizeEvent n) ≠ 0) :
    IsProbabilityMeasure (conditionedPlaneTreeLaw μ n) := by
  let a : PlaneTree → ℝ≥0∞ := fun t => conditioned μ n {t.toLocallyFinite}
  have hsupp : Function.support a ⊆ Set.range
      (fun t : {t : PlaneTree // t.size = n} => t.1) := by
    intro t ht
    by_cases htn : t.size = n
    · exact ⟨⟨t, htn⟩, rfl⟩
    · exfalso
      apply ht
      dsimp only [a]
      change (bienaymeLaw μ)[|sizeEvent n] {t.toLocallyFinite} = 0
      rw [cond_sizeEvent_singleton μ n t]
      simp [htn]
  have hsum : (∑' t : {t : PlaneTree // t.size = n}, a t.1) = ∑' t : PlaneTree, a t :=
    (Subtype.val_injective : Function.Injective
      (fun t : {t : PlaneTree // t.size = n} => t.1)).tsum_eq hsupp
  have hone : (∑' t : {t : PlaneTree // t.size = n}, a t.1) = 1 := by
    let _ : IsProbabilityMeasure (conditioned μ n) := conditioned_isProbability μ n hsize
    have h := conditioned_apply_eq_tsum μ n Set.univ MeasurableSet.univ
    simpa only [a, Set.mem_univ, ite_true, mul_one, measure_univ] using h.symm
  refine ⟨?_⟩
  rw [conditionedPlaneTreeLaw, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply,
    Set.indicator_univ, Pi.one_apply, mul_one]
  exact hsum.symm.trans hone

/-- The frozen attached-slot law is the pushforward of the transported
conditioned plane-tree law. -/
theorem attachedSlotsLaw_eq_map (μ : Measure ℕ) [IsProbabilityMeasure μ] (n k : ℕ) :
    attachedSlotsLaw μ n k = (conditionedPlaneTreeLaw μ n).map (attachedSlotsTree k) := by
  rw [conditionedPlaneTreeLaw, Measure.map_sum (measurable_of_countable _).aemeasurable]
  rw [attachedSlotsLaw]
  congr 1
  funext t
  rw [Measure.map_smul _ (measurable_of_countable _).aemeasurable,
    Measure.map_dirac' (measurable_of_countable _)]


/-- The padded list of attached subtrees agrees with the list decoder on every
slot, including absent slots. -/
theorem attachedSlotsTree_eq_planeForestToTrees (k : ℕ) (t : PlaneTree) :
    attachedSlotsTree k t = planeForestToTrees k ((attachedForest t).take k) := by
  funext i
  simp [attachedSlotsTree, planeForestToTrees, attachedChild,
    List.getElem?_take_of_lt i.isLt]

/-- Transporting the conditioned plane-tree measure back to the locally finite
carrier recovers the original conditioned law. -/
theorem conditionedPlaneTreeLaw_map_toLocallyFinite (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (n : ℕ) :
    (conditionedPlaneTreeLaw μ n).map PlaneTree.toLocallyFinite = conditioned μ n := by
  classical
  ext A hA
  rw [Measure.map_apply (measurableEmbedding_toLocallyFinite.measurable) hA,
    conditionedPlaneTreeLaw, Measure.sum_apply _
      ((measurableEmbedding_toLocallyFinite.measurable hA)),
    conditioned_apply_eq_tsum μ n A hA]
  let f : PlaneTree → ℝ≥0∞ := fun t => conditioned μ n {t.toLocallyFinite} *
    (if t.toLocallyFinite ∈ A then 1 else 0)
  have hsupp : Function.support f ⊆ Set.range
      (fun t : {t : PlaneTree // t.size = n} => t.1) := by
    intro t ht
    by_cases htn : t.size = n
    · exact ⟨⟨t, htn⟩, rfl⟩
    · exfalso
      apply ht
      dsimp only [f]
      have hz : conditioned μ n {t.toLocallyFinite} = 0 := by
        change (bienaymeLaw μ)[|sizeEvent n] {t.toLocallyFinite} = 0
        rw [cond_sizeEvent_singleton μ n t]
        simp [htn]
      rw [hz, zero_mul]
  have hsum : (∑' t : {t : PlaneTree // t.size = n}, f t.1) = ∑' t : PlaneTree, f t :=
    (Subtype.val_injective : Function.Injective
      (fun t : {t : PlaneTree // t.size = n} => t.1)).tsum_eq hsupp
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply]
  symm
  exact hsum

/-- An increment word contains the stopped forest word whenever its length is
at least the first-passage time. -/
theorem firstHit_stepWord_prefix (ω : ℕ → ℕ) {k N : ℕ}
    (h : ∃ j, walkSum ω j = -(k : ℤ)) (hN : walkFirstPassage ω k ≤ N) :
    firstHit? k (BGW.stepWord (fun i : Fin N => ω i)) = some (walkFirstPassage ω k) := by
  rw [firstHit_eq_some_iff]
  refine ⟨by simpa [BGW.stepWord] using hN, ?_, ?_⟩
  · rw [prefixSum_stepWord_prefix ω hN]
    exact walkFirstPassage_spec ω k h
  · intro j hj
    rw [prefixSum_stepWord_prefix ω (hj.le.trans hN)]
    intro he
    have hp := walkFirstPassage_le ω k j he
    omega

/-- On a sufficiently long finite prefix, the finite-list and infinite-walk
forest decoders coincide. -/
theorem decodedListForest_stepWord_eq (ω : ℕ → ℕ) {k N : ℕ}
    (h : ∃ j, walkSum ω j = -(k : ℤ)) (hN : walkFirstPassage ω k ≤ N) :
    decodedListForest k (BGW.stepWord (fun i : Fin N => ω i)) = decodedWalkForest k ω := by
  rw [decodedListForest, firstHit_stepWord_prefix ω h hN, Option.getD_some,
    decodedWalkForest, stoppedForestWord]
  congr 1
  unfold BGW.stepWord
  rw [← Fin.ofFn_take_eq_take_ofFn hN]
  apply congrArg List.ofFn
  funext i
  simp

/-- The finite-product decoder is the prefix pushforward of the corresponding
function on infinite iid words. -/
theorem finiteDecodedForestLaw_eq_iid_map (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (k N : ℕ) :
    (Measure.pi (fun _ : Fin N => μ)).map
        (fun ω => decodedListForest k (BGW.stepWord ω)) =
      (iidOffspringLaw μ).map (fun ω =>
        decodedListForest k (BGW.stepWord (fun i : Fin N => ω i))) := by
  rw [← iidOffspringLaw_map_prefix μ N, Measure.map_map
    (g := fun ω : Fin N → ℕ => decodedListForest k (BGW.stepWord ω))
    (f := fun (ω : ℕ → ℕ) (i : Fin N) => ω i)
    (measurable_of_countable _)
    (measurable_pi_iff.mpr fun i => measurable_pi_apply (i : ℕ))]
  simp only [Function.comp_def]


/-- A uniform bound on every measurable event error controls total variation. -/
theorem tvDist_le_two_of_event_error {α : Type*} [MeasurableSpace α]
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (c : ℝ)
    (h : ∀ A : Set α, MeasurableSet A → |P.real A - Q.real A| ≤ c) :
    tvDist P Q ≤ 2 * c := by
  classical
  rw [tvDist_eq_iSup_finPartition_abs]
  refine ciSup_le fun P0 => ?_
  let d : {A : Set α // MeasurableSet A} → ℝ := fun A => P.real A - Q.real A
  let S := P0.parts.filter (fun p => 0 ≤ d p)
  let T := P0.parts.filter (fun p => ¬ 0 ≤ d p)
  let U : Set α := ⋃ p ∈ S, (p : Set α)
  let V : Set α := ⋃ p ∈ T, (p : Set α)
  have hU : MeasurableSet U := S.measurableSet_biUnion (fun p _ => p.property)
  have hV : MeasurableSet V := T.measurableSet_biUnion (fun p _ => p.property)
  have hdisjS : (↑S : Set {A : Set α // MeasurableSet A}).PairwiseDisjoint (fun p => (p : Set α)) := by
    intro p hp q hq hpq
    exact (disjoint_subtype_iff (fun _ _ hs ht => hs.inter ht) _).1
      (P0.disjoint (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1 hpq)
  have hdisjT : (↑T : Set {A : Set α // MeasurableSet A}).PairwiseDisjoint (fun p => (p : Set α)) := by
    intro p hp q hq hpq
    exact (disjoint_subtype_iff (fun _ _ hs ht => hs.inter ht) _).1
      (P0.disjoint (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1 hpq)
  have hPU : P.real U = ∑ p ∈ S, P.real p :=
    measureReal_biUnion_finset hdisjS (fun p _ => p.property)
  have hQU : Q.real U = ∑ p ∈ S, Q.real p :=
    measureReal_biUnion_finset hdisjS (fun p _ => p.property)
  have hPV : P.real V = ∑ p ∈ T, P.real p :=
    measureReal_biUnion_finset hdisjT (fun p _ => p.property)
  have hQV : Q.real V = ∑ p ∈ T, Q.real p :=
    measureReal_biUnion_finset hdisjT (fun p _ => p.property)
  have hsumU : (∑ p ∈ S, d p) = P.real U - Q.real U := by
    rw [hPU, hQU, Finset.sum_sub_distrib]
  have hsumV : (∑ p ∈ T, -d p) = Q.real V - P.real V := by
    calc
      (∑ p ∈ T, -d p) = ∑ p ∈ T, (Q.real p - P.real p) := by
        apply Finset.sum_congr rfl
        intro p _
        dsimp only [d]
        ring
      _ = Q.real V - P.real V := by rw [hPV, hQV, Finset.sum_sub_distrib]
  have hneg : Q.real V - P.real V ≤ c := by
    have hh := (abs_le.mp (h V hV)).1
    linarith
  change (∑ p ∈ P0.parts, |d p|) ≤ 2 * c
  calc
    (∑ p ∈ P0.parts, |P.real p - Q.real p|) =
        (∑ p ∈ S, |d p|) + ∑ p ∈ T, |d p| := by
      exact (Finset.sum_filter_add_sum_filter_not P0.parts
        (fun p => 0 ≤ d p) (fun p => |d p|)).symm
    _ = (∑ p ∈ S, d p) + ∑ p ∈ T, -d p := by
      congr 1
      · apply Finset.sum_congr rfl
        intro p hp
        exact abs_of_nonneg (Finset.mem_filter.mp hp).2
      · apply Finset.sum_congr rfl
        intro p hp
        exact abs_of_neg (lt_of_not_ge (Finset.mem_filter.mp hp).2)
    _ = (P.real U - Q.real U) + (Q.real V - P.real V) := by rw [hsumU, hsumV]
    _ ≤ c + c := add_le_add ((abs_le.mp (h U hU)).2) hneg
    _ = 2 * c := by ring


/-- Events on the transported plane-tree law have the original conditioned
probability. -/
theorem conditionedPlaneTreeLaw_finiteTreeEvent (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (n : ℕ) (P : PlaneTree → Prop) :
    (conditionedPlaneTreeLaw μ n).real {t | P t} =
      (conditioned μ n).real (finiteTreeEvent P) := by
  have hpre : PlaneTree.toLocallyFinite ⁻¹' finiteTreeEvent P = {t | P t} := by
    ext t
    simp [finiteTreeEvent, PlaneTree.toLocallyFinite_injective.eq_iff]
  change (conditionedPlaneTreeLaw μ n {t | P t}).toReal =
    (conditioned μ n (finiteTreeEvent P)).toReal
  have hmeas : MeasurableSet (finiteTreeEvent P) :=
    (Set.to_countable {t : PlaneTree | P t}).image PlaneTree.toLocallyFinite |>.measurableSet
  rw [← conditionedPlaneTreeLaw_map_toLocallyFinite μ n,
    Measure.map_apply (measurableEmbedding_toLocallyFinite.measurable) hmeas, hpre]

/-- The conditioned residual and bridge residual differ in TV by at most twice
the non-unique-maximum probability. -/
theorem conditioned_residual_tvDist_le (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : n ≠ 0) (hsize : bienaymeLaw μ (sizeEvent n) ≠ 0) :
    tvDist
      ((conditionedPlaneTreeLaw μ n).map (fun t => cyclicResidual t.increments))
      ((MaximumSwapLaw.bridgeCountsLaw μ n).map (fun ω => cyclicResidual (stepWord ω))) ≤
    2 * (conditioned μ n).real (finiteTreeEvent fun t => ¬ uniqueWordMaximum t.increments) := by
  let _ : IsProbabilityMeasure (conditionedPlaneTreeLaw μ n) :=
    conditionedPlaneTreeLaw_isProbability μ hsize
  let _ : IsProbabilityMeasure (MaximumSwapLaw.bridgeCountsLaw μ n) :=
    BGW.isProbabilityMeasure_cond_pi_countBridges μ hn hsize
  apply tvDist_le_two_of_event_error
  intro A hA
  have hpre : (fun t : PlaneTree => cyclicResidual t.increments) ⁻¹' A =
      PlaneTree.toLocallyFinite ⁻¹' finiteIncrementEvent (fun x => cyclicResidual x ∈ A) := by
    ext t
    simp only [Set.mem_preimage, toLocallyFinite_mem_finiteIncrementEvent_iff]
  change |((conditionedPlaneTreeLaw μ n).map
      (fun t => cyclicResidual t.increments) A).toReal -
    ((MaximumSwapLaw.bridgeCountsLaw μ n).map
      (fun ω => cyclicResidual (stepWord ω)) A).toReal| ≤ _
  rw [Measure.map_apply (measurable_of_countable _) hA,
    Measure.map_apply (measurable_of_countable _) hA, hpre,
    ← Measure.map_apply (measurableEmbedding_toLocallyFinite.measurable)
      (measurableSet_finiteIncrementEvent (fun x => cyclicResidual x ∈ A)),
    conditionedPlaneTreeLaw_map_toLocallyFinite]
  change |(conditioned μ n (finiteIncrementEvent fun x => cyclicResidual x ∈ A)).toReal -
    ((MaximumSwapLaw.bridgeCountsLaw μ n) {ω | cyclicResidual (stepWord ω) ∈ A}).toReal| ≤
      (conditioned μ n).real (finiteTreeEvent fun t => ¬ uniqueWordMaximum t.increments)
  exact conditioned_cyclicResidual_event_error_le μ hn hsize A

/-- Decoding the iid increment word is the same as decoding the corresponding
finite offspring-count word. -/
theorem decoded_increment_word_law (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (k N : ℕ) :
    (((Measure.pi (fun _ : Fin N => incrementLaw μ)).map List.ofFn).map
        (decodedListForest k)) =
      (Measure.pi (fun _ : Fin N => μ)).map
        (fun ω => decodedListForest k (BGW.stepWord ω)) := by
  rw [pi_incrementLaw_eq_map, Measure.map_map (measurable_of_countable _)
    (measurable_of_countable _), Measure.map_map (measurable_of_countable _)
    (measurable_pi_iff.mpr fun i => measurable_of_countable _)]
  simp only [Function.comp_def, BGW.stepWord]

/-- Passage times beyond the finite prefix form a vanishing event along
`k = ⌊δn⌋` for `0 ≤ δ < 1-m`. -/
theorem iid_walkFirstPassage_floor_gt_pred_tendsto_zero
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 - (offspringMean μ).toReal) :
    Tendsto (fun n : ℕ => (iidOffspringLaw μ).real
      {ω | ¬ walkFirstPassage ω ⌊δ * (n : ℝ)⌋₊ ≤ n - 1}) atTop (𝓝 0) := by
  by_cases hδ : δ = 0
  · subst δ
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    simp [Nat.floor_zero, walkFirstPassage_zero]
  · have hδpos : 0 < δ := lt_of_le_of_ne hδ0 (Ne.symm hδ)
    have hfin : offspringMean μ ≠ ∞ := ne_top_of_lt (hμ.1.trans ENNReal.one_lt_top)
    have hmR : (offspringMean μ).toReal < 1 := by
      simpa using (ENNReal.toReal_lt_toReal hfin ENNReal.one_ne_top).mpr hμ.1
    let γ := 1 - (offspringMean μ).toReal
    have hγ : 0 < γ := by dsimp [γ]; linarith
    let r := δ / γ
    have hr : r < 1 := by
      dsimp [r, γ]
      exact (div_lt_one hγ).mpr hδ1
    have hr0 : 0 ≤ r := div_nonneg hδ0 hγ.le
    have hε : 0 < 1 - r := sub_pos.mpr hr
    have hdev := (tendstoInMeasure_iff_measureReal_norm.mp
      (iid_walkFirstPassage_ratio_tendstoInMeasure μ hμ.1 hδpos)) (1 - r) hε
    simp only [Real.norm_eq_abs] at hdev
    apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_ hdev
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    apply measureReal_mono _ (measure_ne_top _ _)
    intro ω hbad
    change ¬ walkFirstPassage ω ⌊δ * (n : ℝ)⌋₊ ≤ n - 1 at hbad
    have hge : n ≤ walkFirstPassage ω ⌊δ * (n : ℝ)⌋₊ := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hratio : (1 : ℝ) ≤
        (walkFirstPassage ω ⌊δ * (n : ℝ)⌋₊ : ℝ) / (n : ℝ) := by
      apply (le_div_iff₀ hnR).mpr
      simpa using (show (n : ℝ) ≤ walkFirstPassage ω ⌊δ * (n : ℝ)⌋₊ by exact_mod_cast hge)
    change 1 - r ≤ |(walkFirstPassage ω ⌊δ * (n : ℝ)⌋₊ : ℝ) / (n : ℝ) - r|
    rw [abs_of_nonneg (sub_nonneg.mpr (hr.le.trans hratio))]
    linarith


/-- The probability that the first `⌊δn⌋` maximal-child slots are absent tends
to zero. -/
theorem conditioned_slots_bad_tendsto_zero (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 - (offspringMean μ).toReal) :
    Tendsto (fun n : ℕ => (conditionedPlaneTreeLaw μ n).real
      {t | ¬ ⌊δ * (n : ℝ)⌋₊ ≤ maxDegree t}) atTop (𝓝 0) := by
  have hfin : offspringMean μ ≠ ∞ := ne_top_of_lt (hμ.1.trans ENNReal.one_lt_top)
  have hmR : (offspringMean μ).toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hfin ENNReal.one_ne_top).mpr hμ.1
  let γ := 1 - (offspringMean μ).toReal
  have hγ : 0 < γ := by dsimp [γ]; linarith
  let q := (δ + γ) / 2
  have hδq : δ < q := by dsimp [q]; linarith
  have hqγ : q < γ := by dsimp [q]; linarith
  let ε := 1 - q / γ
  have hε : 0 < ε := by
    dsimp [ε]
    exact sub_pos.mpr ((div_lt_one hγ).mpr hqγ)
  have hfloor : Tendsto (fun n : ℕ => (⌊δ * (n : ℝ)⌋₊ : ℝ) / (n : ℝ))
      atTop (𝓝 δ) :=
    (tendsto_nat_floor_mul_div_atTop hδ0).comp tendsto_natCast_atTop_atTop
  have hmain := main_maxDegree_condensation_real μ hμ ε hε
  simp_rw [conditionedPlaneTreeLaw_finiteTreeEvent]
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_ hmain
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    (tendsto_order.1 hfloor).2 q hδq,
    eventually_size_admissible μ hμ.to_literal] with n hn hk hsize
  let _ : IsProbabilityMeasure (conditioned μ n) := conditioned_isProbability μ n hsize
  apply measureReal_mono _ (measure_ne_top _ _)
  rintro _ ⟨t, ht, rfl⟩
  refine ⟨t, ?_, rfl⟩
  have hlt : maxDegree t < ⌊δ * (n : ℝ)⌋₊ := Nat.lt_of_not_ge ht
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmaxN : (maxDegree t : ℝ) / (n : ℝ) < q := by
    apply lt_of_le_of_lt _ hk
    exact (div_le_div_iff_of_pos_right hnR).mpr (by exact_mod_cast hlt.le)
  have hratio : (maxDegree t : ℝ) / ((n : ℝ) * γ) < q / γ := by
    have heq : (maxDegree t : ℝ) / ((n : ℝ) * γ) =
        ((maxDegree t : ℝ) / (n : ℝ)) / γ := by field_simp
    rw [heq]
    exact (div_lt_div_iff_of_pos_right hγ).mpr hmaxN
  change ε < |(maxDegree t : ℝ) / ((n : ℝ) * γ) - 1|
  have hratio1 : (maxDegree t : ℝ) / ((n : ℝ) * γ) < 1 :=
    hratio.trans ((div_lt_one hγ).mpr hqγ)
  rw [abs_of_neg (sub_neg.mpr hratio1)]
  dsimp only [ε]
  linarith


/-- Prefix decoding agrees as soon as the prefix contains the totalized
first-passage time, including nonhitting paths. -/
theorem decodedListForest_stepWord_eq_of_le (ω : ℕ → ℕ) {k N : ℕ}
    (hN : walkFirstPassage ω k ≤ N) :
    decodedListForest k (BGW.stepWord (fun i : Fin N => ω i)) = decodedWalkForest k ω := by
  by_cases h : ∃ j, walkSum ω j = -(k : ℤ)
  · exact decodedListForest_stepWord_eq ω h hN
  · have hp0 : walkFirstPassage ω k = 0 := walkFirstPassage_of_no_hit ω k (not_exists.mp h)
    have hnone : firstHit? k (BGW.stepWord (fun i : Fin N => ω i)) = none := by
      cases hh : firstHit? k (BGW.stepWord (fun i : Fin N => ω i)) with
      | none => rfl
      | some m =>
          exfalso
          apply h
          have hp := (firstHit_eq_some_iff k (BGW.stepWord (fun i : Fin N => ω i)) m).mp hh
          refine ⟨m, ?_⟩
          rw [← prefixSum_stepWord_prefix ω (by simpa [BGW.stepWord] using hp.1)]
          exact hp.2.1
    rw [decodedListForest, hnone]
    simp [decodedWalkForest, stoppedForestWord, hp0,
      decodeForestWord, BGW.stepWord, wordDegrees]

/-- Finite-`n` total-variation estimate for Proposition 4.2. -/
theorem attachedSlotsLaw_tvDist_le_errors (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) {n k : ℕ}
    (hn : n ≠ 0) (hsize : bienaymeLaw μ (sizeEvent n) ≠ 0) :
    tvDist (attachedSlotsLaw μ n k) (forestLaw μ k) ≤
      2 * (conditionedPlaneTreeLaw μ n).real {t | ¬ k ≤ maxDegree t} +
      2 * (conditioned μ n).real (finiteTreeEvent fun t => ¬ uniqueWordMaximum t.increments) +
      tvDist
        ((MaximumSwapLaw.bridgeCountsLaw μ n).map (fun ω => cyclicResidual (stepWord ω)))
        ((Measure.pi (fun _ : Fin (n - 1) => incrementLaw μ)).map List.ofFn) +
      2 * (iidOffspringLaw μ).real {ω | ¬ walkFirstPassage ω k ≤ n - 1} := by
  let C := conditionedPlaneTreeLaw μ n
  let _ : IsProbabilityMeasure C := conditionedPlaneTreeLaw_isProbability μ hsize
  let _ : IsProbabilityMeasure (MaximumSwapLaw.bridgeCountsLaw μ n) :=
    BGW.isProbabilityMeasure_cond_pi_countBridges μ hn hsize
  let RC := C.map (fun t => cyclicResidual t.increments)
  let RB := (MaximumSwapLaw.bridgeCountsLaw μ n).map (fun ω => cyclicResidual (stepWord ω))
  let _ : IsProbabilityMeasure (incrementLaw μ) := by
    unfold incrementLaw
    infer_instance
  let W := (Measure.pi (fun _ : Fin (n - 1) => incrementLaw μ)).map List.ofFn
  let D := decodedListForest k
  let P := planeForestToTrees k
  let A0 := (C.map (fun t => (attachedForest t).take k)).map P
  let A1 := (RC.map D).map P
  let B1 := (RB.map D).map P
  let W1 := (W.map D).map P
  let I1 := ((iidOffspringLaw μ).map (decodedWalkForest k)).map P
  have hmeasd : Measurable D := measurable_of_countable _
  have hmeasp : Measurable P := measurable_of_countable _
  have hAttached : attachedSlotsLaw μ n k = A0 := by
    rw [attachedSlotsLaw_eq_map]
    change (C.map (attachedSlotsTree k)) = (C.map (fun t => (attachedForest t).take k)).map P
    rw [Measure.map_map hmeasp (measurable_of_countable _)]
    congr 1
    funext t
    exact attachedSlotsTree_eq_planeForestToTrees k t
  have hslot : tvDist A0 A1 ≤ 2 * C.real {t | ¬ k ≤ maxDegree t} := by
    calc
      tvDist A0 A1 = tvDist ((C.map (fun t => (attachedForest t).take k)).map P)
          ((C.map (fun t => D (cyclicResidual t.increments))).map P) := by
        dsimp only [A0, A1, RC, D]
        rw [Measure.map_map hmeasd (measurable_of_countable _)]
        simp only [Function.comp_def, D]
      _ ≤ tvDist (C.map (fun t => (attachedForest t).take k))
          (C.map (fun t => D (cyclicResidual t.increments))) :=
        tvDist_map_le _ _ P hmeasp
      _ ≤ 2 * C.real {t | ¬ k ≤ maxDegree t} := by
        have h := tvDist_map_le_of_eqOn C
          (fun t => (attachedForest t).take k)
          (fun t => D (cyclicResidual t.increments))
          (measurable_of_countable _) (measurable_of_countable _)
          {t | k ≤ maxDegree t} (Set.to_countable _).measurableSet (fun t ht =>
            (decodedListForest_cyclicResidual t ht).symm)
        simpa only [D, Set.compl_ofPred] using h
  have htransfer : tvDist A1 B1 ≤
      2 * (conditioned μ n).real (finiteTreeEvent fun t => ¬ uniqueWordMaximum t.increments) := by
    calc
      tvDist A1 B1 ≤ tvDist (RC.map D) (RB.map D) := tvDist_map_le _ _ P hmeasp
      _ ≤ tvDist RC RB := tvDist_map_le _ _ D hmeasd
      _ ≤ _ := conditioned_residual_tvDist_le μ hn hsize
  have hbridge : tvDist B1 W1 ≤ tvDist RB W := by
    calc
      tvDist B1 W1 ≤ tvDist (RB.map D) (W.map D) := tvDist_map_le _ _ P hmeasp
      _ ≤ tvDist RB W := tvDist_map_le _ _ D hmeasd
  have hpassBase : tvDist (W.map D) ((iidOffspringLaw μ).map (decodedWalkForest k)) ≤
      2 * (iidOffspringLaw μ).real {ω | ¬ walkFirstPassage ω k ≤ n - 1} := by
    dsimp only [W, D]
    rw [decoded_increment_word_law, finiteDecodedForestLaw_eq_iid_map]
    have hfinmeas : Measurable
        (fun ω : ℕ → ℕ => decodedListForest k (BGW.stepWord (fun i : Fin (n - 1) => ω i))) :=
      (measurable_of_countable (fun w : Fin (n - 1) → ℕ =>
        decodedListForest k (BGW.stepWord w))).comp
        (measurable_pi_iff.mpr fun i => measurable_pi_apply (i : ℕ))
    have h := tvDist_map_le_of_eqOn (iidOffspringLaw μ)
      (fun ω => decodedListForest k (BGW.stepWord (fun i : Fin (n - 1) => ω i)))
      (decodedWalkForest k) hfinmeas (measurable_decodedWalkForest k)
      {ω | walkFirstPassage ω k ≤ n - 1}
      (measurableSet_le (measurable_walkFirstPassage k) measurable_const)
      (fun ω hω => decodedListForest_stepWord_eq_of_le ω hω)
    simpa only [Set.compl_ofPred] using h
  have hpass : tvDist W1 I1 ≤
      2 * (iidOffspringLaw μ).real {ω | ¬ walkFirstPassage ω k ≤ n - 1} := by
    exact (tvDist_map_le (W.map D) ((iidOffspringLaw μ).map (decodedWalkForest k)) P hmeasp).trans hpassBase
  have hIfinal : I1 = forestLaw μ k := by
    dsimp only [I1, P]
    rw [Measure.map_map hmeasp (measurable_decodedWalkForest k)]
    change (iidOffspringLaw μ).map (iidFirstBlocks k) = forestLaw μ k
    exact iid_firstBlocks_law μ hμ.1 k
  rw [hAttached, ← hIfinal]
  have h1 := tvDist_triangle A0 A1 I1
  have h2 := tvDist_triangle A1 B1 I1
  have h3 := tvDist_triangle B1 W1 I1
  have h4 := tvDist_triangle W1 I1 I1
  rw [tvDist_self] at h4
  dsimp only [C, RB, W] at hslot htransfer hbridge ⊢
  linarith


/-- Limit form of Proposition 4.2, before filling the frozen wrapper. -/
theorem attached_forest_tvDist (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1 - (offspringMean μ).toReal) :
    Tendsto (fun n : ℕ =>
        tvDist (attachedSlotsLaw μ n ⌊δ * n⌋₊) (forestLaw μ ⌊δ * n⌋₊))
      atTop (𝓝 0) := by
  let _ : IsProbabilityMeasure (incrementLaw μ) := by
    unfold incrementLaw
    infer_instance
  have hslots := conditioned_slots_bad_tendsto_zero μ hμ hδ0 hδ1
  have hties := conditioned_nonunique_maximum_tendsto_zero μ hμ
  have hbridge := cyclicResidual_bridge_tvDist μ hμ
  have hpass := iid_walkFirstPassage_floor_gt_pred_tendsto_zero μ hμ hδ0 hδ1
  have hlim : Tendsto (fun n : ℕ =>
      2 * (conditionedPlaneTreeLaw μ n).real {t | ¬ ⌊δ * (n : ℝ)⌋₊ ≤ maxDegree t} +
      2 * (conditioned μ n).real (finiteTreeEvent fun t => ¬ uniqueWordMaximum t.increments) +
      tvDist
        ((MaximumSwapLaw.bridgeCountsLaw μ n).map (fun ω => cyclicResidual (stepWord ω)))
        ((Measure.pi (fun _ : Fin (n - 1) => incrementLaw μ)).map List.ofFn) +
      2 * (iidOffspringLaw μ).real
        {ω | ¬ walkFirstPassage ω ⌊δ * (n : ℝ)⌋₊ ≤ n - 1}) atTop (𝓝 0) := by
    simpa only [Measure.real, mul_zero, add_zero] using
      (((hslots.const_mul 2).add (hties.const_mul 2)).add hbridge).add
        (hpass.const_mul 2)
  apply squeeze_zero' (Eventually.of_forall fun _ => tvDist_nonneg) ?_ hlim
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    eventually_size_admissible μ hμ.to_literal] with n hn hsize
  exact attachedSlotsLaw_tvDist_le_errors μ hμ (Nat.ne_of_gt hn) hsize

end
end SubcriticalCauchy.Bienayme
