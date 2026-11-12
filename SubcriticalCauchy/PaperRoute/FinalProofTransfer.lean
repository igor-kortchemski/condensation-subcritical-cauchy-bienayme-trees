module

public import SubcriticalCauchy.PaperRoute.Defs
public import SubcriticalCauchy.MaximumSwapLaw
public import SubcriticalCauchy.LatticeWindow
public import SubcriticalCauchy.TotalVariationTypical
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Data.List.GetD
public import Mathlib.Probability.ConditionalProbability

/-!
# Exact measure-transfer lemmas for the paper route

These lemmas are finite and non-asymptotic.  In particular, conditioning and
extended total variation are both compatible with a measurable embedding.
-/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section

/-- A measurable map out of a countable space with a measurable global left
inverse is a measurable embedding. -/
theorem final_measurableEmbedding_of_countable_leftInverse
    {α β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β] {f : α → β}
    (hf : Measurable f) {g : β → α} (hg : Measurable g)
    (hleft : Function.LeftInverse g f) : MeasurableEmbedding f :=
  MeasurableEmbedding.of_measurable_inverse hf (Set.countable_range f).measurableSet hg hleft

/-- Extended total variation is exactly preserved by a measurable embedding. -/
theorem final_etvDist_map_of_measurableEmbedding
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (P Q : Measure α) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (f : α → β) (hf : MeasurableEmbedding f) :
    etvDist (P.map f) (Q.map f) = etvDist P Q := by
  let V := P.toSignedMeasure - Q.toSignedMeasure
  have hmap : (P.map f).toSignedMeasure - (Q.map f).toSignedMeasure = V.map f := by
    ext s hs
    simp only [Measure.toSignedMeasure_sub_apply hs, VectorMeasure.map_apply _ hf.measurable hs,
      Measure.map_apply hf.measurable hs, Measure.real, V,
      Measure.toSignedMeasure_sub_apply (hf.measurable hs)]
  rw [etvDist_eq_etvDist_toSignedMeasure, etvDist_eq_etvDist_toSignedMeasure]
  change ((P.map f).toSignedMeasure - (Q.map f).toSignedMeasure).variation Set.univ =
    V.variation Set.univ
  rw [hmap, hf.variation_map]
  simp [Measure.map_apply hf.measurable]

/-- Total variation is exactly preserved by a measurable embedding. -/
theorem final_tvDist_map_of_measurableEmbedding
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (P Q : Measure α) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (f : α → β) (hf : MeasurableEmbedding f) :
    tvDist (P.map f) (Q.map f) = tvDist P Q := by
  rw [tvDist, tvDist, final_etvDist_map_of_measurableEmbedding P Q f hf]

/-- Conditioning commutes with pushforward by a measurable embedding. -/
theorem final_map_cond {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (f : α → β) (hf : MeasurableEmbedding f) (s : Set β) :
    (μ.map f)[|s] = (μ[|f ⁻¹' s]).map f := by
  unfold ProbabilityTheory.cond
  rw [hf.restrict_map, Measure.map_smul _ hf.measurable.aemeasurable, hf.map_apply]

/-- The common translation of integer increments by a real constant. -/
def finalRealShift {n : ℕ} (γ : ℝ) (z : Fin n → ℤ) : Fin n → ℝ :=
  fun i => (z i : ℝ) + γ

/-- The real-centered increments associated with a vector of offspring counts. -/
def finalCountShift {n : ℕ} (γ : ℝ) (ω : Fin n → ℕ) : Fin n → ℝ :=
  fun i => (ω i : ℝ) - 1 + γ

theorem finalRealShift_measurable {n : ℕ} (γ : ℝ) : Measurable (finalRealShift (n := n) γ) := by
  fun_prop

theorem finalCountShift_measurable {n : ℕ} (γ : ℝ) : Measurable (finalCountShift (n := n) γ) := by
  fun_prop

theorem finalRealShift_leftInverse {n : ℕ} (γ : ℝ) :
    Function.LeftInverse (fun y : Fin n → ℝ => fun i => ⌊y i - γ⌋)
      (finalRealShift (n := n) γ) := by
  intro z
  funext i
  simp [finalRealShift]

theorem finalCountShift_leftInverse {n : ℕ} (γ : ℝ) :
    Function.LeftInverse (fun y : Fin n → ℝ => fun i => ⌊y i + 1 - γ⌋₊)
      (finalCountShift (n := n) γ) := by
  intro ω
  funext i
  have h : (ω i : ℝ) - 1 + γ + 1 - γ = (ω i : ℝ) := by ring
  simp [finalCountShift, h]

theorem finalRealShift_measurableEmbedding {n : ℕ} (γ : ℝ) :
    MeasurableEmbedding (finalRealShift (n := n) γ) :=
  final_measurableEmbedding_of_countable_leftInverse (finalRealShift_measurable γ)
    (by fun_prop) (finalRealShift_leftInverse γ)

theorem finalCountShift_measurableEmbedding {n : ℕ} (γ : ℝ) :
    MeasurableEmbedding (finalCountShift (n := n) γ) :=
  final_measurableEmbedding_of_countable_leftInverse (finalCountShift_measurable γ)
    (by fun_prop) (finalCountShift_leftInverse γ)

/-- Centering is the direct pushforward of the offspring law. -/
theorem final_centeredIncrementLaw_eq_map (μ : Measure ℕ) :
    centeredIncrementLaw μ = μ.map (fun k : ℕ => (k : ℝ) - 1 + (1 - (offspringMean μ).toReal)) := by
  rw [centeredIncrementLaw, incrementLaw, Measure.map_map]
  · apply Measure.map_congr
    filter_upwards [] with k
    simp only [Function.comp_apply]
    push_cast
    ring
  · fun_prop
  · exact measurable_of_countable _

/-- The centered iid law is the pushforward of the iid offspring law. -/
theorem final_pi_centeredIncrementLaw (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) :
    (Measure.pi fun _ : Fin n => centeredIncrementLaw μ) =
      (Measure.pi fun _ : Fin n => μ).map
        (finalCountShift (n := n) (1 - (offspringMean μ).toReal)) := by
  change (Measure.pi fun _ : Fin n => centeredIncrementLaw μ) =
    (Measure.pi fun _ : Fin n => μ).map
      (fun x i => (x i : ℝ) - 1 + (1 - (offspringMean μ).toReal))
  symm
  calc
    (Measure.pi fun _ : Fin n => μ).map
        (fun x i => (x i : ℝ) - 1 + (1 - (offspringMean μ).toReal)) =
        (Measure.pi fun _ : Fin n => μ.map
          (fun k : ℕ => (k : ℝ) - 1 + (1 - (offspringMean μ).toReal))) :=
      Measure.pi_map_pi (X := fun _ : Fin n => ℕ) (Y := fun _ : Fin n => ℝ)
        (μ := fun _ : Fin n => μ) (f := fun (_ : Fin n) (k : ℕ) => (k : ℝ) - 1 + (1 - (offspringMean μ).toReal))
        (fun _ => (measurable_of_countable _).aemeasurable)
    _ = _ := by
      congr 1
      funext i
      exact (final_centeredIncrementLaw_eq_map μ).symm


/-- The finite centered walk is the offspring walk plus `γn`. -/
theorem final_sum_countShift {n : ℕ} (γ : ℝ) (ω : Fin n → ℕ) :
    (∑ i, finalCountShift γ ω i) = (finiteWalkSum ω : ℝ) + γ * n := by
  simp only [finalCountShift, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [show (∑ i, (ω i : ℝ)) = ((∑ i, ω i : ℕ) : ℝ) by push_cast; rfl]
  have hw : (finiteWalkSum ω : ℝ) = ((∑ i, ω i : ℕ) : ℝ) - n := by
    simp only [finiteWalkSum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  rw [hw]
  ring

/-- The corrected centered window is exactly the actual count-bridge event. -/
theorem final_countShift_window {n : ℕ} (γ : ℝ) :
    (finalCountShift (n := n) γ) ⁻¹'
        {y : Fin n → ℝ | ∑ i, y i ∈ Set.Ioc (γ * n - 2) (γ * n - 1)} =
      BGW.countBridges n := by
  ext ω
  change (∑ i, finalCountShift γ ω i) ∈ Set.Ioc (γ * n - 2) (γ * n - 1) ↔ _
  rw [final_sum_countShift]
  have hwin : ((finiteWalkSum ω : ℝ) + γ * n ∈
      Set.Ioc (γ * n - 2) (γ * n - 1)) ↔ finiteWalkSum ω = -1 :=
    Set.ext_iff.mp (finiteWalk_centered_window (n := n) γ) ω
  rw [hwin]
  change finiteWalkSum ω = -1 ↔ (∑ i, ω i) + 1 = n
  have hw : finiteWalkSum ω = (∑ i, ((ω i : ℤ) - 1)) := rfl
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hw
  have hcast : ((∑ i, ω i : ℕ) : ℤ) = ∑ i, (ω i : ℤ) := by push_cast; rfl
  omega

/-- Conditioning the centered iid law on the corrected window is precisely the
pushforward of the actual conditioned offspring-count law. -/
theorem final_conditioned_centered_eq (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (n : ℕ) :
    ((Measure.pi fun _ : Fin n => centeredIncrementLaw μ)[|
      {y : Fin n → ℝ | ∑ i, y i ∈ Set.Ioc
        ((1 - (offspringMean μ).toReal) * n - 2)
        ((1 - (offspringMean μ).toReal) * n - 1)}]) =
      (MaximumSwapLaw.bridgeCountsLaw μ n).map
        (finalCountShift (n := n) (1 - (offspringMean μ).toReal)) := by
  rw [final_pi_centeredIncrementLaw]
  rw [final_map_cond _ _ (finalCountShift_measurableEmbedding _) _]
  rw [final_countShift_window]
  rfl

/-- Centering is pushforward of the integer increment law by `finalRealShift`
in one coordinate. -/
theorem final_centeredIncrementLaw_eq_realShift (μ : Measure ℕ) :
    centeredIncrementLaw μ = (incrementLaw μ).map
      (fun z : ℤ => (z : ℝ) + (1 - (offspringMean μ).toReal)) := by
  rfl

/-- The centered iid law is the common affine pushforward of the integer iid
increment law. -/
theorem final_pi_realShift_incrementLaw (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) :
    ((Measure.pi fun _ : Fin n => incrementLaw μ).map
      (finalRealShift (n := n) (1 - (offspringMean μ).toReal))) =
      Measure.pi fun _ : Fin n => centeredIncrementLaw μ := by
  rw [final_pi_centeredIncrementLaw]
  have hpi : (Measure.pi fun _ : Fin n => incrementLaw μ) =
      (Measure.pi fun _ : Fin n => μ).map
        (fun z i => (z i : ℤ) - 1) := by
    symm
    exact Measure.pi_map_pi (X := fun _ : Fin n => ℕ) (Y := fun _ : Fin n => ℤ)
      (μ := fun _ : Fin n => μ)
      (f := fun (_ : Fin n) (k : ℕ) => (k : ℤ) - 1)
      (fun _ => (measurable_of_countable _).aemeasurable)
  rw [hpi, Measure.map_map (finalRealShift_measurable _) (measurable_of_countable _)]
  apply Measure.map_congr
  filter_upwards [] with z
  funext i
  simp only [Function.comp_apply, finalCountShift, finalRealShift]
  push_cast
  ring


open ArmendarizLoulakis MaximumSwapBridge

/-- The selected first-maximum coordinate is maximal. -/
theorem final_firstMaxIndex_isMax {m : ℕ} (x : Fin (m + 1) → ℝ) (j : Fin (m + 1)) :
    x j ≤ x (firstMaxIndex x) := by
  have hmem := Finset.min'_mem (Finset.univ.filter fun i => ∀ j, x j ≤ x i)
    (show (Finset.univ.filter fun i => ∀ j, x j ≤ x i).Nonempty by
      obtain ⟨i, -, hi⟩ := Finset.univ.exists_max_image x Finset.univ_nonempty
      exact ⟨i, by simpa using hi⟩)
  exact (Finset.mem_filter.mp hmem).2 j

/-- The selected maximal coordinate is no later than any other maximal one. -/
theorem final_firstMaxIndex_le {m : ℕ} (x : Fin (m + 1) → ℝ) {i : Fin (m + 1)}
    (hi : ∀ j, x j ≤ x i) : firstMaxIndex x ≤ i := by
  apply Finset.min'_le
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩

/-- Every entry of a count list is bounded by its list maximum. -/
theorem final_le_listMaxDegree {ds : List ℕ} {d : ℕ} (hd : d ∈ ds) : d ≤ listMaxDegree ds := by
  exact Finset.le_sup (f := id) (List.mem_toFinset.mpr hd)

/-- The common affine shift is strictly monotone on count coordinates. -/
theorem finalCountShift_le_iff {n : ℕ} (γ : ℝ) (ω : Fin n → ℕ) (i j : Fin n) :
    finalCountShift γ ω i ≤ finalCountShift γ ω j ↔ ω i ≤ ω j := by
  constructor
  · intro h
    have h' := (add_le_add_iff_right γ).mp h
    have h'' := (sub_le_sub_iff_right (1 : ℝ)).mp h'
    exact_mod_cast h''
  · intro h
    have h' : (ω i : ℝ) ≤ (ω j : ℝ) := by exact_mod_cast h
    dsimp [finalCountShift]
    linarith

/-- Counts remaining after the first maximum is swapped to the end and dropped. -/
def finalSwapTakeCounts (n : ℕ) (ω : Fin n → ℕ) : List ℕ :=
  (swapFirstMaxToLast (List.ofFn ω)).take (n - 1)

/-- The increment vector of a list, with the harmless out-of-range default `-1`. -/
def finalListIncrements (n : ℕ) (ds : List ℕ) : Fin (n - 1) → ℤ :=
  fun i => (ds.map (fun d : ℕ => (d : ℤ) - 1)).getD i (-1)

/-- At the actual coordinates, the auxiliary list vector agrees with the frozen
`deletedIncrements` definition. -/
theorem finalListIncrements_delete {n : ℕ} (hn : n ≠ 0) (ω : Fin n → ℕ) :
    finalListIncrements n (deleteMaxCounts (List.ofFn ω)) = deletedIncrements n ω := by
  have hne : List.ofFn ω ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    simp only [List.length_ofFn, List.length_nil] at hlen
    exact hn hlen
  have hlen := length_deletedMaximumWord (ds := List.ofFn ω) hne
  simp only [List.length_ofFn] at hlen
  funext i
  change (deletedMaximumWord (List.ofFn ω)).getD i (-1) =
    (deletedMaximumWord (List.ofFn ω)).getD i 0
  rw [List.getD_eq_getElem _ _ (by omega : i.val < (deletedMaximumWord (List.ofFn ω)).length),
    List.getD_eq_getElem _ _ (by omega : i.val < (deletedMaximumWord (List.ofFn ω)).length)]

/-- The affine real pushforward of swap-and-drop has exactly the same law as the
affine real pushforward of ordered first-maximum deletion. -/
theorem final_map_swapTake_realShift_delete
    (μ : Measure ℕ) [IsProbabilityMeasure μ] {n : ℕ} (hn : n ≠ 0) (γ : ℝ) :
    ((MaximumSwapLaw.bridgeCountsLaw μ n).map
      (fun ω => finalRealShift γ (finalListIncrements n (finalSwapTakeCounts n ω)))) =
      (MaximumSwapLaw.bridgeCountsLaw μ n).map
        (fun ω => finalRealShift γ (deletedIncrements n ω)) := by
  let finalListNatMeasurableSpace : MeasurableSpace (List ℕ) := ⊤
  have hcount : (MaximumSwapLaw.bridgeCountsLaw μ n).map (finalSwapTakeCounts n) =
      (MaximumSwapLaw.bridgeCountsLaw μ n).map
        (fun ω => deleteMaxCounts (List.ofFn ω)) :=
    MaximumSwapLaw.map_swap_take_eq_map_delete μ hn
  have hlist := congrArg (fun ρ : Measure (List ℕ) => ρ.map (finalListIncrements n)) hcount
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)] at hlist
  have hreal := congrArg (fun ρ : Measure (Fin (n - 1) → ℤ) => ρ.map (finalRealShift γ)) hlist
  rw [Measure.map_map (finalRealShift_measurable γ) (measurable_of_countable _),
    Measure.map_map (finalRealShift_measurable γ) (measurable_of_countable _)] at hreal
  simp only [Function.comp_def] at hreal
  have hfun : (fun ω => finalRealShift γ
      (finalListIncrements n (deleteMaxCounts (List.ofFn ω)))) =
      (fun ω => finalRealShift γ (deletedIncrements n ω)) := by
    funext ω
    rw [finalListIncrements_delete hn]
  rw [hfun] at hreal
  simpa only [Function.comp_def, finalSwapTakeCounts] using hreal


/-- Reading an in-range entry of `List.ofFn` with `getD`. -/
theorem final_ofFn_getD {n : ℕ} (ω : Fin n → ℕ) (i : Fin n) :
    (List.ofFn ω).getD i.val 0 = ω i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

/-- In a first-maximum decomposition, AL's selected index is exactly the length
of the prefix before the first maximum. -/
theorem final_firstMaxIndex_eq_pre {m : ℕ} (γ : ℝ) (ω : Fin (m + 1) → ℕ)
    (pre post : List ℕ) (hpre : listMaxDegree (List.ofFn ω) ∉ pre)
    (hds : List.ofFn ω = pre ++ listMaxDegree (List.ofFn ω) :: post) :
    (firstMaxIndex (finalCountShift γ ω)).val = pre.length := by
  have hlen := congrArg List.length hds
  simp only [List.length_ofFn, List.length_append, List.length_cons] at hlen
  let k : Fin (m + 1) := ⟨pre.length, by omega⟩
  have hk0 : ω k = listMaxDegree (List.ofFn ω) := by
    rw [← final_ofFn_getD ω k]
    change (List.ofFn ω).getD pre.length 0 = listMaxDegree (List.ofFn ω)
    calc
      (List.ofFn ω).getD pre.length 0 =
          (pre ++ listMaxDegree (List.ofFn ω) :: post).getD pre.length 0 :=
        congrArg (fun ds : List ℕ => ds.getD pre.length 0) hds
      _ = listMaxDegree (List.ofFn ω) := by
        rw [List.getD_append_right _ _ _ _ (Nat.le_refl _)]
        simp only [Nat.sub_self, List.getD_cons_zero]
  have hkmax : ∀ i, finalCountShift γ ω i ≤ finalCountShift γ ω k := by
    intro i
    rw [finalCountShift_le_iff, hk0]
    exact final_le_listMaxDegree (List.mem_ofFn.mpr ⟨i, rfl⟩)
  have hle : (firstMaxIndex (finalCountShift γ ω)).val ≤ pre.length :=
    final_firstMaxIndex_le (finalCountShift γ ω) hkmax
  apply Nat.le_antisymm hle
  by_contra hnot
  have hj : (firstMaxIndex (finalCountShift γ ω)).val < pre.length := by omega
  let j := firstMaxIndex (finalCountShift γ ω)
  have hjmax : ω j = listMaxDegree (List.ofFn ω) := by
    apply Nat.le_antisymm
      (final_le_listMaxDegree (List.mem_ofFn.mpr ⟨j, rfl⟩))
    have h := (finalCountShift_le_iff γ ω k j).mp
      (final_firstMaxIndex_isMax (finalCountShift γ ω) k)
    rwa [hk0] at h
  have hjmem : ω j ∈ pre := by
    have hjval : ω j = pre.getD j.val 0 := by
      rw [← final_ofFn_getD ω j, hds, List.getD_append _ _ _ _ hj]
    rw [hjval, List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem _
  exact hpre (hjmax ▸ hjmem)


/-- **B4, pointwise coordinate identity.** AL's swap-and-drop commutes with the
common affine shift of the offspring counts. -/
theorem final_alSwapDrop_countShift {m : ℕ} (γ : ℝ) (ω : Fin (m + 1) → ℕ) :
    alSwapDrop (m + 1) (finalCountShift γ ω) =
      finalRealShift γ (finalListIncrements (m + 1) (finalSwapTakeCounts (m + 1) ω)) := by
  have hne : List.ofFn ω ≠ [] := by simp
  obtain ⟨pre, post, hpre, hds, -⟩ := deleteMaxCounts_first hne
  have hj := final_firstMaxIndex_eq_pre γ ω pre post hpre hds
  have hlen := congrArg List.length hds
  simp only [List.length_ofFn, List.length_append, List.length_cons] at hlen
  rcases post.eq_nil_or_concat' with hp | ⟨mid, z, hp⟩
  · subst post
    have hm : m = pre.length := by
      simp only [List.length_nil] at hlen
      omega
    have hjlast : firstMaxIndex (finalCountShift γ ω) = Fin.last m := by
      apply Fin.ext
      change (firstMaxIndex (finalCountShift γ ω)).val = m
      exact hj.trans hm.symm
    have hswap : swapFirstMaxToLast (List.ofFn ω) =
        pre ++ [listMaxDegree (List.ofFn ω)] := by
      unfold swapFirstMaxToLast
      calc
        swapFirstLast (listMaxDegree (List.ofFn ω)) (List.ofFn ω) =
            swapFirstLast (listMaxDegree (List.ofFn ω))
              (pre ++ [listMaxDegree (List.ofFn ω)]) := by
          simpa only [List.append_nil] using
            congrArg (swapFirstLast (listMaxDegree (List.ofFn ω))) hds
        _ = pre ++ [listMaxDegree (List.ofFn ω)] := by
          rw [swapFirstLast_append [] hpre]
          rfl
    have ht : finalSwapTakeCounts (m + 1) ω = pre := by
      unfold finalSwapTakeCounts
      rw [hswap]
      simp only [Nat.add_sub_cancel, hm]
      exact List.take_left
    funext i
    change finalCountShift γ ω
      (Equiv.swap (firstMaxIndex (finalCountShift γ ω)) (Fin.last m) i.castSucc) =
        ((finalListIncrements (m + 1) (finalSwapTakeCounts (m + 1) ω) i : ℤ) : ℝ) + γ
    rw [finalListIncrements]
    have hmap : ((finalSwapTakeCounts (m + 1) ω).map
        (fun d : ℕ => (d : ℤ) - 1)).getD i.val (-1) =
        (((finalSwapTakeCounts (m + 1) ω).getD i.val 0 : ℕ) : ℤ) - 1 := by
      simpa using List.getD_map (finalSwapTakeCounts (m + 1) ω) 0
        (n := i.val) (fun d : ℕ => (d : ℤ) - 1)
    rw [hmap]
    have hc : (finalSwapTakeCounts (m + 1) ω).getD i.val 0 =
        ω (Equiv.swap (firstMaxIndex (finalCountShift γ ω)) (Fin.last m) i.castSucc) := by
      rw [ht, hjlast]
      simp only [Equiv.swap_self, Equiv.refl_apply]
      rw [← final_ofFn_getD ω i.castSucc, hds]
      change pre.getD i.val 0 = (pre ++ [listMaxDegree (List.ofFn ω)]).getD i.val 0
      rw [List.getD_append _ _ _ _ (by omega : i.val < pre.length)]
    rw [hc]
    push_cast
    rfl
  · subst post
    have hm : m = pre.length + mid.length + 1 := by
      simp only [List.length_append, List.length_singleton] at hlen
      omega
    have hswap : swapFirstMaxToLast (List.ofFn ω) =
        (pre ++ z :: mid) ++ [listMaxDegree (List.ofFn ω)] := by
      unfold swapFirstMaxToLast
      calc
        swapFirstLast (listMaxDegree (List.ofFn ω)) (List.ofFn ω) =
            swapFirstLast (listMaxDegree (List.ofFn ω))
              (pre ++ listMaxDegree (List.ofFn ω) :: (mid ++ [z])) :=
          congrArg (swapFirstLast (listMaxDegree (List.ofFn ω))) hds
        _ = (pre ++ z :: mid) ++ [listMaxDegree (List.ofFn ω)] := by
          rw [swapFirstLast_append (mid ++ [z]) hpre, swapHeadLast_append]
          exact (List.append_assoc pre (z :: mid) [listMaxDegree (List.ofFn ω)]).symm
    have ht : finalSwapTakeCounts (m + 1) ω = pre ++ z :: mid := by
      unfold finalSwapTakeCounts
      rw [hswap, Nat.add_sub_cancel]
      have hprelen : (pre ++ z :: mid).length = m := by
        simp only [List.length_append, List.length_cons]
        omega
      have htake := List.take_left (l₁ := pre ++ z :: mid)
        (l₂ := [listMaxDegree (List.ofFn ω)])
      rw [hprelen] at htake
      exact htake
    funext i
    change finalCountShift γ ω
      (Equiv.swap (firstMaxIndex (finalCountShift γ ω)) (Fin.last m) i.castSucc) =
        ((finalListIncrements (m + 1) (finalSwapTakeCounts (m + 1) ω) i : ℤ) : ℝ) + γ
    rw [finalListIncrements]
    have hmap : ((finalSwapTakeCounts (m + 1) ω).map
        (fun d : ℕ => (d : ℤ) - 1)).getD i.val (-1) =
        (((finalSwapTakeCounts (m + 1) ω).getD i.val 0 : ℕ) : ℤ) - 1 := by
      simpa using List.getD_map (finalSwapTakeCounts (m + 1) ω) 0
        (n := i.val) (fun d : ℕ => (d : ℤ) - 1)
    rw [hmap]
    have hc : (finalSwapTakeCounts (m + 1) ω).getD i.val 0 =
        ω (Equiv.swap (firstMaxIndex (finalCountShift γ ω)) (Fin.last m) i.castSucc) := by
      rw [ht]
      by_cases hi : i.val < pre.length
      · have hne1 : i.castSucc ≠ firstMaxIndex (finalCountShift γ ω) := by
          intro h
          have hv := congrArg Fin.val h
          simp only [Fin.val_castSucc, hj] at hv
          omega
        have hne2 : i.castSucc ≠ Fin.last m := by
          intro h
          have hv := congrArg Fin.val h
          simp only [Fin.val_castSucc, Fin.val_last] at hv
          omega
        rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2, ← final_ofFn_getD ω i.castSucc, hds]
        simp only [Fin.val_castSucc]
        rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ hi]
      · by_cases hieq : i.val = pre.length
        · have hidx : i.castSucc = firstMaxIndex (finalCountShift γ ω) := by
            apply Fin.ext
            simp [hj, hieq]
          rw [hidx, Equiv.swap_apply_left]
          rw [List.getD_append_right _ _ _ _ (by omega : pre.length ≤ i.val)]
          simp only [hieq, Nat.sub_self, List.getD_cons_zero]
          rw [← final_ofFn_getD ω (Fin.last m)]
          have hds' : List.ofFn ω =
              (pre ++ listMaxDegree (List.ofFn ω) :: mid) ++ [z] := by
            exact hds.trans
              (List.append_assoc pre (listMaxDegree (List.ofFn ω) :: mid) [z]).symm
          rw [hds']
          have hplen : (pre ++ listMaxDegree (List.ofFn ω) :: mid).length = m := by
            simp only [List.length_append, List.length_cons]
            omega
          rw [List.getD_append_right _ _ _ _ (by
            simp only [hplen, Fin.val_last, le_refl] :
            (pre ++ listMaxDegree (List.ofFn ω) :: mid).length ≤ (Fin.last m).val)]
          simp only [Fin.val_last, hplen, Nat.sub_self, List.getD_cons_zero]
        · have hgt : pre.length < i.val := by omega
          have hne1 : i.castSucc ≠ firstMaxIndex (finalCountShift γ ω) := by
            intro h
            have hv := congrArg Fin.val h
            simp only [Fin.val_castSucc, hj] at hv
            omega
          have hne2 : i.castSucc ≠ Fin.last m := by
            intro h
            have hv := congrArg Fin.val h
            simp only [Fin.val_castSucc, Fin.val_last] at hv
            omega
          rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2, ← final_ofFn_getD ω i.castSucc, hds]
          simp only [Fin.val_castSucc]
          rw [List.getD_append_right _ _ _ _ (by omega : pre.length ≤ i.val),
            List.getD_append_right _ _ _ _ (by omega : pre.length ≤ i.val)]
          have hidx : i.val - pre.length = (i.val - pre.length - 1) + 1 := by omega
          rw [hidx, List.getD_cons_succ, List.getD_cons_succ]
          exact (List.getD_append mid [z] 0 (i.val - pre.length - 1) (by omega)).symm
    rw [hc]
    push_cast
    rfl


/-- **B4.** AL's conditioned centered output has exactly the same total
variation from the centered iid law as ordered deletion has from the integer
iid law. -/
theorem final_al_deleted_tvDist (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : n ≠ 0) :
    tvDist (((Measure.pi fun _ : Fin n => centeredIncrementLaw μ)[|
        {y : Fin n → ℝ | ∑ i, y i ∈ Set.Ioc
          ((1 - (offspringMean μ).toReal) * n - 2)
          ((1 - (offspringMean μ).toReal) * n - 1)}]).map (alSwapDrop n))
        (Measure.pi fun _ : Fin (n - 1) => centeredIncrementLaw μ) =
      tvDist ((MaximumSwapLaw.bridgeCountsLaw μ n).map (deletedIncrements n))
        (Measure.pi fun _ : Fin (n - 1) => incrementLaw μ) := by
  cases n with
  | zero => exact (hn rfl).elim
  | succ m =>
    let γ := (1 - (offspringMean μ).toReal)
    rw [final_conditioned_centered_eq]
    have hal : AEMeasurable (alSwapDrop (m + 1))
        ((MaximumSwapLaw.bridgeCountsLaw μ (m + 1)).map (finalCountShift γ)) := by
      apply (finalCountShift_measurableEmbedding γ).aemeasurable_map_iff.mpr
      exact (measurable_of_countable _).aemeasurable
    have hcomp := hal.map_map_of_aemeasurable (finalCountShift_measurable γ).aemeasurable
    have hfun : (alSwapDrop (m + 1) ∘ finalCountShift γ) =
        (fun ω => finalRealShift γ
          (finalListIncrements (m + 1) (finalSwapTakeCounts (m + 1) ω))) := by
      funext ω
      exact final_alSwapDrop_countShift γ ω
    rw [hfun] at hcomp
    have hlaws := hcomp.trans (final_map_swapTake_realShift_delete μ (Nat.succ_ne_zero m) γ)
    rw [hlaws, ← final_pi_realShift_incrementLaw]
    let finalIncrementProbability : IsProbabilityMeasure (incrementLaw μ) := by
      unfold incrementLaw
      infer_instance
    let finalBridgeZero : IsZeroOrProbabilityMeasure
        (MaximumSwapLaw.bridgeCountsLaw μ (m + 1)) := by
      unfold MaximumSwapLaw.bridgeCountsLaw
      infer_instance
    have hdel : (MaximumSwapLaw.bridgeCountsLaw μ (m + 1)).map
        (fun ω => finalRealShift γ (deletedIncrements (m + 1) ω)) =
        ((MaximumSwapLaw.bridgeCountsLaw μ (m + 1)).map
          (deletedIncrements (m + 1))).map (finalRealShift γ) := by
      simpa only [Function.comp_def] using
        (Measure.map_map (finalRealShift_measurable γ) (measurable_of_countable _)).symm
    rw [hdel]
    dsimp only [γ]
    exact (final_tvDist_map_of_measurableEmbedding
      ((MaximumSwapLaw.bridgeCountsLaw μ (m + 1)).map (deletedIncrements (m + 1)))
      (Measure.pi fun _ : Fin m => incrementLaw μ)
      (finalRealShift (1 - (offspringMean μ).toReal))
      (finalRealShift_measurableEmbedding (1 - (offspringMean μ).toReal)))

end
end SubcriticalCauchy.Bienayme
