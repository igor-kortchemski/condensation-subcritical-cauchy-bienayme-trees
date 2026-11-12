module

public import SubcriticalCauchy.PaperRoute.Defs
public import Mathlib.MeasureTheory.Constructions.Pi

/-! Elementary measurability and permutation facts for the AL argument. -/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Topology BigOperators

namespace SubcriticalCauchy.ArmendarizLoulakis

noncomputable section

/-- The first-maximum statistic is measurable. -/
theorem al_firstMaxIndex_measurable {n : ℕ} :
    Measurable (firstMaxIndex (n := n)) := by
  classical
  apply measurable_to_countable'
  intro k
  have hset : {x : Fin (n + 1) → ℝ | firstMaxIndex x = k} =
      (⋂ j, {x : Fin (n + 1) → ℝ | x j ≤ x k}) ∩
        (⋂ j : {j : Fin (n + 1) // j < k},
          ⋃ l, {x : Fin (n + 1) → ℝ | x j.1 < x l}) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_iUnion]
    change (Finset.univ.filter fun i => ∀ j, x j ≤ x i).min' _ = k ↔ _
    rw [Finset.min'_eq_iff]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hmax, hleast⟩
      refine ⟨hmax, fun j => ?_⟩
      by_contra h
      push Not at h
      exact (not_le_of_gt j.2) (hleast j.1 h)
    · rintro ⟨hmax, hleast⟩
      refine ⟨hmax, fun j hj => ?_⟩
      by_contra hkj
      obtain ⟨l, hl⟩ := hleast ⟨j, lt_of_not_ge hkj⟩
      exact (not_lt_of_ge (hj l)) hl
  change MeasurableSet {x : Fin (n + 1) → ℝ | firstMaxIndex x = k}
  rw [hset]
  apply MeasurableSet.inter
  · exact MeasurableSet.iInter fun j =>
      measurableSet_le (measurable_pi_apply j) (measurable_pi_apply k)
  · exact MeasurableSet.iInter fun j => MeasurableSet.iUnion fun l =>
      measurableSet_lt (measurable_pi_apply j.1) (measurable_pi_apply l)

/-- AL's swap-and-drop map is measurable in every dimension, including zero. -/
theorem al_alSwapDrop_measurable (n : ℕ) : Measurable (alSwapDrop n) := by
  classical
  cases n with
  | zero =>
      apply measurable_pi_iff.mpr
      intro i
      exact i.elim0
  | succ m =>
      apply measurable_pi_iff.mpr
      intro i
      let f : Fin (m + 1) → (Fin (m + 1) → ℝ) → ℝ := fun k x =>
        x (Equiv.swap k (Fin.last m) i.castSucc)
      have hf : ∀ k, Measurable (f k) := fun k => measurable_pi_apply _
      have hfun : (fun x : Fin (m + 1) → ℝ => alSwapDrop (m + 1) x i) =
          fun x => ∑ k : Fin (m + 1), if firstMaxIndex x = k then f k x else 0 := by
        funext x
        simp [alSwapDrop, f]
      rw [hfun]
      apply Finset.measurable_fun_sum
      intro k _
      exact Measurable.ite
        (al_firstMaxIndex_measurable (measurableSet_singleton k)) (hf k) measurable_const

/-- A permutation of coordinates preserves a finite iid product measure. -/
theorem al_measurePreserving_pi_perm {n : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (e : Fin n ≃ Fin n) :
    MeasurePreserving (fun x : Fin n → ℝ => x ∘ e) (Measure.pi fun _ : Fin n => ν)
      (Measure.pi fun _ : Fin n => ν) := by
  have h := measurePreserving_piCongrLeft (fun _ : Fin n => ν) e.symm
  convert h using 1
  ext x i
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using
    (MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin n => ℝ) e.symm x (e i)).symm

/-- The coordinates left after AL's transposition of `k` with the last coordinate. -/
def alResidual {m : ℕ} (k : Fin (m + 1)) (z : Fin (m + 1) → ℝ) : Fin m → ℝ :=
  fun i => z (Equiv.swap k (Fin.last m) i.castSucc)

/-- A strict maximum at `k`, with no condition at `k` itself. -/
def alStrictMaxAt {m : ℕ} (k : Fin (m + 1)) (z : Fin (m + 1) → ℝ) : Prop :=
  ∀ j, j ≠ k → z j < z k

/-- The cell where `k` is the strict maximum, the AL residual lies in `B ∩ G`,
and the total sum belongs to `x + Δ`. -/
def alCell {m : ℕ} (k : Fin (m + 1)) (B G : Set (Fin m → ℝ)) (x : ℝ) :
    Set (Fin (m + 1) → ℝ) :=
  {z | alStrictMaxAt k z ∧ alResidual k z ∈ B ∩ G ∧
    ∑ i, z i ∈ Set.Ioc x (x + 1)}

/-- The last-coordinate cell before using the strict-maximum consequence of `G`. -/
def alEndSet (m : ℕ) (B G : Set (Fin m → ℝ)) (x : ℝ) : Set (Fin (m + 1) → ℝ) :=
  {z | alResidual (Fin.last m) z ∈ B ∩ G ∧ ∑ i, z i ∈ Set.Ioc x (x + 1)}

theorem al_residual_measurable {m : ℕ} (k : Fin (m + 1)) : Measurable (alResidual k) := by
  apply measurable_pi_iff.mpr
  intro i
  exact measurable_pi_apply _

theorem al_strictMaxAt_measurableSet {m : ℕ} (k : Fin (m + 1)) :
    MeasurableSet {z : Fin (m + 1) → ℝ | alStrictMaxAt k z} := by
  have hset : {z : Fin (m + 1) → ℝ | alStrictMaxAt k z} =
      ⋂ j : {j : Fin (m + 1) // j ≠ k}, {z : Fin (m + 1) → ℝ | z j.1 < z k} := by
    ext z
    simp [alStrictMaxAt]
  rw [hset]
  exact MeasurableSet.iInter fun j =>
    measurableSet_lt (measurable_pi_apply j.1) (measurable_pi_apply k)

theorem al_cell_measurableSet {m : ℕ} (k : Fin (m + 1))
    {B G : Set (Fin m → ℝ)} (hB : MeasurableSet B) (hG : MeasurableSet G) (x : ℝ) :
    MeasurableSet (alCell k B G x) := by
  apply MeasurableSet.inter
  · exact al_strictMaxAt_measurableSet k
  · apply MeasurableSet.inter
    · exact (hB.inter hG).preimage (al_residual_measurable k)
    · exact measurableSet_Ioc.preimage
        (Finset.measurable_fun_sum _ fun i _ => measurable_pi_apply i)

theorem al_residual_last {m : ℕ} (z : Fin (m + 1) → ℝ) :
    alResidual (Fin.last m) z = fun i => z i.castSucc := by
  funext i
  simp [alResidual]

theorem al_sum_eq_sum_residual_add {m : ℕ} (z : Fin (m + 1) → ℝ) (k : Fin (m + 1)) :
    (∑ i, z i) = (∑ i, alResidual k z i) + z k := by
  let e := Equiv.swap k (Fin.last m)
  calc
    (∑ i, z i) = ∑ i, z (e i) := (Equiv.sum_comp e z).symm
    _ = (∑ i : Fin m, z (e i.castSucc)) + z (e (Fin.last m)) :=
      Fin.sum_univ_castSucc (n := m) (fun i : Fin (m + 1) => z (e i))
    _ = _ := by simp [alResidual, e]

/-- Every AL cell has the same product-measure mass as the last-coordinate cell. -/
theorem al_cell_measure {m : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (k : Fin (m + 1)) (B G : Set (Fin m → ℝ)) (x : ℝ)
    (hB : MeasurableSet B) (hG : MeasurableSet G) :
    (Measure.pi fun _ : Fin (m + 1) => ν) (alCell k B G x) =
      (Measure.pi fun _ : Fin (m + 1) => ν) (alCell (Fin.last m) B G x) := by
  let e := Equiv.swap k (Fin.last m)
  have hr : (fun z : Fin (m + 1) → ℝ => alResidual (Fin.last m) (z ∘ e)) =
      alResidual k := by
    funext z i
    simp [alResidual, e]
  have hset : (fun z : Fin (m + 1) → ℝ => z ∘ e) ⁻¹'
      alCell (Fin.last m) B G x = alCell k B G x := by
    ext z
    change (alStrictMaxAt (Fin.last m) (z ∘ e) ∧ alResidual (Fin.last m) (z ∘ e) ∈ B ∩ G ∧
      (∑ i, (z ∘ e) i) ∈ Set.Ioc x (x + 1)) ↔
        (alStrictMaxAt k z ∧ alResidual k z ∈ B ∩ G ∧
          (∑ i, z i) ∈ Set.Ioc x (x + 1))
    rw [show alResidual (Fin.last m) (z ∘ e) = alResidual k z from congrFun hr z]
    have hsum : (∑ i, (z ∘ e) i) = ∑ i, z i := Equiv.sum_comp e z
    rw [hsum]
    constructor
    · rintro ⟨hmax, hG', hx⟩
      refine ⟨?_, hG', hx⟩
      intro j hj
      have hej : e j ≠ Fin.last m := by
        intro he
        apply hj
        calc j = e (e j) := by simp [e]
          _ = k := by simp [he, e]
      simpa [e] using hmax (e j) hej
    · rintro ⟨hmax, hG', hx⟩
      refine ⟨?_, hG', hx⟩
      intro j hj
      have hej : e j ≠ k := by
        intro he
        apply hj
        calc j = e (e j) := by simp [e]
          _ = Fin.last m := by rw [he]; simp [e]
      simpa [e] using hmax (e j) hej
  rw [← hset]
  exact (al_measurePreserving_pi_perm ν e).measure_preimage
    (al_cell_measurableSet (Fin.last m) hB hG x).nullMeasurableSet

/-- On a strict-maximum cell, `alSwapDrop` is exactly `alResidual`. -/
theorem al_alSwapDrop_eq_residual {m : ℕ} (k : Fin (m + 1))
    (z : Fin (m + 1) → ℝ) (hz : alStrictMaxAt k z) :
    alSwapDrop (m + 1) z = alResidual k z := by
  have hfirst : firstMaxIndex z = k := by
    unfold firstMaxIndex
    rw [Finset.min'_eq_iff]
    constructor
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro j
      by_cases hjk : j = k
      · simp [hjk]
      · exact (hz j hjk).le
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      by_contra hkj
      exact (not_lt_of_ge (hj k)) (hz j (lt_of_not_ge hkj).ne)
  change (fun i => z (Equiv.swap (firstMaxIndex z) (Fin.last m) i.castSucc)) =
    alResidual k z
  unfold alResidual
  rw [hfirst]


/-- Exchangeability and disjointness give AL's lower bound before evaluating the
last-coordinate cell. -/
theorem al_cells_le_map_event {m : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {B G : Set (Fin m → ℝ)} (hB : MeasurableSet B) (hG : MeasurableSet G) (x : ℝ) :
    ((m : ℝ) + 1) *
        ((Measure.pi fun _ : Fin (m + 1) => ν) (alCell (Fin.last m) B G x)).toReal ≤
      ((Measure.pi fun _ : Fin (m + 1) => ν)
        {z | alSwapDrop (m + 1) z ∈ B ∧ ∑ i, z i ∈ Set.Ioc x (x + 1)}).toReal := by
  classical
  let P : Measure (Fin (m + 1) → ℝ) := Measure.pi fun _ => ν
  let T : Set (Fin (m + 1) → ℝ) :=
    {z | alSwapDrop (m + 1) z ∈ B ∧ ∑ i, z i ∈ Set.Ioc x (x + 1)}
  have hdisj : (↑(Finset.univ : Finset (Fin (m + 1))) : Set (Fin (m + 1))).PairwiseDisjoint
      (fun k => alCell k B G x) := by
    intro k _ l _ hkl
    apply Set.disjoint_left.mpr
    intro z hzk hzl
    have h₁ := hzk.1 l hkl.symm
    have h₂ := hzl.1 k hkl
    exact (not_lt_of_ge h₂.le) h₁
  have hsub : (⋃ k ∈ Finset.univ, alCell k B G x) ⊆ T := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨k, -, hmax, hres, hx⟩ := hz
    exact ⟨by rw [al_alSwapDrop_eq_residual k z hmax]; exact hres.1, hx⟩
  have hle : (∑ k : Fin (m + 1), P (alCell k B G x)) ≤ P T := by
    rw [← MeasureTheory.measure_biUnion_finset hdisj
      (fun k _ => al_cell_measurableSet k hB hG x)]
    exact measure_mono hsub
  have heq : (∑ k : Fin (m + 1), P (alCell k B G x)) =
      (m + 1 : ℕ) * P (alCell (Fin.last m) B G x) := by
    calc
      _ = ∑ _k : Fin (m + 1), P (alCell (Fin.last m) B G x) := by
        apply Finset.sum_congr rfl
        intro k _
        exact al_cell_measure ν k B G x hB hG
      _ = _ := by simp
  have hreal := ENNReal.toReal_mono (measure_ne_top P T) hle
  rw [heq] at hreal
  dsimp [P, T] at hreal
  norm_num [ENNReal.toReal_add] at hreal
  simpa only [Set.mem_Ioc] using hreal


end
end SubcriticalCauchy.ArmendarizLoulakis
