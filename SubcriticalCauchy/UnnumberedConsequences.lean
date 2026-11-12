module

public import SubcriticalCauchy.MainTheorems
public import SubcriticalCauchy.UnnumberedConsequencesAux

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Consequences of the main theorems and the stable limit

This module covers the unnumbered claims U1.1, U2.8 and U2.10 in the source
inventory. The stable law cited in U2.8 is exactly the frozen, proved
`paper_stable_limit`: the Laplace characterization is `IsCauchyOneLaw`, with
existence given by `exists_cauchyOneLaw`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section

/-- U1.1: with probability tending to one, the first maximal vertex has degree
at least `ε * n` and every other vertex has degree at most `ε * n`. -/
theorem unnumbered_unique_macroscopic_degree
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) {ε : ℝ}
    (hε : 0 < ε) (hεm : ε < 1 - (offspringMean μ).toReal) :
    Tendsto (fun n : ℕ => (conditioned μ n (finiteTreeEvent fun t =>
      ε * (n : ℝ) ≤ (maxDegree t : ℝ) ∧
        ∀ v : List ℕ, t.IsVertex v → v ≠ maxDegreeVertex t →
          (degreeAt t v : ℝ) ≤ ε * (n : ℝ))).toReal) atTop (𝓝 1) := by
  let gam : ℝ := 1 - (offspringMean μ).toReal
  let del : ℝ := 1 - ε / gam
  let G : ℕ → BGW.PlaneTree → Prop := fun n t =>
    ε * (n : ℝ) ≤ (maxDegree t : ℝ) ∧
      ∀ v : List ℕ, t.IsVertex v → v ≠ maxDegreeVertex t →
        (degreeAt t v : ℝ) ≤ ε * (n : ℝ)
  let B1 : ℕ → Set BGW.LocallyFinite.Tree := fun n => finiteTreeEvent fun t =>
    del < |(maxDegree t : ℝ) / ((n : ℝ) * gam) - 1|
  let B2 : ℕ → Set BGW.LocallyFinite.Tree := fun n => finiteTreeEvent fun t =>
    ε < (secondMaxDegree t : ℝ) / n
  have hgam : 0 < gam := by simpa [gam] using hεm.trans' hε
  have hdel : 0 < del := by
    dsimp [del]
    have : ε / gam < 1 := (div_lt_one hgam).mpr (by simpa [gam] using hεm)
    linarith
  have hB1 : Tendsto (fun n : ℕ => (conditioned μ n (B1 n)).toReal) atTop (𝓝 0) := by
    simpa only [B1, del, gam] using main_maxDegree_condensation_real μ hμ del hdel
  have hB2 : Tendsto (fun n : ℕ => (conditioned μ n (B2 n)).toReal) atTop (𝓝 0) := by
    simpa only [B2] using main_secondMaxDegree_negligible_real μ hμ ε hε
  have hsubset : ∀ᶠ n in atTop,
      finiteTreeEvent (fun t => ¬ G n t) ⊆ B1 n ∪ B2 n := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    intro x hx
    rcases hx with ⟨t, ht, rfl⟩
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    by_cases hmax : ε * (n : ℝ) ≤ (maxDegree t : ℝ)
    · by_cases hother : ∀ v : List ℕ, t.IsVertex v → v ≠ maxDegreeVertex t →
          (degreeAt t v : ℝ) ≤ ε * (n : ℝ)
      · exact (ht ⟨hmax, hother⟩).elim
      · push Not at hother
        obtain ⟨v, hv, hne, hvdeg⟩ := hother
        apply Set.mem_union_right
        refine ⟨t, ?_, rfl⟩
        change ε < (secondMaxDegree t : ℝ) / (n : ℝ)
        apply (lt_div_iff₀ hnR).mpr
        exact hvdeg.trans_le (Nat.cast_le.mpr
          (uconseq_degreeAt_le_secondMaxDegree_of_ne hv hne))
    · apply Set.mem_union_left
      refine ⟨t, ?_, rfl⟩
      have hmaxlt : (maxDegree t : ℝ) < ε * (n : ℝ) := lt_of_not_ge hmax
      have hratio : (maxDegree t : ℝ) / ((n : ℝ) * gam) < ε / gam := by
        apply (div_lt_div_iff₀ (mul_pos hnR hgam) hgam).mpr
        nlinarith [mul_lt_mul_of_pos_right hmaxlt hgam]
      change del < |(maxDegree t : ℝ) / ((n : ℝ) * gam) - 1|
      have heg : ε / gam < 1 := (div_lt_one hgam).mpr (by simpa [gam] using hεm)
      rw [abs_of_neg (sub_neg.mpr (hratio.trans heg))]
      dsimp [del]
      linarith
  have hbound : ∀ᶠ n in atTop,
      (conditioned μ n (finiteTreeEvent fun t => ¬ G n t)).toReal ≤
        (conditioned μ n (B1 n)).toReal + (conditioned μ n (B2 n)).toReal := by
    filter_upwards [hsubset] with n hn
    have hfin (A : Set BGW.LocallyFinite.Tree) : conditioned μ n A ≠ ∞ := by
      unfold conditioned
      finiteness
    calc
      _ ≤ (conditioned μ n (B1 n ∪ B2 n)).toReal :=
        ENNReal.toReal_mono (hfin _) (measure_mono hn)
      _ ≤ (conditioned μ n (B1 n) + conditioned μ n (B2 n)).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin _, hfin _⟩)
          (measure_union_le _ _)
      _ = _ := by rw [ENNReal.toReal_add (hfin _) (hfin _)]
  have hbad : Tendsto (fun n : ℕ =>
      (conditioned μ n (finiteTreeEvent fun t => ¬ G n t)).toReal) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hbound
      (by simpa only [zero_add] using hB1.add hB2)
  have hone := (tendsto_const_nhds (x := (1 : ℝ))).sub hbad
  simp only [sub_zero] at hone
  change Tendsto (fun n : ℕ => (conditioned μ n (finiteTreeEvent (G n))).toReal) atTop (𝓝 1)
  apply hone.congr'
  filter_upwards [eventually_size_admissible μ hμ.to_literal] with n hn
  let _ : IsProbabilityMeasure (conditioned μ n) := conditioned_isProbability μ n hn
  have hmeas : MeasurableSet (finiteTreeEvent (G n)) :=
    ((Set.to_countable {t : BGW.PlaneTree | G n t}).image
      BGW.PlaneTree.toLocallyFinite).measurableSet
  have hprob := probReal_add_probReal_compl (μ := conditioned μ n) hmeas
  rw [uconseq_conditioned_not_eq_compl]
  dsimp only [Measure.real] at hprob ⊢
  linarith

/-- U2.8: every source-normalized scaling sequence is regularly varying of
index one,using the floor of `lam * n` as the rounding convention. -/
theorem unnumbered_scaling_regularly_varying
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun n : ℕ => a (Nat.floor (lam * (n : ℝ))) / a n) atTop (𝓝 lam) :=
  uconseq_scaling_index_div μ hμ a ha hlam

/-- U2.8 for the centering: `|b⌊lam*n⌋| / |bₙ| → lam`. -/
theorem unnumbered_abs_centering_regularly_varying
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun n : ℕ =>
      |centering μ a (Nat.floor (lam * (n : ℝ)))| / |centering μ a n|)
      atTop (𝓝 lam) := by
  let k : ℕ → ℕ := fun n => Nat.floor (lam * (n : ℝ))
  let m : ℝ := (offspringMean μ).toReal
  have hm : m < 1 := by
    have hfin : offspringMean μ ≠ ∞ := ne_top_of_lt (hμ.1.trans ENNReal.one_lt_top)
    simpa [m] using (ENNReal.toReal_lt_toReal hfin ENNReal.one_ne_top).mpr hμ.1
  have hc : 0 < 1 - m := sub_pos.mpr hm
  have hkTop : Tendsto k atTop atTop := uconseq_indexTop hlam
  have hkdiv : Tendsto (fun n : ℕ => (k n : ℝ) / (n : ℝ)) atTop (𝓝 lam) :=
    uconseq_index_div hlam
  have hb := paper_centering_ratio_tendsto_one μ hμ.to_literal ha
  have hbk := hb.comp hkTop
  have hratio := (hbk.div hb one_ne_zero).mul hkdiv
  have heq : (fun n : ℕ =>
      ((centering μ a (k n) / (-(k n : ℝ) * (1 - m))) /
        (centering μ a n / (-(n : ℝ) * (1 - m)))) *
        ((k n : ℝ) / (n : ℝ))) =ᶠ[atTop]
      (fun n : ℕ => |centering μ a (k n)| / |centering μ a n|) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ), hkTop.eventually_gt_atTop 0,
      hb.eventually (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
      hbk.eventually (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with n hn hk hnpos hkpos
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hkR : (0 : ℝ) < k n := Nat.cast_pos.mpr hk
    have hdn : -(n : ℝ) * (1 - m) < 0 := by nlinarith [mul_pos hnR hc]
    have hdk : -(k n : ℝ) * (1 - m) < 0 := by nlinarith [mul_pos hkR hc]
    have hbn : centering μ a n < 0 := by
      rcases div_pos_iff.mp hnpos with h | h
      · nlinarith
      · exact h.1
    have hbkneg : centering μ a (k n) < 0 := by
      rcases div_pos_iff.mp hkpos with h | h
      · nlinarith
      · exact h.1
    rw [abs_of_neg hbn, abs_of_neg hbkneg]
    field_simp [hnR.ne', hkR.ne', hc.ne', hbn.ne, hbkneg.ne]
  change Tendsto (fun n : ℕ => |centering μ a (k n)| / |centering μ a n|) atTop (𝓝 lam)
  simpa only [one_div, div_one, one_mul] using hratio.congr' heq

/-- U2.10(a): `Wₙ / (n(m-1)) → 1` in probability. -/
theorem unnumbered_walk_drift_ratio
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n => μ)).real
      {ω | ε ≤ |(finiteWalkSum ω : ℝ) /
        ((n : ℝ) * ((offspringMean μ).toReal - 1)) - 1|}) atTop (𝓝 0) :=
  finiteWalk_driftRatio_deviation_tendsto_zero μ hμ.1 hε

/-- The mean-centering defect divided by `aₙ` tends to `+∞`. -/
theorem unnumbered_centering_defect_div_scaling_tendsto_atTop
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) :
    Tendsto (fun n : ℕ =>
      ((n : ℝ) * ((offspringMean μ).toReal - 1) - centering μ a n) / a n)
      atTop atTop := by
  obtain ⟨hm, L, hpos, hsv, hmeas, hlocal⟩ := hμ
  have hfin : offspringMean μ ≠ ∞ := ne_top_of_lt (hm.trans ENNReal.one_lt_top)
  have hsum := summable_localModel_over_nat μ hfin hpos hlocal
  have haTop := scaling_tendsto_atTop μ ⟨hm, L, hpos, hsv, hlocal⟩ ha
  have htail := (tailIncrementMean_div_ellStarReal_tendsto_one
    μ hfin hpos hmeas hsv hlocal).comp haTop
  have hzero : Tendsto (fun n : ℕ => L (a n) / ellStarReal L (a n))
      atTop (𝓝 0) := (localModel_div_ellStarReal_tendsto_zero
    hpos hmeas hsv hsum).comp haTop
  have hzeroGT : Tendsto (fun n : ℕ => L (a n) / ellStarReal L (a n))
      atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨hzero,
    (haTop.eventually_gt_atTop 0).mono (fun n hn =>
      div_pos (hpos _ hn) (ellStarReal_pos hpos hsum _))⟩
  have hmodel := hzeroGT.inv_tendsto_nhdsGT_zero
  have hscale := scaling_div_mul_tendsto_one μ hm hpos hmeas hsv hlocal ha
  have hscaleInv : Tendsto (fun n : ℕ =>
      ((n : ℝ) * L (a n)) / a n) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).div hscale one_ne_zero
    simpa only [Pi.div_def, one_div, inv_div, div_one] using h
  have hnum := htail.mul hscaleInv
  have hnum' : Tendsto (fun n : ℕ =>
      (tailIncrementMean μ (a n) / ellStarReal L (a n)) *
        (((n : ℝ) * L (a n)) / a n)) atTop (𝓝 1) := by
    simpa only [one_mul, Function.comp_def] using hnum
  have hprod := hmodel.atTop_mul_pos zero_lt_one hnum'
  have heq : (fun n : ℕ =>
      ((tailIncrementMean μ (a n) / ellStarReal L (a n)) *
        (((n : ℝ) * L (a n)) / a n)) *
        (ellStarReal L (a n) / L (a n))) =ᶠ[atTop]
      (fun n : ℕ =>
        ((n : ℝ) * ((offspringMean μ).toReal - 1) - centering μ a n) / a n) := by
    filter_upwards [haTop.eventually_gt_atTop 0, eventually_gt_atTop (0 : ℕ)] with n han hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have hLpos := hpos _ han
    have hellpos := ellStarReal_pos hpos hsum (a n)
    have hshift := centering_shift_eq_tail μ hfin a n
    field_simp [hn0, han.ne', hLpos.ne', hellpos.ne']
    nlinarith
  have hprod' : Tendsto (fun n : ℕ =>
      ((tailIncrementMean μ (a n) / ellStarReal L (a n)) *
        (((n : ℝ) * L (a n)) / a n)) *
        (ellStarReal L (a n) / L (a n))) atTop atTop := by
    simpa only [Pi.inv_apply, inv_div, mul_comm] using hprod
  exact hprod'.congr' heq


/-- The expectation of the sum of `n` independent increments is `n * (m-1)`. -/
theorem unnumbered_incrementWalk_expectation
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ ≠ ∞) (n : ℕ) :
    ∫ x : Fin n → ℤ, ((∑ i, x i : ℤ) : ℝ) ∂(Measure.pi fun _ : Fin n => incrementLaw μ) =
      (n : ℝ) * ((offspringMean μ).toReal - 1) := by
  let uconseqCenteredLawProbability : IsProbabilityMeasure (incrementLaw μ) := by
    unfold incrementLaw
    infer_instance
  have hcast : Integrable (fun z : ℤ => (z : ℝ)) (incrementLaw μ) := by
    unfold incrementLaw
    apply (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_countable _).aemeasurable).mpr
    have heq : ((fun z : ℤ => (z : ℝ)) ∘ fun k : ℕ => (k : ℤ) - 1) =
        offspringIncrement := by
      funext k
      simp [offspringIncrement]
    rw [heq]
    exact integrable_offspringIncrement μ hm
  push_cast
  rw [integral_finsetSum]
  · simp_rw [integral_comp_eval (μ := fun _ : Fin n => incrementLaw μ)
      hcast.aestronglyMeasurable]
    unfold incrementLaw
    rw [integral_map (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aestronglyMeasurable]
    simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one]
    rw [show (fun k : ℕ => (k : ℝ) - 1) = offspringIncrement from rfl,
      integral_offspringIncrement μ hm]
    simp [Finset.sum_const, nsmul_eq_mul]
    ring
  · intro i hi
    exact integrable_comp_eval hcast

/-- The law of `(Wₙ - E Wₙ) / aₙ`; the centering is identified with
`n * (m-1)` by `unnumbered_incrementWalk_expectation`. -/
noncomputable def meanCenteredIncrementLaw
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (a : ℕ → ℝ) (n : ℕ) :
    ProbabilityMeasure ℝ := by
  let meanCenteredIncrementLawProbability : IsProbabilityMeasure (incrementLaw μ) := by
    unfold incrementLaw
    infer_instance
  exact ⟨(Measure.pi fun _ : Fin n => incrementLaw μ).map (fun x =>
    (((∑ i, x i : ℤ) : ℝ) - (n : ℝ) * ((offspringMean μ).toReal - 1)) / a n),
    inferInstance⟩

private theorem uconseq_normalizedIncrementLaw_tight
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) :
    IsTightMeasureSet (Set.range fun n => (normalizedIncrementLaw μ a n : Measure ℝ)) := by
  let Λ : ℝ → ℝ := fun s => s * Real.log s +
    (Real.eulerMascheroniConstant - 1) * s
  have hΛ0 : Λ 0 = 0 := by simp [Λ]
  have hΛcont : ContinuousWithinAt (fun s => Real.exp (Λ s)) (Set.Ioi 0) 0 := by
    have hc : Continuous Λ := by
      exact Real.continuous_mul_log.add (continuous_const.mul continuous_id)
    exact hc.rexp.continuousWithinAt
  exact isTightMeasureSet_range_of_exponential_laplace_limit hΛ0 hΛcont
    (normalizedIncrementLaw μ a) (fun s hs => by
      simpa only [Λ] using normalizedIncrementLaw_laplace_tendsto μ hμ
        (oneStepLaplaceLimit_holds μ) a ha hs)

private theorem uconseq_uniform_stable_tail
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) {η : ℝ} (hη : 0 < η) :
    ∃ R : ℝ, ∀ n : ℕ,
      (normalizedIncrementLaw μ a n : Measure ℝ).real {x | R < ‖x‖} ≤ η := by
  have htight := tendsto_measure_norm_gt_of_isTightMeasureSet
    (uconseq_normalizedIncrementLaw_tight μ hμ a ha)
  simp only [iSup_range] at htight
  rw [ENNReal.tendsto_atTop_zero] at htight
  obtain ⟨R, hR⟩ := htight (ENNReal.ofReal η) (ENNReal.ofReal_pos.mpr hη)
  refine ⟨R, fun n => ?_⟩
  have hbound : (normalizedIncrementLaw μ a n : Measure ℝ) {x | R < ‖x‖} ≤
      ENNReal.ofReal η := (le_iSup (fun k : ℕ =>
        (normalizedIncrementLaw μ a k : Measure ℝ) {x | R < ‖x‖}) n).trans
          (hR R le_rfl)
  rw [Measure.real, ← ENNReal.toReal_ofReal hη.le]
  exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound

private theorem uconseq_meanCenteredLaw_eq_shift
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (a : ℕ → ℝ) (n : ℕ) :
    (meanCenteredIncrementLaw μ a n : Measure ℝ) =
      (normalizedIncrementLaw μ a n : Measure ℝ).map (fun x => x -
        (((n : ℝ) * ((offspringMean μ).toReal - 1) - centering μ a n) / a n)) := by
  let uconseqShiftLawProbability : IsProbabilityMeasure (incrementLaw μ) := by
    unfold incrementLaw
    infer_instance
  have hnorm : Measurable (fun x : Fin n → ℤ =>
      (((∑ i, x i : ℤ) : ℝ) - centering μ a n) / a n) := by fun_prop
  have hshift : Measurable (fun x : ℝ => x -
      (((n : ℝ) * ((offspringMean μ).toReal - 1) - centering μ a n) / a n)) := by fun_prop
  rw [meanCenteredIncrementLaw, normalizedIncrementLaw]
  change (Measure.pi fun _ : Fin n => incrementLaw μ).map _ =
    Measure.map _ (Measure.map _ _)
  rw [Measure.map_map hshift hnorm]
  apply Measure.map_congr
  filter_upwards [] with x
  simp only [Function.comp_def]
  push_cast
  ring


/-- U2.10(b), escape form: for every fixed real `M`, the upper tail of the
mean-centered walk above `M` has probability tending to zero. -/
theorem unnumbered_meanCenteredWalk_tendsto_atBot_in_probability
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) (M : ℝ) :
    Tendsto (fun n : ℕ =>
      (meanCenteredIncrementLaw μ a n : Measure ℝ).real {x | M ≤ x}) atTop (𝓝 0) := by
  let d : ℕ → ℝ := fun n =>
    ((n : ℝ) * ((offspringMean μ).toReal - 1) - centering μ a n) / a n
  have hd : Tendsto d atTop atTop := by
    simpa only [d] using unnumbered_centering_defect_div_scaling_tendsto_atTop μ hμ a ha
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro q hq
    filter_upwards [] with n
    exact hq.trans_le measureReal_nonneg
  · intro q hq
    have hqpos : 0 < q := hq
    obtain ⟨R, hR⟩ := uconseq_uniform_stable_tail μ hμ a ha (half_pos hqpos)
    filter_upwards [hd.eventually_gt_atTop (R - M)] with n hn
    have hsubset : {x : ℝ | M + d n ≤ x} ⊆ {x : ℝ | R < ‖x‖} := by
      intro x hx
      have hRx : R < x := by
        change M + d n ≤ x at hx
        linarith
      exact hRx.trans_le (le_abs_self x)
    have hlaw := uconseq_meanCenteredLaw_eq_shift μ a n
    change (meanCenteredIncrementLaw μ a n : Measure ℝ) =
      (normalizedIncrementLaw μ a n : Measure ℝ).map (fun x => x - d n) at hlaw
    have hshift : Measurable (fun x : ℝ => x - d n) := by fun_prop
    have hset : (fun x : ℝ => x - d n) ⁻¹' {x | M ≤ x} = {x | M + d n ≤ x} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_ofPred_eq]
      constructor <;> intro hx <;> linarith
    calc
      (meanCenteredIncrementLaw μ a n : Measure ℝ).real {x | M ≤ x} =
          (normalizedIncrementLaw μ a n : Measure ℝ).real {x | M + d n ≤ x} := by
        rw [Measure.real, hlaw, Measure.map_apply hshift
          (show MeasurableSet {x : ℝ | M ≤ x} from measurableSet_Ici), hset]
        rfl
      _ ≤ (normalizedIncrementLaw μ a n : Measure ℝ).real {x | R < ‖x‖} :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsubset)
      _ ≤ q / 2 := hR n
      _ < q := half_lt_self hqpos


private theorem uconseq_logistic_integral_tendsto_zero
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => ∫ x, uconseqLogistic x
      ∂(meanCenteredIncrementLaw μ a n : Measure ℝ)) atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro q hq
    filter_upwards [] with n
    exact hq.trans_le (integral_nonneg fun x => (uconseqLogistic_pos x).le)
  · intro q hq
    have hqpos : 0 < q := hq
    have hsmall := uconseqLogistic_tendsto_atBot.eventually
      (Iio_mem_nhds (half_pos hqpos))
    obtain ⟨K, hK⟩ := eventually_atBot.mp hsmall
    have hprob := (unnumbered_meanCenteredWalk_tendsto_atBot_in_probability
      μ hμ a ha K).eventually (Iio_mem_nhds (half_pos hqpos))
    filter_upwards [hprob] with n hn
    have hgInt : Integrable uconseqLogistic (meanCenteredIncrementLaw μ a n : Measure ℝ) :=
      Integrable.of_bound uconseqLogistic_continuous.aestronglyMeasurable 1
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_pos (uconseqLogistic_pos x)]
          exact uconseqLogistic_le_one x)
    have hset : MeasurableSet {x : ℝ | K ≤ x} := measurableSet_Ici
    have hind : Integrable ({x : ℝ | K ≤ x}.indicator (fun _ => (1 : ℝ)))
        (meanCenteredIncrementLaw μ a n : Measure ℝ) :=
      (integrable_const 1).indicator hset
    have hright : Integrable (fun x => q / 2 + {x : ℝ | K ≤ x}.indicator (fun _ => (1 : ℝ)) x)
        (meanCenteredIncrementLaw μ a n : Measure ℝ) := (integrable_const _).add hind
    calc
      (∫ x, uconseqLogistic x ∂(meanCenteredIncrementLaw μ a n : Measure ℝ)) ≤
          ∫ x, (q / 2 + {x : ℝ | K ≤ x}.indicator (fun _ => (1 : ℝ)) x)
            ∂(meanCenteredIncrementLaw μ a n : Measure ℝ) := by
        apply integral_mono hgInt hright
        intro x
        change uconseqLogistic x ≤ q / 2 +
          {x : ℝ | K ≤ x}.indicator (fun _ => (1 : ℝ)) x
        by_cases hx : K ≤ x
        · simp only [Set.indicator_apply, Set.mem_ofPred_eq, hx, ite_true]
          exact (uconseqLogistic_le_one x).trans (by linarith)
        · have hxK : x ≤ K := le_of_not_ge hx
          have hg := hK x hxK
          simp only [Set.indicator_apply, Set.mem_ofPred_eq, hx, ite_false, add_zero]
          exact hg.le
      _ = q / 2 + (meanCenteredIncrementLaw μ a n : Measure ℝ).real {x | K ≤ x} := by
        rw [integral_add (integrable_const _) hind, integral_indicator_const 1 hset]
        simp
      _ < q / 2 + q / 2 := add_lt_add_right hn _
      _ = q := by ring

/-- U2.10(b): `(Wₙ - E Wₙ) / aₙ` has no distributional limit which is a
probability measure on `ℝ`. -/
theorem unnumbered_meanCenteredWalk_not_convergent_in_distribution
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) :
    ¬ ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
      ∀ f : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun n : ℕ => ∫ x, f x ∂(meanCenteredIncrementLaw μ a n : Measure ℝ))
          atTop (𝓝 (∫ y, f y ∂ν)) := by
  rintro ⟨ν, hν, hlim⟩
  let unnumberedCandidateProbability : IsProbabilityMeasure ν := hν
  let g : BoundedContinuousFunction ℝ ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup uconseqLogistic
      uconseqLogistic_continuous 1 (fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (uconseqLogistic_pos x)]
        exact uconseqLogistic_le_one x)
  have hlim' : Tendsto (fun n : ℕ => ∫ x, uconseqLogistic x
      ∂(meanCenteredIncrementLaw μ a n : Measure ℝ)) atTop
      (𝓝 (∫ y, uconseqLogistic y ∂ν)) := hlim g
  have hzero := uconseq_logistic_integral_tendsto_zero μ hμ a ha
  have heq : (∫ y, uconseqLogistic y ∂ν) = 0 := tendsto_nhds_unique hlim' hzero
  exact (uconseqLogistic_integral_pos ν).ne' heq

end
end SubcriticalCauchy.Bienayme
