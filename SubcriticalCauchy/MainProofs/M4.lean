module

public import SubcriticalCauchy.Propositions42_43
public import SubcriticalCauchy.BienaymeForestLog

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Proof helpers for the frozen statement M4

The proof applies Proposition 4.3 at the two logarithmic thresholds.  The
thresholds are replaced by their maxima with one in order to meet its global
positivity hypothesis; all the relevant limits are unchanged eventually.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section
open BGW BGW.LocallyFinite

attribute [local instance] Classical.propDecidable

private theorem measurableSet_finiteTreeEvent_m4 (P : PlaneTree → Prop) :
    MeasurableSet (finiteTreeEvent P) :=
  ((Set.to_countable {t : PlaneTree | P t}).image
    PlaneTree.toLocallyFinite).measurableSet

private theorem toLocallyFinite_mem_finiteTreeEvent_iff_m4
    (P : PlaneTree → Prop) (t : PlaneTree) :
    t.toLocallyFinite ∈ finiteTreeEvent P ↔ P t := by
  constructor
  · rintro ⟨s, hs, hst⟩
    have hst' : s = t := PlaneTree.toLocallyFinite_injective hst
    simpa only [hst', Set.mem_ofPred_eq] using hs
  · intro ht
    exact ⟨t, ht, rfl⟩

private theorem conditioned_ne_top_m4 (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (n : ℕ) (A : Set Tree) : conditioned μ n A ≠ ∞ := by
  unfold conditioned
  finiteness

private theorem conditioned_apply_eq_tsum_plane_m4 (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (n : ℕ) (A : Set Tree) (hA : MeasurableSet A) :
    conditioned μ n A =
      ∑' t : PlaneTree, conditioned μ n {t.toLocallyFinite} *
        (if t.toLocallyFinite ∈ A then 1 else 0) := by
  classical
  let f (t : PlaneTree) : ℝ≥0∞ := conditioned μ n {t.toLocallyFinite} *
    (if t.toLocallyFinite ∈ A then 1 else 0)
  change conditioned μ n A = ∑' t : PlaneTree, f t
  change (bienaymeLaw μ (sizeEvent n))⁻¹ *
      (bienaymeLaw μ).restrict (sizeEvent n) A = _
  rw [restrict_sizeEvent_apply μ n A hA, ← ENNReal.tsum_mul_left]
  have hatom (t : PlaneTree) : conditioned μ n {t.toLocallyFinite} =
      (bienaymeLaw μ (sizeEvent n))⁻¹ *
        (if t.size = n then PlaneTree.weight (fun k => μ {k}) t else 0) := by
    change (bienaymeLaw μ (sizeEvent n))⁻¹ *
      (bienaymeLaw μ).restrict (sizeEvent n) {t.toLocallyFinite} = _
    rw [restrict_sizeEvent_apply μ n _ (MeasurableSet.singleton _)]
    have heq (s : PlaneTree) : s.toLocallyFinite = t.toLocallyFinite ↔ s = t := by
      constructor
      · exact fun h => PlaneTree.toLocallyFinite_injective h
      · exact congrArg PlaneTree.toLocallyFinite
    simp [heq]
  simp only [f, hatom, mul_assoc]

private theorem conditioned_finiteTreeEvent_not_eq_compl (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (n : ℕ) (P : PlaneTree → Prop) :
    conditioned μ n (finiteTreeEvent fun t => ¬ P t) =
      conditioned μ n (finiteTreeEvent P)ᶜ := by
  classical
  rw [conditioned_apply_eq_tsum_plane_m4 μ n _ (measurableSet_finiteTreeEvent_m4 _),
    conditioned_apply_eq_tsum_plane_m4 μ n _
      (measurableSet_finiteTreeEvent_m4 _).compl]
  apply tsum_congr
  intro t
  by_cases ht : P t <;>
    simp [toLocallyFinite_mem_finiteTreeEvent_iff_m4, ht]

/-- On an eventually admissible size, a complementary finite-tree event has
real probability tending to zero when the original probability tends to one. -/
private theorem conditioned_not_tendsto_zero_real (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (hμ : IsMeasurableSubcriticalCauchyOffspring μ)
    (P : ℕ → PlaneTree → Prop)
    (hP : Tendsto (fun n : ℕ => conditioned μ n (finiteTreeEvent (P n)))
      atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => (conditioned μ n
      (finiteTreeEvent fun t => ¬ P n t)).toReal) atTop (𝓝 0) := by
  have hr : Tendsto (fun n : ℕ => (conditioned μ n
      (finiteTreeEvent (P n))).toReal) atTop (𝓝 1) := by
    simpa using (ENNReal.tendsto_toReal_iff
      (fun n => conditioned_ne_top_m4 μ n _) ENNReal.one_ne_top).mpr hP
  have hz := (tendsto_const_nhds (x := (1 : ℝ))).sub hr
  simp only [sub_self] at hz
  apply hz.congr'
  filter_upwards [eventually_size_admissible μ hμ.to_literal] with n hn
  let _ : IsProbabilityMeasure (conditioned μ n) := conditioned_isProbability μ n hn
  rw [conditioned_finiteTreeEvent_not_eq_compl,
    measure_compl (measurableSet_finiteTreeEvent_m4 _) (conditioned_ne_top_m4 μ n _),
    measure_univ, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
    ENNReal.toReal_one]

private theorem logarithmicHeightThreshold_tendsto_atTop_m4 {m c : ℝ}
    (hc : 0 < c / Real.log (1 / m)) :
    Tendsto (logarithmicHeightThreshold m c) atTop atTop := by
  exact tendsto_log_nat_atTop.const_mul_atTop hc

private theorem main_height_log_small_real (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (δ : ℝ) (hδ : 0 < δ)
    (hδL : δ * Real.log (1 / (offspringMean μ).toReal) < 1) :
    Tendsto (fun n : ℕ => (conditioned μ n (finiteTreeEvent fun t =>
      δ < |(height t : ℝ) / Real.log n -
        1 / Real.log (1 / (offspringMean μ).toReal)|)).toReal) atTop (𝓝 0) := by
  let L := Real.log (1 / (offspringMean μ).toReal)
  let upper : ℕ → ℝ := fun n => max
    (logarithmicHeightThreshold (offspringMean μ).toReal (1 + δ * L) n) 1
  let lower : ℕ → ℝ := fun n => max
    (logarithmicHeightThreshold (offspringMean μ).toReal (1 - δ * L) n) 1
  have hm0 : 0 < offspringMean μ := offspringMean_pos_of_paper μ hμ.to_literal
  have hm1 : offspringMean μ < 1 := hμ.1
  have hfin : offspringMean μ ≠ ∞ := ne_top_of_lt (hm1.trans ENNReal.one_lt_top)
  have hmR0 : 0 < (offspringMean μ).toReal := ENNReal.toReal_pos hm0.ne' hfin
  have hmR1 : (offspringMean μ).toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hfin ENNReal.one_ne_top).mpr hm1
  have hL : 0 < L := log_inv_mean_pos hmR0 hmR1
  have hδLpos : 0 < δ * L := mul_pos hδ hL
  have huTop : Tendsto (fun n : ℕ =>
      logarithmicHeightThreshold (offspringMean μ).toReal (1 + δ * L) n)
      atTop atTop :=
    logarithmicHeightThreshold_tendsto_atTop_m4 (div_pos (by linarith) hL)
  have hlTop : Tendsto (fun n : ℕ =>
      logarithmicHeightThreshold (offspringMean μ).toReal (1 - δ * L) n)
      atTop atTop :=
    logarithmicHeightThreshold_tendsto_atTop_m4 (div_pos (by linarith) hL)
  have huTop' : Tendsto upper atTop atTop := by
    apply huTop.congr'
    filter_upwards [huTop.eventually_ge_atTop 1] with n hn
    exact (max_eq_left hn).symm
  have hlTop' : Tendsto lower atTop atTop := by
    apply hlTop.congr'
    filter_upwards [hlTop.eventually_ge_atTop 1] with n hn
    exact (max_eq_left hn).symm
  have huQ : Tendsto (fun n : ℕ =>
      (n : ℝ) * (survival μ ⌈upper n⌉₊).toReal) atTop (𝓝 0) := by
    apply (survival_log_upper_tendsto_zero μ hm0 hm1 (by exact hδLpos)).congr'
    filter_upwards [huTop.eventually_ge_atTop 1] with n hn
    simp only [upper, max_eq_left hn]
  have hlQ : Tendsto (fun n : ℕ =>
      (n : ℝ) * (survival μ ⌈lower n⌉₊).toReal) atTop atTop := by
    apply (survival_log_lower_tendsto_atTop μ hm0 hm1 (by exact hδLpos) (by simpa only [L] using hδL)).congr'
    filter_upwards [hlTop.eventually_ge_atTop 1] with n hn
    simp only [lower, max_eq_left hn]
  have huGood := paper_height_upper μ hμ upper
    (fun n => lt_of_lt_of_le zero_lt_one (le_max_right _ _)) huTop' huQ
  have hlGood := paper_height_lower μ hμ lower
    (fun n => lt_of_lt_of_le zero_lt_one (le_max_right _ _)) hlTop' hlQ
  have huBad : Tendsto (fun n : ℕ => (conditioned μ n
      (finiteTreeEvent fun t => (upper n : ℝ) ≤ (height t : ℝ))).toReal)
      atTop (𝓝 0) := by
    simpa only [not_lt] using conditioned_not_tendsto_zero_real μ hμ
      (fun n t => (height t : ℝ) < upper n) huGood
  have hlBad : Tendsto (fun n : ℕ => (conditioned μ n
      (finiteTreeEvent fun t => (height t : ℝ) < lower n)).toReal)
      atTop (𝓝 0) := by
    simpa only [not_le] using conditioned_not_tendsto_zero_real μ hμ
      (fun n t => lower n ≤ (height t : ℝ)) hlGood
  apply squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) ?_
    (by simpa using huBad.add hlBad)
  filter_upwards [huTop.eventually_ge_atTop 1, hlTop.eventually_ge_atTop 1,
    eventually_gt_atTop (1 : ℕ)] with n hu hl hn
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have huEq : upper n =
      (1 / L + δ) * Real.log n := by
    simp only [upper, max_eq_left hu]
    change (1 + δ * L) / L * Real.log n = (1 / L + δ) * Real.log n
    field_simp [hL.ne']
  have hlEq : lower n =
      (1 / L - δ) * Real.log n := by
    simp only [lower, max_eq_left hl]
    change (1 - δ * L) / L * Real.log n = (1 / L - δ) * Real.log n
    field_simp [hL.ne']
  calc
    (conditioned μ n (finiteTreeEvent fun t =>
      δ < |(height t : ℝ) / Real.log n - 1 /
        Real.log (1 / (offspringMean μ).toReal)|)).toReal ≤
        (conditioned μ n ((finiteTreeEvent fun t => upper n ≤ (height t : ℝ)) ∪
          (finiteTreeEvent fun t => (height t : ℝ) < lower n))).toReal := by
      apply ENNReal.toReal_mono (conditioned_ne_top_m4 μ n _)
      apply measure_mono
      rintro _ ⟨t, ht, rfl⟩
      change δ < |(height t : ℝ) / Real.log n - 1 / L| at ht
      rcases lt_abs.mp ht with hup | hlow
      · apply Or.inl
        refine ⟨t, ?_, rfl⟩
        change upper n ≤ (height t : ℝ)
        rw [huEq]
        apply le_of_lt
        apply (lt_div_iff₀ hlog).mp
        linarith
      · apply Or.inr
        refine ⟨t, ?_, rfl⟩
        change (height t : ℝ) < lower n
        rw [hlEq]
        apply (div_lt_iff₀ hlog).mp
        linarith
    _ ≤ ((conditioned μ n (finiteTreeEvent fun t => upper n ≤ (height t : ℝ))) +
        (conditioned μ n (finiteTreeEvent fun t => (height t : ℝ) < lower n))).toReal :=
      ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
        ⟨conditioned_ne_top_m4 μ n _, conditioned_ne_top_m4 μ n _⟩) (measure_union_le _ _)
    _ = _ := ENNReal.toReal_add (conditioned_ne_top_m4 μ n _) (conditioned_ne_top_m4 μ n _)

/-- Theorem 1.1(iii)(a). -/
theorem main_height_log_proof (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => conditioned μ n (finiteTreeEvent fun t =>
      ε < |(height t : ℝ) / Real.log n -
        1 / Real.log (1 / (offspringMean μ).toReal)|)) atTop (𝓝 0) := by
  apply (ENNReal.tendsto_toReal_zero_iff (fun n => by
    unfold conditioned
    finiteness)).mp
  let L := Real.log (1 / (offspringMean μ).toReal)
  let δ := min ε (1 / (2 * L))
  have hm0 : 0 < offspringMean μ := offspringMean_pos_of_paper μ hμ.to_literal
  have hm1 : offspringMean μ < 1 := hμ.1
  have hfin : offspringMean μ ≠ ∞ := ne_top_of_lt (hm1.trans ENNReal.one_lt_top)
  have hmR0 : 0 < (offspringMean μ).toReal := ENNReal.toReal_pos hm0.ne' hfin
  have hmR1 : (offspringMean μ).toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hfin ENNReal.one_ne_top).mpr hm1
  have hL : 0 < L := log_inv_mean_pos hmR0 hmR1
  have hδ : 0 < δ := lt_min hε (by positivity)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδL : δ * L < 1 := by
    have hle : δ ≤ 1 / (2 * L) := min_le_right _ _
    calc
      δ * L ≤ (1 / (2 * L)) * L := mul_le_mul_of_nonneg_right hle hL.le
      _ = 1 / 2 := by field_simp [hL.ne']
      _ < 1 := by norm_num
  apply squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) ?_
    (main_height_log_small_real μ hμ δ hδ (by simpa only [L] using hδL))
  apply Eventually.of_forall
  intro n
  apply ENNReal.toReal_mono (conditioned_ne_top_m4 μ n _)
  apply measure_mono
  rintro _ ⟨t, ht, rfl⟩
  exact ⟨t, hδε.trans_lt ht, rfl⟩

end
end SubcriticalCauchy.Bienayme
