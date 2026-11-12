module

public import SubcriticalCauchy.Corollary41
public import SubcriticalCauchy.RefinedCentering
public import SubcriticalCauchy.SlowVariationBoundary
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp

/-! # Auxiliary asymptotics for the unnumbered consequences -/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section

theorem uconseq_indexTop {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun n : ℕ => Nat.floor (lam * (n : ℝ))) atTop atTop :=
  tendsto_nat_floor_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hlam)

theorem uconseq_index_div {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun n : ℕ => (Nat.floor (lam * (n : ℝ)) : ℝ) / (n : ℝ))
      atTop (𝓝 lam) := by
  have hmul : Tendsto (fun n : ℕ => lam * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hlam
  have hfloor := tendsto_nat_floor_div_atTop.comp hmul
  have hprod := hfloor.mul_const lam
  have heq : (fun n : ℕ =>
      ((Nat.floor (lam * (n : ℝ)) : ℝ) / (lam * (n : ℝ))) * lam) =ᶠ[atTop]
      (fun n : ℕ => (Nat.floor (lam * (n : ℝ)) : ℝ) / (n : ℝ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    field_simp [hlam.ne', hn0]
  simpa only [Function.comp_def, one_mul] using hprod.congr' heq

/-- The fixed-factor tail ratio used in the scale squeeze. -/
private theorem uconseq_tail_const_mul_div
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (haTop : Tendsto a atTop atTop) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ =>
      (incrementTail μ (c * a n)).toReal / (incrementTail μ (a n)).toReal)
      atTop (𝓝 (1 / c)) := by
  obtain ⟨hm, L, hpos, hsv, hmeas, hlocal⟩ := hμ
  have hcurr := (incrementTail_div_tendsto_one μ hm hpos hmeas hsv hlocal).comp haTop
  have hscaled := (incrementTail_div_tendsto_one μ hm hpos hmeas hsv hlocal).comp
    (haTop.const_mul_atTop hc)
  have hL := (hsv c hc).comp haTop
  have hcurrInv : Tendsto (fun n : ℕ =>
      (L (a n) / a n) / (incrementTail μ (a n)).toReal) atTop (𝓝 1) := by
    simpa only [Pi.div_def, one_div, inv_div, div_one, Function.comp_def] using
      (tendsto_const_nhds (x := (1 : ℝ))).div hcurr one_ne_zero
  have hprod := hscaled.mul (hL.const_mul (1 / c)) |>.mul hcurrInv
  have heq : (fun n : ℕ =>
      ((incrementTail μ (c * a n)).toReal / (L (c * a n) / (c * a n))) *
        ((1 / c) * (L (c * a n) / L (a n))) *
        ((L (a n) / a n) / (incrementTail μ (a n)).toReal)) =ᶠ[atTop]
      (fun n : ℕ =>
        (incrementTail μ (c * a n)).toReal / (incrementTail μ (a n)).toReal) := by
    filter_upwards [haTop.eventually_gt_atTop 0] with n han
    have hca : 0 < c * a n := mul_pos hc han
    have hLc : 0 < L (c * a n) := hpos _ hca
    have hLa : 0 < L (a n) := hpos _ han
    have hTc : (incrementTail μ (c * a n)).toReal ≠ 0 :=
      (ENNReal.toReal_pos (incrementTail_pos μ ⟨hm, ⟨L, hpos, hsv, hlocal⟩⟩
        (c * a n)).ne' (measure_ne_top _ _)).ne'
    have hTa : (incrementTail μ (a n)).toReal ≠ 0 :=
      (ENNReal.toReal_pos (incrementTail_pos μ ⟨hm, ⟨L, hpos, hsv, hlocal⟩⟩
        (a n)).ne' (measure_ne_top _ _)).ne'
    field_simp [hc.ne', han.ne', hLc.ne', hLa.ne', hTc, hTa]
  simpa only [Function.comp_def, one_mul, inv_one, mul_one] using hprod.congr' heq

private theorem uconseq_tail_index_div
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun n : ℕ =>
      (incrementTail μ (a (Nat.floor (lam * (n : ℝ))))).toReal /
        (incrementTail μ (a n)).toReal) atTop (𝓝 (1 / lam)) := by
  let k : ℕ → ℕ := fun n => Nat.floor (lam * (n : ℝ))
  have hkTop : Tendsto k atTop atTop := uconseq_indexTop hlam
  have hkdiv : Tendsto (fun n : ℕ => (k n : ℝ) / (n : ℝ)) atTop (𝓝 lam) :=
    uconseq_index_div hlam
  have hk : Tendsto (fun n : ℕ => (k n : ℝ) * (incrementTail μ (a (k n))).toReal)
      atTop (𝓝 1) := ha.comp hkTop
  have hscaled := hk.div ha one_ne_zero
  have hraw := hscaled.div hkdiv hlam.ne'
  have heq : (fun n : ℕ =>
      (((k n : ℝ) * (incrementTail μ (a (k n))).toReal) /
        ((n : ℝ) * (incrementTail μ (a n)).toReal)) /
        ((k n : ℝ) / (n : ℝ))) =ᶠ[atTop]
      (fun n : ℕ => (incrementTail μ (a (k n))).toReal /
        (incrementTail μ (a n)).toReal) := by
    filter_upwards [hkTop.eventually_gt_atTop 0, eventually_gt_atTop (0 : ℕ)] with n hk0 hn0
    have hkR : (k n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk0.ne'
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0.ne'
    have hTk : (incrementTail μ (a (k n))).toReal ≠ 0 :=
      (ENNReal.toReal_pos (incrementTail_pos μ
        (hμ.to_literal) _).ne'
        (measure_ne_top _ _)).ne'
    have hTn : (incrementTail μ (a n)).toReal ≠ 0 :=
      (ENNReal.toReal_pos (incrementTail_pos μ
        (hμ.to_literal) _).ne'
        (measure_ne_top _ _)).ne'
    field_simp [hkR, hnR, hTk, hTn]
  simpa only [one_div, inv_div, div_one] using hraw.congr' heq

/-- The de Bruijn-conjugate ratio, proved by the regular-variation squeeze. -/
theorem uconseq_scaling_index_div
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun n : ℕ => a (Nat.floor (lam * (n : ℝ))) / a n) atTop (𝓝 lam) := by
  let k : ℕ → ℕ := fun n => Nat.floor (lam * (n : ℝ))
  have haTop := scaling_tendsto_atTop μ hμ.to_literal ha
  have hkTop : Tendsto k atTop atTop := uconseq_indexTop hlam
  have hakTop : Tendsto (a ∘ k) atTop atTop := haTop.comp hkTop
  have htail := uconseq_tail_index_div μ hμ a ha hlam
  change Tendsto (fun n : ℕ => a (k n) / a n) atTop (𝓝 lam)
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro d hd
    by_cases hd0 : 0 < d
    · have hd1 : 1 / lam < 1 / d := (one_div_lt_one_div_of_lt hd0 hd)
      let r := (1 / lam + 1 / d) / 2
      have hr₁ : 1 / lam < r := by dsimp [r]; linarith
      have hr₂ : r < 1 / d := by dsimp [r]; linarith
      have hfixed := uconseq_tail_const_mul_div μ hμ a haTop hd0
      by_contra hev
      have hfreq : ∃ᶠ n in atTop, a (k n) / a n ≤ d := by
        simpa only [not_lt] using not_eventually.mp hev
      obtain ⟨n, hnle, hpos, htailn, hfixedn⟩ := (hfreq.and_eventually
        (haTop.eventually_gt_atTop 0 |>.and
          (htail.eventually (Iio_mem_nhds hr₁) |>.and
            (hfixed.eventually (Ioi_mem_nhds hr₂))))).exists
      have huv : a (k n) ≤ d * a n := (div_le_iff₀ hpos).mp hnle
      have hmono : (incrementTail μ (d * a n)).toReal ≤
          (incrementTail μ (a (k n))).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) (incrementTail_antitone μ huv)
      have hTpos : 0 < (incrementTail μ (a n)).toReal :=
        ENNReal.toReal_pos (incrementTail_pos μ hμ.to_literal _).ne' (measure_ne_top _ _)
      have hle := (div_le_div_iff_of_pos_right hTpos).mpr hmono
      linarith
    · filter_upwards [haTop.eventually_gt_atTop 0, hakTop.eventually_gt_atTop 0]
        with n han hak
      have hratio : 0 < a (k n) / a n := div_pos hak han
      linarith
  · intro c hc
    have hc0 : 0 < c := hlam.trans hc
    have hcinv : 1 / c < 1 / lam := (one_div_lt_one_div_of_lt hlam hc)
    let r := (1 / lam + 1 / c) / 2
    have hr₁ : 1 / c < r := by dsimp [r]; linarith
    have hr₂ : r < 1 / lam := by dsimp [r]; linarith
    have hfixed := uconseq_tail_const_mul_div μ hμ a haTop hc0
    by_contra hev
    have hfreq : ∃ᶠ n in atTop, c ≤ a (k n) / a n := by
      simpa only [not_lt] using not_eventually.mp hev
    obtain ⟨n, hnle, hpos, htailn, hfixedn⟩ := (hfreq.and_eventually
      (haTop.eventually_gt_atTop 0 |>.and
        (htail.eventually (Ioi_mem_nhds hr₂) |>.and
          (hfixed.eventually (Iio_mem_nhds hr₁))))).exists
    have huv : c * a n ≤ a (k n) := (le_div_iff₀ hpos).mp hnle
    have hmono : (incrementTail μ (a (k n))).toReal ≤
        (incrementTail μ (c * a n)).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (incrementTail_antitone μ huv)
    have hTpos : 0 < (incrementTail μ (a n)).toReal :=
      ENNReal.toReal_pos (incrementTail_pos μ hμ.to_literal _).ne' (measure_ne_top _ _)
    have hle := (div_le_div_iff_of_pos_right hTpos).mpr hmono
    linarith


private theorem uconseq_list_le_second {α : Type*} [DecidableEq α]
    {l : List α} {f : α → ℕ} {x z : α} (hx : x ∈ l) (hz : z ∈ l)
    (hzx : z ≠ x) (hmax : f x = listMaxDegree (l.map f)) :
    f z ≤ listSecondMaxDegree (l.map f) := by
  classical
  by_cases hzmax : f z = f x
  · have hperm := (List.perm_cons_erase hx).map f
    have hzErase : z ∈ l.erase x := (List.mem_erase_of_ne hzx).mpr hz
    have hzmap : f z ∈ (l.erase x).map f := List.mem_map_of_mem hzErase
    have hp : (f x :: (l.erase x).map f).Perm (l.map f) := by
      simpa only [List.map_cons] using hperm.symm
    have hmaxlist : listMaxDegree (f x :: (l.erase x).map f) = f x :=
      (listMaxDegree_perm hp).trans hmax.symm
    rw [listSecondMaxDegree_perm hperm]
    simp only [List.map_cons]
    unfold listSecondMaxDegree
    rw [hmaxlist, List.erase_cons_head]
    exact Finset.le_sup (f := id) (List.mem_toFinset.mpr hzmap)
  · have hzmap : f z ∈ l.map f := List.mem_map_of_mem hz
    have hne : f z ≠ listMaxDegree (l.map f) := by simpa [hmax] using hzmax
    have herase : f z ∈ (l.map f).erase (listMaxDegree (l.map f)) :=
      (List.mem_erase_of_ne hne).mpr hzmap
    unfold listSecondMaxDegree listMaxDegree
    exact Finset.le_sup (f := id) (List.mem_toFinset.mpr herase)

/-- Every vertex other than the selected first maximum is bounded by the
second maximum, including when its degree ties the maximum. -/
theorem uconseq_degreeAt_le_secondMaxDegree_of_ne
    {t : BGW.PlaneTree} {v : List ℕ} (hv : t.IsVertex v)
    (hne : v ≠ maxDegreeVertex t) : degreeAt t v ≤ secondMaxDegree t := by
  have hx : maxDegreeVertex t ∈ t.vertices :=
    (BGW.PlaneTree.mem_vertices_iff _ _).mpr (maxDegreeVertex_isVertex t)
  have hz : v ∈ t.vertices := (BGW.PlaneTree.mem_vertices_iff _ _).mpr hv
  have hmax : degreeAt t (maxDegreeVertex t) =
      listMaxDegree (t.vertices.map (degreeAt t)) := by
    rw [degreeAt_maxDegreeVertex, maxDegree_eq_listMaxDegree, map_degreeAt_vertices]
  rw [secondMaxDegree, ← map_degreeAt_vertices]
  exact uconseq_list_le_second hx hz hne hmax

private theorem uconseq_mem_finiteTreeEvent {P : BGW.PlaneTree → Prop}
    {t : BGW.PlaneTree} : t.toLocallyFinite ∈ finiteTreeEvent P ↔ P t := by
  constructor
  · rintro ⟨s, hs, hst⟩
    have hst' : s = t := BGW.PlaneTree.toLocallyFinite_injective hst
    simpa only [hst', Set.mem_ofPred_eq] using hs
  · intro ht
    exact ⟨t, ht, rfl⟩

theorem uconseq_conditioned_not_eq_compl
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) (P : BGW.PlaneTree → Prop) :
    conditioned μ n (finiteTreeEvent fun t => ¬ P t) =
      conditioned μ n (finiteTreeEvent P)ᶜ := by
  classical
  have hnot : MeasurableSet (finiteTreeEvent fun t => ¬ P t) :=
    ((Set.to_countable {t : BGW.PlaneTree | ¬ P t}).image
      BGW.PlaneTree.toLocallyFinite).measurableSet
  have hP : MeasurableSet (finiteTreeEvent P) :=
    ((Set.to_countable {t : BGW.PlaneTree | P t}).image
      BGW.PlaneTree.toLocallyFinite).measurableSet
  rw [conditioned_apply_eq_tsum μ n _ hnot,
    conditioned_apply_eq_tsum μ n _ hP.compl]
  apply tsum_congr
  intro t
  by_cases ht : P t.1 <;> simp [uconseq_mem_finiteTreeEvent, ht]


/-- A bounded, strictly positive test function vanishing at `-∞`. -/
noncomputable def uconseqLogistic (x : ℝ) : ℝ := (1 + Real.exp (-x))⁻¹

theorem uconseqLogistic_pos (x : ℝ) : 0 < uconseqLogistic x := by
  unfold uconseqLogistic
  positivity

theorem uconseqLogistic_le_one (x : ℝ) : uconseqLogistic x ≤ 1 := by
  have h : (1 : ℝ) ≤ 1 + Real.exp (-x) := by nlinarith [Real.exp_nonneg (-x)]
  have hi := one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) h
  simpa only [one_div, inv_one, uconseqLogistic] using hi

theorem uconseqLogistic_continuous : Continuous uconseqLogistic := by
  unfold uconseqLogistic
  apply Continuous.inv₀
  · exact continuous_const.add (Real.continuous_exp.comp continuous_neg)
  · intro x
    exact (show (0 : ℝ) < 1 + Real.exp (-x) by positivity).ne'

theorem uconseqLogistic_tendsto_atBot :
    Tendsto uconseqLogistic atBot (𝓝 0) := by
  have hexp : Tendsto (fun x : ℝ => Real.exp (-x)) atBot atTop :=
    Real.tendsto_exp_atTop.comp tendsto_neg_atBot_atTop
  have hden := tendsto_atTop_add_const_right atBot 1 hexp
  apply hden.inv_tendsto_atTop.congr'
  filter_upwards [] with x
  simp only [uconseqLogistic, Pi.inv_apply]
  rw [add_comm]

theorem uconseqLogistic_mono : Monotone uconseqLogistic := by
  intro x y hxy
  have hd : 1 + Real.exp (-y) ≤ 1 + Real.exp (-x) := by
    nlinarith [Real.exp_le_exp.mpr (neg_le_neg hxy)]
  exact (inv_le_inv₀ (by positivity) (by positivity)).mpr hd

theorem uconseqLogistic_integral_pos
    (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    0 < ∫ x, uconseqLogistic x ∂ν := by
  have hint : Integrable uconseqLogistic ν :=
    Integrable.of_bound uconseqLogistic_continuous.aestronglyMeasurable 1
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (uconseqLogistic_pos x)]
        exact uconseqLogistic_le_one x)
  apply (integral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall fun x => (uconseqLogistic_pos x).le) hint).mpr
  have hsupp : Function.support uconseqLogistic = Set.univ := by
    ext x
    simp [Function.support, (uconseqLogistic_pos x).ne']
  rw [hsupp, measure_univ]
  exact zero_lt_one

end
end SubcriticalCauchy.Bienayme
