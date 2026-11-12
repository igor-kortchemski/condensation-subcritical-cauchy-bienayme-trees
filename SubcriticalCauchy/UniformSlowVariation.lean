module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Measurable uniform slow variation: additive sequential foundation

The arguments use the original pointwise values of the a.e. measurable
function. Translation invariance of outer Lebesgue measure permits choosing a
point outside two small bad sets without replacing the function by a Borel
representative. The exponential nonsingularity lemma transports Lebesgue
measurability on the positive half-line to the logarithmic parametrization.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace SubcriticalCauchy

/-- A measurable function whose increment at every fixed shift vanishes also
has vanishing increments at shifts tending to zero along any diverging base
sequence. This is the sequential additive uniform-convergence theorem. -/
theorem additive_uniform_sequential {f : ℝ → ℝ}
    (hf : AEMeasurable f (volume : Measure ℝ))
    (hfixed : ∀ c : ℝ, Tendsto (fun x => f (x + c) - f x) atTop (𝓝 0))
    {x h : ℕ → ℝ} (hx : Tendsto x atTop atTop) (hh : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => f (x n + h n) - f (x n)) atTop (𝓝 0) := by
  classical
  let J : Set ℝ := Icc (-2) 2
  let ν : Measure ℝ := volume.restrict J
  have : IsFiniteMeasure ν := inferInstanceAs
    (IsFiniteMeasure (volume.restrict (Icc (-2 : ℝ) 2)))
  let F (n : ℕ) (t : ℝ) := f (x n + t) - f (x n)
  let G (n : ℕ) (t : ℝ) := f (x n + h n + t) - f (x n + h n)
  have hy : Tendsto (fun n => x n + h n) atTop atTop := hx.atTop_add hh
  have hFmeas (n : ℕ) : AEMeasurable (F n) (volume : Measure ℝ) :=
    (hf.comp_quasiMeasurePreserving
      (measurePreserving_add_left (volume : Measure ℝ) (x n)).quasiMeasurePreserving).sub
        aemeasurable_const
  have hGmeas (n : ℕ) : AEMeasurable (G n) (volume : Measure ℝ) :=
    (hf.comp_quasiMeasurePreserving
      (measurePreserving_add_left (volume : Measure ℝ) (x n + h n)).quasiMeasurePreserving).sub
        aemeasurable_const
  have hFpoint (t : ℝ) : Tendsto (fun n => F n t) atTop (𝓝 0) := (hfixed t).comp hx
  have hGpoint (t : ℝ) : Tendsto (fun n => G n t) atTop (𝓝 0) := (hfixed t).comp hy
  have hFprob : TendstoInMeasure ν F atTop (fun _ => 0) :=
    tendstoInMeasure_of_tendsto_ae
      (fun n => ((hFmeas n).mono_measure Measure.restrict_le_self).aestronglyMeasurable)
      (Eventually.of_forall hFpoint)
  have hGprob : TendstoInMeasure ν G atTop (fun _ => 0) :=
    tendstoInMeasure_of_tendsto_ae
      (fun n => ((hGmeas n).mono_measure Measure.restrict_le_self).aestronglyMeasurable)
      (Eventually.of_forall hGpoint)
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  let BF (n : ℕ) : Set ℝ := {t | ε / 2 ≤ |F n t|} ∩ J
  let BG (n : ℕ) : Set ℝ := {t | ε / 2 ≤ |G n t|} ∩ J
  have hFbad : Tendsto (fun n => volume (BF n)) atTop (𝓝 0) := by
    have hp := (tendstoInMeasure_iff_norm.mp hFprob) (ε / 2) (half_pos hε)
    simpa only [ν, BF, J, Measure.restrict_apply' measurableSet_Icc, sub_zero,
      Real.norm_eq_abs] using hp
  have hGbad : Tendsto (fun n => volume (BG n)) atTop (𝓝 0) := by
    have hp := (tendstoInMeasure_iff_norm.mp hGprob) (ε / 2) (half_pos hε)
    simpa only [ν, BG, J, Measure.restrict_apply' measurableSet_Icc, sub_zero,
      Real.norm_eq_abs] using hp
  have hquarter : (0 : ℝ≥0∞) < 1 / 4 := by norm_num
  have hsmallh : ∀ᶠ n in atTop, |h n| < (1 / 4 : ℝ) :=
    hh.abs.eventually (gt_mem_nhds (by norm_num : |(0 : ℝ)| < 1 / 4))
  filter_upwards [hFbad.eventually (gt_mem_nhds hquarter),
    hGbad.eventually (gt_mem_nhds hquarter), hsmallh] with n hFn hGn hhn
  let B : Set ℝ := BF n ∪ (fun t : ℝ => t - h n) ⁻¹' BG n
  have htranslate : volume ((fun t : ℝ => t - h n) ⁻¹' BG n) = volume (BG n) := by
    simpa only [sub_eq_add_neg] using
      measure_preimage_add_right (volume : Measure ℝ) (-h n) (BG n)
  have hB : volume B < 1 := by
    calc
      volume B ≤ volume (BF n) + volume ((fun t : ℝ => t - h n) ⁻¹' BG n) :=
        measure_union_le _ _
      _ = volume (BF n) + volume (BG n) := by rw [htranslate]
      _ ≤ (1 / 4 : ℝ≥0∞) + 1 / 4 := add_le_add hFn.le hGn.le
      _ < 1 := by
        simp only [div_eq_mul_inv, one_mul]
        rw [← two_mul, ← div_eq_mul_inv,
          ENNReal.div_lt_iff (by simp) (by simp)]
        norm_num
  have hnot : ¬ Icc (0 : ℝ) 1 ⊆ B := by
    intro hsub
    have hle : volume (Icc (0 : ℝ) 1) ≤ volume B := measure_mono hsub
    have hone : volume (Icc (0 : ℝ) 1) = (1 : ℝ≥0∞) := by simp
    rw [hone] at hle
    exact (not_le.mpr hB) hle
  obtain ⟨t, ht, htBad⟩ := Set.not_subset.mp hnot
  have htJ : t ∈ J := by
    constructor <;> linarith [ht.1, ht.2]
  have huJ : t - h n ∈ J := by
    obtain ⟨hl, hu⟩ := abs_lt.mp hhn
    constructor <;> linarith [ht.1, ht.2]
  simp only [B, BF, BG, Set.mem_union, Set.mem_inter_iff, Set.mem_preimage,
    Set.mem_ofPred_eq] at htBad
  have hFlt : |F n t| < ε / 2 := by
    apply lt_of_not_ge
    intro hbad
    exact htBad (Or.inl ⟨hbad, htJ⟩)
  have hGlt : |G n (t - h n)| < ε / 2 := by
    apply lt_of_not_ge
    intro hbad
    exact htBad (Or.inr ⟨hbad, huJ⟩)
  have hvalue : f (x n + h n) - f (x n) = F n t - G n (t - h n) := by
    dsimp only [F, G]
    have harg : x n + h n + (t - h n) = x n + t := by ring
    rw [harg]
    ring
  rw [Real.dist_eq, sub_zero, hvalue]
  calc
    |F n t - G n (t - h n)| ≤ |F n t| + |G n (t - h n)| := abs_sub _ _
    _ < ε / 2 + ε / 2 := add_lt_add hFlt hGlt
    _ = ε := by ring

/-- The exponential sends Lebesgue measure nonsingularly to the positive
half-line with its restricted Lebesgue measure. It transports null sets by the
differentiable logarithmic inverse, without choosing a representative of `L`. -/
theorem quasiMeasurePreserving_exp_positive :
    QuasiMeasurePreserving Real.exp (volume : Measure ℝ) (volume.restrict (Ioi 0)) := by
  refine ⟨Real.measurable_exp, Measure.AbsolutelyContinuous.mk ?_⟩
  intro A hA hnull
  rw [Measure.map_apply Real.measurable_exp hA]
  have hnull' : volume (A ∩ Ioi 0) = (0 : ℝ≥0∞) := by
    simpa only [Measure.restrict_apply' measurableSet_Ioi] using hnull
  have hpre : Real.exp ⁻¹' A = Real.log '' (A ∩ Ioi 0) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_inter_iff, Set.mem_Ioi]
    constructor
    · intro hy
      exact ⟨Real.exp y, ⟨hy, Real.exp_pos y⟩, Real.log_exp y⟩
    · rintro ⟨z, ⟨hzA, hzpos⟩, hzy⟩
      rw [← hzy, Real.exp_log hzpos]
      exact hzA
  rw [hpre]
  exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    (volume : Measure ℝ)
    (fun z hz => (Real.differentiableAt_log (ne_of_gt hz.2)).differentiableWithinAt) hnull'

theorem aemeasurable_log_exp_transform {L : ℝ → ℝ}
    (hL : AEMeasurable L (volume.restrict (Ioi 0))) :
    AEMeasurable (fun x => Real.log (L (Real.exp x))) (volume : Measure ℝ) :=
  Real.measurable_log.comp_aemeasurable
    (hL.comp_quasiMeasurePreserving quasiMeasurePreserving_exp_positive)

end SubcriticalCauchy
