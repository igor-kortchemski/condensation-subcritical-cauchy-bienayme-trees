module

public import SubcriticalCauchy.StableKernel
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Calculus.Deriv.Inv

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


/-!
# Elementary analysis of the index-one stable kernel
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section

/-- The density in the positive-tail formula for `stableKernel`. -/
def stableKernelSlope (s u : ℝ) : ℝ :=
  if 0 < u then (if u < 1 then s * (1 - Real.exp (-s * u)) else -s * Real.exp (-s * u)) else 0

lemma stableKernelSlope_eq_deriv {s u : ℝ} (hu0 : 0 < u) (hu : u ≠ 1) :
    HasDerivAt (stableKernel s) (stableKernelSlope s u) u := by
  unfold stableKernel stableKernelSlope
  simp only [hu0, ite_true]
  by_cases h : u < 1
  · have he : HasDerivAt (fun x : ℝ => Real.exp (-s * x))
        (-s * Real.exp (-s * u)) u := by
      convert ((hasDerivAt_id u).const_mul (-s)).exp using 1 <;> simp [id]; ring
    have hi : HasDerivAt (fun x : ℝ => if x ≤ 1 then s * x else 0) s u := by
      have hh : HasDerivAt (fun x : ℝ => s * x) s u := by
        simpa using (hasDerivAt_id u).const_mul s
      apply hh.congr_of_eventuallyEq
      filter_upwards [eventually_lt_nhds h] with x hx
      simp [hx.le]
    convert (he.sub_const 1).add hi using 1; simp [h]; ring
  · have hu1 : 1 < u := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hu)
    have he : HasDerivAt (fun x : ℝ => Real.exp (-s * x))
        (-s * Real.exp (-s * u)) u := by
      convert ((hasDerivAt_id u).const_mul (-s)).exp using 1 <;> simp [id]; ring
    have hi : HasDerivAt (fun x : ℝ => if x ≤ 1 then s * x else 0) 0 u := by
      apply HasDerivAt.congr_of_eventuallyEq (hasDerivAt_const u (0 : ℝ))
      filter_upwards [eventually_gt_nhds hu1] with x hx
      simp [not_le.mpr hx]
    convert (he.sub_const 1).add hi using 1; simp [h]

lemma stableKernelSlope_nonpos_of_one_le {s u : ℝ} (_hs : 0 < s) (hu : 1 ≤ u) :
    stableKernelSlope s u = -s * Real.exp (-s * u) := by
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  simp [stableKernelSlope, hu0, not_lt.mpr hu]

lemma stableKernelSlope_nonneg_of_lt_one {s u : ℝ} (hs : 0 < s) (hu0 : 0 ≤ u)
    (hu : u < 1) : 0 ≤ stableKernelSlope s u := by
  by_cases hupos : 0 < u
  · simp only [stableKernelSlope, hupos, hu, ↓reduceIte]
    exact mul_nonneg hs.le (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by
      nlinarith [mul_nonneg hs.le hu0])))
  · have hu00 : u = 0 := le_antisymm (le_of_not_gt hupos) hu0
    subst u
    simp [stableKernelSlope]

lemma stableKernelSlope_abs_le {s u : ℝ} (hs : 0 < s) (hu : 0 < u) :
    |stableKernelSlope s u| ≤
      if u < 1 then s ^ 2 * u else s * Real.exp (-s * u) := by
  by_cases h : u < 1
  · simp only [h, hu, ↓reduceIte, stableKernelSlope]
    rw [abs_of_nonneg (mul_nonneg hs.le (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hs.le hu.le]))))]
    have he : 1 - Real.exp (-s * u) ≤ s * u := by
      have hh := Real.add_one_le_exp (-s * u)
      nlinarith
    have hh := mul_le_mul_of_nonneg_left he hs.le
    nlinarith [sq_nonneg s]
  · simp only [h, hu, ↓reduceIte, stableKernelSlope]
    rw [abs_mul, abs_neg, abs_of_pos hs, abs_of_pos (Real.exp_pos _)]



lemma measurable_stableKernelSlope (s : ℝ) : Measurable (stableKernelSlope s) := by
  unfold stableKernelSlope
  exact Measurable.ite measurableSet_Ioi
    (Measurable.ite measurableSet_Iio (by fun_prop) (by fun_prop)) measurable_const

/-- The positive and negative parts of the stable-kernel slope. -/
def stableKernelSlopePos (s u : ℝ) : ℝ :=
  (Set.Ioo 0 1).indicator (fun x => s * (1 - Real.exp (-s * x))) u

def stableKernelSlopeNeg (s u : ℝ) : ℝ :=
  (Set.Ici 1).indicator (fun x => s * Real.exp (-s * x)) u

lemma stableKernelSlope_eq_pos_sub_neg (s u : ℝ) :
    stableKernelSlope s u = stableKernelSlopePos s u - stableKernelSlopeNeg s u := by
  by_cases hu1 : u < 1
  · by_cases hu0 : 0 < u
    · have hn : ¬ 1 ≤ u := not_le.mpr hu1
      simp [stableKernelSlope, stableKernelSlopePos, stableKernelSlopeNeg, Set.indicator, hu1, hu0, hn]
    · have hn : ¬ 1 ≤ u := not_le.mpr hu1
      simp [stableKernelSlope, stableKernelSlopePos, stableKernelSlopeNeg, Set.indicator, hu1, hu0, hn]
  · have hu1' : 1 ≤ u := le_of_not_gt hu1
    have hu0 : 0 < u := zero_lt_one.trans_le hu1'
    simp [stableKernelSlope, stableKernelSlopePos, stableKernelSlopeNeg, Set.indicator, hu1, hu1', hu0]

lemma stableKernelSlopePos_nonneg {s u : ℝ} (hs : 0 < s) :
    0 ≤ stableKernelSlopePos s u := by
  simp only [stableKernelSlopePos, Set.indicator]
  split_ifs with h
  · exact mul_nonneg hs.le (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by
      have := mul_nonneg hs.le h.1.le
      nlinarith)))
  · exact le_rfl

lemma stableKernelSlopeNeg_nonneg {s u : ℝ} (hs : 0 < s) :
    0 ≤ stableKernelSlopeNeg s u := by
  simp only [stableKernelSlopeNeg, Set.indicator]
  split_ifs <;> positivity

lemma integrable_stableKernelSlopePos (s : ℝ) : Integrable (stableKernelSlopePos s) := by
  apply IntegrableOn.integrable_indicator (s := Set.Ioo (0 : ℝ) 1) _ measurableSet_Ioo
  exact (Continuous.continuousOn (by fun_prop :
    Continuous fun x : ℝ => s * (1 - Real.exp (-s * x)))).integrableOn_Icc.mono_set
      (Set.Ioo_subset_Icc_self)

lemma integrable_stableKernelSlopeNeg {s : ℝ} (hs : 0 < s) :
    Integrable (stableKernelSlopeNeg s) := by
  apply IntegrableOn.integrable_indicator (s := Set.Ici (1 : ℝ)) _ measurableSet_Ici
  have h := integrableOn_exp_mul_Ioi (a := -s) (by linarith) 1
  have hm : IntegrableOn (fun u : ℝ => s * Real.exp (-s * u)) (Set.Ioi 1) := h.const_mul s
  exact hm.congr_set_ae (MeasureTheory.Ioi_ae_eq_Ici (a := (1 : ℝ))).symm

/-- A real-integral version of the layer-cake formula for a nonnegative density.
The bounded-primitive hypothesis is immediate for compactly supported or exponentially
decaying densities and is kept explicit to make the conversion short. -/
lemma integral_primitive_tail_of_nonneg {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ} {g : ℝ → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hg : Integrable g)
    (hg0 : ∀ u, 0 ≤ g u) {B : ℝ}
    (hbound : ∀ x : ℝ, 0 ≤ x → |∫ t in 0..x, g t| ≤ B) :
    (∫ x, (∫ t in 0..f x, g t) ∂μ) =
      ∫ t in Set.Ioi 0, g t * μ.real {x | t ≤ f x} := by
  have hgIoi : IntegrableOn g (Set.Ioi 0) := hg.integrableOn
  have htail : Antitone (fun t : ℝ => μ.real {x | t ≤ f x}) := by
    intro a b hab
    exact measureReal_mono (fun x hx => hab.trans hx)
  have htail_meas : Measurable (fun t : ℝ => μ.real {x | t ≤ f x}) := htail.measurable
  have hprod : IntegrableOn (fun t => g t * μ.real {x | t ≤ f x}) (Set.Ioi 0) := by
    apply Integrable.mono' hgIoi
      ((hgIoi.aestronglyMeasurable.mul htail_meas.aestronglyMeasurable))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change |g t * μ.real {x | t ≤ f x}| ≤ g t
    rw [abs_of_nonneg (mul_nonneg (hg0 t) measureReal_nonneg)]
    calc
      g t * μ.real {x | t ≤ f x} ≤ g t * 1 :=
        mul_le_mul_of_nonneg_left measureReal_le_one (hg0 t)
      _ = g t := mul_one _
  have hprim_cont : Continuous (fun x : ℝ => ∫ t in 0..x, g t) := hg.continuous_primitive 0
  have hprim_comp : Integrable (fun x => ∫ t in 0..f x, g t) μ := by
    apply Integrable.of_bound (hprim_cont.measurable.comp hf).aestronglyMeasurable B
    exact Eventually.of_forall (fun x => hbound _ (hf0 x))
  have hprim_nonneg : ∀ x, 0 ≤ ∫ t in 0..f x, g t := by
    intro x
    rw [intervalIntegral.integral_of_le (hf0 x)]
    exact integral_nonneg_of_ae (Eventually.of_forall fun t => hg0 t)
  have hlayer := lintegral_comp_eq_lintegral_meas_le_mul μ
    (f := f) (g := g) (Eventually.of_forall hf0) hf.aemeasurable
    (fun _ _ => hg.intervalIntegrable) (Eventually.of_forall (fun _ => hg0 _))
  have hleft : ENNReal.ofReal (∫ x, (∫ t in 0..f x, g t) ∂μ) =
      ∫⁻ t in Set.Ioi 0, μ {x | t ≤ f x} * ENNReal.ofReal (g t) :=
    (ofReal_integral_eq_lintegral_ofReal hprim_comp
      (Eventually.of_forall hprim_nonneg)).trans hlayer
  have hright : ENNReal.ofReal (∫ t in Set.Ioi 0, g t * μ.real {x | t ≤ f x}) =
      ∫⁻ t in Set.Ioi 0, μ {x | t ≤ f x} * ENNReal.ofReal (g t) := by
    rw [ofReal_integral_eq_lintegral_ofReal hprod
      (Eventually.of_forall fun t => mul_nonneg (hg0 t) measureReal_nonneg)]
    apply lintegral_congr_ae
    filter_upwards [] with t
    rw [Measure.real, ENNReal.ofReal_mul (hg0 t), ENNReal.ofReal_toReal (measure_ne_top μ _),
      mul_comm]
  have hfin := congrArg ENNReal.toReal (hleft.trans hright.symm)
  have hL0 : 0 ≤ ∫ x, (∫ t in 0..f x, g t) ∂μ :=
    integral_nonneg_of_ae (Eventually.of_forall hprim_nonneg)
  have hR0 : 0 ≤ ∫ t in Set.Ioi 0, g t * μ.real {x | t ≤ f x} :=
    integral_nonneg_of_ae (Eventually.of_forall fun t => mul_nonneg (hg0 t) measureReal_nonneg)
  rw [ENNReal.toReal_ofReal hL0, ENNReal.toReal_ofReal hR0] at hfin
  exact hfin





lemma integrable_primitive_comp_of_nonneg {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ} {g : ℝ → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hg : Integrable g) {B : ℝ}
    (hbound : ∀ x : ℝ, 0 ≤ x → |∫ t in 0..x, g t| ≤ B) :
    Integrable (fun x => ∫ t in 0..f x, g t) μ := by
  have hcont : Continuous (fun x : ℝ => ∫ t in 0..x, g t) := hg.continuous_primitive 0
  exact Integrable.of_bound (hcont.measurable.comp hf).aestronglyMeasurable B
    (Eventually.of_forall (fun x => hbound _ (hf0 x)))

lemma integrableOn_mul_measureReal_tail_of_nonneg {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ} {g : ℝ → ℝ}
    (_hf : Measurable f) (hg : IntegrableOn g (Set.Ioi 0)) (hg0 : ∀ u, 0 ≤ g u) :
    IntegrableOn (fun t => g t * μ.real {x | t ≤ f x}) (Set.Ioi 0) := by
  have htail : Antitone (fun t : ℝ => μ.real {x | t ≤ f x}) := by
    intro a b hab
    exact measureReal_mono (fun x hx => hab.trans hx)
  apply Integrable.mono' hg
    (hg.aestronglyMeasurable.mul htail.measurable.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change |g t * μ.real {x | t ≤ f x}| ≤ g t
  rw [abs_of_nonneg (mul_nonneg (hg0 t) measureReal_nonneg)]
  simpa only [mul_one] using
    (mul_le_mul_of_nonneg_left (measureReal_le_one (μ := μ)
      (s := {x | t ≤ f x})) (hg0 t))



lemma abs_intervalIntegral_le_integral_of_nonneg {g : ℝ → ℝ}
    (hg : Integrable g) (hg0 : ∀ u, 0 ≤ g u) {x : ℝ} (hx : 0 ≤ x) :
    |∫ t in 0..x, g t| ≤ ∫ t, g t := by
  have hn : 0 ≤ ∫ t in 0..x, g t := by
    rw [intervalIntegral.integral_of_le hx]
    exact integral_nonneg_of_ae (Eventually.of_forall hg0)
  rw [abs_of_nonneg hn, intervalIntegral.integral_of_le hx]
  exact setIntegral_le_integral hg (Eventually.of_forall hg0)

lemma continuousOn_stableKernel_Iic_one (s : ℝ) :
    ContinuousOn (stableKernel s) (Set.Iic 1) := by
  apply ContinuousOn.congr (by fun_prop : ContinuousOn
    (fun x : ℝ => Real.exp (-s * x) - 1 + s * x) (Set.Iic 1))
  intro x hx
  change x ≤ 1 at hx
  simp [stableKernel, hx]

lemma integral_stableKernelSlope_zero_to_le_one {s x : ℝ} (hs : 0 < s) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (∫ t in 0..x, stableKernelSlope s t) = stableKernel s x := by
  have hderiv : ∀ y ∈ Set.Ioo 0 x, HasDerivAt (stableKernel s) (stableKernelSlope s y) y := by
    intro y hy
    exact stableKernelSlope_eq_deriv hy.1 (by linarith [hy.2])
  have hint : IntervalIntegrable (stableKernelSlope s) volume 0 x :=
    ((integrable_stableKernelSlopePos s).sub
      (integrable_stableKernelSlopeNeg hs)).intervalIntegrable.congr (fun y hy =>
        (stableKernelSlope_eq_pos_sub_neg s y).symm)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx0
    ((continuousOn_stableKernel_Iic_one s).mono (Set.Icc_subset_Iic_self.trans
      (Set.Iic_subset_Iic.mpr hx1))) hderiv hint
  simpa [stableKernel] using h

lemma integral_stableKernelSlope_one_to {s x : ℝ} (hs : 0 < s) (hx : 1 ≤ x) :
    (∫ t in 1..x, stableKernelSlope s t) = Real.exp (-s * x) - Real.exp (-s) := by
  let G : ℝ → ℝ := fun y => Real.exp (-s * y) - 1
  have hderiv : ∀ y ∈ Set.Ioo 1 x, HasDerivAt G (stableKernelSlope s y) y := by
    intro y hy
    have hd := stableKernelSlope_eq_deriv (s := s) (lt_trans zero_lt_one hy.1) (by linarith [hy.1])
    apply hd.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hy.1] with z hz
    simp [G, stableKernel, not_le.mpr hz]
  have hint : IntervalIntegrable (stableKernelSlope s) volume 1 x :=
    ((integrable_stableKernelSlopePos s).sub
      (integrable_stableKernelSlopeNeg hs)).intervalIntegrable.congr (fun y hy =>
        (stableKernelSlope_eq_pos_sub_neg s y).symm)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx
    (by fun_prop : ContinuousOn G (Set.Icc 1 x)) hderiv hint
  simpa [G] using h

lemma integral_stableKernelSlope_zero_to {s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x) :
    (∫ t in 0..x, stableKernelSlope s t) = stableKernel s x + if 1 < x then s else 0 := by
  by_cases hx1 : x ≤ 1
  · simp [hx1, integral_stableKernelSlope_zero_to_le_one hs hx hx1]
  · have hx1' : 1 < x := lt_of_not_ge hx1
    have h01 : IntervalIntegrable (stableKernelSlope s) volume 0 1 :=
      ((integrable_stableKernelSlopePos s).sub
        (integrable_stableKernelSlopeNeg hs)).intervalIntegrable.congr (fun y hy =>
          (stableKernelSlope_eq_pos_sub_neg s y).symm)
    have h1x : IntervalIntegrable (stableKernelSlope s) volume 1 x :=
      ((integrable_stableKernelSlopePos s).sub
        (integrable_stableKernelSlopeNeg hs)).intervalIntegrable.congr (fun y hy =>
          (stableKernelSlope_eq_pos_sub_neg s y).symm)
    rw [← intervalIntegral.integral_add_adjacent_intervals h01 h1x,
      integral_stableKernelSlope_zero_to_le_one hs zero_le_one le_rfl,
      integral_stableKernelSlope_one_to hs hx1'.le]
    simp [stableKernel, hx1', not_le.mpr hx1']
    ring

lemma stableKernel_eq_primitive_pos_sub_neg (s x : ℝ) (hs : 0 < s) (hx : 0 ≤ x) :
    stableKernel s x = (∫ t in 0..x, stableKernelSlopePos s t) -
      (∫ t in 0..x, stableKernelSlopeNeg s t) - if 1 < x then s else 0 := by
  rw [← intervalIntegral.integral_sub
    ((integrable_stableKernelSlopePos s).intervalIntegrable)
    ((integrable_stableKernelSlopeNeg hs).intervalIntegrable)]
  have heq : (fun t => stableKernelSlopePos s t - stableKernelSlopeNeg s t) =
      stableKernelSlope s := by
    funext t
    exact (stableKernelSlope_eq_pos_sub_neg s t).symm
  rw [heq, integral_stableKernelSlope_zero_to hs hx]
  ring

lemma stableKernelSlopePos_le_sq {s u : ℝ} (hs : 0 < s) (hu : 0 < u) :
    stableKernelSlopePos s u ≤ s ^ 2 * u := by
  by_cases hu1 : u < 1
  · rw [show stableKernelSlopePos s u = stableKernelSlope s u by
      simp [stableKernelSlopePos, stableKernelSlope, hu, hu1, Set.indicator]]
    exact (le_abs_self _).trans (stableKernelSlope_abs_le hs hu |>.trans_eq (by simp only [hu1, ↓reduceIte]))
  · simp [stableKernelSlopePos, Set.indicator, hu1]
    positivity

lemma stableKernelSlopePos_primitive_le_sq {s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x) :
    |∫ t in 0..x, stableKernelSlopePos s t| ≤ s ^ 2 * x ^ 2 := by
  have hnonneg : 0 ≤ ∫ t in 0..x, stableKernelSlopePos s t := by
    rw [intervalIntegral.integral_of_le hx]
    exact integral_nonneg_of_ae (Eventually.of_forall fun _ => stableKernelSlopePos_nonneg hs)
  rw [abs_of_nonneg hnonneg, intervalIntegral.integral_of_le hx]
  have hg : IntegrableOn (stableKernelSlopePos s) (Set.Ioc 0 x) :=
    (integrable_stableKernelSlopePos s).integrableOn
  have hc : IntegrableOn (fun _ : ℝ => s ^ 2 * x) (Set.Ioc 0 x) := (continuousOn_const).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  calc
    (∫ t in Set.Ioc 0 x, stableKernelSlopePos s t)
        ≤ ∫ _t in Set.Ioc 0 x, s ^ 2 * x := by
      apply setIntegral_mono_on hg hc measurableSet_Ioc
      intro u hu
      exact (stableKernelSlopePos_le_sq hs hu.1).trans
        (mul_le_mul_of_nonneg_left hu.2 (sq_nonneg s))
    _ = s ^ 2 * x ^ 2 := by simp [max_eq_left hx]; ring

lemma stableKernelSlopeNeg_primitive_eq_zero {s x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (∫ t in 0..x, stableKernelSlopeNeg s t) = 0 := by
  rw [intervalIntegral.integral_of_le hx0]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae (Measure.ae_ne volume (1 : ℝ))] with u hu huOne
  have hu1 : u < 1 := lt_of_le_of_ne (hu.2.trans hx1) huOne
  simp [stableKernelSlopeNeg, Set.indicator, not_le.mpr hu1]

/-- Real layer-cake conversion for a possibly infinite base measure, with the
integrability and finiteness conditions isolated. -/
lemma integral_primitive_tail_general {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {f : α → ℝ} {g : ℝ → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hg : Integrable g)
    (hg0 : ∀ u, 0 ≤ g u)
    (hprim : Integrable (fun x => ∫ t in 0..f x, g t) μ)
    (hprod : IntegrableOn (fun t => g t * μ.real {x | t ≤ f x}) (Set.Ioi 0))
    (hfin : ∀ t : ℝ, 0 < t → 0 < g t → μ {x | t ≤ f x} ≠ ⊤) :
    (∫ x, (∫ t in 0..f x, g t) ∂μ) =
      ∫ t in Set.Ioi 0, g t * μ.real {x | t ≤ f x} := by
  have hprim_nonneg : ∀ x, 0 ≤ ∫ t in 0..f x, g t := by
    intro x
    rw [intervalIntegral.integral_of_le (hf0 x)]
    exact integral_nonneg_of_ae (Eventually.of_forall fun t => hg0 t)
  have hlayer := lintegral_comp_eq_lintegral_meas_le_mul μ
    (f := f) (g := g) (Eventually.of_forall hf0) hf.aemeasurable
    (fun _ _ => hg.intervalIntegrable) (Eventually.of_forall (fun _ => hg0 _))
  have hleft : ENNReal.ofReal (∫ x, (∫ t in 0..f x, g t) ∂μ) =
      ∫⁻ t in Set.Ioi 0, μ {x | t ≤ f x} * ENNReal.ofReal (g t) :=
    (ofReal_integral_eq_lintegral_ofReal hprim
      (Eventually.of_forall hprim_nonneg)).trans hlayer
  have hright : ENNReal.ofReal (∫ t in Set.Ioi 0, g t * μ.real {x | t ≤ f x}) =
      ∫⁻ t in Set.Ioi 0, μ {x | t ≤ f x} * ENNReal.ofReal (g t) := by
    rw [ofReal_integral_eq_lintegral_ofReal hprod
      (Eventually.of_forall fun t => mul_nonneg (hg0 t) measureReal_nonneg)]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    by_cases hgzero : g t = 0
    · simp [hgzero]
    · have htg : 0 < g t := lt_of_le_of_ne (hg0 t) (Ne.symm hgzero)
      rw [Measure.real, ENNReal.ofReal_mul (hg0 t), ENNReal.ofReal_toReal (hfin t ht htg), mul_comm]
  have hfin' := congrArg ENNReal.toReal (hleft.trans hright.symm)
  have hL0 : 0 ≤ ∫ x, (∫ t in 0..f x, g t) ∂μ :=
    integral_nonneg_of_ae (Eventually.of_forall hprim_nonneg)
  have hR0 : 0 ≤ ∫ t in Set.Ioi 0, g t * μ.real {x | t ≤ f x} :=
    integral_nonneg_of_ae (Eventually.of_forall fun t => mul_nonneg (hg0 t) measureReal_nonneg)
  rw [ENNReal.toReal_ofReal hL0, ENNReal.toReal_ofReal hR0] at hfin'
  exact hfin'

lemma oneStep_inv_sq_tail {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x : ℝ => 1 / x ^ 2) (Ici t) ∧
    (∫ x in Ici t, 1 / x ^ 2) = 1 / t := by
  have heq : (fun x : ℝ => x ^ (-2 : ℝ)) = (fun x : ℝ => 1 / x ^ 2) := by
    funext x
    simp
  constructor
  · rw [← heq]
    exact (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ht).congr_set_ae Ioi_ae_eq_Ici.symm
  · rw [integral_Ici_eq_integral_Ioi, ← heq, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ht]
    norm_num [Real.rpow_neg_one]

lemma oneStep_primitive_div_sq {g : ℝ → ℝ}
    (hgm : Measurable g) (hg0 : ∀ t, 0 ≤ g t)
    (hgd : IntegrableOn (fun t => g t / t) (Ioi 0)) :
    IntegrableOn (fun x => (∫ t in 0..x, g t) / x ^ 2) (Ioi 0) ∧
    (∫ x in Ioi 0, (∫ t in 0..x, g t) / x ^ 2) =
      ∫ t in Ioi 0, g t / t := by
  let Q : ℝ × ℝ → ℝ := fun p => if p.2 ≤ p.1 then g p.2 / p.1 ^ 2 else 0
  let v := volume.restrict (Ioi (0 : ℝ))
  have hQm : Measurable Q := by
    exact ((hgm.comp measurable_snd).div (measurable_fst.pow_const 2)).ite
      (measurableSet_le measurable_snd measurable_fst) measurable_const
  have hQ0 : ∀ p, 0 ≤ Q p := fun p => by dsimp [Q]; split_ifs; exact div_nonneg (hg0 _) (sq_nonneg _); exact le_rfl
  have hinner : ∀ t, 0 < t → Integrable (fun x => Q (x,t)) v ∧
      (∫ x, Q (x,t) ∂v) = g t / t := by
    intro t ht
    have hi := (oneStep_inv_sq_tail ht).1.const_mul (g t)
    have hfun : (fun x => Q (x,t)) = (Ici t).indicator (fun x => g t * (1 / x ^ 2)) := by
      funext x; simp [Q, Set.indicator, div_eq_mul_inv]
    have hs : Ioi (0 : ℝ) ∩ Ici t = Ici t := by
      ext x
      simp only [mem_inter_iff, mem_Ioi, mem_Ici]
      constructor
      · exact And.right
      · intro h; exact ⟨ht.trans_le h, h⟩
    rw [hfun]
    constructor
    · exact (IntegrableOn.integrable_indicator hi measurableSet_Ici).integrableOn
    · rw [setIntegral_indicator measurableSet_Ici, hs, integral_const_mul,
        (oneStep_inv_sq_tail ht).2]
      ring
  have hQi : Integrable Q (v.prod v) := by
    apply (integrable_prod_iff' hQm.aestronglyMeasurable).mpr
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (hinner t ht).1
    · apply hgd.congr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      dsimp
      rw [show (fun x => |Q (x,t)|) = (fun x => Q (x,t)) by
        funext x; exact abs_of_nonneg (hQ0 _)]
      exact (hinner t ht).2.symm
  have hother : ∀ x, 0 < x → (∫ t, Q (x,t) ∂v) = (∫ t in 0..x, g t) / x ^ 2 := by
    intro x hx
    have hfun : (fun t => Q (x,t)) = (Iic x).indicator (fun t => g t / x ^ 2) := by
      funext t; simp [Q, Set.indicator]
    rw [hfun, setIntegral_indicator measurableSet_Iic]
    have hs : Ioi (0 : ℝ) ∩ Iic x = Ioc 0 x := by ext t; rfl
    rw [hs, integral_div, intervalIntegral.integral_of_le hx.le]
  constructor
  · exact hQi.integral_prod_left.congr (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact hother x hx)
  · calc
      _ = ∫ x, ∫ t, Q (x,t) ∂v ∂v := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact (hother x hx).symm
      _ = ∫ t, ∫ x, Q (x,t) ∂v ∂v := integral_integral_swap hQi
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact (hinner t ht).2

/-- Integrability of the limiting positive-slope tail integrand. -/
lemma oneStep_slopePos_div_integrable {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun u => stableKernelSlopePos s u / u) (Ioi 0) := by
  have hc : Integrable ((Ioo (0 : ℝ) 1).indicator (fun _ => s ^ 2)) :=
    ((continuousOn_const : ContinuousOn (fun _ : ℝ => s ^ 2) (Icc 0 1)).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self).integrable_indicator measurableSet_Ioo
  apply hc.integrableOn.mono'
    (((Measurable.indicator (by fun_prop) measurableSet_Ioo).div measurable_id).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  change |stableKernelSlopePos s u / u| ≤ _
  rw [abs_of_nonneg (div_nonneg (stableKernelSlopePos_nonneg hs) hu.le)]
  by_cases hu1 : u < 1
  · rw [indicator_of_mem (show u ∈ Ioo (0 : ℝ) 1 from ⟨hu, hu1⟩)]
    exact (div_le_iff₀ hu).mpr (by simpa [mul_comm] using stableKernelSlopePos_le_sq hs hu)
  · simp [stableKernelSlopePos, Set.indicator, hu1]

lemma oneStep_slopeNeg_div_integrable {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun u => stableKernelSlopeNeg s u / u) (Ioi 0) := by
  apply (integrable_stableKernelSlopeNeg hs).integrableOn.mono'
    (((Measurable.indicator (by fun_prop) measurableSet_Ici).div measurable_id).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  change |stableKernelSlopeNeg s u / u| ≤ _
  rw [abs_of_nonneg (div_nonneg (stableKernelSlopeNeg_nonneg hs) hu.le)]
  by_cases hu1 : 1 ≤ u
  · exact div_le_self (stableKernelSlopeNeg_nonneg hs) hu1
  · simp [stableKernelSlopeNeg, Set.indicator, hu1]

/-- Direct layer cake against `x⁻² dx`; the explicit term records the jump at one. -/
lemma oneStep_stableKernelIntegral_layercake {s : ℝ} (hs : 0 < s) :
    stableKernelIntegral s =
      (∫ u in Ioi 0, stableKernelSlopePos s u * (1 / u)) -
      (∫ u in Ioi 0, stableKernelSlopeNeg s u * (1 / u)) - s := by
  have hp := oneStep_primitive_div_sq (g := stableKernelSlopePos s)
    (Measurable.indicator (by fun_prop) measurableSet_Ioo)
    (fun _ => stableKernelSlopePos_nonneg hs) (oneStep_slopePos_div_integrable hs)
  have hn := oneStep_primitive_div_sq (g := stableKernelSlopeNeg s)
    (Measurable.indicator (by fun_prop) measurableSet_Ici)
    (fun _ => stableKernelSlopeNeg_nonneg hs) (oneStep_slopeNeg_div_integrable hs)
  have hj : IntegrableOn (fun x : ℝ => (if 1 < x then s else 0) / x ^ 2) (Ioi 0) := by
    have hi := IntegrableOn.integrable_indicator ((oneStep_inv_sq_tail zero_lt_one).1.const_mul s) measurableSet_Ici
    apply hi.integrableOn.congr
    filter_upwards [ae_restrict_of_ae (Measure.ae_ne volume (1 : ℝ))] with x hx
    by_cases h : 1 < x
    · simp [Set.indicator, h.le, h, div_eq_mul_inv]
    · have h' : ¬ 1 ≤ x := by grind
      simp [Set.indicator, h', h]
  have hjval : (∫ x in Ioi 0, (if 1 < x then s else 0) / x ^ 2) = s := by
    calc
      _ = ∫ x in Ioi 0, (Ioi (1 : ℝ)).indicator (fun x => s * (1 / x ^ 2)) x := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          by_cases h : 1 < x <;> simp [Set.indicator, h, div_eq_mul_inv]
      _ = ∫ x in Ioi 1, s * (1 / x ^ 2) := by
        rw [setIntegral_indicator measurableSet_Ioi]
        have hset : Ioi (0 : ℝ) ∩ Ioi 1 = Ioi 1 := by
          ext x
          simp only [mem_inter_iff, mem_Ioi]
          constructor
          · exact And.right
          · intro hx; exact ⟨zero_lt_one.trans hx, hx⟩
        rw [hset]
      _ = s := by
        rw [integral_const_mul, ← integral_Ici_eq_integral_Ioi, (oneStep_inv_sq_tail zero_lt_one).2]
        simp
  unfold stableKernelIntegral
  calc
    _ = ∫ x in Ioi 0,
        ((∫ t in 0..x, stableKernelSlopePos s t) / x ^ 2 -
        (∫ t in 0..x, stableKernelSlopeNeg s t) / x ^ 2) -
        (if 1 < x then s else 0) / x ^ 2 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [stableKernel_eq_primitive_pos_sub_neg s x hs hx.le]
      ring
    _ = _ := by
      have hsub := integral_sub (Integrable.sub hp.1 hn.1) hj
      simp only [Pi.sub_apply] at hsub
      rw [hsub, integral_sub hp.1 hn.1, hp.2, hn.2, hjval]
      simp only [div_eq_mul_inv, one_mul]

end
end SubcriticalCauchy.Bienayme
