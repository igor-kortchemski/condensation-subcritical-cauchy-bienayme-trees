module

public import SubcriticalCauchy.CauchyOneLaw
public import Mathlib.Probability.Moments.ComplexMGF
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Analytic continuation of negative Laplace transforms

The continuation and boundary arguments are ported from
`scratch/bgw-ref/LimitLaw.lean` (BGW-formalization, same author, Apache 2.0),
with exponent `(-z) * Complex.log (-z)` for the index-one law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set Complex
open scoped Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section

/-- The explicit characteristic function of the paper's law `𝒞₁`. -/
noncomputable def cauchyOneCF (t : ℝ) : ℂ :=
  Complex.exp (-((Real.pi / 2 * |t| : ℝ) : ℂ) -
    (t * Real.log |t| : ℝ) * Complex.I)

private lemma Iio_subset_interior_integrableExpSet_of_laplace {ν : Measure ℝ}
    (hint : ∀ s : ℝ, 0 < s → Integrable (fun x => Real.exp (-s * x)) ν) :
    Set.Iio (0 : ℝ) ⊆ interior (integrableExpSet id ν) := by
  apply interior_maximal _ isOpen_Iio
  intro t ht
  have h := hint (-t) (by simpa using ht)
  simpa [integrableExpSet] using h

/-- On the open left half-plane, equal negative Laplace transforms give equal complex MGFs. -/
private lemma complexMGF_eq_of_laplace {μ ν : Measure ℝ}
    (hintμ : ∀ s : ℝ, 0 < s → Integrable (fun x => Real.exp (-s * x)) μ)
    (hintν : ∀ s : ℝ, 0 < s → Integrable (fun x => Real.exp (-s * x)) ν)
    (hL : ∀ s : ℝ, 0 < s →
      (∫ x, Real.exp (-s * x) ∂μ) = ∫ x, Real.exp (-s * x) ∂ν)
    {z : ℂ} (hz : z.re < 0) :
    complexMGF id μ z = complexMGF id ν z := by
  let U : Set ℂ := {z | z.re < 0}
  have hU : IsPreconnected U := (convex_halfSpace_re_lt 0).isPreconnected
  have hf : AnalyticOnNhd ℂ (complexMGF id μ) U := by
    intro w hw
    exact analyticAt_complexMGF (Iio_subset_interior_integrableExpSet_of_laplace hintμ hw)
  have hg : AnalyticOnNhd ℂ (complexMGF id ν) U := by
    intro w hw
    exact analyticAt_complexMGF (Iio_subset_interior_integrableExpSet_of_laplace hintν hw)
  have hmem : (-1 : ℂ) ∈ U := by simp [U]
  have hfreq : ∃ᶠ w in 𝓝[≠] (-1 : ℂ), complexMGF id μ w = complexMGF id ν w := by
    have ht : Tendsto (fun n : ℕ => ((-1 + 1 / ((n : ℝ) + 2) : ℝ) : ℂ)) atTop
        (𝓝[≠] (-1 : ℂ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have h : Tendsto (fun n : ℕ => (-1 + 1 / ((n : ℝ) + 2) : ℝ)) atTop
            (𝓝 (-1 + 0)) := by
          apply Tendsto.add tendsto_const_nhds
          apply Tendsto.div_atTop tendsto_const_nhds
          exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
        rw [add_zero] at h
        simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto _).comp h
      · refine Eventually.of_forall fun n => ?_
        simp only [mem_compl_iff, mem_singleton_iff]
        intro h
        have h2 : (-1 + 1 / ((n : ℝ) + 2) : ℝ) = -1 := by exact_mod_cast h
        have h3 : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
        linarith
    apply ht.frequently
    refine Frequently.of_forall fun n => ?_
    let t : ℝ := -1 + 1 / ((n : ℝ) + 2)
    have htneg : t < 0 := by
      have h : 1 / ((n : ℝ) + 2) < 1 := by
        rw [div_lt_one (by positivity)]
        linarith [n.cast_nonneg (α := ℝ)]
      dsimp [t]
      linarith
    rw [complexMGF_ofReal, complexMGF_ofReal]
    apply congrArg Complex.ofReal
    simpa only [mgf, id_eq, t, neg_mul, neg_neg] using hL (-t) (by linarith)
  exact AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hf hg hU hmem hfreq hz

private lemma tendsto_complexMGF_boundary_of_laplace {ν : Measure ℝ}
    [IsProbabilityMeasure ν]
    (hint : ∀ s : ℝ, 0 < s → Integrable (fun x => Real.exp (-s * x)) ν) (t : ℝ) :
    Tendsto (fun ε : ℝ => complexMGF id ν (-(ε : ℂ) + t * I)) (𝓝[>] 0)
      (𝓝 (complexMGF id ν (t * I))) := by
  unfold complexMGF
  apply tendsto_integral_filter_of_dominated_convergence (fun y => 1 + Real.exp (-y))
  · exact Eventually.of_forall fun ε => (by fun_prop : Continuous fun y : ℝ =>
      Complex.exp ((-(ε : ℂ) + t * I) * (id y : ℂ))).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with ε hε
    refine Eventually.of_forall fun y => ?_
    rw [Complex.norm_exp]
    have hre : ((-(ε : ℂ) + t * I) * ((id y : ℝ) : ℂ)).re = -ε * y := by
      simp [mul_re]
    rw [hre]
    rcases le_or_gt 0 y with hy | hy
    · have h : Real.exp (-ε * y) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hε.1])
      linarith [Real.exp_pos (-y)]
    · have h : Real.exp (-ε * y) ≤ Real.exp (-y) :=
        Real.exp_le_exp.mpr (by nlinarith [hε.2])
      linarith
  · exact (integrable_const 1).add (by simpa using hint 1 one_pos)
  · refine Eventually.of_forall fun y => ?_
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have h : Continuous fun ε : ℝ => Complex.exp ((-(ε : ℂ) + t * I) * ((id y : ℝ) : ℂ)) := by
      fun_prop
    simpa using h.tendsto 0

/-- Probability laws with equal finite negative Laplace transforms on `(0,∞)` coincide. -/
theorem measure_eq_of_laplace_eq_Ioi {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hintμ : ∀ s : ℝ, 0 < s → Integrable (fun x => Real.exp (-s * x)) μ)
    (hintν : ∀ s : ℝ, 0 < s → Integrable (fun x => Real.exp (-s * x)) ν)
    (hL : ∀ s : ℝ, 0 < s →
      (∫ x, Real.exp (-s * x) ∂μ) = ∫ x, Real.exp (-s * x) ∂ν) : μ = ν := by
  apply Measure.ext_of_charFun
  funext t
  rw [← complexMGF_id_mul_I, ← complexMGF_id_mul_I]
  have hμ := tendsto_complexMGF_boundary_of_laplace hintμ t
  have hν := tendsto_complexMGF_boundary_of_laplace hintν t
  apply tendsto_nhds_unique hμ
  apply Tendsto.congr' _ hν
  filter_upwards [self_mem_nhdsWithin] with ε hε
  symm
  apply complexMGF_eq_of_laplace hintμ hintν hL
  simp only [add_re, neg_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
    mul_one, sub_self, add_zero]
  simpa using hε

private lemma complexMGF_cauchyOne_of_re_neg {ν : Measure ℝ} (hν : IsCauchyOneLaw ν)
    {z : ℂ} (hz : z.re < 0) :
    complexMGF id ν z = Complex.exp ((-z) * Complex.log (-z)) := by
  have hprob : IsProbabilityMeasure ν := hν.1
  let U : Set ℂ := {z | z.re < 0}
  have hU : IsPreconnected U := (convex_halfSpace_re_lt 0).isPreconnected
  have hint : ∀ s : ℝ, 0 < s → Integrable (fun x => Real.exp (-s * x)) ν :=
    fun s hs => by simpa only [neg_mul] using (hν.2 s hs).1
  have hf : AnalyticOnNhd ℂ (complexMGF id ν) U := by
    intro w hw
    exact analyticAt_complexMGF (Iio_subset_interior_integrableExpSet_of_laplace hint hw)
  have hg : AnalyticOnNhd ℂ (fun w : ℂ => Complex.exp ((-w) * Complex.log (-w))) U := by
    intro w hw
    apply AnalyticAt.cexp
    apply AnalyticAt.mul (analyticAt_id.neg)
    apply AnalyticAt.clog analyticAt_id.neg
    rw [mem_slitPlane_iff]
    left
    change 0 < (-w).re
    simpa only [neg_re] using neg_pos.mpr hw
  have hmem : (-1 : ℂ) ∈ U := by simp [U]
  have hfreq : ∃ᶠ w in 𝓝[≠] (-1 : ℂ),
      complexMGF id ν w = Complex.exp ((-w) * Complex.log (-w)) := by
    have ht : Tendsto (fun n : ℕ => ((-1 + 1 / ((n : ℝ) + 2) : ℝ) : ℂ)) atTop
        (𝓝[≠] (-1 : ℂ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have h : Tendsto (fun n : ℕ => (-1 + 1 / ((n : ℝ) + 2) : ℝ)) atTop
            (𝓝 (-1 + 0)) := by
          apply Tendsto.add tendsto_const_nhds
          apply Tendsto.div_atTop tendsto_const_nhds
          exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
        rw [add_zero] at h
        simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto _).comp h
      · refine Eventually.of_forall fun n => ?_
        simp only [mem_compl_iff, mem_singleton_iff]
        intro h
        have h2 : (-1 + 1 / ((n : ℝ) + 2) : ℝ) = -1 := by exact_mod_cast h
        have h3 : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
        linarith
    apply ht.frequently
    refine Frequently.of_forall fun n => ?_
    let t : ℝ := -1 + 1 / ((n : ℝ) + 2)
    have htneg : t < 0 := by
      have h : 1 / ((n : ℝ) + 2) < 1 := by
        rw [div_lt_one (by positivity)]
        linarith [n.cast_nonneg (α := ℝ)]
      dsimp [t]
      linarith
    rw [complexMGF_ofReal]
    have hL : mgf id ν t = Real.exp ((-t) * Real.log (-t)) := by
      simpa only [mgf, id_eq, neg_mul, neg_neg] using (hν.2 (-t) (by linarith)).2
    rw [hL, Complex.ofReal_exp]
    apply congrArg Complex.exp
    rw [show -(t : ℂ) = ((-t : ℝ) : ℂ) by push_cast; rfl]
    rw [← Complex.ofReal_log (by linarith : (0 : ℝ) ≤ -t)]
    push_cast
    ring
  exact AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hf hg hU hmem hfreq hz

private lemma cauchyOne_exponent (t : ℝ) (ht : t ≠ 0) :
    (-((t : ℂ) * Complex.I)) * Complex.log (-((t : ℂ) * Complex.I)) =
      -((Real.pi / 2 * |t| : ℝ) : ℂ) - (t * Real.log |t| : ℝ) * Complex.I := by
  rcases lt_or_gt_of_ne ht with ht | ht
  · have hpos : 0 < -t := by linarith
    rw [show -((t : ℂ) * Complex.I) = ((-t : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [show ((-t : ℝ) : ℂ) * Complex.I = ((-t : ℝ) : ℂ) * Complex.I by rfl]
    rw [Complex.log_ofReal_mul hpos Complex.I_ne_zero, Complex.log_I]
    simp only [abs_of_neg ht]
    push_cast
    ring_nf
    simp [Complex.I_sq]
    ring
  · rw [show -((t : ℂ) * Complex.I) = (t : ℂ) * (-Complex.I) by ring]
    rw [Complex.log_ofReal_mul ht (neg_ne_zero.mpr Complex.I_ne_zero), Complex.log_neg_I]
    simp only [abs_of_pos ht]
    push_cast
    ring_nf
    simp [Complex.I_sq]
    ring

/-- The characteristic function determined by the index-one Laplace identity. -/
theorem charFun_of_isCauchyOneLaw {ν : Measure ℝ} (hν : IsCauchyOneLaw ν) (t : ℝ) :
    charFun ν t = cauchyOneCF t := by
  have hprob : IsProbabilityMeasure ν := hν.1
  rw [← complexMGF_id_mul_I]
  have hboundary := tendsto_complexMGF_boundary_of_laplace (fun s hs => by simpa only [neg_mul] using (hν.2 s hs).1) t
  rcases eq_or_ne t 0 with rfl | ht
  · simp [cauchyOneCF, complexMGF]
  have hformula : Tendsto (fun ε : ℝ => complexMGF id ν (-(ε : ℂ) + t * I)) (𝓝[>] 0)
      (𝓝 (cauchyOneCF t)) := by
    have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0, complexMGF id ν (-(ε : ℂ) + t * I) =
        Complex.exp ((-(-(ε : ℂ) + t * I)) * Complex.log (-(-(ε : ℂ) + t * I))) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      apply complexMGF_cauchyOne_of_re_neg hν
      simp only [add_re, neg_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
        mul_one, sub_self, add_zero]
      simpa using hε
    apply Tendsto.congr' (hev.mono fun ε h => h.symm)
    have hc : ContinuousAt (fun w : ℂ => Complex.exp ((-w) * Complex.log (-w))) (t * I) := by
      apply ContinuousAt.cexp
      apply ContinuousAt.mul continuousAt_neg
      apply ContinuousAt.clog continuousAt_neg
      rw [mem_slitPlane_iff]
      right
      simp [ht]
    have hz : Tendsto (fun ε : ℝ => -(ε : ℂ) + t * I) (𝓝[>] 0) (𝓝 (t * I)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds
      have h : Continuous fun ε : ℝ => -(ε : ℂ) + t * I := by fun_prop
      simpa using h.tendsto 0
    have hlim := hc.tendsto.comp hz
    simpa only [Function.comp_def, neg_zero, ofReal_zero, zero_add, cauchyOne_exponent t ht, cauchyOneCF] using hlim
  exact tendsto_nhds_unique hboundary hformula

/-- Uniqueness of the law of `𝒞₁`. -/
theorem cauchyOneLaw_unique {ν₁ ν₂ : Measure ℝ}
    (h₁ : IsCauchyOneLaw ν₁) (h₂ : IsCauchyOneLaw ν₂) : ν₁ = ν₂ := by
  have hprob₁ : IsProbabilityMeasure ν₁ := h₁.1
  have hprob₂ : IsProbabilityMeasure ν₂ := h₂.1
  exact measure_eq_of_laplace_eq_Ioi (fun s hs => by simpa only [neg_mul] using (h₁.2 s hs).1)
    (fun s hs => by simpa only [neg_mul] using (h₂.2 s hs).1)
    (fun s hs => by simpa only [neg_mul] using (h₁.2 s hs).2.trans (h₂.2 s hs).2.symm)

end
end SubcriticalCauchy.Bienayme
