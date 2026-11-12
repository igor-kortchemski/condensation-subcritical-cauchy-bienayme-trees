module

public import SubcriticalCauchy.LateProofs.StableLimitAux
public import SubcriticalCauchy.MainProofs.M1
public import SubcriticalCauchy.IncrementTailAsymptotics
public import SubcriticalCauchy.PotterBounds
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Proof helpers for the frozen statement of (2.4) (`paper_stable_limit`)

The analytic one-step estimate is isolated as `OneStepLaplaceLimit`; the iid
assembly and weak-convergence arguments here do not depend on its proof.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace SubcriticalCauchy.Bienayme

noncomputable section

/-- The one-step Laplace exponent asymptotic supplied by Node 3. -/
def OneStepLaplaceLimit (μ : Measure ℕ) [IsProbabilityMeasure μ] : Prop :=
  ∀ (_hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ),
    Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal) atTop (𝓝 1) →
    ∀ {s : ℝ}, 0 < s →
      Tendsto (fun n : ℕ => (n : ℝ) *
        ∫ k, (Real.exp (-(s / a n) * offspringIncrement k) - 1 +
          (s / a n) * (if |offspringIncrement k| ≤ a n then offspringIncrement k else 0)) ∂μ)
        atTop (𝓝 (stableKernelIntegral s))

/-- Law of the normalized sum of `n` independent increments. -/
noncomputable def normalizedIncrementLaw
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (a : ℕ → ℝ) (n : ℕ) :
    ProbabilityMeasure ℝ := by
  let stableLimitIncrementLawProbability : IsProbabilityMeasure (incrementLaw μ) := by
    unfold incrementLaw
    infer_instance
  exact ⟨(Measure.pi fun _ : Fin n => incrementLaw μ).map (fun x =>
      (((∑ i, x i : ℤ) : ℝ) - centering μ a n) / a n), inferInstance⟩

/-- Exact Laplace transform of the normalized `n`-fold increment law. -/
theorem normalizedIncrementLaw_laplace
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (a : ℕ → ℝ) (n : ℕ) (s : ℝ) :
    (∫ y, Real.exp (-s * y) ∂(normalizedIncrementLaw μ a n : Measure ℝ)) =
      (∫ k, Real.exp (-(s / a n) * offspringIncrement k) ∂μ) ^ n *
        Real.exp (s * centering μ a n / a n) := by
  let stableLimitIncrementLawProbability : IsProbabilityMeasure (incrementLaw μ) := by
    unfold incrementLaw
    infer_instance
  have hrealLaw : (incrementLaw μ).map (fun z : ℤ => (z : ℝ)) =
      μ.map offspringIncrement := by
    rw [incrementLaw, Measure.map_map (measurable_of_countable (fun z : ℤ => (z : ℝ)))
      (measurable_of_countable (fun k : ℕ => (k : ℤ) - 1))]
    apply Measure.map_congr
    filter_upwards [] with k
    simp [offspringIncrement]
  have hpi : (Measure.pi fun _ : Fin n => μ.map offspringIncrement) =
      (Measure.pi fun _ : Fin n => incrementLaw μ).map
        (fun x i => (x i : ℝ)) := by
    rw [← hrealLaw]
    exact (Measure.pi_map_pi (fun _ => (measurable_of_countable _).aemeasurable)).symm
  have hnormmap : (Measure.pi fun _ : Fin n => incrementLaw μ).map (fun x =>
      (((∑ i, x i : ℤ) : ℝ) - centering μ a n) / a n) =
      (Measure.pi fun _ : Fin n => μ.map offspringIncrement).map (fun x =>
        ((∑ i, x i) - centering μ a n) / a n) := by
    have hcast : Measurable (fun x : (Fin n → ℤ) => fun i => (x i : ℝ)) := by fun_prop
    have hout : Measurable (fun x : Fin n → ℝ =>
        ((∑ i, x i) - centering μ a n) / a n) := by fun_prop
    rw [hpi, Measure.map_map hout hcast]
    apply Measure.map_congr
    filter_upwards [] with x
    simp only [Function.comp_def]
    push_cast
    rfl
  have hprod := integral_exp_sum_pi (fun _ : Fin n => μ.map offspringIncrement)
    (fun _ => (a n)⁻¹) s
  have hfactor (i : Fin n) :
      (∫ z : ℝ, Real.exp (-s * (a n)⁻¹ * z) ∂μ.map offspringIncrement) =
        ∫ k, Real.exp (-(s / a n) * offspringIncrement k) ∂μ := by
    rw [integral_map measurable_offspringIncrement.aemeasurable (by fun_prop)]
    apply integral_congr_ae
    filter_upwards [] with k
    congr 1
    field_simp
  have hfactor' : (∏ i : Fin n, ∫ z : ℝ, Real.exp (-s * (a n)⁻¹ * z)
      ∂μ.map offspringIncrement) =
      (∫ k, Real.exp (-(s / a n) * offspringIncrement k) ∂μ) ^ n := by
    calc
      _ = ∏ _i : Fin n, ∫ k, Real.exp (-(s / a n) * offspringIncrement k) ∂μ :=
        Finset.prod_congr rfl (fun i _ => hfactor i)
      _ = _ := by simp
  rw [hfactor'] at hprod
  rw [normalizedIncrementLaw]
  change (∫ y, Real.exp (-s * y) ∂Measure.map
      (fun x : Fin n → ℤ => (((∑ i, x i : ℤ) : ℝ) - centering μ a n) / a n)
      (Measure.pi fun _ : Fin n => incrementLaw μ)) = _
  rw [hnormmap, integral_map (by fun_prop) (by fun_prop)]
  calc
    (∫ x : Fin n → ℝ, Real.exp (-s *
        (((∑ i, x i) - centering μ a n) / a n))
        ∂Measure.pi fun _ : Fin n => μ.map offspringIncrement) =
        (∫ x : Fin n → ℝ, Real.exp (-s * ∑ i, (a n)⁻¹ * x i)
          ∂Measure.pi fun _ : Fin n => μ.map offspringIncrement) *
          Real.exp (s * centering μ a n / a n) := by
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [← Real.exp_add]
      congr 1
      have hsum : (∑ i, (a n)⁻¹ * x i) = (a n)⁻¹ * ∑ i, x i := by
        rw [Finset.mul_sum]
      simp only [div_eq_mul_inv, hsum]
      ring
    _ = _ := by rw [hprod]

private lemma integrable_exp_neg_mul_offspringIncrement
    (μ : Measure ℕ) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r) :
    Integrable (fun k : ℕ => Real.exp (-r * offspringIncrement k)) μ := by
  apply memLp_one_iff_integrable.mp
  apply MemLp.of_bound (by fun_prop) (Real.exp r)
  filter_upwards [] with k
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hk : -1 ≤ offspringIncrement k := by
    unfold offspringIncrement
    linarith [Nat.cast_nonneg (α := ℝ) k]
  nlinarith [mul_nonneg hr.le (show 0 ≤ offspringIncrement k + 1 by linarith)]

private lemma oneStepKernel_eq_laplace_sub_add_centering
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ ≠ ∞) {a s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    (∫ k, Real.exp (-(s / a) * offspringIncrement k) ∂μ) - 1 +
        (s / a) * truncatedIncrementMean μ a =
      ∫ k, (Real.exp (-(s / a) * offspringIncrement k) - 1 +
        (s / a) * (if |offspringIncrement k| ≤ a then offspringIncrement k else 0)) ∂μ := by
  have hexp := integrable_exp_neg_mul_offspringIncrement μ (div_pos hs ha)
  have htr := integrable_truncatedIncrement μ hm a
  have hsub : (∫ k, (Real.exp (-(s / a) * offspringIncrement k) - 1) ∂μ) =
      (∫ k, Real.exp (-(s / a) * offspringIncrement k) ∂μ) - 1 := by
    rw [integral_sub hexp (integrable_const 1)]
    simp
  have hmul : (∫ k, (s / a) *
      (if |offspringIncrement k| ≤ a then offspringIncrement k else 0) ∂μ) =
      (s / a) * truncatedIncrementMean μ a := by
    rw [integral_const_mul, truncatedIncrementMean]
  rw [← hsub, ← hmul]
  exact (integral_add (hexp.sub (integrable_const 1)) (htr.const_mul (s / a))).symm

private lemma normalizedIncrementLaw_laplace_exp
    (μ : Measure ℕ) [IsProbabilityMeasure μ] {a : ℕ → ℝ} {s : ℝ}
    (hat : Tendsto a atTop atTop) (hs : 0 < s) :
    ∀ᶠ n in atTop,
      (∫ y, Real.exp (-s * y) ∂(normalizedIncrementLaw μ a n : Measure ℝ)) =
        Real.exp ((n : ℝ) * Real.log
            (∫ k, Real.exp (-(s / a n) * offspringIncrement k) ∂μ) +
          (n : ℝ) * ((s / a n) * truncatedIncrementMean μ (a n))) := by
  filter_upwards [hat.eventually_gt_atTop 0] with n han
  let L := ∫ k, Real.exp (-(s / a n) * offspringIncrement k) ∂μ
  have hLpos : 0 < L := integral_exp_pos
    (integrable_exp_neg_mul_offspringIncrement μ (div_pos hs han))
  rw [normalizedIncrementLaw_laplace]
  change L ^ n * Real.exp (s * centering μ a n / a n) = _
  calc
    L ^ n * Real.exp (s * centering μ a n / a n) =
        Real.exp ((n : ℝ) * Real.log L) * Real.exp (s * centering μ a n / a n) := by
      congr 1
      rw [← Real.exp_log (pow_pos hLpos n), Real.log_pow]
    _ = Real.exp ((n : ℝ) * Real.log L +
        (n : ℝ) * ((s / a n) * truncatedIncrementMean μ (a n))) := by
      rw [← Real.exp_add]
      congr 1
      unfold centering
      ring

/-- The product `aₙ L(aₙ)` diverges for a positive measurable slowly varying `L`. -/
theorem tendsto_mul_slowlyVarying_atTop {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L) {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) :
    Tendsto (fun n => a n * L (a n)) atTop atTop := by
  obtain ⟨C, hC, N, hN, hcomp⟩ := sqrt_potter_comparison hpos hL hsv
  let D := L N * Real.sqrt N / C
  have hD : 0 < D := div_pos (mul_pos (hpos N hN) (Real.sqrt_pos.mpr hN)) hC
  have hmain : Tendsto (fun n => D * Real.sqrt (a n)) atTop atTop := by
    simpa only [Function.comp_def, mul_comm] using
      (Real.tendsto_sqrt_atTop.comp ha).atTop_mul_const hD
  apply tendsto_atTop_mono' atTop _ hmain
  filter_upwards [ha.eventually_ge_atTop N] with n hn
  have h := hcomp N (a n) le_rfl hn
  have hDle : D ≤ L (a n) * Real.sqrt (a n) := by
    exact (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using h)
  have hsqrt : 0 ≤ Real.sqrt (a n) := Real.sqrt_nonneg _
  calc
    D * Real.sqrt (a n) ≤ (L (a n) * Real.sqrt (a n)) * Real.sqrt (a n) :=
      mul_le_mul_of_nonneg_right hDle hsqrt
    _ = L (a n) * (Real.sqrt (a n) * Real.sqrt (a n)) := by ring
    _ = a n * L (a n) := by
      rw [Real.mul_self_sqrt (hN.le.trans hn)]
      ring

/-- The scaling relation implies the second-order estimate `n / aₙ² → 0`. -/
theorem scaling_nat_div_sq_tendsto_zero
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) {a : ℕ → ℝ}
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => (n : ℝ) / (a n) ^ 2) atTop (𝓝 0) := by
  obtain ⟨hm, L, hpos, hsv, hL, hlocal⟩ := hμ
  have hlit : IsSubcriticalCauchyOffspring μ := ⟨hm, L, hpos, hsv, hlocal⟩
  have hat : Tendsto a atTop atTop := scaling_tendsto_atTop μ hlit ha
  have hratio := scaling_div_mul_tendsto_one μ hm hpos hL hsv hlocal ha
  have hrecip : Tendsto (fun n : ℕ => (n : ℝ) * L (a n) / a n) atTop (𝓝 1) := by
    simpa only [div_eq_mul_inv, mul_inv_rev, inv_inv, inv_one] using
      hratio.inv₀ one_ne_zero
  have hinv : Tendsto (fun n : ℕ => (a n * L (a n))⁻¹) atTop (𝓝 0) :=
    (tendsto_mul_slowlyVarying_atTop hpos hL hsv hat).inv_tendsto_atTop
  have hprod : Tendsto
      (fun n : ℕ => ((n : ℝ) * L (a n) / a n) * (a n * L (a n))⁻¹) atTop (𝓝 0) := by
    simpa using hrecip.mul hinv
  apply hprod.congr'
  filter_upwards [hat.eventually_gt_atTop 0] with n han
  have hLa : 0 < L (a n) := hpos _ han
  field_simp [han.ne', hLa.ne']

/-- Logarithmic correction with a vanishing second-order term. -/
theorem tendsto_nat_mul_log_sub_of_tendsto_zero {u : ℕ → ℝ} (hu0 : Tendsto u atTop (𝓝 0))
    (hsq : Tendsto (fun n : ℕ => (n : ℝ) * u n ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (n : ℝ) * (Real.log (1 + u n) - u n)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_
    (show Tendsto (fun n : ℕ => 2 * ((n : ℝ) * u n ^ 2)) atTop (𝓝 0) by
      simpa using hsq.const_mul 2)
  have hu0norm : Tendsto (fun n => ‖u n‖) atTop (𝓝 0) := by simpa using hu0.norm
  filter_upwards [hu0norm.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)),
    eventually_gt_atTop (0 : ℕ)] with n hun hn
  have hu : ‖u n‖ < 1 := by
    rw [Real.norm_eq_abs] at hun ⊢
    linarith
  have hpos : 0 < 1 + u n := by
    rw [Real.norm_eq_abs] at hun
    linarith [neg_abs_le (u n)]
  have hbound := Complex.norm_log_one_add_sub_self_le
    (z := (u n : ℂ)) (by simpa using hu)
  have heq : Complex.log (1 + (u n : ℂ)) =
      ((Real.log (1 + u n) : ℝ) : ℂ) := by
    rw [show 1 + (u n : ℂ) = ((1 + u n : ℝ) : ℂ) by norm_cast,
      ← Complex.ofReal_log hpos.le]
  rw [heq] at hbound
  have hbound' : ‖Real.log (1 + u n) - u n‖ ≤ 2 * ‖u n‖ ^ 2 := by
    have hcomm : (1 - ‖(u n : ℂ)‖)⁻¹ / 2 ≤ 1 := by
      have hnorm : ‖(u n : ℂ)‖ < 1 / 2 := by simpa using hun
      have hpos' : 0 < 1 - ‖(u n : ℂ)‖ := by linarith
      have hi : (1 - ‖(u n : ℂ)‖)⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ hpos' two_pos]
        linarith
      linarith
    calc
      ‖Real.log (1 + u n) - u n‖ ≤ ‖(u n : ℂ)‖ ^ 2 * (1 - ‖(u n : ℂ)‖)⁻¹ / 2 := by
        exact_mod_cast hbound
      _ = ‖u n‖ ^ 2 * ((1 - ‖(u n : ℂ)‖)⁻¹ / 2) := by simp [mul_div_assoc]
      _ ≤ ‖u n‖ ^ 2 * 1 := by
        exact mul_le_mul_of_nonneg_left hcomm (sq_nonneg _)
      _ ≤ 2 * ‖u n‖ ^ 2 := by nlinarith [sq_nonneg ‖u n‖]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  calc
    (n : ℝ) * ‖Real.log (1 + u n) - u n‖ ≤ (n : ℝ) * (2 * ‖u n‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hbound' (Nat.cast_nonneg n)
    _ = 2 * ((n : ℝ) * u n ^ 2) := by simp [Real.norm_eq_abs, sq_abs]; ring


/-- Laplace transforms of the normalized iid laws, under the Node 3 one-step limit. -/
theorem normalizedIncrementLaw_laplace_tendsto
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (hOne : OneStepLaplaceLimit μ)
    (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n => ∫ y, Real.exp (-s * y) ∂(normalizedIncrementLaw μ a n : Measure ℝ))
      atTop (𝓝 (Real.exp (s * Real.log s +
        (Real.eulerMascheroniConstant - 1) * s))) := by
  let L : ℕ → ℝ := fun n => ∫ k, Real.exp (-(s / a n) * offspringIncrement k) ∂μ
  let u : ℕ → ℝ := fun n => L n - 1
  let B : ℕ → ℝ := fun n => (s / a n) * truncatedIncrementMean μ (a n)
  let H : ℕ → ℝ := fun n => (n : ℝ) * (u n + B n)
  have hfin : offspringMean μ ≠ ∞ := ne_top_of_lt (hμ.1.trans ENNReal.one_lt_top)
  have hat : Tendsto a atTop atTop := scaling_tendsto_atTop μ hμ.to_literal ha
  have hH : Tendsto H atTop (𝓝 (stableKernelIntegral s)) := by
    apply (hOne hμ a ha hs).congr'
    filter_upwards [hat.eventually_gt_atTop 0] with n han
    dsimp only [H, u, B, L]
    rw [oneStepKernel_eq_laplace_sub_add_centering μ hfin han hs]
  have hT := truncatedIncrementMean_tendsto μ hfin hat
  have hB : Tendsto B atTop (𝓝 0) := by
    have hraw := ((tendsto_const_nhds (x := s)).mul hat.inv_tendsto_atTop).mul hT
    have hraw0 : Tendsto (fun n : ℕ =>
        (s * (a n)⁻¹) * truncatedIncrementMean μ (a n)) atTop (𝓝 0) := by
      simpa using hraw
    apply hraw0.congr'
    filter_upwards [] with n
    dsimp only [B]
    ring
  have hHd : Tendsto (fun n : ℕ => H n / (n : ℝ)) atTop (𝓝 0) := by
    simpa using hH.div_atTop tendsto_natCast_atTop_atTop
  have hu0 : Tendsto u atTop (𝓝 0) := by
    have hdiff : Tendsto (fun n : ℕ => H n / (n : ℝ) - B n) atTop (𝓝 0) := by
      simpa using hHd.sub hB
    apply hdiff.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    dsimp only [H]
    field_simp [hn0]
    ring
  have hBsq : Tendsto (fun n : ℕ => (n : ℝ) * B n ^ 2) atTop (𝓝 0) := by
    have hprod := (scaling_nat_div_sq_tendsto_zero μ hμ ha).mul ((hT.const_mul s).pow 2)
    have hprod0 : Tendsto (fun n : ℕ => ((n : ℝ) / (a n) ^ 2) *
        (s * truncatedIncrementMean μ (a n)) ^ 2) atTop (𝓝 0) := by
      simpa using hprod
    apply hprod0.congr'
    filter_upwards [hat.eventually_gt_atTop 0] with n han
    dsimp only [B]
    field_simp [han.ne']
  have husq : Tendsto (fun n : ℕ => (n : ℝ) * u n ^ 2) atTop (𝓝 0) := by
    have hH2 : Tendsto (fun n : ℕ => H n ^ 2 / (n : ℝ)) atTop (𝓝 0) := by
      simpa using (hH.pow 2).div_atTop tendsto_natCast_atTop_atTop
    have hHB : Tendsto (fun n : ℕ => 2 * (H n * B n)) atTop (𝓝 0) := by
      simpa using (hH.mul hB).const_mul 2
    have hzero : Tendsto (fun n : ℕ =>
        H n ^ 2 / (n : ℝ) - 2 * (H n * B n) + (n : ℝ) * B n ^ 2)
        atTop (𝓝 0) := by
      simpa using (hH2.sub hHB).add hBsq
    apply hzero.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    dsimp only [H]
    field_simp [hn0]
    ring
  have hlog := tendsto_nat_mul_log_sub_of_tendsto_zero hu0 husq
  have hexponent : Tendsto (fun n : ℕ => (n : ℝ) * Real.log (L n) +
      (n : ℝ) * B n) atTop (𝓝 (stableKernelIntegral s)) := by
    have hadd : Tendsto (fun n : ℕ =>
        (n : ℝ) * (Real.log (1 + u n) - u n) + H n)
        atTop (𝓝 (0 + stableKernelIntegral s)) := hlog.add hH
    have hadd0 : Tendsto (fun n : ℕ =>
        (n : ℝ) * (Real.log (1 + u n) - u n) + H n)
        atTop (𝓝 (stableKernelIntegral s)) := by simpa using hadd
    apply hadd0.congr'
    filter_upwards [] with n
    have hLu : 1 + u n = L n := by dsimp only [u]; ring
    rw [hLu]
    dsimp only [H]
    ring
  rw [← stableKernelIntegral_eq hs]
  apply (hexponent.rexp).congr'
  filter_upwards [normalizedIncrementLaw_laplace_exp μ hat hs] with n hn
  exact hn.symm


/-- The frozen (2.4) conclusion, conditional only on the Node 3 one-step limit. -/
theorem stable_limit_of_oneStep
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (hOne : OneStepLaplaceLimit μ)
    (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1))
    (ν : Measure ℝ) (hν : IsCauchyOneLaw ν) (f : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (fun n : ℕ => ∫ x, f (((∑ i, (x i : ℝ)) - centering μ a n) / a n)
        ∂(Measure.pi fun _ : Fin n => incrementLaw μ))
      atTop (𝓝 (∫ y, f (y + (1 - Real.eulerMascheroniConstant)) ∂ν)) := by
  let c : ℝ := 1 - Real.eulerMascheroniConstant
  let Λ : ℝ → ℝ := fun s => s * Real.log s + (Real.eulerMascheroniConstant - 1) * s
  let ρ : Measure ℝ := ν.map (fun x => x + c)
  let stableLimitCauchyProbability : IsProbabilityMeasure ν := hν.1
  let stableLimitShiftedProbability : IsProbabilityMeasure ρ := by
    dsimp only [ρ]
    infer_instance
  have hΛ0 : Λ 0 = 0 := by simp [Λ]
  have hΛcont : ContinuousWithinAt (fun s => Real.exp (Λ s)) (Set.Ioi 0) 0 := by
    have hc : Continuous Λ := by
      exact Real.continuous_mul_log.add (continuous_const.mul continuous_id)
    exact hc.rexp.continuousWithinAt
  have hmapν : AEMeasurable (fun x : ℝ => x + c) ν := by fun_prop
  have hint : ∀ s : ℝ, 0 < s → Integrable (fun x => Real.exp (-s * x)) ρ := by
    intro t ht
    apply (integrable_map_measure (by fun_prop) hmapν).2
    have hbase := (hν.2 t ht).1.const_mul (Real.exp (-t * c))
    apply hbase.congr
    filter_upwards [] with x
    rw [← Real.exp_add]
    congr 1
    ring
  have hρL : ∀ s : ℝ, 0 < s → ∫ x, Real.exp (-s * x) ∂ρ = Real.exp (Λ s) := by
    intro t ht
    rw [show (∫ x, Real.exp (-t * x) ∂ρ) =
        ∫ x, Real.exp (-t * (x + c)) ∂ν by
      exact integral_map hmapν (by fun_prop)]
    calc
      (∫ x, Real.exp (-t * (x + c)) ∂ν) =
          Real.exp (-t * c) * ∫ x, Real.exp (-t * x) ∂ν := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with x
        rw [← Real.exp_add]
        congr 1
        ring
      _ = Real.exp (-t * c) * Real.exp (t * Real.log t) := by
        have hbase : (∫ x, Real.exp (-t * x) ∂ν) = Real.exp (t * Real.log t) := by
          simpa only [neg_mul] using (hν.2 t ht).2
        rw [hbase]
      _ = Real.exp (Λ t) := by
        rw [← Real.exp_add]
        congr 1
        dsimp only [Λ, c]
        ring
  have hweak : Tendsto (normalizedIncrementLaw μ a) atTop
      (𝓝 (⟨ρ, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
    apply tendsto_of_exponential_laplace_limit_of_laplace_eq Λ hΛ0 hΛcont
      (normalizedIncrementLaw μ a) (fun t ht => ?_) hint hρL
    exact normalizedIncrementLaw_laplace_tendsto μ hμ hOne a ha ht
  have hnormInt (n : ℕ) :
      (∫ x, f (((∑ i, (x i : ℝ)) - centering μ a n) / a n)
        ∂(Measure.pi fun _ : Fin n => incrementLaw μ)) =
        ∫ y, f y ∂(normalizedIncrementLaw μ a n : Measure ℝ) := by
    let stableLimitIncrementLawProbability : IsProbabilityMeasure (incrementLaw μ) := by
      unfold incrementLaw
      infer_instance
    change (∫ x, f (((∑ i, (x i : ℝ)) - centering μ a n) / a n)
        ∂(Measure.pi fun _ : Fin n => incrementLaw μ)) =
      ∫ y, f y ∂Measure.map (fun x : Fin n → ℤ =>
        (((∑ i, x i : ℤ) : ℝ) - centering μ a n) / a n)
        (Measure.pi fun _ : Fin n => incrementLaw μ)
    rw [integral_map (by fun_prop) f.continuous.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [] with x
    congr 1
    push_cast
    rfl
  have hfweak := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak f
  have hmain : Tendsto (fun n : ℕ => ∫ x,
      f (((∑ i, (x i : ℝ)) - centering μ a n) / a n)
      ∂(Measure.pi fun _ : Fin n => incrementLaw μ)) atTop
      (𝓝 (∫ y, f y ∂ρ)) := by
    apply hfweak.congr'
    filter_upwards [] with n
    exact (hnormInt n).symm
  rw [show (∫ y, f y ∂ρ) = ∫ y, f (y + c) ∂ν by
    exact integral_map hmapν (by fun_prop)] at hmain
  exact hmain

end
end SubcriticalCauchy.Bienayme
