module

public import SubcriticalCauchy.LogMomentExamplesAux
public import SubcriticalCauchy.LateProofs.C1Witness
public import SubcriticalCauchy.PotterBounds

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The logarithmic moment in the introduction

The source uses `μₙ ∼ L(n) / n^(1+α)`: its Cauchy case `α = 1` is therefore
`μₙ ∼ L(n) / n²`.  The examples below normalize a genuinely subcritical law
with `L(n) ∼ c' / (log n)^(1+β)`.  The nonnegative logarithmic moment converges
exactly when `β > 1`, so it diverges throughout the source's range `0 < β ≤ 1`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace SubcriticalCauchy.Bienayme

noncomputable section

/-- Unnormalized tail weights with `L(n) = c / (log n)^(1+β)`. -/
noncomputable def logMomentRawWeight (c β : ℝ) (k : ℕ) : ℝ :=
  if k < 3 then 0 else c / ((k : ℝ) ^ 2 * Real.log k ^ (1 + β))

/-- First moment before the small multiplier enforcing subcriticality. -/
noncomputable def logMomentRawMoment (c β : ℝ) : ℝ :=
  ∑' k : ℕ, logMomentRawWeight c β k * (k : ℝ)

/-- A multiplier making the raw first moment strictly less than one. -/
noncomputable def logMomentSmallConstant (c β : ℝ) : ℝ :=
  (1 + logMomentRawMoment c β)⁻¹

/-- Mass one at zero and the scaled logarithmic tail. -/
noncomputable def logMomentWeight (c β : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 1 else logMomentSmallConstant c β * logMomentRawWeight c β k

/-- Total unnormalized mass. -/
noncomputable def logMomentTotal (c β : ℝ) : ℝ := ∑' k : ℕ, logMomentWeight c β k

/-- Positive coefficient in the normalized tail asymptotic. -/
noncomputable def logMomentTailConstant (c β : ℝ) : ℝ :=
  c * logMomentSmallConstant c β / logMomentTotal c β

lemma logMomentRawWeight_nonneg {c β : ℝ} (hc : 0 < c) (k : ℕ) :
    0 ≤ logMomentRawWeight c β k := by
  unfold logMomentRawWeight
  split_ifs <;> positivity

lemma logMomentRawMoment_nonneg {c β : ℝ} (hc : 0 < c) :
    0 ≤ logMomentRawMoment c β := by
  apply tsum_nonneg
  intro k
  exact mul_nonneg (logMomentRawWeight_nonneg hc _) (Nat.cast_nonneg _)

lemma logMomentSmallConstant_pos {c β : ℝ} (hc : 0 < c) :
    0 < logMomentSmallConstant c β := by
  have := logMomentRawMoment_nonneg (β := β) hc
  unfold logMomentSmallConstant
  positivity

lemma logMomentWeight_nonneg {c β : ℝ} (hc : 0 < c) (k : ℕ) :
    0 ≤ logMomentWeight c β k := by
  unfold logMomentWeight
  split_ifs with hk
  · norm_num
  · exact mul_nonneg (logMomentSmallConstant_pos hc).le (logMomentRawWeight_nonneg hc _)

lemma logMomentRawMoment_summable {c β : ℝ} (hc : 0 < c) (hβ : 0 < β) :
    Summable (fun k : ℕ => logMomentRawWeight c β k * (k : ℝ)) := by
  apply ((summable_logTail (show 1 < 1 + β by linarith)).mul_left c).congr
  intro k
  by_cases hk : k < 3
  · have hkR : (k : ℝ) < 3 := by exact_mod_cast hk
    simp [logMomentRawWeight, logTail, hk, hkR]
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hlog : 0 < Real.log k := Real.log_pos hk1
  simp only [logMomentRawWeight, logTail, hk, show ¬(k : ℝ) < 3 by exact_mod_cast (show ¬k < 3 by omega),
    ↓reduceIte]
  field_simp [hc.ne', hk0.ne', hlog.ne', (Real.rpow_pos_of_pos hlog (1 + β)).ne']

lemma logMomentRawWeight_summable {c β : ℝ} (hc : 0 < c) (hβ : 0 < β) :
    Summable (logMomentRawWeight c β) := by
  apply Summable.of_nonneg_of_le (f := fun k : ℕ => logMomentRawWeight c β k * (k : ℝ))
    (logMomentRawWeight_nonneg hc) (fun k => ?_) (logMomentRawMoment_summable hc hβ)
  by_cases hk : k < 3
  · simp [logMomentRawWeight, hk]
  · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
    exact le_mul_of_one_le_right (logMomentRawWeight_nonneg hc _) hk1

lemma logMomentWeight_summable {c β : ℝ} (hc : 0 < c) (hβ : 0 < β) :
    Summable (logMomentWeight c β) := by
  rw [← summable_nat_add_iff 1]
  apply ((summable_nat_add_iff 1).mpr
    ((logMomentRawWeight_summable hc hβ).mul_left (logMomentSmallConstant c β))).congr
  intro n
  simp [logMomentWeight]

lemma logMomentTotal_pos {c β : ℝ} (hc : 0 < c) (hβ : 0 < β) :
    0 < logMomentTotal c β := by
  calc
    0 < logMomentWeight c β 0 := by simp [logMomentWeight]
    _ ≤ logMomentTotal c β := (logMomentWeight_summable hc hβ).le_tsum 0
      (fun j _ => logMomentWeight_nonneg hc j)

lemma logMomentTotal_enn {c β : ℝ} (hc : 0 < c) (hβ : 0 < β) :
    (∑' k : ℕ, ENNReal.ofReal (logMomentWeight c β k)) =
      ENNReal.ofReal (logMomentTotal c β) := by
  exact (ENNReal.ofReal_tsum_of_nonneg (logMomentWeight_nonneg hc)
    (logMomentWeight_summable hc hβ)).symm

/-- The normalized offspring PMF for every positive logarithmic exponent. -/
noncomputable def logMomentPMF {c β : ℝ} (hc : 0 < c) (hβ : 0 < β) : PMF ℕ :=
  PMF.normalize (fun k : ℕ => ENNReal.ofReal (logMomentWeight c β k))
    (by
      rw [logMomentTotal_enn hc hβ]
      exact (ENNReal.ofReal_pos.mpr (logMomentTotal_pos hc hβ)).ne')
    (logMomentWeight_summable hc hβ).tsum_ofReal_ne_top

/-- The normalized offspring law for every positive logarithmic exponent. -/
noncomputable def logMomentMeasure {c β : ℝ} (hc : 0 < c) (hβ : 0 < β) : Measure ℕ :=
  (logMomentPMF hc hβ).toMeasure

instance logMomentMeasure_isProbability {c β : ℝ} (hc : 0 < c) (hβ : 0 < β) :
    IsProbabilityMeasure (logMomentMeasure hc hβ) := by
  unfold logMomentMeasure
  infer_instance

lemma logMoment_atom {c β : ℝ} (hc : 0 < c) (hβ : 0 < β) (k : ℕ) :
    logMomentMeasure hc hβ {k} =
      ENNReal.ofReal (logMomentWeight c β k / logMomentTotal c β) := by
  rw [logMomentMeasure, logMomentPMF,
    PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton k), PMF.normalize_apply,
    logMomentTotal_enn hc hβ, ← ENNReal.ofReal_inv_of_pos (logMomentTotal_pos hc hβ),
    ← ENNReal.ofReal_mul (logMomentWeight_nonneg hc k)]
  rfl

lemma logMomentMean {c β : ℝ} (hc : 0 < c) (hβ : 0 < β) :
    offspringMean (logMomentMeasure hc hβ) =
      ENNReal.ofReal ((logMomentSmallConstant c β / logMomentTotal c β) *
        logMomentRawMoment c β) := by
  have hs : 0 ≤ logMomentSmallConstant c β / logMomentTotal c β :=
    div_nonneg (logMomentSmallConstant_pos hc).le (logMomentTotal_pos hc hβ).le
  have hterm (k : ℕ) : (k : ℝ≥0∞) * logMomentMeasure hc hβ {k} =
      ENNReal.ofReal ((logMomentSmallConstant c β / logMomentTotal c β) *
        (logMomentRawWeight c β k * (k : ℝ))) := by
    rw [logMoment_atom hc hβ, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg k)]
    congr 1
    by_cases hk : k = 0
    · subst k
      simp [logMomentWeight, logMomentRawWeight]
    · simp only [logMomentWeight, hk, ↓reduceIte]
      field_simp [(logMomentTotal_pos hc hβ).ne']
  rw [offspringMean, lintegral_countable']
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun k => mul_nonneg hs (mul_nonneg (logMomentRawWeight_nonneg hc _) (Nat.cast_nonneg _)))
    ((logMomentRawMoment_summable hc hβ).mul_left
      (logMomentSmallConstant c β / logMomentTotal c β))]
  rw [tsum_mul_left]
  rfl

lemma logMomentTotal_one_le {c β : ℝ} (hc : 0 < c) (hβ : 0 < β) :
    1 ≤ logMomentTotal c β := by
  calc
    1 = logMomentWeight c β 0 := by simp [logMomentWeight]
    _ ≤ logMomentTotal c β := (logMomentWeight_summable hc hβ).le_tsum 0
      (fun j _ => logMomentWeight_nonneg hc j)

lemma logMoment_mean_lt_one {c β : ℝ} (hc : 0 < c) (hβ : 0 < β) :
    offspringMean (logMomentMeasure hc hβ) < 1 := by
  rw [logMomentMean hc hβ, ENNReal.ofReal_lt_one]
  have hM := logMomentRawMoment_nonneg (β := β) hc
  have hnum : logMomentSmallConstant c β * logMomentRawMoment c β < 1 := by
    unfold logMomentSmallConstant
    rw [inv_mul_eq_div]
    exact (div_lt_one (by linarith)).mpr (by linarith)
  rw [div_mul_eq_mul_div, div_lt_one (logMomentTotal_pos hc hβ)]
  exact hnum.trans_le (logMomentTotal_one_le hc hβ)

/-- The measurable slowly varying scale, equal to its eventual formula at `x ≥ 3`. -/
noncomputable def logMomentSlowScale (c β : ℝ) (x : ℝ) : ℝ :=
  if x < 3 then logMomentTailConstant c β
  else logMomentTailConstant c β / Real.log x ^ (1 + β)

lemma logMomentTailConstant_pos {c β : ℝ} (hc : 0 < c) (hβ : 0 < β) :
    0 < logMomentTailConstant c β :=
  div_pos (mul_pos hc (logMomentSmallConstant_pos hc)) (logMomentTotal_pos hc hβ)

lemma logMomentSlowScale_pos {c β : ℝ} (hc : 0 < c) (hβ : 0 < β) {x : ℝ}
    (_hx : 0 < x) : 0 < logMomentSlowScale c β x := by
  unfold logMomentSlowScale
  split_ifs with hx3
  · exact logMomentTailConstant_pos hc hβ
  · exact div_pos (logMomentTailConstant_pos hc hβ)
      (Real.rpow_pos_of_pos (Real.log_pos (by linarith)) _)

lemma logMomentSlowScale_measurable (c β : ℝ) :
    Measurable (logMomentSlowScale c β) := by
  unfold logMomentSlowScale
  apply Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
  fun_prop

lemma logMomentSlowScale_slowlyVarying {c β : ℝ} (hc : 0 < c) (hβ : 0 < β) :
    IsSlowlyVaryingAtTop (logMomentSlowScale c β) := by
  intro t ht
  have hlog := (tendsto_log_mul_add_div_log_add_atTop ht 0 0).inv₀ one_ne_zero
  have hpow := hlog.rpow_const (p := 1 + β) (Or.inl (inv_ne_zero one_ne_zero))
  have hpow' : Tendsto (fun x : ℝ =>
      (Real.log (t * x + 0) / Real.log (x + 0))⁻¹ ^ (1 + β)) atTop (𝓝 1) := by
    simpa only [inv_one, Real.one_rpow] using hpow
  apply hpow'.congr'
  filter_upwards [eventually_gt_atTop (3 : ℝ),
    (tendsto_id.const_mul_atTop ht).eventually_gt_atTop 3] with x hx htx
  change 3 < t * x at htx
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogtx : 0 < Real.log (t * x) := Real.log_pos (by linarith)
  simp only [logMomentSlowScale, show ¬x < 3 by linarith, show ¬t * x < 3 by linarith,
    ↓reduceIte]
  field_simp [(logMomentTailConstant_pos hc hβ).ne', hlogx.ne', hlogtx.ne',
    (Real.rpow_pos_of_pos hlogx (1 + β)).ne',
    (Real.rpow_pos_of_pos hlogtx (1 + β)).ne']
  simp only [add_zero]
  rw [Real.div_rpow hlogx.le hlogtx.le,
    div_mul_cancel₀ _ (Real.rpow_pos_of_pos hlogtx (1 + β)).ne']

lemma logMoment_local {c β : ℝ} (hc : 0 < c) (hβ : 0 < β) :
    Tendsto (fun k : ℕ => (logMomentMeasure hc hβ {k}).toReal /
      (logMomentSlowScale c β k / (k : ℝ) ^ 2)) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (3 : ℕ)] with k hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hlog : 0 < Real.log k := Real.log_pos hk1
  rw [logMoment_atom hc hβ, ENNReal.toReal_ofReal
    (div_nonneg (logMomentWeight_nonneg hc k) (logMomentTotal_pos hc hβ).le)]
  simp only [logMomentWeight, show k ≠ 0 by omega, ↓reduceIte, logMomentSlowScale,
    show ¬(k : ℝ) < 3 by exact_mod_cast (show ¬k < 3 by omega), logMomentRawWeight,
    show ¬k < 3 by omega, logMomentTailConstant]
  field_simp [(logMomentTotal_pos hc hβ).ne', (logMomentSmallConstant_pos hc).ne',
    hc.ne', hk0.ne', hlog.ne', (Real.rpow_pos_of_pos hlog (1 + β)).ne']

/-- The explicit law satisfies the standing measurable subcritical Cauchy hypothesis. -/
theorem logMoment_isMeasurableSubcriticalCauchyOffspring {c β : ℝ}
    (hc : 0 < c) (hβ : 0 < β) :
    IsMeasurableSubcriticalCauchyOffspring (logMomentMeasure hc hβ) := by
  exact ⟨logMoment_mean_lt_one hc hβ, logMomentSlowScale c β,
    (fun _ hx => logMomentSlowScale_pos hc hβ hx),
    logMomentSlowScale_slowlyVarying hc hβ,
    (logMomentSlowScale_measurable c β).aemeasurable.restrict, logMoment_local hc hβ⟩

/-- The literal source-tail asymptotic of the explicit law. -/
theorem logMoment_tail {c β : ℝ} (hc : 0 < c) (hβ : 0 < β) :
    Tendsto (fun k : ℕ => (logMomentMeasure hc hβ {k}).toReal /
      (logMomentTailConstant c β / ((k : ℝ) ^ 2 * Real.log k ^ (1 + β))))
    atTop (𝓝 1) := by
  have hlocal := logMoment_local hc hβ
  apply hlocal.congr'
  filter_upwards [eventually_ge_atTop (3 : ℕ)] with k hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hlog : 0 < Real.log k := Real.log_pos hk1
  simp only [logMomentSlowScale,
    show ¬(k : ℝ) < 3 by exact_mod_cast (show ¬k < 3 by omega), ↓reduceIte]
  field_simp [hk0.ne', hlog.ne', (Real.rpow_pos_of_pos hlog (1 + β)).ne']

lemma logMoment_moment_eq {c β : ℝ} (hc : 0 < c) (hβ : 0 < β) {k : ℕ}
    (hk : 3 ≤ k) :
    (k : ℝ) * Real.log k * (logMomentMeasure hc hβ {k}).toReal =
      logMomentTailConstant c β * logTail β k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hlog : 0 < Real.log k := Real.log_pos hk1
  rw [logMoment_atom hc hβ, ENNReal.toReal_ofReal
    (div_nonneg (logMomentWeight_nonneg hc k) (logMomentTotal_pos hc hβ).le)]
  simp only [logMomentWeight, show k ≠ 0 by omega, ↓reduceIte, logMomentRawWeight,
    show ¬k < 3 by omega, logTail, show ¬(k : ℝ) < 3 by exact_mod_cast (show ¬k < 3 by omega),
    logMomentTailConstant]
  rw [show Real.log k ^ (1 + β) = Real.log k * Real.log k ^ β by
    rw [Real.rpow_add hlog, Real.rpow_one]]
  field_simp [(logMomentTotal_pos hc hβ).ne', (logMomentSmallConstant_pos hc).ne',
    hc.ne', hk0.ne', hlog.ne', (Real.rpow_pos_of_pos hlog β).ne']

/-- The logarithmic moment of every explicit law with `β > 1` is finite. -/
theorem logMoment_moment_summable_of_one_lt {c β : ℝ} (hc : 0 < c) (hβ : 1 < β) :
    Summable (fun k : ℕ =>
      (k : ℝ) * Real.log k * (logMomentMeasure hc (by linarith : 0 < β) {k}).toReal) := by
  have hmodel := (summable_logTail hβ).mul_left (logMomentTailConstant c β)
  apply hmodel.congr_cofinite
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop (3 : ℕ)] with k hk
  exact (logMoment_moment_eq hc (by linarith : 0 < β) hk).symm

/-- The logarithmic moment diverges throughout the source's range `0 < β ≤ 1`. -/
theorem logMoment_moment_not_summable {c β : ℝ} (hc : 0 < c) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ¬ Summable (fun k : ℕ =>
      (k : ℝ) * Real.log k * (logMomentMeasure hc hβ {k}).toReal) := by
  intro hs
  have hmodel : Summable (fun k : ℕ => logMomentTailConstant c β * logTail β k) := by
    apply hs.congr_cofinite
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop (3 : ℕ)] with k hk
    exact logMoment_moment_eq hc hβ hk
  have hsum : Summable (fun n : ℕ => logTail β n) :=
    (summable_mul_left_iff (logMomentTailConstant_pos hc hβ).ne').mp hmodel
  exact not_summable_logTail hβ.le hβ1 hsum

/-- In extended nonnegative form, the divergent logarithmic moment is `∞`. -/
theorem logMoment_moment_tsum_eq_top {c β : ℝ} (hc : 0 < c) (hβ : 0 < β)
    (hβ1 : β ≤ 1) :
    (∑' k : ℕ, ENNReal.ofReal
      ((k : ℝ) * Real.log k * (logMomentMeasure hc hβ {k}).toReal)) = ∞ := by
  change (∑' k : ℕ, (Real.toNNReal
    ((k : ℝ) * Real.log k * (logMomentMeasure hc hβ {k}).toReal) : ℝ≥0∞)) = ∞
  apply ENNReal.tsum_coe_eq_top_iff_not_summable_coe.mpr
  have heq : (fun k : ℕ => (Real.toNNReal
      ((k : ℝ) * Real.log k * (logMomentMeasure hc hβ {k}).toReal) : ℝ)) =
      (fun k : ℕ => (k : ℝ) * Real.log k * (logMomentMeasure hc hβ {k}).toReal) := by
    funext k
    exact Real.coe_toNNReal _ (by positivity)
  rw [heq]
  exact logMoment_moment_not_summable hc hβ hβ1

/-- An explicit subcritical law for each `0 < β ≤ 1` and `c > 0`. -/
theorem exists_logMoment_divergent {β c : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hc : 0 < c) :
    ∃ μ : Measure ℕ, ∃ c' : ℝ, ∃ _ : IsProbabilityMeasure μ,
      IsMeasurableSubcriticalCauchyOffspring μ ∧ 0 < c' ∧
      Tendsto (fun n : ℕ => (μ {n}).toReal /
        (c' / ((n : ℝ) ^ 2 * Real.log n ^ (1 + β)))) atTop (𝓝 1) ∧
      ¬ Summable (fun n : ℕ => (n : ℝ) * Real.log n * (μ {n}).toReal) ∧
      (∑' n : ℕ, ENNReal.ofReal ((n : ℝ) * Real.log n * (μ {n}).toReal)) = ∞ := by
  exact ⟨logMomentMeasure hc hβ, logMomentTailConstant c β,
    logMomentMeasure_isProbability hc hβ,
    logMoment_isMeasurableSubcriticalCauchyOffspring hc hβ,
    logMomentTailConstant_pos hc hβ, logMoment_tail hc hβ,
    logMoment_moment_not_summable hc hβ hβ1,
    logMoment_moment_tsum_eq_top hc hβ hβ1⟩


/-- In the source's convention `μₙ ∼ L(n) / n^(1+α)` with `α > 1`, the
logarithmic moment is finite.  Subcriticality and the probability structure are
retained exactly as in the source, although the comparison argument itself
uses only the local tail asymptotic. -/
theorem summable_logMoment_of_one_lt_alpha
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (_hsub : offspringMean μ < 1)
    {α : ℝ} (hα : 1 < α) {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal /
      (L n / (n : ℝ) ^ (1 + α))) atTop (𝓝 1)) :
    Summable (fun n : ℕ => (n : ℝ) * Real.log n * (μ {n}).toReal) := by
  let η : ℝ := (α - 1) / 4
  have hη : 0 < η := by dsimp [η]; linarith
  obtain ⟨C, hC, N, hN, hpotter⟩ := potter_bounds hpos hL hsv η hη
  let K : ℝ := C * L N / N ^ η
  have hLN : 0 < L N := hpos N hN
  have hK : 0 < K := div_pos (mul_pos hC hLN) (Real.rpow_pos_of_pos hN _)
  have hLbound : ∀ᶠ n : ℕ in atTop, L n ≤ K * (n : ℝ) ^ η := by
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop N] with n hn
    have hn0 : 0 < (n : ℝ) := hN.trans_le hn
    have hup := (hpotter N n le_rfl hn).2
    have hmul := (div_le_iff₀ hLN).mp hup
    calc
      L n ≤ C * ((n : ℝ) / N) ^ η * L N := hmul
      _ = K * (n : ℝ) ^ η := by
        rw [Real.div_rpow hn0.le hN.le]
        dsimp [K]
        field_simp [(Real.rpow_pos_of_pos hN η).ne']
  have hlogbound : ∀ᶠ n : ℕ in atTop, ‖Real.log n‖ ≤ (n : ℝ) ^ η := by
    have hcomp := (isLittleO_log_rpow_atTop hη).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))
    filter_upwards [hcomp.bound zero_lt_one] with n hn
    simpa only [Function.comp_apply, one_mul,
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)] using hn
  have hdominant : Summable (fun n : ℕ => 2 * K * (n : ℝ) ^ (-α + 2 * η)) := by
    apply Summable.mul_left
    apply Real.summable_nat_rpow.mpr
    dsimp [η]
    linarith
  apply hdominant.of_norm_bounded_eventually_nat
  filter_upwards [hLbound, hlogbound, eventually_ge_atTop (3 : ℕ),
    hlocal.eventually (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))] with n hLn hlog hn hratio
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hlogpos : 0 < Real.log n := Real.log_pos hn1
  have hden : 0 < L n / (n : ℝ) ^ (1 + α) :=
    div_pos (hpos _ hn0) (Real.rpow_pos_of_pos hn0 _)
  have hmass : (μ {n}).toReal < 2 * (L n / (n : ℝ) ^ (1 + α)) :=
    (div_lt_iff₀ hden).mp hratio
  have hlog' : Real.log n ≤ (n : ℝ) ^ η := by
    calc
      Real.log n = ‖Real.log n‖ := (Real.norm_of_nonneg hlogpos.le).symm
      _ ≤ (n : ℝ) ^ η := hlog
  have hnonneg : 0 ≤ (n : ℝ) * Real.log n * (μ {n}).toReal := by positivity
  rw [Real.norm_of_nonneg hnonneg]
  calc
    (n : ℝ) * Real.log n * (μ {n}).toReal ≤
        (n : ℝ) * (n : ℝ) ^ η * (2 * (K * (n : ℝ) ^ η / (n : ℝ) ^ (1 + α))) := by
      calc
        (n : ℝ) * Real.log n * (μ {n}).toReal ≤
            ((n : ℝ) * (n : ℝ) ^ η) * (μ {n}).toReal := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hlog' hn0.le) ENNReal.toReal_nonneg
        _ ≤ (n : ℝ) * (n : ℝ) ^ η *
            (2 * (K * (n : ℝ) ^ η / (n : ℝ) ^ (1 + α))) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hn0.le (Real.rpow_nonneg hn0.le _))
          calc
            (μ {n}).toReal ≤ 2 * (L n / (n : ℝ) ^ (1 + α)) := hmass.le
            _ ≤ 2 * ((K * (n : ℝ) ^ η) / (n : ℝ) ^ (1 + α)) := by
              gcongr
    _ = 2 * K * ((n : ℝ) ^ (1 + η) * (n : ℝ) ^ η / (n : ℝ) ^ (1 + α)) := by
      rw [show (n : ℝ) * (n : ℝ) ^ η = (n : ℝ) ^ (1 + η) by
        calc
          (n : ℝ) * (n : ℝ) ^ η = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ η := by rw [Real.rpow_one]
          _ = (n : ℝ) ^ (1 + η) := (Real.rpow_add hn0 1 η).symm]
      ring
    _ = 2 * K * (n : ℝ) ^ (-α + 2 * η) := by
      have hquot : (n : ℝ) ^ (1 + η + η) / (n : ℝ) ^ (1 + α) =
          (n : ℝ) ^ (-α + 2 * η) := by
        rw [← Real.rpow_sub hn0]
        congr 1
        ring
      rw [← Real.rpow_add hn0, hquot]

end
end SubcriticalCauchy.Bienayme
