module

public import SubcriticalCauchy.LateProofs.P45Tail
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SumIntegralComparisons

/-!
# An explicit logarithmic Cauchy-type offspring law

Positive weights start at three and decay like `1/(k² log(k+e)²)`. A small
multiplier and a mass at zero make the normalized mean strictly subcritical.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace SubcriticalCauchy.Bienayme

noncomputable section

/-- Unnormalized positive tail weight before the small subcriticality multiplier. -/
noncomputable def c1RawWeight (k : ℕ) : ℝ :=
  if k < 3 then 0 else ((k : ℝ) ^ 2 * Real.log ((k : ℝ) + Real.exp 1) ^ 2)⁻¹

/-- The real first moment of the positive raw weights. -/
noncomputable def c1RawMoment : ℝ := ∑' k : ℕ, c1RawWeight k * (k : ℝ)

/-- A multiplier making the raw first moment less than one. -/
noncomputable def c1SmallConstant : ℝ := (1 + c1RawMoment)⁻¹

/-- Weights, with mass one at zero before normalization. -/
noncomputable def c1WitnessWeight (k : ℕ) : ℝ :=
  if k = 0 then 1 else c1SmallConstant * c1RawWeight k

/-- Total unnormalized mass. -/
noncomputable def c1WitnessTotal : ℝ := ∑' k : ℕ, c1WitnessWeight k

private lemma c1RawWeight_nonneg (k : ℕ) : 0 ≤ c1RawWeight k := by
  unfold c1RawWeight
  split_ifs <;> positivity

private lemma c1WitnessWeight_nonneg (k : ℕ) : 0 ≤ c1WitnessWeight k := by
  unfold c1WitnessWeight
  have hM : 0 ≤ c1RawMoment := by
    apply tsum_nonneg
    intro k
    exact mul_nonneg (c1RawWeight_nonneg k) (Nat.cast_nonneg k)
  have hc : 0 ≤ c1SmallConstant := by
    unfold c1SmallConstant
    positivity
  split_ifs with hk
  · norm_num
  · exact mul_nonneg hc (c1RawWeight_nonneg k)

lemma c1RawMoment_summable : Summable (fun k : ℕ => c1RawWeight k * (k : ℝ)) := by
  let f : ℝ → ℝ := fun x => x⁻¹ / Real.log x ^ 2
  have hfanti : AntitoneOn f (Set.Ici 3) := by
    intro x hx y hy hxy
    change (3 : ℝ) ≤ x at hx
    change (3 : ℝ) ≤ y at hy
    have hx0 : 0 < x := by linarith [hx]
    have hy0 : 0 < y := hx0.trans_le hxy
    have hx1 : 1 < x := by linarith [hx]
    have hy1 : 1 < y := hx1.trans_le hxy
    have hlogx : 0 < Real.log x := Real.log_pos hx1
    have hlogy : 0 < Real.log y := Real.log_pos hy1
    have hlog : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
    have hden : x * Real.log x ^ 2 ≤ y * Real.log y ^ 2 := by gcongr
    dsimp only [f]
    rw [show x⁻¹ / Real.log x ^ 2 = (x * Real.log x ^ 2)⁻¹ by
      field_simp [hx0.ne', hlogx.ne']]
    rw [show y⁻¹ / Real.log y ^ 2 = (y * Real.log y ^ 2)⁻¹ by
      field_simp [hy0.ne', hlogy.ne']]
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hden
  have hfsum : Summable (fun k : ℕ => f k) := by
    apply hfanti.summable_of_integrableOn_Ioi
    · exact integrableOn_inv_div_log_sq_Ioi (by norm_num)
    · intro x hx
      change (3 : ℝ) < x at hx
      have hx1 : 1 < x := by linarith [hx]
      have hlog : 0 < Real.log x := Real.log_pos hx1
      dsimp only [f]
      positivity
  rw [← summable_nat_add_iff 3]
  refine Summable.of_nonneg_of_le (f := fun n : ℕ => f ((n + 3 : ℕ) : ℝ))
    (g := fun n : ℕ => c1RawWeight (n + 3) * ((n + 3 : ℕ) : ℝ))
    (fun n => mul_nonneg (c1RawWeight_nonneg _) (Nat.cast_nonneg _)) (fun n => ?_)
    ((summable_nat_add_iff 3).mpr hfsum)
  have hk0 : 0 < ((n + 3 : ℕ) : ℝ) := by positivity
  have hk1 : 1 < ((n + 3 : ℕ) : ℝ) := by
    have : 1 < n + 3 := by omega
    exact_mod_cast this
  have hlog : 0 < Real.log (((n + 3 : ℕ) : ℝ)) := Real.log_pos hk1
  have hlog' : 0 < Real.log (((n + 3 : ℕ) : ℝ) + Real.exp 1) := by
    apply Real.log_pos
    linarith [Real.exp_pos (1 : ℝ)]
  have hle : Real.log (((n + 3 : ℕ) : ℝ)) ≤
      Real.log (((n + 3 : ℕ) : ℝ) + Real.exp 1) := by
    apply Real.log_le_log hk0
    linarith [Real.exp_pos (1 : ℝ)]
  have hleft : (((n + 3 : ℕ) : ℝ) ^ 2 *
      Real.log (((n + 3 : ℕ) : ℝ) + Real.exp 1) ^ 2)⁻¹ * ((n + 3 : ℕ) : ℝ) =
      1 / (((n + 3 : ℕ) : ℝ) * Real.log (((n + 3 : ℕ) : ℝ) + Real.exp 1) ^ 2) := by
    field_simp [hk0.ne', hlog'.ne']
  have hright : f (n + 3) =
      1 / (((n + 3 : ℕ) : ℝ) * Real.log (((n + 3 : ℕ) : ℝ)) ^ 2) := by
    dsimp only [f]
    push_cast
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  simp only [c1RawWeight, show ¬n + 3 < 3 by omega, ↓reduceIte]
  push_cast at hleft hright ⊢
  rw [hleft, hright]
  push_cast at hlog hlog' hle
  have hden : ((n : ℝ) + 3) * Real.log ((n : ℝ) + 3) ^ 2 ≤
      ((n : ℝ) + 3) * Real.log ((n : ℝ) + 3 + Real.exp 1) ^ 2 := by
    apply mul_le_mul_of_nonneg_left ((sq_le_sq₀ hlog.le hlog'.le).mpr hle)
    positivity
  exact one_div_le_one_div_of_le (mul_pos (by positivity) (sq_pos_of_pos hlog)) hden

lemma c1RawWeight_summable : Summable c1RawWeight := by
  apply Summable.of_nonneg_of_le (f := fun k : ℕ => c1RawWeight k * (k : ℝ))
    c1RawWeight_nonneg (fun k => ?_) c1RawMoment_summable
  by_cases hk : k < 3
  · simp [c1RawWeight, hk]
  · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
      have : 1 ≤ k := by omega
      exact_mod_cast this
    have hnonneg := c1RawWeight_nonneg k
    exact le_mul_of_one_le_right hnonneg hk1

lemma c1WitnessWeight_summable : Summable c1WitnessWeight := by
  rw [← summable_nat_add_iff 1]
  apply ((summable_nat_add_iff 1).mpr
    (c1RawWeight_summable.mul_left c1SmallConstant)).congr
  intro n
  simp [c1WitnessWeight]

lemma c1WitnessTotal_pos : 0 < c1WitnessTotal := by
  calc
    0 < c1WitnessWeight 0 := by simp [c1WitnessWeight]
    _ ≤ c1WitnessTotal := c1WitnessWeight_summable.le_tsum 0
      (fun j _ => c1WitnessWeight_nonneg j)


lemma c1WitnessTotal_enn :
    (∑' k : ℕ, ENNReal.ofReal (c1WitnessWeight k)) = ENNReal.ofReal c1WitnessTotal := by
  exact (ENNReal.ofReal_tsum_of_nonneg c1WitnessWeight_nonneg c1WitnessWeight_summable).symm

/-- The explicit normalized offspring PMF. -/
noncomputable def c1WitnessPMF : PMF ℕ :=
  PMF.normalize (fun k : ℕ => ENNReal.ofReal (c1WitnessWeight k))
    (by
      rw [c1WitnessTotal_enn]
      exact (ENNReal.ofReal_pos.mpr c1WitnessTotal_pos).ne')
    c1WitnessWeight_summable.tsum_ofReal_ne_top

/-- The explicit normalized offspring law. -/
noncomputable def c1WitnessMeasure : Measure ℕ := c1WitnessPMF.toMeasure

instance c1WitnessMeasure_isProbability : IsProbabilityMeasure c1WitnessMeasure := by
  unfold c1WitnessMeasure
  infer_instance

private lemma c1Witness_atom (k : ℕ) :
    c1WitnessMeasure {k} = ENNReal.ofReal (c1WitnessWeight k / c1WitnessTotal) := by
  rw [c1WitnessMeasure, c1WitnessPMF, PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton k), PMF.normalize_apply,
    c1WitnessTotal_enn, ← ENNReal.ofReal_inv_of_pos c1WitnessTotal_pos,
    ← ENNReal.ofReal_mul (c1WitnessWeight_nonneg k)]
  rfl

private lemma c1WitnessMean :
    offspringMean c1WitnessMeasure =
      ENNReal.ofReal ((c1SmallConstant / c1WitnessTotal) * c1RawMoment) := by
  have hc : 0 ≤ c1SmallConstant / c1WitnessTotal :=
    div_nonneg (by
      have hM : 0 ≤ c1RawMoment := by
        apply tsum_nonneg
        intro k
        exact mul_nonneg (c1RawWeight_nonneg k) (Nat.cast_nonneg k)
      unfold c1SmallConstant
      positivity) c1WitnessTotal_pos.le
  have hterm (k : ℕ) : (k : ℝ≥0∞) * c1WitnessMeasure {k} =
      ENNReal.ofReal ((c1SmallConstant / c1WitnessTotal) * (c1RawWeight k * (k : ℝ))) := by
    rw [c1Witness_atom, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg k)]
    congr 1
    by_cases hk : k = 0
    · subst k
      simp [c1WitnessWeight, c1RawWeight]
    · simp only [c1WitnessWeight, hk, ↓reduceIte]
      field_simp [c1WitnessTotal_pos.ne']
  rw [offspringMean, lintegral_countable']
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun k => mul_nonneg hc (mul_nonneg (c1RawWeight_nonneg k) (Nat.cast_nonneg k)))
    (c1RawMoment_summable.mul_left (c1SmallConstant / c1WitnessTotal))]
  rw [tsum_mul_left]
  rfl

private lemma c1WitnessTotal_one_le : 1 ≤ c1WitnessTotal := by
  calc
    1 = c1WitnessWeight 0 := by simp [c1WitnessWeight]
    _ ≤ c1WitnessTotal := c1WitnessWeight_summable.le_tsum 0
      (fun j _ => c1WitnessWeight_nonneg j)

private lemma c1Witness_mean_lt_one : offspringMean c1WitnessMeasure < 1 := by
  rw [c1WitnessMean, ENNReal.ofReal_lt_one]
  have hM : 0 ≤ c1RawMoment := by
    apply tsum_nonneg
    intro k
    exact mul_nonneg (c1RawWeight_nonneg k) (Nat.cast_nonneg k)
  have hnum : c1SmallConstant * c1RawMoment < 1 := by
    unfold c1SmallConstant
    rw [inv_mul_eq_div]
    exact (div_lt_one (by linarith)).mpr (by linarith)
  rw [div_mul_eq_mul_div, div_lt_one c1WitnessTotal_pos]
  exact hnum.trans_le c1WitnessTotal_one_le


/-- Exact normalized slowly varying scale of the witness. -/
noncomputable def c1WitnessSlowScale (x : ℝ) : ℝ :=
  (c1SmallConstant / c1WitnessTotal) / Real.log (x + Real.exp 1) ^ 2

private lemma c1SmallConstant_pos : 0 < c1SmallConstant := by
  have hM : 0 ≤ c1RawMoment := by
    apply tsum_nonneg
    intro k
    exact mul_nonneg (c1RawWeight_nonneg k) (Nat.cast_nonneg k)
  unfold c1SmallConstant
  positivity

private lemma c1WitnessSlowScale_pos {x : ℝ} (hx : 0 < x) :
    0 < c1WitnessSlowScale x := by
  apply div_pos (div_pos c1SmallConstant_pos c1WitnessTotal_pos)
  apply pow_pos
  apply Real.log_pos
  have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
  linarith

private lemma c1WitnessSlowScale_measurable : Measurable c1WitnessSlowScale := by
  unfold c1WitnessSlowScale
  fun_prop

private lemma c1WitnessSlowScale_slowlyVarying :
    IsSlowlyVaryingAtTop c1WitnessSlowScale := by
  intro t ht
  have hlog := tendsto_log_mul_add_div_log_add_atTop ht (Real.exp 1) (Real.exp 1)
  have hpow := (hlog.inv₀ one_ne_zero).pow 2
  have hpow0 : Tendsto (fun x : ℝ =>
      (Real.log (t * x + Real.exp 1) / Real.log (x + Real.exp 1))⁻¹ ^ 2)
      atTop (𝓝 1) := by simpa using hpow
  apply hpow0.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have h₁ : 0 < Real.log (t * x + Real.exp 1) := by
    apply Real.log_pos
    have := mul_pos ht hx
    have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
    linarith
  have h₂ : 0 < Real.log (x + Real.exp 1) := by
    apply Real.log_pos
    have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
    linarith
  dsimp only [c1WitnessSlowScale]
  field_simp [c1SmallConstant_pos.ne', c1WitnessTotal_pos.ne', h₁.ne', h₂.ne']

private lemma c1Witness_local :
    Tendsto (fun k : ℕ => (c1WitnessMeasure {k}).toReal /
      (c1WitnessSlowScale k / (k : ℝ) ^ 2)) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (3 : ℕ)] with k hk
  have hk0 : k ≠ 0 := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hlog : 0 < Real.log ((k : ℝ) + Real.exp 1) := by
    apply Real.log_pos
    have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
    linarith
  rw [c1Witness_atom, ENNReal.toReal_ofReal
    (div_nonneg (c1WitnessWeight_nonneg k) c1WitnessTotal_pos.le)]
  simp only [c1WitnessWeight, hk0, ↓reduceIte, c1WitnessSlowScale, c1RawWeight,
    show ¬k < 3 by omega, ↓reduceIte]
  field_simp [c1WitnessTotal_pos.ne', hkR.ne', hlog.ne', c1SmallConstant_pos.ne']

/-- The explicit logarithmic law satisfies the measurable subcritical Cauchy hypothesis. -/
theorem c1Witness_isMeasurableSubcriticalCauchyOffspring :
    IsMeasurableSubcriticalCauchyOffspring c1WitnessMeasure := by
  exact ⟨c1Witness_mean_lt_one, c1WitnessSlowScale,
    (fun _ hx => c1WitnessSlowScale_pos hx), c1WitnessSlowScale_slowlyVarying,
    c1WitnessSlowScale_measurable.aemeasurable.restrict, c1Witness_local⟩

end
end SubcriticalCauchy.Bienayme
