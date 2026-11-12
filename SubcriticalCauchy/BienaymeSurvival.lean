module

public import BGW.LocallyFinite.GenerationLaw
public import BGW.LocallyFinite.Normalization
public import SubcriticalCauchy.SurvivalBounds
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Survival probabilities of the constructed Bienaymé tree

The height tail in Section 4 is realized as the probability of a nonempty
generation. The PGF recurrence follows from the branching law; the upper bound
uses the generation first moment and Markov's inequality. This establishes
probabilistic inputs, without assuming the survival recurrence or its bounds.
The ratio limit and geometric lower bound are proved in BienaymeSurvivalRatio;
the heavy-tail correction function is treated in `CorrectionAsymptotics`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section

open BGW BGW.LocallyFinite

/-- Having height at least `n`, including generation zero at the root. -/
def survivalEvent (n : ℕ) : Set Tree := {T | 0 < generationSize T n}

theorem survivalEvent_eq_compl_extinctBy (n : ℕ) : survivalEvent n = (extinctBy n)ᶜ := by
  ext T
  simp only [survivalEvent, Set.mem_ofPred_eq, Set.mem_compl_iff,
    ← generationSize_eq_zero_iff, Nat.pos_iff_ne_zero]

theorem measurableSet_survivalEvent (n : ℕ) : MeasurableSet (survivalEvent n) := by
  rw [survivalEvent_eq_compl_extinctBy]
  exact (measurableSet_extinctBy n).compl

/-- The extended nonnegative height-tail probability. -/
def survival (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) : ℝ≥0∞ :=
  bienaymeLaw μ (survivalEvent n)

/-- The offspring mean; infinite means are retained rather than totalized. -/
def offspringMean (μ : Measure ℕ) : ℝ≥0∞ := ∫⁻ k : ℕ, (k : ℝ≥0∞) ∂μ

theorem survival_le_one (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) :
    survival μ n ≤ 1 := prob_le_one

theorem survival_ne_top (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) :
    survival μ n ≠ ∞ := measure_ne_top _ _

theorem survival_eq_one_sub (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) :
    survival μ n = 1 - bienaymeLaw μ (extinctBy n) := by
  rw [survival, survivalEvent_eq_compl_extinctBy,
    measure_compl (measurableSet_extinctBy n) (measure_ne_top _ _), measure_univ]

theorem one_sub_survival (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) :
    1 - survival μ n = bienaymeLaw μ (extinctBy n) := by
  rw [survival_eq_one_sub]
  exact ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one

@[simp] theorem survival_zero (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    survival μ 0 = 1 := by
  rw [survival_eq_one_sub, bienaymeLaw_extinctBy_zero, tsub_zero]

/-- The exact branching/PGF recursion for the paper's survival probabilities. -/
theorem survival_succ (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) :
    survival μ (n + 1) = 1 - offspringGF μ (1 - survival μ n) := by
  rw [survival_eq_one_sub, bienaymeLaw_extinctBy_succ, one_sub_survival]

/-- The geometric upper bound follows from the expected generation size.
It is valid without a subcriticality or finite-mean hypothesis. -/
theorem survival_le_mean_pow (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) :
    survival μ n ≤ offspringMean μ ^ n := by
  have hmeas : Measurable (fun T : Tree => (generationSize T n : ℝ≥0∞)) :=
    (measurable_of_countable _).comp (measurable_generationSize n)
  have h := meas_le_lintegral₀ (μ := bienaymeLaw μ) hmeas.aemeasurable
    (s := survivalEvent n) (fun T hT => by
      have hp : 1 ≤ generationSize T n := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hT)
      exact_mod_cast hp)
  simpa only [survival, offspringMean, lintegral_generationSize] using h

/-- Subcriticality forces the actual height tail to zero. -/
theorem survival_toReal_tendsto_zero (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ < 1) :
    Tendsto (fun n => (survival μ n).toReal) atTop (𝓝 0) := by
  have hfin : offspringMean μ ≠ ∞ := ne_top_of_lt (hm.trans ENNReal.one_lt_top)
  apply tendsto_zero_of_geometric_upper_bound ENNReal.toReal_nonneg
    ((ENNReal.toReal_lt_toReal hfin ENNReal.one_ne_top).mpr hm)
    (fun _ => ENNReal.toReal_nonneg)
  intro n
  simpa only [ENNReal.toReal_pow] using
    ENNReal.toReal_mono (ENNReal.pow_ne_top hfin) (survival_le_mean_pow μ n)

/-- Real-valued offspring PGF, evaluated through the nonnegative PGF. Its
agreement with the paper's series is proved below on the probability interval. -/
def pgfReal (μ : Measure ℕ) (s : ℝ) : ℝ := (offspringGF μ (ENNReal.ofReal s)).toReal

theorem pgfReal_eq_tsum (μ : Measure ℕ) [IsProbabilityMeasure μ] (s : ℝ) (hs : 0 ≤ s) :
    pgfReal μ s = ∑' k : ℕ, (μ {k}).toReal * s ^ k := by
  rw [pgfReal, offspringGF, ENNReal.tsum_toReal_eq (fun k =>
    ENNReal.mul_ne_top (measure_ne_top μ {k})
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hs]

/-- On `[0,1]` this is a genuinely summable probability generating series. -/
theorem summable_pgfReal (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Summable (fun k : ℕ => (μ {k}).toReal * s ^ k) := by
  have hle : offspringGF μ (ENNReal.ofReal s) ≤ 1 := by
    calc
      _ ≤ offspringGF μ 1 := offspringGF_mono μ (by simpa using ENNReal.ofReal_le_ofReal hs1)
      _ = 1 := offspringGF_one μ
  have h := ENNReal.summable_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top hle)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hs0] using h

/-- The exact real-valued recursion, with the PGF's series semantics established. -/
theorem survival_toReal_succ (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) :
    (survival μ (n + 1)).toReal = 1 - pgfReal μ (1 - (survival μ n).toReal) := by
  have hsub : ENNReal.ofReal (1 - (survival μ n).toReal) = 1 - survival μ n := by
    rw [← ENNReal.toReal_one, ← ENNReal.toReal_sub_of_le (survival_le_one μ n)
      ENNReal.one_ne_top, ENNReal.ofReal_toReal]
    exact ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hgf : offspringGF μ (1 - survival μ n) ≤ 1 := by
    calc
      _ ≤ offspringGF μ 1 := offspringGF_mono μ tsub_le_self
      _ = 1 := offspringGF_one μ
  rw [survival_succ, ENNReal.toReal_sub_of_le hgf ENNReal.one_ne_top,
    ENNReal.toReal_one, pgfReal, hsub]

/-- The subcritical offspring law has an almost surely finite constructed tree.
The nondegeneracy needed by the general extinction theorem is derived here. -/
theorem ae_finite_of_subcritical (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ < 1) :
    ∀ᵐ T ∂bienaymeLaw μ, FiniteVertices T := by
  have hle : μ {1} ≤ offspringMean μ := by
    rw [offspringMean, lintegral_countable']
    simpa using (ENNReal.le_tsum (f := fun k : ℕ => (k : ℝ≥0∞) * μ {k}) 1)
  exact ae_finiteVertices_bienaymeLaw μ hm.le (ne_of_lt (hle.trans_lt hm))

end
end SubcriticalCauchy.Bienayme
