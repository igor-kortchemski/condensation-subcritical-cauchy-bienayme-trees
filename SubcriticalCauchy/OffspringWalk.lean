module

public import SubcriticalCauchy.BienaymeSurvival
public import BGW.LocallyFinite.WalkLaw
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Algebra.BigOperators.Fin

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The iid offspring walk and its drift

The canonical infinite product of the offspring law constructs the actual iid
walk with increments `K-1`. Finite mean is sufficient for the almost sure law of
large numbers, and projection to its finite prefixes yields the finite-product
deviation estimates used in the paper. No law of large numbers or condensation
estimate is assumed as a hypothesis.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section

/-- The actual law of an infinite iid sequence of offspring counts. -/
def iidOffspringLaw (μ : Measure ℕ) [IsProbabilityMeasure μ] : Measure (ℕ → ℕ) :=
  Measure.infinitePi (fun _ : ℕ => μ)

instance iidOffspringLaw_isProbability (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (iidOffspringLaw μ) := inferInstanceAs
      (IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ => μ)))

/-- The real-valued version of the paper's integer increment. -/
def offspringIncrement (k : ℕ) : ℝ := (k : ℝ) - 1

@[fun_prop] theorem measurable_offspringIncrement : Measurable offspringIncrement :=
  measurable_of_countable _

/-- The walk after `n` steps; the empty sum is zero. -/
def walkSum (ω : ℕ → ℕ) (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range n, ((ω i : ℤ) - 1)

def walkAverage (n : ℕ) (ω : ℕ → ℕ) : ℝ := (walkSum ω n : ℝ) / (n : ℝ)

def finiteWalkSum {n : ℕ} (ω : Fin n → ℕ) : ℤ := ∑ i, ((ω i : ℤ) - 1)

def finiteWalkAverage (n : ℕ) (ω : Fin n → ℕ) : ℝ :=
  (finiteWalkSum ω : ℝ) / (n : ℝ)

theorem walkSum_cast (ω : ℕ → ℕ) (n : ℕ) :
    (walkSum ω n : ℝ) = ∑ i ∈ Finset.range n, offspringIncrement (ω i) := by
  simp [walkSum, offspringIncrement]

theorem finiteWalkSum_eq_stepWord_sum {n : ℕ} (ω : Fin n → ℕ) :
    finiteWalkSum ω = (BGW.stepWord ω).sum := by
  simp [finiteWalkSum, BGW.stepWord, List.sum_ofFn]

theorem finiteWalkSum_prefix (ω : ℕ → ℕ) (n : ℕ) :
    finiteWalkSum (fun i : Fin n => ω i) = walkSum ω n := by
  unfold finiteWalkSum walkSum
  exact (Finset.sum_range (n := n) (fun i : ℕ => (ω i : ℤ) - 1)).symm

theorem finiteWalkAverage_prefix (ω : ℕ → ℕ) (n : ℕ) :
    finiteWalkAverage n (fun i : Fin n => ω i) = walkAverage n ω := by
  rw [finiteWalkAverage, walkAverage, finiteWalkSum_prefix]

theorem integrable_natCast (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hfin : offspringMean μ ≠ ∞) : Integrable (fun k : ℕ => (k : ℝ)) μ := by
  simpa only [ENNReal.toReal_natCast] using
    integrable_toReal_of_lintegral_ne_top
      (measurable_of_countable (fun k : ℕ => (k : ℝ≥0∞))).aemeasurable hfin

theorem integral_natCast (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    ∫ k : ℕ, (k : ℝ) ∂μ = (offspringMean μ).toReal := by
  simpa only [ENNReal.toReal_natCast, offspringMean] using
    integral_toReal
      (measurable_of_countable (fun k : ℕ => (k : ℝ≥0∞))).aemeasurable
      (Eventually.of_forall fun k => ENNReal.natCast_lt_top k)

theorem integrable_offspringIncrement (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hfin : offspringMean μ ≠ ∞) : Integrable offspringIncrement μ :=
  (integrable_natCast μ hfin).sub (integrable_const 1)

theorem integral_offspringIncrement (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hfin : offspringMean μ ≠ ∞) :
    ∫ k, offspringIncrement k ∂μ = (offspringMean μ).toReal - 1 := by
  unfold offspringIncrement
  rw [integral_sub (integrable_natCast μ hfin) (integrable_const 1), integral_natCast]
  simp

theorem iid_coordinate_hasLaw (μ : Measure ℕ) [IsProbabilityMeasure μ] (i : ℕ) :
    HasLaw (fun ω : ℕ → ℕ => ω i) μ (iidOffspringLaw μ) :=
  ⟨(measurable_pi_apply i).aemeasurable,
    Measure.infinitePi_map_eval (fun _ : ℕ => μ) i⟩

theorem iid_increment_hasLaw (μ : Measure ℕ) [IsProbabilityMeasure μ] (i : ℕ) :
    HasLaw (fun ω : ℕ → ℕ => offspringIncrement (ω i))
      (μ.map offspringIncrement) (iidOffspringLaw μ) := by
  exact (hasLaw_map measurable_offspringIncrement.aemeasurable).comp (iid_coordinate_hasLaw μ i)

theorem iid_coordinates_independent (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    iIndepFun (fun i (ω : ℕ → ℕ) => ω i) (iidOffspringLaw μ) :=
  iIndepFun_infinitePi (X := fun _ : ℕ => (id : ℕ → ℕ)) (fun _ => measurable_id)

theorem iid_increments_independent (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    iIndepFun (fun i (ω : ℕ → ℕ) => offspringIncrement (ω i)) (iidOffspringLaw μ) :=
  iIndepFun_infinitePi (X := fun _ : ℕ => offspringIncrement)
    (fun _ => measurable_offspringIncrement)

@[fun_prop] theorem measurable_walkAverage (n : ℕ) : Measurable (walkAverage n) := by
  have hf : walkAverage n = fun ω : ℕ → ℕ =>
      (∑ i ∈ Finset.range n, offspringIncrement (ω i)) / (n : ℝ) := by
    funext ω
    rw [walkAverage, walkSum_cast]
  rw [hf]
  exact (Finset.measurable_fun_sum (Finset.range n) fun i _ =>
    measurable_offspringIncrement.comp (measurable_pi_apply i)).div_const _

/-- The source walk has almost sure drift `m-1`. This needs finite mean only. -/
theorem walkAverage_ae_tendsto (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hfin : offspringMean μ ≠ ∞) :
    ∀ᵐ ω ∂iidOffspringLaw μ,
      Tendsto (fun n => walkAverage n ω) atTop (𝓝 ((offspringMean μ).toReal - 1)) := by
  have hint : Integrable (fun ω : ℕ → ℕ => offspringIncrement (ω 0)) (iidOffspringLaw μ) :=
    (iid_coordinate_hasLaw μ 0).integrable_comp (integrable_offspringIncrement μ hfin)
  have hident (i : ℕ) : IdentDistrib
      (fun ω : ℕ → ℕ => offspringIncrement (ω i))
      (fun ω : ℕ → ℕ => offspringIncrement (ω 0)) (iidOffspringLaw μ) (iidOffspringLaw μ) :=
    (iid_increment_hasLaw μ i).identDistrib (iid_increment_hasLaw μ 0)
  have hmean : (∫ ω, offspringIncrement (ω 0) ∂iidOffspringLaw μ) =
      (offspringMean μ).toReal - 1 := by
    calc
      (∫ ω, offspringIncrement (ω 0) ∂iidOffspringLaw μ) =
          ∫ k, offspringIncrement k ∂μ :=
        (iid_coordinate_hasLaw μ 0).integral_comp
          measurable_offspringIncrement.aestronglyMeasurable
      _ = _ := integral_offspringIncrement μ hfin
  have h := strong_law_ae_real (fun i (ω : ℕ → ℕ) => offspringIncrement (ω i))
    hint (fun _ _ hij => (iid_increments_independent μ).indepFun hij) hident
  simpa only [walkAverage, walkSum_cast, hmean] using h

theorem walkAverage_tendstoInMeasure (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hfin : offspringMean μ ≠ ∞) :
    TendstoInMeasure (iidOffspringLaw μ) walkAverage atTop
      (fun _ => (offspringMean μ).toReal - 1) :=
  tendstoInMeasure_of_tendsto_ae (fun n => (measurable_walkAverage n).aestronglyMeasurable)
    (walkAverage_ae_tendsto μ hfin)

/-- A finite prefix of the constructed iid sequence has the exact finite product law. -/
theorem iidOffspringLaw_map_prefix (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) :
    (iidOffspringLaw μ).map (fun ω (i : Fin n) => ω i) =
      Measure.pi (fun _ : Fin n => μ) := by
  have hind : iIndepFun (fun (i : Fin n) (ω : ℕ → ℕ) => ω i) (iidOffspringLaw μ) :=
    iIndepFun.precomp Fin.val_injective (iid_coordinates_independent μ)
  have h := (iIndepFun_iff_map_fun_eq_pi_map
    (fun i : Fin n => (measurable_pi_apply (i : ℕ)).aemeasurable)).mp hind
  simpa only [iidOffspringLaw, Measure.infinitePi_map_eval] using h

theorem iidOffspringLaw_prefix_event (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (n : ℕ) (A : Set (Fin n → ℕ)) :
    iidOffspringLaw μ ((fun ω (i : Fin n) => ω i) ⁻¹' A) =
      Measure.pi (fun _ : Fin n => μ) A := by
  have hp : Measurable (fun (ω : ℕ → ℕ) (i : Fin n) => ω i) :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply (i : ℕ)
  calc
    iidOffspringLaw μ ((fun ω (i : Fin n) => ω i) ⁻¹' A) =
        (iidOffspringLaw μ).map (fun ω (i : Fin n) => ω i) A :=
      (Measure.map_apply (μ := iidOffspringLaw μ) hp (Set.to_countable A).measurableSet).symm
    _ = _ := by rw [iidOffspringLaw_map_prefix]

/-- The actual finite-product weak law for the paper's walk. -/
theorem finiteWalkAverage_deviation_tendsto_zero (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hfin : offspringMean μ ≠ ∞) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n => μ)).real
      {ω | ε ≤ |finiteWalkAverage n ω - ((offspringMean μ).toReal - 1)|})
      atTop (𝓝 0) := by
  have h := (tendstoInMeasure_iff_measureReal_norm.mp
    (walkAverage_tendstoInMeasure μ hfin)) ε hε
  simp only [Real.norm_eq_abs] at h
  have heq (n : ℕ) : (iidOffspringLaw μ).real
      {ω | ε ≤ |walkAverage n ω - ((offspringMean μ).toReal - 1)|} =
      (Measure.pi (fun _ : Fin n => μ)).real
        {ω | ε ≤ |finiteWalkAverage n ω - ((offspringMean μ).toReal - 1)|} := by
    have hset : {ω : ℕ → ℕ | ε ≤ |walkAverage n ω - ((offspringMean μ).toReal - 1)|} =
        (fun ω (i : Fin n) => ω i) ⁻¹'
          {ω | ε ≤ |finiteWalkAverage n ω - ((offspringMean μ).toReal - 1)|} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, finiteWalkAverage_prefix]
    rw [Measure.real, Measure.real, hset, iidOffspringLaw_prefix_event μ n]
  exact h.congr' (Eventually.of_forall heq)

/-- The quantity compared with the largest degree in the paper: minus the sum
of `n-1` increments, normalized by `n`. -/
def previousWalkAverage (n : ℕ) (ω : ℕ → ℕ) : ℝ :=
  -(walkSum ω (n - 1) : ℝ) / (n : ℝ)

def finitePreviousWalkAverage (n : ℕ) (ω : Fin (n - 1) → ℕ) : ℝ :=
  -(finiteWalkSum ω : ℝ) / (n : ℝ)

theorem finitePreviousWalkAverage_prefix (ω : ℕ → ℕ) (n : ℕ) :
    finitePreviousWalkAverage n (fun i : Fin (n - 1) => ω i) = previousWalkAverage n ω := by
  rw [finitePreviousWalkAverage, previousWalkAverage, finiteWalkSum_prefix]

theorem previousWalkAverage_ae_tendsto (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hfin : offspringMean μ ≠ ∞) :
    ∀ᵐ ω ∂iidOffspringLaw μ,
      Tendsto (fun n => previousWalkAverage n ω) atTop (𝓝 (1 - (offspringMean μ).toReal)) := by
  have hratio : Tendsto (fun n : ℕ => ((n - 1 : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
    have heq : (fun n : ℕ => 1 - 1 / (n : ℝ)) =ᶠ[atTop]
        (fun n : ℕ => ((n - 1 : ℕ) : ℝ) / (n : ℝ)) := by
      filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      rw [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
      field_simp
    simpa only [sub_zero] using h.congr' heq
  filter_upwards [walkAverage_ae_tendsto μ hfin] with ω hω
  have hs := ((hω.comp (tendsto_sub_atTop_nat 1)).neg).mul hratio
  have heq : (fun n : ℕ => -(walkAverage (n - 1) ω) *
      (((n - 1 : ℕ) : ℝ) / (n : ℝ))) =ᶠ[atTop]
      (fun n => previousWalkAverage n ω) := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
    have hk : (((n - 1 : ℕ) : ℝ)) ≠ 0 := by
      exact_mod_cast (show n - 1 ≠ 0 by omega)
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    dsimp only [walkAverage, previousWalkAverage]
    field_simp [hk, hn0]
  simpa only [neg_sub, mul_one] using hs.congr' heq

@[fun_prop] theorem measurable_previousWalkAverage (n : ℕ) :
    Measurable (previousWalkAverage n) := by
  have hf : previousWalkAverage n = fun ω : ℕ → ℕ =>
      -(∑ i ∈ Finset.range (n - 1), offspringIncrement (ω i)) / (n : ℝ) := by
    funext ω
    rw [previousWalkAverage, walkSum_cast]
  rw [hf]
  exact ((Finset.measurable_fun_sum (Finset.range (n - 1)) fun i _ =>
    measurable_offspringIncrement.comp (measurable_pi_apply i)).neg).div_const _

theorem previousWalkAverage_tendstoInMeasure (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hfin : offspringMean μ ≠ ∞) :
    TendstoInMeasure (iidOffspringLaw μ) previousWalkAverage atTop
      (fun _ => 1 - (offspringMean μ).toReal) :=
  tendstoInMeasure_of_tendsto_ae
    (fun n => (measurable_previousWalkAverage n).aestronglyMeasurable)
    (previousWalkAverage_ae_tendsto μ hfin)

/-- The finite-product weak law with exactly the paper's `n-1` summands and
normalization by `n`, needed for the largest-degree condensation conclusion. -/
theorem finitePreviousWalkAverage_deviation_tendsto_zero
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hfin : offspringMean μ ≠ ∞)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin (n - 1) => μ)).real
      {ω | ε ≤ |finitePreviousWalkAverage n ω - (1 - (offspringMean μ).toReal)|})
      atTop (𝓝 0) := by
  have h := (tendstoInMeasure_iff_measureReal_norm.mp
    (previousWalkAverage_tendstoInMeasure μ hfin)) ε hε
  simp only [Real.norm_eq_abs] at h
  have heq (n : ℕ) : (iidOffspringLaw μ).real
      {ω | ε ≤ |previousWalkAverage n ω - (1 - (offspringMean μ).toReal)|} =
      (Measure.pi (fun _ : Fin (n - 1) => μ)).real
        {ω | ε ≤ |finitePreviousWalkAverage n ω - (1 - (offspringMean μ).toReal)|} := by
    have hset : {ω : ℕ → ℕ | ε ≤ |previousWalkAverage n ω - (1 - (offspringMean μ).toReal)|} =
        (fun ω (i : Fin (n - 1)) => ω i) ⁻¹'
          {ω | ε ≤ |finitePreviousWalkAverage n ω - (1 - (offspringMean μ).toReal)|} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, finitePreviousWalkAverage_prefix]
    rw [Measure.real, Measure.real, hset, iidOffspringLaw_prefix_event μ (n - 1)]
  exact h.congr' (Eventually.of_forall heq)

/-- Source equation `eq:proba`: the iid walk divided by `n(m-1)` tends to one
in probability. Subcriticality makes the drift nonzero; finite mean and the
actual finite-product weak law are proved inputs rather than extra assumptions. -/
theorem finiteWalk_driftRatio_deviation_tendsto_zero
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ < 1)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n => μ)).real
      {ω | ε ≤ |(finiteWalkSum ω : ℝ) /
        ((n : ℝ) * ((offspringMean μ).toReal - 1)) - 1|}) atTop (𝓝 0) := by
  have hfin : offspringMean μ ≠ ∞ := ne_top_of_lt (hm.trans ENNReal.one_lt_top)
  have hmR : (offspringMean μ).toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hfin ENNReal.one_ne_top).mpr hm
  let d : ℝ := (offspringMean μ).toReal - 1
  have hd : d ≠ 0 := (sub_neg.mpr hmR).ne
  have h := finiteWalkAverage_deviation_tendsto_zero μ hfin
    (mul_pos hε (abs_pos.mpr hd))
  have hset (n : ℕ) :
      {ω : Fin n → ℕ | ε ≤ |(finiteWalkSum ω : ℝ) / ((n : ℝ) * d) - 1|} =
        {ω | ε * |d| ≤ |finiteWalkAverage n ω - d|} := by
    ext ω
    change (ε ≤ |(finiteWalkSum ω : ℝ) / ((n : ℝ) * d) - 1|) ↔
      (ε * |d| ≤ |finiteWalkAverage n ω - d|)
    have halgebra : (finiteWalkSum ω : ℝ) / ((n : ℝ) * d) - 1 =
        (finiteWalkAverage n ω - d) / d := by
      rw [sub_div, finiteWalkAverage, div_div, div_self hd]
    rw [halgebra, abs_div, le_div_iff₀ (abs_pos.mpr hd)]
  have heq (n : ℕ) : (Measure.pi (fun _ : Fin n => μ)).real
      {ω | ε * |d| ≤ |finiteWalkAverage n ω - d|} =
      (Measure.pi (fun _ : Fin n => μ)).real
        {ω | ε ≤ |(finiteWalkSum ω : ℝ) / ((n : ℝ) * d) - 1|} :=
    congrArg (fun A : Set (Fin n → ℕ) => (Measure.pi (fun _ : Fin n => μ)).real A)
      (hset n).symm
  exact h.congr' (Eventually.of_forall heq)

end
end SubcriticalCauchy.Bienayme
