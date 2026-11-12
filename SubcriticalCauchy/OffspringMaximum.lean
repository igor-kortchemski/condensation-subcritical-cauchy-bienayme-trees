module

public import SubcriticalCauchy.DegreeStatistics
public import SubcriticalCauchy.OffspringWalk

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Sublinear maxima of iid offspring counts with finite mean

The actual iid offspring sequence has a sublinear maximum. We derive the
individual-coordinate rate from the proved strong law, then use an elementary
finite-prefix maximum argument. Projection to finite product measures gives the
probability estimates used for the second-degree condensation conclusion.

This finite-mean route does not prove the source's Fréchet extreme-value limit;
that stronger obligation and the one-big-jump comparison remain separate.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section

def finiteMaximumAverage (n : ℕ) (ω : Fin n → ℕ) : ℝ :=
  (listMaxDegree (List.ofFn ω) : ℝ) / (n : ℝ)

def prefixMaximumAverage (n : ℕ) (ω : ℕ → ℕ) : ℝ :=
  finiteMaximumAverage n (fun i : Fin n => ω i)

theorem finiteMaximumAverage_nonneg (n : ℕ) (ω : Fin n → ℕ) :
    0 ≤ finiteMaximumAverage n ω :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem prefixMaximumAverage_nonneg (n : ℕ) (ω : ℕ → ℕ) :
    0 ≤ prefixMaximumAverage n ω := finiteMaximumAverage_nonneg _ _

theorem walkSum_succ (ω : ℕ → ℕ) (n : ℕ) :
    walkSum ω (n + 1) = walkSum ω n + ((ω n : ℤ) - 1) := by
  simp only [walkSum, Finset.sum_range_succ]

/-- Convergence of the partial averages forces each individual count to be
sublinear. This is deterministic; no independence is assumed here. -/
theorem coordinate_div_succ_tendsto_zero_of_walkAverage
    (ω : ℕ → ℕ) {d : ℝ}
    (hω : Tendsto (fun n => walkAverage n ω) atTop (𝓝 d)) :
    Tendsto (fun n : ℕ => (ω n : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hsmall : Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  have hratio : Tendsto (fun n : ℕ => (n : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 1) := by
    have heq (n : ℕ) : 1 - 1 / ((n + 1 : ℕ) : ℝ) =
        (n : ℝ) / ((n + 1 : ℕ) : ℝ) := by
      have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      rw [Nat.cast_add, Nat.cast_one] at hn
      rw [Nat.cast_add, Nat.cast_one]
      field_simp [hn]
      ring
    simpa only [sub_zero] using
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hsmall).congr
        (fun n => heq n)
  have hsucc : Tendsto (fun n => walkAverage (n + 1) ω) atTop (𝓝 d) :=
    (tendsto_add_atTop_iff_nat 1).mpr hω
  have h := (hsucc.sub (hω.mul hratio)).add hsmall
  have heq : (fun n : ℕ => walkAverage (n + 1) ω -
      walkAverage n ω * ((n : ℝ) / ((n + 1 : ℕ) : ℝ)) +
        1 / ((n + 1 : ℕ) : ℝ)) =ᶠ[atTop]
      (fun n : ℕ => (ω n : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hp0 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    dsimp only [walkAverage]
    rw [walkSum_succ]
    simp only [Int.cast_add, Int.cast_sub, Int.cast_natCast, Int.cast_one]
    field_simp [hn0, hp0]
    ring
  simpa only [mul_one, sub_self, add_zero] using h.congr' heq

/-- A nonnegative sequence with sublinear coordinates has a sublinear finite
prefix maximum. Finite initial prefixes contribute only a vanishing constant. -/
theorem prefixMaximumAverage_tendsto_zero_of_coordinate
    (ω : ℕ → ℕ)
    (hω : Tendsto (fun n : ℕ => (ω n : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => prefixMaximumAverage n ω) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hω.eventually (gt_mem_nhds (half_pos hε)))
  let M : ℕ := (Finset.range N).sup ω
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    ((tendsto_const_div_atTop_nhds_zero_nat (M : ℝ)).eventually
      (gt_mem_nhds (half_pos hε)))
  refine ⟨max N₀ 1, fun n hn => ?_⟩
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one ((le_max_right N₀ 1).trans hn)
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hnpos
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (prefixMaximumAverage_nonneg n ω)]
  let ds := List.ofFn (fun i : Fin n => ω i)
  have hne : ds.toFinset.Nonempty := by
    refine ⟨ω 0, List.mem_toFinset.mpr ?_⟩
    exact List.mem_ofFn.mpr ⟨⟨0, hnpos⟩, rfl⟩
  obtain ⟨d, hd, hmax⟩ := Finset.exists_mem_eq_sup ds.toFinset hne id
  have hmax' : listMaxDegree ds = d := hmax
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hd)
  change (listMaxDegree ds : ℝ) / (n : ℝ) < ε
  rw [hmax']
  by_cases hiN : (i : ℕ) < N
  · have hiM : ω i ≤ M := Finset.le_sup (Finset.mem_range.mpr hiN)
    calc
      (ω i : ℝ) / (n : ℝ) ≤ (M : ℝ) / (n : ℝ) :=
        div_le_div_of_nonneg_right (Nat.cast_le.mpr hiM) hnR.le
      _ < ε / 2 := hN₀ n ((le_max_left N₀ 1).trans hn)
      _ < ε := half_lt_self hε
  · have hlate := hN (i : ℕ) (le_of_not_gt hiN)
    have hip : (((i : ℕ) + 1 : ℕ) : ℝ) ≤ (n : ℝ) :=
      Nat.cast_le.mpr (Nat.succ_le_of_lt i.isLt)
    have hnum : (ω i : ℝ) < ε / 2 * (n : ℝ) := by
      have hp : 0 < (((i : ℕ) + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos _)
      exact ((div_lt_iff₀ hp).mp hlate).trans_le
        (mul_le_mul_of_nonneg_left hip (half_pos hε).le)
    exact ((div_lt_iff₀ hnR).mpr hnum).trans (half_lt_self hε)

theorem offspringCoordinate_div_succ_ae_tendsto_zero
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hfin : offspringMean μ ≠ ∞) :
    ∀ᵐ ω ∂iidOffspringLaw μ,
      Tendsto (fun n : ℕ => (ω n : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  filter_upwards [walkAverage_ae_tendsto μ hfin] with ω hω
  exact coordinate_div_succ_tendsto_zero_of_walkAverage ω hω

theorem prefixMaximumAverage_ae_tendsto_zero
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hfin : offspringMean μ ≠ ∞) :
    ∀ᵐ ω ∂iidOffspringLaw μ,
      Tendsto (fun n => prefixMaximumAverage n ω) atTop (𝓝 0) := by
  filter_upwards [offspringCoordinate_div_succ_ae_tendsto_zero μ hfin] with ω hω
  exact prefixMaximumAverage_tendsto_zero_of_coordinate ω hω

@[fun_prop] theorem measurable_prefixMaximumAverage (n : ℕ) :
    Measurable (prefixMaximumAverage n) := by
  have hp : Measurable (fun (ω : ℕ → ℕ) (i : Fin n) => ω i) :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply (i : ℕ)
  exact (measurable_of_countable (finiteMaximumAverage n)).comp hp

theorem prefixMaximumAverage_tendstoInMeasure
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hfin : offspringMean μ ≠ ∞) :
    TendstoInMeasure (iidOffspringLaw μ) prefixMaximumAverage atTop (fun _ => 0) :=
  tendstoInMeasure_of_tendsto_ae
    (fun n => (measurable_prefixMaximumAverage n).aestronglyMeasurable)
    (prefixMaximumAverage_ae_tendsto_zero μ hfin)

/-- The largest of `n` actual iid offspring counts is sublinear in probability,
with no regular-variation assumption. -/
theorem finiteMaximumAverage_deviation_tendsto_zero
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hfin : offspringMean μ ≠ ∞)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n => μ)).real
      {ω | ε ≤ finiteMaximumAverage n ω}) atTop (𝓝 0) := by
  have h := (tendstoInMeasure_iff_measureReal_norm.mp
    (prefixMaximumAverage_tendstoInMeasure μ hfin)) ε hε
  have habs (n : ℕ) (ω : ℕ → ℕ) : |prefixMaximumAverage n ω| = prefixMaximumAverage n ω :=
    abs_of_nonneg (prefixMaximumAverage_nonneg n ω)
  simp_rw [sub_zero, Real.norm_eq_abs, habs] at h
  have heq (n : ℕ) : (iidOffspringLaw μ).real {ω | ε ≤ prefixMaximumAverage n ω} =
      (Measure.pi (fun _ : Fin n => μ)).real {ω | ε ≤ finiteMaximumAverage n ω} := by
    have hset : {ω : ℕ → ℕ | ε ≤ prefixMaximumAverage n ω} =
        (fun ω (i : Fin n) => ω i) ⁻¹' {ω | ε ≤ finiteMaximumAverage n ω} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, prefixMaximumAverage]
    rw [Measure.real, Measure.real, hset, iidOffspringLaw_prefix_event μ n]
  exact h.congr' (Eventually.of_forall heq)

/-- The same maximum, using `n-1` samples and normalization by `n`, as required
after removing the first largest jump from an `n`-step bridge. -/
def finitePreviousMaximumAverage (n : ℕ) (ω : Fin (n - 1) → ℕ) : ℝ :=
  (listMaxDegree (List.ofFn ω) : ℝ) / (n : ℝ)

def previousMaximumAverage (n : ℕ) (ω : ℕ → ℕ) : ℝ :=
  finitePreviousMaximumAverage n (fun i : Fin (n - 1) => ω i)

theorem previousMaximumAverage_nonneg (n : ℕ) (ω : ℕ → ℕ) :
    0 ≤ previousMaximumAverage n ω :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem previousMaximumAverage_ae_tendsto_zero
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hfin : offspringMean μ ≠ ∞) :
    ∀ᵐ ω ∂iidOffspringLaw μ,
      Tendsto (fun n => previousMaximumAverage n ω) atTop (𝓝 0) := by
  filter_upwards [prefixMaximumAverage_ae_tendsto_zero μ hfin] with ω hω
  apply squeeze_zero' (Eventually.of_forall fun n => previousMaximumAverage_nonneg n ω) _
    (hω.comp (tendsto_sub_atTop_nat 1))
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _)
    (Nat.cast_pos.mpr (show 0 < n - 1 by omega)) (Nat.cast_le.mpr (Nat.sub_le n 1))

@[fun_prop] theorem measurable_previousMaximumAverage (n : ℕ) :
    Measurable (previousMaximumAverage n) := by
  have hp : Measurable (fun (ω : ℕ → ℕ) (i : Fin (n - 1)) => ω i) :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply (i : ℕ)
  exact (measurable_of_countable (finitePreviousMaximumAverage n)).comp hp

theorem previousMaximumAverage_tendstoInMeasure
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hfin : offspringMean μ ≠ ∞) :
    TendstoInMeasure (iidOffspringLaw μ) previousMaximumAverage atTop (fun _ => 0) :=
  tendstoInMeasure_of_tendsto_ae
    (fun n => (measurable_previousMaximumAverage n).aestronglyMeasurable)
    (previousMaximumAverage_ae_tendsto_zero μ hfin)

theorem finitePreviousMaximumAverage_deviation_tendsto_zero
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hfin : offspringMean μ ≠ ∞)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin (n - 1) => μ)).real
      {ω | ε ≤ finitePreviousMaximumAverage n ω}) atTop (𝓝 0) := by
  have h := (tendstoInMeasure_iff_measureReal_norm.mp
    (previousMaximumAverage_tendstoInMeasure μ hfin)) ε hε
  have habs (n : ℕ) (ω : ℕ → ℕ) :
      |previousMaximumAverage n ω| = previousMaximumAverage n ω :=
    abs_of_nonneg (previousMaximumAverage_nonneg n ω)
  simp_rw [sub_zero, Real.norm_eq_abs, habs] at h
  have heq (n : ℕ) : (iidOffspringLaw μ).real {ω | ε ≤ previousMaximumAverage n ω} =
      (Measure.pi (fun _ : Fin (n - 1) => μ)).real
        {ω | ε ≤ finitePreviousMaximumAverage n ω} := by
    have hset : {ω : ℕ → ℕ | ε ≤ previousMaximumAverage n ω} =
        (fun ω (i : Fin (n - 1)) => ω i) ⁻¹'
          {ω | ε ≤ finitePreviousMaximumAverage n ω} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, previousMaximumAverage]
    rw [Measure.real, Measure.real, hset, iidOffspringLaw_prefix_event μ (n - 1)]
  exact h.congr' (Eventually.of_forall heq)

end
end SubcriticalCauchy.Bienayme
