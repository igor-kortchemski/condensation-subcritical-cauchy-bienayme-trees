module

public import SubcriticalCauchy.BienaymeCorrection
public import SubcriticalCauchy.BienaymeTilting

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The paper's standing offspring assumption

This is the literal positive slow-variation/local-asymptotic assumption in the
Introduction. No measurability, stable-domain theorem, or asymptotic estimate is
bundled into it. Arguments at nonpositive real inputs and index zero are harmless
totalizations. Additional regularity needed for later uniform theorems must be
proved or explicitly resolved, not silently added here.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section
open BGW BGW.LocallyFinite

/-- The pointwise ratio definition of slow variation given in the Introduction. -/
def IsSlowlyVaryingAtTop (L : ℝ → ℝ) : Prop :=
  ∀ a : ℝ, 0 < a → Tendsto (fun x : ℝ => L (a * x) / L x) atTop (𝓝 1)

/-- Assumption `H_mu^loc` of the paper, without any extra analytic regularity. -/
def IsSubcriticalCauchyOffspring (μ : Measure ℕ) : Prop :=
  offspringMean μ < 1 ∧ ∃ L : ℝ → ℝ,
    (∀ x : ℝ, 0 < x → 0 < L x) ∧ IsSlowlyVaryingAtTop L ∧
      Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2)) atTop (𝓝 1)

theorem eventually_mass_pos (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsSubcriticalCauchyOffspring μ) : ∀ᶠ n in atTop, 0 < μ {n} := by
  obtain ⟨_, L, hLpos, _, hratio⟩ := hμ
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    hratio.eventually (lt_mem_nhds (show (0 : ℝ) < 1 from zero_lt_one))] with n hn hr
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hd : 0 < L n / (n : ℝ) ^ 2 := div_pos (hLpos _ hnR) (sq_pos_of_pos hnR)
  have hp : 0 < (μ {n}).toReal := (div_pos_iff_of_pos_right hd).mp hr
  exact (ENNReal.toReal_pos_iff.mp hp).1

theorem offspring_support_unbounded (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsSubcriticalCauchyOffspring μ) (N : ℕ) : ∃ k, N ≤ k ∧ 0 < μ {k} := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp (eventually_mass_pos μ hμ)
  exact ⟨max N M, le_max_left _ _, hM _ (le_max_right _ _)⟩

theorem branching_mass_pos (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsSubcriticalCauchyOffspring μ) : ∃ k : ℕ, 2 ≤ k ∧ 0 < μ {k} :=
  offspring_support_unbounded μ hμ 2

theorem offspringMean_pos_of_paper (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsSubcriticalCauchyOffspring μ) : 0 < offspringMean μ := by
  obtain ⟨k, hk, hμk⟩ := branching_mass_pos μ hμ
  have hk0 : 0 < (k : ℝ≥0∞) := by exact_mod_cast (show 0 < k by omega)
  have hle : (k : ℝ≥0∞) * μ {k} ≤ offspringMean μ := by
    rw [offspringMean, lintegral_countable']
    exact ENNReal.le_tsum (f := fun a : ℕ => (a : ℝ≥0∞) * μ {a}) k
  exact (ENNReal.mul_pos hk0.ne' hμk.ne').trans_le hle

/-- Every subcritical probability law has positive mass at zero. -/
theorem mass_zero_pos_of_subcritical (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ < 1) : 0 < μ {0} := by
  by_contra hnot
  have hz : μ {0} = 0 := le_antisymm (not_lt.mp hnot) bot_le
  have hle : 1 ≤ offspringMean μ := by
    rw [offspringMean, lintegral_countable', ← tsum_measure_singleton μ]
    apply ENNReal.tsum_le_tsum
    intro k
    cases k with
    | zero => simp [hz]
    | succ k =>
      have hk : (1 : ℝ≥0∞) ≤ (k + 1 : ℕ) := by exact_mod_cast Nat.succ_pos k
      simpa only [one_mul, mul_comm] using mul_le_mul_right hk (μ {k + 1})
  exact (not_le.mpr hm) hle

/-- A star with `k` leaves has `k+1` vertices. -/
def starTree (k : ℕ) : PlaneTree := PlaneTree.node (List.replicate k PlaneTree.leaf)

@[simp] theorem size_starTree (k : ℕ) : (starTree k).size = k + 1 := by
  simp [starTree, PlaneTree.size_node, Nat.add_comm]

theorem weight_starTree (μ : Measure ℕ) (k : ℕ) :
    PlaneTree.weight (fun j => μ {j}) (starTree k) = μ {k} * μ {0} ^ k := by
  simp [starTree, PlaneTree.weight_node]

/-- The local asymptotic forces all sufficiently large sizes to be admissible;
no separate aperiodicity assumption has been added. -/
theorem eventually_size_admissible (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsSubcriticalCauchyOffspring μ) :
    ∀ᶠ n in atTop, bienaymeLaw μ (sizeEvent n) ≠ 0 := by
  have hz := mass_zero_pos_of_subcritical μ hμ.1
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_mass_pos μ hμ)
  filter_upwards [eventually_ge_atTop (N + 1)] with n hn
  have hn0 : 0 < n := by omega
  apply (bienaymeLaw_sizeEvent_ne_zero_iff μ n).mpr
  refine ⟨starTree (n - 1), by simpa using Nat.sub_add_cancel hn0, ?_⟩
  rw [weight_starTree]
  exact mul_ne_zero (hN (n - 1) (by omega)).ne' (pow_ne_zero _ hz.ne')

/-- The positive correction and exact recurrence now follow from the actual
paper assumption. Its slow variation still requires the heavy-tail analysis. -/
theorem paper_survivalCorrection (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsSubcriticalCauchyOffspring μ) :
    (∀ q : ℝ, 0 < q → q ≤ 1 →
      0 < survivalCorrection μ q ∧ survivalCorrection μ q < (offspringMean μ).toReal) ∧
      ∀ n, (survival μ (n + 1)).toReal = (survival μ n).toReal *
        ((offspringMean μ).toReal - survivalCorrection μ (survival μ n).toReal) := by
  have hm : offspringMean μ ≠ ∞ := ne_top_of_lt (hμ.1.trans ENNReal.one_lt_top)
  constructor
  · intro q hq0 hq1
    exact ⟨survivalCorrection_pos μ hm (branching_mass_pos μ hμ) hq0 hq1,
      survivalCorrection_lt_mean μ hm (offspringMean_pos_of_paper μ hμ) hq0.le hq1⟩
  · exact survival_toReal_succ_correction μ hm

end
end SubcriticalCauchy.Bienayme
