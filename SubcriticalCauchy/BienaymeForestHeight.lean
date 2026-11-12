module

public import SubcriticalCauchy.BienaymeHeight
public import SubcriticalCauchy.ForestBounds
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Algebra.Order.Floor.Semiring

import Mathlib.Tactic.FieldSimp

/-!
# Independent Bienaymé forest heights

The product law constructs a forest of independent trees. The event that every
component has height below a threshold has probability `(1-q)^k`. This proves
the unconditioned forest estimates used in Proposition 4.3, independently of the
still open comparison with the forest below a conditioned tree's largest vertex.
The empty forest satisfies the universal event even at threshold zero.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section
open BGW.LocallyFinite

/-- A forest with `k` independent components, each with the constructed tree law. -/
def forestLaw (μ : Measure ℕ) [IsProbabilityMeasure μ] (k : ℕ) :
    Measure (Fin k → Tree) := Measure.pi (fun _ => bienaymeLaw μ)

instance forestLaw_isProbability (μ : Measure ℕ) [IsProbabilityMeasure μ] (k : ℕ) :
    IsProbabilityMeasure (forestLaw μ k) := inferInstanceAs
      (IsProbabilityMeasure (Measure.pi (fun _ : Fin k => bienaymeLaw μ)))

/-- Every component has height strictly less than `n`. -/
def forestBelow (k n : ℕ) : Set (Fin k → Tree) :=
  Set.univ.pi (fun _ => extinctBy n)

theorem mem_forestBelow (k n : ℕ) (F : Fin k → Tree) :
    F ∈ forestBelow k n ↔ ∀ i, F i ∉ survivalEvent n := by
  simp [forestBelow, survivalEvent_eq_compl_extinctBy]

theorem measurableSet_forestBelow (k n : ℕ) : MeasurableSet (forestBelow k n) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_extinctBy n)

/-- The finite-tree interpretation uses strict height, with no index shift. -/
theorem finite_forestBelow_iff (k n : ℕ) (F : Fin k → BGW.PlaneTree) :
    (fun i => (F i).toLocallyFinite) ∈ forestBelow k n ↔ ∀ i, height (F i) < n := by
  rw [mem_forestBelow]
  simp only [toLocallyFinite_mem_survivalEvent_iff, not_le]

/-- Exact independent-forest probability, including zero components. -/
theorem forestBelow_mass (μ : Measure ℕ) [IsProbabilityMeasure μ] (k n : ℕ) :
    forestLaw μ k (forestBelow k n) = (1 - survival μ n) ^ k := by
  rw [forestLaw, forestBelow, Measure.pi_pi]
  simp only [← one_sub_survival, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem forestBelow_mass_toReal (μ : Measure ℕ) [IsProbabilityMeasure μ] (k n : ℕ) :
    (forestLaw μ k (forestBelow k n)).toReal = (1 - (survival μ n).toReal) ^ k := by
  rw [forestBelow_mass, ENNReal.toReal_pow,
    ENNReal.toReal_sub_of_le (survival_le_one μ n) ENNReal.one_ne_top, ENNReal.toReal_one]

theorem forestAbove_mass_toReal (μ : Measure ℕ) [IsProbabilityMeasure μ] (k n : ℕ) :
    (forestLaw μ k (forestBelow k n)ᶜ).toReal = 1 - (1 - (survival μ n).toReal) ^ k := by
  rw [measure_compl (measurableSet_forestBelow k n) (measure_ne_top _ _),
    measure_univ, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
    ENNReal.toReal_one, forestBelow_mass_toReal]

/-- Union and exponential bounds for the actual independent forest. -/
theorem forest_height_bounds (μ : Measure ℕ) [IsProbabilityMeasure μ] (k n : ℕ) :
    (forestLaw μ k (forestBelow k n)ᶜ).toReal ≤ (k : ℝ) * (survival μ n).toReal ∧
      (forestLaw μ k (forestBelow k n)).toReal ≤
        Real.exp (-((k : ℝ) * (survival μ n).toReal)) := by
  have hq : (survival μ n).toReal ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using survival_le_one μ n)
  rw [forestAbove_mass_toReal, forestBelow_mass_toReal]
  exact ⟨(one_sub_pow_bounds ENNReal.toReal_nonneg hq k).2, one_sub_pow_le_exp hq k⟩

theorem forestBelow_tendsto_one (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (k h : ℕ → ℕ)
    (hprod : Tendsto (fun n : ℕ => (k n : ℝ) * (survival μ (h n)).toReal) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (forestLaw μ (k n) (forestBelow (k n) (h n))).toReal)
      atTop (𝓝 1) := by
  simp_rw [forestBelow_mass_toReal]
  exact tendsto_one_sub_pow_of_mul_tendsto_zero (fun _ => ENNReal.toReal_nonneg)
    (fun n : ℕ => ENNReal.toReal_le_of_le_ofReal zero_le_one
      (by simpa using survival_le_one μ (h n))) hprod

theorem forestBelow_tendsto_zero (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (k h : ℕ → ℕ)
    (hprod : Tendsto (fun n : ℕ => (k n : ℝ) * (survival μ (h n)).toReal) atTop atTop) :
    Tendsto (fun n : ℕ => (forestLaw μ (k n) (forestBelow (k n) (h n))).toReal)
      atTop (𝓝 0) := by
  simp_rw [forestBelow_mass_toReal]
  exact tendsto_one_sub_pow_of_mul_tendsto_atTop
    (fun n : ℕ => ENNReal.toReal_le_of_le_ofReal zero_le_one
      (by simpa using survival_le_one μ (h n))) hprod

theorem forestAbove_tendsto_one (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (k h : ℕ → ℕ)
    (hprod : Tendsto (fun n : ℕ => (k n : ℝ) * (survival μ (h n)).toReal) atTop atTop) :
    Tendsto (fun n : ℕ => (forestLaw μ (k n) (forestBelow (k n) (h n))ᶜ).toReal)
      atTop (𝓝 1) := by
  have heq (n : ℕ) : (forestLaw μ (k n) (forestBelow (k n) (h n))ᶜ).toReal =
      1 - (forestLaw μ (k n) (forestBelow (k n) (h n))).toReal := by
    rw [forestAbove_mass_toReal, forestBelow_mass_toReal]
  simp_rw [heq]
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
    (forestBelow_tendsto_zero μ k h hprod)

/-- Real height thresholds are interpreted by ceiling, as required for integer heights. -/
def forestBelowReal (k : ℕ) (h : ℝ) : Set (Fin k → Tree) := forestBelow k ⌈h⌉₊

theorem finite_forestBelowReal_iff (k : ℕ) (h : ℝ) (F : Fin k → BGW.PlaneTree) :
    (fun i => (F i).toLocallyFinite) ∈ forestBelowReal k h ↔
      ∀ i, (height (F i) : ℝ) < h := by
  simp only [forestBelowReal, finite_forestBelow_iff, Nat.lt_ceil]

theorem forestBelowReal_mass (μ : Measure ℕ) [IsProbabilityMeasure μ] (k : ℕ) (h : ℝ) :
    forestLaw μ k (forestBelowReal k h) = (1 - survival μ ⌈h⌉₊) ^ k :=
  forestBelow_mass μ k ⌈h⌉₊

theorem forestBelowReal_tendsto_one (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (k : ℕ → ℕ) (h : ℕ → ℝ)
    (hprod : Tendsto (fun n : ℕ => (k n : ℝ) * (survival μ ⌈h n⌉₊).toReal)
      atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (forestLaw μ (k n) (forestBelowReal (k n) (h n))).toReal)
      atTop (𝓝 1) := forestBelow_tendsto_one μ k (fun n : ℕ => ⌈h n⌉₊) hprod

theorem forestBelowReal_tendsto_zero (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (k : ℕ → ℕ) (h : ℕ → ℝ)
    (hprod : Tendsto (fun n : ℕ => (k n : ℝ) * (survival μ ⌈h n⌉₊).toReal)
      atTop atTop) :
    Tendsto (fun n : ℕ => (forestLaw μ (k n) (forestBelowReal (k n) (h n))).toReal)
      atTop (𝓝 0) := forestBelow_tendsto_zero μ k (fun n : ℕ => ⌈h n⌉₊) hprod

/-- Passing from `n` components to a fixed nonnegative fraction preserves a vanishing
expected number of tall trees. -/
theorem floor_mul_survival_tendsto_zero (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (h : ℕ → ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * (survival μ (h n)).toReal) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (⌊δ * n⌋₊ : ℝ) * (survival μ (h n)).toReal) atTop (𝓝 0) := by
  have hr := (tendsto_nat_floor_mul_div_atTop hδ).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have heq : (fun n : ℕ => ((⌊δ * n⌋₊ : ℝ) / n) *
      ((n : ℝ) * (survival μ (h n)).toReal)) =ᶠ[atTop]
      (fun n : ℕ => (⌊δ * n⌋₊ : ℝ) * (survival μ (h n)).toReal) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    field_simp [Nat.cast_ne_zero.mpr hn.ne']
  simpa using (hr.mul hp).congr' heq

/-- A positive fraction of the components also sees a diverging expected number
of tall trees. The strict positivity of the fraction is essential. -/
theorem floor_mul_survival_tendsto_atTop (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (h : ℕ → ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * (survival μ (h n)).toReal) atTop atTop) :
    Tendsto (fun n : ℕ => (⌊δ * n⌋₊ : ℝ) * (survival μ (h n)).toReal) atTop atTop := by
  have hr := (tendsto_nat_floor_mul_div_atTop hδ.le).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply (hr.pos_mul_atTop hδ hp).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  dsimp only [Function.comp_apply]
  field_simp [Nat.cast_ne_zero.mpr hn.ne']

/-- The vanishing-tail independent-forest limit in Proposition 4.3, with both
the paper's floor in the number of trees and the ceiling for real heights. -/
theorem forestBelowReal_floor_tendsto_one (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (h : ℕ → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * (survival μ ⌈h n⌉₊).toReal) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (forestLaw μ ⌊δ * n⌋₊
      (forestBelowReal ⌊δ * n⌋₊ (h n))).toReal) atTop (𝓝 1) :=
  forestBelowReal_tendsto_one μ _ h
    (floor_mul_survival_tendsto_zero μ (fun n : ℕ => ⌈h n⌉₊) hδ hp)

/-- The diverging-tail independent-forest limit in Proposition 4.3. -/
theorem forestBelowReal_floor_tendsto_zero (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (h : ℕ → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * (survival μ ⌈h n⌉₊).toReal) atTop atTop) :
    Tendsto (fun n : ℕ => (forestLaw μ ⌊δ * n⌋₊
      (forestBelowReal ⌊δ * n⌋₊ (h n))).toReal) atTop (𝓝 0) :=
  forestBelowReal_tendsto_zero μ _ h
    (floor_mul_survival_tendsto_atTop μ (fun n : ℕ => ⌈h n⌉₊) hδ hp)

end
end SubcriticalCauchy.Bienayme
