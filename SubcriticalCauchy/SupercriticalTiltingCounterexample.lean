module

public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Order

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# A counterexample to the unqualified supercritical-tilting assertion

The paragraph following Proposition 2.1 asserts that every supercritical
offspring law is equivalent to a critical one. The deterministic law with two
offspring refutes that assertion without support qualifications: every
normalized law exponentially equivalent to it is again concentrated at two,
and hence has mean two.

This law does not satisfy the main heavy-tail assumption. The result below
does not refute Proposition 2.1 or the paper's main condensation results.
-/

@[expose] public section

namespace SubcriticalCauchy.SupercriticalTiltingCounterexample

open MeasureTheory

noncomputable section

/-- The real mass function of deterministic binary offspring. -/
def twoMass (k : ℕ) : ℝ := if k = 2 then 1 else 0

theorem twoMass_nonneg (k : ℕ) : 0 ≤ twoMass k := by
  by_cases hk : k = 2 <;> simp [twoMass, hk]

theorem twoMass_hasSum : HasSum twoMass 1 :=
  hasSum_ite_eq 2 1

theorem twoMass_mean : HasSum (fun k : ℕ => (k : ℝ) * twoMass k) 2 := by
  have h : HasSum (fun k : ℕ => (k : ℝ) * twoMass k) ((2 : ℝ) * twoMass 2) :=
    hasSum_single 2 (fun k hk => by simp [twoMass, hk])
  simpa [twoMass] using h

/-- The displayed masses are those of an actual probability measure. -/
theorem dirac_two_mass (k : ℕ) :
    ((Measure.dirac (2 : ℕ)) {k}).toReal = twoMass k := by
  by_cases hk : k = 2 <;> simp [twoMass, hk, eq_comm]

theorem dirac_two_isProbability : IsProbabilityMeasure (Measure.dirac (2 : ℕ)) :=
  inferInstance

/-- Positive exponential equivalence preserves the singleton support. -/
theorem equivalentMass_eq_zero {ν : ℕ → ℝ} {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r)
    (heq : ∀ k, twoMass k = a * r ^ k * ν k) (k : ℕ) (hk : k ≠ 2) : ν k = 0 := by
  have hprod : (a * r ^ k) * ν k = 0 :=
    (heq k).symm.trans (by simp [twoMass, hk])
  exact (mul_eq_zero.mp hprod).resolve_left (mul_pos ha (pow_pos hr k)).ne'

/-- Normalization forces the retained mass to be one. -/
theorem equivalentMass_two {ν : ℕ → ℝ} {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hnorm : HasSum ν 1)
    (heq : ∀ k, twoMass k = a * r ^ k * ν k) : ν 2 = 1 := by
  have h : HasSum ν (ν 2) := hasSum_single 2 (equivalentMass_eq_zero ha hr heq)
  exact h.unique hnorm

/-- Every normalized equivalent law is exactly the original mass function. -/
theorem equivalentMass_eq {ν : ℕ → ℝ} {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hnorm : HasSum ν 1)
    (heq : ∀ k, twoMass k = a * r ^ k * ν k) : ν = twoMass := by
  funext k
  by_cases hk : k = 2
  · subst k
    simpa [twoMass] using equivalentMass_two ha hr hnorm heq
  · simp [twoMass, hk, equivalentMass_eq_zero ha hr heq k hk]

theorem equivalentMass_mean {ν : ℕ → ℝ} {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hnorm : HasSum ν 1)
    (heq : ∀ k, twoMass k = a * r ^ k * ν k) :
    HasSum (fun k : ℕ => (k : ℝ) * ν k) 2 := by
  rw [equivalentMass_eq ha hr hnorm heq]
  exact twoMass_mean

/-- The exact positive exponential equivalence relation of Proposition 2.1
cannot relate this supercritical law to any normalized critical law. -/
theorem no_equivalent_critical_law :
    ¬ ∃ (ν : ℕ → ℝ) (a r : ℝ),
      0 < a ∧ 0 < r ∧ HasSum ν 1 ∧
      (∀ k, twoMass k = a * r ^ k * ν k) ∧
      HasSum (fun k : ℕ => (k : ℝ) * ν k) 1 := by
  rintro ⟨ν, a, r, ha, hr, hnorm, heq, hmean⟩
  have h : (2 : ℝ) = 1 := (equivalentMass_mean ha hr hnorm heq).unique hmean
  norm_num at h

/-- A normalized actual offspring law of mean two which has no equivalent
critical offspring law under the paper's stated equivalence relation. -/
theorem supercritical_equivalence_counterexample :
    IsProbabilityMeasure (Measure.dirac (2 : ℕ)) ∧
      (∀ k : ℕ, ((Measure.dirac (2 : ℕ)) {k}).toReal = twoMass k) ∧
      (∀ k, 0 ≤ twoMass k) ∧ HasSum twoMass 1 ∧
      HasSum (fun k : ℕ => (k : ℝ) * twoMass k) 2 ∧
      ¬ ∃ (ν : ℕ → ℝ) (a r : ℝ),
        0 < a ∧ 0 < r ∧ HasSum ν 1 ∧
        (∀ k, twoMass k = a * r ^ k * ν k) ∧
        HasSum (fun k : ℕ => (k : ℝ) * ν k) 1 :=
  ⟨dirac_two_isProbability, dirac_two_mass, twoMass_nonneg, twoMass_hasSum,
    twoMass_mean, no_equivalent_critical_law⟩

end
end SubcriticalCauchy.SupercriticalTiltingCounterexample
