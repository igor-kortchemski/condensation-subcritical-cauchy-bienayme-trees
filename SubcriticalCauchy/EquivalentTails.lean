module

public import SubcriticalCauchy.CriticalTail
public import Mathlib.Topology.Algebra.InfiniteSum.Ring

import Mathlib.Tactic.Linarith

/-!
# Equivalence of summable series tails

Termwise asymptotic equivalence transfers to the corresponding series tails
when the reference sequence is nonnegative and eventually strictly positive.
The comparison sequence may have negative terms in a finite initial segment;
no monotonicity of either sequence is required.
-/

@[expose] public section

open Filter
open scoped Topology

namespace SubcriticalCauchy

/-- Pointwise multiplicative comparisons beyond an index transfer to genuine
summable tails. The constants need not be positive. -/
theorem tailMass_mul_bounds {T V : ℕ → ℝ}
    (hT : Summable T) (hV : Summable V) {n : ℕ} {a b : ℝ}
    (hlo : ∀ k : ℕ, n ≤ k → a * T k ≤ V k)
    (hhi : ∀ k : ℕ, n ≤ k → V k ≤ b * T k) :
    a * tailMass T n ≤ tailMass V n ∧ tailMass V n ≤ b * tailMass T n := by
  have hTtail := summable_tailMass hT n
  have hVtail := summable_tailMass hV n
  constructor
  · have h := (hTtail.mul_left a).tsum_le_tsum
      (fun j => hlo (n + j) (Nat.le_add_right _ _)) hVtail
    simpa only [tailMass, tsum_mul_left] using h
  · have h := hVtail.tsum_le_tsum
      (fun j => hhi (n + j) (Nat.le_add_right _ _)) (hTtail.mul_left b)
    simpa only [tailMass, tsum_mul_left] using h

/-- Equivalent summable terms have equivalent tails, provided the reference
terms are nonnegative everywhere and strictly positive at positive indices. -/
theorem tailMass_div_tendsto_one {T V : ℕ → ℝ}
    (hT : Summable T) (hV : Summable V) (h0 : ∀ n : ℕ, 0 ≤ T n)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < T n)
    (hratio : Tendsto (fun n : ℕ => V n / T n) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => tailMass V n / tailMass T n) atTop (𝓝 1) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hδ : 0 < ε / 2 := half_pos hε
  have hevent : ∀ᶠ k : ℕ in atTop, |V k / T k - 1| < ε / 2 := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp hratio (ε / 2) hδ)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  filter_upwards [eventually_ge_atTop (max N 1)] with n hn
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have htail : 0 < tailMass T n := tailMass_pos hT h0 hpos hn1
  have hbds : (1 - ε / 2) * tailMass T n ≤ tailMass V n ∧
      tailMass V n ≤ (1 + ε / 2) * tailMass T n := by
    apply tailMass_mul_bounds hT hV
    · intro k hnk
      have hkpos := hpos k (hn1.trans hnk)
      have hk := (abs_lt.mp (hN k (hnN.trans hnk))).1
      apply (le_div_iff₀ hkpos).mp
      linarith
    · intro k hnk
      have hkpos := hpos k (hn1.trans hnk)
      have hk := (abs_lt.mp (hN k (hnN.trans hnk))).2
      apply (div_le_iff₀ hkpos).mp
      linarith
  have hlo : 1 - ε / 2 ≤ tailMass V n / tailMass T n :=
    (le_div_iff₀ htail).mpr hbds.1
  have hhi : tailMass V n / tailMass T n ≤ 1 + ε / 2 :=
    (div_le_iff₀ htail).mpr hbds.2
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor <;> linarith

end SubcriticalCauchy
