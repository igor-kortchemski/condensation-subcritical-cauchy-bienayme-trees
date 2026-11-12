module

public import SubcriticalCauchy.OffspringWalk

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The centered lattice window in the one-big-jump argument

The cited half-open window is `(x,x+1]`. The manuscript's choice
`x = γ*n-1` selects endpoint zero; the bridge endpoint minus one requires
`x = γ*n-2`. These are exact arithmetic identities, not a local-deviation
or one-big-jump theorem.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace SubcriticalCauchy

theorem centered_lattice_window_zero (w : ℤ) (c : ℝ) :
    (w : ℝ) + c ∈ Ioc (c - 1) c ↔ w = 0 := by
  constructor
  · rintro ⟨hlo, hhi⟩
    have hlo' : (-1 : ℝ) < (w : ℝ) := by linarith
    have hhi' : (w : ℝ) ≤ 0 := by linarith
    have hloZ : (-1 : ℤ) < w := by exact_mod_cast hlo'
    have hhiZ : w ≤ 0 := by exact_mod_cast hhi'
    omega
  · rintro rfl
    constructor <;> norm_num

theorem centered_lattice_window_neg_one (w : ℤ) (c : ℝ) :
    (w : ℝ) + c ∈ Ioc (c - 2) (c - 1) ↔ w = -1 := by
  constructor
  · rintro ⟨hlo, hhi⟩
    have hlo' : (-2 : ℝ) < (w : ℝ) := by linarith
    have hhi' : (w : ℝ) ≤ -1 := by linarith
    have hloZ : (-2 : ℤ) < w := by exact_mod_cast hlo'
    have hhiZ : w ≤ -1 := by exact_mod_cast hhi'
    omega
  · rintro rfl
    simp only [Int.cast_neg, Int.cast_one]
    constructor <;> linarith

/-- Correcting the bounded offset preserves the linear lower threshold. -/
theorem corrected_window_eventually_ge {γ ε : ℝ} (h : ε < γ) :
    ∀ᶠ n : ℕ in atTop, ε * n ≤ γ * n - 2 := by
  have hg : 0 < γ - ε := sub_pos.mpr h
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 / (γ - ε))]
    with n hn
  have hmul := (div_le_iff₀ hg).mp hn
  nlinarith

namespace Bienayme

/-- The corrected window is exactly the actual finite iid walk bridge event. -/
theorem finiteWalk_centered_window {n : ℕ} (γ : ℝ) :
    {ω : Fin n → ℕ | (finiteWalkSum ω : ℝ) + γ * n ∈
      Ioc (γ * n - 2) (γ * n - 1)} = {ω | finiteWalkSum ω = -1} := by
  ext ω
  exact centered_lattice_window_neg_one (finiteWalkSum ω) (γ * n)

theorem finiteWalk_source_window {n : ℕ} (γ : ℝ) :
    {ω : Fin n → ℕ | (finiteWalkSum ω : ℝ) + γ * n ∈
      Ioc (γ * n - 1) (γ * n)} = {ω | finiteWalkSum ω = 0} := by
  ext ω
  exact centered_lattice_window_zero (finiteWalkSum ω) (γ * n)

end Bienayme
end SubcriticalCauchy
