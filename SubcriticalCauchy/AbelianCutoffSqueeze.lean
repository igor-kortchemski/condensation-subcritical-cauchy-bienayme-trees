module

public import Mathlib.Analysis.SpecificLimits.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A cutoff squeeze for an Abelian tail comparison

This is a conditional analytic helper. Fixed-scale floor and ceiling ratios,
together with upper and lower cutoff bounds, force a normalized ratio to tend
to one. The cutoff bounds themselves remain premises and must be discharged
for each application.
-/

@[expose] public section

open Filter
open scoped Topology

namespace SubcriticalCauchy

/-- Upper cutoffs with coefficient `1 + Cc` and lower cutoffs with coefficient
`1 - 1/M` determine the asymptotic ratio. The hypotheses concern actual values
of `U`, `B`, and `A`; no measurability or summability assumptions are needed. -/
theorem abelian_cutoff_ratio_tendsto_one {U B : ℝ → ℝ} {A : ℕ → ℝ} {C : ℝ}
    (hC : 0 < C) (hBpos : ∀ᶠ t : ℝ in atTop, 0 < B t)
    (hfloor : ∀ c : ℝ, 0 < c →
      Tendsto (fun t : ℝ => A ⌊c * t⌋₊ / B t) atTop (𝓝 1))
    (hceil : ∀ c : ℝ, 0 < c →
      Tendsto (fun t : ℝ => A ⌈c * t⌉₊ / B t) atTop (𝓝 1))
    (hupper : ∀ c : ℝ, 0 < c →
      ∀ᶠ t : ℝ in atTop, U t ≤ (1 + C * c) * A ⌊c * t⌋₊)
    (hlower : ∀ M : ℝ, 1 < M →
      ∀ᶠ t : ℝ in atTop, (1 - 1 / M) * A ⌈M * t⌉₊ ≤ U t) :
    Tendsto (fun t : ℝ => U t / B t) atTop (𝓝 1) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    have hgap : 0 < 1 - a := sub_pos.mpr ha
    let M : ℝ := max 2 (2 / (1 - a))
    have hM2 : 2 ≤ M := le_max_left _ _
    have hM1 : 1 < M := lt_of_lt_of_le (by norm_num) hM2
    have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM2
    have hMscale : 2 / (1 - a) ≤ M := le_max_right _ _
    have hprod : 2 ≤ M * (1 - a) := (div_le_iff₀ hgap).mp hMscale
    have hInv : 1 / M < 1 - a := (div_lt_iff₀ hMpos).mpr (by nlinarith)
    have hcoeff : a < 1 - 1 / M := by linarith
    have hlim : Tendsto (fun t : ℝ => (1 - 1 / M) * (A ⌈M * t⌉₊ / B t))
        atTop (𝓝 (1 - 1 / M)) := by
      simpa only [mul_one] using (hceil M hMpos).const_mul (1 - 1 / M)
    filter_upwards [hlim.eventually (lt_mem_nhds hcoeff), hlower M hM1, hBpos]
      with t ht hbound hBt
    apply ht.trans_le
    calc
      (1 - 1 / M) * (A ⌈M * t⌉₊ / B t) = ((1 - 1 / M) * A ⌈M * t⌉₊) / B t :=
        (mul_div_assoc _ _ _).symm
      _ ≤ U t / B t := div_le_div_of_nonneg_right hbound hBt.le
  · intro b hb
    let c : ℝ := (b - 1) / (2 * C)
    have hc : 0 < c := div_pos (sub_pos.mpr hb) (mul_pos (by norm_num) hC)
    have hCc : C * c = (b - 1) / 2 := by
      dsimp [c]
      field_simp [hC.ne']
    have hcoeff : 1 + C * c < b := by linarith
    have hlim : Tendsto (fun t : ℝ => (1 + C * c) * (A ⌊c * t⌋₊ / B t))
        atTop (𝓝 (1 + C * c)) := by
      simpa only [mul_one] using (hfloor c hc).const_mul (1 + C * c)
    filter_upwards [hlim.eventually (gt_mem_nhds hcoeff), hupper c hc, hBpos]
      with t ht hbound hBt
    apply lt_of_le_of_lt _ ht
    calc
      U t / B t ≤ ((1 + C * c) * A ⌊c * t⌋₊) / B t :=
        div_le_div_of_nonneg_right hbound hBt.le
      _ = (1 + C * c) * (A ⌊c * t⌋₊ / B t) := mul_div_assoc _ _ _

end SubcriticalCauchy
