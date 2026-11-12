module

public import SubcriticalCauchy.Centering

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniform linear-window estimates

Sublinear shifts are negligible uniformly above a positive linear threshold.
The actual paper centering and scale satisfy the required hypotheses by the
finite-mean proofs, without using their refined regular-variation asymptotics.
These deterministic bounds do not establish Berger's local probability estimate.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy

theorem sublinear_shift_uniform {s : ℕ → ℝ}
    (hs : Tendsto (fun n => s n / (n : ℝ)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ x : ℝ, ε * n ≤ x →
      |(x - s n) / x - 1| < δ := by
  have hsmall := hs.abs.eventually (gt_mem_nhds
    (show |(0 : ℝ)| < ε * δ by simpa only [abs_zero] using mul_pos hε hδ))
  filter_upwards [hsmall, eventually_gt_atTop (0 : ℕ)] with n hn hn0 x hx
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn0
  have hxR : 0 < x := (mul_pos hε hnR).trans_le hx
  simp only [abs_div, abs_of_pos hnR] at hn
  have hb := (div_lt_iff₀ hnR).mp hn
  have heq : (x - s n) / x - 1 = -(s n / x) := by
    field_simp
    ring
  rw [heq, abs_neg, abs_div, abs_of_pos hxR]
  apply (div_lt_iff₀ hxR).mpr
  have hmul := mul_le_mul_of_nonneg_left hx hδ.le
  nlinarith

theorem sublinear_scale_uniform_divergence {s a : ℕ → ℝ}
    (hs : Tendsto (fun n => s n / (n : ℝ)) atTop (𝓝 0))
    (ha : Tendsto (fun n => a n / (n : ℝ)) atTop (𝓝 0))
    (hapos : ∀ᶠ n in atTop, 0 < a n)
    {ε : ℝ} (hε : 0 < ε) (M : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ x : ℝ, ε * n ≤ x →
      M ≤ (x - s n) / a n := by
  let B : ℝ := |M| + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hMB : M ≤ B := by dsimp [B]; linarith [le_abs_self M]
  have hsmallS := hs.abs.eventually (gt_mem_nhds
    (show |(0 : ℝ)| < ε / 2 by simpa only [abs_zero] using half_pos hε))
  have hsmallA := (ha.mul_const B).eventually (gt_mem_nhds
    (show (0 : ℝ) * B < ε / 2 by simpa only [zero_mul] using half_pos hε))
  filter_upwards [hsmallS, hsmallA, hapos, eventually_gt_atTop (0 : ℕ)]
    with n hsN haN hap hn0 x hx
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn0
  simp only [abs_div, abs_of_pos hnR] at hsN
  have hsBound := (div_lt_iff₀ hnR).mp hsN
  simp only [div_mul_eq_mul_div] at haN
  have haBound := (div_lt_iff₀ hnR).mp haN
  apply (le_div_iff₀ hap).mpr
  have hMa := mul_le_mul_of_nonneg_right hMB hap.le
  nlinarith [le_abs_self (s n)]

theorem sublinear_scale_uniform_abs_divergence {s a : ℕ → ℝ}
    (hs : Tendsto (fun n => s n / (n : ℝ)) atTop (𝓝 0))
    (ha : Tendsto (fun n => a n / (n : ℝ)) atTop (𝓝 0))
    (hapos : ∀ᶠ n in atTop, 0 < a n)
    {ε : ℝ} (hε : 0 < ε) (M : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ x : ℝ, ε * n ≤ x →
      M ≤ |x - s n| / a n := by
  filter_upwards [sublinear_scale_uniform_divergence hs ha hapos hε M, hapos]
    with n hn hap x hx
  exact (hn x hx).trans (div_le_div_of_nonneg_right (le_abs_self _) hap.le)

namespace Bienayme

theorem paper_centering_shift_div_nat_tendsto_zero
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsSubcriticalCauchyOffspring μ) {a : ℕ → ℝ}
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) :
    Tendsto (fun n : ℕ =>
      (centering μ a n + (1 - (offspringMean μ).toReal) * n) / n) atTop (𝓝 0) := by
  have hfin := ne_top_of_lt (hμ.1.trans ENNReal.one_lt_top)
  have hb := (centering_div_nat_tendsto μ hfin (scaling_tendsto_atTop μ hμ ha)).add_const
    (1 - (offspringMean μ).toReal)
  have hlim : (offspringMean μ).toReal - 1 + (1 - (offspringMean μ).toReal) = 0 := by ring
  rw [hlim] at hb
  apply hb.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp

/-- Elementary uniform estimates preceding the external local-deviation theorem. -/
theorem paper_centering_uniform_windows
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsSubcriticalCauchyOffspring μ) {a : ℕ → ℝ}
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) {ε : ℝ} (hε : 0 < ε) :
    (∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, ∀ x : ℝ, ε * n ≤ x →
      |(x - (centering μ a n + (1 - (offspringMean μ).toReal) * n)) / x - 1| < δ) ∧
    (∀ M : ℝ, ∀ᶠ n : ℕ in atTop, ∀ x : ℝ, ε * n ≤ x →
      M ≤ |x - (centering μ a n + (1 - (offspringMean μ).toReal) * n)| / a n) := by
  have hs := paper_centering_shift_div_nat_tendsto_zero μ hμ ha
  have ha0 := scaling_div_nat_tendsto_zero μ hμ ha
  have hapos := (scaling_tendsto_atTop μ hμ ha).eventually_gt_atTop 0
  exact ⟨fun δ hδ => sublinear_shift_uniform hs hε hδ,
    fun M => sublinear_scale_uniform_abs_divergence hs ha0 hapos hε M⟩

end Bienayme
end SubcriticalCauchy
