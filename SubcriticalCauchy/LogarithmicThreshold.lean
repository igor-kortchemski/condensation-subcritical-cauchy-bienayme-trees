module

public import SubcriticalCauchy.SurvivalLog
public import Mathlib.Analysis.SpecificLimits.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Sampling a positive tail at logarithmic thresholds

The logarithmic rate of a sequence determines whether `n * q (ceil (a * log n))`
vanishes or diverges. Ceiling rounding is explicit. These analytic results are
applied to actual Bienaymé survival probabilities in BienaymeForestLog.
-/

@[expose] public section

open Filter
open scoped Topology

namespace SubcriticalCauchy

theorem tendsto_log_nat_atTop : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem tendsto_ceil_log_div_log {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ => (⌈a * Real.log n⌉₊ : ℝ) / Real.log n)
      atTop (𝓝 a) :=
  (tendsto_nat_ceil_mul_div_atTop ha).comp tendsto_log_nat_atTop

/-- The logarithmic exponent after sampling at a rounded logarithmic index. -/
theorem tendsto_log_product_ceil_log {q : ℕ → ℝ} {L a : ℝ}
    (hq : ∀ n, 0 < q n) (ha : 0 < a)
    (hrate : Tendsto (fun n : ℕ => Real.log (q n) / (n : ℝ)) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => Real.log ((n : ℝ) * q ⌈a * Real.log n⌉₊) / Real.log n)
      atTop (𝓝 (1 + a * L)) := by
  have hk : Tendsto (fun n : ℕ => ⌈a * Real.log n⌉₊) atTop atTop :=
    tendsto_nat_ceil_atTop.comp (tendsto_log_nat_atTop.const_mul_atTop ha)
  have ht := (tendsto_const_nhds (x := (1 : ℝ))).add
    ((hrate.comp hk).mul (tendsto_ceil_log_div_log ha.le))
  have heq : (fun n : ℕ => 1 +
      (Real.log (q ⌈a * Real.log n⌉₊) / (⌈a * Real.log n⌉₊ : ℝ)) *
        ((⌈a * Real.log n⌉₊ : ℝ) / Real.log n)) =ᶠ[atTop]
      (fun n : ℕ => Real.log ((n : ℝ) * q ⌈a * Real.log n⌉₊) / Real.log n) := by
    filter_upwards [eventually_gt_atTop (1 : ℕ), hk.eventually_gt_atTop 0] with n hn hkn
    have hnR : 1 < (n : ℝ) := by exact_mod_cast hn
    have hn0 : (n : ℝ) ≠ 0 := (lt_trans zero_lt_one hnR).ne'
    have hlog : Real.log (n : ℝ) ≠ 0 := (Real.log_pos hnR).ne'
    have hk0 : (⌈a * Real.log n⌉₊ : ℝ) ≠ 0 := by exact_mod_cast hkn.ne'
    rw [Real.log_mul hn0 (hq _).ne']
    field_simp
  simpa only [Function.comp_apply, mul_comm L a] using ht.congr' heq

theorem tendsto_zero_of_log_div_log_neg {f : ℕ → ℝ} {L : ℝ}
    (hf : ∀ᶠ n in atTop, 0 < f n) (hL : L < 0)
    (h : Tendsto (fun n : ℕ => Real.log (f n) / Real.log n) atTop (𝓝 L)) :
    Tendsto f atTop (𝓝 0) := by
  have hlog : Tendsto (fun n => Real.log (f n)) atTop atBot := by
    apply (h.neg_mul_atTop hL tendsto_log_nat_atTop).congr'
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
    exact div_mul_cancel₀ _ (Real.log_pos (by exact_mod_cast hn)).ne'
  apply (Real.tendsto_exp_atBot.comp hlog).congr'
  filter_upwards [hf] with n hn
  exact Real.exp_log hn

theorem tendsto_atTop_of_log_div_log_pos {f : ℕ → ℝ} {L : ℝ}
    (hf : ∀ᶠ n in atTop, 0 < f n) (hL : 0 < L)
    (h : Tendsto (fun n : ℕ => Real.log (f n) / Real.log n) atTop (𝓝 L)) :
    Tendsto f atTop atTop := by
  have hlog : Tendsto (fun n => Real.log (f n)) atTop atTop := by
    apply (h.pos_mul_atTop hL tendsto_log_nat_atTop).congr'
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
    exact div_mul_cancel₀ _ (Real.log_pos (by exact_mod_cast hn)).ne'
  apply (Real.tendsto_exp_atTop.comp hlog).congr'
  filter_upwards [hf] with n hn
  exact Real.exp_log hn

theorem product_ceil_log_tendsto_zero {q : ℕ → ℝ} {L a : ℝ}
    (hq : ∀ n, 0 < q n) (ha : 0 < a) (hexp : 1 + a * L < 0)
    (hrate : Tendsto (fun n : ℕ => Real.log (q n) / (n : ℝ)) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => (n : ℝ) * q ⌈a * Real.log n⌉₊) atTop (𝓝 0) := by
  apply tendsto_zero_of_log_div_log_neg _ hexp (tendsto_log_product_ceil_log hq ha hrate)
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact mul_pos (Nat.cast_pos.mpr hn) (hq _)

theorem product_ceil_log_tendsto_atTop {q : ℕ → ℝ} {L a : ℝ}
    (hq : ∀ n, 0 < q n) (ha : 0 < a) (hexp : 0 < 1 + a * L)
    (hrate : Tendsto (fun n : ℕ => Real.log (q n) / (n : ℝ)) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => (n : ℝ) * q ⌈a * Real.log n⌉₊) atTop atTop := by
  apply tendsto_atTop_of_log_div_log_pos _ hexp (tendsto_log_product_ceil_log hq ha hrate)
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact mul_pos (Nat.cast_pos.mpr hn) (hq _)

end SubcriticalCauchy
