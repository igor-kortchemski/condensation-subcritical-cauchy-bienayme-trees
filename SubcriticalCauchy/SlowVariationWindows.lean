module

public import SubcriticalCauchy.MultiplicativeUniformSlowVariation

import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ring

/-!
# Uniform slowly varying ratios on shrinking windows

The sequential uniform-convergence theorem gives uniformity simultaneously over
all sufficiently large base points. Consequently additive windows of width
`o(n)` are harmless uniformly over bases bounded below by a positive multiple
of `n`. No uniform ratio estimate is assumed in these proofs.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace SubcriticalCauchy

/-- Uniformity over arbitrary bases beyond a diverging lower bound, with a
relative window tending to zero. The statement uses the original values of `L`. -/
theorem slowlyVarying_uniform_relative_tail {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hfixed : ∀ a : ℝ, 0 < a →
      Tendsto (fun x : ℝ => L (a * x) / L x) atTop (𝓝 1))
    {z d : ℕ → ℝ} (hz : Tendsto z atTop atTop) (hd : Tendsto d atTop (𝓝 0)) :
    ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ x y : ℝ,
      z n ≤ x → |y / x - 1| ≤ |d n| → |L y / L x - 1| < τ := by
  classical
  intro τ hτ
  by_contra hnot
  have hbad (N : ℕ) : ∃ (n : ℕ) (x y : ℝ),
      N ≤ n ∧ z n ≤ x ∧ |y / x - 1| ≤ |d n| ∧ τ ≤ |L y / L x - 1| := by
    by_contra hnone
    apply hnot
    refine eventually_atTop.mpr ⟨N, ?_⟩
    intro n hn x y hbase hrel
    by_contra herr
    exact hnone ⟨n, x, y, hn, hbase, hrel, le_of_not_gt herr⟩
  choose ns xs ys hN hbase hrel herr using hbad
  have hns : Tendsto ns atTop atTop := tendsto_atTop_mono hN tendsto_id
  have hxs : Tendsto xs atTop atTop := tendsto_atTop_mono hbase (hz.comp hns)
  have herror : Tendsto (fun n => |ys n / xs n - 1|) atTop (𝓝 0) :=
    squeeze_zero (fun _ => abs_nonneg _) hrel
      (by simpa only [Function.comp_def, abs_zero] using (hd.comp hns).abs)
  have hcoef : Tendsto (fun n => ys n / xs n) atTop (𝓝 1) :=
    tendsto_iff_dist_tendsto_zero.mpr (by simpa only [Real.dist_eq] using herror)
  have hratio : Tendsto (fun n => L (ys n) / L (xs n)) atTop (𝓝 1) := by
    apply (slowlyVarying_uniform_sequential hpos hL hfixed hxs hcoef zero_lt_one).congr'
    filter_upwards [hxs.eventually_gt_atTop 0] with n hn
    rw [div_mul_cancel₀ _ hn.ne']
  have hzero : Tendsto (fun n => |L (ys n) / L (xs n) - 1|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero] using (hratio.sub_const 1).abs
  obtain ⟨n, hn⟩ := (hzero.eventually (gt_mem_nhds hτ)).exists
  exact (not_lt_of_ge (herr n)) hn

/-- The relative shrinking-window form at a prescribed diverging base sequence. -/
theorem slowlyVarying_uniform_relative_window {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hfixed : ∀ a : ℝ, 0 < a →
      Tendsto (fun x : ℝ => L (a * x) / L x) atTop (𝓝 1))
    {z d : ℕ → ℝ} (hz : Tendsto z atTop atTop) (hd : Tendsto d atTop (𝓝 0)) :
    ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ y : ℝ,
      |y / z n - 1| ≤ |d n| → |L y / L (z n) - 1| < τ := by
  intro τ hτ
  filter_upwards [slowlyVarying_uniform_relative_tail hpos hL hfixed hz hd τ hτ] with n hn
  intro y hy
  exact hn (z n) y le_rfl hy

/-- The additive `o(n)` windows in the paper's one-big-jump argument. The
uniformity ranges over every `x ≥ εn`, not only a single prescribed base. -/
theorem slowlyVarying_uniform_additive_window {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hfixed : ∀ a : ℝ, 0 < a →
      Tendsto (fun x : ℝ => L (a * x) / L x) atTop (𝓝 1))
    {ε : ℝ} (hε : 0 < ε) {η : ℕ → ℝ}
    (hη : Tendsto (fun n : ℕ => η n / (n : ℝ)) atTop (𝓝 0)) :
    ∀ τ : ℝ, 0 < τ → ∀ᶠ n : ℕ in atTop, ∀ x u : ℝ,
      ε * (n : ℝ) ≤ x → |u| ≤ |η n| → |L (x + u) / L x - 1| < τ := by
  intro τ hτ
  have hz : Tendsto (fun n : ℕ => ε * (n : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hε
  have hsmall : Tendsto (fun n : ℕ => (η n / (n : ℝ)) / ε) atTop (𝓝 0) := by
    simpa only [zero_div] using hη.div_const ε
  have hUC := slowlyVarying_uniform_relative_tail hpos hL hfixed hz hsmall τ hτ
  filter_upwards [hUC, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  intro x u hbase hu
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hnpos
  have hxp : 0 < x := (mul_pos hε hnR).trans_le hbase
  apply hn x (x + u) hbase
  have hrel : (x + u) / x - 1 = u / x := by
    rw [add_div, div_self hxp.ne']
    ring
  rw [hrel, abs_div, abs_of_pos hxp]
  calc
    |u| / x ≤ |η n| / x := div_le_div_of_nonneg_right hu hxp.le
    _ ≤ |η n| / (ε * (n : ℝ)) :=
      div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos hε hnR) hbase
    _ = |(η n / (n : ℝ)) / ε| := by
      rw [abs_div, abs_div, abs_of_pos hnR, abs_of_pos hε, div_div,
        mul_comm (n : ℝ) ε]

end SubcriticalCauchy
