module

public import SubcriticalCauchy.UniformSlowVariation

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Sequential uniform convergence for measurable slowly varying functions

The logarithmic change of variables uses the original values of `L` throughout.
Only positivity on the positive half-line, Lebesgue a.e. measurability there,
and the literal fixed-factor ratio limits are assumed.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace SubcriticalCauchy

/-- A finite limiting shift reduces to the zero-shift additive theorem by
subtracting its limit and adding back one fixed increment. -/
theorem additive_uniform_sequential_of_shift_tendsto {f : ℝ → ℝ}
    (hf : AEMeasurable f (volume : Measure ℝ))
    (hfixed : ∀ c : ℝ, Tendsto (fun x => f (x + c) - f x) atTop (𝓝 0))
    {x s : ℕ → ℝ} {c : ℝ} (hx : Tendsto x atTop atTop) (hs : Tendsto s atTop (𝓝 c)) :
    Tendsto (fun n => f (x n + s n) - f (x n)) atTop (𝓝 0) := by
  have hsmall : Tendsto (fun n => s n - c) atTop (𝓝 0) := by
    simpa only [sub_self] using hs.sub_const c
  have hmove := additive_uniform_sequential hf hfixed
    (hx.atTop_add (tendsto_const_nhds (x := c))) hsmall
  have hconst := (hfixed c).comp hx
  have hsum := hmove.add hconst
  have heq : (fun n => (f (x n + c + (s n - c)) - f (x n + c)) +
      (f (x n + c) - f (x n))) =ᶠ[atTop]
      (fun n => f (x n + s n) - f (x n)) := by
    apply Eventually.of_forall
    intro n
    change (f (x n + c + (s n - c)) - f (x n + c)) +
      (f (x n + c) - f (x n)) = f (x n + s n) - f (x n)
    have harg : x n + c + (s n - c) = x n + s n := by ring
    rw [harg]
    ring
  simpa only [zero_add] using hsum.congr' heq

/-- Sequential uniform convergence on the positive factor axis. In particular,
the multiplying factors may approach one instead of being fixed. -/
theorem slowlyVarying_uniform_sequential {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hfixed : ∀ a : ℝ, 0 < a →
      Tendsto (fun x : ℝ => L (a * x) / L x) atTop (𝓝 1))
    {x a : ℕ → ℝ} {c : ℝ} (hx : Tendsto x atTop atTop)
    (ha : Tendsto a atTop (𝓝 c)) (hc : 0 < c) :
    Tendsto (fun n => L (a n * x n) / L (x n)) atTop (𝓝 1) := by
  let f (y : ℝ) := Real.log (L (Real.exp y))
  have hf : AEMeasurable f (volume : Measure ℝ) := aemeasurable_log_exp_transform hL
  have hfshift (b : ℝ) : Tendsto (fun y => f (y + b) - f y) atTop (𝓝 0) := by
    have hr := (hfixed (Real.exp b) (Real.exp_pos b)).comp Real.tendsto_exp_atTop
    have hl := hr.log (by norm_num : (1 : ℝ) ≠ 0)
    have heq (y : ℝ) : Real.log (L (Real.exp b * Real.exp y) / L (Real.exp y)) =
        f (y + b) - f y := by
      rw [Real.log_div
        (hpos _ (mul_pos (Real.exp_pos b) (Real.exp_pos y))).ne'
        (hpos _ (Real.exp_pos y)).ne']
      dsimp only [f]
      rw [Real.exp_add, mul_comm (Real.exp b) (Real.exp y)]
    simpa only [Real.log_one] using hl.congr' (Eventually.of_forall heq)
  have hbase : Tendsto (fun n => Real.log (x n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hx
  have hshift : Tendsto (fun n => Real.log (a n)) atTop (𝓝 (Real.log c)) := ha.log hc.ne'
  have hlog := additive_uniform_sequential_of_shift_tendsto hf hfshift hbase hshift
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hlog
  have heq : (fun n => Real.exp (f (Real.log (x n) + Real.log (a n)) -
      f (Real.log (x n)))) =ᶠ[atTop] (fun n => L (a n * x n) / L (x n)) := by
    filter_upwards [hx.eventually_gt_atTop 0, ha.eventually (lt_mem_nhds hc)] with n hxn han
    dsimp only [f]
    rw [Real.exp_add, Real.exp_log hxn, Real.exp_log han, Real.exp_sub,
      Real.exp_log (hpos _ (mul_pos hxn han)), Real.exp_log (hpos _ hxn), mul_comm (x n) (a n)]
  simpa only [Real.exp_zero] using hexp.congr' heq

end SubcriticalCauchy
