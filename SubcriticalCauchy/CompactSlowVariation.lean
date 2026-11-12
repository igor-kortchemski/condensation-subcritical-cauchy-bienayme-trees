module

public import SubcriticalCauchy.MultiplicativeUniformSlowVariation

import Mathlib.Topology.Sequences
import Mathlib.Tactic.Choose

/-!
# Uniform slow variation over compact sets of scale factors

Sequential uniform convergence gives uniformity over a compact positive
interval of multipliers, simultaneously for every base beyond a diverging
lower bound. The proof preserves the original values of the slowly varying
function.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace SubcriticalCauchy

/-- Compact-factor uniform convergence, uniformly over all bases beyond a
diverging lower bound. No boundedness or monotonicity of `L` is assumed. -/
theorem slowlyVarying_uniform_compact_tail {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hfixed : ∀ a : ℝ, 0 < a →
      Tendsto (fun x : ℝ => L (a * x) / L x) atTop (𝓝 1))
    {a b : ℝ} (ha : 0 < a) (_hab : a ≤ b)
    {z : ℕ → ℝ} (hz : Tendsto z atTop atTop) :
    ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ x c : ℝ,
      z n ≤ x → c ∈ Set.Icc a b → |L (c * x) / L x - 1| < τ := by
  classical
  intro τ hτ
  by_contra hnot
  have hbad (N : ℕ) : ∃ (n : ℕ) (x c : ℝ),
      N ≤ n ∧ z n ≤ x ∧ c ∈ Set.Icc a b ∧ τ ≤ |L (c * x) / L x - 1| := by
    by_contra hnone
    apply hnot
    refine eventually_atTop.mpr ⟨N, ?_⟩
    intro n hn x c hbase hc
    by_contra herr
    exact hnone ⟨n, x, c, hn, hbase, hc, le_of_not_gt herr⟩
  choose ns xs cs hN hbase hcs herr using hbad
  have hns : Tendsto ns atTop atTop := tendsto_atTop_mono hN tendsto_id
  have hxs : Tendsto xs atTop atTop := tendsto_atTop_mono hbase (hz.comp hns)
  obtain ⟨c, hc, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hcs
  have hratio : Tendsto (fun n => L (cs (φ n) * xs (φ n)) / L (xs (φ n)))
      atTop (𝓝 1) := by
    simpa only [Function.comp_def] using
      slowlyVarying_uniform_sequential hpos hL hfixed
        (hxs.comp hφ.tendsto_atTop) hlim (ha.trans_le hc.1)
  have hzero : Tendsto
      (fun n => |L (cs (φ n) * xs (φ n)) / L (xs (φ n)) - 1|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero] using (hratio.sub_const 1).abs
  obtain ⟨n, hn⟩ := (hzero.eventually (gt_mem_nhds hτ)).exists
  exact (not_lt_of_ge (herr (φ n))) hn

/-- Compact-factor uniform convergence at a prescribed diverging base
sequence. -/
theorem slowlyVarying_uniform_compact_window {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hfixed : ∀ a : ℝ, 0 < a →
      Tendsto (fun x : ℝ => L (a * x) / L x) atTop (𝓝 1))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {z : ℕ → ℝ} (hz : Tendsto z atTop atTop) :
    ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ c : ℝ,
      c ∈ Set.Icc a b → |L (c * z n) / L (z n) - 1| < τ := by
  intro τ hτ
  filter_upwards [slowlyVarying_uniform_compact_tail hpos hL hfixed ha hab hz τ hτ]
    with n hn
  intro c hc
  exact hn (z n) c le_rfl hc

end SubcriticalCauchy
