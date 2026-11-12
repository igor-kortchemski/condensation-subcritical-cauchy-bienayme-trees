module

public import SubcriticalCauchy.ExampleScalesAux
public import Mathlib.Analysis.SpecialFunctions.NonIntegrable
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Integral tests for logarithmic powers

The tail coefficients of the explicit index-one examples reduce to the series
`1 / (n (log n)^p)`.  This module proves its convergence for `p > 1` and its
divergence for `0 ≤ p ≤ 1`, using explicit primitives on `[3, ∞)`.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section

/-- The comparison sequence for logarithmic moments. -/
noncomputable def logTail (p x : ℝ) : ℝ :=
  if x < 3 then 0 else (x * Real.log x ^ p)⁻¹

private lemma logTail_eq_of_three_le {p x : ℝ} (hx : 3 ≤ x) :
    logTail p x = (x * Real.log x ^ p)⁻¹ := by
  simp [logTail, not_lt.mpr hx]

private lemma logTail_pos {p x : ℝ} (hx : 3 ≤ x) :
    0 < logTail p x := by
  rw [logTail_eq_of_three_le hx]
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  positivity

private lemma logTail_antitone {p : ℝ} (hp : 0 ≤ p) :
    AntitoneOn (logTail p) (Set.Ici 3) := by
  intro x hx y hy hxy
  change 3 ≤ x at hx
  change 3 ≤ y at hy
  rw [logTail_eq_of_three_le hx, logTail_eq_of_three_le hy]
  have hx0 : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hpow : Real.log x ^ p ≤ Real.log y ^ p :=
    Real.rpow_le_rpow hlogx.le (Real.log_le_log hx0 hxy) hp
  have hden : x * Real.log x ^ p ≤ y * Real.log y ^ p :=
    mul_le_mul hxy hpow (Real.rpow_nonneg hlogx.le _) (by linarith)
  simpa only [← one_div] using
    one_div_le_one_div_of_le (mul_pos hx0 (Real.rpow_pos_of_pos hlogx _)) hden

private noncomputable def convergentLogPrimitive (p x : ℝ) : ℝ :=
  1 / ((p - 1) * Real.log x ^ (p - 1))

private lemma convergentLogPrimitive_tendsto {p : ℝ} (hp : 1 < p) :
    Tendsto (convergentLogPrimitive p) atTop (𝓝 0) := by
  have hpow : Tendsto (fun x : ℝ => Real.log x ^ (p - 1)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hp)).comp Real.tendsto_log_atTop
  have hden : Tendsto (fun x : ℝ => (p - 1) * Real.log x ^ (p - 1)) atTop atTop :=
    hpow.const_mul_atTop (sub_pos.mpr hp)
  exact hden.const_div_atTop 1

private lemma convergentLogPrimitive_hasDerivAt {p : ℝ} (hp : 1 < p) {x : ℝ}
    (hx : 3 ≤ x) :
    HasDerivAt (convergentLogPrimitive p) (-logTail p x) x := by
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hpow : 0 < Real.log x ^ (p - 1) := Real.rpow_pos_of_pos hlog _
  have hd := (hasDerivAt_const x 1).div
    (((Real.hasDerivAt_log hx0.ne').rpow_const (p := p - 1) (Or.inl hlog.ne')).const_mul
      (p - 1))
    (mul_ne_zero (sub_pos.mpr hp).ne' hpow.ne')
  rw [logTail_eq_of_three_le hx]
  unfold convergentLogPrimitive
  convert hd using 1
  have hp_pow : Real.log x ^ p = Real.log x ^ (p - 1) * Real.log x := by
    calc
      Real.log x ^ p = Real.log x ^ ((p - 1) + 1) := by congr 2; ring
      _ = Real.log x ^ (p - 1) * Real.log x := by rw [Real.rpow_add hlog, Real.rpow_one]
  rw [hp_pow, Real.rpow_sub hlog]
  simp only [Real.rpow_one, zero_mul, zero_sub]
  field_simp [hx0.ne', hlog.ne', hpow.ne', (sub_pos.mpr hp).ne']
  rw [← Real.rpow_natCast, ← Real.rpow_add hlog]
  congr 2
  push_cast
  ring

/-- For `p > 1`, `∑' n, 1 / (n (log n)^p)` converges. -/
theorem summable_logTail {p : ℝ} (hp : 1 < p) : Summable (fun n : ℕ => logTail p n) := by
  apply summable_nat_of_antitone_primitive (N := 3)
    (convergentLogPrimitive_tendsto hp) (logTail_antitone (by linarith : 0 ≤ p))
  · intro x hx
    exact convergentLogPrimitive_hasDerivAt hp hx
  · intro x hx
    exact (logTail_pos hx).le

private noncomputable def divergentLogPrimitive (p x : ℝ) : ℝ :=
  if p = 1 then Real.log (Real.log x) else Real.log x ^ (1 - p) / (1 - p)

private lemma divergentLogPrimitive_tendsto {p : ℝ} (hp : p ≤ 1) :
    Tendsto (divergentLogPrimitive p) atTop atTop := by
  by_cases heq : p = 1
  · subst p
    unfold divergentLogPrimitive
    simp only [↓reduceIte]
    exact Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  · have hlt : p < 1 := lt_of_le_of_ne hp heq
    have hpow : Tendsto (fun x : ℝ => Real.log x ^ (1 - p)) atTop atTop :=
      (tendsto_rpow_atTop (sub_pos.mpr hlt)).comp Real.tendsto_log_atTop
    unfold divergentLogPrimitive
    simp only [heq, ↓reduceIte]
    exact hpow.atTop_div_const (sub_pos.mpr hlt)

private lemma divergentLogPrimitive_hasDerivAt {p : ℝ} (hp : p ≤ 1) {x : ℝ}
    (hx : 3 < x) : HasDerivAt (divergentLogPrimitive p) (logTail p x) x := by
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  rw [logTail_eq_of_three_le hx.le]
  by_cases heq : p = 1
  · subst p
    unfold divergentLogPrimitive
    simp only [↓reduceIte, Real.rpow_one]
    convert (Real.hasDerivAt_log hx0.ne').log hlog.ne' using 1
    simp [div_eq_mul_inv, mul_inv_rev]
    ring
  · have hlt : p < 1 := lt_of_le_of_ne hp heq
    unfold divergentLogPrimitive
    simp only [heq, ↓reduceIte]
    have hd := ((Real.hasDerivAt_log hx0.ne').rpow_const
      (p := 1 - p) (Or.inl hlog.ne')).div_const (1 - p)
    convert hd using 1
    rw [show 1 - p - 1 = -p by ring, Real.rpow_neg hlog.le]
    field_simp [hx0.ne', hlog.ne', (sub_pos.mpr hlt).ne',
      (Real.rpow_pos_of_pos hlog p).ne']

/-- For `0 ≤ p ≤ 1`, `∑' n, 1 / (n (log n)^p)` diverges. -/
theorem not_summable_logTail {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ¬ Summable (fun n : ℕ => logTail p n) := by
  intro hs
  have hderiv : ∀ᶠ x : ℝ in atTop,
      HasDerivAt (divergentLogPrimitive p) (logTail p x) x := by
    filter_upwards [eventually_gt_atTop (3 : ℝ)] with x hx
    exact divergentLogPrimitive_hasDerivAt hp1 hx
  have hnorm : Tendsto (fun x : ℝ => ‖divergentLogPrimitive p x‖) atTop atTop := by
    have hpos : ∀ᶠ x : ℝ in atTop, 0 ≤ divergentLogPrimitive p x :=
      (divergentLogPrimitive_tendsto hp1).eventually_ge_atTop 0
    apply (divergentLogPrimitive_tendsto hp1).congr'
    filter_upwards [hpos] with x hx
    exact (Real.norm_of_nonneg hx).symm
  have hfg : deriv (divergentLogPrimitive p) =O[atTop] logTail p :=
    Filter.EventuallyEq.isBigO (hderiv.mono fun _ h => h.deriv)
  have hnonint : ¬ IntegrableOn (logTail p) (Set.Ioi (3 : ℝ)) :=
    not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter atTop
      (Ioi_mem_atTop 3) (hderiv.mono fun _ h => h.differentiableAt) hnorm hfg
  apply hnonint
  apply (logTail_antitone hp0).integrableOn_Ioi_of_summable_comp_add
    ((summable_nat_add_iff 3).mpr hs)
  intro x hx
  exact (logTail_pos hx.le).le

end
end SubcriticalCauchy.Bienayme
