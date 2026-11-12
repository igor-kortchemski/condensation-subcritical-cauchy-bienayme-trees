module

public import SubcriticalCauchy.PaperRoute.Eq26ProofAux

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Helpers for `SubcriticalCauchy.PaperRoute.Statements` (Eq26Proof)

The proof of (2.6), conditional on Berger's local limit.  Exact lattice-window
identities and denominator positivity are proved in `Eq26ProofAux`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section

/-- Paper equation (2.6), with Berger's local limit as its only probabilistic
input.  The type of `hB` is the conclusion of `berger_local_limit μ hμ`. -/
theorem paper_eq26_of_berger (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ)
    (hB : ∀ (a : ℕ → ℝ),
      Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal) atTop (𝓝 1) →
      ∀ τ > 0, ∃ N : ℕ, ∃ R : ℝ, ∀ n ≥ N, ∀ z : ℤ, R * a n ≤ z →
        |((Measure.pi fun _ : Fin n => incrementLaw μ)
              {x | ∑ i, x i = z + ⌊centering μ a n⌋}).toReal /
            ((n : ℝ) * (incrementLaw μ {z}).toReal) - 1| ≤ τ)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ τ > 0, ∀ᶠ n : ℕ in atTop, ∀ x : ℝ, ε * n ≤ x →
      |((Measure.pi fun _ : Fin n => centeredIncrementLaw μ)
            {y | ∑ i, y i ∈ Set.Ioc x (x + 1)}).toReal /
          ((n : ℝ) * (centeredIncrementLaw μ (Set.Ioc x (x + 1))).toReal) - 1| ≤ τ := by
  obtain ⟨a, ha⟩ := exists_scaling μ hμ
  let γ : ℝ := 1 - (offspringMean μ).toReal
  let m : ℕ → ℝ := fun n => centering μ a n + γ * n
  have hlit : IsSubcriticalCauchyOffspring μ := hμ.to_literal
  let incrementLaw_isProbability : IsProbabilityMeasure (incrementLaw μ) := by
    unfold incrementLaw
    infer_instance
  have hm : Tendsto (fun n : ℕ => m n / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [m, γ] using paper_centering_shift_div_nat_tendsto_zero μ hlit ha
  have ha0 : Tendsto (fun n : ℕ => a n / (n : ℝ)) atTop (𝓝 0) :=
    scaling_div_nat_tendsto_zero μ hlit ha
  have hapos : ∀ᶠ n : ℕ in atTop, 0 < a n :=
    (scaling_tendsto_atTop μ hlit ha).eventually_gt_atTop 0
  have hη : Tendsto (fun n : ℕ => (|m n| + |γ| + 3) / (n : ℝ)) atTop (𝓝 0) := by
    have hconst : Tendsto (fun n : ℕ => (|γ| + 3) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hsum := hm.abs.add hconst
    have heq : (fun n : ℕ => |m n / (n : ℝ)| + (|γ| + 3) / (n : ℝ)) =ᶠ[atTop]
        (fun n : ℕ => (|m n| + |γ| + 3) / (n : ℝ)) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
      rw [abs_div, abs_of_pos hnR]
      ring
    simpa only [zero_add, add_zero, abs_zero] using hsum.congr' heq
  intro τ hτ
  let δ : ℝ := min (τ / 3) (1 / 4)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδτ : δ ≤ τ / 3 := min_le_left _ _
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (by norm_num)
  obtain ⟨N, R, hBerger⟩ := hB a ha δ hδ
  have hdiverge : ∀ᶠ n : ℕ in atTop, ∀ x : ℝ, ε * n ≤ x →
      |R| + 1 ≤ (x - m n) / a n := by
    simpa only [m] using
      sublinear_scale_uniform_divergence hm ha0 hapos hε (|R| + 1)
  have hwindow := paper_centeredUnitWindow_uniform_additive_window
    μ hμ γ hε hη δ hδ
  have hpositive := eq26_centeredUnitWindow_eventually_pos μ hμ γ hε hm
  filter_upwards [eventually_ge_atTop N, hapos, hdiverge, hwindow, hpositive,
    eventually_gt_atTop (0 : ℕ)] with n hnN han hdiv hwin hpos hn x hx
  let b : ℝ := centering μ a n
  let z : ℤ := ⌊x - γ * n⌋ + 1 - ⌊b⌋
  let u : ℝ := (z : ℝ) + γ - 1 - x
  have hm_eq : m n = b + γ * n := rfl
  have hzLower : x - m n < (z : ℝ) := by
    rw [hm_eq]
    exact eq26_bergerIndex_sub_lower b γ n x
  have hu : |u| ≤ |m n| + |γ| + 3 := by
    rw [hm_eq]
    exact eq26_bergerIndex_window_bound b γ n x
  have hzR : R * a n ≤ (z : ℝ) := by
    calc
      R * a n ≤ (|R| + 1) * a n :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self R]) han.le
      _ ≤ x - m n := (le_div_iff₀ han).mp (hdiv x hx)
      _ ≤ (z : ℝ) := hzLower.le
  have hnum :
      (Measure.pi fun _ : Fin n => centeredIncrementLaw μ)
          {y | ∑ i, y i ∈ Set.Ioc x (x + 1)} =
        (Measure.pi fun _ : Fin n => incrementLaw μ)
          {y | ∑ i, y i = z + ⌊b⌋} := by
    rw [pi_centeredIncrementLaw_window]
    congr 1
    ext y
    simp only [Set.mem_ofPred_eq, z, γ]
    constructor <;> intro h <;> convert h using 1 <;> omega
  have hdenq : incrementLaw μ {z} = centeredIncrementUnitWindow μ γ (x + u) := by
    have h := eq26_bergerIndex_singleton_eq_window μ b γ rfl n x
    change incrementLaw μ {z} = centeredIncrementUnitWindow μ γ (x + u)
    have hpoint :
        ((((⌊x - γ * n⌋ + 1 - ⌊b⌋ : ℤ) : ℝ) + γ - 1 - x) + x) = x + u := by
      dsimp only [u, z]
      ring
    rw [hpoint] at h
    exact h
  have hA := hBerger n hnN z hzR
  rw [← hnum] at hA
  have hu' : |u| ≤ |(|m n| + |γ| + 3)| := by
    rwa [abs_of_nonneg (by positivity : 0 ≤ |m n| + |γ| + 3)]
  have hW := hwin x u hx hu' 
  rw [← hdenq] at hW
  rw [centeredIncrementLaw_ioc]
  let P : ℝ := ((Measure.pi fun _ : Fin n => centeredIncrementLaw μ)
    {y | ∑ i, y i ∈ Set.Ioc x (x + 1)}).toReal
  let Q : ℝ := (n : ℝ) * (incrementLaw μ {z}).toReal
  let C : ℝ := (n : ℝ) * (centeredIncrementUnitWindow μ γ x).toReal
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hq0 : 0 < (incrementLaw μ {z}).toReal := by
    have hq : 0 < incrementLaw μ {z} := by rw [hdenq]; exact (hpos x u hx hu).2
    exact ENNReal.toReal_pos hq.ne' (measure_ne_top _ _)
  have hc0 : 0 < (centeredIncrementUnitWindow μ γ x).toReal := by
    exact ENNReal.toReal_pos (hpos x u hx hu).1.ne' (measure_ne_top _ _)
  have hQ : Q ≠ 0 := (mul_pos hnR hq0).ne'
  have hC : C ≠ 0 := (mul_pos hnR hc0).ne'
  have hQC : Q / C = (incrementLaw μ {z}).toReal /
      (centeredIncrementUnitWindow μ γ x).toReal := by
    dsimp only [Q, C]
    field_simp [hnR.ne', hc0.ne']
  change |P / C - 1| ≤ τ
  change |P / Q - 1| ≤ δ at hA
  rw [← hQC] at hW
  have hPabs : |P / Q| ≤ 1 + δ := by
    calc
      |P / Q| = |(P / Q - 1) + 1| := by congr 1; ring
      _ ≤ |P / Q - 1| + |(1 : ℝ)| := abs_add_le _ _
      _ ≤ δ + 1 := by simpa only [abs_one] using add_le_add hA (le_refl 1)
      _ = 1 + δ := by ring
  have hprod : P / C - 1 = (P / Q - 1) + (P / Q) * (Q / C - 1) := by
    field_simp [hQ, hC]
    ring
  rw [hprod]
  calc
    |(P / Q - 1) + (P / Q) * (Q / C - 1)| ≤
        |P / Q - 1| + |(P / Q) * (Q / C - 1)| := abs_add_le _ _
    _ = |P / Q - 1| + |P / Q| * |Q / C - 1| := by rw [abs_mul]
    _ ≤ δ + (1 + δ) * δ := by
      exact add_le_add hA (mul_le_mul hPabs hW.le (abs_nonneg _) (by positivity))
    _ ≤ τ := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hδ1) hδ.le]

end

end SubcriticalCauchy.Bienayme
