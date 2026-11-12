module

public import SubcriticalCauchy.PaperRoute.Eq33Proof
public import SubcriticalCauchy.LinearWindows
public import SubcriticalCauchy.IncrementTailAsymptotics

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Arithmetic helpers for paper equation (2.6)

This module contains only the lattice-window identities used to connect the
centered walk to the integer-indexed local limit.  The probabilistic estimates
are supplied by `berger_local_limit` and the existing uniform window lemmas.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section

/-- The lattice `ℤ + c` meets `(x, x + 1]` at exactly one point. -/
theorem intCast_add_mem_unitIoc_iff (z : ℤ) (c x : ℝ) :
    (z : ℝ) + c ∈ Set.Ioc x (x + 1) ↔ z = ⌊x - c⌋ + 1 := by
  have hfloor := Int.floor_le (x - c)
  have hnext := Int.lt_floor_add_one (x - c)
  constructor
  · rintro ⟨hlo, hhi⟩
    have h₁ : (⌊x - c⌋ : ℝ) < (z : ℝ) := by linarith
    have h₂ : (z : ℝ) < (⌊x - c⌋ : ℝ) + 2 := by linarith
    have h₁Z : ⌊x - c⌋ < z := by exact_mod_cast h₁
    have h₂Z : z < ⌊x - c⌋ + 2 := by exact_mod_cast h₂
    omega
  · rintro rfl
    push_cast
    constructor <;> linarith

/-- A centered-increment unit window is a singleton of the increment law. -/
theorem centeredIncrementLaw_ioc_eq_singleton (μ : Measure ℕ) (x : ℝ) :
    centeredIncrementLaw μ (Set.Ioc x (x + 1)) =
      incrementLaw μ {⌊x - (1 - (offspringMean μ).toReal)⌋ + 1} := by
  rw [centeredIncrementLaw, Measure.map_apply (by fun_prop) measurableSet_Ioc]
  congr 1
  ext z
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  exact intCast_add_mem_unitIoc_iff z _ x

/-- The centered-walk window is the corresponding integer-sum singleton. -/
theorem pi_centeredIncrementLaw_window (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (n : ℕ) (x : ℝ) :
    (Measure.pi fun _ : Fin n => centeredIncrementLaw μ)
        {y | ∑ i, y i ∈ Set.Ioc x (x + 1)} =
      (Measure.pi fun _ : Fin n => incrementLaw μ)
        {y | ∑ i, y i = ⌊x - (1 - (offspringMean μ).toReal) * n⌋ + 1} := by
  let γ : ℝ := 1 - (offspringMean μ).toReal
  let incrementLaw_isProbability : IsProbabilityMeasure (incrementLaw μ) := by
    unfold incrementLaw
    infer_instance
  have hmap : (Measure.pi fun _ : Fin n => incrementLaw μ).map
      (fun y i => (y i : ℝ) + γ) =
      (Measure.pi fun _ : Fin n => centeredIncrementLaw μ) := by
    simpa only [centeredIncrementLaw, γ] using
      (Measure.pi_map_pi (μ := fun _ : Fin n => incrementLaw μ)
        (f := fun (_ : Fin n) (k : ℤ) => (k : ℝ) + γ)
        (fun _ => Measurable.aemeasurable (by fun_prop)))
  have hmeas : MeasurableSet {y : Fin n → ℝ | ∑ i, y i ∈ Set.Ioc x (x + 1)} :=
    measurableSet_Ioc.preimage (by fun_prop)
  rw [← hmap, Measure.map_apply (by fun_prop) hmeas]
  congr 1
  ext y
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Int.cast_sum]
  simpa only [γ, mul_comm] using intCast_add_mem_unitIoc_iff (∑ i, y i) (γ * n) x

/-- The integer used in Berger's local limit lies above the unrounded window point. -/
theorem eq26_bergerIndex_sub_lower (b γ : ℝ) (n : ℕ) (x : ℝ) :
    x - (b + γ * n) <
      ((⌊x - γ * n⌋ + 1 - ⌊b⌋ : ℤ) : ℝ) := by
  push_cast
  linarith [Int.floor_le b, Int.lt_floor_add_one (x - γ * n)]

/-- Berger's singleton is the centered window at a point within a bounded,
sublinear displacement of the original window point. -/
theorem eq26_bergerIndex_window_bound (b γ : ℝ) (n : ℕ) (x : ℝ) :
    |(((⌊x - γ * n⌋ + 1 - ⌊b⌋ : ℤ) : ℝ) + γ - 1) - x| ≤
      |b + γ * n| + |γ| + 3 := by
  have hfloorX := Int.floor_le (x - γ * n)
  have hnextX := Int.lt_floor_add_one (x - γ * n)
  have hfloorB := Int.floor_le b
  have hnextB := Int.lt_floor_add_one b
  rw [abs_le]
  push_cast
  constructor <;>
    linarith [le_abs_self (b + γ * n), neg_abs_le (b + γ * n),
      le_abs_self γ, neg_abs_le γ]

/-- The exact reciprocal relation between Berger's singleton denominator and
the shifted centered window. -/
theorem eq26_bergerIndex_singleton_eq_window (μ : Measure ℕ) (b γ : ℝ)
    (hγ : γ = 1 - (offspringMean μ).toReal) (n : ℕ) (x : ℝ) :
    incrementLaw μ {⌊x - γ * n⌋ + 1 - ⌊b⌋} =
      centeredIncrementUnitWindow μ γ
        ((((⌊x - γ * n⌋ + 1 - ⌊b⌋ : ℤ) : ℝ) + γ - 1 - x) + x) := by
  subst γ
  have hsingleton := centeredIncrementLaw_ioc_eq_singleton μ
    (((⌊x - (1 - (offspringMean μ).toReal) * n⌋ + 1 - ⌊b⌋ : ℤ) : ℝ) +
      (1 - (offspringMean μ).toReal) - 1)
  rw [centeredIncrementLaw_ioc] at hsingleton
  have hfloor :
      ⌊(((⌊x - (1 - (offspringMean μ).toReal) * n⌋ + 1 - ⌊b⌋ : ℤ) : ℝ) +
          (1 - (offspringMean μ).toReal) - 1 - (1 - (offspringMean μ).toReal))⌋ + 1 =
        ⌊x - (1 - (offspringMean μ).toReal) * n⌋ + 1 - ⌊b⌋ := by
    have heq :
        (((⌊x - (1 - (offspringMean μ).toReal) * n⌋ + 1 - ⌊b⌋ : ℤ) : ℝ) +
          (1 - (offspringMean μ).toReal) - 1 - (1 - (offspringMean μ).toReal)) =
          (((⌊x - (1 - (offspringMean μ).toReal) * n⌋ + 1 - ⌊b⌋ : ℤ) - 1 : ℤ) : ℝ) := by
      push_cast
      ring
    rw [heq, Int.floor_intCast]
    omega
  rw [hfloor] at hsingleton
  have hpoint :
      (((⌊x - (1 - (offspringMean μ).toReal) * n⌋ + 1 - ⌊b⌋ : ℤ) : ℝ) +
          (1 - (offspringMean μ).toReal) - 1 - x) + x =
        (((⌊x - (1 - (offspringMean μ).toReal) * n⌋ + 1 - ⌊b⌋ : ℤ) : ℝ) +
          (1 - (offspringMean μ).toReal) - 1) := by ring
  rw [hpoint]
  exact hsingleton.symm

/-- Above a linear threshold, the original and all boundedly sublinearly shifted
centered unit windows are eventually nonzero. -/
theorem eq26_centeredUnitWindow_eventually_pos
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (γ : ℝ)
    {ε : ℝ} (hε : 0 < ε) {s : ℕ → ℝ}
    (hs : Tendsto (fun n : ℕ => s n / (n : ℝ)) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop, ∀ x u : ℝ, ε * n ≤ x →
      |u| ≤ |s n| + |γ| + 3 →
      0 < centeredIncrementUnitWindow μ γ x ∧
        0 < centeredIncrementUnitWindow μ γ (x + u) := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (incrementUnitWindow_eventually_pos μ hμ.to_literal)
  have hhalf : Tendsto (fun n : ℕ => (ε / 2) * (n : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (half_pos hε)
  have hquarter : Tendsto (fun n : ℕ => (ε / 4) * (n : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by positivity)
  have hsmall := hs.abs.eventually (gt_mem_nhds
    (show |(0 : ℝ)| < ε / 4 by simpa only [abs_zero] using by positivity))
  filter_upwards [hhalf.eventually_ge_atTop (K + |γ|),
    hquarter.eventually_ge_atTop (2 * |γ| + 3), hsmall,
    eventually_gt_atTop (0 : ℕ)] with n hbase hconst hsn hn x u hx hu
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  rw [abs_div, abs_of_pos hnR] at hsn
  have hsle : |s n| ≤ (ε / 4) * (n : ℝ) :=
    ((div_lt_iff₀ hnR).mp hsn).le
  have hxpos : K ≤ x - γ := by
    nlinarith [le_abs_self γ]
  have hulower : -(|s n| + |γ| + 3) ≤ u := by
    linarith [neg_abs_le u]
  have hupos : K ≤ x + u - γ := by
    nlinarith [le_abs_self γ, neg_abs_le γ]
  rw [centeredIncrementUnitWindow_eq, centeredIncrementUnitWindow_eq]
  exact ⟨hK _ hxpos, hK _ hupos⟩

end

end SubcriticalCauchy.Bienayme
