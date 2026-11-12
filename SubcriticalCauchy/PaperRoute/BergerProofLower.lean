module

public import SubcriticalCauchy.PaperRoute.BergerProofAux

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Residual arithmetic for Berger's one-big-jump argument
-/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Topology BigOperators

namespace SubcriticalCauchy.Bienayme

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The window around the dominant jump. -/
def bergerNearSet (ε : ℝ) (z : ℤ) : Set ℤ :=
  {w | (1 - ε) * (z : ℝ) ≤ (w : ℝ) ∧ (w : ℝ) ≤ (1 + ε) * (z : ℝ)}

/-- Big jumps outside the dominant window. -/
def bergerFarSet (δ ε : ℝ) (z : ℤ) : Set ℤ :=
  {w | δ * (z : ℝ) < (w : ℝ) ∧ w ∉ bergerNearSet ε z}

/-- Residual sum and maximum conditions used on both sides of the estimate. -/
def bergerGoodSet {m : ℕ} (K A : ℝ) (z : ℤ) (dev : (Fin m → ℤ) → ℝ) :
    Set (Fin m → ℤ) :=
  {y | |dev y| ≤ K * A ∧ ∀ i, (y i : ℝ) ≤ (z : ℝ) / 2}

/-- The three deterministic consequences of the residual good event. -/
lemma berger_residual_spec {m : ℕ} (T z : ℤ) (dev : (Fin m → ℤ) → ℝ)
    (δ ε K A d : ℝ)
    (hcenter : ∀ y : Fin m → ℤ,
      ((T - ∑ i, y i : ℤ) : ℝ) = (z : ℝ) + d - dev y)
    (hε : ε < 1 / 2) (hz : 0 < (z : ℝ))
    (hβ : K * A + |d| < ε * (z : ℝ)) (_hKz : K * A < (z : ℝ) / 2) :
    (∀ y ∈ bergerGoodSet K A z dev, T - ∑ i, y i ∈ bergerNearSet ε z) ∧
    (∀ y ∈ bergerGoodSet K A z dev, ∀ i, y i < T - ∑ k, y k) ∧
    (∀ y : Fin m → ℤ, T - ∑ i, y i ∈ bergerFarSet δ ε z →
      y ∈ (bergerGoodSet K A z dev)ᶜ) := by
  have hnear : ∀ y ∈ bergerGoodSet K A z dev, T - ∑ i, y i ∈ bergerNearSet ε z := by
    intro y hy
    have hdev := hy.1
    have hw := hcenter y
    change |dev y| ≤ K * A at hdev
    rw [abs_le] at hdev
    change (1 - ε) * (z : ℝ) ≤ ((T - ∑ i, y i : ℤ) : ℝ) ∧
      ((T - ∑ i, y i : ℤ) : ℝ) ≤ (1 + ε) * (z : ℝ)
    rw [hw]
    have hdabs := le_abs_self d
    have hdabs' := neg_abs_le d
    constructor <;> nlinarith only [hdev.1, hdev.2, hdabs, hdabs', hβ]
  refine ⟨hnear, ?_, ?_⟩
  · intro y hy i
    have hn := hnear y hy
    have hi := hy.2 i
    have hz' : (z : ℝ) / 2 < ((T - ∑ k, y k : ℤ) : ℝ) := by
      have hlo := hn.1
      have hεz : 0 < (1 / 2 - ε) * (z : ℝ) := mul_pos (by linarith) hz
      nlinarith only [hlo, hεz]
    have hi' : (y i : ℝ) < ((T - ∑ k, y k : ℤ) : ℝ) := lt_of_le_of_lt hi hz'
    exact_mod_cast hi'
  · intro y hy
    simp only [bergerGoodSet, Set.mem_compl_iff, Set.mem_ofPred_eq, not_and]
    intro hdev
    exfalso
    have hw := hcenter y
    have hfar := hy
    change δ * (z : ℝ) < ((T - ∑ i, y i : ℤ) : ℝ) ∧
      (T - ∑ i, y i : ℤ) ∉ bergerNearSet ε z at hfar
    rw [hw] at hfar
    change |dev y| ≤ K * A at hdev
    rw [abs_le] at hdev
    have hfar2 := hfar.2
    simp only [bergerNearSet, Set.mem_ofPred_eq] at hfar2
    rw [hw] at hfar2
    have hdlo := neg_abs_le d
    have hdhi := le_abs_self d
    by_cases hh : (z : ℝ) + d - dev y ≤ (1 + ε) * (z : ℝ)
    · have hl : ¬(1 - ε) * (z : ℝ) ≤ (z : ℝ) + d - dev y := by
        intro hl
        exact hfar2 ⟨hl, hh⟩
      nlinarith only [hdev.1, hdev.2, hdlo, hdhi, hβ, hl]
    · nlinarith only [hdev.1, hdev.2, hdlo, hdhi, hβ, hh, hz, hε]

/-- The good residual complement is covered by the two tightness events. -/
lemma berger_good_compl_subset {m : ℕ} (K A : ℝ) (z : ℤ)
    (dev : (Fin m → ℤ) → ℝ) (hKz : K * A < (z : ℝ) / 2) :
    (bergerGoodSet K A z dev)ᶜ ⊆
      {y : Fin m → ℤ | K * A < |dev y|} ∪
        {y | ∃ i, K * A < (y i : ℝ)} := by
  intro y hy
  simp only [bergerGoodSet, Set.mem_compl_iff, Set.mem_ofPred_eq, not_and,
    not_forall] at hy
  by_cases hs : |dev y| ≤ K * A
  · right
    obtain ⟨i, hi⟩ := hy hs
    exact ⟨i, hKz.trans (lt_of_not_ge hi)⟩
  · exact Or.inl (lt_of_not_ge hs)


/-- Shifted ratios retain the near-window bounds. -/
lemma berger_near_shift {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    {z w : ℤ} (hz : 0 < (z : ℝ)) (hw : w ∈ bergerNearSet ε z) :
    ((w : ℝ) + 1) / ((z : ℝ) + 1) ∈ Set.Icc (1 - ε) (1 + ε) := by
  change (1 - ε) * (z : ℝ) ≤ (w : ℝ) ∧ (w : ℝ) ≤ (1 + ε) * (z : ℝ) at hw
  have hz1 : (0 : ℝ) < (z : ℝ) + 1 := by linarith
  constructor
  · exact (le_div_iff₀ hz1).mpr (by nlinarith only [hw.1, hε])
  · exact (div_le_iff₀ hz1).mpr (by nlinarith only [hw.2, hε])

/-- Shifted reciprocal ratios retain the reciprocal near-window bounds. -/
lemma berger_swap_shift {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    {z w : ℤ} (hz : 0 < (z : ℝ)) (hw : w ∈ bergerNearSet ε z) :
    ((z : ℝ) + 1) / ((w : ℝ) + 1) ∈ Set.Icc (1 + ε)⁻¹ (1 - ε)⁻¹ := by
  change (1 - ε) * (z : ℝ) ≤ (w : ℝ) ∧ (w : ℝ) ≤ (1 + ε) * (z : ℝ) at hw
  have hεa : 0 < 1 - ε := by linarith
  have hw1 : (0 : ℝ) < (w : ℝ) + 1 := by nlinarith [mul_pos hεa hz]
  constructor
  · have hh : (1 + ε) * ((z : ℝ) + 1) ≥ (w : ℝ) + 1 := by
      calc
        (w : ℝ) + 1 ≤ (1 + ε) * (z : ℝ) + (1 + ε) := add_le_add hw.2 (by linarith)
        _ = (1 + ε) * ((z : ℝ) + 1) := by ring
    exact (le_div_iff₀ hw1).mpr (by
      rw [inv_mul_eq_div]
      exact (div_le_iff₀ (by linarith : (0 : ℝ) < 1 + ε)).mpr (by nlinarith only [hh]))
  · have hh : (1 - ε) * ((z : ℝ) + 1) ≤ (w : ℝ) + 1 := by
      calc
        (1 - ε) * ((z : ℝ) + 1) = (1 - ε) * (z : ℝ) + (1 - ε) := by ring
        _ ≤ (w : ℝ) + (1 - ε) := add_le_add hw.1 (le_refl _)
        _ ≤ (w : ℝ) + 1 := by linarith
    exact (div_le_iff₀ hw1).mpr (by
      rw [inv_mul_eq_div]
      exact (le_div_iff₀ hεa).mpr (by simpa only [mul_comm] using hh))

/-- The shifted-index Potter premise follows from a big unshifted jump. -/
lemma berger_far_shift {δ : ℝ} (hδ1 : δ ≤ 1) {z w : ℤ}
    (_hz : 0 ≤ (z : ℝ)) (hw : δ * (z : ℝ) < (w : ℝ)) :
    δ * ((z : ℝ) + 1) ≤ (w : ℝ) + 1 := by
  nlinarith

end
end SubcriticalCauchy.Bienayme
