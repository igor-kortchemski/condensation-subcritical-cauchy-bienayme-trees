module

public import SubcriticalCauchy.TruncatedExponential
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Product-measure infrastructure for the endpoint jump estimate

This module transports an iid family indexed by `Fin (j + k)` to two
independent iid blocks, and bounds a marker event on the first block by a
finite sum over its possible sum.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology ENNReal BigOperators

namespace SubcriticalCauchy.Bienayme

/-- Append two finite iid blocks into one family. -/
noncomputable def iidBlockEquiv (j k : ℕ) :
    ((Fin j → ℕ) × (Fin k → ℕ)) ≃ᵐ (Fin (j + k) → ℕ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin j ⊕ Fin k => ℕ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (j + k) => ℕ) finSumFinEquiv)

@[simp] theorem iidBlockEquiv_apply (j k : ℕ)
    (p : (Fin j → ℕ) × (Fin k → ℕ)) :
    iidBlockEquiv j k p = Fin.append p.1 p.2 := by
  ext i
  refine Fin.addCases ?_ ?_ i
  · intro a
    simp [iidBlockEquiv, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
    change p.1 a = p.1 a
    rfl
  · intro b
    simp [iidBlockEquiv, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
    change p.2 b = p.2 b
    rfl

/-- Appending preserves the product iid law. -/
theorem measurePreserving_iidBlockEquiv
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (j k : ℕ) :
    MeasurePreserving (iidBlockEquiv j k)
      ((Measure.pi fun _ : Fin j => μ).prod (Measure.pi fun _ : Fin k => μ))
      (Measure.pi fun _ : Fin (j + k) => μ) := by
  exact (MeasureTheory.measurePreserving_piCongrLeft
      (fun _ : Fin (j + k) => μ) finSumFinEquiv).comp
    (MeasureTheory.measurePreserving_sumPiEquivProdPi_symm
      (fun _ : Fin j ⊕ Fin k => μ))

@[simp] theorem sum_iidBlockEquiv (j k : ℕ)
    (p : (Fin j → ℕ) × (Fin k → ℕ)) :
    ∑ i, iidBlockEquiv j k p i = (∑ i, p.1 i) + ∑ i, p.2 i := by
  rw [iidBlockEquiv_apply, Fin.sum_univ_add]
  simp

@[simp] theorem sum_iidBlockEquiv_real (j k : ℕ)
    (p : (Fin j → ℕ) × (Fin k → ℕ)) :
    ∑ i, (iidBlockEquiv j k p i : ℝ) =
      (∑ i, (p.1 i : ℝ)) + ∑ i, (p.2 i : ℝ) := by
  rw [iidBlockEquiv_apply, Fin.sum_univ_add]
  simp

/-- A one-block upper estimate, summed over all possible first-block sums. -/
theorem measureReal_first_block_le
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (j k n : ℕ) (hn : 0 < n) (a c m X Y : ℝ)
    (hfirst :
      ((Measure.pi fun _ : Fin j => μ)
        {ω | a * (n : ℝ) ≤ (∑ i, (ω i : ℝ)) - m * j ∧
          (∑ i, ω i) < n ∧ ∀ i, (ω i : ℝ) ≤ c * n}).toReal ≤ X)
    (hsecond : ∀ t : ℕ,
      ((Measure.pi fun _ : Fin k => μ) {ω | ∑ i, ω i = t}).toReal ≤ Y) :
    (((Measure.pi fun _ : Fin j => μ).prod (Measure.pi fun _ : Fin k => μ))
      {p | a * (n : ℝ) ≤ (∑ i, (p.1 i : ℝ)) - m * j ∧
        (∑ i, p.1 i) + (∑ i, p.2 i) = n - 1 ∧
        (∀ i, (p.1 i : ℝ) ≤ c * n) ∧ ∀ i, (p.2 i : ℝ) ≤ c * n}).toReal ≤
      X * Y := by
  classical
  let ν := (Measure.pi fun _ : Fin j => μ).prod (Measure.pi fun _ : Fin k => μ)
  let F : Fin n → Set (Fin j → ℕ) := fun s =>
    {ω | a * (n : ℝ) ≤ (∑ i, (ω i : ℝ)) - m * j ∧
      (∑ i, ω i) = (s : ℕ) ∧ ∀ i, (ω i : ℝ) ≤ c * n}
  let A : Fin n → Set ((Fin j → ℕ) × (Fin k → ℕ)) := fun s =>
    F s ×ˢ {ω : Fin k → ℕ | (∑ i, ω i) = n - 1 - (s : ℕ)}
  have hdisj : Pairwise (fun s t => Disjoint (F s) (F t)) := by
    intro s t hst
    rw [Set.disjoint_left]
    intro ω hωs hωt
    apply hst
    apply Fin.ext
    exact hωs.2.1.symm.trans hωt.2.1
  have hunion : (⋃ s, F s) =
      {ω | a * (n : ℝ) ≤ (∑ i, (ω i : ℝ)) - m * j ∧
        (∑ i, ω i) < n ∧ ∀ i, (ω i : ℝ) ≤ c * n} := by
    ext ω
    constructor
    · intro hω
      simp only [Set.mem_iUnion] at hω
      obtain ⟨s, hs⟩ := hω
      exact ⟨hs.1, by simp [hs.2.1], hs.2.2⟩
    · intro hω
      refine Set.mem_iUnion.mpr ⟨⟨∑ i, ω i, hω.2.1⟩, ?_⟩
      exact ⟨hω.1, rfl, hω.2.2⟩
  have hpartition : (Measure.pi fun _ : Fin j => μ).real (⋃ s, F s) =
      ∑ s : Fin n, ((Measure.pi fun _ : Fin j => μ) (F s)).toReal :=
    measureReal_iUnion_fintype hdisj (fun _ => MeasurableSet.of_discrete)
      (fun _ => measure_ne_top _ _)
  have hsum : (∑ s : Fin n,
      ((Measure.pi fun _ : Fin j => μ) (F s)).toReal) ≤ X := by
    rw [← hpartition, hunion]
    exact hfirst
  have hY : 0 ≤ Y := ENNReal.toReal_nonneg.trans (hsecond 0)
  have hsub :
      {p | a * (n : ℝ) ≤ (∑ i, (p.1 i : ℝ)) - m * j ∧
        (∑ i, p.1 i) + (∑ i, p.2 i) = n - 1 ∧
        (∀ i, (p.1 i : ℝ) ≤ c * n) ∧ ∀ i, (p.2 i : ℝ) ≤ c * n} ⊆
        ⋃ s ∈ Finset.univ, A s := by
    intro p hp
    rcases hp with ⟨hhigh, htotal, hmaxfirst, hmaxsecond⟩
    have hs : (∑ i, p.1 i) < n := by omega
    let s : Fin n := ⟨∑ i, p.1 i, hs⟩
    refine Set.mem_biUnion (Finset.mem_univ s) ?_
    refine ⟨⟨hhigh, rfl, hmaxfirst⟩, ?_⟩
    dsimp [s]
    omega
  have hmeasure : ν
      {p | a * (n : ℝ) ≤ (∑ i, (p.1 i : ℝ)) - m * j ∧
        (∑ i, p.1 i) + (∑ i, p.2 i) = n - 1 ∧
        (∀ i, (p.1 i : ℝ) ≤ c * n) ∧ ∀ i, (p.2 i : ℝ) ≤ c * n} ≤
      ∑ s ∈ Finset.univ, ν (A s) :=
    (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
  have htop : (∑ s ∈ Finset.univ, ν (A s)) ≠ ∞ := by
    rw [ENNReal.sum_ne_top]
    intro s _
    exact measure_ne_top _ _
  have hreal := ENNReal.toReal_mono htop hmeasure
  rw [ENNReal.toReal_sum (fun s _ => measure_ne_top _ _)] at hreal
  calc
    _ ≤ ∑ s ∈ Finset.univ, (ν (A s)).toReal := hreal
    _ ≤ ∑ s ∈ Finset.univ,
        ((Measure.pi fun _ : Fin j => μ) (F s)).toReal * Y := by
      apply Finset.sum_le_sum
      intro s _
      rw [show (ν (A s)).toReal =
          ((Measure.pi fun _ : Fin j => μ) (F s)).toReal *
          ((Measure.pi fun _ : Fin k => μ)
            {ω | (∑ i, ω i) = n - 1 - (s : ℕ)}).toReal by
        exact measureReal_prod_prod _ _]
      exact mul_le_mul_of_nonneg_left (hsecond _) ENNReal.toReal_nonneg
    _ = (∑ s ∈ Finset.univ,
        ((Measure.pi fun _ : Fin j => μ) (F s)).toReal) * Y := by
      rw [Finset.sum_mul]
    _ ≤ X * Y := mul_le_mul_of_nonneg_right hsum hY


/-- The symmetric one-block estimate, with the marker event on the second
block. It is obtained from `measureReal_first_block_le` by `Prod.swap`. -/
theorem measureReal_second_block_le
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (j k n : ℕ) (hn : 0 < n) (a c m X Y : ℝ)
    (hfirst :
      ((Measure.pi fun _ : Fin k => μ)
        {ω | a * (n : ℝ) ≤ (∑ i, (ω i : ℝ)) - m * k ∧
          (∑ i, ω i) < n ∧ ∀ i, (ω i : ℝ) ≤ c * n}).toReal ≤ X)
    (hsecond : ∀ s : ℕ,
      ((Measure.pi fun _ : Fin j => μ) {ω | ∑ i, ω i = s}).toReal ≤ Y) :
    (((Measure.pi fun _ : Fin j => μ).prod (Measure.pi fun _ : Fin k => μ))
      {p | a * (n : ℝ) ≤ (∑ i, (p.2 i : ℝ)) - m * k ∧
        (∑ i, p.1 i) + (∑ i, p.2 i) = n - 1 ∧
        (∀ i, (p.1 i : ℝ) ≤ c * n) ∧ ∀ i, (p.2 i : ℝ) ≤ c * n}).toReal ≤
      X * Y := by
  let Q := (Measure.pi fun _ : Fin k => μ).prod (Measure.pi fun _ : Fin j => μ)
  let B : Set ((Fin k → ℕ) × (Fin j → ℕ)) :=
    {p | a * (n : ℝ) ≤ (∑ i, (p.1 i : ℝ)) - m * k ∧
      (∑ i, p.1 i) + (∑ i, p.2 i) = n - 1 ∧
      (∀ i, (p.1 i : ℝ) ≤ c * n) ∧ ∀ i, (p.2 i : ℝ) ≤ c * n}
  have hswap : Prod.swap ⁻¹' B =
      {p : (Fin j → ℕ) × (Fin k → ℕ) |
        a * (n : ℝ) ≤ (∑ i, (p.2 i : ℝ)) - m * k ∧
        (∑ i, p.1 i) + (∑ i, p.2 i) = n - 1 ∧
        (∀ i, (p.1 i : ℝ) ≤ c * n) ∧ ∀ i, (p.2 i : ℝ) ≤ c * n} := by
    ext p
    simp only [B, Set.mem_preimage, Set.mem_ofPred_eq]
    constructor <;> intro h
    · exact ⟨h.1, by simpa [add_comm] using h.2.1, h.2.2.2, h.2.2.1⟩
    · exact ⟨h.1, by simpa [add_comm] using h.2.1, h.2.2.2, h.2.2.1⟩
  have hmeasure := (Measure.measurePreserving_swap (μ := (Measure.pi fun _ : Fin j => μ))
    (ν := (Measure.pi fun _ : Fin k => μ))).measure_preimage
      (s := B) MeasurableSet.of_discrete.nullMeasurableSet
  rw [hswap] at hmeasure
  rw [show (((Measure.pi fun _ : Fin j => μ).prod (Measure.pi fun _ : Fin k => μ))
      {p | a * (n : ℝ) ≤ (∑ i, (p.2 i : ℝ)) - m * k ∧
        (∑ i, p.1 i) + (∑ i, p.2 i) = n - 1 ∧
        (∀ i, (p.1 i : ℝ) ≤ c * n) ∧ ∀ i, (p.2 i : ℝ) ≤ c * n}).toReal =
      (Q B).toReal by exact congrArg ENNReal.toReal hmeasure]
  exact measureReal_first_block_le μ k j n hn a c m X Y hfirst hsecond

end SubcriticalCauchy.Bienayme
