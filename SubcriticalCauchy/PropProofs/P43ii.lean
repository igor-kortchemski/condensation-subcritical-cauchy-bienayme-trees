module

public import SubcriticalCauchy.PropProofs.P43iiAux

/-!
# Proof helpers for the frozen statement of Proposition 4.3(ii) (`paper_height_upper`)

Owned helper module for one registered hole of
`SubcriticalCauchy.Propositions42_43`. It is imported by the frozen statement
file, which must not change except inside its holes; add the proof and any
further imports here.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section
open BGW BGW.LocallyFinite

attribute [local instance] Classical.propDecidable

private theorem measurableSet_finiteTreeEvent_p43ii (P : PlaneTree → Prop) :
    MeasurableSet (finiteTreeEvent P) :=
  ((Set.to_countable {t : PlaneTree | P t}).image
    PlaneTree.toLocallyFinite).measurableSet

private theorem toLocallyFinite_mem_finiteTreeEvent_iff_p43ii
    (P : PlaneTree → Prop) (t : PlaneTree) :
    t.toLocallyFinite ∈ finiteTreeEvent P ↔ P t := by
  constructor
  · rintro ⟨s, hs, hst⟩
    have hst' : s = t := PlaneTree.toLocallyFinite_injective hst
    simpa only [hst', Set.mem_ofPred_eq] using hs
  · intro ht
    exact ⟨t, ht, rfl⟩

private theorem conditioned_apply_eq_tsum_plane_p43ii (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (n : ℕ) (A : Set Tree) (hA : MeasurableSet A) :
    conditioned μ n A =
      ∑' t : PlaneTree, conditioned μ n {t.toLocallyFinite} *
        (if t.toLocallyFinite ∈ A then 1 else 0) := by
  classical
  let f (t : PlaneTree) : ℝ≥0∞ := conditioned μ n {t.toLocallyFinite} *
    (if t.toLocallyFinite ∈ A then 1 else 0)
  change conditioned μ n A = ∑' t : PlaneTree, f t
  change (bienaymeLaw μ (sizeEvent n))⁻¹ *
      (bienaymeLaw μ).restrict (sizeEvent n) A = _
  rw [restrict_sizeEvent_apply μ n A hA, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro t
  dsimp only [f]
  have hat : conditioned μ n {t.toLocallyFinite} =
      if t.size = n then
        PlaneTree.weight (fun k => μ {k}) t / bienaymeLaw μ (sizeEvent n) else 0 :=
    cond_sizeEvent_singleton μ n t
  rw [hat]
  by_cases ht : t.size = n
  · simp only [ht, ↓reduceIte, ENNReal.div_eq_inv_mul, mul_assoc]
  · simp only [ht, ↓reduceIte, zero_mul, mul_zero]

private theorem conditioned_height_lt_eq_compl_p43ii (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (n : ℕ) (a : ℝ) :
    conditioned μ n (finiteTreeEvent fun t => (height t : ℝ) < a) =
      conditioned μ n (finiteTreeEvent fun t => a ≤ (height t : ℝ))ᶜ := by
  classical
  rw [conditioned_apply_eq_tsum_plane_p43ii μ n _ (measurableSet_finiteTreeEvent_p43ii _),
    conditioned_apply_eq_tsum_plane_p43ii μ n _
      (measurableSet_finiteTreeEvent_p43ii _).compl]
  apply tsum_congr
  intro t
  by_cases ht : (height t : ℝ) < a
  · have hnot : ¬ a ≤ (height t : ℝ) := by linarith
    simp [toLocallyFinite_mem_finiteTreeEvent_iff_p43ii, ht, hnot]
  · have hge : a ≤ (height t : ℝ) := by linarith
    simp [toLocallyFinite_mem_finiteTreeEvent_iff_p43ii, ht, hge]

/-- Proposition 4.3(ii), before filling the frozen wrapper. -/
theorem height_upper (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (h : ℕ → ℝ)
    (hpos : ∀ n, 0 < h n) (hh : Tendsto h atTop atTop)
    (hQ : Tendsto (fun n : ℕ => (n : ℝ) * (survival μ ⌈h n⌉₊).toReal) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => conditioned μ n (finiteTreeEvent fun t => (height t : ℝ) < h n))
      atTop (𝓝 1) := by
  have _ : ∀ n, 0 < h n := hpos
  have hhigh := height_ge_real_tendsto_zero μ hμ h hh hQ
  have hreal : Tendsto
      (fun n : ℕ => (conditioned μ n
        (finiteTreeEvent fun t => (height t : ℝ) < h n)).toReal) atTop (𝓝 1) := by
    have hc := (tendsto_const_nhds (x := (1 : ℝ))).sub hhigh
    simp only [sub_zero] at hc
    apply hc.congr'
    filter_upwards [eventually_size_admissible μ hμ.to_literal] with n hn
    let _ : IsProbabilityMeasure (conditioned μ n) := conditioned_isProbability μ n hn
    rw [conditioned_height_lt_eq_compl_p43ii μ n (h n),
      measure_compl (measurableSet_finiteTreeEvent_p43ii _) (measure_ne_top _ _),
      measure_univ, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
      ENNReal.toReal_one]
  have he := ENNReal.tendsto_ofReal hreal
  simp only [ENNReal.ofReal_one] at he
  apply he.congr'
  filter_upwards [eventually_size_admissible μ hμ.to_literal] with n hn
  let _ : IsProbabilityMeasure (conditioned μ n) := conditioned_isProbability μ n hn
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

end
end SubcriticalCauchy.Bienayme
