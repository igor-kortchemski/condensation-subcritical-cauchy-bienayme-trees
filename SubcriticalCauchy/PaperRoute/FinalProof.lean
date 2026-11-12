module

public import SubcriticalCauchy.PaperRoute.FinalProofAux

/-!
# Theorem 3.1 by the paper's route

This module proves the final implication from AL, (2.6), and (3.3).  It does
not import the frozen statements and does not use the endpoint route.
-/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section

/-- Conditional form of `paper_route_deleted_maximum_tvDist`, with its three
analytic inputs exposed for separate proof. -/
theorem paper_route_of (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ)
    (hAL : ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν] (d ℓ c : ℕ → ℝ),
    (∀ᶠ n : ℕ in atTop, 0 < c n) →
    (Tendsto (fun n : ℕ => ℓ n / c n) atTop atTop) →
    (∀ τ > 0, ∀ᶠ n : ℕ in atTop, ∀ x : ℝ, d n ≤ x →
      |((Measure.pi fun _ : Fin n => ν) {y | ∑ i, y i ∈ Set.Ioc x (x + 1)}).toReal /
          ((n : ℝ) * (ν (Set.Ioc x (x + 1))).toReal) - 1| ≤ τ) →
    (∀ A > 0, ∀ τ > 0, ∀ᶠ n : ℕ in atTop, ∀ x y : ℝ, ℓ n ≤ x → |y| ≤ A * c n →
      1 - (ν (Set.Ioc (x - y) (x - y + 1))).toReal / (ν (Set.Ioc x (x + 1))).toReal ≤ τ) →
    (∀ τ > 0, ∃ A : ℝ, ∀ᶠ n : ℕ in atTop,
      ((Measure.pi fun _ : Fin (n - 1) => ν) {y | A * c n < |∑ i, y i|}).toReal ≤ τ) →
    (∀ A > 0,
      Tendsto (fun n : ℕ => (n : ℝ) * (ν (Set.Ioi (ℓ n - A * c n))).toReal) atTop (𝓝 0)) →
    ∀ τ > 0, ∀ᶠ n : ℕ in atTop, ∀ x : ℝ, max (d n) (ℓ n) ≤ x →
      tvDist (((Measure.pi fun _ : Fin n => ν)[|{y | ∑ i, y i ∈ Set.Ioc x (x + 1)}]).map
          (ArmendarizLoulakis.alSwapDrop n))
        (Measure.pi fun _ : Fin (n - 1) => ν) ≤ τ)
    (h26 : ∀ ε : ℝ, 0 < ε → ∀ τ > 0, ∀ᶠ n : ℕ in atTop, ∀ x : ℝ, ε * n ≤ x →
      |((Measure.pi fun _ : Fin n => centeredIncrementLaw μ)
            {y | ∑ i, y i ∈ Set.Ioc x (x + 1)}).toReal /
          ((n : ℝ) * (centeredIncrementLaw μ (Set.Ioc x (x + 1))).toReal) - 1| ≤ τ)
    (h33 : offspringMean μ < 1 → ∀ L : ℝ → ℝ, (∀ x : ℝ, 0 < x → 0 < L x) →
      IsSlowlyVaryingAtTop L → AEMeasurable L (volume.restrict (Set.Ioi 0)) →
      (Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2)) atTop (𝓝 1)) →
      ∀ a : ℕ → ℝ,
      (Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal) atTop (𝓝 1)) →
      (∀ τ > 0, ∃ K : ℝ, ∀ᶠ n : ℕ in atTop,
        ((Measure.pi fun _ : Fin n => centeredIncrementLaw μ)
          {y | K * ((n : ℝ) * ellStarReal L (a n)) < |∑ i, y i|}).toReal ≤ τ) ∧
      Tendsto (fun n : ℕ => a n / ((n : ℝ) * ellStarReal L (a n))) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => (centering μ a n + (1 - (offspringMean μ).toReal) * n) /
          ((n : ℝ) * ellStarReal L (a n))) atTop (𝓝 (-1)) ∧
      ∀ ε > 0, ∀ A > 0, ∀ τ > 0, ∀ᶠ n : ℕ in atTop, ∀ x y : ℝ, ε * n ≤ x →
        |y| ≤ A * ((n : ℝ) * ellStarReal L (a n)) →
        |1 - (centeredIncrementLaw μ (Set.Ioc (x - y) (x - y + 1))).toReal /
            (centeredIncrementLaw μ (Set.Ioc x (x + 1))).toReal| ≤ τ) :
    Tendsto (fun n : ℕ => tvDist ((MaximumSwapLaw.bridgeCountsLaw μ n).map (deletedIncrements n))
        (Measure.pi fun _ : Fin (n - 1) => incrementLaw μ))
      atTop (𝓝 0) := by
  have hm : offspringMean μ < 1 := hμ.1
  obtain ⟨L, hpos, hsv, hmeas, hlocal, hsum, -, hell, -⟩ :=
    paper_integratedTail_properties μ hμ
  obtain ⟨a, ha⟩ := exists_scaling μ hμ
  obtain ⟨htight33, hac, -, h32all⟩ := h33 hm L hpos hsv hmeas hlocal a ha
  let γ : ℝ := 1 - (offspringMean μ).toReal
  let ε : ℝ := γ / 2
  let c : ℕ → ℝ := fun n => (n : ℝ) * ellStarReal L (a n)
  have hmfin : offspringMean μ ≠ ∞ := ne_top_of_lt (hm.trans ENNReal.one_lt_top)
  have hmreal : (offspringMean μ).toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hmfin ENNReal.one_ne_top).mpr hm
  have hγ : 0 < γ := sub_pos.mpr hmreal
  have hε : 0 < ε := by positivity
  have hεγ : ε < γ := by dsimp [ε]; linarith
  have haTop : Tendsto a atTop atTop := scaling_tendsto_atTop μ hμ.to_literal ha
  have hella : Tendsto (fun n : ℕ => ellStarReal L (a n)) atTop (𝓝 0) := hell.comp haTop
  have hcpos : ∀ᶠ n : ℕ in atTop, 0 < c n := final_scale_pos hpos hsum a
  have hℓc : Tendsto (fun n : ℕ => (ε * n) / c n) atTop atTop :=
    final_linear_div_scale_tendsto_atTop hpos hsum hella hε
  have hac' : Tendsto (fun n : ℕ => a n / c n) atTop (𝓝 0) := hac
  have hc : Tendsto c atTop atTop := final_scale_tendsto_atTop haTop hac' hcpos
  have hcdiv : Tendsto (fun n : ℕ => c n / (n : ℝ)) atTop (𝓝 0) :=
    final_scale_div_nat_tendsto_zero hella
  let finalIncrementProbability : IsProbabilityMeasure (incrementLaw μ) := by
    unfold incrementLaw
    infer_instance
  let finalCenteredProbability : IsProbabilityMeasure (centeredIncrementLaw μ) := by
    unfold centeredIncrementLaw
    infer_instance
  have h32 : ∀ A > 0, ∀ τ > 0, ∀ᶠ n : ℕ in atTop, ∀ x y : ℝ, ε * n ≤ x →
      |y| ≤ A * c n →
      1 - (centeredIncrementLaw μ (Set.Ioc (x - y) (x - y + 1))).toReal /
        (centeredIncrementLaw μ (Set.Ioc x (x + 1))).toReal ≤ τ := by
    intro A hA τ hτ
    filter_upwards [h32all ε hε A hA τ hτ] with n hn x y hx hy
    exact (le_abs_self _).trans (hn x y hx hy)
  have htight : ∀ τ > 0, ∃ A : ℝ, ∀ᶠ n : ℕ in atTop,
      ((Measure.pi fun _ : Fin (n - 1) => centeredIncrementLaw μ)
        {y | A * c n < |∑ i, y i|}).toReal ≤ τ :=
    final_predecessor_tight (centeredIncrementLaw μ) c hc htight33
  have hmax : ∀ A > 0, Tendsto (fun n : ℕ => (n : ℝ) *
      (centeredIncrementLaw μ (Set.Ioi (ε * n - A * c n))).toReal) atTop (𝓝 0) := by
    intro A hA
    exact final_hmax_linear μ hm hε c hcdiv A hA
  have hALout := hAL (centeredIncrementLaw μ) (fun n => ε * n) (fun n => ε * n) c
    hcpos hℓc (h26 ε hε) h32 htight hmax
  rw [Metric.tendsto_atTop]
  intro τ hτ
  apply eventually_atTop.1
  filter_upwards [hALout (τ / 2) (by positivity), corrected_window_eventually_ge hεγ,
    eventually_gt_atTop (0 : ℕ)] with n hn hnwin hnpos
  have hx := hn (γ * n - 2) (by simpa only [max_self] using hnwin)
  change tvDist (((Measure.pi fun _ : Fin n => centeredIncrementLaw μ)[|
    {y | ∑ i, y i ∈ Set.Ioc (γ * n - 2) (γ * n - 2 + 1)}]).map
      (ArmendarizLoulakis.alSwapDrop n))
    (Measure.pi fun _ : Fin (n - 1) => centeredIncrementLaw μ) ≤ τ / 2 at hx
  have hwindow : γ * (n : ℝ) - 2 + 1 = γ * (n : ℝ) - 1 := by ring
  rw [hwindow, final_al_deleted_tvDist μ (Nat.ne_of_gt hnpos)] at hx
  rw [Real.dist_eq, sub_zero, abs_of_nonneg tvDist_nonneg]
  linarith

end
end SubcriticalCauchy.Bienayme
