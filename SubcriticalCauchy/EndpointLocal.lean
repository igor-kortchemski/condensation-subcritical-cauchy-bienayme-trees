module

public import SubcriticalCauchy.EndpointLocalAux

/-!
# Typical residuals and endpoint local bounds

This module proves the typical-residual and insertion lower-bound steps of the
endpoint local limit argument. It does not use the separate no-large-jump
estimate.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology BigOperators

namespace SubcriticalCauchy.Bienayme

/-- **Lemma 5:** a typical residual set with diverging sublinear error scale. -/
theorem endpoint_typical_residual_set
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ < 1)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1)) :
    ∃ h : ℕ → ℝ, Tendsto h atTop atTop ∧
      Tendsto (fun n => h n / (n : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => (Measure.pi fun _ : Fin (n - 1) => μ)
        (endpointResidualSet μ h n)) atTop (𝓝 1) ∧
      ∀ τ : ℝ, 0 < τ → ∀ᶠ n : ℕ in atTop, ∀ z ∈ endpointResidualSet μ h n,
        ∑ i, z i < n - 1 ∧
        (∀ i, z i < n - 1 - ∑ i, z i) ∧
        |(μ {n - 1 - ∑ i, z i}).toReal /
          (μ {⌊(1 - (offspringMean μ).toReal) * n⌋₊}).toReal - 1| < τ := by
  obtain ⟨h, hh, hη, hG⟩ := exists_endpointResidualSet_typical μ hm
  have hG' : Tendsto (fun n : ℕ => (Measure.pi fun _ : Fin (n - 1) => μ)
      (endpointResidualSet μ h n)) atTop (𝓝 1) := by
    have ht := ENNReal.tendsto_ofReal hG
    have heq : (fun n : ℕ => ENNReal.ofReal
        ((Measure.pi fun _ : Fin (n - 1) => μ) (endpointResidualSet μ h n)).toReal) =ᶠ[atTop]
        (fun n : ℕ => (Measure.pi fun _ : Fin (n - 1) => μ) (endpointResidualSet μ h n)) := by
      filter_upwards [] with n
      exact ENNReal.ofReal_toReal (measure_ne_top _ _)
    simpa only [ENNReal.ofReal_one, Measure.real] using ht.congr' heq
  exact ⟨h, hh, hη, hG',
    endpointResidualSet_eventually_good μ hm hpos hL hsv hlocal hh hη⟩

/-- **Lemma 6, lower bound:** strict-maximum insertions from the typical set. -/
theorem endpoint_lower_bound
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ < 1)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1)) :
    ∀ τ : ℝ, 0 < τ → ∀ᶠ n : ℕ in atTop,
      (1 - τ) * n * (μ {⌊(1 - (offspringMean μ).toReal) * n⌋₊}).toReal ≤
        ((Measure.pi fun _ : Fin n => μ) (BGW.countBridges n)).toReal := by
  obtain ⟨h, hh, hη, hG⟩ := exists_endpointResidualSet_typical μ hm
  exact endpoint_lower_bound_with_scale μ hm hpos hL hsv hlocal hh hη hG

/-- **Lemma 6, big-jump upper bound:** the position union bound together with
local regular variation and the weak-law residual estimate. -/
theorem endpoint_bigJump_upper_bound
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ < 1)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1))
    {c : ℝ} (hc : 0 < c) (hcγ : c < 1 - (offspringMean μ).toReal) :
    ∀ τ : ℝ, 0 < τ → ∀ᶠ n : ℕ in atTop,
      ((Measure.pi fun _ : Fin n => μ)
        {ω | ∑ i, ω i = n - 1 ∧ ∃ i, c * n < (ω i : ℝ)}).toReal ≤
        (1 + τ) * n * (μ {⌊(1 - (offspringMean μ).toReal) * n⌋₊}).toReal := by
  obtain ⟨h, hh, hη, hG⟩ := exists_endpointResidualSet_typical μ hm
  exact endpoint_bigJump_upper_with_scale μ hm hpos hL hsv hlocal hh hη hG hc hcγ


end SubcriticalCauchy.Bienayme
