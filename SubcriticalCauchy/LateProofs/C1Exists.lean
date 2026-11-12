module

public import SubcriticalCauchy.LateProofs.StableLimit
public import SubcriticalCauchy.StableOneStep
public import SubcriticalCauchy.LateProofs.C1Witness

/-!
# Existence of the law of `𝒞₁`

The explicit logarithmic offspring law is combined with the Laplace existence
and normalized-product machinery. The one-step asymptotic is the sole analytic
hypothesis supplied by Node 3.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace SubcriticalCauchy.Bienayme

noncomputable section

/-- The one-step Laplace limit holds for every law satisfying the hypothesis
(Node 3, `oneStep_increment_laplace_exponent_tendsto`). -/
theorem oneStepLaplaceLimit_holds (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    OneStepLaplaceLimit μ :=
  fun hμ a ha _ hs => oneStep_increment_laplace_exponent_tendsto μ hμ a ha hs

/-- Existence of `𝒞₁`, conditional on the Node 3 one-step limit for the witness. -/
theorem cauchyOneLaw_exists_of_oneStep
    (hOne : OneStepLaplaceLimit c1WitnessMeasure) :
    ∃ ν : Measure ℝ, IsCauchyOneLaw ν := by
  let c : ℝ := 1 - Real.eulerMascheroniConstant
  let Λ : ℝ → ℝ := fun s => s * Real.log s + (Real.eulerMascheroniConstant - 1) * s
  have hμ : IsMeasurableSubcriticalCauchyOffspring c1WitnessMeasure :=
    c1Witness_isMeasurableSubcriticalCauchyOffspring
  obtain ⟨a, ha⟩ := exists_scaling c1WitnessMeasure hμ
  have hL : ∀ s : ℝ, 0 < s → Tendsto
      (fun n => ∫ x, Real.exp (-s * x) ∂(normalizedIncrementLaw c1WitnessMeasure a n : Measure ℝ))
      atTop (𝓝 (Real.exp (Λ s))) := by
    intro s hs
    exact normalizedIncrementLaw_laplace_tendsto c1WitnessMeasure hμ hOne a ha hs
  have hΛ0 : Λ 0 = 0 := by simp [Λ]
  have hΛcont : ContinuousWithinAt (fun s => Real.exp (Λ s)) (Set.Ioi 0) 0 := by
    have hc : Continuous Λ := Real.continuous_mul_log.add (continuous_const.mul continuous_id)
    exact hc.rexp.continuousWithinAt
  obtain ⟨Q, -, hQL⟩ := exists_tendsto_of_exponential_laplace_limit
    Λ hΛ0 hΛcont (normalizedIncrementLaw c1WitnessMeasure a) hL
  let ν : Measure ℝ := (Q : Measure ℝ).map (fun x => x - c)
  let c1TranslatedProbability : IsProbabilityMeasure ν := by
    dsimp only [ν]
    infer_instance
  have hmap : AEMeasurable (fun x : ℝ => x - c) (Q : Measure ℝ) := by fun_prop
  refine ⟨ν, c1TranslatedProbability, fun s hs => ?_⟩
  have hint : Integrable (fun x => Real.exp (-s * x)) ν := by
    apply (integrable_map_measure (by fun_prop) hmap).2
    have hbase := (hQL s hs).1.const_mul (Real.exp (s * c))
    apply hbase.congr
    filter_upwards [] with x
    rw [← Real.exp_add]
    congr 1
    ring
  refine ⟨by simpa only [neg_mul] using hint, ?_⟩
  rw [show (∫ x, Real.exp (-(s * x)) ∂ν) =
      ∫ x, Real.exp (-s * (x - c)) ∂(Q : Measure ℝ) by
    simp only [neg_mul]
    exact integral_map hmap (by fun_prop)]
  calc
    (∫ x, Real.exp (-s * (x - c)) ∂(Q : Measure ℝ)) =
        Real.exp (s * c) * ∫ x, Real.exp (-s * x) ∂(Q : Measure ℝ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [← Real.exp_add]
      congr 1
      ring
    _ = Real.exp (s * c) * Real.exp (Λ s) := by rw [(hQL s hs).2]
    _ = Real.exp (s * Real.log s) := by
      rw [← Real.exp_add]
      congr 1
      dsimp only [Λ, c]
      ring

end
end SubcriticalCauchy.Bienayme
