module

public import SubcriticalCauchy.StableLaplaceAux
public import SubcriticalCauchy.StableKernel

/-!
# Laplace analysis for the index-one stable limit

Shared kernel normalization, analytic uniqueness and Laplace weak convergence.
-/
 
@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section

/-- Existence and identification of a weak limit from negative exponential moments. -/
theorem exists_tendsto_of_exponential_laplace_limit
    (Λ : ℝ → ℝ) (hΛ0 : Λ 0 = 0)
    (hΛcont : ContinuousWithinAt (fun s => Real.exp (Λ s)) (Set.Ioi 0) 0)
    (P : ℕ → ProbabilityMeasure ℝ)
    (hL : ∀ s : ℝ, 0 < s → Tendsto
      (fun n => ∫ x, Real.exp (-s * x) ∂(P n : Measure ℝ)) atTop
      (𝓝 (Real.exp (Λ s)))) :
    ∃ Q : ProbabilityMeasure ℝ, Tendsto P atTop (𝓝 Q) ∧
      ∀ s : ℝ, 0 < s → Integrable (fun x => Real.exp (-s * x)) (Q : Measure ℝ) ∧
        ∫ x, Real.exp (-s * x) ∂(Q : Measure ℝ) = Real.exp (Λ s) := by
  have htight : IsTightMeasureSet
      {((P' : ProbabilityMeasure ℝ) : Measure ℝ) | P' ∈ Set.range P} := by
    rw [show {((P' : ProbabilityMeasure ℝ) : Measure ℝ) | P' ∈ Set.range P} =
        Set.range (fun n => (P n : Measure ℝ)) by
      ext μ
      constructor
      · rintro ⟨P', ⟨n, rfl⟩, rfl⟩
        exact ⟨n, rfl⟩
      · rintro ⟨n, rfl⟩
        exact ⟨P n, ⟨n, rfl⟩, rfl⟩]
    exact isTightMeasureSet_range_of_exponential_laplace_limit hΛ0 hΛcont P hL
  have hK : IsCompact (closure (Set.range P)) := isCompact_closure_of_isTightMeasureSet htight
  have hmem : ∀ n, P n ∈ closure (Set.range P) := fun n => subset_closure ⟨n, rfl⟩
  have hsub : ∀ (φ : ℕ → ℕ) (Q : ProbabilityMeasure ℝ), Tendsto φ atTop atTop →
      Tendsto (fun n => P (φ n)) atTop (𝓝 Q) →
      ∀ s : ℝ, 0 < s → Integrable (fun x => Real.exp (-s * x)) (Q : Measure ℝ) ∧
        ∫ x, Real.exp (-s * x) ∂(Q : Measure ℝ) = Real.exp (Λ s) :=
    fun φ Q hφ hQ s hs =>
      laplace_eq_of_exponential_tendsto hQ (fun t ht => (hL t ht).comp hφ) hs
  obtain ⟨Q, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  have hQL := hsub φ Q hφ.tendsto_atTop hlim
  refine ⟨Q, ?_, hQL⟩
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨Q', -, ψ, hψ, hlim'⟩ := hK.tendsto_subseq (x := fun n => P (ns n))
    (fun n => hmem _)
  have hQ'L := hsub (ns ∘ ψ) Q' (hns.comp hψ.tendsto_atTop) hlim'
  have hQQ : (Q' : Measure ℝ) = (Q : Measure ℝ) :=
    measure_eq_of_laplace_eq_Ioi (fun s hs => (hQ'L s hs).1) (fun s hs => (hQL s hs).1)
      (fun s hs => (hQ'L s hs).2.trans (hQL s hs).2.symm)
  have hQeq : Q' = Q := ProbabilityMeasure.toMeasure_injective hQQ
  exact ⟨ψ, hQeq ▸ hlim'⟩

/-- Known-limit form of exponential Laplace convergence. -/
theorem tendsto_of_exponential_laplace_limit_of_laplace_eq
    (Λ : ℝ → ℝ) (hΛ0 : Λ 0 = 0)
    (hΛcont : ContinuousWithinAt (fun s => Real.exp (Λ s)) (Set.Ioi 0) 0)
    (P : ℕ → ProbabilityMeasure ℝ)
    (hL : ∀ s : ℝ, 0 < s → Tendsto
      (fun n => ∫ x, Real.exp (-s * x) ∂(P n : Measure ℝ)) atTop
      (𝓝 (Real.exp (Λ s))))
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hint : ∀ s : ℝ, 0 < s → Integrable (fun x => Real.exp (-s * x)) ν)
    (hνL : ∀ s : ℝ, 0 < s → ∫ x, Real.exp (-s * x) ∂ν = Real.exp (Λ s)) :
    Tendsto P atTop (𝓝 (⟨ν, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  obtain ⟨Q, hPQ, hQL⟩ := exists_tendsto_of_exponential_laplace_limit Λ hΛ0 hΛcont P hL
  have hmeasure : (Q : Measure ℝ) = ν := measure_eq_of_laplace_eq_Ioi
    (fun s hs => (hQL s hs).1) hint (fun s hs => (hQL s hs).2.trans (hνL s hs).symm)
  have hQ : Q = (⟨ν, inferInstance⟩ : ProbabilityMeasure ℝ) :=
    ProbabilityMeasure.toMeasure_injective hmeasure
  exact hQ ▸ hPQ

end
end SubcriticalCauchy.Bienayme
