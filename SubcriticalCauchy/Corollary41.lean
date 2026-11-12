module

public import SubcriticalCauchy.MeasurableHypothesis
public import SubcriticalCauchy.MaxDegree
public import SubcriticalCauchy.BienaymeTilting
public import SubcriticalCauchy.Centering
public import SubcriticalCauchy.CauchyOneLaw
public import SubcriticalCauchy.LateProofs.C1Exists
public import SubcriticalCauchy.LateProofs.StableLimit
public import SubcriticalCauchy.LateProofs.Cor41
public import SubcriticalCauchy.ScalingSublinear
public import SubcriticalCauchy.DeletedIncrements
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# (2.4) and Corollary 4.1 — frozen statements

Approved by the author on 10 November 2026 (with the corrections R9), and
frozen: this file may change only inside its three registered `sorry` holes,
filled with proof text only. Proofs go in the helper modules
`SubcriticalCauchy.LateProofs.C1Exists`, `StableLimit` and `Cor41`, already
imported here; they must not import this file.

`IsCauchyOneLaw ν` (frozen in `SubcriticalCauchy.CauchyOneLaw`): `ν` is the
law of `𝒞₁`.

A scale is any `a : ℕ → ℝ` with `n P(X ≥ a n) → 1` (`incrementTail`), and
`centering μ a n = n E[X 1_{|X| ≤ a n}]` is the paper's `b_n` exactly.
Convergence in distribution is stated against every bounded continuous test
function. The law of `𝒯_n` is the sum of its atoms over finite plane trees.

**Correction R9.** With exactly this `b_n`, the limits carry the deterministic
shift `1 - γ_E` (γ_E the Euler–Mascheroni constant): `(W_n - b_n)/a_n → 𝒞₁ + (1-γ_E)`
and `(Δ(𝒯_n) + b_n)/a_n → -𝒞₁ - (1-γ_E)`. The paper states the limits
without the shift. Quantifying over every `ν` with `IsCauchyOneLaw ν` makes
the statements independent of the choice of `𝒞₁` (its law is determined by
the Laplace transform).
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section
open BGW BGW.LocallyFinite

/-- The law of `𝒞₁` exists. -/
theorem exists_cauchyOneLaw : ∃ ν : Measure ℝ, IsCauchyOneLaw ν := by
  exact cauchyOneLaw_exists_of_oneStep (oneStepLaplaceLimit_holds c1WitnessMeasure)

/-- (2.4), corrected (R9): `(X₁ + ⋯ + X_n - b_n)/a_n → 𝒞₁ + (1 - γ_E)` in distribution. -/
theorem paper_stable_limit (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal) atTop (𝓝 1))
    (ν : Measure ℝ) (hν : IsCauchyOneLaw ν) (f : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (fun n : ℕ => ∫ x, f (((∑ i, (x i : ℝ)) - centering μ a n) / a n)
        ∂(Measure.pi fun _ : Fin n => incrementLaw μ))
      atTop (𝓝 (∫ y, f (y + (1 - Real.eulerMascheroniConstant)) ∂ν)) := by
  exact stable_limit_of_oneStep μ hμ (oneStepLaplaceLimit_holds μ) a ha ν hν f

/-- Corollary 4.1, corrected (R9): `(Δ(𝒯_n) + b_n)/a_n → -𝒞₁ - (1 - γ_E)` in distribution. -/
theorem paper_maxDegree_fluctuations (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal) atTop (𝓝 1))
    (ν : Measure ℝ) (hν : IsCauchyOneLaw ν) (f : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (fun n : ℕ => ∑' t : PlaneTree, (conditioned μ n {t.toLocallyFinite}).toReal *
        f (((maxDegree t : ℝ) + centering μ a n) / a n))
      atTop (𝓝 (∫ y, f (-y - (1 - Real.eulerMascheroniConstant)) ∂ν)) := by
  exact maxDegree_fluctuations_of_stable_limit μ hμ a ha
    (fun a ha ν hν f => paper_stable_limit μ hμ a ha ν hν f) ν hν f

end
end SubcriticalCauchy.Bienayme
