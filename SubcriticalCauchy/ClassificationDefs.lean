module

public import SubcriticalCauchy.BienaymeSurvival
public import SubcriticalCauchy.OffspringHypothesis

/-!
# Definitions for the five-case classification (U2.5) — frozen

Approved by the author on 11 November 2026 with the statement in
`SubcriticalCauchy.Classification`, and frozen whole: read only, byte for byte.

* `IsTiltEquivalent μ ν`: Kennedy equivalence, `μ_k = a λ^k ν_k` for all `k`,
  for some `a, λ > 0` (Proposition 2.1 of the paper).
* `HasHeavyTail μ α L`: `μ_n ∼ L(n)/n^{1+α}`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section

/-- Kennedy equivalence: `μ_k = a λ^k ν_k` for all `k`, for some `a, λ > 0`. -/
def IsTiltEquivalent (μ ν : Measure ℕ) : Prop :=
  ∃ a r : ℝ, 0 < a ∧ 0 < r ∧ ∀ k : ℕ, (μ {k}).toReal = a * r ^ k * (ν {k}).toReal

/-- The heavy tail `μ_n ∼ L(n)/n^{1+α}`. -/
def HasHeavyTail (μ : Measure ℕ) (α : ℝ) (L : ℝ → ℝ) : Prop :=
  Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ (1 + α))) atTop (𝓝 1)

end
end SubcriticalCauchy.Bienayme
