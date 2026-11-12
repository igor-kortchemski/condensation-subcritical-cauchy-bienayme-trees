module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The law of `𝒞₁` — frozen definition

Approved by the author on 10 November 2026 with (2.4) and Corollary 4.1, and
frozen whole: this file is read only, byte for byte.

`IsCauchyOneLaw ν`: `ν` is the law of the paper's `𝒞₁`, a probability measure
on ℝ with `E[e^{-λ𝒞₁}] = e^{λ log λ}` for every `λ > 0`.
-/

@[expose] public section

open MeasureTheory

namespace SubcriticalCauchy.Bienayme

noncomputable section

/-- `ν` is the law of `𝒞₁`: `E[e^{-λ𝒞₁}] = e^{λ log λ}` for every `λ > 0`. -/
def IsCauchyOneLaw (ν : Measure ℝ) : Prop :=
  IsProbabilityMeasure ν ∧ ∀ s : ℝ, 0 < s →
    Integrable (fun x => Real.exp (-(s * x))) ν ∧
      ∫ x, Real.exp (-(s * x)) ∂ν = Real.exp (s * Real.log s)

end
end SubcriticalCauchy.Bienayme
