module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The index-one stable kernel (shared interface)

Coordinator-owned interface of `docs/blueprint/STABLE_LIMIT.md` (Nodes 1–4).
`stableKernelIntegral s = ∫_0^∞ (e^{-s x} - 1 + s x 1_{x ≤ 1}) x^{-2} dx` is the
Laplace exponent of the limit of `(W_n - b_n)/a_n`; it equals
`s log s + (γ_E - 1) s` for `s > 0` (to be proved, Node 1).
-/

@[expose] public section

open MeasureTheory

namespace SubcriticalCauchy.Bienayme

noncomputable section

/-- The integrand kernel `e^{-s x} - 1 + s x 1_{x ≤ 1}`. -/
def stableKernel (s x : ℝ) : ℝ :=
  Real.exp (-s * x) - 1 + if x ≤ 1 then s * x else 0

/-- The Laplace exponent `∫_0^∞ stableKernel s x / x² dx`. -/
def stableKernelIntegral (s : ℝ) : ℝ :=
  ∫ x in Set.Ioi 0, stableKernel s x / x ^ 2

end
end SubcriticalCauchy.Bienayme
