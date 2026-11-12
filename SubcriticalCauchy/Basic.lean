module

public import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Subcritical Cauchy Bienaymé trees

Starting module for the formalization of
"Condensation in subcritical Cauchy Bienaymé trees" (arXiv:2503.07530v2).

The example below checks the probability library setup. It is not a result
from the paper; the paper's definitions and proofs remain to be formalized.
-/

public section

namespace SubcriticalCauchy

example (p : PMF ℕ) : ∑' n, p n = 1 := by
  exact p.tsum_coe

end SubcriticalCauchy
