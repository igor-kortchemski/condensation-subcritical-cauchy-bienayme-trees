module

public import SubcriticalCauchy.DeletedIncrements
public import SubcriticalCauchy.BienaymeSurvival

/-!
# Definitions for the paper's own proof of Theorem 3.1 — frozen

Approved by the author on 11 November 2026 together with the statements in
`SubcriticalCauchy.PaperRoute.Statements`, and frozen whole: read only, byte
for byte.

* `firstMaxIndex x` is the least index of a maximal coordinate.
* `alSwapDrop n` swaps the first maximal coordinate of `x ∈ ℝⁿ` with the last
  one and drops the last coordinate (Armendáriz–Loulakis's `π ∘ T`).
* `centeredIncrementLaw μ` is the law of `X̄ = X + (1 - m)` on `ℝ`.
-/

@[expose] public section

open MeasureTheory

namespace SubcriticalCauchy

noncomputable section

namespace ArmendarizLoulakis

/-- The first index of a maximal coordinate. -/
def firstMaxIndex {n : ℕ} (x : Fin (n + 1) → ℝ) : Fin (n + 1) :=
  (Finset.univ.filter fun i => ∀ j, x j ≤ x i).min' (by
    obtain ⟨i, -, hi⟩ := Finset.univ.exists_max_image x Finset.univ_nonempty
    exact ⟨i, by simpa using hi⟩)

/-- AL's `π ∘ T`: swap the first maximal coordinate with the last, drop the last. -/
def alSwapDrop : (n : ℕ) → (Fin n → ℝ) → (Fin (n - 1) → ℝ)
  | 0, _ => fun i => i.elim0
  | n + 1, x => fun i => x (Equiv.swap (firstMaxIndex x) (Fin.last n) i.castSucc)

end ArmendarizLoulakis

namespace Bienayme

/-- The law of `X̄ = X + (1 - m)` on `ℝ`. -/
def centeredIncrementLaw (μ : Measure ℕ) : Measure ℝ :=
  (incrementLaw μ).map fun k : ℤ => (k : ℝ) + (1 - (offspringMean μ).toReal)

end Bienayme

end
end SubcriticalCauchy
