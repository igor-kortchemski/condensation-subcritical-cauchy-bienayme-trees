module

public import SubcriticalCauchy.PaperRoute.Defs
public import SubcriticalCauchy.MeasurableHypothesis
public import SubcriticalCauchy.MaximumSwapLaw
public import SubcriticalCauchy.DeletedIncrements
public import SubcriticalCauchy.Centering
public import SubcriticalCauchy.ScalingSublinear
public import SubcriticalCauchy.SlowVariationPrimitive
public import Mathlib.MeasureTheory.Measure.TotalVariation.Defs
public import Mathlib.Probability.ConditionalProbability
public import SubcriticalCauchy.PaperRoute.ALProof
public import SubcriticalCauchy.PaperRoute.BergerProof
public import SubcriticalCauchy.PaperRoute.Eq26Proof
public import SubcriticalCauchy.PaperRoute.Eq33Proof
public import SubcriticalCauchy.PaperRoute.FinalProof

/-!
# The paper's own proof of Theorem 3.1 — frozen statements

Approved by the author on 11 November 2026 ("Ask astra, if astra is ok i'm ok";
the Astra review returned `VERDICT: ACCEPT`), and frozen: this file may change
only inside its five registered `sorry` holes, filled with proof text only.
Definitions are in `SubcriticalCauchy.PaperRoute.Defs` (frozen whole). Proofs
go in the helper modules `SubcriticalCauchy.PaperRoute.ALProof`, `BergerProof`,
`Eq26Proof`, `Eq33Proof` and `FinalProof`, already imported here; they must not
import this file. The paper-route proof must not use the endpoint route D12
(`paper_deleted_maximum_tvDist`, `deleted_maximum_tvDist`,
`endpoint_bridge_mass_div_tendsto_one` or their helpers).

Conventions: `Δ = (0,1]`, so `x + Δ = Set.Ioc x (x + 1)`; `X = ξ - 1` has law
`incrementLaw μ` on `ℤ`; `γ = 1 - m`; a scale is any `a` with
`n P(X ≥ a n) → 1`; `centering μ a n` is the paper's `b_n`;
`ellStarReal L x = ∑_{k ≥ ⌊x⌋} L(k)/k` is `ℓ⋆`. Mathlib's `tvDist` is twice the
paper's total variation distance; `μ[|s]` is the conditional probability (zero
when `μ s = 0`). Uniform limits are written with explicit tolerances `τ`.
-/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Topology

namespace SubcriticalCauchy

noncomputable section

namespace ArmendarizLoulakis

/-- **AL criterion** (Armendáriz–Loulakis, Theorem 1, in the form of its proof,
§§2–3): conditions (2.6) at thresholds `d n`, (3.2) at thresholds `ℓ n` with
scale `c n`, tightness of `S_{n-1}/c n`, and a maximum-tail condition give,
uniformly over `x ≥ max (d n) (ℓ n)`, total variation convergence of the
conditional law of `π T X` given `S_n ∈ x + Δ` to the iid law. AL's
Theorem 1 itself asserts only that some threshold `q_n` exists; this criterion
supplies `q_n = max (d n) (ℓ n)` directly, and its hypothesis `hmax` replaces
AL's maximum-tail bound (3.8), which their proof uses only through
`n P(X̄ > ℓ_n - A c_n) → 0`. No `Δ`-subexponentiality is assumed. -/
theorem al_criterion (ν : Measure ℝ) [IsProbabilityMeasure ν] (d ℓ c : ℕ → ℝ)
    (hc : ∀ᶠ n : ℕ in atTop, 0 < c n)
    (hℓc : Tendsto (fun n : ℕ => ℓ n / c n) atTop atTop)
    (h26 : ∀ τ > 0, ∀ᶠ n : ℕ in atTop, ∀ x : ℝ, d n ≤ x →
      |((Measure.pi fun _ : Fin n => ν) {y | ∑ i, y i ∈ Set.Ioc x (x + 1)}).toReal /
          ((n : ℝ) * (ν (Set.Ioc x (x + 1))).toReal) - 1| ≤ τ)
    (h32 : ∀ A > 0, ∀ τ > 0, ∀ᶠ n : ℕ in atTop, ∀ x y : ℝ, ℓ n ≤ x → |y| ≤ A * c n →
      1 - (ν (Set.Ioc (x - y) (x - y + 1))).toReal / (ν (Set.Ioc x (x + 1))).toReal ≤ τ)
    (htight : ∀ τ > 0, ∃ A : ℝ, ∀ᶠ n : ℕ in atTop,
      ((Measure.pi fun _ : Fin (n - 1) => ν) {y | A * c n < |∑ i, y i|}).toReal ≤ τ)
    (hmax : ∀ A > 0,
      Tendsto (fun n : ℕ => (n : ℝ) * (ν (Set.Ioi (ℓ n - A * c n))).toReal) atTop (𝓝 0)) :
    ∀ τ > 0, ∀ᶠ n : ℕ in atTop, ∀ x : ℝ, max (d n) (ℓ n) ≤ x →
      tvDist (((Measure.pi fun _ : Fin n => ν)[|{y | ∑ i, y i ∈ Set.Ioc x (x + 1)}]).map
          (alSwapDrop n))
        (Measure.pi fun _ : Fin (n - 1) => ν) ≤ τ := by
  exact al_criterion_wrapper ν d ℓ c hc hℓc h26 h32 htight hmax

end ArmendarizLoulakis

namespace Bienayme

/-- **Berger, Theorem 2.4**, index one, specialized to the paper's offspring laws:
`P(W_n - ⌊b_n⌋ = z) ∼ n P(X = z)` jointly as `n → ∞` and `z / a_n → ∞`. -/
theorem berger_local_limit (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal) atTop (𝓝 1)) :
    ∀ τ > 0, ∃ N : ℕ, ∃ R : ℝ, ∀ n ≥ N, ∀ z : ℤ, R * a n ≤ z →
      |((Measure.pi fun _ : Fin n => incrementLaw μ)
            {x | ∑ i, x i = z + ⌊centering μ a n⌋}).toReal /
          ((n : ℝ) * (incrementLaw μ {z}).toReal) - 1| ≤ τ := by
  exact berger_local_limit_of_smallMax μ hμ
    (fun a ha => incrementSum_smallMax_of_fukNagaev μ hμ
      (fun {_} hpos hL hsv hlocal {_} ha => incrementSum_fukNagaev μ hμ.1 hpos hL hsv hlocal ha) a ha)
    a ha

/-- **(2.6) of the paper** (`eq:26`): for every `ε > 0`,
`P(W̄_n ∈ x + Δ) ∼ n P(X̄ ∈ x + Δ)` uniformly in `x ≥ ε n`. -/
theorem paper_eq26 (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (ε : ℝ) (hε : 0 < ε) :
    ∀ τ > 0, ∀ᶠ n : ℕ in atTop, ∀ x : ℝ, ε * n ≤ x →
      |((Measure.pi fun _ : Fin n => centeredIncrementLaw μ)
            {y | ∑ i, y i ∈ Set.Ioc x (x + 1)}).toReal /
          ((n : ℝ) * (centeredIncrementLaw μ (Set.Ioc x (x + 1))).toReal) - 1| ≤ τ := by
  exact paper_eq26_of_berger μ hμ (berger_local_limit μ hμ) ε hε

/-- **Condition (3.3) of the paper** (`eq:33`) with the scale `b̂_n = n ℓ⋆(a_n)`:
tightness of `W̄_n / b̂_n`, `a_n / b̂_n → 0`, `(b_n + γ n) / b̂_n → -1`, and
`P(X̄ ∈ x - y + Δ) / P(X̄ ∈ x + Δ) → 1` uniformly in `x ≥ ε n`, `|y| ≤ A b̂_n`. -/
theorem paper_eq33 (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ < 1) (L : ℝ → ℝ) (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hsv : IsSlowlyVaryingAtTop L) (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2)) atTop (𝓝 1))
    (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal) atTop (𝓝 1)) :
    (∀ τ > 0, ∃ K : ℝ, ∀ᶠ n : ℕ in atTop,
        ((Measure.pi fun _ : Fin n => centeredIncrementLaw μ)
          {y | K * ((n : ℝ) * ellStarReal L (a n)) < |∑ i, y i|}).toReal ≤ τ) ∧
      Tendsto (fun n : ℕ => a n / ((n : ℝ) * ellStarReal L (a n))) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => (centering μ a n + (1 - (offspringMean μ).toReal) * n) /
          ((n : ℝ) * ellStarReal L (a n))) atTop (𝓝 (-1)) ∧
      ∀ ε > 0, ∀ A > 0, ∀ τ > 0, ∀ᶠ n : ℕ in atTop, ∀ x y : ℝ, ε * n ≤ x →
        |y| ≤ A * ((n : ℝ) * ellStarReal L (a n)) →
        |1 - (centeredIncrementLaw μ (Set.Ioc (x - y) (x - y + 1))).toReal /
            (centeredIncrementLaw μ (Set.Ioc x (x + 1))).toReal| ≤ τ := by
  exact paper_eq33_of_tight μ hm L hpos hsv hL hlocal a ha
    (incrementSum_tight_scale μ hm hpos hL hsv hlocal ha)

/-- **Theorem 3.1 by the paper's route**: same statement as the frozen
`paper_deleted_maximum_tvDist`, to be proved from `al_criterion` applied to
`centeredIncrementLaw μ` with `d n = ℓ n = ε n`, `c n = n ℓ⋆(a_n)` and the
corrected window `x = γ n - 2` (R8), using `berger_local_limit`, `paper_eq26`
and `paper_eq33`, without the endpoint route. -/
theorem paper_route_deleted_maximum_tvDist (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) :
    Tendsto (fun n : ℕ => tvDist ((MaximumSwapLaw.bridgeCountsLaw μ n).map (deletedIncrements n))
        (Measure.pi fun _ : Fin (n - 1) => incrementLaw μ))
      atTop (𝓝 0) := by
  exact paper_route_of μ hμ ArmendarizLoulakis.al_criterion (paper_eq26 μ hμ) (paper_eq33 μ)

end Bienayme

end
end SubcriticalCauchy
