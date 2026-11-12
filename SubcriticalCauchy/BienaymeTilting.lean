module

public import BGW.LocallyFinite.SizeConditioning

/-!
# Exponential tilting of the constructed Bienaymé law

Proposition 2.1 of the manuscript, on the actual BGW branching-process carrier.
The reused BGW construction supplies the branching property and finite-tree
atoms. Restricting those atoms to a fixed size and cancelling the common tilt
factor proves equality of conditional measures. No subcriticality is needed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SubcriticalCauchy.Bienayme

noncomputable section

attribute [local instance] Classical.propDecidable

open BGW.LocallyFinite

/-- The actual Bienaymé law conditioned on a vertex count. At a null size this
is the zero measure, in accordance with Mathlib's conditional-measure convention. -/
def conditioned (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) : Measure Tree :=
  (bienaymeLaw μ)[|sizeEvent n]

/-- The common product-weight factor for a finite plane tree. -/
theorem bgw_weight_tilt {p q : ℕ → ℝ≥0∞} {a r : ℝ≥0∞}
    (h : ∀ k, p k = a * r ^ k * q k) (t : BGW.PlaneTree) :
    BGW.PlaneTree.weight p t =
      (a ^ t.size * r ^ (t.size - 1)) * BGW.PlaneTree.weight q t := by
  have hlist (ks : List ℕ) :
      (ks.map p).prod = a ^ ks.length * r ^ ks.sum * (ks.map q).prod := by
    induction ks with
    | nil => simp
    | cons k ks ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons,
        List.sum_cons, h k, ih, pow_succ, pow_add]
      ac_rfl
  have hs : t.degrees.sum = t.size - 1 := by
    have := BGW.PlaneTree.sum_degrees_add_one t
    omega
  simpa only [BGW.PlaneTree.weight, BGW.PlaneTree.length_degrees, hs] using
    hlist t.degrees

/-- The size-restricted branching measure is determined by its finite-tree atoms. -/
theorem restrict_sizeEvent_apply (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (n : ℕ) (A : Set Tree) (hA : MeasurableSet A) :
    (bienaymeLaw μ).restrict (sizeEvent n) A =
      ∑' t : BGW.PlaneTree,
        (if t.size = n then BGW.PlaneTree.weight (fun k => μ {k}) t else 0) *
          (if t.toLocallyFinite ∈ A then 1 else 0) := by
  classical
  have hsub : sizeEvent n ⊆ {T : Tree | FiniteVertices T} := fun _ h => h.1
  rw [← Measure.restrict_restrict_of_subset hsub,
    bienaymeLaw_restrict_finiteVertices, Measure.restrict_apply hA,
    Measure.sum_apply _ (hA.inter (measurableSet_sizeEvent n))]
  apply tsum_congr
  intro t
  rw [Measure.smul_apply,
    Measure.dirac_apply' _ (hA.inter (measurableSet_sizeEvent n)), smul_eq_mul]
  by_cases hn : t.size = n <;> by_cases ht : t.toLocallyFinite ∈ A <;>
    simp [hn, ht, toLocallyFinite_mem_sizeEvent_iff]

/-- A finite positive exponential tilt multiplies the entire size-restricted
measure by the same scalar. -/
theorem restrict_sizeEvent_tilt (μ ν : Measure ℕ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {a r : ℝ≥0∞}
    (h : ∀ k, μ {k} = a * r ^ k * ν {k}) (n : ℕ) :
    (bienaymeLaw μ).restrict (sizeEvent n) =
      (a ^ n * r ^ (n - 1)) • (bienaymeLaw ν).restrict (sizeEvent n) := by
  ext A hA
  rw [Measure.smul_apply, smul_eq_mul, restrict_sizeEvent_apply μ n A hA,
    restrict_sizeEvent_apply ν n A hA, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro t
  by_cases hn : t.size = n
  · simp only [hn, ↓reduceIte, bgw_weight_tilt h]
    simp only [mul_assoc]
  · simp only [hn, ↓reduceIte, zero_mul, mul_zero]

/-- Scaling of the mass of the conditioning event, including null sizes. -/
theorem sizeEvent_mass_tilt (μ ν : Measure ℕ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {a r : ℝ≥0∞}
    (h : ∀ k, μ {k} = a * r ^ k * ν {k}) (n : ℕ) :
    bienaymeLaw μ (sizeEvent n) =
      (a ^ n * r ^ (n - 1)) * bienaymeLaw ν (sizeEvent n) := by
  have heq := congrArg (fun M : Measure Tree => M Set.univ)
    (restrict_sizeEvent_tilt μ ν h n)
  simpa using heq

/-- Proposition 2.1: equality of the size-conditioned laws of the constructed
Bienaymé trees under a positive finite exponential tilt. -/
theorem conditioned_tilt (μ ν : Measure ℕ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {a r : ℝ≥0∞}
    (ha0 : a ≠ 0) (hafin : a ≠ ∞) (hr0 : r ≠ 0) (hrfin : r ≠ ∞)
    (h : ∀ k, μ {k} = a * r ^ k * ν {k}) (n : ℕ) :
    conditioned μ n = conditioned ν n := by
  have hc0 : a ^ n * r ^ (n - 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ ha0) (pow_ne_zero _ hr0)
  have hcfin : a ^ n * r ^ (n - 1) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top hafin) (ENNReal.pow_ne_top hrfin)
  ext A hA
  change (bienaymeLaw μ)[|sizeEvent n] A = (bienaymeLaw ν)[|sizeEvent n] A
  simp only [ProbabilityTheory.cond, Measure.smul_apply, smul_eq_mul]
  rw [sizeEvent_mass_tilt μ ν h n,
    congrArg (fun M : Measure Tree => M A) (restrict_sizeEvent_tilt μ ν h n),
    Measure.smul_apply, smul_eq_mul, ENNReal.mul_inv (Or.inl hc0) (Or.inl hcfin)]
  calc
    (a ^ n * r ^ (n - 1))⁻¹ * (bienaymeLaw ν (sizeEvent n))⁻¹ *
        ((a ^ n * r ^ (n - 1)) * (bienaymeLaw ν).restrict (sizeEvent n) A) =
      ((a ^ n * r ^ (n - 1)) * (a ^ n * r ^ (n - 1))⁻¹) *
        ((bienaymeLaw ν (sizeEvent n))⁻¹ * (bienaymeLaw ν).restrict (sizeEvent n) A) := by ac_rfl
    _ = _ := by rw [ENNReal.mul_inv_cancel hc0 hcfin, one_mul]

/-- Exponential equivalence preserves the set of admissible conditioning sizes. -/
theorem admissible_tilt_iff (μ ν : Measure ℕ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {a r : ℝ≥0∞}
    (ha0 : a ≠ 0) (hr0 : r ≠ 0)
    (h : ∀ k, μ {k} = a * r ^ k * ν {k}) (n : ℕ) :
    bienaymeLaw μ (sizeEvent n) ≠ 0 ↔ bienaymeLaw ν (sizeEvent n) ≠ 0 := by
  rw [sizeEvent_mass_tilt μ ν h n]
  have hc0 : a ^ n * r ^ (n - 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ ha0) (pow_ne_zero _ hr0)
  constructor
  · intro hmass hzero
    exact hmass (by rw [hzero, mul_zero])
  · intro hmass
    exact mul_ne_zero hc0 hmass

/-- At an admissible size the conditional measure is a probability law. -/
theorem conditioned_isProbability (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : bienaymeLaw μ (sizeEvent n) ≠ 0) :
    IsProbabilityMeasure (conditioned μ n) :=
  isProbabilityMeasure_cond_sizeEvent μ hn

/-- The positive-real-parameter version of Proposition 2.1. The offspring masses
remain extended nonnegative values, as usual for measure singletons in Mathlib. -/
theorem conditioned_tilt_of_pos (μ ν : Measure ℕ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (h : ∀ k, μ {k} = ENNReal.ofReal a * ENNReal.ofReal r ^ k * ν {k}) (n : ℕ) :
    conditioned μ n = conditioned ν n :=
  conditioned_tilt μ ν (ENNReal.ofReal_ne_zero_iff.mpr ha) ENNReal.ofReal_ne_top
    (ENNReal.ofReal_ne_zero_iff.mpr hr) ENNReal.ofReal_ne_top h n

end
end SubcriticalCauchy.Bienayme
