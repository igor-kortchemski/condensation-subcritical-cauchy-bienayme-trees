module

public import SubcriticalCauchy.PlaneTreeFinite
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Size-conditioned offspring weights

The normalization argument in Proposition `prop:tilting` (Section 2.2).
Weights are defined on actual finite plane trees. The positive and finite
normalization conditions are explicit; relating this construction to a branching
process remains a separate probabilistic characterization obligation.
-/

@[expose] public section

open NNReal ENNReal

namespace SubcriticalCauchy

noncomputable section

/-- Offspring product weight restricted to trees with exactly `n` vertices. -/
def sizeWeight (μ : ℕ → ℝ≥0∞) (n : ℕ) (t : PlaneTree) : ℝ≥0∞ :=
  if t.size = n then t.weight μ else 0

/-- Total offspring product weight of the size-`n` trees. -/
def partition (μ : ℕ → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ := ∑' t, sizeWeight μ n t

/-- The normalized distribution on trees of a fixed size. -/
def conditionedTree (μ : ℕ → ℝ≥0∞) (n : ℕ)
    (h0 : partition μ n ≠ 0) (hfin : partition μ n ≠ ∞) : PMF PlaneTree :=
  PMF.normalize (sizeWeight μ n) h0 hfin

theorem weight_ne_top (μ : PMF ℕ) (t : PlaneTree) : t.weight μ ≠ ∞ := by
  have hlist (ks : List ℕ) : (ks.map μ).prod ≠ ∞ := by
    induction ks with
    | nil => simp
    | cons k ks ih =>
      simp only [List.map_cons, List.prod_cons]
      exact ENNReal.mul_ne_top (μ.apply_ne_top k) ih
  exact hlist t.degrees

/-- For any offspring probability law, the normalizer at a fixed size is finite.
This follows from finite tree enumeration, without an extinction hypothesis. -/
theorem partition_ne_top (μ : PMF ℕ) (n : ℕ) : partition μ n ≠ ∞ := by
  classical
  let s := (PlaneTree.finite_size_eq n).toFinset
  have hs : ∀ t, t ∉ s → sizeWeight μ n t = 0 := by
    intro t ht
    have hsize : t.size ≠ n := by simpa [s] using ht
    simp only [sizeWeight, hsize, ↓reduceIte]
  unfold partition
  rw [tsum_eq_sum hs]
  apply ENNReal.sum_ne_top.mpr
  intro t ht
  by_cases hsize : t.size = n
  · simpa only [sizeWeight, hsize, ↓reduceIte] using weight_ne_top μ t
  · simp only [sizeWeight, hsize, ↓reduceIte, ne_eq, zero_ne_top, not_false_eq_true]

/-- Canonical size-conditioned offspring-product law. Its only admissibility
condition is positive total weight at the requested size. -/
def conditionedTreeOfPMF (μ : PMF ℕ) (n : ℕ) (h0 : partition μ n ≠ 0) :
    PMF PlaneTree := conditionedTree μ n h0 (partition_ne_top μ n)

theorem sizeWeight_tilt {μ ν : ℕ → ℝ≥0∞} {a r : ℝ≥0∞}
    (h : ∀ k, μ k = a * r ^ k * ν k) (n : ℕ) (t : PlaneTree) :
    sizeWeight μ n t = (a ^ n * r ^ (n - 1)) * sizeWeight ν n t := by
  by_cases ht : t.size = n
  · simp only [sizeWeight, ht, ↓reduceIte]
    simpa only [ht] using t.weight_tilt h
  · simp only [sizeWeight, ht, ↓reduceIte, mul_zero]

theorem partition_tilt {μ ν : ℕ → ℝ≥0∞} {a r : ℝ≥0∞}
    (h : ∀ k, μ k = a * r ^ k * ν k) (n : ℕ) :
    partition μ n = (a ^ n * r ^ (n - 1)) * partition ν n := by
  simp only [partition, sizeWeight_tilt h, ENNReal.tsum_mul_left]

/-- Multiplication by a positive finite constant does not change a normalized
mass function. This holds on any carrier, without countability assumptions. -/
theorem normalize_scale {α : Type*} (f : α → ℝ≥0∞) (c : ℝ≥0∞)
    (hc0 : c ≠ 0) (hcfin : c ≠ ∞)
    (hf0 : (∑' x, f x) ≠ 0) (hffin : (∑' x, f x) ≠ ∞)
    (hg0 : (∑' x, c * f x) ≠ 0) (hgfin : (∑' x, c * f x) ≠ ∞) :
    PMF.normalize (fun x => c * f x) hg0 hgfin = PMF.normalize f hf0 hffin := by
  apply PMF.ext
  intro x
  simp only [PMF.normalize_apply, ENNReal.tsum_mul_left]
  exact ENNReal.mul_div_mul_left (f x) (∑' y, f y) hc0 hcfin

/-- Exponential tilting leaves normalized fixed-size offspring-product laws
unchanged. Admissibility and finite normalization are kept explicit. -/
theorem conditionedTree_tilt {μ ν : ℕ → ℝ≥0∞} {a r : ℝ≥0∞}
    (ha0 : a ≠ 0) (hafin : a ≠ ∞) (hr0 : r ≠ 0) (hrfin : r ≠ ∞)
    (h : ∀ k, μ k = a * r ^ k * ν k) (n : ℕ)
    (hμ0 : partition μ n ≠ 0) (hμfin : partition μ n ≠ ∞)
    (hν0 : partition ν n ≠ 0) (hνfin : partition ν n ≠ ∞) :
    conditionedTree μ n hμ0 hμfin = conditionedTree ν n hν0 hνfin := by
  apply PMF.ext
  intro t
  change sizeWeight μ n t * (partition μ n)⁻¹ =
    sizeWeight ν n t * (partition ν n)⁻¹
  rw [sizeWeight_tilt h, partition_tilt h]
  exact ENNReal.mul_div_mul_left _ _
    (mul_ne_zero (pow_ne_zero _ ha0) (pow_ne_zero _ hr0))
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top hafin) (ENNReal.pow_ne_top hrfin))

/-- Proposition 2.1's normalization identity for the canonical fixed-size
offspring-product distributions, with the paper's admissible-size restriction. -/
theorem conditionedTreeOfPMF_tilt (μ ν : PMF ℕ) {a r : ℝ≥0∞}
    (ha0 : a ≠ 0) (hafin : a ≠ ∞) (hr0 : r ≠ 0) (hrfin : r ≠ ∞)
    (h : ∀ k, μ k = a * r ^ k * ν k) (n : ℕ)
    (hμ0 : partition μ n ≠ 0) (hν0 : partition ν n ≠ 0) :
    conditionedTreeOfPMF μ n hμ0 = conditionedTreeOfPMF ν n hν0 :=
  conditionedTree_tilt ha0 hafin hr0 hrfin h n hμ0 (partition_ne_top μ n)
    hν0 (partition_ne_top ν n)

end
end SubcriticalCauchy
