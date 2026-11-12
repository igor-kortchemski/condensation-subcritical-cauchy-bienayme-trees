module

public import SubcriticalCauchy.BienaymeSurvival
public import BGW.LocallyFinite.GenerationLaw
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-! # Expected total progeny

Total progeny counts all present addresses, including the root, and takes value
in `ℝ≥0∞` to retain infinite trees. Its generation decomposition allows Tonelli
without first restricting to almost surely finite trees.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace SubcriticalCauchy.Bienayme

noncomputable section

/-- The number of present vertices, with value infinity on infinite trees. -/
def totalProgeny (T : BGW.LocallyFinite.Tree) : ℝ≥0∞ :=
  ∑' _u : {u // BGW.LocallyFinite.Present T u}, (1 : ℝ≥0∞)

/-- Identification with the extended cardinality of the actual vertex set. -/
theorem totalProgeny_eq_encard (T : BGW.LocallyFinite.Tree) :
    totalProgeny T = ({u | BGW.LocallyFinite.Present T u}.encard : ℝ≥0∞) :=
  ENNReal.tsum_set_one _

/-- On finite trees, total progeny is the vertex count used by `sizeEvent`. -/
theorem totalProgeny_eq_ncard (T : BGW.LocallyFinite.Tree)
    (hT : BGW.LocallyFinite.FiniteVertices T) :
    totalProgeny T = ({u | BGW.LocallyFinite.Present T u}.ncard : ℝ≥0∞) := by
  rw [totalProgeny_eq_encard, ← hT.cast_ncard_eq]
  simp

/-- Partition the vertex set by its depth. -/
theorem totalProgeny_eq_tsum_generationSize (T : BGW.LocallyFinite.Tree) :
    totalProgeny T = ∑' n : ℕ, (BGW.LocallyFinite.generationSize T n : ℝ≥0∞) := by
  classical
  rw [totalProgeny, ← ENNReal.tsum_fiberwise (fun _ => (1 : ℝ≥0∞))
    (fun u : {u // BGW.LocallyFinite.Present T u} => u.val.length)]
  apply tsum_congr
  intro n
  let e : {u : {u // BGW.LocallyFinite.Present T u} // u.val.length = n} ≃
      {u // u ∈ BGW.LocallyFinite.generation T n} :=
    { toFun := fun u => ⟨u.val.val,
        (BGW.LocallyFinite.mem_generation T n u.val.val).mpr ⟨u.val.property, u.property⟩⟩
      invFun := fun u => ⟨⟨u.val,
        ((BGW.LocallyFinite.mem_generation T n u.val).mp u.property).1⟩,
        ((BGW.LocallyFinite.mem_generation T n u.val).mp u.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  change (∑' u : {u : {u // BGW.LocallyFinite.Present T u} // u.val.length = n},
    (1 : ℝ≥0∞)) = _
  rw [e.tsum_eq (fun _ => (1 : ℝ≥0∞))]
  simp [BGW.LocallyFinite.generationSize]

/-- Expected total progeny of the actual Bienaymé law. The equality remains
valid at critical and supercritical means, with infinite right-hand side. -/
theorem lintegral_totalProgeny (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    (∫⁻ T, totalProgeny T ∂BGW.LocallyFinite.bienaymeLaw μ) =
      (1 - offspringMean μ)⁻¹ := by
  simp_rw [totalProgeny_eq_tsum_generationSize]
  rw [lintegral_tsum]
  · simp_rw [BGW.LocallyFinite.lintegral_generationSize]
    exact ENNReal.tsum_geometric _
  · intro n
    exact ((measurable_of_countable (fun k : ℕ => (k : ℝ≥0∞))).comp
      (BGW.LocallyFinite.measurable_generationSize n)).aemeasurable

/-- The subcritical formula with the paper's real mean `m`. -/
theorem lintegral_totalProgeny_subcritical (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ < 1) :
    (∫⁻ T, totalProgeny T ∂BGW.LocallyFinite.bienaymeLaw μ) =
      ENNReal.ofReal (1 / (1 - (offspringMean μ).toReal)) := by
  have hfin : offspringMean μ ≠ ∞ := ne_top_of_lt (hm.trans ENNReal.one_lt_top)
  have hmR : (offspringMean μ).toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hfin ENNReal.one_ne_top).mpr hm
  rw [lintegral_totalProgeny, one_div, ENNReal.ofReal_inv_of_pos (sub_pos.mpr hmR),
    ENNReal.ofReal_sub 1 ENNReal.toReal_nonneg, ENNReal.ofReal_one,
    ENNReal.ofReal_toReal hfin]

end
end SubcriticalCauchy.Bienayme
