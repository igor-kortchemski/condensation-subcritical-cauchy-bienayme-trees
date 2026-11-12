module

public import SubcriticalCauchy.CauchyOneLaw
public import SubcriticalCauchy.LateProofs.Cor41Aux
public import SubcriticalCauchy.LateProofs.Cor41Reindex
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Proof helpers for the frozen statement of Corollary 4.1 (`paper_maxDegree_fluctuations`)

Owned helper module for one registered hole of `SubcriticalCauchy.Corollary41`. It is
imported by the frozen statement file, which must not change except inside its
holes; add the proof and any further imports here. It must not import
`SubcriticalCauchy.Corollary41`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators

namespace SubcriticalCauchy.Bienayme

noncomputable section
open BGW BGW.LocallyFinite

local instance cor41IncrementLawProbability (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (incrementLaw μ) := by
  unfold incrementLaw
  infer_instance

local instance cor41PlaneTreeMeasurableSpace : MeasurableSpace PlaneTree := ⊤

local instance cor41IncrementSumLawProbability (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (n : ℕ) : IsProbabilityMeasure (incrementSumLaw μ n) := by
  unfold incrementSumLaw
  infer_instance

/-- Corollary 4.1 from its input stable limit, with all reindexing and TV
transfer steps discharged. -/
theorem maxDegree_fluctuations_of_stable_limit
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1))
    (h24 : ∀ (a : ℕ → ℝ),
      Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
        atTop (𝓝 1) →
      ∀ (ν : Measure ℝ), IsCauchyOneLaw ν → ∀ f : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun n => ∫ x, f (((∑ i, (x i : ℝ)) - centering μ a n) / a n)
          ∂(Measure.pi fun _ : Fin n => incrementLaw μ)) atTop
          (𝓝 (∫ y, f (y + (1 - Real.eulerMascheroniConstant)) ∂ν)))
    (ν : Measure ℝ) (hν : IsCauchyOneLaw ν) (f : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (fun n : ℕ => ∑' t : PlaneTree, (conditioned μ n {t.toLocallyFinite}).toReal *
        f (((maxDegree t : ℝ) + centering μ a n) / a n))
      atTop (𝓝 (∫ y, f (-y - (1 - Real.eulerMascheroniConstant)) ∂ν)) := by
  let cor41CauchyProbability : IsProbabilityMeasure ν := hν.1
  let η : Measure ℝ := ν.map (fun y => -y - (1 - Real.eulerMascheroniConstant))
  let cor41LimitProbability : IsProbabilityMeasure η := by
    dsimp only [η]
    infer_instance
  let negTest (g : BoundedContinuousFunction ℝ ℝ) : BoundedContinuousFunction ℝ ℝ :=
    { toContinuousMap := ⟨fun x => g (-x), g.continuous.comp continuous_neg⟩
      map_bounded' := g.map_bounded'.imp fun _ hg x y => hg (-x) (-y) }
  have hη (g : BoundedContinuousFunction ℝ ℝ) :
      ∫ z, g z ∂η = ∫ y, g (-y - (1 - Real.eulerMascheroniConstant)) ∂ν := by
    dsimp only [η]
    rw [integral_map (by fun_prop) g.continuous.aestronglyMeasurable]
  let P : ℕ → Measure ℝ := fun n =>
    (Measure.pi fun _ : Fin (n - 1) => incrementLaw μ).map
      (fun x => ((-∑ i, (x i : ℝ)) + centering μ a (n - 1)) / a (n - 1))
  let cor41NormalizedProbability (n : ℕ) : IsProbabilityMeasure (P n) := by
    dsimp only [P]
    infer_instance
  have hP : ∀ g : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n => ∫ z, g z ∂P n) atTop (𝓝 (∫ z, g z ∂η)) := by
    intro g
    have hstable0 := h24 a ha ν hν (negTest g)
    have hstable : Tendsto (fun n : ℕ => ∫ x, negTest g
        (((∑ i, (x i : ℝ)) - centering μ a n) / a n)
          ∂(Measure.pi fun _ : Fin n => incrementLaw μ)) atTop
        (𝓝 (∫ y, g (-y - (1 - Real.eulerMascheroniConstant)) ∂ν)) := by
      simpa only [negTest, BoundedContinuousFunction.coe_mk,
        sub_eq_add_neg, neg_add_rev, neg_neg, add_comm, add_left_comm, add_assoc] using hstable0
    have hshift : Tendsto (fun n : ℕ => ∫ x, negTest g
        (((∑ i, (x i : ℝ)) - centering μ a (n - 1)) / a (n - 1))
          ∂(Measure.pi fun _ : Fin (n - 1) => incrementLaw μ)) atTop
        (𝓝 (∫ y, g (-y - (1 - Real.eulerMascheroniConstant)) ∂ν)) := by
      apply (tendsto_add_atTop_iff_nat (f := fun n : ℕ => ∫ x, negTest g
        (((∑ i, (x i : ℝ)) - centering μ a (n - 1)) / a (n - 1))
          ∂(Measure.pi fun _ : Fin (n - 1) => incrementLaw μ)) 1).mp
      simp only [Nat.add_sub_cancel]
      exact hstable
    have hsrc (n : ℕ) : ∫ z, g z ∂P n = ∫ x, negTest g
        (((∑ i, (x i : ℝ)) - centering μ a (n - 1)) / a (n - 1))
          ∂(Measure.pi fun _ : Fin (n - 1) => incrementLaw μ) := by
      dsimp only [P]
      rw [integral_map (measurable_of_countable _).aemeasurable
        g.continuous.aestronglyMeasurable]
      apply integral_congr_ae
      filter_upwards [] with x
      change g (((-∑ i, (x i : ℝ)) + centering μ a (n - 1)) / a (n - 1)) =
        g (-(((∑ i, (x i : ℝ)) - centering μ a (n - 1)) / a (n - 1)))
      congr 1
      ring
    rw [hη]
    exact hshift.congr' (Eventually.of_forall fun n => (hsrc n).symm)
  let c : ℕ → ℝ := fun n => a (n - 1) / a n
  let d : ℕ → ℝ := fun n => (centering μ a n - centering μ a (n - 1)) / a n
  have hc : Tendsto c atTop (𝓝 1) := scaling_pred_div_tendsto_one μ hμ a ha
  have hd : Tendsto d atTop (𝓝 0) := centering_pred_sub_div_tendsto_zero μ hμ a ha
  have haffine := tendsto_integral_affine_of_forall_boundedContinuous P η hP hc hd f
  let A : ℕ → ℝ := fun n => ∫ z : ℤ, f (((z : ℝ) + centering μ a n) / a n)
    ∂conditionedMaxDegreeLaw μ n
  let B : ℕ → ℝ := fun n => ∫ z : ℤ, f (((z : ℝ) + centering μ a n) / a n)
    ∂incrementSumLaw μ n
  have haTop := scaling_tendsto_atTop μ hμ.to_literal ha
  have hprevTop : Tendsto (fun n : ℕ => a (n - 1)) atTop atTop := by
    apply (tendsto_add_atTop_iff_nat (f := fun n : ℕ => a (n - 1)) 1).mp
    simpa only [Nat.add_sub_cancel] using haTop
  have hlim : Tendsto B atTop
      (𝓝 (∫ y, f (-y - (1 - Real.eulerMascheroniConstant)) ∂ν)) := by
    rw [← hη]
    apply haffine.congr'
    filter_upwards [haTop.eventually_gt_atTop 0,
      hprevTop.eventually_gt_atTop 0] with n han hprevn
    have hprev : a (n - 1) ≠ 0 := hprevn.ne'
    change (∫ x, f (c n * x + d n) ∂P n) = B n
    have hPmap : (∫ x, f (c n * x + d n) ∂P n) = ∫ x, f
        (c n * (((-∑ i, (x i : ℝ)) + centering μ a (n - 1)) / a (n - 1)) + d n)
        ∂(Measure.pi fun _ : Fin (n - 1) => incrementLaw μ) := by
      dsimp only [P]
      exact integral_map (measurable_of_countable _).aemeasurable (by fun_prop)
    have hBmap : B n = ∫ x, f ((((-∑ i, x i : ℤ) : ℝ) + centering μ a n) / a n)
        ∂(Measure.pi fun _ : Fin (n - 1) => incrementLaw μ) := by
      dsimp only [B, incrementSumLaw]
      exact integral_map (measurable_of_countable _).aemeasurable (by fun_prop)
    rw [hPmap, hBmap]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [Int.cast_sum, Int.cast_neg, c, d]
    field_simp [han.ne', hprev]
    ring_nf
  have hAtom (n : ℕ) (hsize : bienaymeLaw μ (sizeEvent n) ≠ 0) :
      (∑' t : PlaneTree, (conditioned μ n {t.toLocallyFinite}).toReal *
        f (((maxDegree t : ℝ) + centering μ a n) / a n)) = A n := by
    let cor41AtomicConditionedProbability : IsProbabilityMeasure (conditioned μ n) :=
      conditioned_isProbability μ n hsize
    dsimp only [A, conditionedMaxDegreeLaw]
    rw [integral_map (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aestronglyMeasurable]
    dsimp only [conditionedPlaneTreeLaw]
    rw [integral_sum_dirac (fun _ => measure_ne_top _ _)]
    simp only [smul_eq_mul, Int.cast_natCast]
  have htv := conditioned_maxDegree_tvDist μ hμ
  let M : ℝ := ‖f‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hupper := htv.const_mul M
  have hupper0 : Tendsto (fun n => M * tvDist (conditionedMaxDegreeLaw μ n)
      (incrementSumLaw μ n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hupper
  have hdiff : Tendsto (fun n => A n - B n) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) _ hupper0
    filter_upwards [eventually_size_admissible μ hμ.to_literal] with n hsize
    let cor41ConditionedProbability : IsProbabilityMeasure (conditionedPlaneTreeLaw μ n) :=
      conditionedPlaneTreeLaw_isProbability μ hsize
    let cor41ConditionedMaxProbability : IsProbabilityMeasure (conditionedMaxDegreeLaw μ n) := by
      dsimp only [conditionedMaxDegreeLaw]
      infer_instance
    exact bounded_integral_sub_le_mul_tvDist _ _ hM (fun z => by
      calc
        |f (((z : ℝ) + centering μ a n) / a n)| =
            ‖f (((z : ℝ) + centering μ a n) / a n)‖ := Real.norm_eq_abs _
        _ ≤ ‖f‖ := f.norm_coe_le_norm _
        _ ≤ M := by dsimp [M]; linarith [norm_nonneg f])
  have hfinal := hlim.add hdiff
  have heq : (fun n => B n + (A n - B n)) =ᶠ[atTop]
      (fun n : ℕ => ∑' t : PlaneTree, (conditioned μ n {t.toLocallyFinite}).toReal *
        f (((maxDegree t : ℝ) + centering μ a n) / a n)) := by
    filter_upwards [eventually_size_admissible μ hμ.to_literal] with n hsize
    rw [← hAtom n hsize]
    ring
  simpa only [add_zero] using hfinal.congr' heq

end
end SubcriticalCauchy.Bienayme
