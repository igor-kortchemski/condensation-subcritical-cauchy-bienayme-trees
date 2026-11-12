module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

import Mathlib.Tactic.FunProp

/-! # Affine perturbations of bounded-continuous weak limits -/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section

/-- Deterministic affine perturbations with scale tending to one and shift
tending to zero preserve every bounded-continuous weak limit. -/
theorem tendsto_integral_affine_of_forall_boundedContinuous
    (P : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (P n)]
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hP : ∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n => ∫ x, f x ∂P n) atTop (𝓝 (∫ y, f y ∂ν)))
    {c d : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 1)) (hd : Tendsto d atTop (𝓝 0))
    (f : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (fun n => ∫ x, f (c n * x + d n) ∂P n) atTop (𝓝 (∫ y, f y ∂ν)) := by
  let Λ : Measure (ℕ → ℝ) := Measure.infinitePi P
  let _ : IsProbabilityMeasure Λ := by
    dsimp only [Λ]
    infer_instance
  have hX : ∀ n, AEMeasurable (fun ω : ℕ → ℝ => ω n) Λ := fun n => by
    exact (measurable_pi_apply n).aemeasurable
  have hXZ : TendstoInDistribution (fun n (ω : ℕ → ℝ) => ω n) atTop id
      (fun _ => Λ) ν := by
    refine (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ hX
      measurable_id.aemeasurable).2 ?_
    intro g
    have hcomp (n : ℕ) : ∫ ω, g (ω n) ∂Λ = ∫ x, g x ∂P n := by
      dsimp only [Λ]
      rw [← Measure.infinitePi_map_eval P n,
        integral_map (measurable_pi_apply n).aemeasurable
          g.continuous.aestronglyMeasurable]
    simpa only [hcomp, id_eq] using hP g
  have hparams : Tendsto (fun n => (c n, d n)) atTop (𝓝 ((1, 0) : ℝ × ℝ)) :=
    hc.prodMk_nhds hd
  have hY : TendstoInMeasure Λ (fun n (_ : ℕ → ℝ) => (c n, d n)) atTop
      (fun _ => (1, 0)) := by
    apply tendstoInMeasure_of_tendsto_ae
      (fun _ => measurable_const.aestronglyMeasurable)
    exact Eventually.of_forall fun _ => hparams
  have hout := hXZ.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun q : ℝ × (ℝ × ℝ) => q.2.1 * q.1 + q.2.2) (by fun_prop)
    hY (fun _ => measurable_const.aemeasurable)
  have hfout := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    (fun _ => by fun_prop) (by fun_prop)).1 hout f
  have hcomp (n : ℕ) : ∫ ω, f (c n * ω n + d n) ∂Λ =
      ∫ x, f (c n * x + d n) ∂P n := by
    dsimp only [Λ]
    rw [← Measure.infinitePi_map_eval P n,
      integral_map (measurable_pi_apply n).aemeasurable (by fun_prop)]
  simpa only [one_mul, zero_add, id_eq, hcomp, add_zero] using hfout

end
end SubcriticalCauchy.Bienayme
