module

public import SubcriticalCauchy.MultiplicativeUniformSlowVariation
public import SubcriticalCauchy.SlowVariationPrimitive
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

import Mathlib.Tactic.FieldSimp

/-!
# Slow variation and integer rounding

The sequential uniform-convergence theorem extends to countably generated
filters through the proved sequential filter criterion. In particular both
integer roundings preserve the original slowly varying function asymptotically.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace SubcriticalCauchy

theorem slowlyVarying_uniform_filter {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hfixed : ∀ a : ℝ, 0 < a →
      Tendsto (fun x : ℝ => L (a * x) / L x) atTop (𝓝 1))
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {x a : ι → ℝ} {c : ℝ} (hx : Tendsto x l atTop)
    (ha : Tendsto a l (𝓝 c)) (hc : 0 < c) :
    Tendsto (fun i => L (a i * x i) / L (x i)) l (𝓝 1) := by
  apply Filter.tendsto_iff_seq_tendsto.mpr
  intro u hu
  simpa only [Function.comp_def] using
    slowlyVarying_uniform_sequential hpos hL hfixed (hx.comp hu) (ha.comp hu) hc

theorem slowlyVarying_ratio_of_relative_tendsto_one_filter {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hfixed : ∀ a : ℝ, 0 < a →
      Tendsto (fun x : ℝ => L (a * x) / L x) atTop (𝓝 1))
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {x y : ι → ℝ} (hx : Tendsto x l atTop)
    (hr : Tendsto (fun i => y i / x i) l (𝓝 1)) :
    Tendsto (fun i => L (y i) / L (x i)) l (𝓝 1) := by
  apply (slowlyVarying_uniform_filter hpos hL hfixed hx hr zero_lt_one).congr'
  filter_upwards [hx.eventually_gt_atTop 0] with i hi
  simp only [div_mul_cancel₀ _ hi.ne']

theorem localModel_floor_div_tendsto_one {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hfixed : ∀ a : ℝ, 0 < a →
      Tendsto (fun x : ℝ => L (a * x) / L x) atTop (𝓝 1)) :
    Tendsto (fun x : ℝ => L (Nat.floor x) / L x) atTop (𝓝 1) :=
  slowlyVarying_ratio_of_relative_tendsto_one_filter hpos hL hfixed tendsto_id
    tendsto_nat_floor_div_atTop

theorem localModel_ceil_div_tendsto_one {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hfixed : ∀ a : ℝ, 0 < a →
      Tendsto (fun x : ℝ => L (a * x) / L x) atTop (𝓝 1)) :
    Tendsto (fun x : ℝ => L (Nat.ceil x) / L x) atTop (𝓝 1) :=
  slowlyVarying_ratio_of_relative_tendsto_one_filter hpos hL hfixed tendsto_id
    tendsto_nat_ceil_div_atTop

@[simp] theorem ellStarReal_natCast (L : ℝ → ℝ) (n : ℕ) :
    ellStarReal L (n : ℝ) = ellStar L n := by simp [ellStarReal]

theorem ellStarReal_tendsto_zero (L : ℝ → ℝ) :
    Tendsto (ellStarReal L) atTop (𝓝 0) :=
  (ellStar_tendsto_zero L).comp tendsto_nat_floor_atTop

/-- Floor and ceiling extensions of the source's integer tail are equivalent. -/
theorem ellStar_ceil_div_floor_tendsto_one {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hfixed : ∀ a : ℝ, 0 < a →
      Tendsto (fun x : ℝ => L (a * x) / L x) atTop (𝓝 1))
    (hsum : Summable (fun k : ℕ => L k / (k : ℝ))) :
    Tendsto (fun x : ℝ => ellStar L (Nat.ceil x) / ellStar L (Nat.floor x))
      atTop (𝓝 1) := by
  have hfloor : Tendsto (fun x : ℝ => Nat.floor x) atTop atTop := tendsto_nat_floor_atTop
  have hceil : Tendsto (fun x : ℝ => Nat.ceil x) atTop atTop := tendsto_nat_ceil_atTop
  have hratio : Tendsto (fun x : ℝ => (Nat.ceil x : ℝ) / (Nat.floor x : ℝ))
      atTop (𝓝 1) := by
    have h : Tendsto (fun x : ℝ => ((Nat.ceil x : ℝ) / x) / ((Nat.floor x : ℝ) / x))
        atTop (𝓝 (1 / 1 : ℝ)) :=
      tendsto_nat_ceil_div_atTop.div tendsto_nat_floor_div_atTop one_ne_zero
    have h' : Tendsto (fun x : ℝ => ((Nat.ceil x : ℝ) / x) / ((Nat.floor x : ℝ) / x))
        atTop (𝓝 1) := by simpa only [div_one] using h
    apply h'.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ), hfloor.eventually_gt_atTop 0] with x hx hnx
    have hn0 : (Nat.floor x : ℝ) ≠ 0 := (Nat.cast_pos.mpr hnx).ne'
    field_simp [hx.ne', hn0]
  exact ellStar_ratio_of_index_ratio hpos hL hfixed hsum zero_lt_one hfloor hceil hratio

/-- The source's negligible-factor assertion holds for the original real L,
not only for its integer samples. -/
theorem localModel_div_ellStarReal_tendsto_zero {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hfixed : ∀ a : ℝ, 0 < a →
      Tendsto (fun x : ℝ => L (a * x) / L x) atTop (𝓝 1))
    (hsum : Summable (fun k : ℕ => L k / (k : ℝ))) :
    Tendsto (fun x : ℝ => L x / ellStarReal L x) atTop (𝓝 0) := by
  have hleft : Tendsto (fun x : ℝ => L x / L (Nat.floor x)) atTop (𝓝 1) := by
    simpa only [Pi.inv_apply, inv_div, inv_one] using
      (localModel_floor_div_tendsto_one hpos hL hfixed).inv₀ one_ne_zero
  have hright := (localModel_div_ellStar_tendsto_zero hpos hL hfixed hsum).comp
    (tendsto_nat_floor_atTop (α := ℝ))
  have hprod := hleft.mul hright
  have heq : (fun x : ℝ => (L x / L (Nat.floor x)) *
      (L (Nat.floor x) / ellStar L (Nat.floor x))) =ᶠ[atTop]
      (fun x : ℝ => L x / ellStarReal L x) := by
    filter_upwards [(tendsto_nat_floor_atTop (α := ℝ)).eventually_gt_atTop 0] with x hx
    have hLn : L (Nat.floor x) ≠ 0 := (hpos _ (Nat.cast_pos.mpr hx)).ne'
    have htail : ellStar L (Nat.floor x) ≠ 0 := (ellStar_pos_all hpos hsum _).ne'
    dsimp only [ellStarReal]
    field_simp [hLn, htail]
  simpa only [one_mul, Function.comp_def] using hprod.congr' heq

namespace Bienayme

/-- Lemma 2.2(i), with the author-approved measurable convention and an
explicit real extension agreeing with the source series at integer arguments. -/
theorem paper_integratedTail_properties
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) :
    ∃ L : ℝ → ℝ, (∀ x : ℝ, 0 < x → 0 < L x) ∧ IsSlowlyVaryingAtTop L ∧
      AEMeasurable L (volume.restrict (Set.Ioi 0)) ∧
      Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2)) atTop (𝓝 1) ∧
      Summable (fun k : ℕ => L k / (k : ℝ)) ∧
      IsSlowlyVaryingAtTop (ellStarReal L) ∧ Tendsto (ellStarReal L) atTop (𝓝 0) ∧
      Tendsto (fun x : ℝ => L x / ellStarReal L x) atTop (𝓝 0) := by
  obtain ⟨hm, L, hpos, hsv, hmeas, hlocal⟩ := hμ
  have hfin := ne_top_of_lt (hm.trans ENNReal.one_lt_top)
  have hsum := summable_localModel_over_nat μ hfin hpos hlocal
  exact ⟨L, hpos, hsv, hmeas, hlocal, hsum,
    ellStarReal_slowlyVarying hpos hmeas hsv hsum, ellStarReal_tendsto_zero L,
    localModel_div_ellStarReal_tendsto_zero hpos hmeas hsv hsum⟩

end Bienayme

end SubcriticalCauchy
