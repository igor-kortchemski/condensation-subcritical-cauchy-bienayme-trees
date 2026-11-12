module

public import SubcriticalCauchy.IncrementTailAux
public import SubcriticalCauchy.ScalingSublinear
public import SubcriticalCauchy.CenteringTailSeries
public import SubcriticalCauchy.MeasurableHypothesis

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Increment-tail asymptotics and existence of the Cauchy scale
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section
attribute [local instance] Classical.propDecidable

private def incrementMass (μ : Measure ℕ) (n : ℕ) : ℝ := (μ {n}).toReal

private theorem summable_incrementMass (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    Summable (incrementMass μ) := by
  change Summable (fun n : ℕ => (μ {n}).toReal)
  simpa using summable_pgfReal μ 1 zero_le_one le_rfl

private theorem incrementTail_toReal_eq_tailMass (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (x : ℝ) : (incrementTail μ x).toReal =
      tailMass (incrementMass μ) (Nat.ceil (x + 1)) := by
  rw [incrementTail, measure_toReal_eq_tsum]
  have heq (k : ℕ) : (x ≤ (k : ℝ) - 1) ↔ Nat.ceil (x + 1) ≤ k := by
    rw [Nat.ceil_le]
    constructor <;> intro h <;> linarith
  simp only [Set.mem_ofPred_eq, heq]
  exact tsum_ite_ge_eq_tailMass (summable_incrementMass μ) _

private theorem ceil_add_one_natCast_div_tendsto_one :
    Tendsto (fun x : ℝ => ((Nat.ceil (x + 1) : ℕ) : ℝ) / x) atTop (𝓝 1) := by
  have hshift : Tendsto (fun x : ℝ => x + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_id
  have hc := tendsto_nat_ceil_div_atTop.comp hshift
  have hi : Tendsto (fun x : ℝ => (1 : ℝ) / x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hfactor : Tendsto (fun x : ℝ => (x + 1) / x) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).add hi
    have heq : (fun x : ℝ => 1 + 1 / x) =ᶠ[atTop] (fun x : ℝ => (x + 1) / x) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      field_simp [hx.ne']
    simpa only [add_zero] using h.congr' heq
  have hprod := hc.mul hfactor
  have heq : (fun x : ℝ => (((Nat.ceil (x + 1) : ℕ) : ℝ) / (x + 1)) * ((x + 1) / x)) =ᶠ[atTop]
      (fun x : ℝ => ((Nat.ceil (x + 1) : ℕ) : ℝ) / x) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hx1 : (0 : ℝ) < x + 1 := by linarith
    field_simp [hx.ne', hx1.ne']
  simpa only [Function.comp_def, one_mul] using hprod.congr' heq

/-- `P(X ≥ x) ∼ L(x)/x` along real `x → ∞`. -/
theorem incrementTail_div_tendsto_one
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ < 1)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1)) :
    Tendsto (fun x : ℝ => (incrementTail μ x).toReal / (L x / x)) atTop (𝓝 1) := by
  have hmfin : offspringMean μ ≠ ∞ := ne_top_of_lt (hm.trans ENNReal.one_lt_top)
  have hsref := summable_incrementLocalSq (μ := μ) hmfin hpos hlocal
  have hN : Tendsto (fun x : ℝ => Nat.ceil (x + 1)) atTop atTop :=
    tendsto_nat_ceil_atTop.comp (tendsto_atTop_add_const_right atTop 1 tendsto_id)
  have hmodel := (tailMass_incrementLocalSq_div_tendsto_one μ hmfin hpos hL hsv hlocal).comp hN
  have hcompare := (tailMass_div_tendsto_one hsref (summable_incrementMass μ)
    (incrementLocalSq_nonneg hpos) (fun _ hn => incrementLocalSq_pos hpos hn) hlocal).comp hN
  have hNratio := ceil_add_one_natCast_div_tendsto_one
  have hLratio := slowlyVarying_ratio_of_relative_tendsto_one_filter hpos hL hsv
    (x := fun x : ℝ => x) (y := fun x : ℝ => ((Nat.ceil (x + 1) : ℕ) : ℝ))
    tendsto_id hNratio
  have hNratioInv : Tendsto (fun x : ℝ => x / ((Nat.ceil (x + 1) : ℕ) : ℝ)) atTop (𝓝 1) := by
    have h0 := (tendsto_const_nhds (x := (1 : ℝ))).div hNratio one_ne_zero
    have h : Tendsto (fun x : ℝ => (1 : ℝ) / (((Nat.ceil (x + 1) : ℕ) : ℝ) / x))
        atTop (𝓝 1) := by
      simpa only [Pi.div_def, one_div, inv_div, div_one] using h0
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ), hN.eventually_gt_atTop 0] with x hx hNx
    have hN0 : (0 : ℝ) < ((Nat.ceil (x + 1) : ℕ) : ℝ) := by exact_mod_cast hNx
    field_simp [hx.ne', hN0.ne']
  have hprod := ((hcompare.mul hmodel).mul hLratio).mul hNratioInv
  have heq : (fun x : ℝ =>
      (tailMass (incrementMass μ) (Nat.ceil (x + 1)) /
          tailMass (incrementLocalSq L) (Nat.ceil (x + 1))) *
        (tailMass (incrementLocalSq L) (Nat.ceil (x + 1)) /
          (L (Nat.ceil (x + 1)) / (Nat.ceil (x + 1) : ℝ))) *
        (L (Nat.ceil (x + 1)) / L x) *
        (x / ((Nat.ceil (x + 1) : ℕ) : ℝ))) =ᶠ[atTop]
      (fun x : ℝ => (incrementTail μ x).toReal / (L x / x)) := by
    filter_upwards [hN.eventually_ge_atTop 1, eventually_gt_atTop (0 : ℝ)] with x hNx hx
    have hN0 : (0 : ℝ) < ((Nat.ceil (x + 1) : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < Nat.ceil (x + 1))
    have hLN : 0 < L ((Nat.ceil (x + 1) : ℕ) : ℝ) := hpos _ hN0
    have hLx : 0 < L x := hpos _ hx
    have href : 0 < tailMass (incrementLocalSq L) (Nat.ceil (x + 1)) :=
      tailMass_pos hsref (incrementLocalSq_nonneg hpos)
      (fun _ hn => incrementLocalSq_pos hpos hn) hNx
    rw [incrementTail_toReal_eq_tailMass]
    field_simp [href.ne', hLN.ne', hLx.ne', hN0.ne', hx.ne']
  simpa only [Function.comp_def, one_mul] using hprod.congr' heq

  end

private abbrev integerIncrementTail (μ : Measure ℕ) (j : ℕ) : ℝ :=
  (incrementTail μ (j : ℝ)).toReal

private theorem integerIncrementTail_pos (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsSubcriticalCauchyOffspring μ) (j : ℕ) : 0 < integerIncrementTail μ j :=
  ENNReal.toReal_pos (incrementTail_pos μ hμ j).ne' (measure_ne_top _ _)

private theorem integerIncrementTail_tendsto_zero (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    Tendsto (integerIncrementTail μ) atTop (𝓝 0) := by
  have hN : Tendsto (fun j : ℕ => Nat.ceil ((j : ℝ) + 1)) atTop atTop :=
    tendsto_nat_ceil_atTop.comp
      ((tendsto_atTop_add_const_right atTop 1 tendsto_id).comp
        (tendsto_natCast_atTop_atTop (R := ℝ)))
  have h := (tailMass_tendsto_zero (incrementMass μ)).comp hN
  apply h.congr'
  filter_upwards [] with j
  exact (incrementTail_toReal_eq_tailMass μ (j : ℝ)).symm

private theorem integerIncrementTail_succ_div_tendsto_one
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ < 1)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1)) :
    Tendsto (fun j : ℕ => integerIncrementTail μ (j + 1) / integerIncrementTail μ j)
      atTop (𝓝 1) := by
  have hj : Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hj1 : Tendsto (fun j : ℕ => ((j + 1 : ℕ) : ℝ)) atTop atTop :=
    hj.comp (tendsto_add_atTop_nat 1)
  have hi : Tendsto (fun j : ℕ => (1 : ℝ) / (j : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := (1 : ℝ))).div_atTop hj
  have hidx : Tendsto (fun j : ℕ => ((j + 1 : ℕ) : ℝ) / (j : ℝ)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).add hi
    have heq : (fun j : ℕ => 1 + 1 / (j : ℝ)) =ᶠ[atTop]
        (fun j : ℕ => ((j + 1 : ℕ) : ℝ) / (j : ℝ)) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with j hj'
      have hjR : (0 : ℝ) < (j : ℝ) := Nat.cast_pos.mpr hj'
      push_cast
      field_simp [hjR.ne']
    simpa only [add_zero] using h.congr' heq
  have hidxInv : Tendsto (fun j : ℕ => (j : ℝ) / ((j + 1 : ℕ) : ℝ)) atTop (𝓝 1) := by
    have h0 := (tendsto_const_nhds (x := (1 : ℝ))).div hidx one_ne_zero
    have h : Tendsto (fun j : ℕ => (1 : ℝ) / (((j + 1 : ℕ) : ℝ) / (j : ℝ)))
        atTop (𝓝 1) := by simpa only [Pi.div_def, one_div, inv_div, div_one] using h0
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with j hj'
    have hjR : (0 : ℝ) < (j : ℝ) := Nat.cast_pos.mpr hj'
    push_cast
    field_simp [hjR.ne']
  have hLratio := slowlyVarying_ratio_of_relative_tendsto_one_filter hpos hL hsv
    (x := fun j : ℕ => (j : ℝ)) (y := fun j : ℕ => ((j + 1 : ℕ) : ℝ)) hj hidx
  have hreal := (incrementTail_div_tendsto_one μ hm hpos hL hsv hlocal).comp hj
  have hreal1 := (incrementTail_div_tendsto_one μ hm hpos hL hsv hlocal).comp hj1
  have hrealInv : Tendsto (fun j : ℕ =>
      1 / (integerIncrementTail μ j / (L j / (j : ℝ)))) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Pi.div_def, one_div, div_one] using
      (tendsto_const_nhds (x := (1 : ℝ))).div hreal one_ne_zero
  have hprod := ((hreal1.mul hrealInv).mul hLratio).mul hidxInv
  have heq : (fun j : ℕ =>
      ((integerIncrementTail μ (j + 1) / (L ((j + 1 : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ))) *
        (1 / (integerIncrementTail μ j / (L j / (j : ℝ))))) *
        (L ((j + 1 : ℕ) : ℝ) / L j) * ((j : ℝ) / ((j + 1 : ℕ) : ℝ))) =ᶠ[atTop]
      (fun j : ℕ => integerIncrementTail μ (j + 1) / integerIncrementTail μ j) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with j hj'
    have hjR : (0 : ℝ) < (j : ℝ) := Nat.cast_pos.mpr hj'
    have hlit : IsSubcriticalCauchyOffspring μ := ⟨hm, ⟨L, hpos, hsv, hlocal⟩⟩
    have hT0 := (integerIncrementTail_pos μ hlit j).ne'
    have hT1 := (integerIncrementTail_pos μ hlit (j + 1)).ne'
    have hLj := (hpos _ hjR).ne'
    have hLj1 := (hpos _ (by exact_mod_cast (Nat.succ_pos j) : (0 : ℝ) < ((j + 1 : ℕ) : ℝ))).ne'
    push_cast at hLj1
    field_simp [hT0, hT1, hLj, hLj1, hjR.ne']
  simpa only [Function.comp_def, one_div, one_mul] using hprod.congr' heq

/-- Existence of a scaling sequence. -/
theorem exists_scaling
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) :
    ∃ a : ℕ → ℝ, Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1) := by
  obtain ⟨hm, L, hpos, hsv, hL, hlocal⟩ := hμ
  have hlit : IsSubcriticalCauchyOffspring μ := ⟨hm, ⟨L, hpos, hsv, hlocal⟩⟩
  have hzero := integerIncrementTail_tendsto_zero μ
  have hex : ∀ n : ℕ, ∃ j : ℕ, (n : ℝ) * integerIncrementTail μ j ≤ 1 := by
    intro n
    have hev : ∀ᶠ j : ℕ in atTop, integerIncrementTail μ j < 1 / ((n : ℝ) + 1) :=
      hzero.eventually (gt_mem_nhds (by positivity))
    obtain ⟨j, hj⟩ := hev.exists
    refine ⟨j, ?_⟩
    have hT := (integerIncrementTail_pos μ hlit j).le
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hbound : (n : ℝ) + 1 > 0 := by positivity
    have hlt : ((n : ℝ) + 1) * integerIncrementTail μ j < 1 := by
      simpa only [mul_comm] using (lt_div_iff₀ hbound).mp hj
    nlinarith
  let a : ℕ → ℕ := fun n => Nat.find (hex n)
  have hspec (n : ℕ) : (n : ℝ) * integerIncrementTail μ (a n) ≤ 1 := Nat.find_spec (hex n)
  have ha : Tendsto a atTop atTop := by
    apply tendsto_atTop.2
    intro B
    have hTB : 0 < integerIncrementTail μ B := integerIncrementTail_pos μ hlit B
    have hg : Tendsto (fun n : ℕ => (n : ℝ) * integerIncrementTail μ B) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const hTB
    filter_upwards [hg.eventually_gt_atTop 1] with n hn
    by_contra hnot
    have haB : a n ≤ B := le_of_not_ge hnot
    have hmono : integerIncrementTail μ B ≤ integerIncrementTail μ (a n) := by
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      apply incrementTail_antitone μ
      exact_mod_cast haB
    have hn' := hspec n
    nlinarith [mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hstep := integerIncrementTail_succ_div_tendsto_one μ hm hpos hL hsv hlocal
  have hstepInv : Tendsto (fun j : ℕ => integerIncrementTail μ j / integerIncrementTail μ (j + 1))
      atTop (𝓝 1) := by
    simpa only [Pi.div_def, one_div, inv_div, div_one] using
      (tendsto_const_nhds (x := (1 : ℝ))).div hstep one_ne_zero
  have hasub : Tendsto (fun n => a n - 1) atTop atTop := by
    apply tendsto_atTop.2
    intro B
    filter_upwards [ha.eventually_ge_atTop (B + 1)] with n hn
    omega
  have hprev0 := hstepInv.comp hasub
  have hprev : Tendsto (fun n => integerIncrementTail μ (a n - 1) / integerIncrementTail μ (a n))
      atTop (𝓝 1) := by
    apply hprev0.congr'
    filter_upwards [ha.eventually_ge_atTop 1] with n hn
    simp only [Function.comp_def, Nat.sub_add_cancel hn]
  have hlower : Tendsto (fun n => integerIncrementTail μ (a n) / integerIncrementTail μ (a n - 1))
      atTop (𝓝 1) := by
    simpa only [Pi.div_def, one_div, inv_div, div_one] using
      (tendsto_const_nhds (x := (1 : ℝ))).div hprev one_ne_zero
  refine ⟨fun n => (a n : ℝ), ?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds
  · filter_upwards [ha.eventually_ge_atTop 1] with n hn
    have hprevSpec : 1 < (n : ℝ) * integerIncrementTail μ (a n - 1) := by
      have hlt : a n - 1 < a n := by omega
      exact lt_of_not_ge (Nat.find_min (hex n) hlt)
    have hTprev := integerIncrementTail_pos μ hlit (a n - 1)
    apply (div_le_iff₀ hTprev).mpr
    have hTa := integerIncrementTail_pos μ hlit (a n)
    have hrw : (n : ℝ) * integerIncrementTail μ (a n) * integerIncrementTail μ (a n - 1) =
        integerIncrementTail μ (a n) * ((n : ℝ) * integerIncrementTail μ (a n - 1)) := by ring
    rw [hrw]
    exact (le_mul_iff_one_le_right hTa).mpr hprevSpec.le
  · exact Eventually.of_forall hspec

/-- Every scaling sequence satisfies `a_n ∼ n L(a_n)`, for every witness `L`. -/
theorem scaling_div_mul_tendsto_one
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ < 1)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1))
    {a : ℕ → ℝ}
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => a n / ((n : ℝ) * L (a n))) atTop (𝓝 1) := by
  have hlit : IsSubcriticalCauchyOffspring μ := ⟨hm, ⟨L, hpos, hsv, hlocal⟩⟩
  have hat := scaling_tendsto_atTop μ hlit ha
  have htail := (incrementTail_div_tendsto_one μ hm hpos hL hsv hlocal).comp hat
  have hprod := ha.mul ((tendsto_const_nhds (x := (1 : ℝ))).div htail one_ne_zero)
  have hinv := (tendsto_const_nhds (x := (1 : ℝ))).div hprod (by norm_num)
  have heq : (fun n : ℕ => (1 : ℝ) /
      (((n : ℝ) * (incrementTail μ (a n)).toReal) *
        (1 / ((incrementTail μ (a n)).toReal / (L (a n) / a n))))) =ᶠ[atTop]
      (fun n : ℕ => a n / ((n : ℝ) * L (a n))) := by
    filter_upwards [hat.eventually_gt_atTop 0, eventually_gt_atTop (0 : ℕ)] with n han hn
    have hT := (ENNReal.toReal_pos (incrementTail_pos μ hlit (a n)).ne'
      (measure_ne_top _ _)).ne'
    have hLa := (hpos _ han).ne'
    have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    field_simp [hT, hLa, han.ne', hnR.ne']
  simpa only [Function.comp_def, Pi.div_def, one_div, one_mul, div_one] using hinv.congr' heq

  end SubcriticalCauchy.Bienayme
