module

public import SubcriticalCauchy.AbelianCutoffSqueeze
public import SubcriticalCauchy.CorrectionCutoffs
public import SubcriticalCauchy.SlowTailPartialSums
public import SubcriticalCauchy.SlowVariationRounding
public import SubcriticalCauchy.TailPrefixMoments

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Asymptotics of the actual survival correction

The finite-kernel cutoff estimates compare the correction with the actual
first-moment tail. A uniform partial-sum bound controls the truncated second
moment. Fixed-scale rounding limits then give the integrated-tail asymptotic,
slow variation at zero, and Lemma 4.4(i).
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

private theorem firstMomentTail_index_div_ellStarReal_tendsto_one
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ ≠ ∞)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1)) {M : ℝ → ℕ} {c : ℝ} (hc : 0 < c)
    (hM : Tendsto M atTop atTop)
    (hMN : Tendsto (fun t : ℝ => (M t : ℝ) / (Nat.floor t : ℝ)) atTop (𝓝 c)) :
    Tendsto (fun t : ℝ => firstMomentTail μ (M t) / ellStarReal L t)
      atTop (𝓝 1) := by
  have hfloor : Tendsto (fun t : ℝ => Nat.floor t) atTop atTop :=
    tendsto_nat_floor_atTop
  have hfirst := firstMomentTail_ratio_of_index_ratio μ hm hpos hL hsv hlocal hc
    hfloor hM hMN
  have htail := (firstMomentTail_div_ellStar_tendsto_one μ hm hpos hlocal).comp hfloor
  have hprod := hfirst.mul htail
  have heq : (fun t : ℝ =>
      (firstMomentTail μ (M t) / firstMomentTail μ ⌊t⌋₊) *
        (firstMomentTail μ ⌊t⌋₊ / ellStar L ⌊t⌋₊)) =ᶠ[atTop]
      (fun t : ℝ => firstMomentTail μ (M t) / ellStarReal L t) := by
    filter_upwards [] with t
    have hA : firstMomentTail μ (Nat.floor t) ≠ 0 :=
      (firstMomentTail_pos_of_local μ hm hpos hlocal _).ne'
    dsimp only [ellStarReal]
    field_simp [hA]
  simpa only [Function.comp_def, one_mul] using hprod.congr' heq

private theorem firstMomentTail_floor_div_ellStarReal_tendsto_one
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ ≠ ∞)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1)) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => firstMomentTail μ ⌊c * t⌋₊ / ellStarReal L t)
      atTop (𝓝 1) := by
  apply firstMomentTail_index_div_ellStarReal_tendsto_one μ hm hpos hL hsv hlocal hc
  · exact tendsto_nat_floor_atTop.comp (tendsto_id.const_mul_atTop hc)
  · have h := (tendsto_nat_floor_mul_div_atTop hc.le).div tendsto_nat_floor_div_atTop
      (show (1 : ℝ) ≠ 0 from one_ne_zero)
    have heq : (fun t : ℝ => ((⌊c * t⌋₊ : ℝ) / t) / ((⌊t⌋₊ : ℝ) / t)) =ᶠ[atTop]
        (fun t : ℝ => (⌊c * t⌋₊ : ℝ) / (⌊t⌋₊ : ℝ)) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ),
        (tendsto_nat_floor_atTop (α := ℝ)).eventually_gt_atTop 0] with t ht hnt
      have hn0 : (⌊t⌋₊ : ℝ) ≠ 0 := (Nat.cast_pos.mpr hnt).ne'
      field_simp [ht.ne', hn0]
    simpa only [div_one] using h.congr' heq

private theorem firstMomentTail_ceil_div_ellStarReal_tendsto_one
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ ≠ ∞)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1)) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => firstMomentTail μ ⌈c * t⌉₊ / ellStarReal L t)
      atTop (𝓝 1) := by
  apply firstMomentTail_index_div_ellStarReal_tendsto_one μ hm hpos hL hsv hlocal hc
  · exact tendsto_nat_ceil_atTop.comp (tendsto_id.const_mul_atTop hc)
  · have h := (tendsto_nat_ceil_mul_div_atTop hc.le).div tendsto_nat_floor_div_atTop
      (show (1 : ℝ) ≠ 0 from one_ne_zero)
    have heq : (fun t : ℝ => ((⌈c * t⌉₊ : ℝ) / t) / ((⌊t⌋₊ : ℝ) / t)) =ᶠ[atTop]
        (fun t : ℝ => (⌈c * t⌉₊ : ℝ) / (⌊t⌋₊ : ℝ)) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ),
        (tendsto_nat_floor_atTop (α := ℝ)).eventually_gt_atTop 0] with t ht hnt
      have hn0 : (⌊t⌋₊ : ℝ) ≠ 0 := (Nat.cast_pos.mpr hnt).ne'
      field_simp [ht.ne', hn0]
    simpa only [div_one] using h.congr' heq

/-- The reciprocal-parameter version of the survival-correction asymptotic. -/
theorem survivalCorrection_div_ellStarReal_atTop
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ < 1)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1)) :
    Tendsto (fun t : ℝ => survivalCorrection μ t⁻¹ / ellStarReal L t)
      atTop (𝓝 1) := by
  have hfin : offspringMean μ ≠ ∞ := ne_top_of_lt (hm.trans ENNReal.one_lt_top)
  have hsum := summable_localModel_over_nat μ hfin hpos hlocal
  obtain ⟨C, hC, hCsum⟩ := slowTail_partial_sum_bound
    (firstMomentTail_nonneg μ)
    (fun n _ => firstMomentTail_pos_of_local μ hfin hpos hlocal n)
    (firstMomentTail_antitone μ hfin)
    (fun c hc => firstMomentTail_floor_mul_div_tendsto_one μ hfin hpos hL hsv hlocal hc)
  apply abelian_cutoff_ratio_tendsto_one hC
    (Filter.Eventually.of_forall (fun t => ellStarReal_pos hpos hsum t))
  · exact fun c hc =>
      firstMomentTail_floor_div_ellStarReal_tendsto_one μ hfin hpos hL hsv hlocal hc
  · exact fun c hc =>
      firstMomentTail_ceil_div_ellStarReal_tendsto_one μ hfin hpos hL hsv hlocal hc
  · intro c hc
    filter_upwards [eventually_ge_atTop (1 : ℝ),
      (tendsto_nat_floor_atTop.comp (tendsto_id.const_mul_atTop hc)).eventually_ge_atTop 1]
      with t ht hN
    have ht0 : 0 < t := zero_lt_one.trans_le ht
    let N := ⌊c * t⌋₊
    have hN1 : 1 ≤ N := hN
    have hq1 : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht
    have hweighted :
        (∑ k ∈ Finset.range N, (k : ℝ) * ((μ {k}).toReal * (k : ℝ))) ≤
          ∑ j ∈ Finset.Icc 1 N, firstMomentTail μ j := by
      have hw := weighted_prefix_le_sum_tailMass (summable_offspringMean μ hfin)
        (fun k => mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg k)) N
      calc
        _ ≤ ∑ j ∈ Finset.range N, firstMomentTail μ (j + 1) := by
          simpa only [firstMomentTail] using hw
        _ = _ := by
          rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
          simp only [Nat.add_sub_cancel, Nat.add_comm]
    have hprefix :
        (∑ k ∈ Finset.range N, (k : ℝ) * ((μ {k}).toReal * (k : ℝ))) ≤
          C * (N : ℝ) * firstMomentTail μ N := hweighted.trans (hCsum N hN1)
    have hqN : t⁻¹ * (N : ℝ) ≤ c := by
      rw [inv_mul_eq_div, div_le_iff₀ ht0]
      exact Nat.floor_le (mul_nonneg hc.le ht0.le)
    have hterm : t⁻¹ * (C * (N : ℝ) * firstMomentTail μ N) ≤
        C * c * firstMomentTail μ N := by
      calc
        _ = (t⁻¹ * (N : ℝ)) * (C * firstMomentTail μ N) := by ring
        _ ≤ c * (C * firstMomentTail μ N) :=
          mul_le_mul_of_nonneg_right hqN
            (mul_nonneg hC.le (firstMomentTail_nonneg μ N))
        _ = _ := by ring
    calc
      survivalCorrection μ t⁻¹ ≤ firstMomentTail μ N +
          t⁻¹ * ∑ k ∈ Finset.range N, (k : ℝ) * ((μ {k}).toReal * (k : ℝ)) :=
        survivalCorrection_upper_cutoff μ hfin (inv_nonneg.mpr ht0.le) hq1 N
      _ ≤ firstMomentTail μ N + t⁻¹ * (C * (N : ℝ) * firstMomentTail μ N) :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hprefix (inv_nonneg.mpr ht0.le))
      _ ≤ firstMomentTail μ N + C * c * firstMomentTail μ N := add_le_add (le_refl _) hterm
      _ = (1 + C * c) * firstMomentTail μ N := by ring
  · intro M hM
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := zero_lt_one.trans_le ht
    apply survivalCorrection_lower_cutoff μ hfin (inv_pos.mpr ht0)
      (inv_le_one_of_one_le₀ ht) hM
    simpa only [div_eq_mul_inv, inv_inv] using (Nat.le_ceil (M * t))

theorem survivalCorrection_div_ellStarReal_tendsto_one
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ < 1)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1)) :
    Tendsto (fun x : ℝ => survivalCorrection μ x / ellStarReal L x⁻¹)
      (𝓝[>] 0) (𝓝 1) := by
  apply tendsto_nhdsGT_zero_of_comp_inv_tendsto_atTop
  simpa only [inv_inv] using
    survivalCorrection_div_ellStarReal_atTop μ hm hpos hL hsv hlocal

theorem survivalCorrection_slowlyVarying_atZero
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℝ) (ha : 0 < a) :
    Tendsto (fun x : ℝ => survivalCorrection μ (a * x) / survivalCorrection μ x)
      (𝓝[>] 0) (𝓝 1) := by
  obtain ⟨hm, L, hpos, hsv, hL, hlocal⟩ := hμ
  have hsum := summable_localModel_over_nat μ
    (ne_top_of_lt (hm.trans ENNReal.one_lt_top)) hpos hlocal
  have htop := survivalCorrection_div_ellStarReal_atTop μ hm hpos hL hsv hlocal
  have hslow := ellStarReal_slowlyVarying hpos hL hsv hsum
  have hscaled := htop.comp (tendsto_id.const_mul_atTop (inv_pos.mpr ha))
  have hinv : Tendsto (fun t : ℝ => ellStarReal L t / survivalCorrection μ t⁻¹)
      atTop (𝓝 1) := by
    simpa only [Pi.inv_apply, inv_div, inv_one] using htop.inv₀ one_ne_zero
  have hprod := (hscaled.mul (hslow a⁻¹ (inv_pos.mpr ha))).mul hinv
  apply tendsto_nhdsGT_zero_of_comp_inv_tendsto_atTop
  have heq : (fun t : ℝ =>
      (survivalCorrection μ (a⁻¹ * t)⁻¹ / ellStarReal L (a⁻¹ * t)) *
        (ellStarReal L (a⁻¹ * t) / ellStarReal L t) *
        (ellStarReal L t / survivalCorrection μ t⁻¹)) =ᶠ[atTop]
      (fun t : ℝ => survivalCorrection μ (a * t⁻¹) / survivalCorrection μ t⁻¹) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := zero_lt_one.trans_le ht
    have hcorr : survivalCorrection μ t⁻¹ ≠ 0 := by
      apply ne_of_gt
      exact (paper_survivalCorrection μ ⟨hm, L, hpos, hsv, hlocal⟩).1 t⁻¹
        (inv_pos.mpr ht0) (inv_le_one_of_one_le₀ ht) |>.1
    have hB : ellStarReal L t ≠ 0 := (ellStarReal_pos hpos hsum t).ne'
    have hBa : ellStarReal L (a⁻¹ * t) ≠ 0 := (ellStarReal_pos hpos hsum (a⁻¹ * t)).ne'
    have hBa_div : ellStarReal L (t / a) ≠ 0 :=
      (ellStarReal_pos hpos hsum (t / a)).ne'
    field_simp [hcorr, hB, hBa, hBa_div, ha.ne', ht0.ne']
  simpa only [Function.comp_def, id_eq, one_mul] using hprod.congr' heq

/-- Lemma 4.4(i). -/
theorem paper_survival_correction_lemma
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) :
    ∃ ℓ : ℝ → ℝ, (∀ x : ℝ, 0 < x → x ≤ 1 → 0 < ℓ x) ∧
      (∀ a : ℝ, 0 < a → Tendsto (fun x : ℝ => ℓ (a * x) / ℓ x) (𝓝[>] 0) (𝓝 1)) ∧
      Tendsto ℓ (𝓝[>] 0) (𝓝 0) ∧
      ∀ n : ℕ, (survival μ (n + 1)).toReal =
        (survival μ n).toReal * ((offspringMean μ).toReal - ℓ (survival μ n).toReal) := by
  obtain ⟨hm, L, hpos, hsv, hL, hlocal⟩ := hμ
  have hmfin : offspringMean μ ≠ ∞ := ne_top_of_lt (hm.trans ENNReal.one_lt_top)
  refine ⟨survivalCorrection μ, ?_, survivalCorrection_slowlyVarying_atZero μ
    ⟨hm, L, hpos, hsv, hL, hlocal⟩, survivalCorrection_tendsto_zero μ hmfin, ?_⟩
  · intro x hx0 hx1
    exact (paper_survivalCorrection μ ⟨hm, L, hpos, hsv, hlocal⟩).1 x hx0 hx1 |>.1
  · exact (paper_survivalCorrection μ ⟨hm, L, hpos, hsv, hlocal⟩).2

end SubcriticalCauchy.Bienayme
