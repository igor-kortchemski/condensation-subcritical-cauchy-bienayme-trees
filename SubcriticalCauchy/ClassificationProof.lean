module

public import SubcriticalCauchy.ClassificationDefs
public import SubcriticalCauchy.TiltingFacts

import Mathlib.Analysis.PSeries
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Helpers for `SubcriticalCauchy.Classification` (U2.5)

Owned helper module; must not import `SubcriticalCauchy.Classification`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section

/-- A local mass asymptotic with exponent strictly below one makes the
first-moment series diverge, including the endpoint `α = 0`. -/
theorem not_summable_first_moment_of_tail_lt_one_U25
    (μ : Measure ℕ) [IsProbabilityMeasure μ] {L : ℝ → ℝ} {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ (1 + α)))
      atTop (𝓝 1)) :
    ¬ Summable (fun n : ℕ => (n : ℝ) * (μ {n}).toReal) := by
  let η := (1 - α) / 2
  let p := (1 + α) / 2
  have hη : 0 < η := by dsimp [η]; linarith
  obtain ⟨C, hC, N, hN, hpotter⟩ := potter_bounds hpos hL hsv η hη
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (hlocal.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)))
  obtain ⟨M, hM⟩ := exists_nat_ge N
  let T := max M (max K 1)
  have hTM : M ≤ T := le_max_left _ _
  have hTK : K ≤ T := (le_max_left K 1).trans (le_max_right M _)
  have hT1 : 1 ≤ T := (le_max_right K 1).trans (le_max_right M _)
  have hTN : N ≤ (T : ℝ) := hM.trans (Nat.cast_le.mpr hTM)
  have hT0 : 0 < (T : ℝ) := Nat.cast_pos.mpr (by omega)
  have hLT : 0 < L T := hpos _ hT0
  let d := (1 / 2 : ℝ) * C⁻¹ * L T * (T : ℝ) ^ η
  have hd : 0 < d := by dsimp [d]; positivity
  have hp1 : p < 1 := by dsimp [p]; linarith
  have hcomparison (n : ℕ) :
      d * ((n + T : ℕ) : ℝ) ^ (-p) ≤
        ((n + T : ℕ) : ℝ) * (μ {n + T}).toReal := by
    have hn0 : 0 < ((n + T : ℕ) : ℝ) := by positivity
    have hpot := (hpotter T ((n + T : ℕ) : ℝ) hTN (by exact_mod_cast Nat.le_add_left T n)).1
    have hLn : C⁻¹ * L T * (T : ℝ) ^ η * ((n + T : ℕ) : ℝ) ^ (-η) ≤
        L ((n + T : ℕ) : ℝ) := by
      have hh := (le_div_iff₀ hLT).mp hpot
      rw [Real.div_rpow (Nat.cast_nonneg _) hT0.le] at hh
      calc
        C⁻¹ * L T * (T : ℝ) ^ η * ((n + T : ℕ) : ℝ) ^ (-η) =
            C⁻¹ * (((n + T : ℕ) : ℝ) ^ (-η) / (T : ℝ) ^ (-η)) * L T := by
              rw [Real.rpow_neg (Nat.cast_nonneg T)]
              field_simp
        _ = C⁻¹ * (((n + T : ℕ) : ℝ) / T) ^ (-η) * L T := by
              rw [Real.div_rpow (Nat.cast_nonneg _) hT0.le]
        _ ≤ L ((n + T : ℕ) : ℝ) := by
              exact (le_div_iff₀ hLT).mp hpot |>.trans_eq'
                (by rw [Real.div_rpow (Nat.cast_nonneg _) hT0.le])
    have hratio : (1 / 2 : ℝ) < (μ {n + T}).toReal /
        (L ((n + T : ℕ) : ℝ) / ((n + T : ℕ) : ℝ) ^ (1 + α)) :=
      hK (n + T) (hTK.trans (Nat.le_add_left T n))
    have hden : 0 < L ((n + T : ℕ) : ℝ) / ((n + T : ℕ) : ℝ) ^ (1 + α) :=
      div_pos (hpos _ hn0) (Real.rpow_pos_of_pos hn0 _)
    have hmass : (1 / 2 : ℝ) * (L ((n + T : ℕ) : ℝ) / ((n + T : ℕ) : ℝ) ^ (1 + α)) ≤
        (μ {n + T}).toReal := (lt_div_iff₀ hden).mp hratio |>.le
    have hexp : -p = -η + (1 - (1 + α)) := by dsimp [p, η]; ring
    calc
      d * ((n + T : ℕ) : ℝ) ^ (-p) =
          (((n + T : ℕ) : ℝ) * ((1 / 2 : ℝ) * C⁻¹ * L T * (T : ℝ) ^ η *
            ((n + T : ℕ) : ℝ) ^ (-η))) / ((n + T : ℕ) : ℝ) ^ (1 + α) := by
        rw [eq_div_iff (Real.rpow_pos_of_pos hn0 _).ne']
        have hpow : ((n + T : ℕ) : ℝ) ^ (-p) = ((n + T : ℕ) : ℝ) *
            ((n + T : ℕ) : ℝ) ^ (-η - (1 + α)) := by
          rw [hexp, show -η + (1 - (1 + α)) = 1 + (-η - (1 + α)) by ring,
            Real.rpow_one_add' hn0.le (by dsimp [η]; linarith)]
        rw [hpow]
        calc
          d * (((n + T : ℕ) : ℝ) * ((n + T : ℕ) : ℝ) ^ (-η - (1 + α))) *
              ((n + T : ℕ) : ℝ) ^ (1 + α) =
              d * ((n + T : ℕ) : ℝ) * (((n + T : ℕ) : ℝ) ^ (-η - (1 + α)) *
                ((n + T : ℕ) : ℝ) ^ (1 + α)) := by ring
          _ = d * ((n + T : ℕ) : ℝ) *
              ((n + T : ℕ) : ℝ) ^ ((-η - (1 + α)) + (1 + α)) :=
                congrArg (fun z : ℝ => d * ((n + T : ℕ) : ℝ) * z)
                  (Real.rpow_add hn0 (-η - (1 + α)) (1 + α)).symm
          _ = ((n + T : ℕ) : ℝ) * ((1 / 2 : ℝ) * C⁻¹ * L T * (T : ℝ) ^ η *
              ((n + T : ℕ) : ℝ) ^ (-η)) := by
                rw [show (-η - (1 + α)) + (1 + α) = -η by ring]
                dsimp [d]
                ring
      _ ≤ ((n + T : ℕ) : ℝ) * ((1 / 2 : ℝ) * L ((n + T : ℕ) : ℝ)) /
          ((n + T : ℕ) : ℝ) ^ (1 + α) := by
        apply div_le_div_of_nonneg_right _ (Real.rpow_pos_of_pos hn0 _).le
        apply mul_le_mul_of_nonneg_left _ hn0.le
        simpa only [mul_assoc] using
          (mul_le_mul_of_nonneg_left hLn (by norm_num : (0 : ℝ) ≤ 1 / 2))
      _ = ((n + T : ℕ) : ℝ) * ((1 / 2 : ℝ) *
          (L ((n + T : ℕ) : ℝ) / ((n + T : ℕ) : ℝ) ^ (1 + α))) := by ring
      _ ≤ ((n + T : ℕ) : ℝ) * (μ {n + T}).toReal :=
        mul_le_mul_of_nonneg_left hmass hn0.le
  intro hsum
  have htail : (Summable (fun n : ℕ => 1 / (n : ℝ) ^ p)) ↔
      Summable (fun n => 1 / ((n + T : ℕ) : ℝ) ^ p) :=
    (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ p) T).symm
  have hnot : ¬ Summable (fun n : ℕ => 1 / ((n + T : ℕ) : ℝ) ^ p) := by
    rw [← htail, Real.summable_one_div_nat_rpow]
    exact not_lt_of_ge hp1.le
  apply hnot
  apply Summable.of_nonneg_of_le (f := fun n : ℕ =>
    d⁻¹ * (((n + T : ℕ) : ℝ) * (μ {n + T}).toReal)) (fun n => by positivity)
  · intro n
    rw [le_inv_mul_iff₀ hd]
    simpa only [one_div, ← Real.rpow_neg (x := ((n + T : ℕ) : ℝ)) (Nat.cast_nonneg _)] using hcomparison n
  · exact ((summable_nat_add_iff T).2 hsum).mul_left d⁻¹

/-- Infinite extended-nonnegative first moment for every tail exponent below one. -/
theorem infinite_first_moment_tsum_of_tail_lt_one_U25
    (μ : Measure ℕ) [IsProbabilityMeasure μ] {L : ℝ → ℝ} {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ (1 + α)))
      atTop (𝓝 1)) :
    ∑' n : ℕ, (n : ℝ≥0∞) * μ {n} = ∞ :=
  TiltingFacts.tsum_first_moment_eq_top_iff_not_summable μ |>.mpr
    (not_summable_first_moment_of_tail_lt_one_U25 μ hα0 hα1 hpos hL hsv hlocal)

/-- A heavy tail with `α > 2` has a summable real second-moment series. -/
theorem summable_second_moment_of_two_lt_alpha_U25
    (μ : Measure ℕ) [IsProbabilityMeasure μ] {α : ℝ} (hα : 2 < α) {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal /
      (L n / (n : ℝ) ^ (1 + α))) atTop (𝓝 1)) :
    Summable (fun n : ℕ => (n : ℝ) ^ 2 * (μ {n}).toReal) := by
  let η : ℝ := (α - 2) / 2
  have hη : 0 < η := by dsimp [η]; linarith
  obtain ⟨C, hC, N, hN, hpotter⟩ := potter_bounds hpos hL hsv η hη
  let K : ℝ := C * L N / N ^ η
  have hLN : 0 < L N := hpos N hN
  have hK : 0 < K := div_pos (mul_pos hC hLN) (Real.rpow_pos_of_pos hN _)
  have hLbound : ∀ᶠ n : ℕ in atTop, L n ≤ K * (n : ℝ) ^ η := by
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop N] with n hn
    have hn0 : 0 < (n : ℝ) := hN.trans_le hn
    have hup := (hpotter N n le_rfl hn).2
    have hmul := (div_le_iff₀ hLN).mp hup
    calc
      L n ≤ C * ((n : ℝ) / N) ^ η * L N := hmul
      _ = K * (n : ℝ) ^ η := by
        rw [Real.div_rpow hn0.le hN.le]
        dsimp [K]
        field_simp [(Real.rpow_pos_of_pos hN η).ne']
  have hdominant : Summable (fun n : ℕ => 2 * K * (n : ℝ) ^ (1 - α + η)) := by
    apply Summable.mul_left
    apply Real.summable_nat_rpow.mpr
    dsimp [η]
    linarith
  apply hdominant.of_norm_bounded_eventually_nat
  filter_upwards [hLbound, eventually_ge_atTop (1 : ℕ),
    hlocal.eventually (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))] with n hLn hn hratio
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < L n / (n : ℝ) ^ (1 + α) :=
    div_pos (hpos _ hn0) (Real.rpow_pos_of_pos hn0 _)
  have hmass : (μ {n}).toReal < 2 * (L n / (n : ℝ) ^ (1 + α)) :=
    (div_lt_iff₀ hden).mp hratio
  have hnonneg : 0 ≤ (n : ℝ) ^ 2 * (μ {n}).toReal := by positivity
  rw [Real.norm_of_nonneg hnonneg]
  calc
    (n : ℝ) ^ 2 * (μ {n}).toReal ≤
        (n : ℝ) ^ 2 * (2 * (K * (n : ℝ) ^ η / (n : ℝ) ^ (1 + α))) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      calc
        (μ {n}).toReal ≤ 2 * (L n / (n : ℝ) ^ (1 + α)) := hmass.le
        _ ≤ 2 * (K * (n : ℝ) ^ η / (n : ℝ) ^ (1 + α)) := by gcongr
    _ = 2 * K * (n : ℝ) ^ (1 - α + η) := by
      have hquot : (n : ℝ) ^ (2 + η) / (n : ℝ) ^ (1 + α) =
          (n : ℝ) ^ (1 - α + η) := by
        rw [← Real.rpow_sub hn0]
        congr 1
        ring
      have hsq : (n : ℝ) ^ 2 = (n : ℝ) ^ (2 : ℝ) := by
        rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast]
      rw [hsq]
      calc
        (n : ℝ) ^ (2 : ℝ) * (2 * (K * (n : ℝ) ^ η / (n : ℝ) ^ (1 + α))) =
            2 * K * (((n : ℝ) ^ (2 : ℝ) * (n : ℝ) ^ η) / (n : ℝ) ^ (1 + α)) := by ring
        _ = 2 * K * ((n : ℝ) ^ (2 + η) / (n : ℝ) ^ (1 + α)) := by
          rw [Real.rpow_add hn0 2 η]
        _ = 2 * K * (n : ℝ) ^ (1 - α + η) := by rw [hquot]

/-- Real summability gives a finite extended-nonnegative second moment. -/
theorem second_moment_lt_top_of_summable_U25 (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hs : Summable (fun k : ℕ => (k : ℝ) ^ 2 * (μ {k}).toReal)) :
    ∑' k : ℕ, (k : ℝ≥0∞) ^ 2 * μ {k} < ∞ := by
  have heq : ∑' k : ℕ, (k : ℝ≥0∞) ^ 2 * μ {k} =
      ENNReal.ofReal (∑' k : ℕ, (k : ℝ) ^ 2 * (μ {k}).toReal) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (sq_nonneg _) ENNReal.toReal_nonneg) hs]
    apply tsum_congr
    intro k
    rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_toReal (measure_ne_top _ _),
      ENNReal.ofReal_pow (Nat.cast_nonneg k)]
    simp
  rw [heq]
  exact ENNReal.ofReal_lt_top

/-- A supercritical law with positive mass at zero has an equivalent critical
law with finite second moment. -/
theorem exists_critical_finite_second_tilt_of_supercritical_U25
    (ν : Measure ℕ) [IsProbabilityMeasure ν]
    (hν0 : 0 < (ν {0}).toReal) (hmean : 1 < offspringMean ν) :
    ∃ μ : Measure ℕ, IsProbabilityMeasure μ ∧ IsTiltEquivalent μ ν ∧
      offspringMean μ = 1 ∧ ∑' k : ℕ, (k : ℝ≥0∞) ^ 2 * μ {k} < ∞ := by
  have hradius : 1 ≤ TiltingFacts.offspringRadius ν := by
    apply FormalMultilinearSeries.le_radius_of_summable (r := 1)
    have hs := summable_pgfReal ν 1 zero_le_one le_rfl
    simpa only [TiltingFacts.offspringPowerSeries, FormalMultilinearSeries.ofScalars_norm,
      NNReal.coe_one, one_pow, mul_one, Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg] using hs
  obtain ⟨b, hb0, hb1, hbmean, r, hr0, hr1, hmeanSum, hmoments, p, hp, hmeanp, _⟩ :=
    TiltingFacts.supercritical_equivalent_critical_U24 ν hν0 hmean
  let tiltedProbability : IsProbabilityMeasure p.toMeasure :=
    PMF.toMeasure.isProbabilityMeasure p
  have hrR : ‖r‖ₑ < TiltingFacts.offspringRadius ν := by
    apply lt_of_lt_of_le _ hradius
    rw [Real.enorm_eq_ofReal hr0.le, ← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr hr1
  have hF : 0 < TiltingFacts.offspringPGF ν r :=
    TiltingFacts.offspringPGF_pos ν hr0 hrR
  refine ⟨p.toMeasure, tiltedProbability, ?_, hmeanp, ?_⟩
  · refine ⟨(TiltingFacts.offspringPGF ν r)⁻¹, r, inv_pos.mpr hF, hr0, ?_⟩
    intro k
    rw [hp k]
    simp only [TiltingFacts.tiltedMass, div_eq_mul_inv]
    ring
  · apply @second_moment_lt_top_of_summable_U25 p.toMeasure tiltedProbability
    apply (hmoments 2).congr
    intro k
    rw [hp k]

/-- Helper theorem filling the frozen five-case classification target. -/
theorem paper_heavyTail_classification_proof (ν : Measure ℕ) [IsProbabilityMeasure ν]
    (hν0 : 0 < ν {0}) (α : ℝ) (hα : 0 ≤ α) {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : HasHeavyTail ν α L) :
    ∃ μ : Measure ℕ, IsProbabilityMeasure μ ∧ IsTiltEquivalent μ ν ∧
      ((offspringMean μ = 1 ∧ ∑' k : ℕ, (k : ℝ≥0∞) ^ 2 * μ {k} < ∞) ∨
        (offspringMean μ = 1 ∧ ∑' k : ℕ, (k : ℝ≥0∞) ^ 2 * μ {k} = ∞ ∧ 1 < α ∧ α ≤ 2 ∧
          HasHeavyTail μ α L) ∨
        (offspringMean μ = 1 ∧ α = 1 ∧ HasHeavyTail μ α L) ∨
        (offspringMean μ < 1 ∧ 1 < α ∧ HasHeavyTail μ α L) ∨
        (offspringMean μ < 1 ∧ α = 1 ∧ HasHeavyTail μ α L)) := by
  have hmean_series : offspringMean ν = ∑' k : ℕ, (k : ℝ≥0∞) * ν {k} := by
    rw [offspringMean, lintegral_countable']
  have hα_of_mean_le (hm : offspringMean ν ≤ 1) : 1 ≤ α := by
    by_contra h
    have hαlt : α < 1 := lt_of_not_ge h
    have htop : offspringMean ν = ∞ := by
      rw [hmean_series]
      exact infinite_first_moment_tsum_of_tail_lt_one_U25 ν hα hαlt hpos hL hsv hlocal
    have hle : (∞ : ℝ≥0∞) ≤ 1 := htop ▸ hm
    exact (not_le_of_gt ENNReal.one_lt_top) hle
  have hself : IsTiltEquivalent ν ν := by
    refine ⟨1, 1, one_pos, one_pos, ?_⟩
    intro k
    simp
  rcases lt_trichotomy (offspringMean ν) 1 with hsub | hcrit | hsuper
  · have hαge : 1 ≤ α := hα_of_mean_le hsub.le
    refine ⟨ν, inferInstance, hself, ?_⟩
    by_cases hαeq : α = 1
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hsub, hαeq, hlocal⟩)))
    · have hαgt : 1 < α := lt_of_le_of_ne hαge (Ne.symm hαeq)
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hsub, hαgt, hlocal⟩)))
  · have hαge : 1 ≤ α := hα_of_mean_le hcrit.le
    refine ⟨ν, inferInstance, hself, ?_⟩
    by_cases hαeq : α = 1
    · exact Or.inr (Or.inr (Or.inl ⟨hcrit, hαeq, hlocal⟩))
    · have hαgt : 1 < α := lt_of_le_of_ne hαge (Ne.symm hαeq)
      by_cases hsecond : ∑' k : ℕ, (k : ℝ≥0∞) ^ 2 * ν {k} < ∞
      · exact Or.inl ⟨hcrit, hsecond⟩
      · have htop : ∑' k : ℕ, (k : ℝ≥0∞) ^ 2 * ν {k} = ∞ :=
          top_unique (le_of_not_gt hsecond)
        have hαle : α ≤ 2 := by
          by_contra h
          have hαgt2 : 2 < α := lt_of_not_ge h
          have hs := summable_second_moment_of_two_lt_alpha_U25 ν hαgt2 hpos hL hsv hlocal
          exact hsecond (second_moment_lt_top_of_summable_U25 ν hs)
        exact Or.inr (Or.inl ⟨hcrit, htop, hαgt, hαle, hlocal⟩)
  · have hν0real : 0 < (ν {0}).toReal :=
      ENNReal.toReal_pos hν0.ne' (measure_ne_top _ _)
    obtain ⟨μ, hμ, htilt, hmean, hsecond⟩ :=
      exists_critical_finite_second_tilt_of_supercritical_U25 ν hν0real hsuper
    exact ⟨μ, hμ, htilt, Or.inl ⟨hmean, hsecond⟩⟩

end
end SubcriticalCauchy.Bienayme
