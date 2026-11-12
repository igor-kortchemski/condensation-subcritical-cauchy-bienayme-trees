module

public import SubcriticalCauchy.TiltingFactsAux
public import SubcriticalCauchy.PotterBounds
public import SubcriticalCauchy.BienaymeTilting
public import SubcriticalCauchy.BienaymeSurvivalRatio
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Unnumbered exponential-tilting facts (U2.2 and the corrected U2.4)
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace SubcriticalCauchy.TiltingFacts

noncomputable section

/-- U2.4, remaining component: a local mass asymptotic
`μₙ ~ L(n) / n^(1+α)` with `0 < α < 1` makes the first-moment series diverge. -/
theorem not_summable_first_moment_of_tail_alpha_lt_one
    (μ : Measure ℕ) [IsProbabilityMeasure μ] {L : ℝ → ℝ} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : Bienayme.IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ (1 + α)))
      atTop (𝓝 1)) :
    ¬ Summable (fun n : ℕ => (n : ℝ) * (μ {n}).toReal) := by
  let η := (1 - α) / 2
  let p := (1 + α) / 2
  have hη : 0 < η := by dsimp [η]; linarith
  obtain ⟨C, hC, N, hN, hpotter⟩ := Bienayme.potter_bounds hpos hL hsv η hη
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
    have hTn : (T : ℝ) ≤ ((n + T : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_left T n
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


/-- Positive tilted masses, with the normalization written as in the source. -/
def tiltedMass (μ : Measure ℕ) (r : ℝ) (k : ℕ) : ℝ :=
  r ^ k * (μ {k}).toReal / offspringPGF μ r

/-- The logarithmic-derivative expression for the tilted mean. -/
def tiltedMean (μ : Measure ℕ) (r : ℝ) : ℝ :=
  r * deriv (offspringPGF μ) r / offspringPGF μ r

theorem hasSum_raw_tiltedMass (μ : Measure ℕ) {r : ℝ}
    (hr : ‖r‖ₑ < offspringRadius μ) :
    HasSum (fun k : ℕ => r ^ k * (μ {k}).toReal) (offspringPGF μ r) := by
  convert hasSum_offspringPGF μ hr using 1
  ext k
  ring

theorem offspringPGF_pos (μ : Measure ℕ) [IsProbabilityMeasure μ] {r : ℝ}
    (hr0 : 0 < r) (hr : ‖r‖ₑ < offspringRadius μ) : 0 < offspringPGF μ r := by
  have hsummable : Summable (fun k : ℕ => (μ {k}).toReal) := by
    simpa using Bienayme.summable_pgfReal μ 1 zero_le_one le_rfl
  have hsum_one : HasSum (fun k : ℕ => (μ {k}).toReal) 1 := by
    rw [show (1 : ℝ) = ∑' k : ℕ, (μ {k}).toReal by
      have h := congrArg ENNReal.toReal
        (μ.tsum_indicator_apply_singleton Set.univ MeasurableSet.univ)
      simpa only [Set.indicator_univ, ENNReal.tsum_toReal_eq (fun k => measure_ne_top μ {k}),
        ENNReal.toReal_one, IsProbabilityMeasure.measure_univ] using h.symm]
    exact hsummable.hasSum
  have hraw := hasSum_raw_tiltedMass μ hr
  have hne : offspringPGF μ r ≠ 0 := by
    intro hzero
    have hnil : (fun k : ℕ => r ^ k * (μ {k}).toReal) = 0 :=
      (hasSum_zero_iff_of_nonneg (fun k => show 0 ≤ r ^ k * (μ {k}).toReal from
        mul_nonneg (pow_nonneg hr0.le k) ENNReal.toReal_nonneg)).mp (hzero ▸ hraw)
    have hz (k : ℕ) : (μ {k}).toReal = 0 := by
      have hk := congrFun hnil k
      simp only [Pi.zero_apply, mul_eq_zero] at hk
      rcases hk with hk | hk
      · exact (pow_ne_zero k hr0.ne' hk).elim
      · simpa using hk
    have hzero : HasSum (fun k : ℕ => (μ {k}).toReal) 0 := by
      simpa only [hz] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
    exact zero_ne_one (hzero.unique hsum_one)
  exact lt_of_le_of_ne (by
    rw [← hraw.tsum_eq]
    exact tsum_nonneg (fun k => mul_nonneg (pow_nonneg hr0.le k) ENNReal.toReal_nonneg))
    (Ne.symm hne)

/-- The normalized positive tilt really is a probability mass function. -/
def tiltedPMF (μ : Measure ℕ) [IsProbabilityMeasure μ] {r : ℝ}
    (hr0 : 0 < r) (hr : ‖r‖ₑ < offspringRadius μ) : PMF ℕ := by
  have hF := offspringPGF_pos μ hr0 hr
  have hnorm : HasSum (tiltedMass μ r) 1 := by
    have hh := (hasSum_raw_tiltedMass μ hr).div_const (offspringPGF μ r)
    rw [div_self hF.ne'] at hh
    convert hh using 1
    ext k
    simp only [tiltedMass]
  refine ⟨fun k => ENNReal.ofReal (tiltedMass μ r k), ?_⟩
  have heq : ∑' k : ℕ, ENNReal.ofReal (tiltedMass μ r k) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (f := tiltedMass μ r)
      (fun k => div_nonneg (mul_nonneg (pow_nonneg hr0.le k) ENNReal.toReal_nonneg) hF.le)
      hnorm.summable, hnorm.tsum_eq, ENNReal.ofReal_one]
  rw [← heq]
  exact ENNReal.summable.hasSum

/-- Point masses of the constructed tilted law are the real formulas above. -/
theorem tiltedPMF_apply_toReal (μ : Measure ℕ) [IsProbabilityMeasure μ] {r : ℝ}
    (hr0 : 0 < r) (hr : ‖r‖ₑ < offspringRadius μ) (k : ℕ) :
    ((tiltedPMF μ hr0 hr).toMeasure {k}).toReal = tiltedMass μ r k := by
  rw [(tiltedPMF μ hr0 hr).toMeasure_apply_singleton k (MeasurableSet.singleton k)]
  change (ENNReal.ofReal (tiltedMass μ r k)).toReal = _
  rw [ENNReal.toReal_ofReal]
  exact div_nonneg (mul_nonneg (pow_nonneg hr0.le k) ENNReal.toReal_nonneg)
    (offspringPGF_pos μ hr0 hr).le

/-- U2.2: normalized tilted law, PGF on the exact interior convergence domain,
mean, support equivalence, and invariance of every admissible conditioned tree law. -/
theorem exponential_tilt_U22 (μ : Measure ℕ) [IsProbabilityMeasure μ] {r : ℝ}
    (hr0 : 0 < r) (hr : ‖r‖ₑ < offspringRadius μ) :
    HasSum (fun k : ℕ => r ^ k * (μ {k}).toReal) (offspringPGF μ r) ∧
    HasSum (tiltedMass μ r) 1 ∧
    (∀ x : ℝ, ‖r * x‖ₑ < offspringRadius μ →
      HasSum (fun k => tiltedMass μ r k * x ^ k)
        (offspringPGF μ (r * x) / offspringPGF μ r)) ∧
    HasSum (fun k : ℕ => (k : ℝ) * tiltedMass μ r k) (tiltedMean μ r) ∧
    (∀ k : ℕ, μ {k} ≠ 0 ↔ (tiltedPMF μ hr0 hr).toMeasure {k} ≠ 0) ∧
    ∀ n : ℕ,
      Bienayme.conditioned μ n =
        Bienayme.conditioned (tiltedPMF μ hr0 hr).toMeasure n := by
  have hF := offspringPGF_pos μ hr0 hr
  have hraw := hasSum_raw_tiltedMass μ hr
  have hnorm : HasSum (tiltedMass μ r) 1 := by
    have hh := hraw.div_const (offspringPGF μ r)
    rw [div_self hF.ne'] at hh
    convert hh using 1
    ext k; simp only [tiltedMass]
  have hpgf : ∀ x : ℝ, ‖r * x‖ₑ < offspringRadius μ →
      HasSum (fun k => tiltedMass μ r k * x ^ k)
        (offspringPGF μ (r * x) / offspringPGF μ r) := by
    intro x hx
    convert (hasSum_raw_tiltedMass μ hx).div_const (offspringPGF μ r) using 1
    ext k
    simp only [tiltedMass, mul_pow]
    ring
  have hmass : HasSum (fun k : ℕ => (k : ℝ) * tiltedMass μ r k) (tiltedMean μ r) := by
    let f : ℕ → ℝ := fun k => (k : ℝ) * (μ {k}).toReal * r ^ k
    have hsucc : HasSum (fun n => f (n + 1)) (r * deriv (offspringPGF μ) r) := by
      convert (hasSum_deriv_offspringPGF μ hr).mul_left r using 1
      ext n
      simp only [f, pow_succ]
      push_cast
      ring
    have hfull : HasSum f (r * deriv (offspringPGF μ) r) := by
      have hh := (hasSum_nat_add_iff (f := f) (g := r * deriv (offspringPGF μ) r) 1).mp hsucc
      simpa [f] using hh
    convert hfull.div_const (offspringPGF μ r) using 1
    · ext k
      simp only [f, tiltedMass]
      ring
    · rfl
  have hsupport : ∀ k : ℕ, μ {k} ≠ 0 ↔
      (tiltedPMF μ hr0 hr).toMeasure {k} ≠ 0 := by
    intro k
    constructor
    · intro hk
      rw [(tiltedPMF μ hr0 hr).toMeasure_apply_singleton k (MeasurableSet.singleton k)]
      change ENNReal.ofReal (tiltedMass μ r k) ≠ 0
      rw [ENNReal.ofReal_ne_zero_iff]
      exact div_pos (mul_pos (pow_pos hr0 k)
        (ENNReal.toReal_pos hk (measure_ne_top _ _))) hF
    · intro hk hzero
      rw [(tiltedPMF μ hr0 hr).toMeasure_apply_singleton k (MeasurableSet.singleton k)] at hk
      change ENNReal.ofReal (tiltedMass μ r k) ≠ 0 at hk
      simp [tiltedMass, hzero] at hk
  have heq : ∀ k : ℕ, (tiltedPMF μ hr0 hr).toMeasure {k} =
      ENNReal.ofReal ((offspringPGF μ r)⁻¹) * ENNReal.ofReal r ^ k * μ {k} := by
    intro k
    rw [(tiltedPMF μ hr0 hr).toMeasure_apply_singleton k (MeasurableSet.singleton k)]
    change ENNReal.ofReal (tiltedMass μ r k) =
      ENNReal.ofReal ((offspringPGF μ r)⁻¹) * ENNReal.ofReal r ^ k * μ {k}
    rw [tiltedMass, ENNReal.ofReal_div_of_pos hF, ENNReal.ofReal_mul (pow_nonneg hr0.le k),
      ENNReal.ofReal_pow hr0.le, ENNReal.ofReal_toReal (measure_ne_top _ _), div_eq_mul_inv,
      ENNReal.ofReal_inv_of_pos hF]
    ac_rfl
  exact ⟨hraw, hnorm, hpgf, hmass, hsupport, fun n =>
    (Bienayme.conditioned_tilt_of_pos (tiltedPMF μ hr0 hr).toMeasure μ
      (inv_pos.mpr hF) hr0 heq n).symm⟩


/-- Infinite-mean form: summability of the real first moment is equivalent to
finiteness of the matching `∑' k, k μₖ`. -/
theorem tsum_first_moment_eq_top_iff_not_summable (μ : Measure ℕ)
    [IsProbabilityMeasure μ] :
    ∑' k : ℕ, (k : ℝ≥0∞) * μ {k} = ∞ ↔
      ¬ Summable (fun k : ℕ => (k : ℝ) * (μ {k}).toReal) := by
  constructor
  · intro htop hs
    have hfin : ∑' k : ℕ, (k : ℝ≥0∞) * μ {k} ≠ ∞ := by
      have heq : ∑' k : ℕ, (k : ℝ≥0∞) * μ {k} =
          ENNReal.ofReal (∑' k : ℕ, (k : ℝ) * (μ {k}).toReal) := by
        rw [ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (Nat.cast_nonneg k)
          ENNReal.toReal_nonneg) hs]
        apply tsum_congr
        intro k
        simp [ENNReal.ofReal_mul (Nat.cast_nonneg k)]
      rw [heq]
      have ht := hs.tsum_ofReal_ne_top
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (Nat.cast_nonneg k)
        ENNReal.toReal_nonneg) hs] at ht
      exact ht
    exact hfin htop
  · intro hs
    by_contra hfin
    apply hs
    have hh := (ENNReal.summable_toReal hfin).mul_left (1 : ℝ)
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, one_mul] using hh

/-- U2.4 with the conclusion written as an infinite real `tsum`. -/
theorem infinite_first_moment_tsum_of_tail_alpha_lt_one
    (μ : Measure ℕ) [IsProbabilityMeasure μ] {L : ℝ → ℝ} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : Bienayme.IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ (1 + α)))
      atTop (𝓝 1)) :
    ∑' n : ℕ, (n : ℝ≥0∞) * μ {n} = ∞ :=
  tsum_first_moment_eq_top_iff_not_summable μ |>.mpr
    (not_summable_first_moment_of_tail_alpha_lt_one μ hα0 hα1 hpos hL hsv hlocal)

/-- The actual tilted law has the logarithmic-derivative mean (also when the
mean is infinite, through `ENNReal.ofReal`'s convention for negative reals). -/
theorem offspringMean_tiltedPMF (μ : Measure ℕ) [IsProbabilityMeasure μ] {r : ℝ}
    (hr0 : 0 < r) (hr : ‖r‖ₑ < offspringRadius μ) :
    Bienayme.offspringMean (tiltedPMF μ hr0 hr).toMeasure =
      ENNReal.ofReal (tiltedMean μ r) := by
  obtain ⟨_, _, _, hm, _, _⟩ := exponential_tilt_U22 μ hr0 hr
  have hreal : HasSum (fun k : ℕ => ((tiltedPMF μ hr0 hr).toMeasure {k}).toReal * (k : ℝ))
      (tiltedMean μ r) := by
    convert hm using 1
    ext k
    rw [tiltedPMF_apply_toReal μ hr0 hr]
    ring
  rw [Bienayme.offspringMean, lintegral_countable']
  calc
    ∑' k : ℕ, (k : ℝ≥0∞) * (tiltedPMF μ hr0 hr).toMeasure {k} =
        ENNReal.ofReal (∑' k : ℕ,
          ((tiltedPMF μ hr0 hr).toMeasure {k}).toReal * (k : ℝ)) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg ENNReal.toReal_nonneg
        (Nat.cast_nonneg k)) hreal.summable]
      apply tsum_congr
      intro k
      simp [ENNReal.ofReal_mul (Nat.cast_nonneg k), mul_comm]
    _ = ENNReal.ofReal (tiltedMean μ r) := congrArg ENNReal.ofReal hreal.tsum_eq


/-- At nonnegative interior points the PGF is at least the mass at zero. -/
theorem offspringPGF_pos_of_zero_mass (μ : Measure ℕ) {r : ℝ}
    (hμ0 : 0 < (μ {0}).toReal) (hr0 : 0 ≤ r) (hr : ‖r‖ₑ < offspringRadius μ) :
    0 < offspringPGF μ r := by
  have hraw := hasSum_raw_tiltedMass μ hr
  have hle := hraw.summable.sum_le_tsum {0} (fun k _ =>
    mul_nonneg (pow_nonneg hr0 k) ENNReal.toReal_nonneg)
  rw [← hraw.tsum_eq]
  refine hμ0.trans_le ?_
  simpa using hle

/-- Every power moment of an interior positive tilt converges. -/
theorem summable_power_tiltedMass (μ : Measure ℕ) [IsProbabilityMeasure μ] {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (hr : ‖r‖ₑ < offspringRadius μ) (m : ℕ) :
    Summable (fun k : ℕ => (k : ℝ) ^ m * tiltedMass μ r k) := by
  have hF := offspringPGF_pos μ hr0 hr
  have hleone (k : ℕ) : (μ {k}).toReal ≤ 1 := by
    have h : μ {k} ≤ 1 := (measure_mono (Set.subset_univ {k})).trans_eq measure_univ
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top h
  have hgeom : Summable (fun k : ℕ => (k : ℝ) ^ m * r ^ k) :=
    summable_pow_mul_geometric_of_norm_lt_one m (by simpa [abs_of_pos hr0] using hr1)
  have hraw : Summable (fun k : ℕ => (offspringPGF μ r)⁻¹ *
      ((k : ℝ) ^ m * r ^ k * (μ {k}).toReal)) := by
    apply Summable.of_nonneg_of_le
      (f := fun k : ℕ => (offspringPGF μ r)⁻¹ * ((k : ℝ) ^ m * r ^ k)) (fun k => by positivity)
    · intro k
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hF.le)
      simpa using mul_le_mul_of_nonneg_left (hleone k)
        (mul_nonneg (pow_nonneg (Nat.cast_nonneg k) m) (pow_nonneg hr0.le k))
    · exact hgeom.mul_left _
  apply hraw.congr
  intro k
  simp only [tiltedMass]
  ring


/-- The tilt parameter is continuous at zero for the normalized logarithmic derivative. -/
@[simp] theorem tiltedMean_zero (μ : Measure ℕ) : tiltedMean μ 0 = 0 := by
  simp [tiltedMean]

/-- On every positive compact interval bounded away from one, and assuming only
`μ₀ > 0`, the PGF log-derivative is continuous. -/
theorem continuousOn_tiltedMean (μ : Measure ℕ) {b : ℝ}
    (hμ0 : 0 < (μ {0}).toReal) (hb0 : 0 < b) (hb1 : b < 1)
    (hradius : 1 ≤ offspringRadius μ) : ContinuousOn (tiltedMean μ) (Set.Icc 0 b) := by
  have hbR : ‖b‖ₑ < offspringRadius μ := by
    apply lt_of_lt_of_le _ hradius
    rw [Real.enorm_eq_ofReal hb0.le, ← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr hb1
  intro x hx
  have hx0 : 0 ≤ x := hx.1
  have hxb : x ≤ b := hx.2
  have hxR : ‖x‖ₑ < offspringRadius μ := by
    apply lt_of_le_of_lt _ hbR
    rw [Real.enorm_eq_ofReal hx0, Real.enorm_eq_ofReal hb0.le]
    exact ENNReal.ofReal_le_ofReal hxb
  have hF := offspringPGF_pos_of_zero_mass μ hμ0 hx0 hxR
  exact ((continuousAt_id.mul (continuousAt_deriv_offspringPGF μ hxR)).div
    (continuousAt_offspringPGF μ hxR) hF.ne').continuousWithinAt

/-- Corrected U2.4: a supercritical law with positive mass at zero has an
interior critical exponential tilt with every power moment finite. -/
theorem supercritical_equivalent_critical_U24 (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ0 : 0 < (μ {0}).toReal) (hmean : 1 < Bienayme.offspringMean μ) :
    ∃ b : ℝ, 0 < b ∧ b < 1 ∧ 1 < tiltedMean μ b ∧
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        HasSum (fun k : ℕ => (k : ℝ) * tiltedMass μ r k) 1 ∧
        (∀ m : ℕ, Summable (fun k : ℕ => (k : ℝ) ^ m * tiltedMass μ r k)) ∧
        ∃ ν : PMF ℕ,
          (∀ k : ℕ, (ν.toMeasure {k}).toReal = tiltedMass μ r k) ∧
          Bienayme.offspringMean ν.toMeasure = 1 ∧
          ∀ n : ℕ, Bienayme.conditioned μ n = Bienayme.conditioned ν.toMeasure n := by
  have hradius : 1 ≤ offspringRadius μ := by
    apply FormalMultilinearSeries.le_radius_of_summable (r := 1)
    have hs := Bienayme.summable_pgfReal μ 1 zero_le_one le_rfl
    simpa only [offspringPowerSeries, FormalMultilinearSeries.ofScalars_norm,
      NNReal.coe_one, one_pow, mul_one, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using hs
  rw [Bienayme.offspringMean, lintegral_countable'] at hmean
  have hev := (ENNReal.tendsto_nat_tsum (fun k : ℕ => (k : ℝ≥0∞) * μ {k})).eventually
    (Ioi_mem_nhds hmean)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  let S : ℝ → ℝ := fun r => ∑ k ∈ Finset.range N, (k : ℝ) * r ^ k * (μ {k}).toReal
  have hfin : ∑ k ∈ Finset.range N, (k : ℝ≥0∞) * μ {k} ≠ ∞ :=
    ENNReal.sum_ne_top.mpr (fun k _ => ENNReal.mul_ne_top (ENNReal.natCast_ne_top k)
      (measure_ne_top _ _))
  have hS1 : 1 < S 1 := by
    have hh := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hfin).mpr (hN N le_rfl)
    rw [ENNReal.toReal_one, ENNReal.toReal_sum (fun k _ => ENNReal.mul_ne_top
      (ENNReal.natCast_ne_top k) (measure_ne_top _ _))] at hh
    simpa [S] using hh
  have hcont : Continuous S := by
    apply continuous_finsetSum
    intro k _
    exact (continuous_const.mul (continuous_id.pow k)).mul continuous_const
  have hevS : ∀ᶠ r : ℝ in 𝓝 1, 1 < S r :=
    hcont.continuousAt.eventually (Ioi_mem_nhds hS1)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hevS
  let b := max (1 / 2 : ℝ) (1 - ε / 2)
  have hb0 : 0 < b := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hb1 : b < 1 := max_lt (by norm_num) (by linarith)
  have hbS : 1 < S b := by
    apply hball b
    have hb_le : b ≤ 1 := max_le (by norm_num) (by linarith)
    have hb_near : 1 - ε / 2 ≤ b := le_max_right _ _
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (by linarith)]
    linarith
  have hbR : ‖b‖ₑ < offspringRadius μ := by
    apply lt_of_lt_of_le _ hradius
    rw [Real.enorm_eq_ofReal hb0.le, ← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr hb1
  have hbF : 0 < offspringPGF μ b := offspringPGF_pos μ hb0 hbR
  have hmass : Summable (fun k : ℕ => (μ {k}).toReal) := by
    simpa using Bienayme.summable_pgfReal μ 1 zero_le_one le_rfl
  have hmass_sum : HasSum (fun k : ℕ => (μ {k}).toReal) 1 := by
    rw [← show ∑' k : ℕ, (μ {k}).toReal = 1 by
      have h := congrArg ENNReal.toReal
        (μ.tsum_indicator_apply_singleton Set.univ MeasurableSet.univ)
      simpa only [Set.indicator_univ, ENNReal.tsum_toReal_eq (fun k => measure_ne_top μ {k}),
        ENNReal.toReal_one, IsProbabilityMeasure.measure_univ] using h]
    exact hmass.hasSum
  have hbF1 : offspringPGF μ b ≤ 1 := by
    have hraw := hasSum_raw_tiltedMass μ hbR
    rw [← hraw.tsum_eq, ← hmass_sum.tsum_eq]
    apply hraw.summable.tsum_le_tsum _ hmass_sum.summable
    intro k
    nth_rewrite 2 [← one_mul ((μ {k}).toReal)]
    exact mul_le_mul_of_nonneg_right
      (by simpa using pow_le_one₀ hb0.le hb1.le) ENNReal.toReal_nonneg
  obtain ⟨_, _, _, hbmean, _, _⟩ := exponential_tilt_U22 μ hb0 hbR
  have hbprefix : S b / offspringPGF μ b ≤ tiltedMean μ b := by
    have hle := hbmean.summable.sum_le_tsum (Finset.range N) (fun k _ =>
      mul_nonneg (Nat.cast_nonneg k) (div_nonneg (mul_nonneg (pow_nonneg hb0.le k)
        ENNReal.toReal_nonneg) hbF.le))
    rw [← hbmean.tsum_eq]
    simp only [tiltedMass, S, Finset.sum_div]
    convert hle using 1
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hbmean_gt : 1 < tiltedMean μ b := by
    have hdiv : 1 < S b / offspringPGF μ b := by
      rw [lt_div_iff₀ hbF]
      nlinarith
    exact hdiv.trans_le hbprefix
  have hcontT := continuousOn_tiltedMean μ hμ0 hb0 hb1 hradius
  have hone : 1 ∈ Set.Icc (tiltedMean μ 0) (tiltedMean μ b) := by
    rw [tiltedMean_zero]
    exact ⟨zero_le_one, hbmean_gt.le⟩
  obtain ⟨r, hr, hrmean : tiltedMean μ r = 1⟩ :=
    intermediate_value_Icc hb0.le hcontT hone
  have hr0 : 0 < r := by
    refine lt_of_le_of_ne hr.1 ?_
    intro hz
    subst r
    rw [tiltedMean_zero] at hrmean
    exact zero_ne_one hrmean
  have hr1 : r < 1 := lt_of_le_of_lt hr.2 hb1
  have hrR : ‖r‖ₑ < offspringRadius μ := by
    apply lt_of_le_of_lt _ hbR
    rw [Real.enorm_eq_ofReal hr0.le, Real.enorm_eq_ofReal hb0.le]
    exact ENNReal.ofReal_le_ofReal hr.2
  refine ⟨b, hb0, hb1, hbmean_gt, r, hr0, hr1, ?_, ?_, tiltedPMF μ hr0 hrR,
    tiltedPMF_apply_toReal μ hr0 hrR, ?_, ?_⟩
  · obtain ⟨_, _, _, hm, _, _⟩ := exponential_tilt_U22 μ hr0 hrR
    simpa only [hrmean] using hm
  · exact summable_power_tiltedMass μ hr0 hr1 hrR
  · rw [offspringMean_tiltedPMF μ hr0 hrR, hrmean]
    exact ENNReal.ofReal_one
  · obtain ⟨_, _, _, _, _, hc⟩ := exponential_tilt_U22 μ hr0 hrR
    exact hc

end
end SubcriticalCauchy.TiltingFacts
