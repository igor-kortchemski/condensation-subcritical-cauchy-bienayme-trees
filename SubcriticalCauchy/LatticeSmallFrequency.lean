module

public import SubcriticalCauchy.LatticeConcentrationAux
public import SubcriticalCauchy.PotterBounds
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Small-frequency lower bounds for a lattice characteristic function

All slow-variation comparisons concern the original pointwise witness.
-/

@[expose] public section

open MeasureTheory AddCircle Filter
open scoped Topology

namespace SubcriticalCauchy.Bienayme

/-- Restricting a nonnegative character defect to finitely many atoms. -/
theorem sum_mass_lattice_defect_le (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (s : Finset ℕ) (θ : AddCircle (1 : ℝ)) :
    ∑ k ∈ s, (μ {k}).toReal * (1 - (fourier (k : ℤ) θ).re) ≤
      ∫ k : ℕ, 1 - (fourier (k : ℤ) θ).re ∂μ := by
  have hfi := integrable_lattice_defect μ (fun k : ℕ => (k : ℤ)) θ
  have hh := setIntegral_le_integral (s := (s : Set ℕ)) hfi
    (ae_of_all _ (fun k => lattice_defect_nonneg (k : ℤ) θ))
  rw [setIntegral_finset s hfi.integrableOn] at hh
  simpa only [smul_eq_mul, measureReal_def] using hh

/-- The quadratic character defect in the principal half-period. -/
theorem lattice_character_quadratic_lower (k : ℕ) (x : ℝ)
    (hkx : (k : ℝ) * |x| ≤ 1 / 2) :
    8 * (k : ℝ) ^ 2 * x ^ 2 ≤ 1 - (fourier (k : ℤ) (x : AddCircle (1 : ℝ))).re := by
  have harg : |2 * Real.pi * (k : ℝ) * x| ≤ Real.pi := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi * (k : ℝ))]
    nlinarith [Real.pi_pos]
  have hh := Real.cos_le_one_sub_mul_cos_sq harg
  have heq : 2 / Real.pi ^ 2 * (2 * Real.pi * (k : ℝ) * x) ^ 2 =
      8 * (k : ℝ) ^ 2 * x ^ 2 := by field_simp; ring
  rw [heq] at hh
  rw [lattice_character_re]
  push_cast
  linarith

/-- The zero-atom symmetrization bound written in the actual offspring law. -/
theorem offspring_defect_zero_atom_le (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (θ : AddCircle (1 : ℝ)) :
    (μ {0}).toReal * (∫ k : ℕ, 1 - (fourier (k : ℤ) θ).re ∂μ) ≤
      1 - ‖latticeFourier (offspringIntegerLaw μ) θ‖ ^ 2 := by
  have hh := lattice_defect_zero_atom_le (offspringIntegerLaw μ) θ
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, offspringIntegerLaw_singleton] at hh
  have hm : (∫ k : ℤ, 1 - (fourier k θ).re ∂offspringIntegerLaw μ) =
      ∫ k : ℕ, 1 - (fourier (k : ℤ) θ).re ∂μ := by
    rw [offspringIntegerLaw, integral_map (by fun_prop)
      (measurable_of_countable _).aestronglyMeasurable]
  rwa [hm] at hh

/-- A dyadic block lower bound before choosing its frequency-dependent scale. -/
theorem lattice_block_defect_lower (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {L : ℝ → ℝ} {d : ℕ} {z x : ℝ}
    (hcompare : ∀ k ∈ Finset.Ico d (d + d), L z / 2 ≤ L k)
    (hmass : ∀ k ∈ Finset.Ico d (d + d), L k / 2 ≤ (k : ℝ) ^ 2 * (μ {k}).toReal)
    (hphase : ∀ k ∈ Finset.Ico d (d + d), (k : ℝ) * |x| ≤ 1 / 2) :
    (d : ℝ) * (2 * L z * x ^ 2) ≤
      ∫ k : ℕ, 1 - (fourier (k : ℤ) (x : AddCircle (1 : ℝ))).re ∂μ := by
  have hterm (k : ℕ) (hk : k ∈ Finset.Ico d (d + d)) :
      2 * L z * x ^ 2 ≤ (μ {k}).toReal *
        (1 - (fourier (k : ℤ) (x : AddCircle (1 : ℝ))).re) := by
    have hquad := lattice_character_quadratic_lower k x (hphase k hk)
    calc
      2 * L z * x ^ 2 ≤ 4 * L k * x ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_right (hcompare k hk) (sq_nonneg x)]
      _ ≤ 8 * x ^ 2 * ((k : ℝ) ^ 2 * (μ {k}).toReal) := by
        nlinarith [mul_le_mul_of_nonneg_left (hmass k hk) (show 0 ≤ 8 * x ^ 2 by positivity)]
      _ = (μ {k}).toReal * (8 * (k : ℝ) ^ 2 * x ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hquad ENNReal.toReal_nonneg
  calc
    (d : ℝ) * (2 * L z * x ^ 2) = ∑ _k ∈ Finset.Ico d (d + d), 2 * L z * x ^ 2 := by simp
    _ ≤ ∑ k ∈ Finset.Ico d (d + d), (μ {k}).toReal *
        (1 - (fourier (k : ℤ) (x : AddCircle (1 : ℝ))).re) := Finset.sum_le_sum hterm
    _ ≤ _ := sum_mass_lattice_defect_le μ _ _

/-- Small-frequency lower bound with the original slowly varying witness. -/
theorem lattice_small_frequency
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ < 1)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1)) :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, 0 < x₀ ∧ ∀ x : ℝ, 0 < |x| → |x| ≤ x₀ →
      c * |x| * L (1 / |x|) ≤
        1 - ‖latticeFourier (offspringIntegerLaw μ) (x : AddCircle (1 : ℝ))‖ ^ 2 := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (hlocal.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)))
  obtain ⟨N, hUC⟩ := (slowlyVarying_uniform_compact_tail hpos hL hsv
    (by norm_num : (0 : ℝ) < 1 / 8) (by norm_num : (1 / 8 : ℝ) ≤ 1 / 2)
    (tendsto_natCast_atTop_atTop (R := ℝ)) (1 / 2) (by norm_num)).exists
  let R : ℝ := max (8 * ((K : ℝ) + 1)) (max (N : ℝ) 8)
  have hRK : 8 * ((K : ℝ) + 1) ≤ R := le_max_left _ _
  have hRN : (N : ℝ) ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hR8 : (8 : ℝ) ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  have hR : 0 < R := by linarith
  have hμ0 : 0 < (μ {0}).toReal := ENNReal.toReal_pos_iff.mpr
    ⟨mass_zero_pos_of_subcritical μ hm, measure_lt_top μ _⟩
  refine ⟨(μ {0}).toReal / 4, by positivity, 1 / R, by positivity, ?_⟩
  intro x hx hxb
  let z : ℝ := 1 / |x|
  have hzR : R ≤ z := (le_div_iff₀ hx).mpr (by
    have hh := (le_div_iff₀ hR).mp hxb
    nlinarith)
  have hz8 : 8 ≤ z := hR8.trans hzR
  have hz0 : 0 < z := by linarith
  have hLz : 0 < L z := hpos _ hz0
  have hzN : (N : ℝ) ≤ z := hRN.trans hzR
  have hza : z * |x| = 1 := div_mul_cancel₀ _ hx.ne'
  let d := ⌊z / 4⌋₊
  have hdhi : (d : ℝ) ≤ z / 4 := Nat.floor_le (by positivity)
  have hdlo : z / 8 ≤ (d : ℝ) := by
    have hh := Nat.lt_floor_add_one (z / 4)
    change z / 4 < (d : ℝ) + 1 at hh
    linarith
  have hdK : K ≤ d := by
    have hh : (K : ℝ) ≤ d := by linarith
    exact_mod_cast hh
  have hd0 : 0 < (d : ℝ) := by linarith
  have hklo (k : ℕ) (hk : k ∈ Finset.Ico d (d + d)) :
      (d : ℝ) ≤ k := Nat.cast_le.mpr (Finset.mem_Ico.mp hk).1
  have hkhi (k : ℕ) (hk : k ∈ Finset.Ico d (d + d)) :
      (k : ℝ) ≤ z / 2 := by
    have hh : (k : ℝ) < (d : ℝ) + d := by exact_mod_cast (Finset.mem_Ico.mp hk).2
    linarith
  have hcomp (k : ℕ) (hk : k ∈ Finset.Ico d (d + d)) : L z / 2 ≤ L k := by
    have hc : (k : ℝ) / z ∈ Set.Icc (1 / 8 : ℝ) (1 / 2) := by
      constructor
      · apply (le_div_iff₀ hz0).mpr
        linarith [hklo k hk]
      · exact (div_le_iff₀ hz0).mpr (by linarith [hkhi k hk])
    have hh := (abs_lt.mp (hUC z ((k : ℝ) / z) hzN hc)).1
    rw [div_mul_cancel₀ _ hz0.ne'] at hh
    have hr : (1 / 2 : ℝ) ≤ L k / L z := by linarith
    have hh := (le_div_iff₀ (hpos _ hz0)).mp hr
    linarith
  have hmass (k : ℕ) (hk : k ∈ Finset.Ico d (d + d)) :
      L k / 2 ≤ (k : ℝ) ^ 2 * (μ {k}).toReal := by
    have hk0 : 0 < (k : ℝ) := hd0.trans_le (hklo k hk)
    have hden : 0 < L k / (k : ℝ) ^ 2 := div_pos (hpos _ hk0) (sq_pos_of_pos hk0)
    have hh := mul_le_mul_of_nonneg_left
      ((lt_div_iff₀ hden).mp (hK k (hdK.trans (Finset.mem_Ico.mp hk).1))).le
      (sq_nonneg (k : ℝ))
    have heq : (k : ℝ) ^ 2 * ((1 / 2) * (L k / (k : ℝ) ^ 2)) = L k / 2 := by field_simp
    rwa [heq] at hh
  have hphase (k : ℕ) (hk : k ∈ Finset.Ico d (d + d)) :
      (k : ℝ) * |x| ≤ 1 / 2 := by
    have hh := mul_le_mul_of_nonneg_right (hkhi k hk) hx.le
    nlinarith
  have hblock := lattice_block_defect_lower μ hcomp hmass hphase
  have hlast : |x| * L z / 4 ≤ (d : ℝ) * (2 * L z * x ^ 2) := by
    calc
      |x| * L z / 4 = (z / 8) * (2 * L z * x ^ 2) := by
        rw [← sq_abs x]
        dsimp [z]
        field_simp
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hdlo (by positivity)
  calc
    (μ {0}).toReal / 4 * |x| * L (1 / |x|) =
        (μ {0}).toReal * (|x| * L z / 4) := by ring
    _ ≤ (μ {0}).toReal *
        (∫ k : ℕ, 1 - (fourier (k : ℤ) (x : AddCircle (1 : ℝ))).re ∂μ) :=
      mul_le_mul_of_nonneg_left (hlast.trans hblock) hμ0.le
    _ ≤ _ := offspring_defect_zero_atom_le μ _

/-- The spectral gap specialized to the actual offspring law. Measurability
is retained in the witness interface; this part only needs eventual positive atoms. -/
theorem offspring_lattice_spectral_gap
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ < 1)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (_hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1)) (δ : ℝ) (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ x : ℝ, δ ≤ |x| → |x| ≤ 1 / 2 →
      ‖latticeFourier (offspringIntegerLaw μ) (x : AddCircle (1 : ℝ))‖ ≤ ρ := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp (eventually_mass_pos μ ⟨hm, L, hpos, hsv, hlocal⟩)
  have ha : 0 < ((offspringIntegerLaw μ) {(K : ℤ)}).toReal := by
    rw [offspringIntegerLaw_singleton]
    exact ENNReal.toReal_pos_iff.mpr ⟨hK K le_rfl, measure_lt_top μ _⟩
  have hb : 0 < ((offspringIntegerLaw μ) {(K : ℤ) + 1}).toReal := by
    rw [show (K : ℤ) + 1 = ((K + 1 : ℕ) : ℤ) by simp, offspringIntegerLaw_singleton]
    exact ENNReal.toReal_pos_iff.mpr ⟨hK (K + 1) (by omega), measure_lt_top μ _⟩
  exact lattice_spectral_gap _ ha hb δ hδ

end SubcriticalCauchy.Bienayme
