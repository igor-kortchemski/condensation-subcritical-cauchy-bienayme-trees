module

public import SubcriticalCauchy.LatticeFourier
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.Order.Compact

/-!
# Nonnegative Fourier defects and an atom lower bound

The zero atom of a lattice law supplies one of the two copies in the
symmetrization argument. These facts require no tail assumptions.
-/

@[expose] public section

open MeasureTheory AddCircle

namespace SubcriticalCauchy.Bienayme

/-- The real defect of a unit-circle character is nonnegative. -/
theorem lattice_defect_nonneg (k : ℤ) (θ : AddCircle (1 : ℝ)) :
    0 ≤ 1 - (fourier k θ).re := by
  have hh := Complex.re_le_norm (fourier k θ)
  have hn : ‖fourier k θ‖ = 1 := Circle.norm_coe _
  linarith

/-- The defect is integrable on any countable space with finite measure. -/
theorem integrable_lattice_defect {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsFiniteMeasure μ]
    (f : α → ℤ) (θ : AddCircle (1 : ℝ)) :
    Integrable (fun a => 1 - (fourier (f a) θ).re) μ := by
  refine (integrable_const (2 : ℝ)).mono'
    (measurable_of_countable _).aestronglyMeasurable (ae_of_all _ ?_)
  intro a
  rw [Real.norm_eq_abs]
  calc
    |1 - (fourier (f a) θ).re| ≤ |(1 : ℝ)| + |(fourier (f a) θ).re| := abs_sub _ _
    _ ≤ 1 + ‖fourier (f a) θ‖ := by
      simpa only [abs_one] using
        add_le_add (le_refl (1 : ℝ)) (Complex.abs_re_le_norm (fourier (f a) θ))
    _ = 2 := by rw [show ‖fourier (f a) θ‖ = 1 from Circle.norm_coe _]; norm_num

/-- Keeping just the second copy's zero atom in the symmetrization integral. -/
theorem lattice_defect_zero_atom_le (μ : Measure ℤ) [IsProbabilityMeasure μ]
    (θ : AddCircle (1 : ℝ)) :
    (μ {0}).toReal * (∫ k : ℤ, 1 - (fourier k θ).re ∂μ) ≤
      1 - ‖latticeFourier μ θ‖ ^ 2 := by
  have hpair := integrable_lattice_defect (μ.prod μ) (fun p : ℤ × ℤ => p.1 - p.2) θ
  have hslice (a : ℤ) :
      (μ {0}).toReal * (1 - (fourier a θ).re) ≤
        ∫ b : ℤ, 1 - (fourier (a - b) θ).re ∂μ := by
    have hh := setIntegral_le_integral (s := {0})
      (integrable_lattice_defect μ (fun b : ℤ => a - b) θ)
      (ae_of_all _ (fun b => lattice_defect_nonneg (a - b) θ))
    rw [integral_singleton] at hh
    simpa only [sub_zero, smul_eq_mul, measureReal_def] using hh
  rw [lattice_symmetrization μ θ, integral_prod _ hpair, ← integral_const_mul]
  exact integral_mono
    ((integrable_lattice_defect μ id θ).const_mul (μ {0}).toReal)
    hpair.integral_prod_left hslice

/-- The offspring law transported to the integers, without changing its atoms. -/
noncomputable def offspringIntegerLaw (μ : Measure ℕ) : Measure ℤ :=
  μ.map (fun k : ℕ => (k : ℤ))

instance offspringIntegerLaw_isProbabilityMeasure (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (offspringIntegerLaw μ) := by
  unfold offspringIntegerLaw
  infer_instance

theorem offspringIntegerLaw_singleton (μ : Measure ℕ) (k : ℕ) :
    offspringIntegerLaw μ {(k : ℤ)} = μ {k} := by
  rw [offspringIntegerLaw, Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
  congr 1
  ext n
  simp

/-- Real coordinates of the period-one character. -/
theorem lattice_character_re (k : ℤ) (x : ℝ) :
    (fourier k (x : AddCircle (1 : ℝ))).re = Real.cos (2 * Real.pi * (k : ℝ) * x) := by
  simp [Complex.exp_re]

/-- A single atom pair already lower-bounds the symmetrized defect. -/
theorem lattice_defect_atom_pair_le (μ : Measure ℤ) [IsProbabilityMeasure μ]
    (a b : ℤ) (θ : AddCircle (1 : ℝ)) :
    (μ {a}).toReal * (μ {b}).toReal * (1 - (fourier (a - b) θ).re) ≤
      1 - ‖latticeFourier μ θ‖ ^ 2 := by
  have hh := setIntegral_le_integral (s := {(a, b)})
    (integrable_lattice_defect (μ.prod μ) (fun p : ℤ × ℤ => p.1 - p.2) θ)
    (ae_of_all _ (fun p => lattice_defect_nonneg (p.1 - p.2) θ))
  rw [integral_singleton] at hh
  have hm : (μ.prod μ).real {(a, b)} = (μ {a}).toReal * (μ {b}).toReal := by
    rw [← Set.singleton_prod_singleton, measureReal_prod_prod]
    rfl
  rw [hm] at hh
  simpa only [smul_eq_mul, lattice_symmetrization] using hh

/-- Consecutive positive atoms force strict modulus decay at every
nonzero representative in the centered fundamental interval. -/
theorem norm_latticeFourier_lt_one (μ : Measure ℤ) [IsProbabilityMeasure μ]
    {a : ℤ} (ha : 0 < (μ {a}).toReal) (hb : 0 < (μ {a + 1}).toReal)
    {x : ℝ} (hx : x ≠ 0) (hbound : |x| ≤ 1 / 2) :
    ‖latticeFourier μ (x : AddCircle (1 : ℝ))‖ < 1 := by
  have harglo : -(2 * Real.pi) < 2 * Real.pi * x := by
    have := (abs_le.mp hbound).1
    nlinarith [Real.pi_pos]
  have harghi : 2 * Real.pi * x < 2 * Real.pi := by
    have := (abs_le.mp hbound).2
    nlinarith [Real.pi_pos]
  have hcos : Real.cos (2 * Real.pi * x) < 1 := lt_of_le_of_ne (Real.cos_le_one _) (by
    intro heq
    have hz := (Real.cos_eq_one_iff_of_lt_of_lt harglo harghi).mp heq
    exact hx ((mul_eq_zero.mp hz).resolve_left (by positivity)))
  have hh := lattice_defect_atom_pair_le μ a (a + 1) (x : AddCircle (1 : ℝ))
  have heq : a - (a + 1) = -1 := by ring
  rw [heq, lattice_character_re] at hh
  have hc : Real.cos (2 * Real.pi * ((-1 : ℤ) : ℝ) * x) = Real.cos (2 * Real.pi * x) := by
    simp [mul_neg, neg_mul]
  rw [hc] at hh
  have hp := mul_pos (mul_pos ha hb) (sub_pos.mpr hcos)
  have hn := norm_nonneg (latticeFourier μ (x : AddCircle (1 : ℝ)))
  nlinarith

/-- A uniform spectral gap away from zero on the centered fundamental interval. -/
theorem lattice_spectral_gap (μ : Measure ℤ) [IsProbabilityMeasure μ]
    {a : ℤ} (ha : 0 < (μ {a}).toReal) (hb : 0 < (μ {a + 1}).toReal)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ x : ℝ, δ ≤ |x| → |x| ≤ 1 / 2 →
      ‖latticeFourier μ (x : AddCircle (1 : ℝ))‖ ≤ ρ := by
  let s : Set ℝ := {x | δ ≤ |x|} ∩ Set.Icc (-(1 / 2)) (1 / 2)
  have hs : IsCompact s := isCompact_Icc.inter_left (isClosed_le continuous_const continuous_abs)
  have hf : Continuous (fun x : ℝ => ‖latticeFourier μ (x : AddCircle (1 : ℝ))‖) :=
    ((continuous_latticeFourier μ).comp (AddCircle.continuous_mk' _)).norm
  by_cases hne : s.Nonempty
  · obtain ⟨x, hx, hmax⟩ := hs.exists_isMaxOn hne hf.continuousOn
    have hx0 : x ≠ 0 := by
      intro hz
      have hh := hδ.trans_le hx.1
      simp [hz] at hh
    refine ⟨_, norm_nonneg _, norm_latticeFourier_lt_one μ ha hb
      hx0 (abs_le.mpr hx.2), ?_⟩
    intro y hy hyb
    exact hmax ⟨hy, abs_le.mp hyb⟩
  · refine ⟨0, le_rfl, zero_lt_one, ?_⟩
    intro x hx hxb
    exact (hne ⟨x, hx, abs_le.mp hxb⟩).elim

end SubcriticalCauchy.Bienayme
