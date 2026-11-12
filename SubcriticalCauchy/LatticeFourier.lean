module

public import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic.FunProp

/-!
# Fourier inversion for integer-valued laws

We use the circle of period one with its probability Haar measure. Thus the
character at `θ` is `exp (2π i k θ)`, and inversion has no prefactor.
-/

@[expose] public section

open MeasureTheory AddCircle
open scoped ComplexConjugate

namespace SubcriticalCauchy.Bienayme

/-- The Fourier transform of an integer-valued law on the circle. -/
noncomputable def latticeFourier (μ : Measure ℤ) (θ : AddCircle (1 : ℝ)) : ℂ :=
  ∫ k, fourier k θ ∂μ

/-- Orthogonality of the integer characters, with probability normalization. -/
theorem integral_lattice_character (n k : ℤ) :
    (∫ θ : AddCircle (1 : ℝ), fourier n θ * fourier (-k) θ ∂haarAddCircle) =
      if n = k then 1 else 0 := by
  have hh := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) n) k
  simpa [fourierCoeff, smul_eq_mul, mul_comm, Pi.single_apply, eq_comm] using hh

/-- The shifted character kernel is jointly integrable for every finite law. -/
theorem integrable_lattice_kernel (μ : Measure ℤ) [IsFiniteMeasure μ] (k : ℤ) :
    Integrable (fun p : ℤ × AddCircle (1 : ℝ) => fourier p.1 p.2 * fourier (-k) p.2)
      (μ.prod haarAddCircle) := by
  have hc : Continuous (fun p : ℤ × AddCircle (1 : ℝ) => fourier p.1 p.2 * fourier (-k) p.2) := by
    exact (continuous_eval.comp
      ((continuous_of_discreteTopology : Continuous (fourier (T := (1 : ℝ)))).comp
        continuous_fst |>.prodMk continuous_snd)).mul
      ((fourier (-k)).continuous.comp continuous_snd)
  refine (integrable_const (1 : ℝ)).mono' hc.aestronglyMeasurable ?_
  exact ae_of_all _ (fun p => by simp [fourier_apply, Circle.norm_coe])

/-- Fourier inversion at a singleton for an arbitrary finite integer law. -/
theorem lattice_inversion (μ : Measure ℤ) [IsFiniteMeasure μ] (k : ℤ) :
    (∫ θ : AddCircle (1 : ℝ), latticeFourier μ θ * fourier (-k) θ ∂haarAddCircle) =
      ((μ {k}).toReal : ℂ) := by
  simp_rw [latticeFourier, ← integral_mul_const]
  rw [← integral_integral_swap (integrable_lattice_kernel μ k)]
  simp_rw [integral_lattice_character]
  have heq : (fun n : ℤ => if n = k then (1 : ℂ) else 0) =
      Set.indicator {k} (fun _ => (1 : ℂ)) := by
    ext n
    by_cases hn : n = k <;> simp [hn]
  rw [heq]
  simpa [measureReal_def] using
    (integral_indicator_const (μ := μ) (1 : ℂ) (measurableSet_singleton k))

/-- The inversion upper bound, uniform over all singleton locations. -/
theorem lattice_inversion_bound (μ : Measure ℤ) [IsFiniteMeasure μ] (k : ℤ) :
    (μ {k}).toReal ≤ ∫ θ : AddCircle (1 : ℝ), ‖latticeFourier μ θ‖ ∂haarAddCircle := by
  have hh := norm_integral_le_integral_norm
    (f := fun θ : AddCircle (1 : ℝ) => latticeFourier μ θ * fourier (-k) θ)
    (μ := haarAddCircle)
  rw [lattice_inversion] at hh
  simpa [norm_mul, fourier_apply, Circle.norm_coe, abs_of_nonneg ENNReal.toReal_nonneg] using hh

/-- Each character is integrable against a finite integer law. -/
theorem integrable_lattice_character (μ : Measure ℤ) [IsFiniteMeasure μ]
    (θ : AddCircle (1 : ℝ)) : Integrable (fun k : ℤ => fourier k θ) μ := by
  refine (integrable_const (1 : ℝ)).mono'
    (measurable_of_countable _).aestronglyMeasurable ?_
  exact ae_of_all _ (fun k => by simp [fourier_apply, Circle.norm_coe])

/-- A probability Fourier transform has modulus at most one. -/
theorem norm_latticeFourier_le_one (μ : Measure ℤ) [IsProbabilityMeasure μ]
    (θ : AddCircle (1 : ℝ)) : ‖latticeFourier μ θ‖ ≤ 1 := by
  simpa [latticeFourier, fourier_apply, Circle.norm_coe] using
    (norm_integral_le_integral_norm (μ := μ) (f := fun k : ℤ => fourier k θ))

/-- Continuity of the Fourier transform on the circle. -/
theorem continuous_latticeFourier (μ : Measure ℤ) [IsFiniteMeasure μ] :
    Continuous (latticeFourier μ) := by
  apply continuous_of_dominated (bound := fun _ : ℤ => (1 : ℝ))
  · intro θ
    exact (measurable_of_countable _).aestronglyMeasurable
  · intro θ
    exact ae_of_all _ (fun k => by simp [fourier_apply, Circle.norm_coe])
  · exact integrable_const _
  · exact ae_of_all _ (fun k => (fourier k).continuous)

/-- Symmetrization: the squared modulus is the cosine transform of the
difference of two independent copies. The integrand on the right is
nonnegative pointwise. -/
theorem lattice_symmetrization (μ : Measure ℤ) [IsProbabilityMeasure μ]
    (θ : AddCircle (1 : ℝ)) :
    1 - ‖latticeFourier μ θ‖ ^ 2 =
      ∫ p : ℤ × ℤ, 1 - (fourier (p.1 - p.2) θ).re ∂μ.prod μ := by
  have hfg : Integrable (fun p : ℤ × ℤ => fourier (p.1 - p.2) θ) (μ.prod μ) := by
    refine (integrable_const (1 : ℝ)).mono'
      (measurable_of_countable _).aestronglyMeasurable ?_
    exact ae_of_all _ (fun p => by simp [fourier_apply, Circle.norm_coe])
  have hid : (∫ p : ℤ × ℤ, fourier (p.1 - p.2) θ ∂μ.prod μ) =
      latticeFourier μ θ * conj (latticeFourier μ θ) := by
    simp_rw [sub_eq_add_neg, fourier_add, fourier_neg]
    exact (integral_prod_mul (μ := μ) (ν := μ)
      (fun k : ℤ => fourier k θ) (fun k : ℤ => conj (fourier k θ))).trans
      (by rw [integral_conj]; rfl)
  change 1 - ‖latticeFourier μ θ‖ ^ 2 =
    ∫ p : ℤ × ℤ, 1 - RCLike.re (fourier (p.1 - p.2) θ) ∂μ.prod μ
  rw [integral_sub (integrable_const _) hfg.re, integral_const, integral_re hfg, hid,
    Complex.mul_conj']
  simp [← Complex.ofReal_pow]

end SubcriticalCauchy.Bienayme
