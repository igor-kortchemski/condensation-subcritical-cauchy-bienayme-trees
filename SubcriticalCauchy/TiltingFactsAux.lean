module

public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Tactic.Convert

/-!
# Power-series infrastructure for exponential tilting

The radius is the genuine complex radius of convergence of the real offspring
power series. In particular the sum formulas below hold on `‖x‖ < ρ`, not
merely on a one-sided interval.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace SubcriticalCauchy.TiltingFacts

noncomputable section

/-- The real offspring PGF as a formal power series. -/
def offspringPowerSeries (μ : Measure ℕ) : FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ (fun k => (μ {k}).toReal)

/-- Its genuine radius of convergence. -/
def offspringRadius (μ : Measure ℕ) : ℝ≥0∞ := (offspringPowerSeries μ).radius

/-- The sum of the offspring PGF anywhere it is defined (zero outside its radius,
by the formal-series convention). -/
def offspringPGF (μ : Measure ℕ) : ℝ → ℝ := (offspringPowerSeries μ).sum

/-- Exact convergence of the PGF inside its radius. -/
theorem hasSum_offspringPGF (μ : Measure ℕ) {x : ℝ}
    (hx : ‖x‖ₑ < offspringRadius μ) :
    HasSum (fun k => (μ {k}).toReal * x ^ k) (offspringPGF μ x) := by
  have hr : 0 < (offspringPowerSeries μ).radius := bot_le.trans_lt hx
  have hb := ((offspringPowerSeries μ).hasFPowerSeriesOnBall hr).hasSum
    (show x ∈ Metric.eball 0 (offspringRadius μ) by simpa)
  simpa only [offspringPGF, offspringPowerSeries,
    FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm, zero_add] using hb

/-- The derivative of the PGF is its differentiated power series. -/
theorem hasSum_deriv_offspringPGF (μ : Measure ℕ) {x : ℝ}
    (hx : ‖x‖ₑ < offspringRadius μ) :
    HasSum (fun n : ℕ => (n + 1 : ℝ) * (μ {n + 1}).toReal * x ^ n)
      (deriv (offspringPGF μ) x) := by
  have hr : 0 < (offspringPowerSeries μ).radius := bot_le.trans_lt hx
  have hb : HasFPowerSeriesOnBall (offspringPGF μ) (offspringPowerSeries μ) 0
      (offspringPowerSeries μ).radius :=
    (offspringPowerSeries μ).hasFPowerSeriesOnBall hr
  have hs := hb.fderiv.hasSum
    (show x ∈ Metric.eball 0 (offspringRadius μ) by simpa)
  have hmap := hs.map (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ))
    (ContinuousLinearMap.continuous _)
  simp only [zero_add] at hmap
  convert hmap using 1
  · ext n
    symm
    change (offspringPowerSeries μ).derivSeries n (fun _ => x) 1 = _
    simp [offspringPowerSeries, smul_eq_mul, mul_comm]
  · exact fderiv_apply_one_eq_deriv.symm



/-- Continuity of the PGF inside its radius. -/
theorem continuousAt_offspringPGF (μ : Measure ℕ) {x : ℝ}
    (hx : ‖x‖ₑ < offspringRadius μ) : ContinuousAt (offspringPGF μ) x := by
  have hb := (offspringPowerSeries μ).hasFPowerSeriesOnBall (bot_le.trans_lt hx)
  have h := hb.hasFDerivAt hx
  simpa only [offspringPGF, zero_add] using h.continuousAt

/-- Continuity of the differentiated PGF inside its radius. -/
theorem continuousAt_deriv_offspringPGF (μ : Measure ℕ) {x : ℝ}
    (hx : ‖x‖ₑ < offspringRadius μ) : ContinuousAt (deriv (offspringPGF μ)) x := by
  have hb : HasFPowerSeriesOnBall (offspringPGF μ) (offspringPowerSeries μ) 0
      (offspringPowerSeries μ).radius :=
    (offspringPowerSeries μ).hasFPowerSeriesOnBall (bot_le.trans_lt hx)
  have hd := hb.fderiv.analyticAt_of_mem
    (show x ∈ Metric.eball 0 (offspringRadius μ) by simpa)
  have hc : ContinuousAt (fderiv ℝ (offspringPGF μ)) x := by
    simpa only [zero_add] using hd.continuousAt
  have he := (ContinuousLinearMap.continuous (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ))).continuousAt.comp hc
  exact he

end
end SubcriticalCauchy.TiltingFacts
