module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# A boundary counterexample to the critical-tilt criterion

The unnumbered paragraph after Proposition `prop:tilting` states that a limit
of tilted means at least one ensures a critical exponential tilt. The mass
function with mass `1/2` at both `0` and `1` disproves that statement at equality:
every finite positive tilt has mean strictly less than one, although the means
tend to one as the tilt parameter tends to infinity.

This does not contradict Proposition `prop:tilting` itself. The definitions and
finite-sum certificates below describe an actual normalized mass function and
its exponential tilts. No probability or mean property is assumed.
-/

@[expose] public section

open Filter
open scoped Topology

noncomputable section

namespace SubcriticalCauchy.TiltingCounterexample

/-- The Bernoulli one-half distribution, expressed as real masses on `ℕ`. -/
def bernoulliMass (n : ℕ) : ℝ := if n ≤ 1 then 1 / 2 else 0

theorem bernoulliMass_nonneg (n : ℕ) : 0 ≤ bernoulliMass n := by
  unfold bernoulliMass
  split_ifs <;> norm_num

theorem bernoulliMass_eq_zero (n : ℕ) (hn : 2 ≤ n) : bernoulliMass n = 0 := by
  simp [bernoulliMass, show ¬ n ≤ 1 by omega]

private theorem hasSum_first_two (f : ℕ → ℝ) (hf : ∀ n, 2 ≤ n → f n = 0) :
    HasSum f (f 0 + f 1) := by
  have h : HasSum f (∑ n ∈ Finset.range 2, f n) :=
    hasSum_sum_of_ne_finset_zero (fun n hn => hf n (by
      simp only [Finset.mem_range] at hn
      omega))
  simpa [Finset.sum_range_succ] using h

/-- Normalization of the concrete offspring mass function. -/
theorem bernoulliMass_hasSum : HasSum bernoulliMass 1 := by
  convert hasSum_first_two bernoulliMass bernoulliMass_eq_zero using 1
  norm_num [bernoulliMass]

/-- Its generating function is a polynomial and is defined at every real point. -/
def bernoulliPGF (x : ℝ) : ℝ := (1 + x) / 2

/-- The defining PGF series converges to the stated polynomial for every real `x`. -/
theorem bernoulliPGF_hasSum (x : ℝ) :
    HasSum (fun n => bernoulliMass n * x ^ n) (bernoulliPGF x) := by
  have h := hasSum_first_two (fun n => bernoulliMass n * x ^ n)
    (fun n hn => by rw [bernoulliMass_eq_zero n hn, zero_mul])
  convert h using 1
  simp [bernoulliMass, bernoulliPGF]
  ring

theorem bernoulliPGF_pos {x : ℝ} (hx : 0 < x) : 0 < bernoulliPGF x := by
  dsimp [bernoulliPGF]
  positivity

theorem hasDerivAt_bernoulliPGF (x : ℝ) :
    HasDerivAt bernoulliPGF (1 / 2) x := by
  exact ((hasDerivAt_id x).const_add 1).div_const 2

theorem deriv_bernoulliPGF (x : ℝ) : deriv bernoulliPGF x = 1 / 2 :=
  (hasDerivAt_bernoulliPGF x).deriv

/-- The logarithmic-derivative expression for the tilted mean used in the paper. -/
def tiltedMean (r : ℝ) : ℝ := r * deriv bernoulliPGF r / bernoulliPGF r

theorem tiltedMean_eq (r : ℝ) : tiltedMean r = r / (1 + r) := by
  rw [tiltedMean, deriv_bernoulliPGF]
  dsimp [bernoulliPGF]
  rw [div_div_eq_mul_div]
  congr 1
  ring

/-- Exponential tilting of the concrete mass function by a finite parameter. -/
def tiltedMass (r : ℝ) (n : ℕ) : ℝ := r ^ n * bernoulliMass n / bernoulliPGF r

theorem tiltedMass_nonneg {r : ℝ} (hr : 0 < r) (n : ℕ) :
    0 ≤ tiltedMass r n := by
  exact div_nonneg (mul_nonneg (pow_nonneg hr.le n) (bernoulliMass_nonneg n))
    (bernoulliPGF_pos hr).le

theorem tiltedMass_eq_zero (r : ℝ) (n : ℕ) (hn : 2 ≤ n) : tiltedMass r n = 0 := by
  simp [tiltedMass, bernoulliMass_eq_zero n hn]

theorem tiltedMass_zero {r : ℝ} (hr : 0 < r) :
    tiltedMass r 0 = 1 / (1 + r) := by
  have hden : 1 + r ≠ 0 := ne_of_gt (by linarith)
  dsimp [tiltedMass, bernoulliMass, bernoulliPGF]
  norm_num
  field_simp

theorem tiltedMass_one {r : ℝ} (hr : 0 < r) :
    tiltedMass r 1 = r / (1 + r) := by
  have hden : 1 + r ≠ 0 := ne_of_gt (by linarith)
  dsimp [tiltedMass, bernoulliMass, bernoulliPGF]
  norm_num
  field_simp

/-- Every positive finite tilt is again normalized. -/
theorem tiltedMass_hasSum {r : ℝ} (hr : 0 < r) : HasSum (tiltedMass r) 1 := by
  have hden : 1 + r ≠ 0 := ne_of_gt (by linarith)
  have h := hasSum_first_two (tiltedMass r) (tiltedMass_eq_zero r)
  rw [tiltedMass_zero hr, tiltedMass_one hr] at h
  convert h using 1
  field_simp

/-- The actual first moment of the tilted masses equals the PGF expression. -/
theorem tiltedMass_mean {r : ℝ} (hr : 0 < r) :
    HasSum (fun n : ℕ => (n : ℝ) * tiltedMass r n) (tiltedMean r) := by
  have h := hasSum_first_two (fun n : ℕ => (n : ℝ) * tiltedMass r n)
    (fun n hn => by rw [tiltedMass_eq_zero r n hn, mul_zero])
  simpa [tiltedMean_eq, tiltedMass_one hr] using h

theorem tiltedMean_pos {r : ℝ} (hr : 0 < r) : 0 < tiltedMean r := by
  rw [tiltedMean_eq]
  exact div_pos hr (by linarith)

theorem tiltedMean_lt_one {r : ℝ} (hr : 0 < r) : tiltedMean r < 1 := by
  rw [tiltedMean_eq]
  exact (div_lt_one (by linarith)).2 (by linarith)

/-- The boundary value one is approached but is not attained at a finite tilt. -/
theorem tiltedMean_tendsto_one : Tendsto tiltedMean atTop (𝓝 1) := by
  have hi : Tendsto (fun x : ℝ => (x + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_id)
  have h : Tendsto (fun x : ℝ => 1 - (x + 1)⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hi
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [tiltedMean_eq]
  have hden : x + 1 ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

theorem no_finite_critical_tilt : ¬ ∃ r : ℝ, 0 < r ∧ tiltedMean r = 1 := by
  rintro ⟨r, hr, heq⟩
  exact (ne_of_lt (tiltedMean_lt_one hr)) heq

/-- A limit of tilted means equal to one need not give a finite critical tilt. -/
theorem critical_tilt_boundary_counterexample :
    Tendsto tiltedMean atTop (𝓝 1) ∧
      ¬ ∃ r : ℝ, 0 < r ∧ tiltedMean r = 1 :=
  ⟨tiltedMean_tendsto_one, no_finite_critical_tilt⟩

/-- Any mass function related by the paper's positive exponential equivalence
automatically has nonnegative masses. -/
theorem equivalentMass_nonneg {ν : ℕ → ℝ} {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r)
    (heq : ∀ k, bernoulliMass k = a * r ^ k * ν k) (k : ℕ) : 0 ≤ ν k := by
  apply (mul_nonneg_iff_of_pos_left (mul_pos ha (pow_pos hr k))).1
  rw [← heq k]
  exact bernoulliMass_nonneg k

/-- Positive exponential equivalence preserves the support `{0, 1}`. -/
theorem equivalentMass_eq_zero {ν : ℕ → ℝ} {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r)
    (heq : ∀ k, bernoulliMass k = a * r ^ k * ν k)
    (k : ℕ) (hk : 2 ≤ k) : ν k = 0 := by
  have hprod : (a * r ^ k) * ν k = 0 :=
    (heq k).symm.trans (bernoulliMass_eq_zero k hk)
  exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt (mul_pos ha (pow_pos hr k)))

/-- Every equivalent law retains strictly positive mass at zero. -/
theorem equivalentMass_zero_pos {ν : ℕ → ℝ} {a r : ℝ}
    (ha : 0 < a) (heq : ∀ k, bernoulliMass k = a * r ^ k * ν k) : 0 < ν 0 := by
  apply (mul_pos_iff_of_pos_left ha).1
  have h0 := heq 0
  norm_num [bernoulliMass] at h0
  rw [← h0]
  norm_num

/-- The first moment of every equivalent mass function is its mass at one. -/
theorem equivalentMass_mean {ν : ℕ → ℝ} {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r)
    (heq : ∀ k, bernoulliMass k = a * r ^ k * ν k) :
    HasSum (fun n : ℕ => (n : ℝ) * ν n) (ν 1) := by
  have h := hasSum_first_two (fun n : ℕ => (n : ℝ) * ν n)
    (fun n hn => by rw [equivalentMass_eq_zero ha hr heq n hn, mul_zero])
  simpa using h

/-- Normalization and the positive mass at zero force every equivalent law to
have a strictly subcritical mean. -/
theorem equivalentMass_mean_lt_one {ν : ℕ → ℝ} {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hnorm : HasSum ν 1)
    (heq : ∀ k, bernoulliMass k = a * r ^ k * ν k) : ν 1 < 1 := by
  have hsum : ν 0 + ν 1 = 1 :=
    (hasSum_first_two ν (equivalentMass_eq_zero ha hr heq)).unique hnorm
  have hzero := equivalentMass_zero_pos ha heq
  linarith

/-- There is no normalized critical law equivalent to Bernoulli one-half under
the exact relation used in Proposition `prop:tilting`. -/
theorem no_equivalent_critical_law :
    ¬ ∃ (ν : ℕ → ℝ) (a r : ℝ),
      0 < a ∧ 0 < r ∧ HasSum ν 1 ∧
      (∀ k, bernoulliMass k = a * r ^ k * ν k) ∧
      HasSum (fun n : ℕ => (n : ℝ) * ν n) 1 := by
  rintro ⟨ν, a, r, ha, hr, hnorm, heq, hmean⟩
  have hm : ν 1 = 1 := (equivalentMass_mean ha hr heq).unique hmean
  exact (ne_of_lt (equivalentMass_mean_lt_one ha hr hnorm heq)) hm

/-- The limit criterion's right side holds at equality, while its asserted
existence of an equivalent critical law fails. -/
theorem critical_equivalence_boundary_counterexample :
    Tendsto tiltedMean atTop (𝓝 1) ∧
      ¬ ∃ (ν : ℕ → ℝ) (a r : ℝ),
        0 < a ∧ 0 < r ∧ HasSum ν 1 ∧
        (∀ k, bernoulliMass k = a * r ^ k * ν k) ∧
        HasSum (fun n : ℕ => (n : ℝ) * ν n) 1 :=
  ⟨tiltedMean_tendsto_one, no_equivalent_critical_law⟩

end SubcriticalCauchy.TiltingCounterexample
