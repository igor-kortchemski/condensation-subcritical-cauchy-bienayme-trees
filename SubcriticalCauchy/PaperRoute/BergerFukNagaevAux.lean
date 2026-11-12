module

public import SubcriticalCauchy.TruncatedExponential
public import SubcriticalCauchy.CenteringTailSeries

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

open MeasureTheory Filter
open scoped Topology ENNReal BigOperators

namespace SubcriticalCauchy.Bienayme

/-- The quadratic lower bound for the exponential residual. -/
theorem berger_sq_div_two_le_exp_residual {u : ℝ} (hu : 0 ≤ u) :
    u ^ 2 / 2 ≤ Real.exp u - 1 - u := by
  let f : ℕ → ℝ := fun n => u ^ n / (Nat.factorial n : ℝ)
  have hf : Summable f := by
    simpa only [f, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      (NormedSpace.expSeries_summable' (𝕂 := ℝ) (𝔸 := ℝ) u)
  have hsum : ∑ n ∈ Finset.range 3, f n ≤ ∑' n, f n :=
    hf.sum_le_tsum _ (fun n _ => by positivity)
  have hexp : Real.exp u = ∑' n, f n := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum (𝕂 := ℝ)]
    apply tsum_congr
    intro n
    simp [f, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [hexp]
  norm_num [f, Finset.sum_range_succ] at hsum
  nlinarith

theorem berger_exp_neg_quadratic {w : ℝ} (hw : w ≤ 0) :
    Real.exp w - 1 - w ≤ w ^ 2 / 2 := by
  let g : ℝ → ℝ := fun x => 1 - x + x ^ 2 / 2 - Real.exp (-x)
  have hcont : ContinuousOn g (Set.Ici 0) := by fun_prop
  have hder : ∀ x ≥ (0 : ℝ), HasDerivAt g (x - 1 + Real.exp (-x)) x := by
    intro x hx
    have h1 : HasDerivAt (fun x : ℝ => 1 - x + x ^ 2 / 2) (x - 1) x := by
      convert ((hasDerivAt_id x).const_sub 1).add ((hasDerivAt_pow 2 x).div_const 2) using 1
      · funext y
        simp only [id_eq, Pi.add_apply]
      · ring
    have h2 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-x)) x :=
      (by convert (hasDerivAt_neg x).exp using 1; ring_nf)
    convert h1.sub h2 using 1; ring_nf
  have hmono : MonotoneOn g (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont
    · intro x hx
      rw [interior_Ici] at hx
      exact (hder x hx.le).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hder x hx.le).deriv]
      have hh := Real.add_one_le_exp (-x)
      linarith
  have hz : g 0 = 0 := by simp [g]
  have hm := hmono (Set.mem_Ici.mpr (le_refl 0)) (Set.mem_Ici.mpr (neg_nonneg.mpr hw))
    (neg_nonneg.mpr hw)
  rw [hz] at hm
  dsimp [g] at hm
  simp only [neg_neg] at hm
  linarith

/-- Bennett's pointwise divided-difference inequality. -/
theorem berger_exp_le_bennett {t B w : ℝ} (ht : 0 ≤ t) (hB : 0 < B) (hw : w ≤ B) :
    Real.exp (t * w) ≤ 1 + t * w + w ^ 2 * ((Real.exp (t * B) - 1 - t * B) / B ^ 2) := by
  have hφ : 0 ≤ Real.exp (t * B) - 1 - t * B := by
    linarith [Real.add_one_le_exp (t * B)]
  have hquad : (t * B) ^ 2 / 2 ≤ Real.exp (t * B) - 1 - t * B :=
    berger_sq_div_two_le_exp_residual (mul_nonneg ht hB.le)
  by_cases hw0 : w < 0
  · have htw : t * w ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht hw0.le
    have hquadneg := berger_exp_neg_quadratic htw
    have hfactor : t ^ 2 / 2 ≤ (Real.exp (t * B) - 1 - t * B) / B ^ 2 := by
      rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 2) (sq_pos_of_pos hB)]
      nlinarith
    have hprod := mul_le_mul_of_nonneg_left hfactor (sq_nonneg w)
    nlinarith
  · have hw0' : 0 ≤ w := le_of_not_gt hw0
    let l := w / B
    have hl0 : 0 ≤ l := div_nonneg hw0' hB.le
    have hl1 : l ≤ 1 := (div_le_one hB).mpr hw
    have htB : 0 ≤ t * B := mul_nonneg ht hB.le
    let g : ℝ → ℝ := fun x => l ^ 2 * (Real.exp x - 1 - x) -
      (Real.exp (l * x) - 1 - l * x)
    have hexp (x : ℝ) : HasDerivAt Real.exp (Real.exp x) x := by
      simpa using Real.hasDerivAt_exp x
    have hder : ∀ x : ℝ, HasDerivAt g
        (l ^ 2 * (Real.exp x - 1) - (l * Real.exp (l * x) - l)) x := by
      intro x
      have h1 : HasDerivAt (fun x : ℝ => Real.exp x - 1 - x) (Real.exp x - 1) x := by
        convert ((hexp x).sub_const 1).sub (hasDerivAt_id x) using 1
        funext y
        simp only [Pi.sub_apply, id_eq]
      have h2 : HasDerivAt (fun x : ℝ => Real.exp (l * x) - 1 - l * x)
          (l * Real.exp (l * x) - l) x := by
        convert (((hasDerivAt_id x).const_mul l).exp.sub_const 1).sub
          ((hasDerivAt_id x).const_mul l) using 1
        · funext y
          simp only [Pi.sub_apply, id_eq]
        · simp only [id_eq]
          ring
      convert (h1.const_mul (l ^ 2)).sub h2 using 1
    have hmono : MonotoneOn g (Set.Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop)
      · intro x hx
        exact (hder x).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [(hder x).deriv]
        have hc := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ x)
          (sub_nonneg.mpr hl1) hl0 (by ring)
        simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero] at hc
        nlinarith
    have hg0 : g 0 = 0 := by simp [g]
    have hm := hmono (Set.mem_Ici.mpr (le_refl 0)) (Set.mem_Ici.mpr htB) htB
    rw [hg0] at hm
    dsimp [g] at hm
    have hm' : Real.exp (l * (t * B)) ≤
        1 + l * (t * B) + l ^ 2 * (Real.exp (t * B) - 1 - t * B) := by
      linarith
    have heq : l * (t * B) = t * w := by dsimp [l]; field_simp [hB.ne']
    rw [heq] at hm'
    calc
      _ ≤ 1 + t * w + l ^ 2 * (Real.exp (t * B) - 1 - t * B) := hm'
      _ = _ := by dsimp [l]; field_simp [hB.ne']



/-- Bennett exponential bound at the exact mean of a truncated variable. -/
theorem berger_truncated_mgf_bennett_le
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (Y : ℕ) (u q t B : ℝ)
    (hu : 0 ≤ u) (hq : 0 ≤ q) (ht : 0 ≤ t) (hB0 : 0 < B) (huB : u ≤ B)
    (hqint : (∫ k : ℕ, (if k < Y then (k : ℝ) else u) ∂μ) = q)
    (hYB : ∀ k : ℕ, k < Y → (k : ℝ) ≤ B) :
    (∫ k : ℕ, (if k < Y then Real.exp (t * ((k : ℝ) - q))
      else Real.exp (t * (u - q))) ∂μ) ≤
      1 + ((Real.exp (t * B) - 1 - t * B) / B ^ 2) *
        ((∑ k ∈ Finset.range Y, (k : ℝ) ^ 2 * (μ {k}).toReal) + (u ^ 2 + q ^ 2)) := by
  let F : ℕ → ℝ := fun k => if k < Y then Real.exp (t * ((k : ℝ) - q))
    else Real.exp (t * (u - q))
  let X : ℕ → ℝ := fun k => if k < Y then (k : ℝ) - q else u - q
  let Q : ℕ → ℝ := fun k => if k < Y then ((k : ℝ) - q) ^ 2 else (u - q) ^ 2
  let E := Real.exp (t * B)
  have hF : Integrable F μ := by
    refine Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable E ?_
    filter_upwards [] with k
    by_cases hk : k < Y
    · simp only [F, hk, ite_true, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (by linarith [hYB k hk]) ht)
    · simp only [F, hk, ite_false, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) ht)
  have hX : Integrable X μ := by
    refine Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable
      ((Y : ℝ) + q + u) ?_
    filter_upwards [] with k
    by_cases hk : k < Y
    · simp only [X, hk, ite_true, Real.norm_eq_abs]
      calc
        |(k : ℝ) - q| ≤ |(k : ℝ)| + |q| := abs_sub _ _
        _ ≤ (Y : ℝ) + q + u := by
          rw [abs_of_nonneg (Nat.cast_nonneg k), abs_of_nonneg hq]
          have hcast : (k : ℝ) ≤ Y := by exact_mod_cast hk.le
          linarith
    · simp only [X, hk, ite_false, Real.norm_eq_abs]
      calc
        |u - q| ≤ |u| + |q| := abs_sub _ _
        _ ≤ (Y : ℝ) + q + u := by
          rw [abs_of_nonneg hu, abs_of_nonneg hq]
          nlinarith [(Nat.cast_nonneg Y : (0 : ℝ) ≤ Y)]
  have hQ : Integrable Q μ := by
    refine Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable
      ((Y : ℝ) ^ 2 + (u ^ 2 + q ^ 2)) ?_
    filter_upwards [] with k
    by_cases hk : k < Y
    · simp only [Q, hk, ite_true, Real.norm_eq_abs, abs_pow, sq_abs]
      have hkY : (k : ℝ) ≤ Y := by exact_mod_cast hk.le
      nlinarith [sq_nonneg ((k : ℝ) - q), sq_nonneg ((k : ℝ) + q),
        (Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
    · simp only [Q, hk, ite_false, Real.norm_eq_abs, abs_pow, sq_abs]
      nlinarith [mul_nonneg hu hq, sq_nonneg (Y : ℝ)]
  have hpoint (k : ℕ) : F k ≤ 1 + t * X k +
      ((Real.exp (t * B) - 1 - t * B) / B ^ 2) * Q k := by
    by_cases hk : k < Y
    · simp only [F, X, Q, hk, ite_true]
      convert berger_exp_le_bennett ht hB0 (w := (k : ℝ) - q) (by linarith [hYB k hk]) using 1; ring_nf
    · simp only [F, X, Q, hk, ite_false]
      convert berger_exp_le_bennett ht hB0 (w := u - q) (by linarith) using 1; ring_nf
  have hG : Integrable (fun k => 1 + t * X k + ((Real.exp (t * B) - 1 - t * B) / B ^ 2) * Q k) μ :=
    ((integrable_const 1).add (hX.const_mul t)).add (hQ.const_mul ((Real.exp (t * B) - 1 - t * B) / B ^ 2))
  have hXint : ∫ k, X k ∂μ = 0 := by
    have hdecomp : X = (fun k => (if k < Y then (k : ℝ) else u) - q) := by
      funext k; dsimp [X]; split_ifs <;> ring
    rw [hdecomp, integral_sub]
    · rw [hqint, integral_const]; simp
    · refine Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable ((Y : ℝ) + u) ?_
      filter_upwards [] with k
      by_cases hk : k < Y
      · simp only [hk, ite_true, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
        have hcast : (k : ℝ) ≤ Y := by exact_mod_cast hk.le
        exact hcast.trans (le_add_of_nonneg_right hu)
      · simp only [hk, ite_false, Real.norm_eq_abs, abs_of_nonneg hu]
        exact le_add_of_nonneg_left (Nat.cast_nonneg Y)
    · exact integrable_const q
  have hQint : ∫ k, Q k ∂μ ≤
      (∑ k ∈ Finset.range Y, (k : ℝ) ^ 2 * (μ {k}).toReal) + (u ^ 2 + q ^ 2) := by
    let R : ℕ → ℝ := fun k => (if k < Y then (k : ℝ) ^ 2 else 0) + (u ^ 2 + q ^ 2)
    have hQR : ∀ k, Q k ≤ R k := by
      intro k; dsimp [Q, R]; split_ifs <;> nlinarith [mul_nonneg (Nat.cast_nonneg k) hq]
    have hRint : ∫ k, R k ∂μ =
        (∫ k : ℕ, (if k < Y then (k : ℝ) ^ 2 else 0) ∂μ) + (u ^ 2 + q ^ 2) := by
      dsimp [R]
      rw [integral_add _ (integrable_const _), integral_const]
      · simp
      · refine Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable ((Y : ℝ) ^ 2) ?_
        filter_upwards [] with k
        by_cases hk : k < Y
        · simp only [hk, ite_true, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (k : ℝ))]
          exact pow_le_pow_left₀ (Nat.cast_nonneg k) (by exact_mod_cast hk.le) 2
        · simp [hk, sq_nonneg (Y : ℝ)]
    have hR : Integrable R μ := by
      dsimp [R]
      exact (Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable ((Y : ℝ) ^ 2)
        (by
          filter_upwards [] with k
          by_cases hk : k < Y
          · simp only [hk, ite_true, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (k : ℝ))]
            exact pow_le_pow_left₀ (Nat.cast_nonneg k) (by exact_mod_cast hk.le) 2
          · simp [hk, sq_nonneg (Y : ℝ)])).add (integrable_const _)
    have hprefix : (∫ k : ℕ, (if k < Y then (k : ℝ) ^ 2 else 0) ∂μ) =
        ∑ k ∈ Finset.range Y, (μ {k}).toReal * (k : ℝ) ^ 2 := by
      rw [integral_bounded_prefix (Y := Y) μ _ ((Y : ℝ) ^ 2) (fun k => by
        by_cases hk : k < Y
        · simp [hk, pow_le_pow_left₀
            (Nat.cast_nonneg k) (show (k : ℝ) ≤ Y by exact_mod_cast hk.le) 2]
        · simp [hk]) (fun k hk => by simp [show ¬k < Y from Nat.not_lt.mpr hk])]
      apply Finset.sum_congr rfl
      intro k hk
      rw [ite_eq_left (Finset.mem_range.mp hk)]
    calc
      _ ≤ ∫ k, R k ∂μ := integral_mono hQ hR hQR
      _ = (∫ k : ℕ, (if k < Y then (k : ℝ) ^ 2 else 0) ∂μ) + (u ^ 2 + q ^ 2) := hRint
      _ = (∑ k ∈ Finset.range Y, (μ {k}).toReal * (k : ℝ) ^ 2) + (u ^ 2 + q ^ 2) := by rw [hprefix]
      _ = _ := by
        apply add_right_cancel_iff.mpr
        apply Finset.sum_congr rfl
        intro k _
        exact mul_comm _ _
  calc
    (∫ k, F k ∂μ) ≤ ∫ k, (1 + t * X k + ((Real.exp (t * B) - 1 - t * B) / B ^ 2) * Q k) ∂μ :=
      integral_mono hF hG hpoint
    _ = 1 + t * (∫ k, X k ∂μ) +
        ((Real.exp (t * B) - 1 - t * B) / B ^ 2) * (∫ k, Q k ∂μ) := by
      have hlinint : ∫ k, (1 + t * X k) ∂μ = 1 + t * ∫ k, X k ∂μ := by
        rw [integral_add (integrable_const 1) (hX.const_mul t), integral_const_mul,
          integral_const]
        simp
      have hadd : ∫ k, (1 + t * X k + ((Real.exp (t * B) - 1 - t * B) / B ^ 2) * Q k) ∂μ =
          (∫ k, (1 + t * X k) ∂μ) + ∫ k, (((Real.exp (t * B) - 1 - t * B) / B ^ 2) * Q k) ∂μ :=
        integral_add ((integrable_const 1).add (hX.const_mul t)) (hQ.const_mul _)
      rw [hadd, hlinint, integral_const_mul]
    _ ≤ 1 + ((Real.exp (t * B) - 1 - t * B) / B ^ 2) * ((∑ k ∈ Finset.range Y, (k : ℝ) ^ 2 * (μ {k}).toReal) + (u ^ 2 + q ^ 2)) := by
      rw [hXint]
      have hcoef : 0 ≤ (Real.exp (t * B) - 1 - t * B) / B ^ 2 := by
        have hp : 0 ≤ Real.exp (t * B) - 1 - t * B := by linarith [Real.add_one_le_exp (t * B)]
        positivity
      nlinarith [mul_le_mul_of_nonneg_left hQint hcoef]


theorem berger_truncated_mgf_le
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (Y : ℕ) (u q t B : ℝ)
    (hu : 0 ≤ u) (hq : 0 ≤ q) (ht : 0 ≤ t) (hB : 0 ≤ B) (huB : u ≤ B)
    (hqint : (∫ k : ℕ, (if k < Y then (k : ℝ) else u) ∂μ) = q)
    (hYB : ∀ k : ℕ, k < Y → (k : ℝ) ≤ B) :
    (∫ k : ℕ, (if k < Y then Real.exp (t * ((k : ℝ) - q))
      else Real.exp (t * (u - q))) ∂μ) ≤
      1 + t ^ 2 * Real.exp (t * B) *
        ((∑ k ∈ Finset.range Y, (k : ℝ) ^ 2 * (μ {k}).toReal) + (u ^ 2 + q ^ 2)) := by
  let F : ℕ → ℝ := fun k => if k < Y then Real.exp (t * ((k : ℝ) - q))
    else Real.exp (t * (u - q))
  let X : ℕ → ℝ := fun k => if k < Y then (k : ℝ) - q else u - q
  let Q : ℕ → ℝ := fun k => if k < Y then ((k : ℝ) - q) ^ 2 else (u - q) ^ 2
  let E := Real.exp (t * B)
  have hF : Integrable F μ := by
    refine Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable E ?_
    filter_upwards [] with k
    by_cases hk : k < Y
    · simp only [F, hk, ite_true, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (by linarith [hYB k hk]) ht)
    · simp only [F, hk, ite_false, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) ht)
  have hX : Integrable X μ := by
    refine Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable
      ((Y : ℝ) + q + u) ?_
    filter_upwards [] with k
    by_cases hk : k < Y
    · simp only [X, hk, ite_true, Real.norm_eq_abs]
      calc
        |(k : ℝ) - q| ≤ |(k : ℝ)| + |q| := abs_sub _ _
        _ ≤ (Y : ℝ) + q + u := by
          rw [abs_of_nonneg (Nat.cast_nonneg k), abs_of_nonneg hq]
          have hcast : (k : ℝ) ≤ Y := by exact_mod_cast hk.le
          linarith
    · simp only [X, hk, ite_false, Real.norm_eq_abs]
      calc
        |u - q| ≤ |u| + |q| := abs_sub _ _
        _ ≤ (Y : ℝ) + q + u := by
          rw [abs_of_nonneg hu, abs_of_nonneg hq]
          nlinarith [(Nat.cast_nonneg Y : (0 : ℝ) ≤ Y)]
  have hQ : Integrable Q μ := by
    refine Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable
      ((Y : ℝ) ^ 2 + (u ^ 2 + q ^ 2)) ?_
    filter_upwards [] with k
    by_cases hk : k < Y
    · simp only [Q, hk, ite_true, Real.norm_eq_abs, abs_pow, sq_abs]
      have hkY : (k : ℝ) ≤ Y := by exact_mod_cast hk.le
      nlinarith [sq_nonneg ((k : ℝ) - q), sq_nonneg ((k : ℝ) + q),
        (Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
    · simp only [Q, hk, ite_false, Real.norm_eq_abs, abs_pow, sq_abs]
      nlinarith [mul_nonneg hu hq, sq_nonneg (Y : ℝ)]
  have hpoint (k : ℕ) : F k ≤ 1 + t * X k + (t ^ 2 * E) * Q k := by
    have harg : t * ((if k < Y then (k : ℝ) else u) - q) ≤ t * B :=
      mul_le_mul_of_nonneg_left (by split_ifs with hk <;> [linarith [hYB k hk]; linarith]) ht
    have htay := exp_le_one_add_add_sq_mul_exp_max
      (t * ((if k < Y then (k : ℝ) else u) - q))
    have hmax : Real.exp (max (t * ((if k < Y then (k : ℝ) else u) - q)) 0) ≤ E :=
      Real.exp_le_exp.mpr (max_le harg (mul_nonneg ht hB))
    by_cases hk : k < Y
    · simp only [hk, ite_true] at htay hmax
      simp only [F, X, Q, hk, ite_true]
      calc
        _ ≤ 1 + t * ((k : ℝ) - q) + (t * ((k : ℝ) - q)) ^ 2 *
              Real.exp (max (t * ((k : ℝ) - q)) 0) := htay
        _ ≤ 1 + t * ((k : ℝ) - q) + (t * ((k : ℝ) - q)) ^ 2 * E :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hmax (sq_nonneg _))
        _ = _ := by ring
    · simp only [hk, ite_false] at htay hmax
      simp only [F, X, Q, hk, ite_false]
      calc
        _ ≤ 1 + t * (u - q) + (t * (u - q)) ^ 2 *
              Real.exp (max (t * (u - q)) 0) := htay
        _ ≤ 1 + t * (u - q) + (t * (u - q)) ^ 2 * E :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hmax (sq_nonneg _))
        _ = _ := by ring
  have hG : Integrable (fun k => 1 + t * X k + (t ^ 2 * E) * Q k) μ :=
    ((integrable_const 1).add (hX.const_mul t)).add (hQ.const_mul (t ^ 2 * E))
  have hXint : ∫ k, X k ∂μ = 0 := by
    have hdecomp : X = (fun k => (if k < Y then (k : ℝ) else u) - q) := by
      funext k; dsimp [X]; split_ifs <;> ring
    rw [hdecomp, integral_sub]
    · rw [hqint, integral_const]; simp
    · refine Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable ((Y : ℝ) + u) ?_
      filter_upwards [] with k
      by_cases hk : k < Y
      · simp only [hk, ite_true, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
        have hcast : (k : ℝ) ≤ Y := by exact_mod_cast hk.le
        exact hcast.trans (le_add_of_nonneg_right hu)
      · simp only [hk, ite_false, Real.norm_eq_abs, abs_of_nonneg hu]
        exact le_add_of_nonneg_left (Nat.cast_nonneg Y)
    · exact integrable_const q
  have hQint : ∫ k, Q k ∂μ ≤
      (∑ k ∈ Finset.range Y, (k : ℝ) ^ 2 * (μ {k}).toReal) + (u ^ 2 + q ^ 2) := by
    let R : ℕ → ℝ := fun k => (if k < Y then (k : ℝ) ^ 2 else 0) + (u ^ 2 + q ^ 2)
    have hQR : ∀ k, Q k ≤ R k := by
      intro k; dsimp [Q, R]; split_ifs <;> nlinarith [mul_nonneg (Nat.cast_nonneg k) hq]
    have hRint : ∫ k, R k ∂μ =
        (∫ k : ℕ, (if k < Y then (k : ℝ) ^ 2 else 0) ∂μ) + (u ^ 2 + q ^ 2) := by
      dsimp [R]
      rw [integral_add _ (integrable_const _), integral_const]
      · simp
      · refine Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable ((Y : ℝ) ^ 2) ?_
        filter_upwards [] with k
        by_cases hk : k < Y
        · simp only [hk, ite_true, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (k : ℝ))]
          exact pow_le_pow_left₀ (Nat.cast_nonneg k) (by exact_mod_cast hk.le) 2
        · simp [hk, sq_nonneg (Y : ℝ)]
    have hR : Integrable R μ := by
      dsimp [R]
      exact (Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable ((Y : ℝ) ^ 2)
        (by
          filter_upwards [] with k
          by_cases hk : k < Y
          · simp only [hk, ite_true, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (k : ℝ))]
            exact pow_le_pow_left₀ (Nat.cast_nonneg k) (by exact_mod_cast hk.le) 2
          · simp [hk, sq_nonneg (Y : ℝ)])).add (integrable_const _)
    have hprefix : (∫ k : ℕ, (if k < Y then (k : ℝ) ^ 2 else 0) ∂μ) =
        ∑ k ∈ Finset.range Y, (μ {k}).toReal * (k : ℝ) ^ 2 := by
      rw [integral_bounded_prefix (Y := Y) μ _ ((Y : ℝ) ^ 2) (fun k => by
        by_cases hk : k < Y
        · simp [hk, pow_le_pow_left₀
            (Nat.cast_nonneg k) (show (k : ℝ) ≤ Y by exact_mod_cast hk.le) 2]
        · simp [hk]) (fun k hk => by simp [show ¬k < Y from Nat.not_lt.mpr hk])]
      apply Finset.sum_congr rfl
      intro k hk
      rw [ite_eq_left (Finset.mem_range.mp hk)]
    calc
      _ ≤ ∫ k, R k ∂μ := integral_mono hQ hR hQR
      _ = (∫ k : ℕ, (if k < Y then (k : ℝ) ^ 2 else 0) ∂μ) + (u ^ 2 + q ^ 2) := hRint
      _ = (∑ k ∈ Finset.range Y, (μ {k}).toReal * (k : ℝ) ^ 2) + (u ^ 2 + q ^ 2) := by rw [hprefix]
      _ = _ := by
        apply add_right_cancel_iff.mpr
        apply Finset.sum_congr rfl
        intro k _
        exact mul_comm _ _
  calc
    (∫ k, F k ∂μ) ≤ ∫ k, (1 + t * X k + (t ^ 2 * E) * Q k) ∂μ :=
      integral_mono hF hG hpoint
    _ = 1 + t * (∫ k, X k ∂μ) + (t ^ 2 * E) * (∫ k, Q k ∂μ) := by
      have hlinint : ∫ k, (1 + t * X k) ∂μ = 1 + t * ∫ k, X k ∂μ := by
        rw [integral_add (integrable_const 1) (hX.const_mul t), integral_const_mul,
          integral_const]
        simp
      have hadd : ∫ k, (1 + t * X k + (t ^ 2 * E) * Q k) ∂μ =
          (∫ k, (1 + t * X k) ∂μ) + ∫ k, ((t ^ 2 * E) * Q k) ∂μ :=
        integral_add ((integrable_const 1).add (hX.const_mul t)) (hQ.const_mul _)
      rw [hadd, hlinint, integral_const_mul]
    _ ≤ 1 + t ^ 2 * E * ((∑ k ∈ Finset.range Y, (k : ℝ) ^ 2 * (μ {k}).toReal) + (u ^ 2 + q ^ 2)) := by
      rw [hXint]
      have hcoef : 0 ≤ t ^ 2 * E := mul_nonneg (sq_nonneg t) (Real.exp_pos _).le
      nlinarith [mul_le_mul_of_nonneg_left hQint hcoef]

/-- Exponential Markov with the prefix mean as centering. -/
theorem berger_pi_truncated_probability_le
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (Y j : ℕ) (u t z q : ℝ) (hu : 0 ≤ u) (huY : u ≤ (Y : ℝ)) (ht : 0 ≤ t) :
    ((Measure.pi fun _ : Fin j => μ)
      {ω | z ≤ (∑ i, (ω i : ℝ)) - q * j ∧ ∀ i, ω i < Y}).toReal ≤
      Real.exp (-t * z) *
        (∫ k : ℕ, (if k < Y then Real.exp (t * ((k : ℝ) - q))
        else Real.exp (t * (u - q))) ∂μ) ^ j := by
  let f : ℕ → ℝ := fun k => if k < Y then Real.exp (t * ((k : ℝ) - q))
    else Real.exp (t * (u - q))
  let F : (Fin j → ℕ) → ℝ := fun ω => ∏ i, f (ω i)
  let E : Set (Fin j → ℕ) := {ω | z ≤ (∑ i, (ω i : ℝ)) - q * j ∧ ∀ i, ω i < Y}
  let A := ∫ k, f k ∂μ
  have hf : Integrable f μ := by
    refine Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable
      (Real.exp (t * ((Y : ℝ) + |q|))) ?_
    filter_upwards [] with k
    by_cases hk : k < Y
    · simp only [f, hk, ite_true, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ ht
      have hkY : (k : ℝ) ≤ Y := by exact_mod_cast hk.le
      linarith [neg_le_abs q]
    · simp only [f, hk, ite_false, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ ht
      have h₁ : u - q ≤ |u| + |q| := by linarith [neg_le_abs q, le_abs_self u]
      rw [abs_of_nonneg hu] at h₁
      exact h₁.trans (add_le_add huY le_rfl)
  have hF : Integrable F (Measure.pi fun _ : Fin j => μ) := Integrable.fin_nat_prod (fun _ => hf)
  have hFnonneg : 0 ≤ᵐ[Measure.pi fun _ : Fin j => μ] F :=
    ae_of_all _ (fun _ => Finset.prod_nonneg (fun _ _ => by
      dsimp [f]; split_ifs <;> positivity))
  have hFexp (ω : Fin j → ℕ) (hωY : ∀ i, ω i < Y) :
      F ω = Real.exp (t * ((∑ i, (ω i : ℝ)) - q * j)) := by
    dsimp [F, f]
    simp_rw [hωY, ite_true, ← Real.exp_sum]
    congr 1
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum]
    ring
  have hsubset : E ⊆ {ω | Real.exp (t * z) ≤ F ω} := by
    intro ω hω
    change Real.exp (t * z) ≤ F ω
    rw [hFexp ω hω.2]
    exact Real.exp_le_exp.mpr (by have := mul_le_mul_of_nonneg_left hω.1 ht; convert this using 1)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := Measure.pi fun _ : Fin j => μ) hFnonneg hF (Real.exp (t * z))
  have hint : ∫ ω, F ω ∂(Measure.pi fun _ : Fin j => μ) = A ^ j := by
    dsimp [F, A]
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      (integral_fin_nat_prod_eq_prod (μ := fun _ : Fin j => μ) (fun _ => f))
  rw [hint] at hmarkov
  change ((Measure.pi fun _ : Fin j => μ) E).toReal ≤ _
  calc
    _ = Real.exp (-t * z) * (Real.exp (t * z) * ((Measure.pi fun _ : Fin j => μ) E).toReal) := by
      rw [← mul_assoc, ← Real.exp_add]; simp
    _ ≤ Real.exp (-t * z) * (Real.exp (t * z) *
        ((Measure.pi fun _ : Fin j => μ).real {ω | Real.exp (t * z) ≤ F ω})) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (measureReal_mono hsubset) (Real.exp_pos _).le) (Real.exp_pos _).le
    _ ≤ _ := mul_le_mul_of_nonneg_left hmarkov (Real.exp_pos _).le


theorem berger_mul_slowlyVarying_atTop {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L) {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) :
    Tendsto (fun n => a n * L (a n)) atTop atTop := by
  obtain ⟨C, hC, N, hN, hcomp⟩ := sqrt_potter_comparison hpos hL hsv
  let D := L N * Real.sqrt N / C
  have hD : 0 < D := div_pos (mul_pos (hpos N hN) (Real.sqrt_pos.mpr hN)) hC
  have hmain : Tendsto (fun n : ℕ => D * Real.sqrt (a n)) atTop atTop := by
    simpa only [Function.comp_def, mul_comm] using
      (Real.tendsto_sqrt_atTop.comp ha).atTop_mul_const hD
  apply tendsto_atTop_mono' atTop _ hmain
  filter_upwards [ha.eventually_ge_atTop N] with n hn
  have h := hcomp N (a n) le_rfl hn
  have hDle : D ≤ L (a n) * Real.sqrt (a n) :=
    (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using h)
  have hs : 0 ≤ Real.sqrt (a n) := Real.sqrt_nonneg _
  calc
    D * Real.sqrt (a n) ≤ (L (a n) * Real.sqrt (a n)) * Real.sqrt (a n) :=
      mul_le_mul_of_nonneg_right hDle hs
    _ = a n * L (a n) := by rw [mul_assoc, Real.mul_self_sqrt (hN.le.trans hn)]; ring


theorem berger_mul_slowlyVarying_atTop_real {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L) {a : ℝ → ℝ} (ha : Tendsto a atTop atTop) :
    Tendsto (fun x : ℝ => a x * L (a x)) atTop atTop := by
  obtain ⟨C, hC, N, hN, hcomp⟩ := sqrt_potter_comparison hpos hL hsv
  let D := L N * Real.sqrt N / C
  have hD : 0 < D := div_pos (mul_pos (hpos N hN) (Real.sqrt_pos.mpr hN)) hC
  have hmain : Tendsto (fun x : ℝ => D * Real.sqrt (a x)) atTop atTop := by
    simpa only [Function.comp_def, mul_comm] using
      (Real.tendsto_sqrt_atTop.comp ha).atTop_mul_const hD
  apply tendsto_atTop_mono' atTop _ hmain
  filter_upwards [ha.eventually_ge_atTop N] with n hn
  have h := hcomp N (a n) le_rfl hn
  have hDle : D ≤ L (a n) * Real.sqrt (a n) :=
    (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using h)
  have hs : 0 ≤ Real.sqrt (a n) := Real.sqrt_nonneg _
  calc
    D * Real.sqrt (a n) ≤ (L (a n) * Real.sqrt (a n)) * Real.sqrt (a n) :=
      mul_le_mul_of_nonneg_right hDle hs
    _ = a n * L (a n) := by rw [mul_assoc, Real.mul_self_sqrt (hN.le.trans hn)]; ring

/-- Real-cutoff form of the truncated second-moment bound. -/
theorem berger_second_moment_real_le
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ < 1)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2)) atTop (𝓝 1)) :
    ∃ D : ℝ, 0 < D ∧ ∃ A : ℝ, ∀ y : ℝ, A ≤ y →
      ∑ k ∈ Finset.range (⌊y⌋₊ + 2), (k : ℝ) ^ 2 * (μ {k}).toReal ≤ D * y * L y := by
  obtain ⟨D, M, hD⟩ := truncated_second_moment_le μ hm hpos hL hsv hlocal
  obtain ⟨P, hP, R, hR, hcomp⟩ := potter_bounds hpos hL hsv (1 / 2) (by norm_num)
  let A := max 2 (max R M)
  refine ⟨2 * (|D| + 1) * (P * Real.sqrt 2), by positivity, A, ?_⟩
  intro y hy
  have hy2 : 2 ≤ y := (le_max_left _ _).trans hy
  have hy0 : 0 < y := by linarith
  have hyR : R ≤ y := (le_max_left R M).trans ((le_max_right 2 _).trans hy)
  have hyM : (M : ℝ) ≤ y := (le_max_right R M).trans ((le_max_right 2 _).trans hy)
  let N := ⌊y⌋₊ + 1
  have hNy : (N : ℝ) ≤ y + 1 := by
    dsimp [N]; norm_num only [Nat.cast_add, Nat.cast_one]
    exact add_le_add (Nat.floor_le hy0.le) le_rfl
  have hN2 : (N : ℝ) ≤ 2 * y := by linarith
  have hyN : y ≤ (N : ℝ) := by
    have hh := Nat.lt_floor_add_one y
    dsimp [N]
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have hMN : M ≤ N := by
    have hMfloor : M ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast hyM)
    exact hMfloor.trans (Nat.le_succ _)
  have hc := (hcomp y (N : ℝ) hyR hyN).2
  have hLy : 0 < L y := hpos _ hy0
  have hLN : L N ≤ P * Real.sqrt 2 * L y := by
    have hh := (div_le_iff₀ hLy).mp hc
    rw [← Real.sqrt_eq_rpow, Real.sqrt_div (Nat.cast_nonneg N)] at hh
    have hsy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
    have hroot : Real.sqrt (N : ℝ) / Real.sqrt y ≤ Real.sqrt 2 :=
      (div_le_iff₀ hsy).mpr (by
        have hs := Real.sqrt_le_sqrt hN2
        have hsq : Real.sqrt (2 * y) = Real.sqrt 2 * Real.sqrt y :=
          Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) y
        rw [hsq] at hs
        exact hs)
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hroot hP.le) hLy.le)
  calc
    _ ≤ D * N * L N := hD N hMN
    _ ≤ (|D| + 1) * (2 * y) * (P * Real.sqrt 2 * L y) := by
      have hDnon : D ≤ |D| + 1 := by linarith [le_abs_self D, abs_nonneg D]
      have hfac : D * N ≤ (|D| + 1) * (2 * y) := by
        apply mul_le_mul hDnon hN2 (Nat.cast_nonneg _) (by positivity)
      have hLN0 : 0 ≤ L N := (hpos _ (hy0.trans_le hyN)).le
      calc
        D * N * L N ≤ ((|D| + 1) * (2 * y)) * L N :=
          mul_le_mul_of_nonneg_right hfac hLN0
        _ ≤ _ := mul_le_mul_of_nonneg_left hLN (by positivity)
    _ = (2 * (|D| + 1) * (P * Real.sqrt 2)) * y * L y := by ring

/-- The increment-tail difference on an annulus, bounded using Potter exponent `1/2`. -/
theorem berger_annular_tail_le
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ < 1)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2)) atTop (𝓝 1)) :
    ∃ C : ℝ, 0 < C ∧ ∃ A : ℝ, ∀ a y : ℝ, A ≤ a → a ≤ y →
      tailIncrementMean μ a - tailIncrementMean μ y ≤ C * L a * Real.sqrt (y / a) := by
  obtain ⟨P, hP, R, hR, hcomp⟩ := potter_bounds hpos hL hsv (1 / 2) (by norm_num)
  have htwo : (1 : ℝ) < 2 := by norm_num
  have hev : ∀ᶠ n : ℕ in atTop,
      (μ {n}).toReal / (L n / (n : ℝ) ^ 2) < 2 := (tendsto_order.1 hlocal).2 _ htwo
  obtain ⟨M, hM⟩ := eventually_atTop.1 hev
  let A := max 1 (max R M)
  refine ⟨4 * Real.sqrt 2 * P, by positivity, A, ?_⟩
  intro a y ha hay
  have ha1 : 1 ≤ a := (le_max_left _ _).trans ha
  have ha0 : 0 < a := zero_lt_one.trans_le ha1
  have haR : R ≤ a := (le_max_left R M).trans ((le_max_right 1 _).trans ha)
  have haM : (M : ℝ) ≤ a := (le_max_right R M).trans ((le_max_right 1 _).trans ha)
  have hy1 : 1 ≤ y := ha1.trans hay
  have hy0 : 0 < y := ha0.trans_le hay
  let Y := ⌊y⌋₊ + 2
  let X : ℕ → ℝ := offspringIncrement
  let f : ℕ → ℝ := fun k =>
    (if a < |X k| then X k else 0) - (if y < |X k| then X k else 0)
  have hfY : ∀ k : ℕ, Y ≤ k → f k = 0 := by
    intro k hk
    have hyk : ⌊y⌋₊ + 2 ≤ k := by exact_mod_cast hk
    have hyabs := (abs_increment_gt_iff_floor_add_two_le (k := k) hy1).mpr hyk
    dsimp [f, X]
    rw [ite_eq_left (hay.trans_lt hyabs), ite_eq_left hyabs, sub_self]
  have hfbound : ∀ k : ℕ, ‖f k‖ ≤ 2 * ((Y : ℝ) + 1) := by
    intro k
    by_cases hk : Y ≤ k
    · rw [hfY k hk, norm_zero]
      positivity
    · have hkY : (k : ℝ) ≤ Y := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hk))
      have hXabs : |X k| ≤ (Y : ℝ) + 1 := by
        dsimp [X, offspringIncrement]
        rcases k with _ | k
        · simp
        · simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
          rw [abs_of_nonneg (Nat.cast_nonneg k)]
          norm_num only [Nat.cast_add, Nat.cast_one] at hkY ⊢
          linarith
      have hpiece (r : ℝ) : ‖if r < |X k| then X k else 0‖ ≤ (Y : ℝ) + 1 := by
        split_ifs
        · simpa [Real.norm_eq_abs] using hXabs
        · simp; positivity
      dsimp [f]
      calc
        _ ≤ ‖if a < |X k| then X k else 0‖ + ‖if y < |X k| then X k else 0‖ := norm_sub_le _ _
        _ ≤ 2 * ((Y : ℝ) + 1) := by linarith [hpiece a, hpiece y]
  have hdecomp : tailIncrementMean μ a - tailIncrementMean μ y =
      ∑ k ∈ Finset.range Y, (μ {k}).toReal * f k := by
    unfold tailIncrementMean
    rw [← integral_sub (integrable_tailIncrement μ (ne_top_of_lt hm) a)
      (integrable_tailIncrement μ (ne_top_of_lt hm) y)]
    rw [integral_bounded_prefix (Y := Y) μ f (2 * ((Y : ℝ) + 1)) hfbound hfY]
  have hterm : ∀ k ∈ Finset.range Y, (μ {k}).toReal * f k ≤
      (2 * P * L a / Real.sqrt a) * (Real.sqrt (k : ℝ))⁻¹ := by
    intro k hk
    by_cases hf0 : f k = 0
    · have hLa : 0 < L a := hpos _ ha0
      have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
      rw [hf0, mul_zero]
      positivity
    · have haabs : a < |X k| := by
        by_contra hn
        simp [f, hn, not_lt.mpr ((le_of_not_gt hn).trans hay)] at hf0
      have hyabs : |X k| ≤ y := by
        by_contra hn
        have hy : y < |X k| := lt_of_not_ge hn
        have ha : a < |X k| := haabs
        simp [f, ha, hy] at hf0
      have hkX : X k = (k : ℝ) - 1 := by rfl
      have hkX0 : 0 ≤ X k := by
        have hk1 : 1 ≤ k := by
          by_contra hk0
          have : k = 0 := Nat.eq_zero_of_not_pos hk0
          subst k
          simp [X, offspringIncrement] at haabs
          linarith
        dsimp [X, offspringIncrement]
        exact sub_nonneg.mpr (by exact_mod_cast hk1)
      have haabs' : a < (k : ℝ) - 1 := by
        have h := haabs
        rw [abs_of_nonneg hkX0, hkX] at h
        exact h
      have hak : a ≤ (k : ℝ) := by linarith
      have hkM : M ≤ k := by
        have hlt : (M : ℝ) < (k : ℝ) := by linarith
        have hn : M < k := by exact_mod_cast hlt
        exact hn.le
      have hk0 : (0 : ℝ) < k := ha0.trans_le hak
      have hμ := (div_lt_iff₀ (div_pos (hpos _ hk0) (sq_pos_of_pos hk0))).mp (hM k hkM)
      have hmass : (k : ℝ) * (μ {k}).toReal ≤ 2 * L k / (k : ℝ) := by
        calc
          _ ≤ (k : ℝ) * (2 * (L k / (k : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_left hμ.le (Nat.cast_nonneg k)
          _ = _ := by field_simp [hk0.ne']
      have hfle : f k ≤ (k : ℝ) := by
        dsimp [f]
        split_ifs <;> dsimp [X, offspringIncrement] at * <;> nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      have hmassf : (μ {k}).toReal * f k ≤ 2 * L k / (k : ℝ) := by
        calc
          _ ≤ (μ {k}).toReal * (k : ℝ) :=
            mul_le_mul_of_nonneg_left hfle ENNReal.toReal_nonneg
          _ ≤ _ := by simpa only [mul_comm] using hmass
      have hc := (hcomp a (k : ℝ) haR hak).2
      have hLa := hpos _ ha0
      have hLk : L k ≤ P * (Real.sqrt k / Real.sqrt a) * L a := by
        have hh := (div_le_iff₀ hLa).mp hc
        rw [← Real.sqrt_eq_rpow, Real.sqrt_div (Nat.cast_nonneg k)] at hh
        convert hh using 1
      have hrecip : 2 * L k / (k : ℝ) ≤
          (2 * P * L a / Real.sqrt a) * (Real.sqrt (k : ℝ))⁻¹ := by
        have hsa := Real.sqrt_pos.mpr ha0
        have hsk := Real.sqrt_pos.mpr hk0
        calc
          _ ≤ 2 * (P * (Real.sqrt k / Real.sqrt a) * L a) / (k : ℝ) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hLk (by norm_num)) hk0.le
          _ = _ := by
            field_simp [hk0.ne', hsa.ne', hsk.ne']
            nlinarith [Real.sq_sqrt hk0.le]
      exact hmassf.trans hrecip
  rw [hdecomp]
  calc
    _ ≤ ∑ k ∈ Finset.range Y, (2 * P * L a / Real.sqrt a) * (Real.sqrt (k : ℝ))⁻¹ :=
      Finset.sum_le_sum hterm
    _ = (2 * P * L a / Real.sqrt a) * ∑ k ∈ Finset.range Y, (Real.sqrt (k : ℝ))⁻¹ := by
      rw [Finset.mul_sum]
    _ ≤ (2 * P * L a / Real.sqrt a) * (2 * Real.sqrt (2 * y)) := by
      have hLa : 0 < L a := hpos _ ha0
      have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
      have hs := sum_inv_sqrt_le (⌊y⌋₊ + 1)
      have hYY : ⌊y⌋₊ + 1 + 1 = Y := rfl
      rw [hYY] at hs
      apply mul_le_mul_of_nonneg_left _ (div_nonneg (by positivity) (Real.sqrt_nonneg _))
      calc
        _ ≤ 2 * Real.sqrt (⌊y⌋₊ + 1) := by simpa only [Nat.cast_add, Nat.cast_one] using hs
        _ ≤ 2 * Real.sqrt (2 * y) := by
          apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt _) (by norm_num)
          have hfloor : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy0.le
          linarith
    _ = (4 * Real.sqrt 2 * P) * L a * Real.sqrt (y / a) := by
      have hsa := Real.sqrt_pos.mpr ha0
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) y,
        Real.sqrt_div hy0.le a]
      field_simp
      ring

end SubcriticalCauchy.Bienayme
