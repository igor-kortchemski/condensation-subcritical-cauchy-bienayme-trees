module

public import SubcriticalCauchy.TruncatedExponentialAux
public import Mathlib.MeasureTheory.Integral.Pi

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-!
# Truncated exponential bound

Exponential Markov on finite products, with the one-coordinate estimates from
`TruncatedExponentialAux`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology ENNReal BigOperators

namespace SubcriticalCauchy.Bienayme

/-- The one-coordinate moment-generating estimate, with an integer cutoff. -/
theorem truncated_mgf_le
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ < 1)
    (Y : ℕ) (t : ℝ) (ht : 0 ≤ t) (B : ℝ)
    (hYB : ∀ k : ℕ, k < Y → (k : ℝ) ≤ B) (hmY : (offspringMean μ).toReal ≤ Y) :
    (∫ k : ℕ, (if k < Y then Real.exp (t * ((k : ℝ) - (offspringMean μ).toReal)) else 0) ∂μ) ≤
      1 + t ^ 2 * Real.exp (t * B) *
        ((∑ k ∈ Finset.range Y, (k : ℝ) ^ 2 * (μ {k}).toReal) +
          (offspringMean μ).toReal ^ 2) := by
  let m := (offspringMean μ).toReal
  let F : ℕ → ℝ := fun k => if k < Y then Real.exp (t * ((k : ℝ) - m)) else 0
  let X : ℕ → ℝ := fun k => if k < Y then (k : ℝ) - m else 0
  let Q : ℕ → ℝ := fun k => if k < Y then ((k : ℝ) - m) ^ 2 else 0
  let E := Real.exp (t * B)
  have hm0 : 0 ≤ m := by
    change 0 ≤ (offspringMean μ).toReal
    rw [offspringMean_eq_tsum]
    exact tsum_nonneg (fun k => mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg k))
  have hF : Integrable F μ := by
    refine Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable E ?_
    filter_upwards [] with k
    by_cases hk : k < Y
    · simp only [F, hk, ite_true, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have hkY : (k : ℝ) ≤ B := hYB k hk
      have harg : t * ((k : ℝ) - m) ≤ t * B :=
        mul_le_mul_of_nonneg_left (by linarith) ht
      exact harg
    · simp [F, hk, E, (Real.exp_pos _).le]
  have hX : Integrable X μ := by
    refine Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable
      ((Y : ℝ) + |m|) ?_
    filter_upwards [] with k
    by_cases hk : k < Y
    · simp only [X, hk, ite_true, Real.norm_eq_abs]
      calc
        |(k : ℝ) - m| ≤ |(k : ℝ)| + |m| := abs_sub _ _
        _ ≤ (Y : ℝ) + |m| := add_le_add (by
          rw [abs_of_nonneg (Nat.cast_nonneg k)]
          exact_mod_cast hk.le) le_rfl
    · simp [X, hk, add_nonneg (Nat.cast_nonneg Y) (abs_nonneg m)]
  have hQ : Integrable Q μ := by
    refine Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable
      ((Y : ℝ) ^ 2 + m ^ 2) ?_
    filter_upwards [] with k
    by_cases hk : k < Y
    · simp only [Q, hk, ite_true, Real.norm_eq_abs, abs_pow, sq_abs]
      have hkY : (k : ℝ) ≤ Y := by exact_mod_cast hk.le
      nlinarith [sq_nonneg ((k : ℝ) - m), sq_nonneg ((k : ℝ) + m),
        (Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
    · simp [Q, hk, add_nonneg (sq_nonneg (Y : ℝ)) (sq_nonneg m)]
  have hpoint (k : ℕ) : F k ≤ 1 + t * X k + (t ^ 2 * E) * Q k := by
    by_cases hk : k < Y
    · simp only [F, X, Q, hk, ite_true]
      have htay := exp_le_one_add_add_sq_mul_exp_max (t * ((k : ℝ) - m))
      have hkY : (k : ℝ) ≤ B := hYB k hk
      have hB : 0 ≤ B := (Nat.cast_nonneg k).trans (hYB k hk)
      have htY : 0 ≤ t * B := mul_nonneg ht hB
      have harg : t * ((k : ℝ) - m) ≤ t * B :=
        mul_le_mul_of_nonneg_left (by linarith) ht
      have hmax : Real.exp (max (t * ((k : ℝ) - m)) 0) ≤ E := by
        apply Real.exp_le_exp.mpr
        exact max_le harg htY
      calc
        Real.exp (t * ((k : ℝ) - m)) ≤
            1 + t * ((k : ℝ) - m) + (t * ((k : ℝ) - m)) ^ 2 *
              Real.exp (max (t * ((k : ℝ) - m)) 0) := htay
        _ ≤ 1 + t * ((k : ℝ) - m) + (t * ((k : ℝ) - m)) ^ 2 * E :=
          add_le_add_right (mul_le_mul_of_nonneg_left hmax (sq_nonneg _)) _
        _ = 1 + t * ((k : ℝ) - m) + (t ^ 2 * E) * ((k : ℝ) - m) ^ 2 := by ring
    · simp [F, X, Q, hk]
  have hG : Integrable (fun k => 1 + t * X k + (t ^ 2 * E) * Q k) μ :=
    ((integrable_const 1).add (hX.const_mul t)).add (hQ.const_mul (t ^ 2 * E))
  calc
    (∫ k, F k ∂μ) ≤ ∫ k, (1 + t * X k + (t ^ 2 * E) * Q k) ∂μ :=
      integral_mono hF hG hpoint
    _ = 1 + t * (∫ k, X k ∂μ) + (t ^ 2 * E) * (∫ k, Q k ∂μ) := by
      have hlinint : ∫ k, (1 + t * X k) ∂μ = 1 + t * ∫ k, X k ∂μ := by
        rw [integral_add (integrable_const 1) (hX.const_mul t), integral_const_mul,
          integral_const]
        simp
      have hadd : (∫ k, (1 + t * X k + (t ^ 2 * E) * Q k) ∂μ) =
          (∫ k, (1 + t * X k) ∂μ) + ∫ k, ((t ^ 2 * E) * Q k) ∂μ :=
        integral_add ((integrable_const 1).add (hX.const_mul t)) (hQ.const_mul (t ^ 2 * E))
      rw [hadd, hlinint, integral_const_mul]
    _ ≤ 1 + (t ^ 2 * E) *
        ((∑ k ∈ Finset.range Y, (k : ℝ) ^ 2 * (μ {k}).toReal) + m ^ 2) := by
      have hlin : (∫ k, X k ∂μ) ≤ 0 := integral_truncated_center_nonpos μ hm Y hmY
      have hq := integral_truncated_center_sq_le μ Y
      have hcoef : 0 ≤ t ^ 2 * E := mul_nonneg (sq_nonneg t) (Real.exp_pos _).le
      have htlin : t * (∫ k, X k ∂μ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht hlin
      have hquad := mul_le_mul_of_nonneg_left hq hcoef
      nlinarith
    _ = _ := by rfl


/-- The second moment below `c * n`, after comparison with the value at `n`. -/
theorem truncated_second_moment_cutoff
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ < 1)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2)) atTop (𝓝 1))
    {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      ∑ k ∈ Finset.range (⌊c * n⌋₊ + 1), (k : ℝ) ^ 2 * (μ {k}).toReal ≤
        K * n * L n := by
  obtain ⟨D, M, hD⟩ := truncated_second_moment_le μ hm hpos hL hsv hlocal
  obtain ⟨P, hP, R, hR, hcomp⟩ := potter_bounds hpos hL hsv 1 one_pos
  let K := (|D| + 1) * c * (P * max c (2 / c))
  refine ⟨K, mul_pos (mul_pos (by positivity) hc)
    (mul_pos hP (lt_max_of_lt_right (div_pos (by norm_num) hc))), ?_⟩
  have hyTop : Tendsto (fun n : ℕ => ⌊c * (n : ℝ)⌋₊) atTop atTop := by
    simpa only [Function.comp_def, id_eq, mul_comm] using tendsto_nat_floor_atTop.comp
      ((tendsto_id.atTop_mul_const hc).comp tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_ge_atTop M, (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (eventually_ge_atTop R), hyTop.eventually (eventually_ge_atTop ⌈R⌉₊),
    hyTop.eventually (eventually_ge_atTop M), hyTop.eventually (eventually_ge_atTop 1), eventually_ge_atTop 1,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (2 / c))]
    with n hnM hnR hyRnat hyM hy1 hn1 hn2
  let y := ⌊c * (n : ℝ)⌋₊
  have hyR : R ≤ (y : ℝ) :=
    (Nat.le_ceil R).trans (by exact_mod_cast hyRnat)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hy0 : (0 : ℝ) < y := by exact_mod_cast hy1
  have hcy : 0 ≤ c * (n : ℝ) := (mul_pos hc hn0).le
  have hy_le : (y : ℝ) ≤ c * n := Nat.floor_le hcy
  have hyn0 : 0 < (y : ℝ) / n := div_pos hy0 hn0
  have hLn : 0 < L n := hpos _ hn0
  have hLy : 0 < L y := hpos _ hy0
  have hKn : 0 < max c (2 / c) := lt_max_of_lt_right (div_pos (by norm_num) hc)
  have hLcompare : L y ≤ P * max c (2 / c) * L n := by
    rcases le_total (n : ℝ) y with hny | hyn
    · have h := (hcomp n y hnR hny).2
      simp only [Real.rpow_one] at h
      have h1 : L y ≤ P * ((y : ℝ) / n) * L n := (div_le_iff₀ hLn).mp h
      have h2 : P * ((y : ℝ) / n) ≤ P * max c (2 / c) := by
        apply mul_le_mul_of_nonneg_left _ hP.le
        exact (div_le_iff₀ hn0).mpr (hy_le.trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) hn0.le))
      have h3 : P * max c (2 / c) * L n ≤ P * max c (2 / c) * L n := le_rfl
      calc
        L y ≤ P * ((y : ℝ) / n) * L n := h1
        _ ≤ P * max c (2 / c) * L n := mul_le_mul_of_nonneg_right h2 hLn.le
    · have h := (hcomp y n hyR hyn).1
      simp only [Real.rpow_neg_one] at h
      have hh := (le_div_iff₀ hLy).mp h
      have hhP := mul_le_mul_of_nonneg_left hh hP.le
      simp only [inv_div] at hhP
      have hleft : P * (P⁻¹ * ((y : ℝ) / n) * L y) = ((y : ℝ) / n) * L y := by
        field_simp
      rw [hleft] at hhP
      have hfinal : L y ≤ P * ((n : ℝ) / y) * L n := by
        calc
          L y ≤ (P * L n) / ((y : ℝ) / n) := (le_div_iff₀ hyn0).mpr (by simpa [mul_comm] using hhP)
          _ = P * ((n : ℝ) / y) * L n := by field_simp
      have hyb : c * n - 1 < y := by
        have := Nat.lt_floor_add_one (c * (n : ℝ))
        linarith
      have hcn : 2 ≤ c * n := by
        have hn_ge := (div_le_iff₀ hc).mp hn2
        nlinarith
      have hyb' : (c / 2) * n ≤ y := by nlinarith
      have hnybound : (n : ℝ) / y ≤ 2 / c := by
        apply (div_le_div_iff₀ hy0 hc).mpr
        nlinarith
      calc
        L y ≤ P * ((n : ℝ) / y) * L n := hfinal
        _ ≤ (P * max c (2 / c)) * L n := by
          apply mul_le_mul_of_nonneg_right _ hLn.le
          exact mul_le_mul_of_nonneg_left (hnybound.trans (le_max_right _ _)) hP.le
  have hy_nonneg : 0 ≤ (y : ℝ) := hy0.le
  calc
    _ ≤ D * y * L y := hD y hyM
    _ ≤ (|D| + 1) * y * L y := by
      have hyprod : 0 ≤ (y : ℝ) * L y := mul_nonneg hy_nonneg hLy.le
      nlinarith [le_abs_self D, abs_nonneg D]
    _ ≤ (|D| + 1) * (c * n) * (P * max c (2 / c) * L n) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hy_le (by positivity : 0 ≤ |D| + 1)) hLcompare
        hLy.le (mul_nonneg (by positivity : 0 ≤ |D| + 1) hcy)
    _ = K * n * L n := by dsimp [K]; ring

lemma exp_log_inv_half {x : ℝ} (hx : 0 < x) :
    Real.exp (Real.log (1 / x) / 2) = x ^ (-(1 / 2) : ℝ) := by
  rw [Real.rpow_def_of_pos hx, one_div, Real.log_inv]
  congr 1
  simp only [one_div]
  ring

lemma exp_log_inv_scaled {x b c n : ℝ} (hx : 0 < x) (hc : c ≠ 0) (hn : n ≠ 0) :
    Real.exp (Real.log (1 / x) / (2 * c * n) * b) = x ^ (-b / (2 * c * n)) := by
  rw [Real.rpow_def_of_pos hx, one_div, Real.log_inv]
  congr 1
  field_simp

/-- A uniform power estimate used after the one-coordinate MGF bound. -/
lemma pow_le_exp_one_of_le {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 ≤ ε)
    {j n : ℕ} (hjn : j ≤ n) (hnε : n * ε ≤ 1) (hbound : A ≤ 1 + ε) :
    A ^ j ≤ Real.exp 1 := by
  calc
    A ^ j ≤ (1 + ε) ^ j := pow_le_pow_left₀ hA hbound j
    _ ≤ (Real.exp ε) ^ j := pow_le_pow_left₀ (by linarith)
      (by simpa [add_comm] using Real.add_one_le_exp ε) j
    _ = Real.exp (j * ε) := by rw [← Real.exp_nat_mul]
    _ ≤ Real.exp (n * ε) := Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hjn) hε)
    _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hnε


/-- Exponential Markov for the centred sum on a finite product. -/
theorem pi_truncated_probability_le
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (Y j n : ℕ) (t a : ℝ) (ht : 0 ≤ t) :
    ((Measure.pi fun _ : Fin j => μ)
      {ω | a * n ≤ (∑ i, (ω i : ℝ)) - (offspringMean μ).toReal * j ∧
           ∀ i, ω i < Y}).toReal ≤
      Real.exp (-t * a * n) *
        (∫ k : ℕ, (if k < Y then
          Real.exp (t * ((k : ℝ) - (offspringMean μ).toReal)) else 0) ∂μ) ^ j := by
  let m := (offspringMean μ).toReal
  let f : ℕ → ℝ := fun k => if k < Y then Real.exp (t * ((k : ℝ) - m)) else 0
  let F : (Fin j → ℕ) → ℝ := fun ω => ∏ i, f (ω i)
  let E : Set (Fin j → ℕ) :=
    {ω | a * n ≤ (∑ i, (ω i : ℝ)) - m * j ∧ ∀ i, ω i < Y}
  let A := ∫ k, f k ∂μ
  have hf : Integrable f μ := by
    refine Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable
      (Real.exp (t * ((Y : ℝ) + |m|))) ?_
    filter_upwards [] with k
    by_cases hk : k < Y
    · simp only [f, hk, ite_true, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ ht
      have hkY : (k : ℝ) ≤ Y := by exact_mod_cast hk.le
      have hm : -m ≤ |m| := neg_le_abs m
      linarith
    · simp [f, hk, (Real.exp_pos _).le]
  have hF : Integrable F (Measure.pi fun _ : Fin j => μ) := by
    exact Integrable.fin_nat_prod (fun _ => hf)
  have hFnonneg : 0 ≤ᵐ[Measure.pi fun _ : Fin j => μ] F :=
    ae_of_all _ (fun _ => Finset.prod_nonneg (fun _ _ => by
      dsimp [f]
      split_ifs <;> positivity))
  have hFexp (ω : Fin j → ℕ) (hωY : ∀ i, ω i < Y) :
      F ω = Real.exp (t * ((∑ i, (ω i : ℝ)) - m * j)) := by
    dsimp [F, f]
    simp_rw [hωY, ite_true, ← Real.exp_sum]
    congr 1
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum]
    ring
  have hsubset : E ⊆ {ω | Real.exp (t * a * n) ≤ F ω} := by
    intro ω hω
    change Real.exp (t * a * n) ≤ F ω
    dsimp [E] at hω
    rw [hFexp ω hω.2]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hω.1 ht
    convert h using 1 ; ring
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := Measure.pi fun _ : Fin j => μ) hFnonneg hF (Real.exp (t * a * n))
  have hint : ∫ ω, F ω ∂(Measure.pi fun _ : Fin j => μ) = A ^ j := by
    dsimp [F, A]
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      (integral_fin_nat_prod_eq_prod (μ := fun _ : Fin j => μ) (fun _ => f))
  rw [hint] at hmarkov
  change ((Measure.pi fun _ : Fin j => μ) E).toReal ≤ _
  calc
    ((Measure.pi fun _ : Fin j => μ) E).toReal =
        Real.exp (-t * a * n) * (Real.exp (t * a * n) *
          ((Measure.pi fun _ : Fin j => μ) E).toReal) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    _ ≤ Real.exp (-t * a * n) *
        (Real.exp (t * a * n) * ((Measure.pi fun _ : Fin j => μ).real
          {ω | Real.exp (t * a * n) ≤ F ω})) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact measureReal_mono hsubset
    _ ≤ Real.exp (-t * a * n) * A ^ j :=
      mul_le_mul_of_nonneg_left hmarkov (Real.exp_pos _).le
    _ = _ := by rfl


/-- Potter's lower bound implies `n L(n) → ∞`. -/
theorem natCast_mul_tendsto_atTop_of_potter
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L) :
    Tendsto (fun n : ℕ => (n : ℝ) * L n) atTop atTop := by
  obtain ⟨P, hP, R, hR, hcomp⟩ := potter_bounds hpos hL hsv (1 / 2) (by norm_num)
  let N := max ⌈R⌉₊ 1
  have hNR : R ≤ (N : ℝ) :=
    (Nat.le_ceil R).trans (Nat.cast_le.mpr (le_max_left _ _))
  have hN0 : (0 : ℝ) < N := by
    have : 1 ≤ N := le_max_right _ _
    exact_mod_cast (Nat.zero_lt_of_lt this)
  let D := P⁻¹ * L N * Real.sqrt N
  have hD : 0 < D := mul_pos (mul_pos (inv_pos.mpr hP) (hpos _ hN0)) (Real.sqrt_pos.mpr hN0)
  have hmain : Tendsto (fun n : ℕ => D * Real.sqrt n) atTop atTop := by
    have hh := (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).atTop_mul_const hD
    simpa only [Function.comp_def, mul_comm] using hh
  apply tendsto_atTop_mono' atTop _ hmain
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn0 : (0 : ℝ) < n := hN0.trans_le (by exact_mod_cast hn)
  have hRn : R ≤ (n : ℝ) := hNR.trans (by exact_mod_cast hn)
  have h := (hcomp N n hNR (by exact_mod_cast hn)).1
  have hLn : 0 < L n := hpos _ hn0
  have hLN : 0 < L N := hpos _ hN0
  have hnN : (0 : ℝ) < (n : ℝ) / N := div_pos hn0 hN0
  have hroot : ((n : ℝ) / N) ^ (-(1 / 2) : ℝ) = (Real.sqrt ((n : ℝ) / N))⁻¹ := by
    rw [Real.rpow_neg hnN.le, ← Real.sqrt_eq_rpow]
  rw [hroot] at h
  have hbound : P⁻¹ * L N * (Real.sqrt ((n : ℝ) / N))⁻¹ ≤ L n := by
    convert (le_div_iff₀ hLN).mp h using 1 ; ring
  have hnroot : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hmul := mul_le_mul_of_nonneg_left hbound hn0.le
  have hid : (n : ℝ) * (P⁻¹ * L N * (Real.sqrt ((n : ℝ) / N))⁻¹) =
      D * Real.sqrt n := by
    rw [Real.sqrt_div hn0.le]
    dsimp [D]
    have hNroot : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr hN0).ne'
    have hnroot' : Real.sqrt n ≠ 0 := hnroot.ne'
    field_simp
    rw [Real.sq_sqrt hn0.le]
  have hlow : D * Real.sqrt n ≤ (n : ℝ) * L n := by
    rw [← hid]
    exact hmul
  exact hlow


/-- The truncated exponential estimate from the subcritical Cauchy local model. -/
theorem truncated_exponential_bound
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ < 1)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2)) atTop (𝓝 1))
    (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, j ≤ n →
      ((Measure.pi fun _ : Fin j => μ)
        {ω | a * n ≤ (∑ i, (ω i : ℝ)) - (offspringMean μ).toReal * j ∧
             ∀ i, (ω i : ℝ) ≤ c * n}).toReal
        ≤ Real.exp 1 * L n ^ (a / (2 * c)) := by
  obtain ⟨K, hK, hsecond⟩ := truncated_second_moment_cutoff μ hm hpos hL hsv hlocal hc
  let m := (offspringMean μ).toReal
  let t : ℕ → ℝ := fun n => Real.log (1 / L n) / (2 * c * n)
  let Y : ℕ → ℕ := fun n => ⌊c * (n : ℝ)⌋₊ + 1
  let ε : ℕ → ℝ := fun n => (t n) ^ 2 * Real.exp (t n * c * n) *
    (K * (n * L n) + m ^ 2)
  let δ : ℕ → ℝ := fun n => 1 / (4 * c ^ 2) *
    Real.log (1 / L n) ^ 2 * Real.sqrt (L n) * (K + m ^ 2 / (n * L n))
  have hL0 : Tendsto (fun n : ℕ => L n) atTop (𝓝 0) :=
    localModel_tendsto_zero μ hm hpos hL hsv hlocal
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (L n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hL0
  have hfourth : Tendsto (fun n : ℕ => Real.sqrt (Real.sqrt (L n))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hsqrt
  have hmulLog : Tendsto (fun n : ℕ => Real.sqrt (Real.sqrt (L n)) *
      Real.log (Real.sqrt (Real.sqrt (L n)))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_mul] using
      (Real.continuous_mul_log.tendsto 0).comp hfourth
  have hlogprod : Tendsto (fun n : ℕ => Real.log (1 / L n) ^ 2 * Real.sqrt (L n))
      atTop (𝓝 0) := by
    have hh := (hmulLog.mul hmulLog).const_mul 16
    simp only [mul_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hx : 0 < L n := hpos _ hn0
    have hlog : Real.log (1 / L n) = -4 * Real.log (Real.sqrt (Real.sqrt (L n))) := by
      rw [one_div, Real.log_inv, Real.log_sqrt (Real.sqrt_nonneg _),
        Real.log_sqrt hx.le]
      ring
    rw [hlog]
    calc
      16 * (Real.sqrt (Real.sqrt (L n)) * Real.log (Real.sqrt (Real.sqrt (L n))) *
          (Real.sqrt (Real.sqrt (L n)) * Real.log (Real.sqrt (Real.sqrt (L n))))) =
          16 * (Real.sqrt (Real.sqrt (L n)) ^ 2 *
            Real.log (Real.sqrt (Real.sqrt (L n))) ^ 2) := by ring
      _ = (-4 * Real.log (Real.sqrt (Real.sqrt (L n)))) ^ 2 * Real.sqrt (L n) := by
        rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
        ring
  have hnL : Tendsto (fun n : ℕ => (n : ℝ) * L n) atTop atTop :=
    natCast_mul_tendsto_atTop_of_potter hpos hL hsv
  have hfactor : Tendsto (fun n : ℕ => K + m ^ 2 / (n * L n)) atTop (𝓝 K) := by
    have hh : Tendsto (fun n : ℕ => m ^ 2 / ((n : ℝ) * L n)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hnL
    simpa using tendsto_const_nhds.add hh
  have hδ : Tendsto δ atTop (𝓝 0) := by
    have hh := (hlogprod.mul hfactor).const_mul (1 / (4 * c ^ 2))
    simpa [δ, mul_assoc] using hh
  have hyTop : Tendsto (fun n : ℕ => ⌊c * (n : ℝ)⌋₊) atTop atTop := by
    simpa only [Function.comp_def, id_eq, mul_comm] using tendsto_nat_floor_atTop.comp
      ((tendsto_id.atTop_mul_const hc).comp tendsto_natCast_atTop_atTop)
  obtain ⟨M, hM⟩ := exists_nat_ge m
  filter_upwards [hsecond, hL0.eventually (gt_mem_nhds zero_lt_one),
    hδ.eventually (Iio_mem_nhds zero_lt_one),
    hyTop.eventually (eventually_ge_atTop M), eventually_ge_atTop 1]
    with n hnsecond hLn1 hδ1 hyM hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hLn : 0 < L n := hpos _ hn0
  have hcy : 0 ≤ c * (n : ℝ) := (mul_pos hc hn0).le
  have hmY : m ≤ Y n := by
    apply hM.trans
    exact_mod_cast hyM.trans (Nat.le_succ _)
  have hlogpos : 0 < Real.log (1 / L n) := by
    apply Real.log_pos
    exact one_lt_one_div hLn hLn1
  have ht : 0 < t n := div_pos hlogpos (mul_pos (mul_pos (by norm_num) hc) hn0)
  have hy_le : ((Y n : ℕ) : ℝ) ≤ c * n + 1 := by
    dsimp [Y]
    have hh : ((⌊c * (n : ℝ)⌋₊ : ℕ) : ℝ) ≤ c * n := Nat.floor_le hcy
    push_cast
    linarith
  have hexpct : Real.exp (t n * c * n) = L n ^ (-(1 / 2) : ℝ) := by
    have harg : t n * c * n = Real.log (1 / L n) / 2 := by
      dsimp [t]
      field_simp
    rw [harg, exp_log_inv_half hLn]
  have hε : 0 ≤ ε n := by
    dsimp [ε]
    positivity
  have hδeq : (n : ℝ) * ε n = δ n := by
    have hroot : L n ^ (-(1 / 2) : ℝ) = (Real.sqrt (L n))⁻¹ := by
      rw [Real.rpow_neg hLn.le, ← Real.sqrt_eq_rpow]
    have hLroot : L n * (Real.sqrt (L n))⁻¹ = Real.sqrt (L n) := by
      calc
        L n * (Real.sqrt (L n))⁻¹ = Real.sqrt (L n) ^ 2 * (Real.sqrt (L n))⁻¹ := by
          rw [Real.sq_sqrt hLn.le]
        _ = Real.sqrt (L n) := by
          have hs : Real.sqrt (L n) ≠ 0 := (Real.sqrt_pos.mpr hLn).ne'
          field_simp
    calc
      (n : ℝ) * ε n = 1 / (4 * c ^ 2) * Real.log (1 / L n) ^ 2 *
          (L n * (Real.sqrt (L n))⁻¹) * (K + m ^ 2 / (n * L n)) := by
        dsimp [ε, t]
        rw [hexpct, hroot]
        set z := (Real.sqrt (L n))⁻¹
        field_simp
        ring
      _ = δ n := by rw [hLroot]
  intro j hjn
  let A := ∫ k : ℕ, (if k < Y n then Real.exp (t n * ((k : ℝ) - m)) else 0) ∂μ
  have hA0 : 0 ≤ A := by
    apply integral_nonneg
    intro k
    dsimp [A]
    split_ifs <;> positivity
  have hcutReal : ∀ k : ℕ, k < Y n → (k : ℝ) ≤ c * n := by
    intro k hk
    have hk' : k ≤ ⌊c * (n : ℝ)⌋₊ := by dsimp [Y] at hk; omega
    have hh : ((⌊c * (n : ℝ)⌋₊ : ℕ) : ℝ) ≤ c * n := Nat.floor_le hcy
    have hkR : (k : ℝ) ≤ (⌊c * (n : ℝ)⌋₊ : ℕ) := by exact_mod_cast hk'
    exact hkR.trans hh
  change (∑ k ∈ Finset.range (Y n), (k : ℝ) ^ 2 * (μ {k}).toReal) ≤ K * n * L n at hnsecond
  have hmgf : A ≤ 1 + (t n) ^ 2 * Real.exp (t n * c * n) *
      ((∑ k ∈ Finset.range (Y n), (k : ℝ) ^ 2 * (μ {k}).toReal) + m ^ 2) :=
by simpa only [m, mul_assoc] using
      truncated_mgf_le μ hm (Y n) (t n) ht.le (c * n) hcutReal hmY
  have hAbound : A ≤ 1 + ε n := by
    calc
      A ≤ 1 + (t n) ^ 2 * Real.exp (t n * c * n) *
        ((∑ k ∈ Finset.range (Y n), (k : ℝ) ^ 2 * (μ {k}).toReal) + m ^ 2) := hmgf
      _ ≤ 1 + ε n := by
        dsimp [ε]
        apply add_le_add_right
        calc
          (t n) ^ 2 * Real.exp (t n * c * n) *
              ((∑ k ∈ Finset.range (Y n), (k : ℝ) ^ 2 * (μ {k}).toReal) + m ^ 2) ≤
              (t n) ^ 2 * Real.exp (t n * c * n) * (K * (n * L n) + m ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            convert add_le_add_left hnsecond (m ^ 2) using 1 ; ring
          _ = _ := by ring
  have hnε : (n : ℝ) * ε n ≤ 1 := by
    rw [hδeq]
    exact hδ1.le
  have hApow : A ^ j ≤ Real.exp 1 := pow_le_exp_one_of_le hA0 hε hjn hnε hAbound
  have hcut (k : ℕ) : k < Y n ↔ (k : ℝ) ≤ c * n := by
    constructor
    · intro hk
      have hk' : k ≤ ⌊c * (n : ℝ)⌋₊ := by dsimp [Y] at hk; omega
      have hh : ((⌊c * (n : ℝ)⌋₊ : ℕ) : ℝ) ≤ c * n := Nat.floor_le hcy
      have hkR : (k : ℝ) ≤ (⌊c * (n : ℝ)⌋₊ : ℕ) := by exact_mod_cast hk'
      exact hkR.trans hh
    · intro hk
      have hk' : k ≤ ⌊c * (n : ℝ)⌋₊ := Nat.le_floor hk
      dsimp [Y]
      omega
  have hmarkov := pi_truncated_probability_le μ (Y n) j n (t n) a ht.le
  have hEvent : {ω : Fin j → ℕ | a * n ≤ (∑ i, (ω i : ℝ)) - m * j ∧
      ∀ i, (ω i : ℝ) ≤ c * n} =
      {ω | a * n ≤ (∑ i, (ω i : ℝ)) - m * j ∧ ∀ i, ω i < Y n} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    exact and_congr_right (fun _ => forall_congr' (fun i => (hcut (ω i)).symm))
  change ((Measure.pi fun _ : Fin j => μ) _).toReal ≤ _
  rw [hEvent]
  calc
    _ ≤ Real.exp (-t n * a * n) * A ^ j := hmarkov
    _ ≤ Real.exp (-t n * a * n) * Real.exp 1 :=
      mul_le_mul_of_nonneg_left hApow (Real.exp_pos _).le
    _ = Real.exp 1 * L n ^ (a / (2 * c)) := by
      have he := exp_log_inv_scaled (x := L n) (b := -a * n) (c := c) (n := n)
        hLn hc.ne' hn0.ne'
      rw [show -t n * a * n = t n * (-a * n) by ring, he]
      have hq : -(-a * n) / (2 * c * n) = a / (2 * c) := by
        field_simp
      rw [hq, mul_comm]

end SubcriticalCauchy.Bienayme
