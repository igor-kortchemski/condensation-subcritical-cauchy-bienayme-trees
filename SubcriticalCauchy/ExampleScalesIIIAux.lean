module

public import SubcriticalCauchy.ExampleScalesAux
public import SubcriticalCauchy.SlowVariationTail
public import SubcriticalCauchy.IncrementTailAsymptotics
public import SubcriticalCauchy.SlowVariationRounding
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Taylor

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


@[expose] public section

open Filter MeasureTheory
open scoped Topology BigOperators

namespace SubcriticalCauchy.Bienayme

noncomputable section

/-- The derivative (up to sign) of the explicit primitive in Example 2.3(iii). -/
noncomputable def expLogDerivativeModel (c β x : ℝ) : ℝ :=
  c * Real.exp (-(Real.log x) ^ β) / x *
    (1 - (1 - β) / β * (Real.log x) ^ (-β))

/-- The explicit tail primitive in Example 2.3(iii). -/
noncomputable def expLogPrimitive (c β x : ℝ) : ℝ :=
  c / β * (Real.log x) ^ (1 - β) * Real.exp (-(Real.log x) ^ β)

private theorem hasDerivAt_expLogPrimitive {c β x : ℝ}
    (hcβ : β ≠ 0) (hx : x ≠ 0) (hlogpos : 0 < Real.log x) :
    HasDerivAt (expLogPrimitive c β) (-expLogDerivativeModel c β x) x := by
  have hp : HasDerivAt (fun y : ℝ => Real.log y ^ (1 - β))
      ((1 - β) * Real.log x ^ (1 - β - 1) * x⁻¹) x := by
    convert (Real.hasDerivAt_log hx).rpow_const (Or.inl hlogpos.ne') using 1 ; ring
  have hq : HasDerivAt (fun y : ℝ => Real.exp (-(Real.log y) ^ β))
      (Real.exp (-(Real.log x) ^ β) *
        (-(β * Real.log x ^ (β - 1) * x⁻¹))) x := by
    convert ((Real.hasDerivAt_log hx).rpow_const (p := β) (Or.inl hlogpos.ne')).neg.exp using 1
    simp only [Pi.neg_apply]
    ring
  have h := (hp.const_mul (c / β)).mul hq
  unfold expLogPrimitive expLogDerivativeModel
  convert h using 1
  rw [show 1 - β - 1 = -β by ring]
  have hpow : Real.log x ^ (1 - β) * Real.log x ^ (β - 1) = 1 := by
    rw [← Real.rpow_add hlogpos]
    convert Real.rpow_zero (Real.log x) using 2
    ring
  field_simp [hx, hcβ]
  ring_nf
  have hpow' : Real.log x ^ (1 - β) * Real.log x ^ (-1 + β) = 1 := by
    convert hpow using 2 ; ring
  linear_combination (c * β) * hpow'


/-- The multiplicative correction between the elementary density and the
exact derivative of `expLogPrimitive`. -/
noncomputable def expLogCorrection (β x : ℝ) : ℝ :=
  1 - (1 - β) / β * (Real.log x) ^ (-β)

/-- The bracket controlling the sign of the derivative of the corrected density. -/
noncomputable def expLogSignBracket (β x : ℝ) : ℝ :=
  (β * (Real.log x) ^ (β - 1) + 1) * expLogCorrection β x -
    (1 - β) * (Real.log x) ^ (-β - 1)

private theorem tendsto_expLogCorrection {β : ℝ} (hβ : 0 < β) :
    Tendsto (expLogCorrection β) atTop (𝓝 1) := by
  have hp : Tendsto (fun x : ℝ => (Real.log x) ^ (-β)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hβ).comp Real.tendsto_log_atTop
  have h := tendsto_const_nhds (x := (1 : ℝ)) |>.sub (hp.const_mul ((1 - β) / β))
  unfold expLogCorrection
  simpa using h

private theorem tendsto_expLogSignBracket {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (expLogSignBracket β) atTop (𝓝 1) := by
  have hp : Tendsto (fun x : ℝ => (Real.log x) ^ (β - 1)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (show 0 < -(β - 1) by linarith)).comp
      Real.tendsto_log_atTop
    simpa only [neg_sub, Function.comp_def] using h
  have hq : Tendsto (fun x : ℝ => (Real.log x) ^ (-β - 1)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (show 0 < β + 1 by linarith)).comp
      Real.tendsto_log_atTop
    have he : -(β + 1) = -β - 1 := by ring
    rw [he] at h
    simpa only [Function.comp_def] using h
  have h := ((hp.const_mul β).add_const 1).mul (tendsto_expLogCorrection hβ0) |>.sub
    (hq.const_mul (1 - β))
  unfold expLogSignBracket
  simpa using h

private theorem hasDerivAt_expLogDerivativeModel {c β x : ℝ}
    (hβ : β ≠ 0) (hx : x ≠ 0) (hlogpos : 0 < Real.log x) :
    HasDerivAt (expLogDerivativeModel c β)
      (-(c * Real.exp (-(Real.log x) ^ β) / x ^ 2 * expLogSignBracket β x)) x := by
  have hp : HasDerivAt (fun y : ℝ => Real.log y ^ β)
      (β * Real.log x ^ (β - 1) * x⁻¹) x := by
    convert (Real.hasDerivAt_log hx).rpow_const (Or.inl hlogpos.ne') using 1 ; ring
  have hE : HasDerivAt (fun y : ℝ => Real.exp (-(Real.log y) ^ β))
      (Real.exp (-(Real.log x) ^ β) * (-(β * Real.log x ^ (β - 1) * x⁻¹))) x := by
    convert hp.neg.exp using 1
  have hb : HasDerivAt (fun y : ℝ => c * Real.exp (-(Real.log y) ^ β) / y)
      (c * (Real.exp (-(Real.log x) ^ β) * (-(β * Real.log x ^ (β - 1) * x⁻¹))) / x -
        c * Real.exp (-(Real.log x) ^ β) / x ^ 2) x := by
    convert (hE.const_mul c).div (hasDerivAt_id x) hx using 1
    · ext y
      rfl
    · simp only [id_eq]
      field_simp [hx]
  have hm : HasDerivAt (fun y : ℝ => Real.log y ^ (-β))
      ((-β) * Real.log x ^ (-β - 1) * x⁻¹) x := by
    convert (Real.hasDerivAt_log hx).rpow_const (Or.inl hlogpos.ne') using 1 ; ring
  have hg : HasDerivAt (expLogCorrection β)
      (-((1 - β) / β) * ((-β) * Real.log x ^ (-β - 1) * x⁻¹)) x := by
    change HasDerivAt (fun y : ℝ => 1 - (1 - β) / β * Real.log y ^ (-β))
      (-((1 - β) / β) * ((-β) * Real.log x ^ (-β - 1) * x⁻¹)) x
    convert (hm.const_mul ((1 - β) / β)).const_sub 1 using 1 ; ring
  have h := hb.mul hg
  change HasDerivAt ((fun y : ℝ => c * Real.exp (-(Real.log y) ^ β) / y) * expLogCorrection β)
    (-(c * Real.exp (-(Real.log x) ^ β) / x ^ 2 * expLogSignBracket β x)) x
  convert h using 1
  unfold expLogSignBracket expLogCorrection
  have hpow : Real.log x ^ (-1 + β) * Real.log x ^ (-β) =
      Real.log x ^ (-1 : ℝ) := by
    rw [← Real.rpow_add hlogpos (-1 + β) (-β)]
    ring_nf
  field_simp [hx, hβ]
  ring_nf

private theorem expLogCorrection_eq (c β x : ℝ) :
    expLogDerivativeModel c β x =
      (c * Real.exp (-(Real.log x) ^ β) / x) * expLogCorrection β x := by
  rfl

private theorem expLogPrimitive_pos {c β x : ℝ} (hc : 0 < c) (hβ : 0 < β)
    (hlog : 0 < Real.log x) : 0 < expLogPrimitive c β x := by
  unfold expLogPrimitive
  positivity

private theorem expLogDerivativeModel_pos {c β x : ℝ} (hc : 0 < c)
    (hx : 0 < x) (hcorr : 0 < expLogCorrection β x) :
    0 < expLogDerivativeModel c β x := by
  rw [expLogCorrection_eq]
  positivity

private theorem tendsto_expLogPrimitive {c β : ℝ} (_hc : 0 < c) (hβ0 : 0 < β)
    (hβ1 : β < 1) : Tendsto (expLogPrimitive c β) atTop (𝓝 0) := by
  have hu : Tendsto (fun x : ℝ => (Real.log x) ^ β) atTop atTop :=
    (tendsto_rpow_atTop hβ0).comp Real.tendsto_log_atTop
  have hzero := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((1 - β) / β) 1 one_pos).comp hu
  have hfinal : Tendsto (expLogPrimitive c β) atTop (𝓝 ((c / β) * 0)) := by
    apply (hzero.const_mul (c / β)).congr'
    filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 0] with x hx
    unfold expLogPrimitive
    dsimp only [Function.comp_def]
    rw [← Real.rpow_mul hx.le, show β * ((1 - β) / β) = 1 - β by field_simp [hβ0.ne']]
    simp only [one_mul, neg_mul]
    ring
  simpa using hfinal

private theorem tendsto_expLogDerivativeModel_div_primitive {c β : ℝ}
    (hc : 0 < c) (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun n : ℕ => expLogDerivativeModel c β n / expLogPrimitive c β n)
      atTop (𝓝 0) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp hnat
  have hpow : Tendsto (fun n : ℕ => (Real.log n) ^ (1 - β)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hβ1)).comp hlog
  have hden := hnat.atTop_mul_atTop₀ hpow
  have hbase : Tendsto (fun n : ℕ =>
      (c * Real.exp (-(Real.log n) ^ β) / n) / expLogPrimitive c β n) atTop (𝓝 0) := by
    have hfinal : Tendsto (fun n : ℕ =>
        (c * Real.exp (-(Real.log n) ^ β) / n) / expLogPrimitive c β n)
        atTop (𝓝 0) := by
      apply (hden.const_div_atTop β).congr'
      filter_upwards [hlog.eventually_gt_atTop 0, eventually_gt_atTop (0 : ℕ)] with n hn hnn
      have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hnn
      unfold expLogPrimitive
      field_simp [hc.ne', hβ0.ne', hn0.ne', (Real.rpow_pos_of_pos hn (1 - β)).ne',
        (Real.exp_pos _).ne']
    simpa using hfinal
  have hfinal := hbase.mul ((tendsto_expLogCorrection hβ0).comp hnat)
  have hfinal0 : Tendsto (fun n : ℕ =>
      (c * Real.exp (-(Real.log n) ^ β) / n) / expLogPrimitive c β n *
        expLogCorrection β n) atTop (𝓝 0) := by simpa using hfinal
  apply hfinal0.congr'
  filter_upwards with n
  rw [expLogCorrection_eq]
  ring

private theorem eventually_expLogDerivativeModel_large {c β : ℝ}
    (hc : 0 < c) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      AntitoneOn (expLogDerivativeModel c β) (Set.Ici (n : ℝ)) ∧
      (∀ x ∈ Set.Ici (n : ℝ),
        HasDerivAt (expLogPrimitive c β) (-expLogDerivativeModel c β x) x) ∧
      (∀ x ∈ Set.Ioi (n : ℝ), 0 ≤ expLogDerivativeModel c β x) ∧
      0 < expLogDerivativeModel c β n := by
  have hev : ∀ᶠ x : ℝ in atTop, 0 < x ∧ 0 < Real.log x ∧
      0 < expLogCorrection β x ∧ 0 < expLogSignBracket β x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ),
      Real.tendsto_log_atTop.eventually_gt_atTop 0,
      (tendsto_expLogCorrection hβ0).eventually (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
      (tendsto_expLogSignBracket hβ0 hβ1).eventually (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with x hx hl hc' hs
    exact ⟨hx, hl, hc', hs⟩
  obtain ⟨B, hB⟩ := eventually_atTop.mp hev
  refine ⟨Nat.ceil B, fun n hn => ?_⟩
  have hBn : B ≤ (n : ℝ) := (Nat.le_ceil B).trans (by exact_mod_cast hn)
  have hprops {x : ℝ} (hx : (n : ℝ) ≤ x) := hB x (hBn.trans hx)
  have hstrict (x : ℝ) (hx : x ∈ Set.Ici (n : ℝ)) :
      0 < c * Real.exp (-(Real.log x) ^ β) / x ^ 2 * expLogSignBracket β x := by
    have hh := hprops hx
    exact mul_pos (div_pos (mul_pos hc (Real.exp_pos _)) (sq_pos_of_pos hh.1)) hh.2.2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply antitoneOn_of_deriv_nonpos (convex_Ici (n : ℝ))
    · intro x hx
      exact (hasDerivAt_expLogDerivativeModel hβ0.ne' (hprops hx).1.ne' (hprops hx).2.1).continuousAt.continuousWithinAt
    · intro x hx
      have hxlt : (n : ℝ) < x := by simpa only [interior_Ici, Set.mem_Ioi] using hx
      have hx' : x ∈ Set.Ici (n : ℝ) := hxlt.le
      exact (hasDerivAt_expLogDerivativeModel hβ0.ne' (hprops hx').1.ne' (hprops hx').2.1).differentiableAt.differentiableWithinAt
    · intro x hx
      have hxlt : (n : ℝ) < x := by simpa only [interior_Ici, Set.mem_Ioi] using hx
      have hx' : x ∈ Set.Ici (n : ℝ) := hxlt.le
      rw [(hasDerivAt_expLogDerivativeModel hβ0.ne' (hprops hx').1.ne' (hprops hx').2.1).deriv]
      exact neg_nonpos.mpr (hstrict x hx').le
  · intro x hx
    exact hasDerivAt_expLogPrimitive hβ0.ne' (hprops hx).1.ne' (hprops hx).2.1
  · intro x hx
    have hx' : x ∈ Set.Ici (n : ℝ) := hx.le
    exact (expLogDerivativeModel_pos hc (hprops hx').1 (hprops hx').2.2.1).le
  · exact expLogDerivativeModel_pos hc (hprops le_rfl).1 (hprops le_rfl).2.2.1


open Asymptotics

private theorem isBigO_one_add_rpow_sub_linear {β : ℝ} :
    (fun x : ℝ => (1 + x) ^ β - (1 + β * x)) =O[𝓝[Set.Ioi (-1 : ℝ)] 0]
      (fun x => x ^ 2) := by
  let s : Set ℝ := Set.Ioi (-1)
  let f : ℝ → ℝ := fun x => (1 + x) ^ β
  have hf : ContDiffOn ℝ 2 f s := by
    apply ContDiffOn.rpow_const_of_ne (contDiffOn_const.add contDiffOn_id)
    intro x hx
    have hx' : (-1 : ℝ) < x := hx
    dsimp
    linarith
  have h0 : (0 : ℝ) ∈ s := by simp [s]
  have hfa : ContDiffAt ℝ 2 f 0 := hf.contDiffAt (IsOpen.mem_nhds isOpen_Ioi h0)
  have hu : UniqueDiffOn ℝ s := isOpen_Ioi.uniqueDiffOn
  have hd (x : ℝ) (hx : 1 + x ≠ 0) :
      HasDerivAt f (β * (1 + x) ^ (β - 1)) x := by
    convert ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)).rpow_const
      (Or.inl hx) using 1
    · rfl
    · simp only [Pi.add_apply, id_eq]
      ring
  have hdf : deriv f =ᶠ[𝓝 (0 : ℝ)] fun x : ℝ => β * (1 + x) ^ (β - 1) := by
    filter_upwards [eventually_gt_nhds (show (-1 : ℝ) < 0 by norm_num)] with x hx
    exact (hd x (by linarith)).deriv
  have hi1 : iteratedDerivWithin 1 f s 0 = β := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (hfa.of_le (by norm_num)) h0]
    rw [show (1 : ℕ) = 0 + 1 by omega, iteratedDeriv_succ, iteratedDeriv_zero]
    exact (hd 0 (by norm_num)).deriv.trans (by norm_num)
  have hi2 : iteratedDerivWithin 2 f s 0 = β * (β - 1) := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu hfa h0]
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
    rw [hdf.deriv_eq]
    have hd2 : HasDerivAt (fun x : ℝ => β * (1 + x) ^ (β - 1))
        (β * ((β - 1) * (1 + 0) ^ (β - 1 - 1))) (0 : ℝ) := by
      convert (((hasDerivAt_const (0 : ℝ) (1 : ℝ)).add (hasDerivAt_id 0)).rpow_const
        (p := β - 1) (Or.inl (by norm_num))).const_mul β using 1
      · ext x
        simp only [Pi.add_apply, id_eq]
      · simp only [Pi.add_apply, id_eq]
        ring
    rw [hd2.deriv]
    norm_num
  have ht := taylor_isLittleO (convex_Ioi (-1 : ℝ)) h0 hf
  have heq : (fun x : ℝ => f x - taylorWithinEval f 2 s 0 x) =
      (fun x : ℝ => (1 + x) ^ β - (1 + β * x + β * (β - 1) / 2 * x ^ 2)) := by
    funext x
    simp only [taylor_within_apply, Nat.cast_ofNat, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add, Nat.factorial_zero, Nat.cast_one, inv_one,
      Nat.factorial_one, Nat.factorial_two, pow_zero, pow_one, hi1, hi2,
      smul_eq_mul, iteratedDerivWithin_zero]
    dsimp [f]
    norm_num
    ring
  simp only [sub_zero] at ht
  rw [heq] at ht
  have hq : (fun x : ℝ => β * (β - 1) / 2 * x ^ 2) =O[𝓝[s] 0]
      (fun x => x ^ 2) :=
    (isBigO_refl (fun x : ℝ => x ^ 2) (𝓝[s] 0)).const_mul_left (β * (β - 1) / 2)
  have hs := ht.isBigO.add hq
  exact hs.congr' (by filter_upwards with x; ring) EventuallyEq.rfl

/-- Second-order perturbation of a real power, with a multiplicatively small
relative perturbation. -/
theorem isBigO_rpow_sub_rpow_sub_linear {ι : Type*} {l : Filter ι}
    {A v : ι → ℝ} (β : ℝ) (hA : ∀ᶠ i in l, 0 < A i) (hv : ∀ᶠ i in l, 0 < v i)
    (hratio : Tendsto (fun i => A i / v i) l (𝓝 1)) :
    (fun i => A i ^ β - v i ^ β - β * v i ^ (β - 1) * (A i - v i)) =O[l]
      (fun i => v i ^ (β - 2) * (A i - v i) ^ 2) := by
  let x : ι → ℝ := fun i => A i / v i - 1
  have hx : Tendsto x l (𝓝 0) := by
    have h := hratio.sub_const 1
    simpa [x] using h
  have hx' : Tendsto x l (𝓝[Set.Ioi (-1 : ℝ)] 0) := by
    apply tendsto_nhdsWithin_iff.mpr ⟨hx, ?_⟩
    filter_upwards [hratio.eventually (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with i hi
    dsimp [x]
    change -1 < A i / v i - 1
    linarith
  have hrem := (isBigO_one_add_rpow_sub_linear (β := β)).comp_tendsto hx'
  have hscaled := (isBigO_refl (fun i => v i ^ β) l).mul hrem
  apply hscaled.congr' _ _
  · filter_upwards [hA, hv] with i hAi hvi
    dsimp [x]
    have hvβ : 0 < v i ^ β := Real.rpow_pos_of_pos hvi β
    have hi : 1 + (A i / v i - 1) = A i / v i := by ring
    rw [hi, Real.div_rpow hAi.le hvi.le]
    rw [show β = (β - 1) + 1 by ring, Real.rpow_add hvi, Real.rpow_one]
    field_simp [hvi.ne', hvβ.ne']
    ring
  · filter_upwards [hv] with i hvi
    dsimp [x]
    rw [Real.rpow_sub hvi, Real.rpow_two]
    field_simp [hvi.ne', (Real.rpow_pos_of_pos hvi (2 : ℝ)).ne',
      (Real.rpow_pos_of_pos hvi β).ne']
    




private theorem expLog_floor_le_nat {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    (hsub : Tendsto (fun n : ℕ => a n / (n : ℝ)) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop, ((Nat.floor (a n) : ℕ) : ℝ) ≤ (n : ℝ) := by
  filter_upwards [ha.eventually_ge_atTop 0,
    hsub.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop (0 : ℕ)] with n ha0 hr hn
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have han : a n ≤ (n : ℝ) := by
    have hh := (div_lt_iff₀ hnR).mp hr
    linarith
  exact (Nat.floor_le ha0).trans han

/-- The logarithmic scale ratio for Example 2.3(iii). -/
theorem expLog_scaling_log_ratio (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ < 1) {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hmeas : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1)) {c β : ℝ} (hc : 0 < c)
    (hβ0 : 0 < β) (hβ1 : β < 1)
    (hL : Tendsto (fun n : ℕ => L n / (c * Real.exp (-(Real.log n) ^ β)))
      atTop (𝓝 1)) {a : ℕ → ℝ}
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => Real.log (a n) / Real.log n) atTop (𝓝 1) := by
  have hlit : IsSubcriticalCauchyOffspring μ := ⟨hm, L, hpos, hsv, hlocal⟩
  have hat := scaling_tendsto_atTop μ hlit ha
  have hsub := scaling_div_nat_tendsto_zero μ hlit ha
  have hscale := scaling_div_mul_tendsto_one μ hm hpos hmeas hsv hlocal ha
  have hle := expLog_floor_le_nat hat hsub
  have hfloorNat : Tendsto (fun n : ℕ => Nat.floor (a n)) atTop atTop :=
    tendsto_nat_floor_atTop.comp hat
  have hfloorReal : Tendsto (fun n : ℕ => ((Nat.floor (a n) : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hfloorNat
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlognat : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp hnat
  have hlogfloor : Tendsto (fun n : ℕ => Real.log (Nat.floor (a n))) atTop atTop :=
    Real.tendsto_log_atTop.comp hfloorReal
  have hlogModelRatio := (hL.comp hfloorNat).log one_ne_zero |>.div_atTop hlognat
  have hconst : Tendsto (fun _n : ℕ => Real.log c / Real.log (_n : ℕ)) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := Real.log c)).div_atTop hlognat
  have hupper : Tendsto (fun n : ℕ => (Real.log n) ^ (β - 1)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (show 0 < 1 - β by linarith)).comp hlognat
    have he : -(1 - β) = β - 1 := by ring
    rw [he] at h
    simpa only [Function.comp_def] using h
  have hpowDiv : Tendsto (fun n : ℕ =>
      (Real.log (Nat.floor (a n))) ^ β / Real.log n) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    · filter_upwards [hlogfloor.eventually_ge_atTop 0, hlognat.eventually_gt_atTop 0]
        with n hm hn
      exact div_nonneg (Real.rpow_nonneg hm _) hn.le
    · filter_upwards [hle, hlogfloor.eventually_gt_atTop 0,
        hlognat.eventually_gt_atTop 0] with n hmn hm hn
      have hm0 : 0 < ((Nat.floor (a n) : ℕ) : ℝ) := by
        by_contra h
        have hzero : ((Nat.floor (a n) : ℕ) : ℝ) = 0 :=
          le_antisymm (le_of_not_gt h) (Nat.cast_nonneg _)
        simp [hzero] at hm
      have hleR : ((Nat.floor (a n) : ℕ) : ℝ) ≤ n := by exact_mod_cast hmn
      have hlogle := Real.log_le_log hm0 hleR
      have hp := Real.rpow_le_rpow hm.le hlogle hβ0.le
      rw [Real.rpow_sub (by positivity), Real.rpow_one]
      exact div_le_div_of_nonneg_right hp hn.le
  have hmodelLog : Tendsto (fun n : ℕ =>
      Real.log (c * Real.exp (-(Real.log (Nat.floor (a n))) ^ β)) / Real.log n)
      atTop (𝓝 0) := by
    have h := hconst.sub hpowDiv
    have hfinal : Tendsto (fun n : ℕ =>
        Real.log (c * Real.exp (-(Real.log (Nat.floor (a n))) ^ β)) / Real.log n)
        atTop (𝓝 (0 - 0)) := by
      apply h.congr'
      filter_upwards [hlognat.eventually_gt_atTop 0] with n hn
      rw [Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp]
      ring
    simpa using hfinal
  have hfloorLog : Tendsto (fun n : ℕ => Real.log (L (Nat.floor (a n))) / Real.log n)
      atTop (𝓝 0) := by
    have h := hlogModelRatio.add hmodelLog
    have hfinal : Tendsto (fun n : ℕ => Real.log (L (Nat.floor (a n))) / Real.log n)
        atTop (𝓝 (0 + 0)) := by
      apply h.congr'
      filter_upwards [hfloorReal.eventually_gt_atTop 0,
        hlognat.eventually_gt_atTop 0] with n hm hn
      have hLpos : 0 < L (Nat.floor (a n)) := hpos _ hm
      have hMpos : 0 < c * Real.exp (-(Real.log (Nat.floor (a n))) ^ β) :=
        mul_pos hc (Real.exp_pos _)
      dsimp only [Function.comp_def]
      rw [Real.log_div hLpos.ne' hMpos.ne']
      ring
    simpa using hfinal
  have hlogL : Tendsto (fun n : ℕ => Real.log (L (a n)) / Real.log n) atTop (𝓝 0) := by
    have hratio : Tendsto (fun n : ℕ => L (a n) / L (Nat.floor (a n))) atTop (𝓝 1) := by
      simpa only [Pi.inv_apply, inv_div, inv_one, Function.comp_def] using
        ((localModel_floor_div_tendsto_one hpos hmeas hsv).inv₀ one_ne_zero).comp hat
    have hzero := (hratio.log one_ne_zero).div_atTop hlognat
    have h := hzero.add hfloorLog
    have hfinal : Tendsto (fun n : ℕ => Real.log (L (a n)) / Real.log n)
        atTop (𝓝 (0 + 0)) := by
      apply h.congr'
      filter_upwards [hat.eventually_gt_atTop 0, hfloorReal.eventually_gt_atTop 0]
        with n han hmn
      rw [Real.log_div (hpos _ han).ne' (hpos _ hmn).ne']
      ring
    simpa using hfinal
  have hlogR : Tendsto (fun n : ℕ => Real.log (a n / ((n : ℝ) * L (a n))))
      atTop (𝓝 0) := by simpa using hscale.log one_ne_zero
  have hzero := hlogR.div_atTop hlognat
  have h := (tendsto_const_nhds (x := (1 : ℝ))).add (hzero.add hlogL)
  have hfinal : Tendsto (fun n : ℕ => Real.log (a n) / Real.log n)
      atTop (𝓝 (1 + (0 + 0))) := by
    apply h.congr'
    filter_upwards [hat.eventually_gt_atTop 0, hlognat.eventually_gt_atTop 0,
      eventually_gt_atTop (0 : ℕ)] with n han hlogn hn
    have hLa : 0 < L (a n) := hpos _ han
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    rw [Real.log_div han.ne' (mul_ne_zero hnR.ne' hLa.ne'),
      Real.log_mul hnR.ne' hLa.ne']
    field_simp [hlogn.ne']
    ring
  simpa using hfinal

/-- Transport of the natural-index exponential model to an arbitrary real
sequence tending to infinity, in logarithmic form with a `o(1)` error. -/
theorem tendsto_log_expLog_model {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hmeas : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L) {c β : ℝ} (hc : 0 < c)
    (hβ0 : 0 < β) (hβ1 : β < 1)
    (hL : Tendsto (fun n : ℕ => L n / (c * Real.exp (-(Real.log n) ^ β)))
      atTop (𝓝 1)) {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) :
    Tendsto (fun n : ℕ => Real.log (L (a n)) - Real.log c + (Real.log (a n)) ^ β)
      atTop (𝓝 0) := by
  have hfloorNat : Tendsto (fun n : ℕ => Nat.floor (a n)) atTop atTop :=
    tendsto_nat_floor_atTop.comp ha
  have hfloorReal : Tendsto (fun n : ℕ => ((Nat.floor (a n) : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hfloorNat
  have hloga : Tendsto (fun n : ℕ => Real.log (a n)) atTop atTop :=
    Real.tendsto_log_atTop.comp ha
  have hlogfloor : Tendsto (fun n : ℕ => Real.log (Nat.floor (a n))) atTop atTop :=
    Real.tendsto_log_atTop.comp hfloorReal
  have hd : Tendsto (fun n : ℕ => Real.log (Nat.floor (a n)) - Real.log (a n))
      atTop (𝓝 0) := by
    have h := (tendsto_nat_floor_div_atTop.comp ha).log one_ne_zero
    have h0 : Tendsto (fun n : ℕ => Real.log (Nat.floor (a n) / a n)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, Real.log_one] using h
    apply h0.congr'
    filter_upwards [ha.eventually_gt_atTop 0, hfloorReal.eventually_gt_atTop 0] with n han hmn
    have hm0 : 0 < ((Nat.floor (a n) : ℕ) : ℝ) := hmn
    rw [Real.log_div hm0.ne' han.ne']
  have hlinear : Tendsto (fun n : ℕ =>
      β * (Real.log (a n)) ^ (β - 1) *
        (Real.log (Nat.floor (a n)) - Real.log (a n))) atTop (𝓝 0) := by
    have hp : Tendsto (fun n : ℕ => (Real.log (a n)) ^ (β - 1)) atTop (𝓝 0) := by
      have h := (tendsto_rpow_neg_atTop (show 0 < 1 - β by linarith)).comp hloga
      have he : -(1 - β) = β - 1 := by ring
      rw [he] at h
      simpa only [Function.comp_def] using h
    have h := (hp.const_mul β).mul hd
    simpa using h
  have hrem : Tendsto (fun n : ℕ =>
      (Real.log (Nat.floor (a n))) ^ β - (Real.log (a n)) ^ β -
        β * (Real.log (a n)) ^ (β - 1) *
          (Real.log (Nat.floor (a n)) - Real.log (a n))) atTop (𝓝 0) := by
    apply (isBigO_rpow_sub_rpow_sub_linear β
      (hlogfloor.eventually_gt_atTop 0) (hloga.eventually_gt_atTop 0)
      (by
        have hzero := hd.div_atTop hloga
        have h := (tendsto_const_nhds (x := (1 : ℝ))).add hzero
        have h1 : Tendsto (fun n : ℕ => 1 +
          (Real.log (Nat.floor (a n)) - Real.log (a n)) / Real.log (a n))
          atTop (𝓝 1) := by simpa using h
        apply h1.congr'
        filter_upwards [hloga.eventually_gt_atTop 0] with n hn
        field_simp [hn.ne']
        ring)).trans_tendsto
    have hp : Tendsto (fun n : ℕ => (Real.log (a n)) ^ (β - 2)) atTop (𝓝 0) := by
      have h := (tendsto_rpow_neg_atTop (show 0 < 2 - β by linarith)).comp hloga
      have he : -(2 - β) = β - 2 := by ring
      rw [he] at h
      simpa only [Function.comp_def] using h
    have hd2 : Tendsto (fun n : ℕ =>
        (Real.log (Nat.floor (a n)) - Real.log (a n)) ^ 2) atTop (𝓝 0) := by
      simpa using hd.pow 2
    have h := hp.mul hd2
    simpa using h
  have hpowdiff : Tendsto (fun n : ℕ =>
      (Real.log (a n)) ^ β - (Real.log (Nat.floor (a n))) ^ β) atTop (𝓝 0) := by
    have h := (hrem.add hlinear).neg
    have hfinal : Tendsto (fun n : ℕ =>
        (Real.log (a n)) ^ β - (Real.log (Nat.floor (a n))) ^ β)
        atTop (𝓝 (-(0 + 0))) := by
      apply h.congr'
      filter_upwards with n
      ring
    simpa using hfinal
  have hfloorModel : Tendsto (fun n : ℕ =>
      Real.log (L (Nat.floor (a n))) - Real.log c +
        (Real.log (Nat.floor (a n))) ^ β) atTop (𝓝 0) := by
    have h := (hL.comp hfloorNat).log one_ne_zero
    have h0 : Tendsto (fun n : ℕ => Real.log (L (Nat.floor (a n)) /
      (c * Real.exp (-(Real.log (Nat.floor (a n))) ^ β)))) atTop (𝓝 0) := by
      simpa using h
    apply h0.congr'
    filter_upwards [hfloorReal.eventually_gt_atTop 0, hlogfloor.eventually_gt_atTop 0]
      with n hm hmlog
    have hLpos : 0 < L (Nat.floor (a n)) := hpos _ hm
    have hMpos : 0 < c * Real.exp (-(Real.log (Nat.floor (a n))) ^ β) :=
      mul_pos hc (Real.exp_pos _)
    rw [Real.log_div hLpos.ne' hMpos.ne', Real.log_mul hc.ne' (Real.exp_pos _).ne',
      Real.log_exp]
    ring
  have hround : Tendsto (fun n : ℕ =>
      Real.log (L (a n)) - Real.log (L (Nat.floor (a n)))) atTop (𝓝 0) := by
    have hratio : Tendsto (fun n : ℕ => L (a n) / L (Nat.floor (a n))) atTop (𝓝 1) := by
      simpa only [Pi.inv_apply, inv_div, inv_one, Function.comp_def] using
        ((localModel_floor_div_tendsto_one hpos hmeas hsv).inv₀ one_ne_zero).comp ha
    have h := hratio.log one_ne_zero
    have h0 : Tendsto (fun n : ℕ => Real.log (L (a n) / L (Nat.floor (a n))))
      atTop (𝓝 0) := by simpa using h
    apply h0.congr'
    filter_upwards [ha.eventually_gt_atTop 0, hfloorReal.eventually_gt_atTop 0] with n han hmn
    rw [Real.log_div (hpos _ han).ne' (hpos _ hmn).ne']
  have h := (hround.add hfloorModel).add hpowdiff
  have hfinal : Tendsto (fun n : ℕ => Real.log (L (a n)) - Real.log c +
      (Real.log (a n)) ^ β) atTop (𝓝 ((0 + 0) + 0)) := by
    apply h.congr'
    filter_upwards with n
    ring
  simpa using hfinal

/-- Integrated-tail asymptotics for the exponential-logarithmic model. -/
theorem expLog_ellStar_tendsto {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x) {c β : ℝ} (hc : 0 < c)
    (hβ0 : 0 < β) (hβ1 : β < 1)
    (hL : Tendsto (fun n : ℕ => L n / (c * Real.exp (-(Real.log n) ^ β)))
      atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => ellStar L n / expLogPrimitive c β n) atTop (𝓝 1) := by
  obtain ⟨N, hN⟩ := eventually_expLogDerivativeModel_large hc hβ0 hβ1
  let T : ℝ → ℝ := fun x => if x < (N : ℝ) then 1 else expLogDerivativeModel c β x
  let V : ℕ → ℝ := fun n => L n / (n : ℝ)
  let F : ℝ → ℝ := expLogPrimitive c β
  have hT0 (n : ℕ) : 0 ≤ T n := by
    by_cases hn : (n : ℝ) < (N : ℝ)
    · simp [T, hn]
    · have hnN : N ≤ n := by exact_mod_cast (le_of_not_gt hn)
      simp only [T, hn, ↓reduceIte]
      exact (hN n hnN).2.2.2.le
  have hTpos (n : ℕ) (hn : 1 ≤ n) : 0 < T n := by
    by_cases hnN : (n : ℝ) < (N : ℝ)
    · simp [T, hnN]
    · have hnN' : N ≤ n := by exact_mod_cast (le_of_not_gt hnN)
      simp only [T, hnN, ↓reduceIte]
      exact (hN n hnN').2.2.2
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp hnat
  have hbase : Tendsto (fun n : ℕ => V n /
      (c * Real.exp (-(Real.log n) ^ β) / n)) atTop (𝓝 1) := by
    apply hL.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    simp only [V]
    field_simp [hn0.ne']
  have hinv : Tendsto (fun n : ℕ =>
      (c * Real.exp (-(Real.log n) ^ β) / n) / T n) atTop (𝓝 1) := by
    have hc' := ((tendsto_expLogCorrection hβ0).inv₀ one_ne_zero).comp hnat
    have hfinal : Tendsto (fun n : ℕ =>
        (c * Real.exp (-(Real.log n) ^ β) / n) / T n) atTop (𝓝 (1⁻¹)) := by
      apply hc'.congr'
      filter_upwards [eventually_ge_atTop N, hlog.eventually_gt_atTop 0,
        eventually_gt_atTop (0 : ℕ)] with n hn hln hnn
      have hnR : N ≤ (n : ℝ) := by exact_mod_cast hn
      have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hnn
      simp only [T, show ¬(n : ℝ) < (N : ℝ) by linarith, ↓reduceIte,
        Function.comp_def, expLogCorrection_eq]
      field_simp [(Real.exp_pos _).ne', hn0.ne', hc.ne',
        (hN n hn).2.2.2.ne']
    simpa using hfinal
  have hratio : Tendsto (fun n : ℕ => V n / T n) atTop (𝓝 1) := by
    have h := hbase.mul hinv
    have hfinal : Tendsto (fun n : ℕ => V n / T n) atTop (𝓝 (1 * 1)) := by
      apply h.congr'
      filter_upwards [eventually_ge_atTop N, eventually_gt_atTop (0 : ℕ)] with n hn hnn
      have hnR : N ≤ (n : ℝ) := by exact_mod_cast hn
      have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hnn
      have hT := hTpos n hnn
      have hb : 0 < c * Real.exp (-(Real.log n) ^ β) / n := div_pos (mul_pos hc (Real.exp_pos _)) hn0
      field_simp [hT.ne', hb.ne']
    simpa using hfinal
  have hsumT : Summable (fun n : ℕ => T n) := by
    obtain ⟨hanti, hderiv, hnonneg, hposN⟩ := hN N le_rfl
    apply summable_nat_of_antitone_primitive (f := T) (F := F) (N := N)
      (tendsto_expLogPrimitive hc hβ0 hβ1)
    · apply hanti.congr
      intro x hx
      have hxN : (N : ℝ) ≤ x := hx
      simp only [T, not_lt_of_ge hxN, ↓reduceIte]
    · intro x hx
      have hxN : (N : ℝ) ≤ x := hx
      simp only [F]
      convert hderiv x hx using 1
      simp [T, show ¬x < (N : ℝ) by linarith]
    · intro x hx
      have hxN : (N : ℝ) ≤ x := hx
      rw [show T x = expLogDerivativeModel c β x by simp [T, not_lt_of_ge hxN]]
      rcases hx.eq_or_lt with rfl | hx
      · exact hposN.le
      · exact hnonneg x hx
  have hsumV : Summable V := by
    apply (hsumT.mul_left 2).of_norm_bounded_eventually_nat
    filter_upwards [hratio.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 2)),
      eventually_ge_atTop (1 : ℕ)] with n hr hn
    rw [Real.norm_eq_abs, abs_of_nonneg (localModel_over_nat_nonneg hpos n)]
    have hlt := (div_lt_iff₀ (hTpos n hn)).mp hr
    dsimp only [V, T] at hlt ⊢
    linarith
  have htail : Tendsto (fun n : ℕ => tailMass (fun k : ℕ => T k) n / F n) atTop (𝓝 1) := by
    apply tailMass_div_tendsto_one_of_primitive (f := T) (F := F)
      (tendsto_expLogPrimitive hc hβ0 hβ1)
    · apply (tendsto_expLogDerivativeModel_div_primitive hc hβ0 hβ1).congr'
      filter_upwards [eventually_ge_atTop N] with n hn
      have hnR : N ≤ (n : ℝ) := by exact_mod_cast hn
      simp [T, F, show ¬(n : ℝ) < (N : ℝ) by linarith]
    · filter_upwards [hlog.eventually_gt_atTop 0] with n hn
      exact expLogPrimitive_pos hc hβ0 hn
    · filter_upwards [eventually_ge_atTop N] with n hn
      obtain ⟨hanti, hderiv, hnonneg, hposn⟩ := hN n hn
      have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
      have hTx {x : ℝ} (hx : (n : ℝ) ≤ x) : T x = expLogDerivativeModel c β x := by
        simp [T, show ¬x < (N : ℝ) by linarith]
      refine ⟨?_, ?_, ?_⟩
      · exact hanti.congr (fun x hx => (hTx hx).symm)
      · intro x hx
        simp only [F]
        convert hderiv x hx using 1
        rw [hTx hx]
      · intro x hx
        rw [hTx hx.le]
        exact hnonneg x hx
  have hcompare : Tendsto (fun n : ℕ => ellStar L n / tailMass (fun k : ℕ => T k) n)
      atTop (𝓝 1) := by
    simpa only [ellStar, V] using tailMass_div_tendsto_one hsumT hsumV hT0 hTpos hratio
  have hprod := hcompare.mul htail
  have hfinal : Tendsto (fun n : ℕ => ellStar L n / F n) atTop (𝓝 (1 * 1)) := by
    apply hprod.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have ht := (tailMass_pos hsumT hT0 hTpos hn).ne'
    change ellStar L n / tailMass (fun k : ℕ => T k) n *
      (tailMass (fun k : ℕ => T k) n / F n) = _
    by_cases hden : F n = 0
    · simp [hden]
    · field_simp [ht, hden]
  simpa only [F, one_mul] using hfinal

end
end SubcriticalCauchy.Bienayme
