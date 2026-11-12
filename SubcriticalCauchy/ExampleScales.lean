module

public import SubcriticalCauchy.ExampleScalesAux
public import SubcriticalCauchy.IncrementTailAsymptotics
public import SubcriticalCauchy.SlowVariationRounding
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Example 2.3: explicit integrated tails and scaling sequences
-/


@[expose] public section

open Filter MeasureTheory
open scoped Topology BigOperators

namespace SubcriticalCauchy.Bienayme

noncomputable section

private noncomputable def logPowerModel (c β x : ℝ) : ℝ :=
  if x < 3 then 1 else c / (x * (Real.log x) ^ (1 + β))

private noncomputable def logPowerPrimitive (c β x : ℝ) : ℝ :=
  c / (β * (Real.log x) ^ β)

/-- Example 2.3(i): the integrated tail for a logarithmic power. -/
theorem example23_i_ellStar {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x) {c β : ℝ} (hc : 0 < c) (hβ : 0 < β)
    (hL : Tendsto (fun n : ℕ => L n / (c / (Real.log n) ^ (1 + β)))
      atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => ellStar L n / (c / (β * (Real.log n) ^ β)))
      atTop (𝓝 1) := by
  let T : ℕ → ℝ := fun n => logPowerModel c β n
  let V : ℕ → ℝ := fun n => L n / (n : ℝ)
  let F : ℝ → ℝ := logPowerPrimitive c β
  have hT0 (n : ℕ) : 0 ≤ T n := by
    by_cases hn : n < 3
    · simp [T, logPowerModel, hn]
    · have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
      have hn0 : 0 < (n : ℝ) := by linarith
      have hlog : 0 < Real.log n := Real.log_pos (by linarith)
      simp [T, logPowerModel]
      positivity
  have hTpos (n : ℕ) (hn : 1 ≤ n) : 0 < T n := by
    by_cases hn3 : n < 3
    · simp [T, logPowerModel, hn3]
    · have hn3' : (3 : ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
      have hn0 : 0 < (n : ℝ) := by linarith
      have hlog : 0 < Real.log n := Real.log_pos (by linarith)
      simp [T, logPowerModel]
      positivity
  have hratio : Tendsto (fun n : ℕ => V n / T n) atTop (𝓝 1) := by
    apply hL.congr'
    filter_upwards [eventually_gt_atTop (2 : ℕ)] with n hn
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
    have hn0 : 0 < (n : ℝ) := by linarith
    have hlog : 0 < Real.log n := Real.log_pos (by linarith)
    simp only [V, T, logPowerModel, show ¬(n : ℝ) < 3 by linarith, ↓reduceIte]
    field_simp [hc.ne', hn0.ne', hlog.ne']
  have hF : Tendsto F atTop (𝓝 0) := by
    have hpow : Tendsto (fun x : ℝ => (Real.log x) ^ β) atTop atTop :=
      (tendsto_rpow_atTop hβ).comp Real.tendsto_log_atTop
    have hden : Tendsto (fun x : ℝ => β * (Real.log x) ^ β) atTop atTop :=
      hpow.const_mul_atTop hβ
    change Tendsto (fun x : ℝ => c / (β * (Real.log x) ^ β)) atTop (𝓝 0)
    exact hden.const_div_atTop c
  have hFpos : ∀ᶠ n : ℕ in atTop, 0 < F n := by
    filter_upwards [eventually_gt_atTop (2 : ℕ)] with n hn
    have hnR : (2 : ℝ) < n := by exact_mod_cast hn
    have hlog : 0 < Real.log n := Real.log_pos (by linarith)
    simp only [F, logPowerPrimitive]
    positivity
  have hlarge : ∀ᶠ n : ℕ in atTop,
      AntitoneOn (logPowerModel c β) (Set.Ici (n : ℝ)) ∧
      (∀ x ∈ Set.Ici (n : ℝ),
        HasDerivAt (logPowerPrimitive c β) (-logPowerModel c β x) x) ∧
      (∀ x ∈ Set.Ioi (n : ℝ), 0 ≤ logPowerModel c β x) := by
    filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hx3 {x : ℝ} (hx : x ∈ Set.Ici (n : ℝ)) : (3 : ℝ) ≤ x := hnR.trans hx
    have hx0 {x : ℝ} (hx : x ∈ Set.Ici (n : ℝ)) : 0 < x := by linarith [hx3 hx]
    have hxlog {x : ℝ} (hx : x ∈ Set.Ici (n : ℝ)) : 0 < Real.log x :=
      Real.log_pos (by linarith [hx3 hx])
    have hmodel (x : ℝ) (hx : x ∈ Set.Ici (n : ℝ)) :
        logPowerModel c β x = c / (x * (Real.log x) ^ (1 + β)) := by
      simp [logPowerModel, show ¬x < 3 by linarith [hx3 hx]]
    refine ⟨?_, ?_, ?_⟩
    · intro x hx y hy hxy
      rw [hmodel x hx, hmodel y hy]
      have hlogxy : Real.log x ≤ Real.log y := Real.log_le_log (hx0 hx) hxy
      have hpowxy : (Real.log x) ^ (1 + β) ≤ (Real.log y) ^ (1 + β) :=
        Real.rpow_le_rpow (hxlog hx).le hlogxy (by linarith)
      have hdenx : 0 < x * (Real.log x) ^ (1 + β) :=
        mul_pos (hx0 hx) (Real.rpow_pos_of_pos (hxlog hx) _)
      apply div_le_div_of_nonneg_left hc.le hdenx
      exact mul_le_mul hxy hpowxy (Real.rpow_nonneg (hxlog hx).le _) (hx0 hy).le
    · intro x hx
      have hxne := (hx0 hx).ne'
      have hlogne := (hxlog hx).ne'
      have hpowpos : 0 < (Real.log x) ^ β := Real.rpow_pos_of_pos (hxlog hx) β
      have hd := (hasDerivAt_const x c).div
        (((Real.hasDerivAt_log hxne).rpow_const
          (p := β) (Or.inl hlogne)).const_mul β)
        (mul_ne_zero hβ.ne' hpowpos.ne')
      change HasDerivAt (fun x : ℝ => c / (β * (Real.log x) ^ β))
        (-logPowerModel c β x) x
      convert hd using 1
      rw [hmodel x hx, Real.rpow_add (hxlog hx), Real.rpow_sub (hxlog hx)]
      simp only [Real.rpow_one, zero_mul, zero_sub]
      field_simp [hc.ne', hβ.ne', hxne, hlogne, hpowpos.ne']
    · intro x hx
      have hxci : x ∈ Set.Ici (n : ℝ) := hx.le
      rw [hmodel x hxci]
      exact (div_pos hc (mul_pos (hx0 hxci) (Real.rpow_pos_of_pos (hxlog hxci) _))).le
  obtain ⟨N, hN⟩ := eventually_atTop.mp hlarge
  have hsumT : Summable T := by
    obtain ⟨hanti, hderiv, hnonneg⟩ := hN N le_rfl
    apply summable_nat_of_antitone_primitive hF hanti hderiv
    intro x hx
    rcases hx.eq_or_lt with rfl | hx
    · have hm := hanti (Set.mem_Ici.mpr le_rfl)
        (show (N : ℝ) + 1 ∈ Set.Ici (N : ℝ) by simp)
        (by linarith : (N : ℝ) ≤ (N : ℝ) + 1)
      exact (hnonneg ((N : ℝ) + 1) (by simp)).trans hm
    · exact hnonneg x hx
  have hsumV : Summable V := by
    apply (hsumT.mul_left 2).of_norm_bounded_eventually_nat
    filter_upwards [hratio.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 2)),
      eventually_ge_atTop (1 : ℕ)] with n hr hn
    rw [Real.norm_eq_abs, abs_of_nonneg (localModel_over_nat_nonneg hpos n)]
    have hlt := (div_lt_iff₀ (hTpos n hn)).mp hr
    dsimp only [T] at hlt ⊢
    linarith
  have htail : Tendsto (fun n : ℕ => tailMass T n / F n) atTop (𝓝 1) :=
    tailMass_div_tendsto_one_of_primitive hF (by
      simpa only [T, F] using (show Tendsto (fun n : ℕ =>
        logPowerModel c β n / logPowerPrimitive c β n) atTop (𝓝 0) from by
        have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
          tendsto_natCast_atTop_atTop
        have hlogtop : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
          Real.tendsto_log_atTop.comp hnat
        have hden := hnat.atTop_mul_atTop₀ hlogtop
        have hz := hden.const_div_atTop β
        apply hz.congr'
        filter_upwards [eventually_gt_atTop (2 : ℕ)] with n hn
        have hnR : (3 : ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
        have hn0 : 0 < (n : ℝ) := by linarith
        have hlog : 0 < Real.log n := Real.log_pos (by linarith)
        simp only [logPowerModel, logPowerPrimitive,
          show ¬(n : ℝ) < 3 by linarith, ↓reduceIte]
        rw [Real.rpow_add hlog]
        simp only [Real.rpow_one]
        field_simp [hc.ne', hβ.ne', hn0.ne', hlog.ne', (Real.rpow_pos_of_pos hlog β).ne'])) hFpos hlarge
  have hcompare : Tendsto (fun n : ℕ => ellStar L n / tailMass T n) atTop (𝓝 1) := by
    simpa only [ellStar, V] using tailMass_div_tendsto_one hsumT hsumV hT0 hTpos hratio
  have hprod := hcompare.mul htail
  have hfinal : Tendsto (fun n : ℕ =>
      ellStar L n / (c / (β * (Real.log n) ^ β))) atTop (𝓝 (1 * 1)) := by
    apply hprod.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have ht := (tailMass_pos hsumT hT0 hTpos hn).ne'
    change ellStar L n / tailMass T n *
      (tailMass T n / logPowerPrimitive c β n) = _
    rw [logPowerPrimitive]
    by_cases hden : β * (Real.log n) ^ β = 0
    · simp [hden]
    · field_simp [ht, hden]
  simpa using hfinal


/-- The iterated logarithm `log_(k)` from the manuscript, with `log_(0) x = x`. -/
noncomputable def iterLog : ℕ → ℝ → ℝ
  | 0, x => x
  | k + 1, x => Real.log (iterLog k x)

private theorem iterLog_log (j : ℕ) (x : ℝ) :
    iterLog j (Real.log x) = iterLog (j + 1) x := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
      change Real.log (iterLog j (Real.log x)) = Real.log (iterLog (j + 1) x)
      rw [ih]

private noncomputable def iterExp : ℕ → ℝ
  | 0 => 3
  | k + 1 => Real.exp (iterExp k)

private noncomputable def iterLogModel (k : ℕ) (c x : ℝ) : ℝ :=
  if x < iterExp k then 1 else
    c * (∏ i ∈ Finset.range k, (iterLog i x)⁻¹) / (iterLog k x) ^ 2

private theorem iterExp_pos (k : ℕ) : 0 < iterExp k := by
  induction k with
  | zero => norm_num [iterExp]
  | succ k ih => exact Real.exp_pos _

private theorem iterLog_tendsto_atTop (k : ℕ) : Tendsto (iterLog k) atTop atTop := by
  induction k with
  | zero =>
      change Tendsto (fun x : ℝ => x) atTop atTop
      exact tendsto_id
  | succ k ih =>
      change Tendsto (Real.log ∘ iterLog k) atTop atTop
      exact Real.tendsto_log_atTop.comp ih

private theorem iterLog_mono {k : ℕ} {x y : ℝ} (hxy : x ≤ y)
    (hx : ∀ i < k, 0 < iterLog i x) : iterLog k x ≤ iterLog k y := by
  induction k generalizing x y with
  | zero => exact hxy
  | succ k ih =>
      apply Real.log_le_log (hx k (Nat.lt_succ_self k))
      exact ih hxy (fun i hi => hx i (Nat.lt_succ_of_lt hi))

private theorem three_le_iterExp (k : ℕ) : 3 ≤ iterExp k := by
  induction k with
  | zero => norm_num [iterExp]
  | succ k ih =>
      have he := Real.add_one_le_exp (iterExp k)
      dsimp only [iterExp]
      linarith

private theorem three_le_iterLog_of_iterExp_le {k : ℕ} {x : ℝ}
    (hx : iterExp k ≤ x) {i : ℕ} (hi : i ≤ k) : 3 ≤ iterLog i x := by
  induction k generalizing x i with
  | zero =>
      have hi0 : i = 0 := by omega
      subst i
      simpa [iterExp, iterLog] using hx
  | succ k ih =>
      have hxlog : iterExp k ≤ Real.log x := by
        apply (Real.le_log_iff_exp_le ((iterExp_pos (k + 1)).trans_le hx)).mpr
        simpa only [iterExp] using hx
      cases i with
      | zero =>
          simp only [iterLog]
          exact (three_le_iterExp (k + 1)).trans hx
      | succ j =>
          have hj : j ≤ k := Nat.succ_le_succ_iff.mp hi
          change 3 ≤ iterLog (j + 1) x
          rw [← iterLog_log]
          exact ih hxlog hj

private theorem hasDerivAt_iterLog (k : ℕ) (x : ℝ)
    (hx : ∀ i < k, iterLog i x ≠ 0) :
    HasDerivAt (iterLog k) (∏ i ∈ Finset.range k, (iterLog i x)⁻¹) x := by
  induction k with
  | zero =>
      change HasDerivAt (fun x : ℝ => x) 1 x
      exact hasDerivAt_id x
  | succ k ih =>
      have hk := ih (fun i hi => hx i (Nat.lt_succ_of_lt hi))
      have hd := hk.log (hx k (Nat.lt_succ_self k))
      change HasDerivAt (fun y => Real.log (iterLog k y))
        (∏ i ∈ Finset.range (k + 1), (iterLog i x)⁻¹) x
      convert hd using 1
      simp only [Finset.prod_range_succ, div_eq_mul_inv]

private theorem iterLog_range_prod_eq {k : ℕ} (hk : 1 ≤ k) (x : ℝ) :
    (∏ i ∈ Finset.range k, (iterLog i x)⁻¹) =
      x⁻¹ * ∏ i ∈ Finset.Icc 1 (k - 1), (iterLog i x)⁻¹ := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [Finset.prod_range_succ']
  have hset : Finset.Icc 1 (j + 1 - 1) = Finset.Ico 1 (j + 1) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hset, Finset.prod_Ico_eq_prod_range]
  simp only [Nat.add_sub_cancel, iterLog]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp only [Nat.add_comm, iterLog]

/-- Example 2.3(ii): the integrated tail for the iterated logarithmic model. -/
theorem example23_ii_ellStar {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x) {k : ℕ} (hk : 2 ≤ k) {c : ℝ} (hc : 0 < c)
    (hL : Tendsto (fun n : ℕ => L n /
      (c / (iterLog k n) ^ 2 * ∏ i ∈ Finset.Icc 1 (k - 1), 1 / iterLog i n))
      atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => ellStar L n / (c / iterLog k n)) atTop (𝓝 1) := by
  have hk1 : 1 ≤ k := by omega
  let T : ℕ → ℝ := fun n => iterLogModel k c n
  let V : ℕ → ℝ := fun n => L n / (n : ℝ)
  let F : ℝ → ℝ := fun x => c / iterLog k x
  have hT0 (n : ℕ) : 0 ≤ T n := by
    by_cases hn : (n : ℝ) < iterExp k
    · simp [T, iterLogModel, hn]
    · have hx : iterExp k ≤ (n : ℝ) := le_of_not_gt hn
      have hp (i : ℕ) (hi : i ≤ k) : 0 < iterLog i n := by
        linarith [three_le_iterLog_of_iterExp_le hx hi]
      simp only [T, iterLogModel, hn, ↓reduceIte]
      have hprod : 0 < ∏ i ∈ Finset.range k, (iterLog i n)⁻¹ := by
        apply Finset.prod_pos
        intro i hi
        exact inv_pos.mpr (hp i (Finset.mem_range.mp hi).le)
      exact (div_pos (mul_pos hc hprod) (sq_pos_of_pos (hp k le_rfl))).le
  have hTpos (n : ℕ) (_hn : 1 ≤ n) : 0 < T n := by
    by_cases hn : (n : ℝ) < iterExp k
    · simp [T, iterLogModel, hn]
    · have hx : iterExp k ≤ (n : ℝ) := le_of_not_gt hn
      have hp (i : ℕ) (hi : i ≤ k) : 0 < iterLog i n := by
        linarith [three_le_iterLog_of_iterExp_le hx hi]
      simp only [T, iterLogModel, hn, ↓reduceIte]
      have hprod : 0 < ∏ i ∈ Finset.range k, (iterLog i n)⁻¹ := by
        apply Finset.prod_pos
        intro i hi
        exact inv_pos.mpr (hp i (Finset.mem_range.mp hi).le)
      exact div_pos (mul_pos hc hprod) (sq_pos_of_pos (hp k le_rfl))
  have hratio : Tendsto (fun n : ℕ => V n / T n) atTop (𝓝 1) := by
    apply hL.congr'
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (iterExp k)]
      with n hn
    have hn0 : 0 < (n : ℝ) := (iterExp_pos k).trans_le hn
    have hkpos : 0 < iterLog k n := by
      linarith [three_le_iterLog_of_iterExp_le hn (le_refl k)]
    have hp : 0 < ∏ i ∈ Finset.Icc 1 (k - 1), (iterLog i n)⁻¹ := by
      apply Finset.prod_pos
      intro i hi
      have hik : i ≤ k := by
        have := (Finset.mem_Icc.mp hi).2
        omega
      exact inv_pos.mpr (by linarith [three_le_iterLog_of_iterExp_le hn hik])
    simp only [V, T, iterLogModel, show ¬(n : ℝ) < iterExp k by linarith, ↓reduceIte]
    rw [iterLog_range_prod_eq hk1]
    simp only [one_div]
    field_simp [hc.ne', hn0.ne', hkpos.ne', hp.ne']
  have hF : Tendsto F atTop (𝓝 0) := by
    simpa only [F] using (iterLog_tendsto_atTop k).const_div_atTop c
  have hFpos : ∀ᶠ n : ℕ in atTop, 0 < F n := by
    filter_upwards [(iterLog_tendsto_atTop k).comp tendsto_natCast_atTop_atTop |>.eventually_gt_atTop 0]
      with n hn
    exact div_pos hc hn
  have hlarge : ∀ᶠ n : ℕ in atTop,
      AntitoneOn (iterLogModel k c) (Set.Ici (n : ℝ)) ∧
      (∀ x ∈ Set.Ici (n : ℝ),
        HasDerivAt (fun x => c / iterLog k x) (-iterLogModel k c x) x) ∧
      (∀ x ∈ Set.Ioi (n : ℝ), 0 ≤ iterLogModel k c x) := by
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (iterExp k)]
      with n hn
    have hx3 {x : ℝ} (hx : x ∈ Set.Ici (n : ℝ)) (i : ℕ) (hi : i ≤ k) :
        3 ≤ iterLog i x := three_le_iterLog_of_iterExp_le (hn.trans hx) hi
    have hposi {x : ℝ} (hx : x ∈ Set.Ici (n : ℝ)) (i : ℕ) (hi : i ≤ k) :
        0 < iterLog i x := by linarith [hx3 hx i hi]
    have hmodel (x : ℝ) (hx : x ∈ Set.Ici (n : ℝ)) :
        iterLogModel k c x = c * (∏ i ∈ Finset.range k, (iterLog i x)⁻¹) /
          (iterLog k x) ^ 2 := by
      simp [iterLogModel, show ¬x < iterExp k by exact not_lt.mpr (hn.trans hx)]
    have hmono {x y : ℝ} (hx : x ∈ Set.Ici (n : ℝ)) (hy : y ∈ Set.Ici (n : ℝ))
        (hxy : x ≤ y) (i : ℕ) (hi : i ≤ k) : iterLog i x ≤ iterLog i y := by
      apply iterLog_mono hxy
      intro j hj
      exact hposi hx j (hj.le.trans hi)
    refine ⟨?_, ?_, ?_⟩
    · intro x hx y hy hxy
      rw [hmodel x hx, hmodel y hy]
      have hprod : (∏ i ∈ Finset.range k, (iterLog i y)⁻¹) ≤
          ∏ i ∈ Finset.range k, (iterLog i x)⁻¹ := by
        apply Finset.prod_le_prod₀
        · intro i hi
          exact inv_nonneg.mpr (hposi hy i (Finset.mem_range.mp hi).le).le
        · intro i hi
          have hik : i ≤ k := (Finset.mem_range.mp hi).le
          exact (inv_le_inv₀ (hposi hy i hik) (hposi hx i hik)).mpr (hmono hx hy hxy i hik)
      have hksq : (iterLog k x) ^ 2 ≤ (iterLog k y) ^ 2 := by
        nlinarith [hposi hx k le_rfl, hposi hy k le_rfl, hmono hx hy hxy k le_rfl]
      have hprodX0 : 0 ≤ ∏ i ∈ Finset.range k, (iterLog i x)⁻¹ := by
        apply Finset.prod_nonneg
        intro i hi
        exact inv_nonneg.mpr (hposi hx i (Finset.mem_range.mp hi).le).le
      apply div_le_div₀ (mul_nonneg hc.le hprodX0)
      · exact mul_le_mul_of_nonneg_left hprod hc.le
      · exact sq_pos_of_pos (hposi hx k le_rfl)
      · exact hksq
    · intro x hx
      have hd := (hasDerivAt_const x c).div
        (hasDerivAt_iterLog k x (fun i hi => (hposi hx i hi.le).ne'))
        (hposi hx k le_rfl).ne'
      convert hd using 1
      rw [hmodel x hx]
      ring
    · intro x hx
      have hxci : x ∈ Set.Ici (n : ℝ) := hx.le
      rw [hmodel x hxci]
      have hprod : 0 < ∏ i ∈ Finset.range k, (iterLog i x)⁻¹ := by
        apply Finset.prod_pos
        intro i hi
        exact inv_pos.mpr (hposi hxci i (Finset.mem_range.mp hi).le)
      positivity
  obtain ⟨N, hN⟩ := eventually_atTop.mp hlarge
  have hsumT : Summable T := by
    obtain ⟨hanti, hderiv, hnonneg⟩ := hN N le_rfl
    apply summable_nat_of_antitone_primitive hF hanti hderiv
    intro x hx
    rcases hx.eq_or_lt with rfl | hx
    · have hm := hanti (Set.mem_Ici.mpr le_rfl)
        (show (N : ℝ) + 1 ∈ Set.Ici (N : ℝ) by simp)
        (by linarith : (N : ℝ) ≤ (N : ℝ) + 1)
      exact (hnonneg ((N : ℝ) + 1) (by simp)).trans hm
    · exact hnonneg x hx
  have hsumV : Summable V := by
    apply (hsumT.mul_left 2).of_norm_bounded_eventually_nat
    filter_upwards [hratio.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 2)),
      eventually_ge_atTop (1 : ℕ)] with n hr hn
    rw [Real.norm_eq_abs, abs_of_nonneg (localModel_over_nat_nonneg hpos n)]
    have hlt := (div_lt_iff₀ (hTpos n hn)).mp hr
    dsimp only [T] at hlt ⊢
    linarith
  have hsmall : Tendsto (fun n : ℕ => iterLogModel k c n / (c / iterLog k n))
      atTop (𝓝 0) := by
    have hz : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 1
    apply squeeze_zero' _ _ hz
    · filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (iterExp k)]
        with n hn
      simp only [iterLogModel, show ¬(n : ℝ) < iterExp k by linarith, ↓reduceIte]
      have hkpos : 0 < iterLog k n := by
        linarith [three_le_iterLog_of_iterExp_le hn le_rfl]
      have hprod : 0 < ∏ i ∈ Finset.range k, (iterLog i n)⁻¹ := by
        apply Finset.prod_pos
        intro i hi
        have hi' : i ≤ k := (Finset.mem_range.mp hi).le
        exact inv_pos.mpr (by linarith [three_le_iterLog_of_iterExp_le hn hi'])
      exact div_nonneg (div_pos (mul_pos hc hprod) (sq_pos_of_pos hkpos)).le
        (div_pos hc hkpos).le
    · filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (iterExp k)]
        with n hn
      have hn0 : 0 < (n : ℝ) := (iterExp_pos k).trans_le hn
      have hk3 : 3 ≤ iterLog k n := three_le_iterLog_of_iterExp_le hn le_rfl
      have hp0 : 0 ≤ ∏ i ∈ Finset.range k, (iterLog i n)⁻¹ := by
        apply Finset.prod_nonneg
        intro i hi
        exact inv_nonneg.mpr (by
          have hi' : i ≤ k := (Finset.mem_range.mp hi).le
          linarith [three_le_iterLog_of_iterExp_le hn hi'])
      have hshift0 : 0 ≤ ∏ i ∈ Finset.Icc 1 (k - 1), (iterLog i n)⁻¹ := by
        apply Finset.prod_nonneg
        intro i hi
        have hik : i ≤ k := by
          have := (Finset.mem_Icc.mp hi).2
          omega
        exact inv_nonneg.mpr (by linarith [three_le_iterLog_of_iterExp_le hn hik])
      have hshift1 : (∏ i ∈ Finset.Icc 1 (k - 1), (iterLog i n)⁻¹) ≤ 1 := by
        calc
          _ ≤ ∏ _i ∈ Finset.Icc 1 (k - 1), (1 : ℝ) := by
            apply Finset.prod_le_prod₀
            · intro i hi
              have hik : i ≤ k := by
                have := (Finset.mem_Icc.mp hi).2
                omega
              exact inv_nonneg.mpr (by
                linarith [three_le_iterLog_of_iterExp_le hn hik])
            · intro i hi
              have hik : i ≤ k := by
                have := (Finset.mem_Icc.mp hi).2
                omega
              have hipos : 0 < iterLog i n := by
                linarith [three_le_iterLog_of_iterExp_le hn hik]
              have hh := one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num)
                (show 1 ≤ iterLog i n by linarith [three_le_iterLog_of_iterExp_le hn hik])
              simpa using hh
          _ = 1 := by simp
      have hrange : (∏ i ∈ Finset.range k, (iterLog i n)⁻¹) ≤ 1 / (n : ℝ) := by
        rw [iterLog_range_prod_eq hk1]
        have hh := mul_le_mul_of_nonneg_left hshift1 (inv_nonneg.mpr hn0.le)
        simpa [one_div] using hh
      simp only [iterLogModel, show ¬(n : ℝ) < iterExp k by linarith, ↓reduceIte]
      have hcancel : c * (∏ i ∈ Finset.range k, (iterLog i n)⁻¹) / (iterLog k n) ^ 2 /
          (c / iterLog k n) = (∏ i ∈ Finset.range k, (iterLog i n)⁻¹) / iterLog k n := by
        field_simp [hc.ne', (show 0 < iterLog k n by linarith).ne']
      rw [hcancel]
      exact (div_le_self hp0 (by linarith)).trans hrange
  have htail : Tendsto (fun n : ℕ => tailMass T n / F n) atTop (𝓝 1) := by
    apply tailMass_div_tendsto_one_of_primitive hF _ hFpos hlarge
    simpa only [T, F] using hsmall
  have hcompare : Tendsto (fun n : ℕ => ellStar L n / tailMass T n) atTop (𝓝 1) := by
    simpa only [ellStar, V] using tailMass_div_tendsto_one hsumT hsumV hT0 hTpos hratio
  have hprod := hcompare.mul htail
  have hfinal : Tendsto (fun n : ℕ => ellStar L n / (c / iterLog k n))
      atTop (𝓝 (1 * 1)) := by
    apply hprod.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have ht := (tailMass_pos hsumT hT0 hTpos hn).ne'
    change ellStar L n / tailMass T n * (tailMass T n / (c / iterLog k n)) = _
    field_simp [ht]
  simpa using hfinal


private theorem iterLog_le_log {i : ℕ} (hi : 1 ≤ i) {x : ℝ}
    (hx : ∀ j < i, 0 ≤ iterLog j x) : iterLog i x ≤ Real.log x := by
  induction i with
  | zero => omega
  | succ j ih =>
      cases j with
      | zero => rfl
      | succ j =>
          calc
            iterLog (j + 1 + 1) x = Real.log (iterLog (j + 1) x) := rfl
            _ ≤ iterLog (j + 1) x := Real.log_le_self (hx (j + 1) (by omega))
            _ ≤ Real.log x := ih (by omega) (fun r hr => hx r (by omega))

private theorem floor_le_nat_of_scaling {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
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

private theorem log_iterLog_floor_div_log_nat {a : ℕ → ℝ} {k i : ℕ}
    (hi : 1 ≤ i) (hik : i ≤ k) (ha : Tendsto a atTop atTop)
    (hle : ∀ᶠ n : ℕ in atTop, ((Nat.floor (a n) : ℕ) : ℝ) ≤ (n : ℝ)) :
    Tendsto (fun n : ℕ =>
      Real.log (iterLog i (Nat.floor (a n))) / Real.log n) atTop (𝓝 0) := by
  have hfloorNat : Tendsto (fun n : ℕ => Nat.floor (a n)) atTop atTop :=
    tendsto_nat_floor_atTop.comp ha
  have hfloorReal : Tendsto (fun n : ℕ => ((Nat.floor (a n) : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hfloorNat
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlognat : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp hnat
  have hz : Tendsto (fun n : ℕ => Real.log (Real.log n) / Real.log n) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hlognat
  apply squeeze_zero' _ _ hz
  · filter_upwards [hfloorReal.eventually_ge_atTop (iterExp k),
      hlognat.eventually_gt_atTop 0] with n hm hn
    have hipos : 0 < iterLog i (Nat.floor (a n)) := by
      linarith [three_le_iterLog_of_iterExp_le hm hik]
    exact div_nonneg (Real.log_nonneg (by
      linarith [three_le_iterLog_of_iterExp_le hm hik])) hn.le
  · filter_upwards [hle, hfloorReal.eventually_ge_atTop (iterExp k),
      hlognat.eventually_gt_atTop 0] with n hmn hm hn
    have hmpos : 0 < ((Nat.floor (a n) : ℕ) : ℝ) := (iterExp_pos k).trans_le hm
    have hipos : 0 < iterLog i (Nat.floor (a n)) := by
      linarith [three_le_iterLog_of_iterExp_le hm hik]
    have hnonneg (j : ℕ) (hj : j < i) : 0 ≤ iterLog j (Nat.floor (a n)) := by
      have hjk : j ≤ k := by omega
      linarith [three_le_iterLog_of_iterExp_le hm hjk]
    have hiter : iterLog i (Nat.floor (a n)) ≤ Real.log n :=
      (iterLog_le_log hi hnonneg).trans (Real.log_le_log hmpos hmn)
    have hnum : Real.log (iterLog i (Nat.floor (a n))) ≤ Real.log (Real.log n) := by
      calc
        _ ≤ Real.log (Real.log (Nat.floor (a n))) :=
          Real.log_le_log hipos (iterLog_le_log hi hnonneg)
        _ ≤ _ := Real.log_le_log (Real.log_pos (by
          have : (1 : ℝ) < ((Nat.floor (a n) : ℕ) : ℝ) := by
            have hh := three_le_iterExp k
            exact_mod_cast (show (1 : ℝ) < (3 : ℝ) by norm_num).trans_le (hh.trans hm)
          exact this)) (Real.log_le_log hmpos hmn)
    exact div_le_div_of_nonneg_right hnum hn.le

private theorem log_floor_div_log {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) :
    Tendsto (fun n : ℕ => Real.log (Nat.floor (a n)) / Real.log (a n)) atTop (𝓝 1) := by
  have hratio : Tendsto (fun n : ℕ => ((Nat.floor (a n) : ℕ) : ℝ) / a n)
      atTop (𝓝 1) := tendsto_nat_floor_div_atTop.comp ha
  have hloga : Tendsto (fun n : ℕ => Real.log (a n)) atTop atTop :=
    Real.tendsto_log_atTop.comp ha
  have hzero := (hratio.log one_ne_zero).div_atTop hloga
  have htrend := (tendsto_const_nhds (x := (1 : ℝ))).add hzero
  have hfinal : Tendsto (fun n : ℕ => Real.log (Nat.floor (a n)) / Real.log (a n))
      atTop (𝓝 (1 + 0)) := by
    apply htrend.congr'
    filter_upwards [ha.eventually_gt_atTop 1,
      (tendsto_nat_floor_atTop.comp ha).eventually_gt_atTop 0] with n ha1 hm0
    have ha0 : 0 < a n := by linarith
    have hmR : 0 < ((Nat.floor (a n) : ℕ) : ℝ) := Nat.cast_pos.mpr hm0
    rw [Real.log_div hmR.ne' ha0.ne']
    have hlogane : Real.log (a n) ≠ 0 := (Real.log_pos ha1).ne'
    field_simp [hlogane]
    ring
  simpa using hfinal

private theorem log_L_div_log_of_floor {L : ℝ → ℝ} {a : ℕ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hmeas : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L) (ha : Tendsto a atTop atTop)
    (hfloor : Tendsto (fun n : ℕ => Real.log (L (Nat.floor (a n))) / Real.log n)
      atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => Real.log (L (a n)) / Real.log n) atTop (𝓝 0) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlognat : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp hnat
  have hfloorNat : Tendsto (fun n : ℕ => Nat.floor (a n)) atTop atTop :=
    tendsto_nat_floor_atTop.comp ha
  have hfloorReal : Tendsto (fun n : ℕ => ((Nat.floor (a n) : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hfloorNat
  have hratio : Tendsto (fun n : ℕ => L (a n) / L (Nat.floor (a n))) atTop (𝓝 1) := by
    simpa only [Pi.inv_apply, inv_div, inv_one, Function.comp_def] using
      ((localModel_floor_div_tendsto_one hpos hmeas hsv).inv₀ one_ne_zero).comp ha
  have hzero := (hratio.log one_ne_zero).div_atTop hlognat
  have hsum := hzero.add hfloor
  have hfinal : Tendsto (fun n : ℕ => Real.log (L (a n)) / Real.log n)
      atTop (𝓝 (0 + 0)) := by
    apply hsum.congr'
    filter_upwards [ha.eventually_gt_atTop 0, hfloorReal.eventually_gt_atTop 0] with n han hmn
    have hLa : 0 < L (a n) := hpos _ han
    have hLm : 0 < L (Nat.floor (a n)) := hpos _ hmn
    rw [Real.log_div hLa.ne' hLm.ne']
    ring
  simpa using hfinal

private theorem scaling_log_div_log_of_log_L (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ < 1) {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hmeas : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1)) {a : ℕ → ℝ}
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal) atTop (𝓝 1))
    (hlogL : Tendsto (fun n : ℕ => Real.log (L (a n)) / Real.log n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => Real.log (a n) / Real.log n) atTop (𝓝 1) := by
  have hlit : IsSubcriticalCauchyOffspring μ := ⟨hm, L, hpos, hsv, hlocal⟩
  have hat := scaling_tendsto_atTop μ hlit ha
  have hscale := scaling_div_mul_tendsto_one μ hm hpos hmeas hsv hlocal ha
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlognat : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp hnat
  have hlogR : Tendsto (fun n : ℕ => Real.log (a n / ((n : ℝ) * L (a n))))
      atTop (𝓝 0) := by simpa using hscale.log one_ne_zero
  have hzero := hlogR.div_atTop hlognat
  have htrend := (tendsto_const_nhds (x := (1 : ℝ))).add (hzero.add hlogL)
  have hfinal : Tendsto (fun n : ℕ => Real.log (a n) / Real.log n)
      atTop (𝓝 (1 + (0 + 0))) := by
    apply htrend.congr'
    filter_upwards [hat.eventually_gt_atTop 0, hlognat.eventually_gt_atTop 0,
      eventually_gt_atTop (0 : ℕ)] with n han hlogn hn
    have hLa : 0 < L (a n) := hpos _ han
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    rw [Real.log_div han.ne' (mul_ne_zero hnR.ne' hLa.ne'),
      Real.log_mul hnR.ne' hLa.ne']
    field_simp [hlogn.ne']
    ring
  simpa using hfinal

private theorem L_div_nat_of_explicit_model {L M : ℝ → ℝ} {a : ℕ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hmeas : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L) (ha : Tendsto a atTop atTop)
    (hmodelNat : Tendsto (fun n : ℕ => L n / M n) atTop (𝓝 1))
    (hmodelFloorA : Tendsto (fun n : ℕ => M (Nat.floor (a n)) / M (a n)) atTop (𝓝 1))
    (hmodelAN : Tendsto (fun n : ℕ => M (a n) / M n) atTop (𝓝 1))
    (hMpos : ∀ᶠ n : ℕ in atTop,
      0 < M (Nat.floor (a n)) ∧ 0 < M (a n) ∧ 0 < M n) :
    Tendsto (fun n : ℕ => L (a n) / L n) atTop (𝓝 1) := by
  have hfloorNat : Tendsto (fun n : ℕ => Nat.floor (a n)) atTop atTop :=
    tendsto_nat_floor_atTop.comp ha
  have hfloorReal : Tendsto (fun n : ℕ => ((Nat.floor (a n) : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hfloorNat
  have hratio : Tendsto (fun n : ℕ => L (a n) / L (Nat.floor (a n))) atTop (𝓝 1) := by
    simpa only [Pi.inv_apply, inv_div, inv_one, Function.comp_def] using
      ((localModel_floor_div_tendsto_one hpos hmeas hsv).inv₀ one_ne_zero).comp ha
  have hnat : Tendsto (fun n : ℕ => L n / M (n : ℝ)) atTop (𝓝 1) := hmodelNat
  have hprod := hratio.mul ((hmodelNat.comp hfloorNat).mul
    (hmodelFloorA.mul (hmodelAN.mul (hnat.inv₀ one_ne_zero))))
  have hfinal : Tendsto (fun n : ℕ => L (a n) / L n)
      atTop (𝓝 (1 * (1 * (1 * (1 * 1⁻¹))))) := by
    apply hprod.congr'
    filter_upwards [hMpos, ha.eventually_gt_atTop 0, hfloorReal.eventually_gt_atTop 0,
      tendsto_natCast_atTop_atTop.eventually_gt_atTop (0 : ℝ)] with n hM han hmn hn
    obtain ⟨hMm, hMa, hMn⟩ := hM
    have hLa := hpos _ han
    have hLm := hpos _ hmn
    have hLn := hpos _ hn
    dsimp only [Function.comp_def]
    field_simp [hLa.ne', hLm.ne', hLn.ne', hMm.ne', hMa.ne', hMn.ne']
  simpa using hfinal

private theorem logPowerExplicit_div {x y : ℕ → ℝ} {c _β : ℝ} (hc : 0 < c)
    (hx : Tendsto (fun n => Real.log (x n)) atTop atTop)
    (hy : Tendsto (fun n => Real.log (y n)) atTop atTop)
    (hr : Tendsto (fun n => Real.log (x n) / Real.log (y n)) atTop (𝓝 1)) :
    Tendsto (fun n => (c / (Real.log (x n)) ^ (1 + _β)) /
      (c / (Real.log (y n)) ^ (1 + _β))) atTop (𝓝 1) := by
  have hp : Tendsto (fun n => (Real.log (y n) / Real.log (x n)) ^ (1 + _β))
      atTop (𝓝 1) := by
    simpa using (hr.inv₀ one_ne_zero).rpow_const (p := 1 + _β) (Or.inl (by norm_num))
  have hfinal : Tendsto (fun n => (c / (Real.log (x n)) ^ (1 + _β)) /
      (c / (Real.log (y n)) ^ (1 + _β))) atTop (𝓝 1) := by
    apply hp.congr'
    filter_upwards [hx.eventually_gt_atTop 0, hy.eventually_gt_atTop 0] with n hxn hyn
    rw [Real.div_rpow hyn.le hxn.le]
    field_simp [hc.ne', (Real.rpow_pos_of_pos hxn (1 + _β)).ne',
      (Real.rpow_pos_of_pos hyn (1 + _β)).ne']
  exact hfinal


/-- Example 2.3(i): logarithmic and multiplicative asymptotics of every scale. -/
theorem example23_i_scale (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ < 1) {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hmeas : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1)) {c β : ℝ} (hc : 0 < c) (_hβ : 0 < β)
    (hL : Tendsto (fun n : ℕ => L n / (c / (Real.log n) ^ (1 + β)))
      atTop (𝓝 1)) {a : ℕ → ℝ}
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => Real.log (a n) / Real.log n) atTop (𝓝 1) ∧
      Tendsto (fun n : ℕ => a n / ((n : ℝ) * L n)) atTop (𝓝 1) := by
  have hlit : IsSubcriticalCauchyOffspring μ := ⟨hm, L, hpos, hsv, hlocal⟩
  have hat := scaling_tendsto_atTop μ hlit ha
  have hsub := scaling_div_nat_tendsto_zero μ hlit ha
  have hscale := scaling_div_mul_tendsto_one μ hm hpos hmeas hsv hlocal ha
  have hle := floor_le_nat_of_scaling hat hsub
  have hfloorNat : Tendsto (fun n : ℕ => Nat.floor (a n)) atTop atTop :=
    tendsto_nat_floor_atTop.comp hat
  have hfloorReal : Tendsto (fun n : ℕ => ((Nat.floor (a n) : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hfloorNat
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlognat : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp hnat
  have hloga : Tendsto (fun n : ℕ => Real.log (a n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hat
  have hlogfloor : Tendsto (fun n : ℕ => Real.log (Nat.floor (a n))) atTop atTop :=
    Real.tendsto_log_atTop.comp hfloorReal
  have hloglog : Tendsto (fun n : ℕ =>
      Real.log (Real.log (Nat.floor (a n))) / Real.log n) atTop (𝓝 0) := by
    simpa only [iterLog] using
      (log_iterLog_floor_div_log_nat (a := a) (k := 1) (i := 1) le_rfl le_rfl hat hle)
  have hlogModelRatio := (hL.comp hfloorNat).log one_ne_zero |>.div_atTop hlognat
  have hconst : Tendsto (fun _n : ℕ => Real.log c / Real.log (_n : ℕ)) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := Real.log c)).div_atTop hlognat
  have hlogpow := hloglog.const_mul (1 + β)
  have hmodelLog : Tendsto (fun n : ℕ =>
      Real.log (c / (Real.log (Nat.floor (a n))) ^ (1 + β)) / Real.log n)
      atTop (𝓝 0) := by
    have hh := hconst.sub hlogpow
    have hfinal : Tendsto (fun n : ℕ =>
        Real.log (c / (Real.log (Nat.floor (a n))) ^ (1 + β)) / Real.log n)
        atTop (𝓝 (0 - (1 + β) * 0)) := by
      apply hh.congr'
      filter_upwards [hlogfloor.eventually_gt_atTop 0, hlognat.eventually_gt_atTop 0]
        with n hm hn
      rw [Real.log_div hc.ne' (Real.rpow_pos_of_pos hm (1 + β)).ne',
        Real.log_rpow hm (1 + β)]
      field_simp [hn.ne']
    simpa using hfinal
  have hfloorLog : Tendsto (fun n : ℕ => Real.log (L (Nat.floor (a n))) / Real.log n)
      atTop (𝓝 0) := by
    have hh := hlogModelRatio.add hmodelLog
    have hfinal : Tendsto (fun n : ℕ => Real.log (L (Nat.floor (a n))) / Real.log n)
        atTop (𝓝 (0 + 0)) := by
      apply hh.congr'
      filter_upwards [hfloorReal.eventually_gt_atTop 0,
        hlogfloor.eventually_gt_atTop 0, hlognat.eventually_gt_atTop 0]
        with n hm hmlog hn
      have hLm : 0 < L (Nat.floor (a n)) := hpos _ hm
      have hM : 0 < c / (Real.log (Nat.floor (a n))) ^ (1 + β) :=
        div_pos hc (Real.rpow_pos_of_pos hmlog _)
      dsimp only [Function.comp_def]
      rw [Real.log_div hLm.ne' hM.ne']
      field_simp [hn.ne']
      ring
    simpa using hfinal
  have hlogL := log_L_div_log_of_floor hpos hmeas hsv hat hfloorLog
  have hlogratio := scaling_log_div_log_of_log_L μ hm hpos hmeas hsv hlocal ha hlogL
  have hLratio : Tendsto (fun n : ℕ => L (a n) / L n) atTop (𝓝 1) := by
    let M : ℝ → ℝ := fun x => c / (Real.log x) ^ (1 + β)
    have hmodelNat : Tendsto (fun n : ℕ => L n / M n) atTop (𝓝 1) := by
      simpa only [M] using hL
    have hmodelFloorA : Tendsto (fun n : ℕ => M (Nat.floor (a n)) / M (a n))
        atTop (𝓝 1) := by
      simpa only [M] using logPowerExplicit_div hc hlogfloor hloga (log_floor_div_log hat)
    have hmodelAN : Tendsto (fun n : ℕ => M (a n) / M n) atTop (𝓝 1) := by
      simpa only [M] using logPowerExplicit_div hc hloga hlognat hlogratio
    apply L_div_nat_of_explicit_model (M := M) hpos hmeas hsv hat
      hmodelNat hmodelFloorA hmodelAN
    filter_upwards [hlogfloor.eventually_gt_atTop 0, hloga.eventually_gt_atTop 0,
      hlognat.eventually_gt_atTop 0] with n hm han hn
    exact ⟨div_pos hc (Real.rpow_pos_of_pos hm _), div_pos hc (Real.rpow_pos_of_pos han _),
      div_pos hc (Real.rpow_pos_of_pos hn _)⟩
  have hfinal : Tendsto (fun n : ℕ => a n / ((n : ℝ) * L n)) atTop (𝓝 (1 * 1)) := by
    have hh := hscale.mul hLratio
    apply hh.congr'
    filter_upwards [hat.eventually_gt_atTop 0, eventually_gt_atTop (0 : ℕ),
      hlognat.eventually_gt_atTop 0] with n han hn hlogn
    have hLa : 0 < L (a n) := hpos _ han
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hLn : 0 < L n := hpos _ hnR
    field_simp [hLa.ne', hLn.ne', hnR.ne']
  exact ⟨hlogratio, by simpa using hfinal⟩


private noncomputable def iterLogExplicit (k : ℕ) (c x : ℝ) : ℝ :=
  c / (iterLog k x) ^ 2 * ∏ i ∈ Finset.Icc 1 (k - 1), 1 / iterLog i x

private theorem iterLog_floor_div_iterLog {a : ℕ → ℝ} (i : ℕ)
    (ha : Tendsto a atTop atTop) :
    Tendsto (fun n : ℕ => iterLog i (Nat.floor (a n)) / iterLog i (a n))
      atTop (𝓝 1) := by
  induction i with
  | zero =>
      change Tendsto (fun n : ℕ => ((Nat.floor (a n) : ℕ) : ℝ) / a n) atTop (𝓝 1)
      exact tendsto_nat_floor_div_atTop.comp ha
  | succ i ih =>
      have hfloorNat : Tendsto (fun n : ℕ => Nat.floor (a n)) atTop atTop :=
        tendsto_nat_floor_atTop.comp ha
      have hfloorReal : Tendsto (fun n : ℕ => ((Nat.floor (a n) : ℕ) : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp hfloorNat
      have htopa := (iterLog_tendsto_atTop i).comp ha
      have htopm := (iterLog_tendsto_atTop i).comp hfloorReal
      have hlogtopa := Real.tendsto_log_atTop.comp htopa
      have hzero := (ih.log one_ne_zero).div_atTop hlogtopa
      have htrend := (tendsto_const_nhds (x := (1 : ℝ))).add hzero
      have hfinal : Tendsto (fun n : ℕ =>
          iterLog (i + 1) (Nat.floor (a n)) / iterLog (i + 1) (a n))
          atTop (𝓝 (1 + 0)) := by
        apply htrend.congr'
        filter_upwards [htopa.eventually_gt_atTop 1, htopm.eventually_gt_atTop 0] with n han hmn
        simp only [Function.comp_def] at han hmn ⊢
        rw [show iterLog (i + 1) (Nat.floor (a n)) =
            Real.log (iterLog i (Nat.floor (a n))) from rfl,
          show iterLog (i + 1) (a n) = Real.log (iterLog i (a n)) from rfl]
        rw [Real.log_div hmn.ne' (show iterLog i (a n) ≠ 0 by linarith)]
        field_simp [(Real.log_pos han).ne']
        ring
      simpa using hfinal

private theorem iterLog_div_nat_of_log_ratio {a : ℕ → ℝ} {i : ℕ} (hi : 1 ≤ i)
    (ha : Tendsto a atTop atTop)
    (hlog : Tendsto (fun n : ℕ => Real.log (a n) / Real.log n) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => iterLog i (a n) / iterLog i n) atTop (𝓝 1) := by
  induction i with
  | zero => omega
  | succ j ih =>
      by_cases hj : j = 0
      · subst j
        simpa only [iterLog] using hlog
      have hprev := ih (by omega)
      have htopa := (iterLog_tendsto_atTop j).comp ha
      have htopn := (iterLog_tendsto_atTop j).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
      have hlogtopn := Real.tendsto_log_atTop.comp htopn
      have hzero := (hprev.log one_ne_zero).div_atTop hlogtopn
      have htrend := (tendsto_const_nhds (x := (1 : ℝ))).add hzero
      have hfinal : Tendsto (fun n : ℕ => iterLog (j + 1) (a n) / iterLog (j + 1) n)
          atTop (𝓝 (1 + 0)) := by
        apply htrend.congr'
        filter_upwards [htopa.eventually_gt_atTop 1, htopn.eventually_gt_atTop 1]
          with n han hn
        simp only [Function.comp_def] at han hn ⊢
        rw [show iterLog (j + 1) (a n) = Real.log (iterLog j (a n)) from rfl,
          show iterLog (j + 1) (n : ℝ) = Real.log (iterLog j n) from rfl]
        rw [Real.log_div (show iterLog j (a n) ≠ 0 by linarith)
          (show iterLog j (n : ℝ) ≠ 0 by linarith)]
        field_simp [(Real.log_pos han).ne', (Real.log_pos hn).ne']
        ring
      simpa using hfinal

private theorem iterLogExplicit_div {x y : ℕ → ℝ} {k : ℕ} (hk : 1 ≤ k) {c : ℝ}
    (hc : 0 < c) (hx : Tendsto x atTop atTop) (hy : Tendsto y atTop atTop)
    (hr : ∀ i : ℕ, 1 ≤ i → i ≤ k →
      Tendsto (fun n => iterLog i (x n) / iterLog i (y n)) atTop (𝓝 1)) :
    Tendsto (fun n => iterLogExplicit k c (x n) / iterLogExplicit k c (y n))
      atTop (𝓝 1) := by
  have hs : Tendsto (fun n => (iterLog k (y n) / iterLog k (x n)) ^ 2)
      atTop (𝓝 1) := by
    simpa using ((hr k hk le_rfl).inv₀ one_ne_zero).pow 2
  have hp : Tendsto (fun n => ∏ i ∈ Finset.Icc 1 (k - 1),
      iterLog i (y n) / iterLog i (x n)) atTop (𝓝 1) := by
    have hh := tendsto_finsetProd (Finset.Icc 1 (k - 1)) (fun i hi =>
      (hr i (Finset.mem_Icc.mp hi).1 (by have := (Finset.mem_Icc.mp hi).2; omega)).inv₀
        one_ne_zero)
    simpa using hh
  have hprod := hs.mul hp
  have hfinal : Tendsto (fun n => iterLogExplicit k c (x n) / iterLogExplicit k c (y n))
      atTop (𝓝 (1 * 1)) := by
    apply hprod.congr'
    filter_upwards [hx.eventually_ge_atTop (iterExp k), hy.eventually_ge_atTop (iterExp k)]
      with n hxn hyn
    have hkx : 0 < iterLog k (x n) := by
      linarith [three_le_iterLog_of_iterExp_le hxn le_rfl]
    have hky : 0 < iterLog k (y n) := by
      linarith [three_le_iterLog_of_iterExp_le hyn le_rfl]
    have hpx : 0 < ∏ i ∈ Finset.Icc 1 (k - 1), 1 / iterLog i (x n) := by
      apply Finset.prod_pos
      intro i hi
      have hik : i ≤ k := by have := (Finset.mem_Icc.mp hi).2; omega
      exact div_pos zero_lt_one (by linarith [three_le_iterLog_of_iterExp_le hxn hik])
    have hpy : 0 < ∏ i ∈ Finset.Icc 1 (k - 1), 1 / iterLog i (y n) := by
      apply Finset.prod_pos
      intro i hi
      have hik : i ≤ k := by have := (Finset.mem_Icc.mp hi).2; omega
      exact div_pos zero_lt_one (by linarith [three_le_iterLog_of_iterExp_le hyn hik])
    change (iterLog k (y n) / iterLog k (x n)) ^ 2 *
      (∏ i ∈ Finset.Icc 1 (k - 1), iterLog i (y n) / iterLog i (x n)) =
      (c / (iterLog k (x n)) ^ 2 *
        ∏ i ∈ Finset.Icc 1 (k - 1), 1 / iterLog i (x n)) /
      (c / (iterLog k (y n)) ^ 2 * ∏ i ∈ Finset.Icc 1 (k - 1), 1 / iterLog i (y n))
    rw [Finset.prod_div_distrib]
    have hxi (i : ℕ) (hi : i ∈ Finset.Icc 1 (k - 1)) : iterLog i (x n) ≠ 0 := by
      have hik : i ≤ k := by have := (Finset.mem_Icc.mp hi).2; omega
      exact (by linarith [three_le_iterLog_of_iterExp_le hxn hik])
    have hyi (i : ℕ) (hi : i ∈ Finset.Icc 1 (k - 1)) : iterLog i (y n) ≠ 0 := by
      have hik : i ≤ k := by have := (Finset.mem_Icc.mp hi).2; omega
      exact (by linarith [three_le_iterLog_of_iterExp_le hyn hik])
    have hPx : 0 < ∏ i ∈ Finset.Icc 1 (k - 1), iterLog i (x n) :=
      Finset.prod_pos (fun i hi => by
        have hik : i ≤ k := by have := (Finset.mem_Icc.mp hi).2; omega
        linarith [three_le_iterLog_of_iterExp_le hxn hik])
    have hPy : 0 < ∏ i ∈ Finset.Icc 1 (k - 1), iterLog i (y n) :=
      Finset.prod_pos (fun i hi => by
        have hik : i ≤ k := by have := (Finset.mem_Icc.mp hi).2; omega
        linarith [three_le_iterLog_of_iterExp_le hyn hik])
    field_simp [hc.ne', hkx.ne', hky.ne', hPx.ne', hPy.ne']
    simp only [one_div]
    rw [Finset.prod_inv_distrib, Finset.prod_inv_distrib]
    field_simp [hPx.ne', hPy.ne']
  simpa using hfinal

/-- Example 2.3(ii): logarithmic and multiplicative asymptotics of every scale. -/
theorem example23_ii_scale (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ < 1) {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hmeas : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1)) {k : ℕ} (hk : 2 ≤ k) {c : ℝ} (hc : 0 < c)
    (hL : Tendsto (fun n : ℕ => L n /
      (c / (iterLog k n) ^ 2 * ∏ i ∈ Finset.Icc 1 (k - 1), 1 / iterLog i n))
      atTop (𝓝 1)) {a : ℕ → ℝ}
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => Real.log (a n) / Real.log n) atTop (𝓝 1) ∧
      Tendsto (fun n : ℕ => a n / ((n : ℝ) * L n)) atTop (𝓝 1) := by
  have hk1 : 1 ≤ k := by omega
  have hlit : IsSubcriticalCauchyOffspring μ := ⟨hm, L, hpos, hsv, hlocal⟩
  have hat := scaling_tendsto_atTop μ hlit ha
  have hsub := scaling_div_nat_tendsto_zero μ hlit ha
  have hscale := scaling_div_mul_tendsto_one μ hm hpos hmeas hsv hlocal ha
  have hle := floor_le_nat_of_scaling hat hsub
  have hfloorNat : Tendsto (fun n : ℕ => Nat.floor (a n)) atTop atTop :=
    tendsto_nat_floor_atTop.comp hat
  have hfloorReal : Tendsto (fun n : ℕ => ((Nat.floor (a n) : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hfloorNat
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlognat : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp hnat
  have hloga : Tendsto (fun n : ℕ => Real.log (a n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hat
  have hlogModelRatio := (hL.comp hfloorNat).log one_ne_zero |>.div_atTop hlognat
  have hlogK : Tendsto (fun n : ℕ =>
      Real.log (iterLog k (Nat.floor (a n))) / Real.log n) atTop (𝓝 0) :=
    log_iterLog_floor_div_log_nat hk1 le_rfl hat hle
  have hlogsum : Tendsto (fun n : ℕ => ∑ i ∈ Finset.Icc 1 (k - 1),
      Real.log (iterLog i (Nat.floor (a n))) / Real.log n) atTop (𝓝 0) := by
    have hh := tendsto_finsetSum (Finset.Icc 1 (k - 1)) (fun i hi =>
      log_iterLog_floor_div_log_nat (a := a) (k := k) (i := i)
        (Finset.mem_Icc.mp hi).1 (by have := (Finset.mem_Icc.mp hi).2; omega) hat hle)
    simpa using hh
  have hconst : Tendsto (fun _n : ℕ => Real.log c / Real.log (_n : ℕ)) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := Real.log c)).div_atTop hlognat
  have hmodelLog : Tendsto (fun n : ℕ => Real.log (iterLogExplicit k c (Nat.floor (a n))) /
      Real.log n) atTop (𝓝 0) := by
    have hh := (hconst.sub (hlogK.const_mul 2)).sub hlogsum
    have hfinal : Tendsto (fun n : ℕ => Real.log (iterLogExplicit k c (Nat.floor (a n))) /
        Real.log n) atTop (𝓝 (0 - 2 * 0 - 0)) := by
      apply hh.congr'
      filter_upwards [hfloorReal.eventually_ge_atTop (iterExp k),
        hlognat.eventually_gt_atTop 0] with n hm hn
      have hposi (i : ℕ) (hik : i ≤ k) : 0 < iterLog i (Nat.floor (a n)) := by
        linarith [three_le_iterLog_of_iterExp_le hm hik]
      have hp : 0 < ∏ i ∈ Finset.Icc 1 (k - 1), 1 / iterLog i (Nat.floor (a n)) := by
        apply Finset.prod_pos
        intro i hi
        exact div_pos zero_lt_one (hposi i (by have := (Finset.mem_Icc.mp hi).2; omega))
      simp only [iterLogExplicit]
      rw [Real.log_mul (div_ne_zero (ne_of_gt hc) (pow_ne_zero 2 (hposi k le_rfl).ne')) hp.ne',
        Real.log_div hc.ne' (pow_ne_zero 2 (hposi k le_rfl).ne'), Real.log_pow,
        Real.log_prod (fun i hi => (div_ne_zero (ne_of_gt zero_lt_one)
          (hposi i (by have := (Finset.mem_Icc.mp hi).2; omega)).ne'))]
      simp only [one_div, Real.log_inv]
      field_simp [hn.ne']
      rw [Finset.mul_sum]
      have hcancel : (∑ i ∈ Finset.Icc 1 (k - 1),
          Real.log n * (Real.log (iterLog i (Nat.floor (a n))) / Real.log n)) =
          ∑ i ∈ Finset.Icc 1 (k - 1), Real.log (iterLog i (Nat.floor (a n))) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← mul_div_assoc]
        exact mul_div_cancel_left₀ _ hn.ne'
      rw [hcancel]
      simp only [Finset.sum_neg_distrib]
      ring
    simpa using hfinal
  have hfloorLog : Tendsto (fun n : ℕ => Real.log (L (Nat.floor (a n))) / Real.log n)
      atTop (𝓝 0) := by
    have hh := hlogModelRatio.add hmodelLog
    have hfinal : Tendsto (fun n : ℕ => Real.log (L (Nat.floor (a n))) / Real.log n)
        atTop (𝓝 (0 + 0)) := by
      apply hh.congr'
      filter_upwards [hfloorReal.eventually_ge_atTop (iterExp k),
        hlognat.eventually_gt_atTop 0] with n hm hn
      have hLm : 0 < L (Nat.floor (a n)) := hpos _ ((iterExp_pos k).trans_le hm)
      have hM : 0 < iterLogExplicit k c (Nat.floor (a n)) := by
        apply mul_pos
        · exact div_pos hc (sq_pos_of_pos (by
            linarith [three_le_iterLog_of_iterExp_le hm le_rfl]))
        · apply Finset.prod_pos
          intro i hi
          exact div_pos zero_lt_one (by
            have hik : i ≤ k := by have := (Finset.mem_Icc.mp hi).2; omega
            linarith [three_le_iterLog_of_iterExp_le hm hik])
      dsimp only [Function.comp_def]
      change Real.log (L (Nat.floor (a n)) / iterLogExplicit k c (Nat.floor (a n))) /
          Real.log n + Real.log (iterLogExplicit k c (Nat.floor (a n))) / Real.log n = _
      rw [Real.log_div hLm.ne' hM.ne']
      field_simp [hn.ne']
      ring
    simpa using hfinal
  have hlogL := log_L_div_log_of_floor hpos hmeas hsv hat hfloorLog
  have hlogratio := scaling_log_div_log_of_log_L μ hm hpos hmeas hsv hlocal ha hlogL
  have hLratio : Tendsto (fun n : ℕ => L (a n) / L n) atTop (𝓝 1) := by
    let M : ℝ → ℝ := iterLogExplicit k c
    have hmodelNat : Tendsto (fun n : ℕ => L n / M n) atTop (𝓝 1) := by
      simpa only [M, iterLogExplicit] using hL
    have hmodelFloorA : Tendsto (fun n : ℕ => M (Nat.floor (a n)) / M (a n))
        atTop (𝓝 1) := by
      apply iterLogExplicit_div hk1 hc hfloorReal hat
      intro i hi hik
      exact iterLog_floor_div_iterLog i hat
    have hmodelAN : Tendsto (fun n : ℕ => M (a n) / M n) atTop (𝓝 1) := by
      apply iterLogExplicit_div hk1 hc hat hnat
      intro i hi hik
      exact iterLog_div_nat_of_log_ratio hi hat hlogratio
    apply L_div_nat_of_explicit_model (M := M) hpos hmeas hsv hat
      hmodelNat hmodelFloorA hmodelAN
    filter_upwards [hfloorReal.eventually_ge_atTop (iterExp k),
      hat.eventually_ge_atTop (iterExp k), hnat.eventually_ge_atTop (iterExp k)]
      with n hm han hn
    have hposM {x : ℝ} (hx : iterExp k ≤ x) : 0 < iterLogExplicit k c x := by
      apply mul_pos
      · exact div_pos hc (sq_pos_of_pos (by
          linarith [three_le_iterLog_of_iterExp_le hx le_rfl]))
      · apply Finset.prod_pos
        intro i hi
        exact div_pos zero_lt_one (by
          have hik : i ≤ k := by have := (Finset.mem_Icc.mp hi).2; omega
          linarith [three_le_iterLog_of_iterExp_le hx hik])
    exact ⟨hposM hm, hposM han, hposM hn⟩
  have hfinal : Tendsto (fun n : ℕ => a n / ((n : ℝ) * L n)) atTop (𝓝 (1 * 1)) := by
    have hh := hscale.mul hLratio
    apply hh.congr'
    filter_upwards [hat.eventually_gt_atTop 0, eventually_gt_atTop (0 : ℕ),
      hlognat.eventually_gt_atTop 0] with n han hn hlogn
    have hLa : 0 < L (a n) := hpos _ han
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hLn : 0 < L n := hpos _ hnR
    field_simp [hLa.ne', hLn.ne', hnR.ne']
  exact ⟨hlogratio, by simpa using hfinal⟩

end
end SubcriticalCauchy.Bienayme
