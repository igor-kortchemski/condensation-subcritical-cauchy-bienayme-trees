module

public import SubcriticalCauchy.ExampleScales
public import SubcriticalCauchy.ExampleScalesIIIAux

import Mathlib.Tactic.Linarith


@[expose] public section

open Filter MeasureTheory Asymptotics
open scoped Topology BigOperators

namespace SubcriticalCauchy.Bienayme

noncomputable section

/-- Example 2.3(iii): the integrated tail for `L(n) ∼ c exp (-(log n)^β)`. -/
theorem example23_iii_ellStar {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x) {c β : ℝ} (hc : 0 < c)
    (hβ0 : 0 < β) (hβ1 : β < 1)
    (hL : Tendsto (fun n : ℕ => L n / (c * Real.exp (-(Real.log n) ^ β)))
      atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => ellStar L n /
      (c / β * (Real.log n) ^ (1 - β) * Real.exp (-(Real.log n) ^ β)))
      atTop (𝓝 1) := by
  simpa only [expLogPrimitive] using expLog_ellStar_tendsto hpos hc hβ0 hβ1 hL


private theorem expLog_one_isBigO {v : ℕ → ℝ} {p : ℝ}
    (hvpos : ∀ᶠ n : ℕ in atTop, 0 < v n)
    (hv : Tendsto (fun n => v n ^ p) atTop atTop) :
    (fun _n : ℕ => (1 : ℝ)) =O[atTop] (fun n => v n ^ p) := by
  apply IsBigO.of_bound 1
  filter_upwards [hv.eventually_ge_atTop 1, hvpos] with n hn hvn
  have hp : 0 ≤ v n ^ p := Real.rpow_nonneg hvn.le p
  simpa [Real.norm_of_nonneg hp] using hn

private theorem expLog_scaling_log_error (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ < 1) {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hmeas : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1)) {c β : ℝ} (hc : 0 < c)
    (hβ0 : 0 < β) (hβ : β < 2 / 3)
    (hL : Tendsto (fun n : ℕ => L n / (c * Real.exp (-(Real.log n) ^ β)))
      atTop (𝓝 1)) {a : ℕ → ℝ}
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => Real.log (a n) - Real.log n - Real.log c +
      (Real.log n) ^ β - β * (Real.log n) ^ (2 * β - 1)) atTop (𝓝 0) := by
  have hβ1 : β < 1 := by linarith
  have hlit : IsSubcriticalCauchyOffspring μ := ⟨hm, L, hpos, hsv, hlocal⟩
  have hat : Tendsto a atTop atTop := scaling_tendsto_atTop μ hlit ha
  have hscale := scaling_div_mul_tendsto_one μ hm hpos hmeas hsv hlocal ha
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlognat : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp hnat
  have hloga : Tendsto (fun n : ℕ => Real.log (a n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hat
  have hpowβ : Tendsto (fun n : ℕ => (Real.log n) ^ β) atTop atTop :=
    (tendsto_rpow_atTop hβ0).comp hlognat
  have hratio : Tendsto (fun n : ℕ => Real.log (a n) / Real.log n) atTop (𝓝 1) :=
    expLog_scaling_log_ratio μ hm hpos hmeas hsv hlocal hc hβ0 hβ1 hL ha
  have hε1 : Tendsto (fun n : ℕ =>
      Real.log (a n) - Real.log n - Real.log (L (a n))) atTop (𝓝 0) := by
    have h := hscale.log one_ne_zero
    have h0 : Tendsto (fun n : ℕ => Real.log (a n / ((n : ℝ) * L (a n))))
        atTop (𝓝 0) := by simpa using h
    apply h0.congr'
    filter_upwards [hat.eventually_gt_atTop 0, eventually_gt_atTop (0 : ℕ)] with n han hn
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    rw [Real.log_div han.ne' (mul_ne_zero hn0.ne' (hpos _ han).ne'),
      Real.log_mul hn0.ne' (hpos _ han).ne']
    ring
  have hε2 := tendsto_log_expLog_model hpos hmeas hsv hc hβ0 hβ1 hL hat
  have hE : Tendsto (fun n : ℕ =>
      (Real.log (a n) - Real.log n) - Real.log c + (Real.log (a n)) ^ β)
      atTop (𝓝 0) := by
    have h := hε1.add hε2
    have h0 : Tendsto (fun n : ℕ =>
      (Real.log (a n) - Real.log n - Real.log (L (a n))) +
        (Real.log (L (a n)) - Real.log c + (Real.log (a n)) ^ β)) atTop (𝓝 0) := by
      simpa using h
    apply h0.congr'
    filter_upwards with n
    ring
  let A : ℕ → ℝ := fun n => Real.log (a n)
  let v : ℕ → ℝ := fun n => Real.log n
  let d : ℕ → ℝ := fun n => A n - v n
  have hA : ∀ᶠ n : ℕ in atTop, 0 < A n := hloga.eventually_gt_atTop 0
  have hv : ∀ᶠ n : ℕ in atTop, 0 < v n := hlognat.eventually_gt_atTop 0
  have hABig : (fun n => A n ^ β) =O[atTop] (fun n => v n ^ β) := by
    have hrpow : Tendsto (fun n : ℕ => (A n / v n) ^ β) atTop (𝓝 1) := by
      have h := hratio.rpow_const (p := β) (Or.inl one_ne_zero)
      simpa using h
    have h := (hrpow.isBigO_one ℝ).mul (isBigO_refl (fun n => v n ^ β) atTop)
    apply h.congr' _ (by filter_upwards with n; simp)
    filter_upwards [hA, hv] with n hAn hvn
    rw [Real.div_rpow hAn.le hvn.le]
    field_simp [(Real.rpow_pos_of_pos hvn β).ne']
  have hOne : (fun _n : ℕ => (1 : ℝ)) =O[atTop] (fun n => v n ^ β) :=
    expLog_one_isBigO hv hpowβ
  have hdBig : d =O[atTop] (fun n => v n ^ β) := by
    have h := ((hE.isBigO_one ℝ).trans hOne).add
      ((tendsto_const_nhds (x := Real.log c)).isBigO_one ℝ |>.trans hOne) |>.sub hABig
    apply h.congr' _ EventuallyEq.rfl
    filter_upwards with n
    dsimp [d, A, v]
    ring
  have hTay := isBigO_rpow_sub_rpow_sub_linear β hA hv hratio
  have hRBig : (fun n => A n ^ β - v n ^ β - β * v n ^ (β - 1) * d n) =O[atTop]
      (fun n => v n ^ (3 * β - 2)) := by
    have hs := (isBigO_refl (fun n => v n ^ (β - 2)) atTop).mul (hdBig.pow 2)
    have ht := hTay.trans hs
    apply ht.congr' EventuallyEq.rfl
    filter_upwards [hv] with n hvn
    rw [← Real.rpow_natCast, ← Real.rpow_mul hvn.le, ← Real.rpow_add hvn]
    congr 1
    norm_num
    ring
  have hlinBig : (fun n => β * v n ^ (β - 1) * d n) =O[atTop]
      (fun n => β * v n ^ (2 * β - 1)) := by
    have h := (isBigO_refl (fun n => β * v n ^ (β - 1)) atTop).mul hdBig
    apply h.congr' EventuallyEq.rfl
    filter_upwards [hv] with n hvn
    rw [show 2 * β - 1 = (β - 1) + β by ring, Real.rpow_add hvn]
    ring
  have hdeltaBig : (fun n => A n ^ β - v n ^ β) =O[atTop]
      (fun n => v n ^ (3 * β - 2) + β * v n ^ (2 * β - 1)) := by
    have h := hRBig.add_add hlinBig
    apply h.congr' _
    · filter_upwards [hv] with n hvn
      have h1 : 0 ≤ v n ^ (3 * β - 2) := Real.rpow_nonneg hvn.le _
      have h2 : 0 ≤ β * v n ^ (2 * β - 1) := by positivity
      simp only [Real.norm_of_nonneg h1, Real.norm_of_nonneg h2]
    · filter_upwards with n
      ring
  have hqBig : (fun n => d n + v n ^ β) =O[atTop]
      (fun n => 1 + 1 + (v n ^ (3 * β - 2) + β * v n ^ (2 * β - 1))) := by
    have h := ((hE.isBigO_one ℝ).add_add
      ((tendsto_const_nhds (x := Real.log c)).isBigO_one ℝ)).add_add hdeltaBig.neg_left
    apply h.congr' _
    · filter_upwards [hv] with n hvn
      have h1 : 0 ≤ v n ^ (3 * β - 2) := Real.rpow_nonneg hvn.le _
      have h2 : 0 ≤ β * v n ^ (2 * β - 1) := by positivity
      have h3 : 0 ≤ v n ^ (3 * β - 2) + β * v n ^ (2 * β - 1) := by positivity
      simp only [norm_one, Real.norm_of_nonneg h3]
      norm_num
    · filter_upwards with n
      dsimp [d, A, v]
      ring
  have hqBig' : (fun n => β * v n ^ (β - 1) * (d n + v n ^ β)) =O[atTop]
      (fun n => β * v n ^ (β - 1) *
        (1 + 1 + (v n ^ (3 * β - 2) + β * v n ^ (2 * β - 1)))) :=
    (isBigO_refl (fun n => β * v n ^ (β - 1)) atTop).mul hqBig
  have hfinalBig : (fun n => A n ^ β - v n ^ β + β * v n ^ (2 * β - 1)) =O[atTop]
      (fun n => v n ^ (3 * β - 2) + β * v n ^ (β - 1) *
        (1 + 1 + (v n ^ (3 * β - 2) + β * v n ^ (2 * β - 1)))) := by
    have h := hRBig.add_add hqBig'
    apply h.congr' _
    · filter_upwards [hv] with n hvn
      have h1 : 0 ≤ v n ^ (3 * β - 2) := by positivity
      have h2 : 0 ≤ β * v n ^ (β - 1) *
          (1 + 1 + (v n ^ (3 * β - 2) + β * v n ^ (2 * β - 1))) := by positivity
      rw [Real.norm_of_nonneg h1, Real.norm_of_nonneg h2]
    · filter_upwards [hv] with n hvn
      have hp : v n ^ (2 * β - 1) = v n ^ (β - 1) * v n ^ β := by
        rw [← Real.rpow_add hvn]
        congr 1
        ring
      linear_combination (-β) * hp
  have hpowZero (p : ℝ) (hp : p < 0) : Tendsto (fun n => v n ^ p) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (show 0 < -p by linarith)).comp hlognat
    have he : -(-p) = p := neg_neg p
    rw [he] at h
    simpa only [Function.comp_def, v] using h
  have hright : Tendsto (fun n : ℕ => v n ^ (3 * β - 2) + β * v n ^ (β - 1) *
      (1 + 1 + (v n ^ (3 * β - 2) + β * v n ^ (2 * β - 1)))) atTop (𝓝 0) := by
    have hlin : Tendsto (fun n : ℕ => β * v n ^ (β - 1) +
        (β * v n ^ (β - 1) + (β * v n ^ (4 * β - 3) +
          β ^ 2 * v n ^ (3 * β - 2)))) atTop (𝓝 0) := by
      have h := ((hpowZero _ (by linarith : β - 1 < 0)).const_mul β).add
        (((hpowZero _ (by linarith : β - 1 < 0)).const_mul β).add
          (((hpowZero _ (by linarith : 4 * β - 3 < 0)).const_mul β).add
            ((hpowZero _ (by linarith : 3 * β - 2 < 0)).const_mul (β ^ 2))))
      simpa using h
    have h := (hpowZero _ (by linarith : 3 * β - 2 < 0)).add hlin
    have h0 : Tendsto (fun n : ℕ => v n ^ (3 * β - 2) +
        (β * v n ^ (β - 1) + (β * v n ^ (β - 1) +
          (β * v n ^ (4 * β - 3) + β ^ 2 * v n ^ (3 * β - 2)))))
        atTop (𝓝 0) := by simpa using h
    apply h0.congr'
    filter_upwards [hv] with n hvn
    have he4 : v n ^ (4 * β - 3) = v n ^ (β - 1) * v n ^ (3 * β - 2) := by
      rw [← Real.rpow_add hvn]
      congr 1
      ring
    have he3 : β ^ 2 * v n ^ (3 * β - 2) =
        β ^ 2 * (v n ^ (β - 1) * v n ^ (2 * β - 1)) := by
      rw [← Real.rpow_add hvn]
      congr 2
      ring
    rw [he4]
    rw [he3]
    ring
  have hrefined : Tendsto (fun n : ℕ => A n ^ β - v n ^ β + β * v n ^ (2 * β - 1))
      atTop (𝓝 0) := hfinalBig.trans_tendsto hright
  have h := (hε1.add hε2).sub hrefined
  have h0 : Tendsto (fun n : ℕ =>
      (Real.log (a n) - Real.log n - Real.log (L (a n))) +
        (Real.log (L (a n)) - Real.log c + (Real.log (a n)) ^ β) -
          (A n ^ β - v n ^ β + β * v n ^ (2 * β - 1))) atTop (𝓝 0) := by
    simpa using h
  have hfinal : Tendsto (fun n : ℕ => Real.log (a n) - Real.log n - Real.log c +
      (Real.log n) ^ β - β * (Real.log n) ^ (2 * β - 1)) atTop (𝓝 0) := by
    apply h0.congr'
    filter_upwards with n
    dsimp [A, v]
    ring
  simpa using hfinal


/-- Example 2.3(iii): the scale asymptotic for `β < 1/2`. -/
theorem example23_iii_scale_small (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ < 1) {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hmeas : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1)) {c β : ℝ} (hc : 0 < c)
    (hβ0 : 0 < β) (hβ : β < 1 / 2)
    (hL : Tendsto (fun n : ℕ => L n / (c * Real.exp (-(Real.log n) ^ β)))
      atTop (𝓝 1)) {a : ℕ → ℝ}
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => a n /
      (c * (n : ℝ) * Real.exp (-(Real.log n) ^ β))) atTop (𝓝 1) := by
  have hβ1 : β < 1 := by linarith
  have hlogmid := expLog_scaling_log_error μ hm hpos hmeas hsv hlocal hc hβ0
    (show β < 2 / 3 by linarith) hL ha
  have hlognat : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hcorr : Tendsto (fun n : ℕ => β * (Real.log n) ^ (2 * β - 1)) atTop (𝓝 0) := by
    have hp := (tendsto_rpow_neg_atTop (show 0 < 1 - 2 * β by linarith)).comp hlognat
    have he : -(1 - 2 * β) = 2 * β - 1 := by ring
    rw [he] at hp
    have hp0 : Tendsto (fun n : ℕ => (Real.log n) ^ (2 * β - 1)) atTop (𝓝 0) := by
      simpa only [Function.comp_def] using hp
    have h := hp0.const_mul β
    simpa using h
  have hlog : Tendsto (fun n : ℕ => Real.log (a n) - Real.log n - Real.log c +
      (Real.log n) ^ β) atTop (𝓝 0) := by
    have h := hlogmid.add hcorr
    have h0 : Tendsto (fun n : ℕ =>
        (Real.log (a n) - Real.log n - Real.log c + (Real.log n) ^ β -
          β * (Real.log n) ^ (2 * β - 1)) + β * (Real.log n) ^ (2 * β - 1))
        atTop (𝓝 0) := by simpa using h
    apply h0.congr'
    filter_upwards with n
    ring
  have h := Real.tendsto_exp_nhds_zero_nhds_one.comp hlog
  have h0 : Tendsto (fun n : ℕ => Real.exp
      (Real.log (a n) - Real.log n - Real.log c + (Real.log n) ^ β))
      atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.exp_zero] using h
  apply h0.congr'
  have hlit : IsSubcriticalCauchyOffspring μ := ⟨hm, L, hpos, hsv, hlocal⟩
  have hat : Tendsto a atTop atTop := scaling_tendsto_atTop μ hlit ha
  filter_upwards [hat.eventually_gt_atTop 0, eventually_gt_atTop (0 : ℕ)] with n han hn
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [Real.exp_add, Real.exp_sub, Real.exp_sub, Real.exp_log han,
    Real.exp_log hn0, Real.exp_log hc, Real.exp_neg]
  field_simp [Real.exp_ne_zero]

/-- Example 2.3(iii): the scale asymptotic for `1/2 ≤ β < 2/3`. -/
theorem example23_iii_scale_mid (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ < 1) {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hmeas : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1)) {c β : ℝ} (hc : 0 < c)
    (hβ0 : 0 < β) (_hβlo : 1 / 2 ≤ β) (hβ : β < 2 / 3)
    (hL : Tendsto (fun n : ℕ => L n / (c * Real.exp (-(Real.log n) ^ β)))
      atTop (𝓝 1)) {a : ℕ → ℝ}
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => a n / (c * (n : ℝ) *
      Real.exp (-(Real.log n) ^ β + β * (Real.log n) ^ (2 * β - 1))))
      atTop (𝓝 1) := by
  have hlog := expLog_scaling_log_error μ hm hpos hmeas hsv hlocal hc hβ0 hβ hL ha
  have h := Real.tendsto_exp_nhds_zero_nhds_one.comp hlog
  have h0 : Tendsto (fun n : ℕ => Real.exp
      (Real.log (a n) - Real.log n - Real.log c + (Real.log n) ^ β -
        β * (Real.log n) ^ (2 * β - 1))) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.exp_zero] using h
  apply h0.congr'
  have hlit : IsSubcriticalCauchyOffspring μ := ⟨hm, L, hpos, hsv, hlocal⟩
  have hat : Tendsto a atTop atTop := scaling_tendsto_atTop μ hlit ha
  filter_upwards [hat.eventually_gt_atTop 0, eventually_gt_atTop (0 : ℕ)] with n han hn
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [Real.exp_sub, Real.exp_add, Real.exp_sub, Real.exp_sub, Real.exp_log han,
    Real.exp_log hn0, Real.exp_log hc,
    show -(Real.log n) ^ β + β * (Real.log n) ^ (2 * β - 1) =
      -((Real.log n) ^ β - β * (Real.log n) ^ (2 * β - 1)) by ring,
    Real.exp_neg, Real.exp_sub]
  field_simp [Real.exp_ne_zero]

end
end SubcriticalCauchy.Bienayme
