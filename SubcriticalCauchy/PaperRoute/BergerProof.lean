module

public import SubcriticalCauchy.PaperRoute.BergerProofLower
public import SubcriticalCauchy.PaperRoute.BergerSmallMax
public import SubcriticalCauchy.PaperRoute.BergerFukNagaev

import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Berger's local limit from the small-maxima estimate
-/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Topology BigOperators

namespace SubcriticalCauchy.Bienayme

noncomputable section

attribute [local instance] Classical.propDecidable

local instance bergerProofIncrementLawIsProbability (μ : Measure ℕ)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (incrementLaw μ) := by
  unfold incrementLaw
  infer_instance

/-- Berger's local limit, conditional only on the small-maxima estimate. -/
theorem berger_local_limit_of_smallMax (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ)
    (hF : ∀ (a : ℕ → ℝ),
      Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal) atTop (𝓝 1) →
      ∀ τ : ℝ, 0 < τ → ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ ∃ N : ℕ, ∃ R : ℝ,
        ∀ n : ℕ, N ≤ n → ∀ z : ℤ, R * a n ≤ z →
          ((Measure.pi fun _ : Fin n => incrementLaw μ)
              {x | ∑ i, x i = z + ⌊centering μ a n⌋ ∧ ∀ i, (x i : ℝ) ≤ δ * z}).toReal
            ≤ τ * ((n : ℝ) * (incrementLaw μ {z}).toReal)) (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal) atTop (𝓝 1)) :
    ∀ τ > 0, ∃ N : ℕ, ∃ R : ℝ, ∀ n ≥ N, ∀ z : ℤ, R * a n ≤ z →
      |((Measure.pi fun _ : Fin n => incrementLaw μ)
            {x | ∑ i, x i = z + ⌊centering μ a n⌋}).toReal /
          ((n : ℝ) * (incrementLaw μ {z}).toReal) - 1| ≤ τ := by
  intro τ hτ
  classical
  obtain ⟨hm, L, hpos, hsv, hmeas, hlocal⟩ := hμ
  let t := min τ 1
  have hτ0 : 0 < τ := by assumption
  have ht0 : 0 < t := lt_min hτ0 zero_lt_one
  have ht1 : t ≤ 1 := min_le_right _ _
  have htτ : t ≤ τ := min_le_left _ _
  have hlit : IsSubcriticalCauchyOffspring μ := ⟨hm, L, hpos, hsv, hlocal⟩
  have haTop : Tendsto a atTop atTop := scaling_tendsto_atTop μ hlit ha
  have hμagain : IsMeasurableSubcriticalCauchyOffspring μ :=
    ⟨hm, L, hpos, hsv, hmeas, hlocal⟩
  let η := t / 48
  have hη : 0 < η := by dsimp [η]; positivity
  let ε := min (1 / 4 : ℝ) η
  have hε : 0 < ε := lt_min (by norm_num) hη
  have hε4 : ε ≤ 1 / 4 := min_le_left _ _
  have hεη : ε ≤ η := min_le_right _ _
  have hε1 : ε < 1 / 2 := hε4.trans_lt (by norm_num)
  have hεa : 0 < 1 - ε := by linarith
  let Au := 1 / (1 - ε) ^ 2 + η
  have hAu_le : Au ≤ 1 + t / 3 := by
    have hquad : 0 ≤ 6 - 15 * ε + 8 * ε ^ 2 := by
      nlinarith only [sq_nonneg ε, hε4]
    have hpoly : 0 ≤ (1 + 8 * ε) * (1 - ε) ^ 2 - 1 := by
      have hid : (1 + 8 * ε) * (1 - ε) ^ 2 - 1 =
          ε * (6 - 15 * ε + 8 * ε ^ 2) := by ring
      rw [hid]
      positivity
    have hratio : 1 / (1 - ε) ^ 2 ≤ 1 + 8 * ε := by
      have hsq : 0 < (1 - ε) ^ 2 := sq_pos_of_pos hεa
      rw [div_le_iff₀ hsq]
      linarith only [hpoly]
    have hεt : 8 * ε + η ≤ t / 3 := by
      dsimp [η] at hεη ⊢
      linarith
    dsimp [Au]
    linarith
  let Bl := (1 + ε) ^ 2 + η
  have hBl : 0 < Bl := by dsimp [Bl]; positivity
  have hBl_le : Bl ≤ 1 + t / 3 := by
    have hε1' : ε ≤ 1 := hε4.trans (by norm_num)
    have hs : (1 + ε) ^ 2 ≤ 1 + 3 * ε := by nlinarith [sq_nonneg ε]
    have ht : 3 * ε + η ≤ t / 3 := by
      dsimp [η] at hεη ⊢
      linarith
    dsimp [Bl]
    linarith
  let Cl := Bl⁻¹
  have hCl : 0 < Cl := inv_pos.mpr hBl
  have hCl_lower : 1 - t / 3 ≤ Cl := by
    have hprod : (1 - t / 3) * Bl ≤ 1 := by
      calc
        (1 - t / 3) * Bl ≤ (1 - t / 3) * (1 + t / 3) := by
          gcongr
          linarith
        _ = 1 - t ^ 2 / 9 := by ring
        _ ≤ 1 := by nlinarith [sq_nonneg t]
    dsimp [Cl]
    rw [inv_eq_one_div]
    exact (le_div_iff₀ hBl).mpr hprod
  obtain ⟨δ, hδ, hδhalf, N₀, R₀, hsmall⟩ := hF a ha (t / 3) (by positivity)
  have hδ1 : δ ≤ 1 := by linarith
  obtain ⟨C, hC, hCbound⟩ := berger_increment_mass_potter μ hμagain
    (haTop.const_mul_atTop (show 0 < 1 by norm_num)) hδ hδ1
  let κ := min (t / 6) ((t / 3) / C / 2)
  have hκ : 0 < κ := lt_min (by positivity) (by positivity)
  have hκt : κ ≤ t / 6 := min_le_left _ _
  have hκC : 2 * κ ≤ (t / 3) / C := by
    have hh := min_le_right (t / 6) ((t / 3) / C / 2)
    dsimp [κ]
    linarith
  obtain ⟨K₁, hK₁, N₁, hsum₁⟩ :=
    incrementSum_tight_scale μ hm hpos hmeas hsv hlocal ha κ hκ
  obtain ⟨K₂, hK₂, N₂, hmax₂⟩ :=
    incrementMax_tight_scale μ hm hpos hmeas hsv hlocal ha κ hκ
  let K := max K₁ K₂
  have hK : 0 < K := lt_of_lt_of_le hK₁ (le_max_left _ _)
  have hK₁K : K₁ ≤ K := le_max_left _ _
  have hK₂K : K₂ ≤ K := le_max_right _ _
  let R := max 1 (max R₀ (max ((K + 1) / ε) (3 * K)))
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hRR₀ : R₀ ≤ R := (le_max_left R₀ _).trans (le_max_right 1 _)
  have hRε : (K + 1) / ε ≤ R :=
    ((le_max_left ((K + 1) / ε) (3 * K)).trans
      (le_max_right R₀ _)).trans (le_max_right 1 _)
  have hRK : 3 * K ≤ R :=
    ((le_max_right ((K + 1) / ε) (3 * K)).trans
      (le_max_right R₀ _)).trans (le_max_right 1 _)
  have hbase : Tendsto (fun n => R * a n) atTop atTop := haTop.const_mul_atTop hR
  have hbaseLower : Tendsto (fun n => (1 - ε) * (R * a n)) atTop atTop :=
    hbase.const_mul_atTop hεa
  have hnearUpper := berger_increment_mass_ratio_compact μ hμagain
    (a := 1 - ε) (b := 1 + ε) hεa (by linarith) hbase η hη
  have hnearLower := berger_increment_mass_ratio_compact μ hμagain
    (a := (1 + ε)⁻¹) (b := (1 - ε)⁻¹) (inv_pos.mpr (by linarith))
    (inv_anti₀ hεa (by linarith)) hbaseLower η hη
  obtain ⟨M, hM⟩ := eventually_atTop.mp (eventually_mass_pos μ hlit)
  let U := |(offspringMean μ).toReal - 1| + 1
  have hU : 0 < U := by dsimp [U]; positivity
  have hmean := truncatedIncrementMean_tendsto μ
    (ne_top_of_lt (hm.trans ENNReal.one_lt_top)) haTop
  have hmeanAbs : ∀ᶠ n in atTop,
      |truncatedIncrementMean μ (a n)| < U := by
    have hh := hmean.abs.eventually_lt_const (show |(offspringMean μ).toReal - 1| < U by
      dsimp [U]; linarith)
    exact hh
  have hevent : ∀ᶠ n : ℕ in atTop,
      (2 ≤ n ∧ 1 ≤ a n ∧ |truncatedIncrementMean μ (a n)| < U ∧ U + 1 ≤ a n) ∧
      (M : ℝ) ≤ R * a n ∧ (M : ℝ) ≤ (1 - ε) * (R * a n) := by
    have hall := (eventually_ge_atTop 2).and ((haTop.eventually_ge_atTop 1).and
      (hmeanAbs.and ((haTop.eventually_ge_atTop (U + 1)).and
        ((hbase.eventually_ge_atTop (M : ℝ)).and
          (hbaseLower.eventually_ge_atTop (M : ℝ))))))
    filter_upwards [hall] with n hn
    rcases hn with ⟨hn, ha1, hmabs, haU, hMR, hML⟩
    exact ⟨⟨hn, ha1, hmabs, haU⟩, hMR, hML⟩
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.mp hevent
  obtain ⟨N₄, hN₄⟩ := eventually_atTop.mp hnearUpper
  obtain ⟨N₅, hN₅⟩ := eventually_atTop.mp hnearLower
  obtain ⟨N₆, hN₆⟩ := eventually_atTop.mp hCbound
  let N := max N₀ (max N₁ (max N₂ (max N₃ (max N₄ (max N₅ N₆)))))
  refine ⟨N, R, ?_⟩
  intro n hn z hz
  have hn₀ : N₀ ≤ n := by dsimp [N] at hn; omega
  have hn₁ : N₁ ≤ n := by dsimp [N] at hn; omega
  have hn₂ : N₂ ≤ n := by dsimp [N] at hn; omega
  have hn₃ : N₃ ≤ n := by dsimp [N] at hn; omega
  have hn₄ : N₄ ≤ n := by dsimp [N] at hn; omega
  have hn₅ : N₅ ≤ n := by dsimp [N] at hn; omega
  have hn₆ : N₆ ≤ n := by dsimp [N] at hn; omega
  obtain ⟨⟨hn2, ha1, hmU, haU⟩, hMR, hML⟩ := hN₃ n hn₃
  have ha0 : 0 < a n := zero_lt_one.trans_le ha1
  have hzR₀ : R₀ * a n ≤ z := (mul_le_mul_of_nonneg_right hRR₀ ha0.le).trans hz
  have hz0 : (0 : ℝ) < z := by
    have hR1 : 1 ≤ R := le_max_left _ _
    have : (0 : ℝ) < 1 * a n := by simpa using ha0
    exact this.trans_le ((mul_le_mul_of_nonneg_right hR1 ha0.le).trans hz)
  have hzint : (0 : ℤ) ≤ z := by exact_mod_cast hz0.le
  have hzFloor : -1 ≤ z := by omega
  have hzMassNat : M ≤ (z + 1).toNat := by
    have hcast : (((z + 1).toNat : ℕ) : ℝ) = (z : ℝ) + 1 :=
      berger_increment_shift_cast hzFloor
    apply Nat.le_of_lt_succ
    have : (M : ℝ) < (((z + 1).toNat + 1 : ℕ) : ℝ) := by
      push_cast
      rw [hcast]
      exact lt_of_le_of_lt hMR (by linarith)
    exact_mod_cast this
  have hpz : 0 < (incrementLaw μ {z}).toReal := by
    rw [berger_incrementLaw_singleton μ z hzFloor]
    exact ENNReal.toReal_pos (ne_of_gt (hM _ hzMassNat)) (by finiteness)
  have hD : 0 < (n : ℝ) * (incrementLaw μ {z}).toReal := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    positivity
  cases n with
  | zero => omega
  | succ m =>
    let T : ℤ := z + ⌊centering μ a (m + 1)⌋
    let ma := truncatedIncrementMean μ (a (m + 1))
    let d : ℝ := (⌊centering μ a (m + 1)⌋ : ℝ) - (m : ℝ) * ma
    let dev : (Fin m → ℤ) → ℝ := fun y =>
      (∑ i, (y i : ℝ)) - (m : ℝ) * ma
    let Bnear := bergerNearSet ε z
    let Bfar := bergerFarSet δ ε z
    let G := bergerGoodSet K (a (m + 1)) z dev
    have hdform : d = (⌊centering μ a (m + 1)⌋ : ℝ) -
        centering μ a (m + 1) + ma := by
      dsimp [d, ma, centering]
      push_cast
      ring
    have hfloor : |(⌊centering μ a (m + 1)⌋ : ℝ) - centering μ a (m + 1)| ≤ 1 := by
      rw [abs_le]
      constructor <;>
        linarith [Int.floor_le (centering μ a (m + 1)),
          Int.lt_floor_add_one (centering μ a (m + 1))]
    have hd : |d| < a (m + 1) := by
      have htri : |d| ≤ |(⌊centering μ a (m + 1)⌋ : ℝ) -
          centering μ a (m + 1)| + |ma| := by
        rw [hdform]
        exact abs_add_le _ _
      dsimp [ma] at htri ⊢
      linarith
    have hβ : K * a (m + 1) + |d| < ε * (z : ℝ) := by
      have hscale : (K + 1) * a (m + 1) ≤ ε * (z : ℝ) := by
        have hmul : (K + 1) ≤ ε * R := by
          simpa only [mul_comm] using (div_le_iff₀ hε).mp hRε
        calc
          (K + 1) * a (m + 1) ≤ (ε * R) * a (m + 1) := by gcongr
          _ = ε * (R * a (m + 1)) := by ring
          _ ≤ ε * (z : ℝ) := mul_le_mul_of_nonneg_left hz hε.le
      nlinarith
    have hKz : K * a (m + 1) < (z : ℝ) / 2 := by
      have hscale : 3 * K * a (m + 1) ≤ (z : ℝ) := by
        calc
          3 * K * a (m + 1) ≤ R * a (m + 1) := by gcongr
          _ ≤ (z : ℝ) := hz
      have hKa : 0 < K * a (m + 1) := mul_pos hK ha0
      nlinarith only [hscale, hKa]
    have hcenter (y : Fin m → ℤ) :
        ((T - ∑ i, y i : ℤ) : ℝ) = (z : ℝ) + d - dev y := by
      dsimp [T, d, dev, ma]
      push_cast
      ring
    have hspec := berger_residual_spec T z dev δ ε K (a (m + 1)) d
      hcenter hε1 hz0 hβ hKz
    have hnearGood : ∀ y ∈ G, T - ∑ i, y i ∈ Bnear := by
      simpa only [G, Bnear] using hspec.1
    have hstrict : ∀ y ∈ G, ∀ i, y i < T - ∑ k, y k := by
      simpa only [G] using hspec.2.1
    have hsumK : ((Measure.pi fun _ : Fin m => incrementLaw μ)
        {y | K * a (m + 1) < |dev y|}).toReal ≤ κ := by
      have hsub : {y : Fin m → ℤ | K * a (m + 1) < |dev y|} ⊆
          {y | K₁ * a (m + 1) < |dev y|} := by
        intro y hy
        exact (mul_le_mul_of_nonneg_right hK₁K ha0.le).trans_lt hy
      calc
        _ ≤ ((Measure.pi fun _ : Fin m => incrementLaw μ)
            {y | K₁ * a (m + 1) < |dev y|}).toReal := measureReal_mono hsub
        _ ≤ κ := by
          simpa only [dev, ma] using hsum₁ (m + 1) hn₁ m (Nat.le_succ m)
    have hmaxK : ((Measure.pi fun _ : Fin m => incrementLaw μ)
        {y | ∃ i, K * a (m + 1) < (y i : ℝ)}).toReal ≤ κ := by
      have hsub : {y : Fin m → ℤ | ∃ i, K * a (m + 1) < (y i : ℝ)} ⊆
          {y | ∃ i, K₂ * a (m + 1) < (y i : ℝ)} := by
        rintro y ⟨i, hi⟩
        exact ⟨i, (mul_le_mul_of_nonneg_right hK₂K ha0.le).trans_lt hi⟩
      calc
        _ ≤ ((Measure.pi fun _ : Fin m => incrementLaw μ)
            {y | ∃ i, K₂ * a (m + 1) < (y i : ℝ)}).toReal := measureReal_mono hsub
        _ ≤ κ := hmax₂ (m + 1) hn₂ m (Nat.le_succ m)
    have hGc : ((Measure.pi fun _ : Fin m => incrementLaw μ) Gᶜ).toReal ≤ 2 * κ := by
      have hsub : Gᶜ ⊆ {y : Fin m → ℤ | K * a (m + 1) < |dev y|} ∪
          {y | ∃ i, K * a (m + 1) < (y i : ℝ)} := by
        simpa only [G] using berger_good_compl_subset K (a (m + 1)) z dev hKz
      apply (measureReal_mono hsub).trans
      apply (measureReal_union_le _ _).trans
      simpa only [Measure.real, two_mul] using add_le_add hsumK hmaxK
    have hGprob : 1 - t / 3 ≤
        ((Measure.pi fun _ : Fin m => incrementLaw μ) G).toReal := by
      have hc : (Measure.pi fun _ : Fin m => incrementLaw μ).real Gᶜ =
          1 - (Measure.pi fun _ : Fin m => incrementLaw μ).real G := by
        rw [measureReal_compl (Set.to_countable G).measurableSet]
        simp [Measure.real]
      change (Measure.pi fun _ : Fin m => incrementLaw μ).real Gᶜ ≤ 2 * κ at hGc
      rw [hc] at hGc
      change 1 - t / 3 ≤ (Measure.pi fun _ : Fin m => incrementLaw μ).real G
      linarith only [hGc, hκt]
    have hFarBad : ∀ y : Fin m → ℤ, T - ∑ i, y i ∈ Bfar → y ∈ Gᶜ := by
      simpa only [G, Bfar] using hspec.2.2
    have hNearShift (w : ℤ) (hw : w ∈ Bnear) :
        ((w : ℝ) + 1) / ((z : ℝ) + 1) ∈ Set.Icc (1 - ε) (1 + ε) := by
      exact berger_near_shift hε (by linarith) hz0 hw
    have hFarScale (w : ℤ) (hw : w ∈ Bfar) :
        δ * ((z : ℝ) + 1) ≤ (w : ℝ) + 1 := by
      exact berger_far_shift hδ1 hz0.le hw.1
    have hNearMass (w : ℤ) (hw : w ∈ Bnear) :
        (incrementLaw μ {w}).toReal ≤ (1 + t / 3) * (incrementLaw μ {z}).toReal := by
      have hrat := hN₄ (m + 1) hn₄ z w hz (hNearShift w hw)
      have hdiv : (incrementLaw μ {w}).toReal ≤ Au * (incrementLaw μ {z}).toReal := by
        have hmul : (incrementLaw μ {w}).toReal / (incrementLaw μ {z}).toReal ≤ Au :=
          by simpa only [Au, one_div] using hrat.le
        exact (div_le_iff₀ hpz).mp hmul
      calc
        _ ≤ Au * (incrementLaw μ {z}).toReal := hdiv
        _ ≤ (1 + t / 3) * (incrementLaw μ {z}).toReal := by gcongr
    have hswapShift (w : ℤ) (hw : w ∈ Bnear) :
        ((z : ℝ) + 1) / ((w : ℝ) + 1) ∈ Set.Icc (1 + ε)⁻¹ (1 - ε)⁻¹ := by
      exact berger_swap_shift hε (by linarith) hz0 hw
    have hnearMassPos (w : ℤ) (hw : w ∈ Bnear) :
        0 < (incrementLaw μ {w}).toReal := by
      have hwbase : (1 - ε) * (R * a (m + 1)) ≤ (w : ℝ) := by
        have hzw := mul_le_mul_of_nonneg_left hz hεa.le
        exact hzw.trans hw.1
      have hwNat : M ≤ (w + 1).toNat := by
        have hw0 : (0 : ℝ) ≤ w := (mul_nonneg hεa.le hz0.le).trans hw.1
        have hw' : -1 ≤ w := by
          have : (0 : ℤ) ≤ w := by exact_mod_cast hw0
          omega
        have hcast : (((w + 1).toNat : ℕ) : ℝ) = (w : ℝ) + 1 :=
          berger_increment_shift_cast hw'
        apply Nat.le_of_lt_succ
        have hh : (M : ℝ) < (((w + 1).toNat + 1 : ℕ) : ℝ) := by
          push_cast
          rw [hcast]
          exact lt_of_le_of_lt (hML.trans hwbase) (by linarith)
        exact_mod_cast hh
      have hw' : -1 ≤ w := by
        have hw0 : (0 : ℝ) ≤ w := (mul_nonneg hεa.le hz0.le).trans hw.1
        have : (0 : ℤ) ≤ w := by exact_mod_cast hw0
        omega
      rw [berger_incrementLaw_singleton μ w hw']
      exact ENNReal.toReal_pos (ne_of_gt (hM _ hwNat)) (by finiteness)
    have hLowerMass (w : ℤ) (hw : w ∈ Bnear) :
        Cl * (incrementLaw μ {z}).toReal ≤ (incrementLaw μ {w}).toReal := by
      have hwbase : (1 - ε) * (R * a (m + 1)) ≤ (w : ℝ) :=
        (mul_le_mul_of_nonneg_left hz hεa.le).trans hw.1
      have hrat := hN₅ (m + 1) hn₅ w z hwbase (hswapShift w hw)
      have hBlform : (((1 + ε)⁻¹) ^ 2)⁻¹ + η = Bl := by
        dsimp [Bl]
        field_simp
      rw [hBlform] at hrat
      have hmul : (incrementLaw μ {z}).toReal ≤
          Bl * (incrementLaw μ {w}).toReal := (div_le_iff₀ (hnearMassPos w hw)).mp hrat.le
      dsimp [Cl]
      rw [inv_mul_eq_div]
      apply (div_le_iff₀ hBl).mpr
      simpa only [mul_comm] using hmul
    have hnearEN : ((Measure.pi fun _ : Fin (m + 1) => incrementLaw μ)
        {x | (∑ j, x j) = T ∧ ∃ i, x i ∈ Bnear}).toReal ≤
        ((m + 1 : ℕ) : ℝ) * (1 + t / 3) * (incrementLaw μ {z}).toReal := by
      have hmass : ∀ w ∈ Bnear, incrementLaw μ {w} ≤
          ENNReal.ofReal (1 + t / 3) * incrementLaw μ {z} := by
        intro w hw
        exact berger_mul_le_ofReal_of_toReal (by finiteness) (by finiteness)
          (by positivity) (hNearMass w hw)
      have hh := berger_near_cell_bound (m := m) (incrementLaw μ) T Bnear
        (ENNReal.ofReal (1 + t / 3)) z hmass
      have hr := (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mpr hh
      simp only [ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (show 0 ≤ 1 + t / 3 by positivity)] at hr
      rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at hr
      simp only [ENNReal.toReal_natCast, ENNReal.toReal_one] at hr
      simpa [ENNReal.toReal_ofReal (show 0 ≤ 1 + t / 3 by positivity),
        Nat.cast_add, Nat.cast_one] using hr
    have hfarEN : ((Measure.pi fun _ : Fin (m + 1) => incrementLaw μ)
        {x | (∑ j, x j) = T ∧ ∃ i, x i ∈ Bfar}).toReal ≤
        ((m + 1 : ℕ) : ℝ) * C * (incrementLaw μ {z}).toReal * (2 * κ) := by
      have hmass : ∀ w ∈ Bfar, incrementLaw μ {w} ≤
          ENNReal.ofReal C * incrementLaw μ {z} := by
        intro w hw
        exact berger_mul_le_ofReal_of_toReal (by finiteness) (by finiteness) hC.le
          (hN₆ (m + 1) hn₆ z w (by
            calc
              1 * a (m + 1) ≤ R * a (m + 1) := by
                apply mul_le_mul_of_nonneg_right (le_max_left 1 _) ha0.le
              _ ≤ (z : ℝ) := hz) (hFarScale w hw))
      have hh := berger_far_cell_bound (m := m) (incrementLaw μ) T Bfar Gᶜ
        (ENNReal.ofReal C) z hmass hFarBad
      have hr := (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mpr hh
      simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC.le] at hr
      rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at hr
      simp only [ENNReal.toReal_natCast, ENNReal.toReal_one] at hr
      have hprob := mul_le_mul_of_nonneg_left hGc
        (show 0 ≤ ((m + 1 : ℕ) : ℝ) * C * (incrementLaw μ {z}).toReal by positivity)
      exact hr.trans (by simpa [ENNReal.toReal_ofReal hC.le, Measure.real] using hprob)
    have hsmall' : ((Measure.pi fun _ : Fin (m + 1) => incrementLaw μ)
        {x | ∑ i, x i = T ∧ ∀ i, (x i : ℝ) ≤ δ * z}).toReal ≤
        (t / 3) * (((m + 1 : ℕ) : ℝ) * (incrementLaw μ {z}).toReal) := by
      simpa only [T] using hsmall (m + 1) hn₀ z hzR₀
    let E : Set (Fin (m + 1) → ℤ) := {x | ∑ i, x i = T}
    let S : Set (Fin (m + 1) → ℤ) :=
      {x | ∑ i, x i = T ∧ ∀ i, (x i : ℝ) ≤ δ * z}
    let V : Set (Fin (m + 1) → ℤ) := {x | ∑ i, x i = T ∧ ∃ i, x i ∈ Bnear}
    let F : Set (Fin (m + 1) → ℤ) := {x | ∑ i, x i = T ∧ ∃ i, x i ∈ Bfar}
    have hEsub : E ⊆ S ∪ (V ∪ F) := by
      intro x hx
      by_cases hs : ∀ i, (x i : ℝ) ≤ δ * z
      · exact Or.inl ⟨hx, hs⟩
      · push Not at hs
        obtain ⟨i, hi⟩ := hs
        by_cases hn : x i ∈ Bnear
        · exact Or.inr (Or.inl ⟨hx, i, hn⟩)
        · exact Or.inr (Or.inr ⟨hx, i, hi, hn⟩)
    have hupper : (Measure.pi fun _ : Fin (m + 1) => incrementLaw μ).real E ≤
        (1 + t) * (((m + 1 : ℕ) : ℝ) * (incrementLaw μ {z}).toReal) := by
      have hsplit := (measureReal_mono hEsub (measure_ne_top _ _)).trans
        ((measureReal_union_le (μ := Measure.pi fun _ : Fin (m + 1) => incrementLaw μ)
          S (V ∪ F)).trans
          (add_le_add (le_refl ((Measure.pi fun _ : Fin (m + 1) => incrementLaw μ).real S))
            (measureReal_union_le (μ := Measure.pi fun _ : Fin (m + 1) => incrementLaw μ)
              V F)))
      change (Measure.pi fun _ : Fin (m + 1) => incrementLaw μ).real E ≤ _
      calc
        _ ≤ (Measure.pi fun _ : Fin (m + 1) => incrementLaw μ).real S +
            ((Measure.pi fun _ : Fin (m + 1) => incrementLaw μ).real V +
              (Measure.pi fun _ : Fin (m + 1) => incrementLaw μ).real F) := hsplit
        _ ≤ (t / 3) * (((m + 1 : ℕ) : ℝ) * (incrementLaw μ {z}).toReal) +
            (((m + 1 : ℕ) : ℝ) * (1 + t / 3) * (incrementLaw μ {z}).toReal +
              ((m + 1 : ℕ) : ℝ) * C * (incrementLaw μ {z}).toReal * (2 * κ)) := by
          dsimp [S, V, F]
          exact add_le_add hsmall' (add_le_add hnearEN hfarEN)
        _ ≤ _ := by
          have hCκ : ((m + 1 : ℕ) : ℝ) * C * (incrementLaw μ {z}).toReal * (2 * κ) ≤
              (t / 3) * (((m + 1 : ℕ) : ℝ) * (incrementLaw μ {z}).toReal) := by
            calc
              _ ≤ ((m + 1 : ℕ) : ℝ) * C * (incrementLaw μ {z}).toReal * ((t / 3) / C) := by
                gcongr
              _ = _ := by field_simp
          linarith only [hCκ]
    have hlowerEN : Cl * ((m + 1 : ℕ) : ℝ) * (incrementLaw μ {z}).toReal *
        ((Measure.pi fun _ : Fin m => incrementLaw μ) G).toReal ≤
        ((Measure.pi fun _ : Fin (m + 1) => incrementLaw μ) E).toReal := by
      have hmass : ∀ w ∈ Bnear, ENNReal.ofReal Cl * incrementLaw μ {z} ≤
          incrementLaw μ {w} := by
        intro w hw
        exact berger_ofReal_mul_le_of_toReal (by finiteness) (by finiteness)
          hCl.le (hLowerMass w hw)
      have hh := berger_lower_insertions (m := m) (incrementLaw μ) T G Bnear
        (ENNReal.ofReal Cl) z hnearGood hstrict hmass
      have hr := (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mpr hh
      simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCl.le] at hr
      rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at hr
      simp only [ENNReal.toReal_natCast, ENNReal.toReal_one] at hr
      simpa only [E, Measure.real, mul_assoc, Nat.cast_add, Nat.cast_one] using hr
    have hlower : (1 - t) * (((m + 1 : ℕ) : ℝ) * (incrementLaw μ {z}).toReal) ≤
        ((Measure.pi fun _ : Fin (m + 1) => incrementLaw μ) E).toReal := by
      have hcoef : (1 - t) ≤ Cl * (1 - t / 3) := by
        calc
          1 - t ≤ (1 - t / 3) * (1 - t / 3) := by nlinarith only [sq_nonneg (t / 3), ht0]
          _ ≤ Cl * (1 - t / 3) := by gcongr; linarith
      have hrealcoef : (1 - t) * (((m + 1 : ℕ) : ℝ) * (incrementLaw μ {z}).toReal) ≤
          Cl * ((m + 1 : ℕ) : ℝ) * (incrementLaw μ {z}).toReal *
            ((Measure.pi fun _ : Fin m => incrementLaw μ) G).toReal := by
        calc
          _ ≤ (Cl * (1 - t / 3)) * (((m + 1 : ℕ) : ℝ) * (incrementLaw μ {z}).toReal) := by
            gcongr
          _ ≤ _ := by
            have hg := mul_le_mul_of_nonneg_left hGprob
              (show 0 ≤ Cl * ((m + 1 : ℕ) : ℝ) * (incrementLaw μ {z}).toReal by positivity)
            linarith only [hg]
      exact hrealcoef.trans (by simpa only [Measure.real, mul_assoc] using hlowerEN)
    have hP := measureReal_nonneg (μ := Measure.pi fun _ : Fin (m + 1) => incrementLaw μ)
      (s := E)
    change |(Measure.pi fun _ : Fin (m + 1) => incrementLaw μ).real E /
      (((m + 1 : ℕ) : ℝ) * (incrementLaw μ {z}).toReal) - 1| ≤ τ
    have hlo : 1 - t ≤ (Measure.pi fun _ : Fin (m + 1) => incrementLaw μ).real E /
        (((m + 1 : ℕ) : ℝ) * (incrementLaw μ {z}).toReal) :=
      (le_div_iff₀ hD).mpr (by simpa only [Measure.real, mul_comm] using hlower)
    have hhi : (Measure.pi fun _ : Fin (m + 1) => incrementLaw μ).real E /
        (((m + 1 : ℕ) : ℝ) * (incrementLaw μ {z}).toReal) ≤ 1 + t :=
      (div_le_iff₀ hD).mpr (by simpa only [Measure.real, mul_comm] using hupper)
    exact abs_le.mpr ⟨by linarith only [hlo, htτ], by linarith only [hhi, htτ]⟩

end
end SubcriticalCauchy.Bienayme
