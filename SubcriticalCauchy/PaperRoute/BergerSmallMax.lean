module

public import SubcriticalCauchy.PaperRoute.BergerSmallMaxAux

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Walks whose jumps are all small are negligible

This is the small-maximum step in Berger's proof.  We split the coordinates
into two blocks.  One block has a large centered sum and is controlled by the
Fuk--Nagaev estimate with truncation `z / 64`; concentration controls the exact
sum in the other block.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology BigOperators

namespace SubcriticalCauchy.Bienayme

noncomputable section

attribute [local instance] Classical.propDecidable

local instance smallMaxIncrementLawIsProbability (μ : Measure ℕ)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (incrementLaw μ) := by
  unfold incrementLaw
  infer_instance

/-- Walks with no jump larger than a small fraction of their final location
are negligible compared with the one-big-jump probability. -/
theorem incrementSum_smallMax_of_fukNagaev
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ)
    (hE : ∀ {L : ℝ → ℝ}, (∀ x : ℝ, 0 < x → 0 < L x) →
      AEMeasurable L (volume.restrict (Set.Ioi 0)) → IsSlowlyVaryingAtTop L →
      Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2)) atTop (𝓝 1) →
      ∀ {a : ℕ → ℝ},
        Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal) atTop (𝓝 1) →
        ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          ∀ j : ℕ, j ≤ n → ∀ z y : ℝ, K * a n ≤ z → a n ≤ y → y ≤ z →
          ((Measure.pi fun _ : Fin j => incrementLaw μ)
              {x | z ≤ (∑ i, (x i : ℝ)) - j * truncatedIncrementMean μ (a n) ∧
                   ∀ i, (x i : ℝ) ≤ y}).toReal
            ≤ Real.exp (z / y) * (1 + c * z / ((n : ℝ) * L y)) ^
              (-(z / (2 * y))))
    (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal) atTop (𝓝 1)) :
    ∀ τ : ℝ, 0 < τ → ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ ∃ N : ℕ, ∃ R : ℝ,
      ∀ n : ℕ, N ≤ n → ∀ z : ℤ, R * a n ≤ z →
        ((Measure.pi fun _ : Fin n => incrementLaw μ)
            {x | ∑ i, x i = z + ⌊centering μ a n⌋ ∧ ∀ i, (x i : ℝ) ≤ δ * z}).toReal
          ≤ τ * ((n : ℝ) * (incrementLaw μ {z}).toReal) := by
  obtain ⟨hm, L, hpos, hsv, hL, hlocal⟩ := hμ
  obtain ⟨c, hc, K, hK, NF, hFN⟩ := hE hpos hL hsv hlocal ha
  obtain ⟨C, NC, hconc⟩ := incrementSum_concentration_scale μ hm hpos hL hsv hlocal ha
  obtain ⟨P, hP, NP, hNP, hpot⟩ := potter_bounds hpos hL hsv (1 / 2) (by norm_num)
  have hscale := scaling_div_mul_tendsto_one μ hm hpos hL hsv hlocal ha
  have haTop := scaling_tendsto_atTop μ
    (show IsSubcriticalCauchyOffspring μ from ⟨hm, ⟨L, hpos, hsv, hlocal⟩⟩) ha
  have hlocal' : ∀ᶠ k : ℕ in atTop, (1 / 2 : ℝ) < (μ {k}).toReal / (L k / (k : ℝ) ^ 2) :=
    hlocal.eventually_const_lt (by norm_num)
  obtain ⟨NL, hNL⟩ := eventually_atTop.mp hlocal'
  have hevN : ∀ᶠ n : ℕ in atTop,
      (max NF (max NC 2) ≤ n) ∧ ((max 1 NP : ℝ) ≤ a n) ∧
      (1 / 2 : ℝ) < a n / ((n : ℝ) * L (a n)) ∧ a n / ((n : ℝ) * L (a n)) < 2 := by
    filter_upwards [eventually_ge_atTop (max NF (max NC 2)),
      haTop.eventually_ge_atTop (max 1 NP),
      hscale.eventually_const_lt (by norm_num : (1 / 2 : ℝ) < 1),
      hscale.eventually_lt_const (by norm_num : (1 : ℝ) < 2)] with n hn haN hlo hhi
    exact ⟨hn, haN, hlo, hhi⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hevN
  let C' := |C| + 1
  let δ : ℝ := 1 / 64
  let δhalf := δ ^ (1 / 2 : ℝ)
  let D₀ := c / (8 * P * δhalf)
  let D := 8 * P ^ 2 * (2 : ℝ) ^ (1 / 2 : ℝ)
  let A := C' * Real.exp 16 * D₀ ^ (-8 : ℝ)
  let Q := 4 * A * D
  have hC' : 0 < C' := by dsimp [C']; positivity
  have hδ : 0 < δ := by norm_num [δ]
  have hδhalf : 0 < δhalf := by dsimp [δhalf]; positivity
  have hD₀ : 0 < D₀ := by dsimp [D₀]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have htend : Tendsto (fun u : ℝ => Q * u ^ (-(3 / 2) : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 2)).const_mul Q
  intro τ hτ
  have hevR : ∀ᶠ R : ℝ in atTop,
      1 ≤ R ∧ 4 * K ≤ R ∧ 64 ≤ R ∧ NP ≤ R ∧ 64 * NP ≤ R ∧ (NL : ℝ) ≤ R ∧
        Q * R ^ (-(3 / 2) : ℝ) ≤ τ :=
    by
    filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (4 * K),
      eventually_ge_atTop (64 : ℝ), eventually_ge_atTop NP,
      eventually_ge_atTop (64 * NP), eventually_ge_atTop (NL : ℝ),
      htend.eventually_le_const hτ] with R h1 h4K h64 hNP hδNP hNL hτR
    exact ⟨h1, h4K, h64, hNP, hδNP, hNL, hτR⟩
  obtain ⟨R, hR1, hR4K, hR64, hRNP, hRδNP, hRNL, hRτ⟩ := hevR.exists
  refine ⟨δ, hδ, by norm_num [δ], N₀, R, ?_⟩
  intro n hn z hz
  obtain ⟨hn0, haN, hslo, hshi⟩ := hN₀ n hn
  have hn2 : 2 ≤ n := (le_max_right NC 2).trans ((le_max_right NF _).trans hn0)
  have hnNF : NF ≤ n := (le_max_left NF _).trans hn0
  have hnNC : NC ≤ n := (le_max_left NC 2).trans ((le_max_right NF _).trans hn0)
  have hn : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have ha1 : 1 ≤ a n := (le_max_left 1 NP).trans haN
  have haNP : NP ≤ a n := (le_max_right 1 NP).trans haN
  have ha0 : 0 < a n := zero_lt_one.trans_le ha1
  have hnpos : 0 ≤ (n : ℝ) := hnR.le
  have hLa : 0 < L (a n) := hpos _ ha0
  have hnLa : 0 < (n : ℝ) * L (a n) := mul_pos hnR hLa
  have hscale_lo : a n / 2 ≤ (n : ℝ) * L (a n) := by
    have hh := (div_lt_iff₀ hnLa).mp hshi
    linarith
  have hscale_hi : (n : ℝ) * L (a n) ≤ 2 * a n := by
    have hh := (lt_div_iff₀ hnLa).mp hslo
    linarith
  let zR : ℝ := z
  let u := zR / a n
  have hR0 : 0 < R := zero_lt_one.trans_le hR1
  have hRa : 0 < R * a n := mul_pos hR0 ha0
  have hzR : R ≤ zR / a n := (le_div_iff₀ ha0).2 hz
  have huR : R ≤ u := hzR
  have hu1 : 1 ≤ u := hR1.trans huR
  have hu : 0 < u := zero_lt_one.trans_le hu1
  have hzu : zR = u * a n := by
    dsimp [u]
    exact (div_mul_cancel₀ _ ha0.ne').symm
  have hzpos : 0 < zR := hRa.trans_le hz
  have hz0 : 0 ≤ z := by
    dsimp [zR] at hzpos
    exact_mod_cast hzpos.le
  have hua : u ≤ zR := by
    calc
      u = u * 1 := by ring
      _ ≤ u * a n := mul_le_mul_of_nonneg_left ha1 hu.le
      _ = zR := hzu.symm
  have haz : a n ≤ zR := by
    calc
      a n = 1 * a n := by ring
      _ ≤ u * a n := mul_le_mul_of_nonneg_right hu1 ha0.le
      _ = zR := hzu.symm
  have hz2 : 2 ≤ zR := by
    have h64 := hR64.trans (huR.trans hua)
    linarith
  have hzNP : NP ≤ zR := by
    have h1 : NP ≤ R := hRNP
    have h2 : R ≤ u := huR
    have h3 : u ≤ zR := hua
    linarith
  let δz := δ * zR
  have hδzNP : NP ≤ δz := by
    have hRp : 64 * NP ≤ zR := by
      calc 64 * NP ≤ R := hRδNP
        _ ≤ u := huR
        _ ≤ zR := hua
    dsimp [δz, δ]
    linarith
  have hay : a n ≤ δz := by
    have h64a : 64 * a n ≤ zR :=
      (mul_le_mul_of_nonneg_right hR64 ha0.le).trans hz
    calc
      a n = 64 * a n / 64 := by ring
      _ ≤ zR / 64 := div_le_div_of_nonneg_right h64a (by norm_num)
      _ = δz := by dsimp [δz, δ]; ring
  have hLz : 0 < L zR := hpos _ hzpos
  have hLδz : 0 < L δz := hpos _ (hNP.trans_le hδzNP)
  have hPz : L (a n) ≤ P * u ^ (1 / 2 : ℝ) * L zR := by
    have hh := (hpot (a n) zR haNP haz).1
    have hdiv : zR / a n = u := rfl
    rw [hdiv] at hh
    have hh' : P⁻¹ * u ^ (-(1 / 2) : ℝ) * L (a n) ≤ L zR :=
      (le_div_iff₀ hLa).mp hh
    calc
      L (a n) = (P * u ^ (1 / 2 : ℝ)) *
          (P⁻¹ * u ^ (-(1 / 2) : ℝ) * L (a n)) := by
        rw [Real.rpow_neg hu.le]
        field_simp [hP.ne', (Real.rpow_pos_of_pos hu (1 / 2 : ℝ)).ne']
      _ ≤ P * u ^ (1 / 2 : ℝ) * L zR :=
        mul_le_mul_of_nonneg_left hh' (by positivity)
  have hPδ : L δz ≤ P * (δ * u) ^ (1 / 2 : ℝ) * L (a n) := by
    have hh := (hpot (a n) δz haNP hay).2
    have hdiv : δz / a n = δ * u := by dsimp [δz, u]; ring
    rw [hdiv] at hh
    exact (div_le_iff₀ hLa).mp hh
  let k : ℕ := (z + 1).toNat
  let kR : ℝ := k
  have hkint : (k : ℤ) = z + 1 := by
    dsimp [k]
    apply Int.toNat_of_nonneg
    omega
  have hkcast : kR = zR + 1 := by
    dsimp [kR]
    calc
      ((k : ℕ) : ℝ) = (((k : ℤ)) : ℝ) := by norm_cast
      _ = ((z + 1 : ℤ) : ℝ) := by rw [hkint]
      _ = zR + 1 := by dsimp [zR]; push_cast; ring
  have hzk : zR ≤ kR := by rw [hkcast]; linarith
  have hk2 : kR ≤ 2 * zR := by rw [hkcast]; linarith
  have hkpos : 0 < kR := hzpos.trans_le hzk
  have hkNP : NP ≤ kR := hzNP.trans hzk
  have hkNL : NL ≤ k := by
    have hRz : (NL : ℝ) ≤ zR := hRNL.trans (huR.trans (hua))
    dsimp [k]
    have hkge : z ≤ (k : ℤ) := by rw [hkint]; omega
    have hzNL : NL ≤ z := by
      dsimp [zR] at hRz
      exact_mod_cast hRz
    omega
  have hrpos : 0 < kR / zR := div_pos hkpos hzpos
  have hr2 : kR / zR ≤ 2 := (div_le_iff₀ hzpos).2 hk2
  have hLk : 0 < L kR := hpos _ hkpos
  have hmassk : L kR ≤ 2 * kR ^ 2 * (μ {k}).toReal := by
    have hh := hNL k hkNL
    have hden : 0 < L k / (k : ℝ) ^ 2 := by
      have hkn : 0 < (k : ℝ) := by simpa [kR] using hkpos
      exact div_pos (hpos _ hkn) (sq_pos_of_pos hkn)
    have hHH := (lt_div_iff₀ hden).mp hh
    have hkr : (k : ℝ) = kR := rfl
    rw [hkr] at hHH hden
    calc
      L kR = 2 * kR ^ 2 * ((1 / 2 : ℝ) * (L kR / kR ^ 2)) := by
        field_simp [hkpos.ne']
      _ ≤ 2 * kR ^ 2 * (μ {k}).toReal := by
        exact mul_le_mul_of_nonneg_left hHH.le (by positivity)
  have hmassz : L kR ≤ 8 * zR ^ 2 * (μ {k}).toReal := by
    calc
      L kR ≤ 2 * kR ^ 2 * (μ {k}).toReal := hmassk
      _ ≤ 2 * (4 * zR ^ 2) * (μ {k}).toReal := by
        have hksq : kR ^ 2 ≤ 4 * zR ^ 2 := by
          calc
            kR ^ 2 ≤ (2 * zR) ^ 2 := pow_le_pow_left₀ hkpos.le hk2 2
            _ = 4 * zR ^ 2 := by ring
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hksq (by norm_num)) ENNReal.toReal_nonneg
      _ = 8 * zR ^ 2 * (μ {k}).toReal := by ring
  have hpzk := (hpot zR kR hzNP hzk).1
  have hpzk' : P⁻¹ * (kR / zR) ^ (-(1 / 2) : ℝ) * L zR ≤ L kR :=
    (le_div_iff₀ hLz).mp hpzk
  have hLz_k : L zR ≤ P * (kR / zR) ^ (1 / 2 : ℝ) * L kR := by
    calc
      L zR = (P * (kR / zR) ^ (1 / 2 : ℝ)) *
          (P⁻¹ * (kR / zR) ^ (-(1 / 2) : ℝ) * L zR) := by
        rw [Real.rpow_neg hrpos.le]
        field_simp [hP.ne', (Real.rpow_pos_of_pos hrpos (1 / 2 : ℝ)).ne']
      _ ≤ P * (kR / zR) ^ (1 / 2 : ℝ) * L kR := by
        exact mul_le_mul_of_nonneg_left hpzk' (by positivity)
  have hLz_mass : L zR ≤ P * (2 : ℝ) ^ (1 / 2 : ℝ) *
      (8 * zR ^ 2 * (μ {k}).toReal) := by
    calc
      L zR ≤ P * (kR / zR) ^ (1 / 2 : ℝ) * L kR := hLz_k
      _ ≤ P * (2 : ℝ) ^ (1 / 2 : ℝ) * (8 * zR ^ 2 * (μ {k}).toReal) := by
        have hrpow : (kR / zR) ^ (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hrpos.le hr2 (by norm_num)
        have hleft : P * (kR / zR) ^ (1 / 2 : ℝ) ≤ P * (2 : ℝ) ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left hrpow hP.le
        have hL0 : 0 ≤ L kR := hLk.le
        calc
          P * (kR / zR) ^ (1 / 2 : ℝ) * L kR
              ≤ P * (2 : ℝ) ^ (1 / 2 : ℝ) * L kR :=
            mul_le_mul_of_nonneg_right hleft hL0
          _ ≤ P * (2 : ℝ) ^ (1 / 2 : ℝ) * (8 * zR ^ 2 * (μ {k}).toReal) :=
            mul_le_mul_of_nonneg_left hmassz (by positivity)
  have hmass_atom : incrementLaw μ {z} = μ {k} := by
    exact smallMax_incrementLaw_singleton μ hz0
  have hmass_nonneg : 0 ≤ (μ {k}).toReal := ENNReal.toReal_nonneg
  have hlocal_norm : L (a n) ≤ D * u ^ (1 / 2 : ℝ) * zR ^ 2 * (μ {k}).toReal := by
    calc
      L (a n) ≤ P * u ^ (1 / 2 : ℝ) * L zR := hPz
      _ ≤ P * u ^ (1 / 2 : ℝ) *
          (P * (2 : ℝ) ^ (1 / 2 : ℝ) * (8 * zR ^ 2 * (μ {k}).toReal)) :=
        mul_le_mul_of_nonneg_left hLz_mass (by positivity)
      _ = D * u ^ (1 / 2 : ℝ) * zR ^ 2 * (μ {k}).toReal := by
        dsimp [D]
        ring
  have hmass := smallMax_mass_lower (n := (n : ℝ)) (a := a n) (z := zR) (u := u)
    (mass := (μ {k}).toReal) (Lₐ := L (a n)) (D := D)
    hnR ha0 hzpos hu hD hLa hzu hscale_lo hlocal_norm
  have hδu : (δ * u) ^ (1 / 2 : ℝ) = δhalf * u ^ (1 / 2 : ℝ) := by
    exact Real.mul_rpow hδ.le hu.le
  have hnLδ : 0 < (n : ℝ) * L δz := mul_pos hnR hLδz
  have hnLδ_bound : (n : ℝ) * L δz ≤ 2 * P * a n * (δhalf * u ^ (1 / 2 : ℝ)) := by
    calc
      (n : ℝ) * L δz ≤ (n : ℝ) * (P * (δ * u) ^ (1 / 2 : ℝ) * L (a n)) :=
        mul_le_mul_of_nonneg_left hPδ hnpos
      _ = P * (δ * u) ^ (1 / 2 : ℝ) * ((n : ℝ) * L (a n)) := by ring
      _ ≤ P * (δ * u) ^ (1 / 2 : ℝ) * (2 * a n) :=
        mul_le_mul_of_nonneg_left hscale_hi (by positivity)
      _ = 2 * P * a n * (δhalf * u ^ (1 / 2 : ℝ)) := by rw [hδu]; ring
  have hbase₀ : D₀ * u ^ (1 / 2 : ℝ) ≤ c * (zR / 4) / ((n : ℝ) * L δz) := by
    apply (le_div_iff₀ hnLδ).2
    calc
      D₀ * u ^ (1 / 2 : ℝ) * ((n : ℝ) * L δz)
          ≤ D₀ * u ^ (1 / 2 : ℝ) * (2 * P * a n * (δhalf * u ^ (1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hnLδ_bound (by positivity)
      _ = c * (zR / 4) := by
        calc
          D₀ * u ^ (1 / 2 : ℝ) * (2 * P * a n * (δhalf * u ^ (1 / 2 : ℝ))) =
              D₀ * (2 * P * a n * δhalf) * (u ^ (1 / 2 : ℝ) * u ^ (1 / 2 : ℝ)) := by ring
          _ = c * (zR / 4) := by
            rw [show u ^ (1 / 2 : ℝ) * u ^ (1 / 2 : ℝ) = u by
              rw [← Real.rpow_add hu]; norm_num]
            rw [hzu]
            dsimp [D₀]
            field_simp [hP.ne', hδhalf.ne']
            ring
  have hbase : D₀ * u ^ (1 / 2 : ℝ) ≤ 1 + c * (zR / 4) / ((n : ℝ) * L δz) :=
    hbase₀.trans (by linarith)
  have hfn := smallMax_rpow_neg_eight_le hu hD₀ hbase
  let p := n / 2
  let q := n - n / 2
  have hpq : p + q = n := by dsimp [p, q]; omega
  have hpn : p ≤ n := by dsimp [p]; omega
  have hqn : q ≤ n := by dsimp [q]; omega
  have hnp : n ≤ 3 * p := by dsimp [p]; omega
  have hnq : n ≤ 3 * q := by dsimp [q]; omega
  let m := truncatedIncrementMean μ (a n)
  have htotal : 2 * (zR / 4) ≤ ((z + ⌊centering μ a n⌋ : ℤ) : ℝ) - n * m := by
    have hfloor := Int.sub_one_lt_floor (centering μ a n)
    have hcent : centering μ a n = (n : ℝ) * m := rfl
    push_cast
    rw [hcent] at hfloor ⊢
    dsimp [zR]
    linarith
  have hconc' : ∀ {j : ℕ} (_ : j = p ∨ j = q) (s : ℤ),
      ((Measure.pi fun _ : Fin j => incrementLaw μ) {x | ∑ i, x i = s}).toReal ≤ C' / a n := by
    intro j hj s
    have hj' : n ≤ 3 * j ∧ j ≤ n := by rcases hj with rfl | rfl; exact ⟨hnp, hpn⟩; exact ⟨hnq, hqn⟩
    exact (hconc n hnNC j hj'.1 hj'.2 s).trans
      (div_le_div_of_nonneg_right (by dsimp [C']; linarith [le_abs_self C]) ha0.le)
  have hKz : K * a n ≤ zR / 4 := by
    have hKa : K * a n ≤ R * a n / 4 := by
      have hh : 4 * K * a n ≤ R * a n :=
        mul_le_mul_of_nonneg_right hR4K ha0.le
      linarith
    exact hKa.trans (div_le_div_of_nonneg_right hz (by norm_num))
  have hyz : δz ≤ zR / 4 := by dsimp [δz, δ]; linarith
  have hexp : zR / 4 / (2 * δz) = 8 := by
    dsimp [δz, δ]
    field_simp [hzpos.ne']
    norm_num
  have hexp' : zR / 4 / δz = 16 := by
    dsimp [δz, δ]
    field_simp [hzpos.ne']
    norm_num
  have hlarge : ∀ {j : ℕ} (_ : j = p ∨ j = q),
      ((Measure.pi fun _ : Fin j => incrementLaw μ)
        {x | zR / 4 ≤ (∑ i, (x i : ℝ)) - j * m ∧ ∀ i, (x i : ℝ) ≤ δz}).toReal ≤
        Real.exp 16 * (1 + c * (zR / 4) / ((n : ℝ) * L δz)) ^ (-8 : ℝ) := by
    intro j hj
    have hjn : j ≤ n := by rcases hj with rfl | rfl; exact hpn; exact hqn
    have hh := hFN n hnNF j hjn (zR / 4) δz hKz hay hyz
    rw [hexp, hexp'] at hh
    exact hh
  have hblock := smallMax_pi_toReal_le_of_add_eq (incrementLaw μ) hpq
    (z + ⌊centering μ a n⌋) m (zR / 4) δz (C' / a n)
    (Real.exp 16 * (1 + c * (zR / 4) / ((n : ℝ) * L δz)) ^ (-8 : ℝ))
    htotal hconc' hlarge
  have hF : C' / a n *
      (Real.exp 16 * (1 + c * (zR / 4) / ((n : ℝ) * L δz)) ^ (-8 : ℝ)) ≤
      A / a n * u ^ (-4 : ℝ) := by
    calc
      C' / a n * (Real.exp 16 * (1 + c * (zR / 4) / ((n : ℝ) * L δz)) ^ (-8 : ℝ))
          ≤ C' / a n * (Real.exp 16 * (D₀ ^ (-8 : ℝ) * u ^ (-4 : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg hC'.le ha0.le)
        exact mul_le_mul_of_nonneg_left hfn (Real.exp_pos _).le
      _ = A / a n * u ^ (-4 : ℝ) := by dsimp [A]; ring
  have hcompare := smallMax_final_comparison
    (F := C' / a n *
      (Real.exp 16 * (1 + c * (zR / 4) / ((n : ℝ) * L δz)) ^ (-8 : ℝ)))
    (A := A) (n := (n : ℝ)) (a := a n) (z := zR) (u := u)
    (mass := (μ {k}).toReal) (D := D) hnR ha0 hzpos hu hA hD hzu hF hmass
  have huτ : Q * u ^ (-(3 / 2) : ℝ) ≤ τ := by
    have hpw : u ^ (-(3 / 2) : ℝ) ≤ R ^ (-(3 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hR0 huR (by norm_num)
    exact (mul_le_mul_of_nonneg_left hpw hQ.le).trans hRτ
  rw [hmass_atom]
  calc
    ((Measure.pi fun _ : Fin n => incrementLaw μ)
        {x | ∑ i, x i = z + ⌊centering μ a n⌋ ∧ ∀ i, (x i : ℝ) ≤ δ * z}).toReal
        ≤ 2 * (C' / a n) *
          (Real.exp 16 * (1 + c * (zR / 4) / ((n : ℝ) * L δz)) ^ (-8 : ℝ)) := by
      convert hblock using 2
    _ ≤ Q * u ^ (-(3 / 2) : ℝ) * ((n : ℝ) * (μ {k}).toReal) := by
      simpa only [Q, mul_assoc] using hcompare
    _ ≤ τ * ((n : ℝ) * (μ {k}).toReal) :=
      mul_le_mul_of_nonneg_right huτ (mul_nonneg hnpos hmass_nonneg)

end
end SubcriticalCauchy.Bienayme
