module

public import SubcriticalCauchy.DeletedMaximumDensity
public import SubcriticalCauchy.LocalMassWindows
public import SubcriticalCauchy.OffspringMaximum
public import SubcriticalCauchy.PotterBounds

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Auxiliary estimates for endpoint local asymptotics
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology BigOperators

namespace SubcriticalCauchy.Bienayme

/-- Residual vectors with sum and maximum controlled by `h`. -/
def endpointResidualSet (μ : Measure ℕ) (h : ℕ → ℝ) (n : ℕ) : Set (Fin (n - 1) → ℕ) :=
  {z | |(∑ i, (z i : ℝ)) - (offspringMean μ).toReal * (n - 1 : ℕ)| ≤ h n ∧
    ∀ i, (z i : ℝ) ≤ h n}

/-- The natural-number form of relative uniformization for singleton masses. -/
theorem uniform_nat_mass_ratio
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ)
    {z d : ℕ → ℝ} (hz : Tendsto z atTop atTop) (hd : Tendsto d atTop (𝓝 0)) :
    ∀ τ : ℝ, 0 < τ → ∀ᶠ n : ℕ in atTop, ∀ j k : ℕ,
      z n ≤ (j : ℝ) → |(k : ℝ) / (j : ℝ) - 1| ≤ |d n| →
      |(μ {k}).toReal / (μ {j}).toReal - 1| < τ := by
  classical
  intro τ hτ
  by_contra hnot
  have hbad (N : ℕ) : ∃ (n j k : ℕ), N ≤ n ∧ z n ≤ (j : ℝ) ∧
      |(k : ℝ) / (j : ℝ) - 1| ≤ |d n| ∧
      τ ≤ |(μ {k}).toReal / (μ {j}).toReal - 1| := by
    by_contra hnone
    apply hnot
    refine eventually_atTop.mpr ⟨N, ?_⟩
    intro n hn j k hbase hrel
    by_contra herr
    exact hnone ⟨n, j, k, hn, hbase, hrel, le_of_not_gt herr⟩
  choose ns js ks hN hbase hrel herr using hbad
  have hns : Tendsto ns atTop atTop := tendsto_atTop_mono hN tendsto_id
  have hjsN : Tendsto js atTop atTop := tendsto_natCast_atTop_iff.mp
    (tendsto_atTop_mono hbase (hz.comp hns))
  have hjs : Tendsto (fun n => (js n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hjsN
  have herror : Tendsto (fun n => |(ks n : ℝ) / (js n : ℝ) - 1|) atTop (𝓝 0) :=
    squeeze_zero (fun _ => abs_nonneg _) hrel
      (by simpa only [abs_zero, Function.comp_def] using (hd.comp hns).abs)
  have hcoef : Tendsto (fun n => (ks n : ℝ) / (js n : ℝ)) atTop (𝓝 1) :=
    tendsto_iff_dist_tendsto_zero.mpr (by simpa only [Real.dist_eq] using herror)
  have hks : Tendsto (fun n => (ks n : ℝ)) atTop atTop := by
    apply (hjs.atTop_mul_pos zero_lt_one hcoef).congr'
    filter_upwards [hjs.eventually_gt_atTop 0] with n hn
    field_simp
  have hksN : Tendsto ks atTop atTop := tendsto_natCast_atTop_iff.mp hks
  have hratio := paper_mass_ratio_of_relative_tendsto_one μ hμ hjsN hksN hcoef
  have hzero : Tendsto (fun n => |(μ {ks n}).toReal / (μ {js n}).toReal - 1|)
      atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero] using (hratio.sub_const 1).abs
  obtain ⟨n, hn⟩ := (hzero.eventually (gt_mem_nhds hτ)).exists
  exact (not_lt_of_ge (herr n)) hn

lemma tendsto_sqrt_nat_atTop :
    Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop

lemma tendsto_sqrt_nat_div :
    Tendsto (fun n : ℕ => Real.sqrt n / (n : ℝ)) atTop (𝓝 0) := by
  have heq : (fun n : ℕ => Real.sqrt n / (n : ℝ)) =ᶠ[atTop]
      (fun n : ℕ => (Real.sqrt n)⁻¹) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
    exact Real.sqrt_div_self
  exact (tendsto_inv_atTop_zero.comp tendsto_sqrt_nat_atTop).congr' heq.symm


lemma coordinate_le_listMaxDegree {k : ℕ} (z : Fin k → ℕ) (i : Fin k) :
    z i ≤ listMaxDegree (List.ofFn z) := by
  apply Finset.le_sup (f := id)
  simp

lemma finitePreviousWalkAverage_error (μ : Measure ℕ) (n : ℕ) (z : Fin (n - 1) → ℕ)
    (hn : 0 < n) :
    finitePreviousWalkAverage n z - (1 - (offspringMean μ).toReal) =
      ((offspringMean μ).toReal * n - 1 - ∑ i, (z i : ℝ)) / (n : ℝ) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [finitePreviousWalkAverage, finiteWalkSum, Int.cast_sum,
    Int.cast_sub, Int.cast_natCast, Int.cast_one]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  field_simp
  ring

lemma natCast_natSqrt_le_realSqrt (n : ℕ) : (Nat.sqrt n : ℝ) ≤ Real.sqrt n := by
  rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  exact_mod_cast Nat.sqrt_le' n

/-- Diagonal selection from the two finite-product weak laws. -/
theorem exists_endpointResidualSet_typical
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ < 1) :
    ∃ h : ℕ → ℝ, Tendsto h atTop atTop ∧ Tendsto (fun n => h n / (n : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => (Measure.pi fun _ : Fin (n - 1) => μ).real
        (endpointResidualSet μ h n)) atTop (𝓝 1) := by
  classical
  have hfin : offspringMean μ ≠ ∞ := ne_top_of_lt (hm.trans ENNReal.one_lt_top)
  let P : ∀ n : ℕ, Measure (Fin (n - 1) → ℕ) := fun n => Measure.pi (fun _ : Fin (n - 1) => μ)
  let ε : ℕ → ℝ := fun k => (2 * (k + 1 : ℕ) : ℝ)⁻¹
  let A : ℕ → ∀ n : ℕ, Set (Fin (n - 1) → ℕ) := fun k n =>
    {z | ε k ≤ |finitePreviousWalkAverage n z - (1 - (offspringMean μ).toReal)|}
  let B : ℕ → ∀ n : ℕ, Set (Fin (n - 1) → ℕ) := fun k n =>
    {z | ε k ≤ finitePreviousMaximumAverage n z}
  have hA (k : ℕ) : Tendsto (fun n => (P n).real (A k n)) atTop (𝓝 0) :=
    finitePreviousWalkAverage_deviation_tendsto_zero μ hfin (by positivity)
  have hB (k : ℕ) : Tendsto (fun n => (P n).real (B k n)) atTop (𝓝 0) :=
    finitePreviousMaximumAverage_deviation_tendsto_zero μ hfin (by positivity)
  have hbound (k : ℕ) : ∃ N : ℕ, ∀ n ≥ N,
      (P n).real (A k n) + (P n).real (B k n) < ((k + 1 : ℕ) : ℝ)⁻¹ := by
    have hh : Tendsto (fun n => (P n).real (A k n) + (P n).real (B k n)) atTop (𝓝 0) := by
      simpa only [add_zero] using (hA k).add (hB k)
    have he := hh.eventually (gt_mem_nhds (show (0 : ℝ) < ((k + 1 : ℕ) : ℝ)⁻¹ by positivity))
    exact eventually_atTop.mp he
  let N : ℕ → ℕ := fun k => max (k + 1) (Classical.choose (hbound k))
  have hN (k n : ℕ) (hn : N k ≤ n) :
      (P n).real (A k n) + (P n).real (B k n) < ((k + 1 : ℕ) : ℝ)⁻¹ := by
    apply Classical.choose_spec (hbound k) n
    exact (le_max_right (k + 1) (Classical.choose (hbound k))).trans hn
  let s (n : ℕ) := (Finset.range (Nat.sqrt n + 1)).filter (fun k => N k ≤ n)
  have hs (n : ℕ) (hn : N 0 ≤ n) : (s n).Nonempty := by
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hn⟩⟩
  let M (n : ℕ) := (s n).sup id
  let K (n : ℕ) := M n + 1
  let h (n : ℕ) := (n : ℝ) / (K n : ℝ)
  have hMmem (n : ℕ) (hn : N 0 ≤ n) : M n ∈ s n := by
    obtain ⟨m, hm, hmeq⟩ := Finset.exists_mem_eq_sup (s n) (hs n hn) id
    simpa [M, hmeq] using hm
  have hNM (n : ℕ) (hn : N 0 ≤ n) : N (M n) ≤ n := (Finset.mem_filter.mp (hMmem n hn)).2
  have hMsqrt (n : ℕ) : M n ≤ Nat.sqrt n := by
    apply Finset.sup_le
    intro k hk
    change k ≤ Nat.sqrt n
    have hklt := (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)
    change k < Nat.sqrt n + 1 at hklt
    omega
  have hMtop : Tendsto M atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro k
    refine ⟨max (N k) (k * k), fun n hnk => ?_⟩
    have hkmem : k ∈ s n := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr ?_, ((le_max_left (N k) (k * k)).trans hnk)⟩
      have hksqrt : k ≤ Nat.sqrt n := Nat.le_sqrt.mpr ((le_max_right (N k) (k * k)).trans hnk)
      omega
    exact Finset.le_sup (f := id) hkmem
  have hKtop : Tendsto K atTop atTop :=
    (tendsto_atTop_mono (fun n => Nat.le_succ (M n)) hMtop)
  have hKcast : Tendsto (fun n => (K n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hKtop
  have hratio : Tendsto (fun n => h n / (n : ℝ)) atTop (𝓝 0) := by
    have hi : Tendsto (fun n => ((K n : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hKcast
    apply hi.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ), hKtop.eventually_gt_atTop 0] with n hn hkn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hk0 : (K n : ℝ) ≠ 0 := by exact_mod_cast hkn.ne'
    dsimp [h]
    field_simp
  have hKupper (n : ℕ) (hn : 1 ≤ n) : (K n : ℝ) ≤ 2 * Real.sqrt n := by
    have hs1 : (1 : ℝ) ≤ Real.sqrt n := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
    calc
      (K n : ℝ) = (M n : ℝ) + 1 := by simp [K]
      _ ≤ (Nat.sqrt n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right (hMsqrt n) 1
      _ ≤ Real.sqrt n + 1 := by linarith [natCast_natSqrt_le_realSqrt n]
      _ ≤ 2 * Real.sqrt n := by linarith
  have hlower (n : ℕ) (hn : 1 ≤ n) : Real.sqrt n / 2 ≤ h n := by
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
    have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
    have hk0 : 0 < (K n : ℝ) := by positivity
    calc
      Real.sqrt n / 2 = (n : ℝ) / (2 * Real.sqrt n) := by
        field_simp
        nlinarith [Real.sq_sqrt hn0.le]
      _ ≤ (n : ℝ) / (K n : ℝ) :=
        div_le_div_of_nonneg_left hn0.le (by positivity) (hKupper n hn)
      _ = h n := rfl
  have hh : Tendsto h atTop atTop := by
    apply tendsto_atTop_mono' atTop ?_ (tendsto_sqrt_nat_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 2))
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact hlower n hn
  refine ⟨h, hh, hratio, ?_⟩
  let G : ∀ n : ℕ, Set (Fin (n - 1) → ℕ) := fun n => endpointResidualSet μ h n
  have hsub : ∀ᶠ n : ℕ in atTop, (G n)ᶜ ⊆ A (M n) n ∪ B (M n) n := by
    filter_upwards [eventually_ge_atTop (1 : ℕ),
      hh.eventually_ge_atTop (2 * (1 - (offspringMean μ).toReal)),
      hKtop.eventually_gt_atTop 0] with n hn1 hhμ hkn
    intro z hz
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn1
    have hk0 : 0 < (K n : ℝ) := by exact_mod_cast hkn
    have hKreal : ((M n + 1 : ℕ) : ℝ) = (K n : ℝ) := rfl
    simp only [G, endpointResidualSet, Set.mem_compl_iff, Set.mem_ofPred_eq, not_and, not_forall,
      not_le] at hz
    by_cases hsum : |(∑ i, (z i : ℝ)) - (offspringMean μ).toReal * (n - 1 : ℕ)| ≤ h n
    · right
      obtain ⟨i, hi⟩ := hz hsum
      have hmax : (z i : ℝ) ≤ (listMaxDegree (List.ofFn z) : ℝ) := by
        exact_mod_cast coordinate_le_listMaxDegree z i
      change ε (M n) ≤ (listMaxDegree (List.ofFn z) : ℝ) / (n : ℝ)
      have hstrict : h n < (listMaxDegree (List.ofFn z) : ℝ) := hi.trans_le hmax
      have hdiv : h n / (n : ℝ) < (listMaxDegree (List.ofFn z) : ℝ) / (n : ℝ) :=
        div_lt_div_of_pos_right hstrict hn0
      have hehalf : ε (M n) ≤ ((M n + 1 : ℕ) : ℝ)⁻¹ := by
        dsimp [ε]
        apply inv_anti₀ (by positivity)
        norm_cast
        omega
      have heq : h n / (n : ℝ) = ((K n : ℝ))⁻¹ := by
        dsimp [h]
        field_simp
      calc
        ε (M n) ≤ ((M n + 1 : ℕ) : ℝ)⁻¹ := hehalf
        _ = ((K n : ℝ))⁻¹ := congrArg (fun x : ℝ => x⁻¹) hKreal
        _ = h n / (n : ℝ) := heq.symm
        _ ≤ (listMaxDegree (List.ofFn z) : ℝ) / (n : ℝ) := hdiv.le
    · left
      change ε (M n) ≤ |finitePreviousWalkAverage n z - (1 - (offspringMean μ).toReal)|
      rw [finitePreviousWalkAverage_error μ n z (by omega), abs_div, abs_of_pos hn0,
        le_div_iff₀ hn0]
      have hdiff : h n - (1 - (offspringMean μ).toReal) ≤
          |(offspringMean μ).toReal * n - 1 - ∑ i, (z i : ℝ)| := by
        have hmR : (offspringMean μ).toReal < 1 := by
          simpa using (ENNReal.toReal_lt_toReal hfin ENNReal.one_ne_top).mpr hm
        have htri := abs_sub_abs_le_abs_sub
          ((∑ i, (z i : ℝ)) - (offspringMean μ).toReal * (n - 1 : ℕ))
          ((offspringMean μ).toReal - 1)
        have habsm : |(offspringMean μ).toReal - 1| = 1 - (offspringMean μ).toReal :=
          by simpa only [neg_sub] using abs_of_nonpos (sub_nonpos.mpr hmR.le)
        have heq : |(∑ i, (z i : ℝ)) - (offspringMean μ).toReal * (n - 1 : ℕ) -
            ((offspringMean μ).toReal - 1)| =
            |(offspringMean μ).toReal * n - 1 - ∑ i, (z i : ℝ)| := by
          calc
            _ = |-((offspringMean μ).toReal * n - 1 - ∑ i, (z i : ℝ))| := by
              congr 1
              rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
              ring
            _ = _ := abs_neg _
        rw [habsm, heq] at htri
        exact (sub_le_sub_right (le_of_not_ge hsum) _).trans htri
      have heps : ε (M n) * (n : ℝ) = h n / 2 := by
        dsimp [ε, h]
        rw [hKreal]
        field_simp
      rw [heps]
      have hmle : (offspringMean μ).toReal ≤ 1 := by
        have hmR : (offspringMean μ).toReal < 1 := by
          simpa using (ENNReal.toReal_lt_toReal hfin ENNReal.one_ne_top).mpr hm
        exact hmR.le
      linarith
  have hcomp0 : Tendsto (fun n => (P n).real (G n)ᶜ) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun n => measureReal_nonneg)
    · filter_upwards [hsub, eventually_ge_atTop (max 1 (N 0)), hKtop.eventually_gt_atTop 0]
        with n hnsub hn1 hkn
      have hb := (hN (M n) n (hNM n ((le_max_right 1 (N 0)).trans hn1))).le
      exact (measureReal_mono hnsub (measure_ne_top (P n) _)).trans <|
        (measureReal_union_le _ _).trans hb
    · have hi : Tendsto (fun n => ((K n : ℝ))⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp hKcast
      exact hi
  have hprob (n : ℕ) : (P n).real (G n) + (P n).real (G n)ᶜ = 1 := by
    have hp := measureReal_add_measureReal_compl (μ := P n) (Set.to_countable (G n)).measurableSet
    simpa [P] using hp
  have heq : (fun n => (P n).real (G n)) =ᶠ[atTop]
      (fun n => 1 - (P n).real (G n)ᶜ) := Eventually.of_forall (fun n => by linarith [hprob n])
  have hlim := (tendsto_const_nhds (x := (1 : ℝ))).sub hcomp0
  simpa only [sub_zero, G, P] using hlim.congr' heq.symm


/-- On the typical residual set, the missing count is large, strictly maximal,
and its mass is uniformly comparable with the mass at `⌊γn⌋`. -/
theorem endpointResidualSet_eventually_good
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ < 1)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1))
    {h : ℕ → ℝ} (hh : Tendsto h atTop atTop)
    (hη : Tendsto (fun n => h n / (n : ℝ)) atTop (𝓝 0)) :
    ∀ τ : ℝ, 0 < τ → ∀ᶠ n : ℕ in atTop, ∀ z ∈ endpointResidualSet μ h n,
      ∑ i, z i < n - 1 ∧
      (∀ i, z i < n - 1 - ∑ i, z i) ∧
      |(μ {n - 1 - ∑ i, z i}).toReal / (μ {⌊(1 - (offspringMean μ).toReal) * n⌋₊}).toReal - 1| < τ := by
  classical
  let m := (offspringMean μ).toReal
  let γ := 1 - m
  have hfin : offspringMean μ ≠ ∞ := ne_top_of_lt (hm.trans ENNReal.one_lt_top)
  have hmR : m < 1 := by
    simpa [m] using (ENNReal.toReal_lt_toReal hfin ENNReal.one_ne_top).mpr hm
  have hγ : 0 < γ := sub_pos.mpr hmR
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  have hγ1 : γ ≤ 1 := by dsimp [γ]; linarith
  have hμ : IsMeasurableSubcriticalCauchyOffspring μ := ⟨hm, L, hpos, hsv, hL, hlocal⟩
  have hsmall : ∀ᶠ n : ℕ in atTop, |h n / (n : ℝ)| < γ / 4 := by
    have ht := hη.abs
    simp only [abs_zero] at ht
    exact ht.eventually (gt_mem_nhds (by positivity))
  have hstruct : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) ∧ 2 * h n < γ * ((n - 1 : ℕ) : ℝ) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ), hh.eventually_gt_atTop 0, hsmall]
      with n hn2 hhn hn
    have hn1 : 1 ≤ n := by omega
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hncast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn1, Nat.cast_one]
    have hnabs : |h n / (n : ℝ)| = h n / (n : ℝ) := abs_of_pos (div_pos hhn hn0)
    rw [hnabs, div_lt_iff₀ hn0] at hn
    refine ⟨hn0, ?_⟩
    have hnle : (n : ℝ) ≤ 2 * ((n - 1 : ℕ) : ℝ) := by
      rw [hncast]
      have hn2R : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      linarith
    calc
      2 * h n < 2 * (γ / 4 * n) := by linarith
      _ = γ * (n : ℝ) / 2 := by ring
      _ ≤ γ * ((n - 1 : ℕ) : ℝ) := by nlinarith
  let d : ℕ → ℝ := fun n => (2 / γ) * (h n + 2) / (n : ℝ)
  have hd : Tendsto d atTop (𝓝 0) := by
    have ht := (hη.add (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ))).const_mul (2 / γ)
    have heq : (fun n => (2 / γ) * (h n / (n : ℝ) + 2 / (n : ℝ))) =ᶠ[atTop] d := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      dsimp [d]
      field_simp
    simpa only [add_zero, mul_zero] using ht.congr' heq
  have hz : Tendsto (fun n : ℕ => (γ / 4) * (n : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by positivity)
  have hrat := uniform_nat_mass_ratio μ hμ hz hd
  intro τ hτ
  filter_upwards [hstruct, hrat τ hτ, hh.eventually_gt_atTop 0,
    ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hγ).eventually_ge_atTop 2,
    hsmall] with n hn hnr hhn hγn hns
  intro z hzG
  obtain ⟨hn0, hhbound⟩ := hn
  have hnpos : 0 < n := by exact_mod_cast hn0
  have hn1 : 1 ≤ n := hnpos
  have hδ := abs_le.mp hzG.1
  have hreal : γ * ((n - 1 : ℕ) : ℝ) = ((n - 1 : ℕ) : ℝ) - m * ((n - 1 : ℕ) : ℝ) := by
    dsimp [γ]; ring
  have hsumlt : ∑ i, z i < n - 1 := by
    by_contra hnot
    have hleN : n - 1 ≤ ∑ i, z i := by omega
    have hle : ((n - 1 : ℕ) : ℝ) ≤ ∑ i, (z i : ℝ) := by exact_mod_cast hleN
    have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
    nlinarith [hδ.2]
  have kn : ((n - 1 - ∑ i, z i : ℕ) : ℝ) = ((n - 1 : ℕ) : ℝ) - ∑ i, (z i : ℝ) := by
    rw [Nat.cast_sub hsumlt.le]
    simp only [Nat.cast_sum]
  have hklower : γ * ((n - 1 : ℕ) : ℝ) - h n ≤ ((n - 1 - ∑ i, z i : ℕ) : ℝ) := by
    rw [kn]
    nlinarith [hδ.2]
  have hmax : ∀ i, z i < n - 1 - ∑ i, z i := by
    intro i
    have hi := hzG.2 i
    by_contra hnot
    have hle : ((n - 1 - ∑ i, z i : ℕ) : ℝ) ≤ (z i : ℝ) := by exact_mod_cast Nat.le_of_not_gt hnot
    nlinarith
  refine ⟨hsumlt, hmax, ?_⟩
  let j := ⌊γ * (n : ℝ)⌋₊
  let k := n - 1 - ∑ i, z i
  have hγcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hjlow : γ * (n : ℝ) - 1 ≤ (j : ℝ) := by
    dsimp [j]
    linarith [Nat.sub_one_lt_floor (γ * (n : ℝ))]
  have hjupper : (j : ℝ) ≤ γ * (n : ℝ) := by
    dsimp [j]
    exact Nat.floor_le (by positivity)
  have hjpos : 0 < (j : ℝ) := by
    have hnle : (2 : ℝ) ≤ γ * n := hγn
    linarith
  have hkdiff : (k : ℝ) = γ * (n : ℝ) - ((∑ i, (z i : ℝ)) - m * ((n - 1 : ℕ) : ℝ)) - γ := by
    dsimp [k, γ]
    rw [kn, hγcast]
    dsimp [m]
    ring
  have hkabs : |(k : ℝ) - (j : ℝ)| ≤ h n + 2 := by
    rw [abs_le, hkdiff]
    have hfloorlo : γ * (n : ℝ) - 1 ≤ (j : ℝ) := hjlow
    have hfloorhi : (j : ℝ) ≤ γ * (n : ℝ) := hjupper
    have hδ' : -h n ≤ (∑ i, (z i : ℝ)) - m * ((n - 1 : ℕ) : ℝ) ∧
        (∑ i, (z i : ℝ)) - m * ((n - 1 : ℕ) : ℝ) ≤ h n := by
      exact hδ
    constructor <;> linarith
  have hbasej : (γ / 4) * n ≤ (j : ℝ) := by
    have hhalf : (γ / 2) * n ≤ (j : ℝ) := by nlinarith
    nlinarith
  have hbasek : (γ / 4) * n ≤ (k : ℝ) := by
    have hne : (n : ℝ) ≤ 2 * ((n - 1 : ℕ) : ℝ) := by
      rw [hγcast]
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
      linarith
    dsimp [k]
    nlinarith
  apply hnr j k hbasej
  have hkj : (k : ℝ) / (j : ℝ) - 1 = ((k : ℝ) - (j : ℝ)) / (j : ℝ) := by
    rw [sub_div, div_self hjpos.ne']
  rw [hkj, abs_div, abs_of_pos hjpos, abs_of_nonneg (by positivity : 0 ≤ d n)]
  have hnum := div_le_div_of_nonneg_right hkabs hjpos.le
  have hden : (h n + 2) / (j : ℝ) ≤ (h n + 2) / ((γ / 2) * n) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith
  have heqd : (h n + 2) / ((γ / 2) * n) = d n := by
    dsimp [d]
    field_simp
  exact hnum.trans (hden.trans_eq heqd)


/-- Product weights of all strict-maximum insertions give a lower bound on the
endpoint mass. This is a purely combinatorial weight estimate. -/
theorem endpoint_lower_of_insertions_succ
    (μ : Measure ℕ) [IsProbabilityMeasure μ] {m j : ℕ}
    (G : Set (Fin m → ℕ)) (a : ℝ≥0∞)
    (hins : ∀ z ∈ G, ∑ i, z i < m ∧
      (∀ i, z i < m - ∑ i, z i))
    (hmass : ∀ z ∈ G, a * μ {j} ≤ μ {m - ∑ i, z i}) :
    a * ((m + 1 : ℕ) : ℝ≥0∞) * μ {j} * (Measure.pi fun _ : Fin m => μ) G ≤
      (Measure.pi fun _ : Fin (m + 1) => μ) (BGW.countBridges (m + 1)) := by
  classical
  let w : (Fin m → ℕ) → ℝ≥0∞ := fun z => ∏ i, μ {z i}
  let r : (Fin m → ℕ) → ℕ := fun z => m - ∑ i, z i
  let f : (G × Fin (m + 1)) → (Fin (m + 1) → ℕ) := fun x =>
    Fin.insertNth x.2 (r x.1.1) x.1.1
  have hf_bridge (x : G × Fin (m + 1)) : f x ∈ BGW.countBridges (m + 1) := by
    have hi := hins x.1.1 x.1.2
    change (∑ j, f x j) + 1 = m + 1
    dsimp [f]
    rw [Fin.sum_insertNth]
    dsimp [r]
    omega
  have hf_weight (x : G × Fin (m + 1)) :
      (∏ j, μ {f x j}) = μ {r x.1.1} * w x.1.1 := by
    dsimp [f]
    rw [← Fin.prod_insertNth (M := ℝ≥0∞) x.2 (μ {r x.1.1}) (fun j => μ {x.1.1 j})]
    apply Finset.prod_congr rfl
    intro k _
    refine Fin.succAboveCases x.2 ?_ (fun i => ?_) k <;> simp
  have hfinj : Function.Injective f := by
    rintro ⟨z, i⟩ ⟨y, l⟩ hxy
    have hzgood := hins z.1 z.2
    have hygood := hins y.1 y.2
    have hdel := congrArg (deletedIncrements (m + 1)) hxy
    change Fin.insertNth (α := fun _ => ℕ) i (r z.1) z.1 = Fin.insertNth (α := fun _ => ℕ) l (r y.1) y.1 at hxy
    change deletedIncrements (m + 1) (Fin.insertNth (α := fun _ => ℕ) i (r z.1) z.1) =
      deletedIncrements (m + 1) (Fin.insertNth (α := fun _ => ℕ) l (r y.1) y.1) at hdel
    rw [deletedIncrements_insertNth i (r z.1) z.1 hzgood.2,
      deletedIncrements_insertNth l (r y.1) y.1 hygood.2] at hdel
    have hzyfun : z.1 = y.1 := by
      funext k
      have hk := congrFun hdel k
      omega
    have hzy : z = y := Subtype.ext hzyfun
    subst y
    have hil : i = l := insertNth_injective_left_of_lt (r z.1) z.1 hzgood.2 hxy
    subst l
    rfl
  have hPG : (Measure.pi fun _ : Fin m => μ) G = ∑' z : G, w z.1 := by
    rw [BGW.pi_eq_tsum_indicator, ← tsum_subtype]
  have hsum_scalar : (∑' x : G × Fin (m + 1), a * μ {j} * w x.1.1) =
      a * ((m + 1 : ℕ) : ℝ≥0∞) * μ {j} * (Measure.pi fun _ : Fin m => μ) G := by
    calc
      (∑' x : G × Fin (m + 1), a * μ {j} * w x.1.1) =
          ∑' z : G, ∑' _i : Fin (m + 1), a * μ {j} * w z.1 := ENNReal.tsum_prod (f := fun (z : G) (_i : Fin (m + 1)) => a * μ {j} * w z.1)
      _ = ∑' z : G, ((m + 1 : ℕ) : ℝ≥0∞) * (a * μ {j} * w z.1) := by
        apply tsum_congr
        intro z
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = _ := ?_
    simp_rw [show ∀ z : G, ((m + 1 : ℕ) : ℝ≥0∞) * (a * μ {j} * w z.1) =
      (a * ((m + 1 : ℕ) : ℝ≥0∞) * μ {j}) * w z.1 from fun z => by ring]
    rw [ENNReal.tsum_mul_left, hPG]
  calc
    a * ((m + 1 : ℕ) : ℝ≥0∞) * μ {j} * (Measure.pi fun _ : Fin m => μ) G =
        ∑' x : G × Fin (m + 1), a * μ {j} * w x.1.1 := hsum_scalar.symm
    _ ≤ ∑' x : G × Fin (m + 1),
        (BGW.countBridges (m + 1)).indicator (fun ω => ∏ i, μ {ω i}) (f x) := by
      apply ENNReal.tsum_le_tsum
      intro x
      rw [Set.indicator_of_mem (hf_bridge x), hf_weight]
      change a * μ {j} * w x.1.1 ≤ μ {m - ∑ i, x.1.1 i} * w x.1.1
      simpa only [mul_comm] using mul_le_mul_right (hmass x.1.1 x.1.2) (w x.1.1)
    _ ≤ ∑' ω : Fin (m + 1) → ℕ,
        (BGW.countBridges (m + 1)).indicator (fun ω => ∏ i, μ {ω i}) ω :=
      ENNReal.tsum_comp_le_tsum_of_injective hfinj _
    _ = (Measure.pi fun _ : Fin (m + 1) => μ) (BGW.countBridges (m + 1)) :=
      (BGW.pi_eq_tsum_indicator μ _).symm




/-- Endpoint lower bound for a supplied typical residual scale. -/
theorem endpoint_lower_bound_with_scale
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ < 1)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1))
    {h : ℕ → ℝ} (hh : Tendsto h atTop atTop)
    (hη : Tendsto (fun n => h n / (n : ℝ)) atTop (𝓝 0))
    (hG : Tendsto (fun n : ℕ => (Measure.pi fun _ : Fin (n - 1) => μ).real
      (endpointResidualSet μ h n)) atTop (𝓝 1)) :
    ∀ τ : ℝ, 0 < τ → ∀ᶠ n : ℕ in atTop,
      (1 - τ) * n * (μ {⌊(1 - (offspringMean μ).toReal) * n⌋₊}).toReal ≤
        ((Measure.pi fun _ : Fin n => μ) (BGW.countBridges n)).toReal := by
  classical
  intro τ hτ
  by_cases hτ1 : 1 ≤ τ
  · filter_upwards [] with n
    exact (mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hτ1) (Nat.cast_nonneg _))
      ENNReal.toReal_nonneg).trans ENNReal.toReal_nonneg
  have hτ1' : τ < 1 := lt_of_not_ge hτ1
  let δ := τ / 2
  have hδ : 0 < δ := by positivity
  have hδ1 : δ < 1 := by dsimp [δ]; linarith
  have hgood := endpointResidualSet_eventually_good μ hm hpos hL hsv hlocal hh hη δ hδ
  have hPG : ∀ᶠ n : ℕ in atTop,
      1 - δ < (Measure.pi fun _ : Fin (n - 1) => μ).real (endpointResidualSet μ h n) :=
    hG.eventually (lt_mem_nhds (by linarith : 1 - δ < 1))
  filter_upwards [hgood, hPG, eventually_ge_atTop (1 : ℕ)] with n hn hPn hn1
  cases n with
  | zero => omega
  | succ k =>
    simp only [Nat.add_sub_cancel] at hn hPn ⊢
    let G := endpointResidualSet μ h (k + 1)
    let j := ⌊(1 - (offspringMean μ).toReal) * (k + 1 : ℕ)⌋₊
    let a := ENNReal.ofReal (1 - δ)
    have hmass (z : Fin k → ℕ) (hz : z ∈ G) : a * μ {j} ≤ μ {k - ∑ i, z i} := by
      have hz' : z ∈ endpointResidualSet μ h (k + 1) := hz
      obtain ⟨hsum, hmax, hratio⟩ := hn z hz'
      have hlow : 1 - δ < (μ {k - ∑ i, z i}).toReal / (μ {j}).toReal - 1 + 1 := by
        have hh := (abs_lt.mp hratio).1
        dsimp [a, j] at *
        linarith
      have hrpos : 0 < (μ {k - ∑ i, z i}).toReal / (μ {j}).toReal := by linarith
      have hqpos : 0 < (μ {j}).toReal := by
        by_contra hq
        have hqz : (μ {j}).toReal = 0 := le_antisymm (le_of_not_gt hq) ENNReal.toReal_nonneg
        rw [hqz, div_zero] at hrpos
        exact (lt_irrefl 0 hrpos)
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)]
      calc
        (1 - δ) * (μ {j}).toReal ≤
            ((μ {k - ∑ i, z i}).toReal / (μ {j}).toReal) * (μ {j}).toReal :=
          mul_le_mul_of_nonneg_right (by linarith) ENNReal.toReal_nonneg
        _ = (μ {k - ∑ i, z i}).toReal := div_mul_cancel₀ _ hqpos.ne'
    have hPn' : 1 - δ < (Measure.pi fun _ : Fin k => μ).real G := hPn
    have hlo := endpoint_lower_of_insertions_succ μ G a
      (fun z hz => let hz' : z ∈ endpointResidualSet μ h (k + 1) := hz
        let hh := hn z hz'
        ⟨hh.1, hh.2.1⟩) hmass
    have heq : k + 1 - 1 + 1 = k + 1 := by omega
    rw [heq] at hlo
    have hloR := (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mpr hlo
    simp only [ENNReal.toReal_mul, Nat.cast_add, Nat.cast_one] at hloR
    have hkc : ((k : ℝ≥0∞) + 1).toReal = (k : ℝ) + 1 := by
      rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_natCast,
        ENNReal.toReal_one]
    rw [hkc] at hloR
    dsimp [j] at hloR
    push_cast at hloR ⊢
    have hq0 : 0 ≤ (μ {⌊(1 - (offspringMean μ).toReal) * (↑k + 1 : ℝ)⌋₊}).toReal := ENNReal.toReal_nonneg
    have hk0 : 0 ≤ (k + 1 : ℝ) := by positivity
    calc
      (1 - τ) * (k + 1 : ℝ) * (μ {⌊(1 - (offspringMean μ).toReal) * (↑k + 1 : ℝ)⌋₊}).toReal ≤
          (1 - δ) * (1 - δ) * (k + 1 : ℝ) * (μ {⌊(1 - (offspringMean μ).toReal) * (↑k + 1 : ℝ)⌋₊}).toReal := by
        apply mul_le_mul_of_nonneg_right _ hq0
        apply mul_le_mul_of_nonneg_right _ hk0
        dsimp [δ]
        nlinarith [sq_nonneg (τ / 2)]
      _ ≤ (1 - δ) * (k + 1 : ℝ) * (μ {⌊(1 - (offspringMean μ).toReal) * (↑k + 1 : ℝ)⌋₊}).toReal *
          (Measure.pi fun _ : Fin k => μ).real G := by
        have hfac : 0 ≤ (1 - δ) * (k + 1 : ℝ) * (μ {⌊(1 - (offspringMean μ).toReal) * (↑k + 1 : ℝ)⌋₊}).toReal := by positivity
        nlinarith
      _ ≤ _ := by
        simpa only [j, a, Measure.real, ENNReal.toReal_ofReal (show 0 ≤ 1 - δ by linarith)] using hloR


/-- Singleton mass ratios have a positive power limit along integer sequences
with a positive limiting ratio. -/
theorem paper_mass_ratio_of_ratio_tendsto
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ)
    {j k : ℕ → ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    (hj : Tendsto j atTop atTop) (hk : Tendsto k atTop atTop)
    (hr : Tendsto (fun n => (k n : ℝ) / (j n : ℝ)) atTop (𝓝 ρ)) :
    Tendsto (fun n => (μ {k n}).toReal / (μ {j n}).toReal)
      atTop (𝓝 ((ρ ^ 2)⁻¹)) := by
  obtain ⟨hm, L, hpos, hsv, hmeas, hlocal⟩ := hμ
  have hjR : Tendsto (fun n => (j n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hj
  have hkR : Tendsto (fun n => (k n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hk
  have hLrat : Tendsto (fun n => L (k n) / L (j n)) atTop (𝓝 1) := by
    have h := slowlyVarying_uniform_sequential hpos hmeas hsv hjR hr hρ
    apply h.congr'
    filter_upwards [hjR.eventually_gt_atTop 0] with n hn
    rw [div_mul_cancel₀ _ hn.ne']
  have hratio := (hlocal.comp hk).div (hlocal.comp hj) one_ne_zero
  have hinv := ((tendsto_const_nhds (x := (1 : ℝ))).div hr hρ.ne').pow 2
  have htotal := (hratio.mul hLrat).mul hinv
  have heq : (fun n =>
      ((μ {k n}).toReal / (L (k n) / (k n : ℝ) ^ 2)) /
        ((μ {j n}).toReal / (L (j n) / (j n : ℝ) ^ 2)) *
          (L (k n) / L (j n)) * (1 / ((k n : ℝ) / (j n : ℝ))) ^ 2) =ᶠ[atTop]
      (fun n => (μ {k n}).toReal / (μ {j n}).toReal) := by
    filter_upwards [hjR.eventually_gt_atTop 0,
      hkR.eventually_gt_atTop 0,
      (hlocal.comp hj).eventually (lt_mem_nhds zero_lt_one)] with n hjn hkn hmass
    have hLjn := (hpos _ hjn).ne'
    have hLkn := (hpos _ hkn).ne'
    have hμjn : (μ {j n}).toReal ≠ 0 := by
      have hden : 0 < L (j n) / (j n : ℝ) ^ 2 := div_pos (hpos _ hjn) (sq_pos_of_pos hjn)
      exact ((div_pos_iff_of_pos_right hden).mp hmass).ne'
    field_simp [hμjn, hLjn, hLkn, hjn.ne', hkn.ne']
  have hlim := htotal.congr' heq
  convert hlim using 1; field_simp

/-- A uniform bound for singleton mass ratios over a compact interval of
integer-index ratios. -/
theorem uniform_nat_mass_ratio_compact
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ)
    {a b : ℝ} (ha : 0 < a) (_hab : a ≤ b)
    {z : ℕ → ℝ} (hz : Tendsto z atTop atTop) :
    ∀ᶠ n : ℕ in atTop, ∀ j k : ℕ, z n ≤ (j : ℝ) →
      (k : ℝ) / (j : ℝ) ∈ Set.Icc a b →
      (μ {k}).toReal / (μ {j}).toReal < (a ^ 2)⁻¹ + 1 := by
  classical
  by_contra hnot
  have hbad (N : ℕ) : ∃ (n j k : ℕ), N ≤ n ∧ z n ≤ (j : ℝ) ∧
      (k : ℝ) / (j : ℝ) ∈ Set.Icc a b ∧
      (a ^ 2)⁻¹ + 1 ≤ (μ {k}).toReal / (μ {j}).toReal := by
    by_contra hnone
    apply hnot
    refine eventually_atTop.mpr ⟨N, ?_⟩
    intro n hn j k hbase hratio
    by_contra herr
    exact hnone ⟨n, j, k, hn, hbase, hratio, le_of_not_gt herr⟩
  choose ns js ks hN hbase hcs herr using hbad
  have hns : Tendsto ns atTop atTop := tendsto_atTop_mono hN tendsto_id
  have hjsN : Tendsto js atTop atTop := tendsto_natCast_atTop_iff.mp
    (tendsto_atTop_mono hbase (hz.comp hns))
  have hjs : Tendsto (fun n => (js n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hjsN
  obtain ⟨ρ, hρmem, φ, hφ, hρ⟩ := isCompact_Icc.tendsto_subseq hcs
  have hρ0 : 0 < ρ := ha.trans_le hρmem.1
  have hjsSub : Tendsto (fun n => (js (φ n) : ℝ)) atTop atTop := hjs.comp hφ.tendsto_atTop
  have hjsSubN : Tendsto (fun n => js (φ n)) atTop atTop := hjsN.comp hφ.tendsto_atTop
  have hksSub : Tendsto (fun n => (ks (φ n) : ℝ)) atTop atTop := by
    apply (hjsSub.atTop_mul_pos hρ0 hρ).congr'
    filter_upwards [hjsSub.eventually_gt_atTop 0] with n hn
    simp only [Function.comp_def]
    field_simp
  have hksSubN : Tendsto (fun n => ks (φ n)) atTop atTop :=
    tendsto_natCast_atTop_iff.mp hksSub
  have hmass := paper_mass_ratio_of_ratio_tendsto μ hμ hρ0 hjsSubN hksSubN hρ
  have hρpow : (ρ ^ 2)⁻¹ ≤ (a ^ 2)⁻¹ := by
    apply inv_anti₀ (sq_pos_of_pos ha)
    exact pow_le_pow_left₀ ha.le hρmem.1 2
  have hlt : (ρ ^ 2)⁻¹ < (a ^ 2)⁻¹ + 1 := by linarith
  obtain ⟨n, hn⟩ := (hmass.eventually (gt_mem_nhds hlt)).exists
  exact (not_lt_of_ge (herr (φ n))) hn


/-- Union bound over the position of a big count, with an exact residual tail
weight for each fixed position. -/
theorem endpoint_bigJump_union_bound
    (μ : Measure ℕ) [IsProbabilityMeasure μ] {m : ℕ} {c : ℝ} (hc : 0 ≤ c) :
    (Measure.pi fun _ : Fin (m + 1) => μ)
      {ω | ∑ i, ω i = m ∧ ∃ i, c * (m + 1 : ℕ) < (ω i : ℝ)} ≤
      ((m + 1 : ℕ) : ℝ≥0∞) * ∑' z : Fin m → ℕ,
        (if c * (m + 1 : ℕ) < ((m - ∑ i, z i : ℕ) : ℝ) then
          μ {m - ∑ i, z i} else 0) * (∏ i, μ {z i}) := by
  classical
  let N : ℝ := (m + 1 : ℕ)
  let A : Fin (m + 1) → Set (Fin (m + 1) → ℕ) := fun i =>
    {ω | ∑ j, ω j = m ∧ c * N < (ω i : ℝ)}
  let w : (Fin m → ℕ) → ℝ≥0∞ := fun z => ∏ j, μ {z j}
  have hpos (i : Fin (m + 1)) : (Measure.pi fun _ : Fin (m + 1) => μ) (A i) ≤
      ∑' z : Fin m → ℕ,
        (if c * N < ((m - ∑ j, z j : ℕ) : ℝ) then μ {m - ∑ j, z j} else 0) * w z := by
    let e := Fin.insertNthEquiv (fun _ : Fin (m + 1) => ℕ) i
    let g : (Fin (m + 1) → ℕ) → ℝ≥0∞ := fun ω =>
      (A i).indicator (fun v => ∏ j, μ {v j}) ω
    have hweight (r : ℕ) (z : Fin m → ℕ) :
        (∏ j, μ {Fin.insertNth (α := fun _ => ℕ) i r z j}) = μ {r} * w z := by
      rw [← Fin.prod_insertNth (M := ℝ≥0∞) i (μ {r}) (fun j => μ {z j})]
      apply Finset.prod_congr rfl
      intro k _
      refine Fin.succAboveCases i ?_ (fun j => ?_) k <;> simp
    have hterm (z : Fin m → ℕ) : (∑' r : ℕ, g (e (r, z))) =
        (if c * N < ((m - ∑ j, z j : ℕ) : ℝ) then μ {m - ∑ j, z j} else 0) * w z := by
      by_cases hsm : ∑ j, z j ≤ m
      · let r₀ := m - ∑ j, z j
        have hrs : r₀ + ∑ j, z j = m := by dsimp [r₀]; omega
        have hne (r : ℕ) (hr : r ≠ r₀) : g (e (r, z)) = 0 := by
          apply Set.indicator_of_notMem
          intro hmem
          change ∑ j, Fin.insertNth (α := fun _ => ℕ) i r z j = m ∧ _ at hmem
          rw [Fin.sum_insertNth] at hmem
          exact hr (by dsimp [r₀]; omega)
        rw [tsum_eq_single r₀ hne]
        by_cases hbig : c * N < (r₀ : ℝ)
        · dsimp [r₀] at hbig
          have hmem : e (r₀, z) ∈ A i := by
            change ∑ j, Fin.insertNth (α := fun _ => ℕ) i r₀ z j = m ∧ _
            rw [Fin.sum_insertNth, hrs]
            exact ⟨rfl, by
              simpa only [e, Fin.insertNthEquiv_apply, Fin.insertNth_apply_same] using hbig⟩
          change (A i).indicator (fun v => ∏ j, μ {v j}) (e (r₀, z)) = _
          rw [Set.indicator_of_mem hmem]
          change (∏ j, μ {Fin.insertNth (α := fun _ => ℕ) i r₀ z j}) = _
          rw [hweight]
          simp only [hbig, ↓reduceIte]
          rfl
        · dsimp [r₀] at hbig
          have hnotmem : e (r₀, z) ∉ A i := by
            intro hmem
            change ∑ j, Fin.insertNth (α := fun _ => ℕ) i r₀ z j = m ∧ _ at hmem
            rw [Fin.sum_insertNth, hrs] at hmem
            apply hbig
            simpa only [e, Fin.insertNthEquiv_apply, Fin.insertNth_apply_same] using hmem.2
          change (A i).indicator (fun v => ∏ j, μ {v j}) (e (r₀, z)) = _
          rw [Set.indicator_of_notMem hnotmem]
          simp only [hbig, ↓reduceIte, zero_mul]
      · have hz : ∀ r : ℕ, ¬r + ∑ j, z j = m := by
          intro r hr
          have hrle : r ≤ m := by omega
          omega
        have hzero : ∀ r : ℕ, g (e (r, z)) = 0 := by
          intro r
          apply Set.indicator_of_notMem
          intro hmem
          change ∑ j, Fin.insertNth (α := fun _ => ℕ) i r z j = m ∧ _ at hmem
          rw [Fin.sum_insertNth] at hmem
          exact hz r hmem.1
        simp_rw [hzero, tsum_zero]
        have hnotbig : ¬c * N < ((m - ∑ j, z j : ℕ) : ℝ) := by
          have hm0 : m - ∑ j, z j = 0 := by omega
          rw [hm0, Nat.cast_zero]
          exact not_lt_of_ge (mul_nonneg hc (by positivity))
        simp only [hnotbig, ↓reduceIte, zero_mul]
    calc
      (Measure.pi fun _ : Fin (m + 1) => μ) (A i) = ∑' ω, g ω := by
        rw [BGW.pi_eq_tsum_indicator]
      _ = ∑' p : ℕ × (Fin m → ℕ), g (e p) := (e.tsum_eq g).symm
      _ = ∑' r : ℕ, ∑' z : Fin m → ℕ, g (e (r, z)) :=
        ENNReal.tsum_prod (f := fun (r : ℕ) (z : Fin m → ℕ) => g (e (r, z)))
      _ = ∑' z : Fin m → ℕ, ∑' r : ℕ, g (e (r, z)) := ENNReal.tsum_comm
      _ ≤ _ := le_of_eq (tsum_congr hterm)
  calc
    (Measure.pi fun _ : Fin (m + 1) => μ)
        {ω | ∑ i, ω i = m ∧ ∃ i, c * (m + 1 : ℕ) < (ω i : ℝ)} ≤
        (Measure.pi fun _ : Fin (m + 1) => μ) (⋃ i, A i) := by
      apply measure_mono
      rintro ω ⟨hsum, i, hi⟩
      exact Set.mem_iUnion.mpr ⟨i, hsum, hi⟩
    _ ≤ ∑' i : Fin (m + 1), (Measure.pi fun _ : Fin (m + 1) => μ) (A i) := measure_iUnion_le _
    _ ≤ ∑' _i : Fin (m + 1), ∑' z : Fin m → ℕ,
        (if c * N < ((m - ∑ j, z j : ℕ) : ℝ) then μ {m - ∑ j, z j} else 0) * w z :=
      ENNReal.tsum_le_tsum hpos
    _ = _ := by
      rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]


/-- Big-jump upper bound for a supplied typical residual scale. -/
theorem endpoint_bigJump_upper_with_scale
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ < 1)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1))
    {h : ℕ → ℝ} (hh : Tendsto h atTop atTop)
    (hη : Tendsto (fun n => h n / (n : ℝ)) atTop (𝓝 0))
    (hG : Tendsto (fun n : ℕ => (Measure.pi fun _ : Fin (n - 1) => μ).real
      (endpointResidualSet μ h n)) atTop (𝓝 1))
    {c : ℝ} (hc : 0 < c) (hcγ : c < 1 - (offspringMean μ).toReal) :
    ∀ τ : ℝ, 0 < τ → ∀ᶠ n : ℕ in atTop,
      ((Measure.pi fun _ : Fin n => μ)
        {ω | ∑ i, ω i = n - 1 ∧ ∃ i, c * n < (ω i : ℝ)}).toReal ≤
        (1 + τ) * n * (μ {⌊(1 - (offspringMean μ).toReal) * n⌋₊}).toReal := by
  classical
  let γ := 1 - (offspringMean μ).toReal
  have hfin : offspringMean μ ≠ ∞ := ne_top_of_lt (hm.trans ENNReal.one_lt_top)
  have hmR : (offspringMean μ).toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hfin ENNReal.one_ne_top).mpr hm
  have hγ : 0 < γ := by dsimp [γ]; linarith
  have hμ : IsMeasurableSubcriticalCauchyOffspring μ := ⟨hm, L, hpos, hsv, hL, hlocal⟩
  have hfloor : Tendsto (fun n : ℕ => ⌊γ * (n : ℝ)⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hγ)
  have hjpos0 : ∀ᶠ n : ℕ in atTop, 0 < μ {⌊γ * (n : ℝ)⌋₊} :=
    hfloor.eventually (eventually_mass_pos μ hμ.to_literal)
  have hcomp : ∀ᶠ n : ℕ in atTop, ∀ z : Fin (n - 1) → ℕ,
      z ∉ endpointResidualSet μ h n → c * n < ((n - 1 - ∑ i, z i : ℕ) : ℝ) →
      (μ {n - 1 - ∑ i, z i}).toReal / (μ {⌊γ * n⌋₊}).toReal <
        ((c / (2 * γ)) ^ 2)⁻¹ + 1 := by
    have hbase := uniform_nat_mass_ratio_compact μ hμ
      (a := c / (2 * γ)) (b := 2 / γ) (by positivity) (by
        have hm0 : 0 ≤ (offspringMean μ).toReal := ENNReal.toReal_nonneg
        have hs : c / 2 ≤ (2 : ℝ) := by linarith
        simpa only [div_div] using div_le_div_of_nonneg_right hs hγ.le)
      (show Tendsto (fun n : ℕ => (γ / 2) * (n : ℝ)) atTop atTop from
        (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by positivity))
    filter_upwards [hbase, hfloor.eventually_ge_atTop 1,
      eventually_ge_atTop (2 : ℕ)] with n hn hj hn2
    intro z hz hbig
    let j := ⌊γ * (n : ℝ)⌋₊
    let k := n - 1 - ∑ i, z i
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hγn : 0 < γ * (n : ℝ) := by positivity
    have hjlo : γ * (n : ℝ) - 1 ≤ (j : ℝ) := by
      dsimp [j]; linarith [Nat.sub_one_lt_floor (γ * (n : ℝ))]
    have hjhi : (j : ℝ) ≤ γ * (n : ℝ) := Nat.floor_le hγn.le
    have hjpos : 0 < (j : ℝ) := by exact_mod_cast hj
    have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hkbig : c * (n : ℝ) < (k : ℝ) := by exact hbig
    apply hn j k
    · dsimp [j]
      nlinarith
    · constructor
      · apply (le_div_iff₀ hjpos).mpr
        change (c / (2 * γ)) * (j : ℝ) ≤ (k : ℝ)
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * γ)]
        have hm1 := mul_le_mul_of_nonneg_left hjhi hc.le
        have hm2 := mul_lt_mul_of_pos_right hkbig (by positivity : (0 : ℝ) < 2 * γ)
        nlinarith
      · apply (div_le_iff₀ hjpos).mpr
        have hk : (k : ℝ) ≤ (n : ℝ) := by
          dsimp [k]
          have hk' : n - 1 - ∑ i, z i ≤ n - 1 := Nat.sub_le _ _
          have hkn : n - 1 ≤ n := Nat.sub_le _ _
          exact_mod_cast hk'.trans hkn
        change (k : ℝ) ≤ (2 / γ) * (j : ℝ)
        rw [div_mul_eq_mul_div, le_div_iff₀ hγ]
        nlinarith
  intro τ hτ
  let δ := τ / 2
  have hδ : 0 < δ := by positivity
  have hgood := endpointResidualSet_eventually_good μ hm hpos hL hsv hlocal hh hη δ hδ
  let C := ((c / (2 * γ)) ^ 2)⁻¹ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hbad : ∀ᶠ n : ℕ in atTop,
      (Measure.pi fun _ : Fin (n - 1) => μ).real (endpointResidualSet μ h n)ᶜ < δ / C := by
    have hc0 : Tendsto (fun n : ℕ => (Measure.pi fun _ : Fin (n - 1) => μ).real
        (endpointResidualSet μ h n)ᶜ) atTop (𝓝 0) := by
      have hlim := (tendsto_const_nhds (x := (1 : ℝ))).sub hG
      have hl0 : Tendsto (fun n : ℕ => 1 -
          (Measure.pi fun _ : Fin (n - 1) => μ).real (endpointResidualSet μ h n)) atTop (𝓝 0) := by
        simpa using hlim
      apply hl0.congr'
      filter_upwards [] with n
      have hp := measureReal_add_measureReal_compl
        (μ := Measure.pi fun _ : Fin (n - 1) => μ)
        (Set.to_countable (endpointResidualSet μ h n)).measurableSet
      have hu : (Measure.pi fun _ : Fin (n - 1) => μ).real Set.univ = 1 := by simp
      rw [hu] at hp
      linarith
    exact hc0.eventually (gt_mem_nhds (div_pos hδ hC))
  filter_upwards [hgood, hcomp, hbad, hjpos0, eventually_ge_atTop (2 : ℕ)] with n hg hc' hb hq hn
  cases n with
  | zero => omega
  | succ m =>
    simp only [Nat.add_sub_cancel] at hg hc' hb hq ⊢
    let G : Set (Fin m → ℕ) := endpointResidualSet μ h (m + 1)
    let j := ⌊γ * (m + 1 : ℕ)⌋₊
    let w : (Fin m → ℕ) → ℝ≥0∞ := fun z => ∏ i, μ {z i}
    let A := ENNReal.ofReal (1 + δ)
    let B := ENNReal.ofReal C
    have hqR : 0 < (μ {j}).toReal := ENNReal.toReal_pos hq.ne' (by finiteness)
    have hle_of_ratio {k : ℕ} {D : ℝ} (hD : 0 ≤ D)
        (hkr : (μ {k}).toReal / (μ {j}).toReal < D) : μ {k} ≤ ENNReal.ofReal D * μ {j} := by
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hD]
      calc
        (μ {k}).toReal = ((μ {k}).toReal / (μ {j}).toReal) * (μ {j}).toReal :=
          (div_mul_cancel₀ _ hqR.ne').symm
        _ ≤ D * (μ {j}).toReal := mul_le_mul_of_nonneg_right hkr.le ENNReal.toReal_nonneg
    have hpoint (z : Fin m → ℕ) :
        (if c * (m + 1 : ℕ) < ((m - ∑ i, z i : ℕ) : ℝ) then
          μ {m - ∑ i, z i} else 0) * w z ≤
          A * μ {j} * w z + B * μ {j} * (if z ∈ G then 0 else w z) := by
      dsimp [w]
      by_cases hz : z ∈ G
      · simp only [hz, ↓reduceIte]
        by_cases hbig : c * (m + 1 : ℕ) < ((m - ∑ i, z i : ℕ) : ℝ)
        · simp only [hbig, ↓reduceIte]
          obtain ⟨hsum, hmax, hr⟩ := hg z hz
          have hmass : μ {m - ∑ i, z i} ≤ A * μ {j} := by
            apply hle_of_ratio (by positivity)
            have hra := (abs_lt.mp hr).2
            dsimp [j] at *
            linarith
          simpa only [w, mul_comm, zero_mul, add_zero] using mul_le_mul_right hmass (w z)
        · simp only [hbig, ↓reduceIte, zero_mul]
          positivity
      · simp only [hz, ↓reduceIte]
        by_cases hbig : c * (m + 1 : ℕ) < ((m - ∑ i, z i : ℕ) : ℝ)
        · simp only [hbig, ↓reduceIte]
          have hmass : μ {m - ∑ i, z i} ≤ B * μ {j} := by
            apply hle_of_ratio hC.le
            have hr := hc' z hz hbig
            dsimp [C, j] at *
            exact hr
          simpa only [mul_comm, add_zero] using
            ((mul_le_mul_right hmass (w z)).trans (le_add_of_nonneg_left (by positivity)))
        · simp only [hbig, ↓reduceIte, zero_mul]
          positivity
    have hbad_weight : (∑' z : Fin m → ℕ, if z ∈ G then 0 else w z) =
        (Measure.pi fun _ : Fin m => μ) Gᶜ := by
      rw [BGW.pi_eq_tsum_indicator]
      apply tsum_congr
      intro z
      dsimp [w]
      by_cases hz : z ∈ G <;> simp [Set.indicator, hz]
    have huniv_weight : (∑' z : Fin m → ℕ, w z) = 1 := by
      dsimp [w]
      calc
        _ = (Measure.pi fun _ : Fin m => μ) Set.univ := by
          rw [BGW.pi_eq_tsum_indicator]
          simp
        _ = 1 := measure_univ
    have hsum : (∑' z : Fin m → ℕ,
        (if c * (m + 1 : ℕ) < ((m - ∑ i, z i : ℕ) : ℝ) then
          μ {m - ∑ i, z i} else 0) * w z) ≤
        A * μ {j} + B * μ {j} * (Measure.pi fun _ : Fin m => μ) Gᶜ := by
      calc
        _ ≤ ∑' z : Fin m → ℕ,
            (A * μ {j} * w z + B * μ {j} * (if z ∈ G then 0 else w z)) :=
          ENNReal.tsum_le_tsum hpoint
        _ = (∑' z, A * μ {j} * w z) + ∑' z, B * μ {j} * (if z ∈ G then 0 else w z) :=
          ENNReal.tsum_add
        _ = A * μ {j} * (∑' z, w z) + B * μ {j} * (∑' z, if z ∈ G then 0 else w z) := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
        _ = _ := by rw [hbad_weight, huniv_weight, mul_one]
    have hbigμ := endpoint_bigJump_union_bound μ (m := m) (c := c) hc.le
    have hscaled : ((m + 1 : ℕ) : ℝ≥0∞) * (∑' z : Fin m → ℕ,
        (if c * (m + 1 : ℕ) < ((m - ∑ i, z i : ℕ) : ℝ) then
          μ {m - ∑ i, z i} else 0) * w z) ≤
        ((m + 1 : ℕ) : ℝ≥0∞) * (A * μ {j} + B * μ {j} *
          (Measure.pi fun _ : Fin m => μ) Gᶜ) := mul_le_mul_right hsum _
    have hbigμ' := hbigμ.trans hscaled
    have hR := (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mpr hbigμ'
    have hcast : ((m : ℝ≥0∞) + 1).toReal = (m : ℝ) + 1 := by
      rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_natCast,
        ENNReal.toReal_one]
    dsimp [j] at hR
    simp only [Nat.cast_add, Nat.cast_one] at hR
    simp only [ENNReal.toReal_mul] at hR
    rw [hcast] at hR
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at hR
    push_cast at hR ⊢
    dsimp [A, B] at hR
    have hbadC : C * (Measure.pi fun _ : Fin m => μ).real Gᶜ < δ := by
      have hh := mul_lt_mul_of_pos_left hb hC
      change C * (Measure.pi fun _ : Fin m => μ).real Gᶜ < C * (δ / C) at hh
      simpa only [mul_div_cancel₀ δ hC.ne'] using hh
    let Q : ℝ := (μ {j}).toReal
    have hQ : 0 ≤ Q := ENNReal.toReal_nonneg
    have hRQ : ((Measure.pi fun _ : Fin (m + 1) => μ)
        {ω | ∑ i, ω i = m ∧ ∃ i, c * ((m : ℝ) + 1) < (ω i : ℝ)}).toReal ≤
        ((m : ℝ) + 1) * ((1 + δ) * Q + C * Q *
          (Measure.pi fun _ : Fin m => μ).real Gᶜ) := by
      dsimp [Q]
      simpa only [Nat.cast_add, Nat.cast_one, mul_add, mul_assoc, j, Measure.real,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 + δ),
        ENNReal.toReal_ofReal hC.le] using hR
    have hscaledBad := mul_le_mul_of_nonneg_left hbadC.le hQ
    have hscaledBad' : C * Q * (Measure.pi fun _ : Fin m => μ).real Gᶜ ≤ δ * Q := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hscaledBad
    have hfinal : ((Measure.pi fun _ : Fin (m + 1) => μ)
        {ω | ∑ i, ω i = m ∧ ∃ i, c * ((m : ℝ) + 1) < (ω i : ℝ)}).toReal ≤
        (1 + τ) * ((m : ℝ) + 1) * Q := by
      apply hRQ.trans
      calc
        ((m : ℝ) + 1) * ((1 + δ) * Q + C * Q *
            (Measure.pi fun _ : Fin m => μ).real Gᶜ) ≤
            ((m : ℝ) + 1) * ((1 + δ) * Q + δ * Q) :=
          mul_le_mul_of_nonneg_left (add_le_add_right hscaledBad' _) (by positivity)
        _ = (1 + τ) * ((m : ℝ) + 1) * Q := by dsimp [δ]; ring
    simpa only [Q, j, γ, Nat.cast_add, Nat.cast_one] using hfinal

end SubcriticalCauchy.Bienayme
