module

public import SubcriticalCauchy.SlowVariationBoundary
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Power comparisons for measurable slowly varying functions

The compact-factor theorem is applied to the original pointwise function.
No monotonicity or replacement by a measurable representative is used.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace SubcriticalCauchy.Bienayme

/-- Finite mean forces the slowly varying local model to vanish. -/
theorem localModel_tendsto_zero
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ < 1)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => L n) atTop (𝓝 0) := by
  have hsum := summable_localModel_over_nat μ (ne_top_of_lt hm) hpos hlocal
  have hratio := localModel_div_ellStar_tendsto_zero hpos hL hsv hsum
  have hprod := hratio.mul (ellStar_tendsto_zero L)
  simp only [mul_zero] at hprod
  apply hprod.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  exact div_mul_cancel₀ _ (ellStar_pos hpos hsum hn).ne'

/-- Iteration of a two-sided comparison on factors in `[1,2]`. -/
theorem dyadic_comparison {L : ℝ → ℝ} {N q : ℝ}
    (hN : 0 < N) (hq : 0 < q)
    (hstep : ∀ x c : ℝ, N ≤ x → c ∈ Set.Icc 1 2 →
      L (c * x) ≤ q * L x ∧ L x ≤ q * L (c * x))
    {u : ℝ} (hu : N ≤ u) (n : ℕ) :
    L (2 ^ n * u) ≤ q ^ n * L u ∧ L u ≤ q ^ n * L (2 ^ n * u) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hbase : N ≤ (2 : ℝ) ^ n * u := by
      exact hu.trans (le_mul_of_one_le_left (hN.le.trans hu)
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))
    have hs := hstep (2 ^ n * u) 2 hbase (by norm_num)
    have heq : (2 : ℝ) ^ (n + 1) * u = 2 * (2 ^ n * u) := by ring
    rw [heq]
    constructor
    · calc
        L (2 * (2 ^ n * u)) ≤ q * L (2 ^ n * u) := hs.1
        _ ≤ q * (q ^ n * L u) := mul_le_mul_of_nonneg_left ih.1 hq.le
        _ = q ^ (n + 1) * L u := by ring
    · calc
        L u ≤ q ^ n * L (2 ^ n * u) := ih.2
        _ ≤ q ^ n * (q * L (2 * (2 ^ n * u))) :=
          mul_le_mul_of_nonneg_left hs.2 (pow_nonneg hq.le _)
        _ = q ^ (n + 1) * L (2 * (2 ^ n * u)) := by ring

/-- Potter's two-sided bound, with arbitrary positive exponent. -/
theorem potter_bounds {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0))) (hsv : IsSlowlyVaryingAtTop L)
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℝ, 0 < N ∧ ∀ u v : ℝ, N ≤ u → u ≤ v →
      C⁻¹ * (v / u) ^ (-η) ≤ L v / L u ∧ L v / L u ≤ C * (v / u) ^ η := by
  let q : ℝ := 2 ^ η
  have hq1 : 1 < q := Real.one_lt_rpow (by norm_num) hη
  have hq : 0 < q := zero_lt_one.trans hq1
  let τ : ℝ := min (q - 1) (1 - q⁻¹)
  have hτ : 0 < τ := lt_min (sub_pos.mpr hq1)
    (sub_pos.mpr ((inv_lt_one₀ hq).mpr hq1))
  obtain ⟨N, hUC, hN⟩ := ((slowlyVarying_uniform_compact_tail hpos hL hsv
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) ≤ 2)
    (tendsto_natCast_atTop_atTop (R := ℝ)) τ hτ).and
    (eventually_ge_atTop (1 : ℕ))).exists
  have hNR : 0 < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hstep : ∀ x c : ℝ, (N : ℝ) ≤ x → c ∈ Set.Icc 1 2 →
      L (c * x) ≤ q * L x ∧ L x ≤ q * L (c * x) := by
    intro x c hx hc
    have hxpos := hNR.trans_le hx
    have hval := abs_lt.mp (hUC x c hx hc)
    have hlo : q⁻¹ ≤ L (c * x) / L x := by
      have := min_le_right (q - 1) (1 - q⁻¹)
      dsimp [τ] at hval
      linarith
    have hhi : L (c * x) / L x ≤ q := by
      have := min_le_left (q - 1) (1 - q⁻¹)
      dsimp [τ] at hval
      linarith
    refine ⟨(div_le_iff₀ (hpos x hxpos)).mp hhi, ?_⟩
    have hh := mul_le_mul_of_nonneg_left ((le_div_iff₀ (hpos x hxpos)).mp hlo) hq.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul] using hh
  refine ⟨q, hq, N, hNR, ?_⟩
  intro u v hu huv
  have hu0 := hNR.trans_le hu
  have hv0 := hu0.trans_le huv
  have hr : 1 ≤ v / u := (one_le_div₀ hu0).mpr huv
  obtain ⟨n, hnlo, hnhi⟩ := exists_nat_pow_near hr (by norm_num : (1 : ℝ) < 2)
  have hb : (N : ℝ) ≤ 2 ^ n * u := hu.trans
    (le_mul_of_one_le_left hu0.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))
  have hb0 : 0 < (2 : ℝ) ^ n * u := mul_pos (by positivity) hu0
  have hc : v / (2 ^ n * u) ∈ Set.Icc (1 : ℝ) 2 := by
    constructor
    · exact (one_le_div₀ hb0).mpr ((le_div_iff₀ hu0).mp hnlo)
    · apply (div_le_iff₀ hb0).mpr
      have ht := (div_lt_iff₀ hu0).mp hnhi
      nlinarith [show (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n by ring]
  have hs := hstep (2 ^ n * u) (v / (2 ^ n * u)) hb hc
  rw [div_mul_cancel₀ _ hb0.ne'] at hs
  have hd := dyadic_comparison hNR hq hstep hu n
  have hforward : L v ≤ q ^ (n + 1) * L u := by
    calc
      L v ≤ q * L (2 ^ n * u) := hs.1
      _ ≤ q * (q ^ n * L u) := mul_le_mul_of_nonneg_left hd.1 hq.le
      _ = q ^ (n + 1) * L u := by ring
  have hback : L u ≤ q ^ (n + 1) * L v := by
    calc
      L u ≤ q ^ n * L (2 ^ n * u) := hd.2
      _ ≤ q ^ n * (q * L v) := mul_le_mul_of_nonneg_left hs.2 (pow_nonneg hq.le _)
      _ = q ^ (n + 1) * L v := by ring
  have hpower : q ^ (n + 1) ≤ q * (v / u) ^ η := by
    have hh := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 2 ^ n) hnlo hη.le
    rw [← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2)] at hh
    calc
      q ^ (n + 1) = q * q ^ n := by ring
      _ ≤ q * (v / u) ^ η := mul_le_mul_of_nonneg_left hh hq.le
  have hupper : L v / L u ≤ q * (v / u) ^ η :=
    (div_le_iff₀ (hpos u hu0)).mpr
      (hforward.trans (mul_le_mul_of_nonneg_right hpower (hpos u hu0).le))
  have hreverse : L u / L v ≤ q * (v / u) ^ η :=
    (div_le_iff₀ (hpos v hv0)).mpr
      (hback.trans (mul_le_mul_of_nonneg_right hpower (hpos v hv0).le))
  refine ⟨?_, hupper⟩
  have hh := (inv_le_inv₀ (mul_pos hq (Real.rpow_pos_of_pos (div_pos hv0 hu0) _))
    (div_pos (hpos u hu0) (hpos v hv0))).mpr hreverse
  simpa only [mul_inv, inv_div, Real.rpow_neg (le_trans zero_le_one hr)] using hh

/-- A convenient square-root form of the lower Potter bound. -/
theorem sqrt_potter_comparison {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℝ, 0 < N ∧ ∀ u v : ℝ, N ≤ u → u ≤ v →
      L u * Real.sqrt u ≤ C * (L v * Real.sqrt v) := by
  obtain ⟨C, hC, N, hN, h⟩ := potter_bounds hpos hL hsv (1 / 2) (by norm_num)
  refine ⟨C, hC, N, hN, ?_⟩
  intro u v hu huv
  have hu0 := hN.trans_le hu
  have hv0 := hu0.trans_le huv
  have hp : (v / u) ^ (-(1 / 2 : ℝ)) = Real.sqrt u / Real.sqrt v := by
    rw [Real.rpow_neg (div_pos hv0 hu0).le, ← Real.sqrt_eq_rpow,
      Real.sqrt_div hv0.le, inv_div]
  have hh := (h u v hu huv).1
  rw [hp] at hh
  have heq : C⁻¹ * (Real.sqrt u / Real.sqrt v) =
      Real.sqrt u / (C * Real.sqrt v) := by ring
  rw [heq] at hh
  have hm := (div_le_div_iff₀ (mul_pos hC (Real.sqrt_pos.mpr hv0)) (hpos u hu0)).mp hh
  nlinarith

/-- The elementary square-root sum estimate used for the truncated moment.
The zero-index summand is zero. -/
theorem sum_inv_sqrt_le (y : ℕ) :
    ∑ k ∈ Finset.range (y + 1), (Real.sqrt (k : ℝ))⁻¹ ≤ 2 * Real.sqrt y := by
  induction y with
  | zero => simp
  | succ y ih =>
    rw [Finset.sum_range_succ]
    have ha : 0 ≤ Real.sqrt (y : ℝ) := Real.sqrt_nonneg _
    have hb : 0 < Real.sqrt ((y + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
    have ha2 := Real.sq_sqrt (show (0 : ℝ) ≤ y by positivity)
    have hb2 := Real.sq_sqrt (show (0 : ℝ) ≤ ((y + 1 : ℕ) : ℝ) by positivity)
    have hdiff : (Real.sqrt ((y + 1 : ℕ) : ℝ))⁻¹ ≤
        2 * (Real.sqrt ((y + 1 : ℕ) : ℝ) - Real.sqrt (y : ℝ)) := by
      rw [inv_eq_one_div, div_le_iff₀ hb]
      have hcast : ((y + 1 : ℕ) : ℝ) = (y : ℝ) + 1 := by simp
      nlinarith [sq_nonneg (Real.sqrt ((y + 1 : ℕ) : ℝ) - Real.sqrt (y : ℝ))]
    exact (add_le_add ih hdiff).trans (by push_cast; ring_nf; rfl)

/-- The second moment below `y` is bounded by a constant times `y L(y)`. -/
-- Subcriticality is retained in the requested interface; the bound itself
-- follows already from the local asymptotic and measurable slow variation.
theorem truncated_second_moment_le
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (_hm : offspringMean μ < 1)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1)) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ y : ℕ, N ≤ y →
      ∑ k ∈ Finset.range (y + 1), (k : ℝ) ^ 2 * (μ {k}).toReal ≤ C * y * L y := by
  obtain ⟨C, hC, N, _hN, hcompare⟩ := sqrt_potter_comparison hpos hL hsv
  obtain ⟨M, hM⟩ := exists_nat_ge N
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (hlocal.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 2)))
  let T := max M (max K 1)
  have hTM : M ≤ T := le_max_left _ _
  have hTK : K ≤ T := (le_max_left K 1).trans (le_max_right M _)
  have hT1 : 1 ≤ T := (le_max_right K 1).trans (le_max_right M _)
  have hT : N ≤ (T : ℝ) := hM.trans (Nat.cast_le.mpr hTM)
  have hT0 : 0 < (T : ℝ) := Nat.cast_pos.mpr (by omega)
  let B := ∑ k ∈ Finset.range T, (k : ℝ) ^ 2 * (μ {k}).toReal
  have hB : 0 ≤ B := Finset.sum_nonneg (fun k _ => by positivity)
  let d := L T * Real.sqrt T / C
  have hd : 0 < d := div_pos (mul_pos (hpos _ hT0) (Real.sqrt_pos.mpr hT0)) hC
  refine ⟨B / d + 4 * C, T, ?_⟩
  intro y hy
  have hy0 : 0 < (y : ℝ) := hT0.trans_le (Nat.cast_le.mpr hy)
  have hLy : 0 < L y := hpos _ hy0
  have hsy : 0 ≤ Real.sqrt (y : ℝ) := Real.sqrt_nonneg _
  have hdle : d ≤ L y * Real.sqrt y :=
    (div_le_iff₀ hC).mpr (by simpa [mul_comm] using hcompare T y hT (Nat.cast_le.mpr hy))
  have hsyle : Real.sqrt (y : ℝ) ≤ y := Real.sqrt_le_self_iff.mpr
    (Or.inr (by exact_mod_cast hT1.trans hy))
  have hdyle : d ≤ (y : ℝ) * L y :=
    hdle.trans (by nlinarith)
  have hprefix : B ≤ (B / d) * ((y : ℝ) * L y) := by
    calc
      B = (B / d) * d := (div_mul_cancel₀ B hd.ne').symm
      _ ≤ (B / d) * ((y : ℝ) * L y) :=
        mul_le_mul_of_nonneg_left hdyle (div_nonneg hB hd.le)
  have hterm (k : ℕ) (hk : k ∈ Finset.Ico T (y + 1)) :
      (k : ℝ) ^ 2 * (μ {k}).toReal ≤
        (2 * C * (L y * Real.sqrt y)) * (Real.sqrt (k : ℝ))⁻¹ := by
    have hkT := (Finset.mem_Ico.mp hk).1
    have hky : k ≤ y := by have := (Finset.mem_Ico.mp hk).2; omega
    have hk0 : 0 < (k : ℝ) := hT0.trans_le (Nat.cast_le.mpr hkT)
    have hsk : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hk0
    have hmass : (k : ℝ) ^ 2 * (μ {k}).toReal ≤ 2 * L k := by
      have hh := (div_lt_iff₀ (div_pos (hpos _ hk0) (sq_pos_of_pos hk0))).mp
        (hK k (hTK.trans hkT))
      calc
        (k : ℝ) ^ 2 * (μ {k}).toReal ≤ (k : ℝ) ^ 2 * (2 * (L k / (k : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hh.le (sq_nonneg _)
        _ = 2 * L k := by field_simp
    have hcomp : L k ≤ C * (L y * Real.sqrt y) / Real.sqrt k :=
      (le_div_iff₀ hsk).mpr
        (hcompare k y (hT.trans (Nat.cast_le.mpr hkT)) (Nat.cast_le.mpr hky))
    calc
      (k : ℝ) ^ 2 * (μ {k}).toReal ≤ 2 * L k := hmass
      _ ≤ 2 * (C * (L y * Real.sqrt y) / Real.sqrt k) :=
        mul_le_mul_of_nonneg_left hcomp (by norm_num)
      _ = (2 * C * (L y * Real.sqrt y)) * (Real.sqrt (k : ℝ))⁻¹ := by ring
  have hsum : ∑ k ∈ Finset.Ico T (y + 1), (Real.sqrt (k : ℝ))⁻¹ ≤
      2 * Real.sqrt y := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (sum_inv_sqrt_le y)
    · intro k hk
      exact Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
    · intro k _ _; positivity
  have htail : ∑ k ∈ Finset.Ico T (y + 1), (k : ℝ) ^ 2 * (μ {k}).toReal ≤
      4 * C * (y : ℝ) * L y := by
    calc
      _ ≤ ∑ k ∈ Finset.Ico T (y + 1),
          (2 * C * (L y * Real.sqrt y)) * (Real.sqrt (k : ℝ))⁻¹ := Finset.sum_le_sum hterm
      _ = (2 * C * (L y * Real.sqrt y)) *
          ∑ k ∈ Finset.Ico T (y + 1), (Real.sqrt (k : ℝ))⁻¹ := by rw [Finset.mul_sum]
      _ ≤ (2 * C * (L y * Real.sqrt y)) * (2 * Real.sqrt y) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 4 * C * L y * (Real.sqrt (y : ℝ)) ^ 2 := by ring
      _ = 4 * C * (y : ℝ) * L y := by rw [Real.sq_sqrt hy0.le]; ring
  rw [← Finset.sum_range_add_sum_Ico _ (hy.trans (Nat.le_succ y))]
  change B + _ ≤ _
  nlinarith

end SubcriticalCauchy.Bienayme
