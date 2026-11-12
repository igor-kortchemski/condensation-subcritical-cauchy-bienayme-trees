module

public import SubcriticalCauchy.EquivalentTails
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Auxiliary integral-comparison estimates for Example 2.3
-/


@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace SubcriticalCauchy.Bienayme

/-- A nonnegative eventually antitone function with derivative `-f` equal to
an infinitesimal primitive has a summable sequence of integer values. -/
theorem summable_nat_of_antitone_primitive {f F : ℝ → ℝ} {N : ℕ}
    (hF : Tendsto F atTop (𝓝 0))
    (hanti : AntitoneOn f (Set.Ici (N : ℝ)))
    (hderiv : ∀ x ∈ Set.Ici (N : ℝ), HasDerivAt F (-f x) x)
    (hnonneg : ∀ x ∈ Set.Ici (N : ℝ), 0 ≤ f x) :
    Summable (fun n : ℕ => f n) := by
  apply hanti.summable_of_integrableOn_Ioi _ (fun x hx => hnonneg x hx.le)
  let b : ℕ → ℝ := fun i => (N : ℝ) + i
  have hb : Tendsto b atTop atTop :=
    by simpa only [b, add_comm] using
      (tendsto_atTop_add_const_right atTop (N : ℝ) (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hfi (i : ℕ) : IntegrableOn f (Set.Ioc (N : ℝ) (b i)) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by simp [b])]
    apply (hanti.mono ?_).intervalIntegrable
    rw [Set.uIcc_of_le (by simp [b])]
    exact Set.Icc_subset_Ici_self
  apply integrableOn_Ioi_of_intervalIntegral_norm_tendsto (F N) (N : ℝ) hfi hb
  have heq (i : ℕ) : ∫ x in (N : ℝ)..b i, ‖f x‖ = F N - F (b i) := by
    have hnorm : ∀ x ∈ Set.uIcc (N : ℝ) (b i), ‖f x‖ = f x := by
      intro x hx
      rw [Set.uIcc_of_le (by simp [b])] at hx
      exact Real.norm_of_nonneg (hnonneg x hx.1)
    rw [intervalIntegral.integral_congr hnorm]
    have hint : IntervalIntegrable f volume (N : ℝ) (b i) := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by simp [b])]
      exact hfi i
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hderiv x (by
        rw [Set.uIcc_of_le (by simp [b])] at hx
        exact hx.1)) hint.neg
    rw [intervalIntegral.integral_neg] at h
    linarith
  have hlim : Tendsto (fun i => F (N : ℝ) - F (b i)) atTop (𝓝 (F (N : ℝ))) := by
    simpa using (tendsto_const_nhds (x := F (N : ℝ))).sub (hF.comp hb)
  apply hlim.congr'
  filter_upwards with i
  exact (heq i).symm

/-- Integral comparison for an eventually antitone sequence with an explicit
primitive. The error is at most one boundary term. -/
theorem tailMass_div_tendsto_one_of_primitive {f F : ℝ → ℝ}
    (hF : Tendsto F atTop (𝓝 0))
    (hsmall : Tendsto (fun n : ℕ => f n / F n) atTop (𝓝 0))
    (hFpos : ∀ᶠ n : ℕ in atTop, 0 < F n)
    (hlarge : ∀ᶠ n : ℕ in atTop,
      AntitoneOn f (Set.Ici (n : ℝ)) ∧
      (∀ x ∈ Set.Ici (n : ℝ), HasDerivAt F (-f x) x) ∧
      (∀ x ∈ Set.Ioi (n : ℝ), 0 ≤ f x)) :
    Tendsto (fun n : ℕ => tailMass (fun k : ℕ => f k) n / F n) atTop (𝓝 1) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hlarge
  have hsum : Summable (fun n : ℕ => f n) := by
    obtain ⟨hanti, hderiv, hnonneg⟩ := hN N le_rfl
    apply summable_nat_of_antitone_primitive hF hanti hderiv
    intro x hx
    rcases hx.eq_or_lt with rfl | hx
    · have hm := hanti (Set.mem_Ici.mpr le_rfl) (show (N : ℝ) + 1 ∈ Set.Ici (N : ℝ) by simp)
        (by linarith : (N : ℝ) ≤ (N : ℝ) + 1)
      exact (hnonneg ((N : ℝ) + 1) (by simp)).trans hm
    · exact hnonneg x hx
  have hupper : Tendsto (fun n : ℕ => 1 + f n / F n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hsmall
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards [hlarge, hFpos] with n hn hFn
    obtain ⟨hanti, hderiv, hnonneg⟩ := hn
    have hshift : Summable (fun j : ℕ => f (j + n : ℕ)) := by
      simpa only [Nat.add_comm] using (summable_nat_add_iff n).mpr hsum
    have hint : IntegrableOn f (Set.Ioi (n : ℝ)) :=
      hanti.integrableOn_Ioi_of_summable_comp_add hshift hnonneg
    have hInt : ∫ x in Set.Ioi (n : ℝ), f x = F n := by
      have hneg := integral_Ioi_of_hasDerivAt_of_tendsto'
        (fun x hx => hderiv x hx) hint.neg hF
      rw [integral_neg] at hneg
      linarith
    have hlower := AntitoneOn.integral_le_tsum_comp_add n hanti hsum hnonneg
    rw [hInt] at hlower
    apply (le_div_iff₀ hFn).mpr
    simpa only [tailMass, Nat.add_comm, one_mul] using hlower
  · filter_upwards [hlarge, hFpos] with n hn hFn
    obtain ⟨hanti, hderiv, hnonneg⟩ := hn
    have hshift : Summable (fun j : ℕ => f (j + n : ℕ)) := by
      simpa only [Nat.add_comm] using (summable_nat_add_iff n).mpr hsum
    have hint : IntegrableOn f (Set.Ioi (n : ℝ)) :=
      hanti.integrableOn_Ioi_of_summable_comp_add hshift hnonneg
    have hInt : ∫ x in Set.Ioi (n : ℝ), f x = F n := by
      have hneg := integral_Ioi_of_hasDerivAt_of_tendsto'
        (fun x hx => hderiv x hx) hint.neg hF
      rw [integral_neg] at hneg
      linarith
    have hup := AntitoneOn.tsum_comp_add_le_integral n hanti hint hnonneg
    rw [hInt] at hup
    have hsplit : tailMass (fun k : ℕ => f k) n =
        f n + ∑' j : ℕ, f (j + n + 1 : ℕ) := by
      rw [tailMass]
      have hs := (summable_nat_add_iff n).mpr hsum
      have hs' : Summable (fun j : ℕ => f (n + j : ℕ)) := by
        simpa only [Nat.add_comm] using hs
      convert hs'.tsum_eq_zero_add using 1
      simp only [Nat.add_zero]
      congr 1
      apply tsum_congr
      intro j
      congr 2
      ring
    apply (div_le_iff₀ hFn).mpr
    rw [hsplit]
    rw [add_mul, one_mul, div_mul_cancel₀ _ hFn.ne']
    nlinarith

end SubcriticalCauchy.Bienayme
