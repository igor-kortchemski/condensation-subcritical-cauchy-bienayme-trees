module

public import SubcriticalCauchy.SlowVariationTail
public import SubcriticalCauchy.CompactSlowVariation

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The boundary comparison for the integrated slowly varying tail

Compact-factor uniform convergence makes every fixed dyadic block contribute
a positive multiple of `L n` to the integrated tail. The number of blocks can
be made arbitrarily large before taking the limit. No monotonicity of `L`, or
of `L k / k`, is assumed.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy

/-- A block of length `d` contributes at least `L n / 4` when `L` is bounded
below by `L n / 2` throughout that block. -/
theorem localModel_block_lower_bound {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    {n d : ℕ} (hn : 1 ≤ n) (hnd : n ≤ d)
    (hbound : ∀ k : ℕ, d ≤ k → k ≤ d + d → L n / 2 ≤ L k) :
    L n / 4 ≤ ∑ j ∈ Finset.range d, L (d + j) / ((d + j : ℕ) : ℝ) := by
  have hdNat : 0 < d := lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_one hn) hnd
  have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hdNat
  have hterm (j : ℕ) (hj : j ∈ Finset.range d) :
      (L n / 2) / (2 * (d : ℝ)) ≤ L (d + j) / ((d + j : ℕ) : ℝ) := by
    have hklo : d ≤ d + j := Nat.le_add_right _ _
    have hkhi : d + j ≤ d + d := Nat.add_le_add_left (Finset.mem_range.mp hj).le d
    have hkpos : 0 < ((d + j : ℕ) : ℝ) :=
      Nat.cast_pos.mpr (hdNat.trans_le hklo)
    have hkhiR : ((d + j : ℕ) : ℝ) ≤ (d : ℝ) + (d : ℝ) := by
      exact_mod_cast hkhi
    exact div_le_div₀
      (by simpa only [Nat.cast_add] using (hpos _ hkpos).le)
      (by simpa only [Nat.cast_add] using hbound _ hklo hkhi) hkpos (by linarith)
  calc
    L n / 4 = ∑ _j ∈ Finset.range d, (L n / 2) / (2 * (d : ℝ)) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp [hdR.ne']
      ring
    _ ≤ ∑ j ∈ Finset.range d, L (d + j) / ((d + j : ℕ) : ℝ) :=
      Finset.sum_le_sum hterm

/-- The first `K` dyadic blocks lower-bound the integrated tail without any
monotonicity requirement on its summands. -/
theorem ellStar_dyadic_lower_bound {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hsum : Summable (fun k : ℕ => L k / (k : ℝ)))
    {n K : ℕ} (hn : 1 ≤ n)
    (hbound : ∀ k : ℕ, n ≤ k → k ≤ 2 ^ K * n → L n / 2 ≤ L k) :
    (K : ℝ) * L n / 4 ≤ ellStar L n := by
  have hstep (j : ℕ) (hj : j < K) :
      L n / 4 + ellStar L (2 ^ (j + 1) * n) ≤ ellStar L (2 ^ j * n) := by
    let d := 2 ^ j * n
    have hnd : n ≤ d := by
      dsimp [d]
      simpa only [one_mul] using
        Nat.mul_le_mul_right n (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2) : 1 ≤ 2 ^ j)
    have hdd : d + d = 2 ^ (j + 1) * n := by
      dsimp [d]
      rw [pow_succ]
      ring
    have hmax : d + d ≤ 2 ^ K * n := by
      rw [hdd]
      exact Nat.mul_le_mul_right n
        (pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (Nat.succ_le_of_lt hj))
    have hblock := localModel_block_lower_bound hpos hn hnd
      (fun k hklo hkhi => hbound k (hnd.trans hklo) (hkhi.trans hmax))
    have hsplit : ellStar L d =
        (∑ k ∈ Finset.range d, L (d + k) / ((d + k : ℕ) : ℝ)) +
          ellStar L (d + d) := by
      simpa only [ellStar, Nat.cast_add] using
        tailMass_split hsum d d
    rw [hdd] at hsplit
    change L n / 4 + ellStar L (2 ^ (j + 1) * n) ≤ ellStar L d
    linarith
  have hind : ∀ j : ℕ, j ≤ K →
      (j : ℝ) * L n / 4 + ellStar L (2 ^ j * n) ≤ ellStar L n := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hp := ih (Nat.le_of_succ_le hj)
      have hs := hstep j (Nat.lt_of_succ_le hj)
      simp only [Nat.cast_succ]
      nlinarith
  have ht : 0 ≤ ellStar L (2 ^ K * n) :=
    tailMass_nonneg (localModel_over_nat_nonneg hpos) _
  have htotal := hind K le_rfl
  linarith

/-- Every fixed finite collection of dyadic blocks is eventually comparable
to `L n`, by compact-factor uniform convergence. -/
theorem eventually_ellStar_dyadic_lower_bound {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hfixed : ∀ a : ℝ, 0 < a →
      Tendsto (fun x : ℝ => L (a * x) / L x) atTop (𝓝 1))
    (hsum : Summable (fun k : ℕ => L k / (k : ℝ))) (K : ℕ) :
    ∀ᶠ n : ℕ in atTop, (K : ℝ) * L n / 4 ≤ ellStar L n := by
  have hUC := slowlyVarying_uniform_compact_window hpos hL hfixed
    (by norm_num : 0 < (1 : ℝ))
    (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : (1 : ℝ) ≤ 2 ^ K)
    (tendsto_natCast_atTop_atTop (R := ℝ)) (1 / 2) (by norm_num)
  filter_upwards [hUC, eventually_ge_atTop (1 : ℕ)] with n hn hnpos
  apply ellStar_dyadic_lower_bound hpos hsum hnpos
  intro k hnk hkhi
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hnpos)
  have hc : (k : ℝ) / (n : ℝ) ∈ Set.Icc 1 ((2 : ℝ) ^ K) := by
    constructor
    · exact (one_le_div₀ hnR).mpr (by exact_mod_cast hnk)
    · apply (div_le_iff₀ hnR).mpr
      exact_mod_cast hkhi
  have hr := hn ((k : ℝ) / (n : ℝ)) hc
  rw [div_mul_cancel₀ _ hnR.ne'] at hr
  have hratio : (1 / 2 : ℝ) ≤ L k / L n := by
    have hl := (abs_lt.mp hr).1
    linarith
  have hmul := (le_div_iff₀ (hpos _ hnR)).mp hratio
  linarith

/-- The integrated tail dominates its single-scale slowly varying factor. -/
theorem ellStar_div_localModel_tendsto_atTop {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hfixed : ∀ a : ℝ, 0 < a →
      Tendsto (fun x : ℝ => L (a * x) / L x) atTop (𝓝 1))
    (hsum : Summable (fun k : ℕ => L k / (k : ℝ))) :
    Tendsto (fun n : ℕ => ellStar L n / L n) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  obtain ⟨K, hK⟩ := exists_nat_gt (4 * b)
  have hb : b < (K : ℝ) / 4 := by linarith
  filter_upwards [eventually_ellStar_dyadic_lower_bound hpos hL hfixed hsum K,
    eventually_ge_atTop (1 : ℕ)] with n hn hnpos
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hnpos)
  apply hb.le.trans
  apply (le_div_iff₀ (hpos _ hnR)).mpr
  nlinarith

/-- The boundary assertion `L(n) = o(ellStar(n))` in Lemma 2.2(i), under the
standard measurable convention and genuine summability of the integrated tail. -/
theorem localModel_div_ellStar_tendsto_zero {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hfixed : ∀ a : ℝ, 0 < a →
      Tendsto (fun x : ℝ => L (a * x) / L x) atTop (𝓝 1))
    (hsum : Summable (fun k : ℕ => L k / (k : ℝ))) :
    Tendsto (fun n : ℕ => L n / ellStar L n) atTop (𝓝 0) := by
  simpa only [Function.comp_def, Pi.inv_apply, inv_div] using
    tendsto_inv_atTop_zero.comp (ellStar_div_localModel_tendsto_atTop hpos hL hfixed hsum)

namespace Bienayme

/-- The summability premise of the boundary estimate follows from the actual
offspring first moment and local mass asymptotic. -/
theorem localModel_div_ellStar_tendsto_zero_of_offspring
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ ≠ ∞)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hfixed : ∀ a : ℝ, 0 < a →
      Tendsto (fun x : ℝ => L (a * x) / L x) atTop (𝓝 1))
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => L n / ellStar L n) atTop (𝓝 0) :=
  localModel_div_ellStar_tendsto_zero hpos hL hfixed
    (summable_localModel_over_nat μ hm hpos hlocal)

end Bienayme
end SubcriticalCauchy
