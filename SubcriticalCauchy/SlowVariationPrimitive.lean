module

public import SubcriticalCauchy.SlowVariationTail
public import SubcriticalCauchy.CompactSlowVariation
public import SubcriticalCauchy.SlowVariationBoundary
public import Mathlib.MeasureTheory.Function.Floor

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
Integrated-tail slow variation. Nonnegative series tails are antitone
even when their individual summands are not. Compact uniform convergence bounds
finite slices, and the boundary ratio `L n / ellStar L n → 0` makes their mass
negligible. The `_of_small` theorems explicitly retain that boundary estimate;
source-hypothesis wrappers discharge it with SlowVariationBoundary.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace SubcriticalCauchy

/-- Nonnegative summable series have antitone tails, without monotonicity of
their summands. -/
theorem tailMass_antitone_of_nonneg {T : ℕ → ℝ} (hT : Summable T)
    (h0 : ∀ n, 0 ≤ T n) : Antitone (tailMass T) := by
  intro n m hnm
  have hm : n + (m - n) = m := by omega
  have hsplit := tailMass_split hT n (m - n)
  rw [hm] at hsplit
  have hsum : 0 ≤ ∑ j ∈ Finset.range (m - n), T (n + j) :=
    Finset.sum_nonneg (fun j _ => h0 (n + j))
  linarith

theorem ellStar_nonneg {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x) (n : ℕ) : 0 ≤ ellStar L n :=
  tailMass_nonneg (localModel_over_nat_nonneg hpos) n

theorem ellStar_antitone {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hsum : Summable (fun k : ℕ => L k / (k : ℝ))) : Antitone (ellStar L) :=
  tailMass_antitone_of_nonneg hsum (localModel_over_nat_nonneg hpos)

theorem ellStar_succ_mul_loss {L : ℝ → ℝ}
    (hsum : Summable (fun k : ℕ => L k / (k : ℝ))) (K n : ℕ) :
    ellStar L n - ellStar L ((K + 1) * n) =
      ∑ j ∈ Finset.range (K * n), L ((n + j : ℕ) : ℝ) / ((n + j : ℕ) : ℝ) := by
  have heq : (K + 1) * n = n + K * n := by ring
  unfold ellStar
  rw [heq, tailMass_split hsum n (K * n)]
  ring

/-- Compact-factor uniformity bounds the entire slice simultaneously. No
monotonicity of `L` or `L n / n` is assumed. -/
theorem ellStar_succ_mul_loss_eventually_le {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hfixed : ∀ a : ℝ, 0 < a →
      Tendsto (fun x : ℝ => L (a * x) / L x) atTop (𝓝 1))
    (hsum : Summable (fun k : ℕ => L k / (k : ℝ))) (K : ℕ) :
    ∀ᶠ n in atTop, ellStar L n - ellStar L ((K + 1) * n) ≤ 2 * (K : ℝ) * L n := by
  have hab : (1 : ℝ) ≤ ((K + 1 : ℕ) : ℝ) := by
    simp only [Nat.cast_add, Nat.cast_one]
    exact le_add_of_nonneg_left (Nat.cast_nonneg K)
  have hwin := slowlyVarying_uniform_compact_window hpos hL hfixed
    (a := (1 : ℝ)) (b := ((K + 1 : ℕ) : ℝ)) zero_lt_one hab
    (tendsto_natCast_atTop_atTop (R := ℝ)) 1 zero_lt_one
  filter_upwards [hwin, eventually_ge_atTop (1 : ℕ)] with n hnwin hn
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hLn : 0 < L (n : ℝ) := hpos _ hnR
  have hterm (j : ℕ) (hj : j ∈ Finset.range (K * n)) :
      L ((n + j : ℕ) : ℝ) / ((n + j : ℕ) : ℝ) ≤ 2 * L n / (n : ℝ) := by
    have hden : (n : ℝ) ≤ ((n + j : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_right n j
    have hjR : (j : ℝ) ≤ (K : ℝ) * (n : ℝ) := by
      exact_mod_cast (Finset.mem_range.mp hj).le
    have hc : (((n + j : ℕ) : ℝ) / (n : ℝ)) ∈
        Set.Icc (1 : ℝ) ((K + 1 : ℕ) : ℝ) := by
      constructor
      · apply (le_div_iff₀ hnR).mpr
        simpa only [one_mul] using hden
      · apply (div_le_iff₀ hnR).mpr
        simp only [Nat.cast_add, Nat.cast_one]
        nlinarith
    have hratio := hnwin (((n + j : ℕ) : ℝ) / (n : ℝ)) hc
    rw [div_mul_cancel₀ _ hnR.ne'] at hratio
    have hupper : L ((n + j : ℕ) : ℝ) ≤ 2 * L n := by
      have hlt : L ((n + j : ℕ) : ℝ) / L n < 2 := by
        have hh := (abs_lt.mp hratio).2
        linarith
      exact ((div_lt_iff₀ hLn).mp hlt).le
    calc
      _ ≤ (2 * L n) / ((n + j : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right hupper (hnR.le.trans hden)
      _ ≤ 2 * L n / (n : ℝ) :=
        div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hLn.le) hnR hden
  rw [ellStar_succ_mul_loss hsum K n]
  calc
    _ ≤ ∑ _j ∈ Finset.range (K * n), 2 * L n / (n : ℝ) :=
      Finset.sum_le_sum hterm
    _ = ((K * n : ℕ) : ℝ) * (2 * L n / (n : ℝ)) := by simp
    _ = 2 * (K : ℝ) * L n := by
      rw [Nat.cast_mul]
      field_simp [hnR.ne']

/-- Conditional analytic step: a vanishing local/primitive ratio makes each
fixed-multiple slice negligible. The source wrapper must supply `hsmall`. -/
theorem ellStar_succ_mul_div_tendsto_one_of_small {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hfixed : ∀ a : ℝ, 0 < a →
      Tendsto (fun x : ℝ => L (a * x) / L x) atTop (𝓝 1))
    (hsum : Summable (fun k : ℕ => L k / (k : ℝ)))
    (hsmall : Tendsto (fun n : ℕ => L n / ellStar L n) atTop (𝓝 0)) (K : ℕ) :
    Tendsto (fun n : ℕ => ellStar L ((K + 1) * n) / ellStar L n) atTop (𝓝 1) := by
  have hlim : Tendsto (fun n : ℕ => (2 * (K : ℝ)) * (L n / ellStar L n))
      atTop (𝓝 0) := by simpa only [mul_zero] using hsmall.const_mul (2 * (K : ℝ))
  have heq (n : ℕ) (hn : 1 ≤ n) :
      1 - ellStar L ((K + 1) * n) / ellStar L n =
        (ellStar L n - ellStar L ((K + 1) * n)) / ellStar L n := by
    rw [sub_div, div_self (ellStar_pos hpos hsum hn).ne']
  have hnonneg (n : ℕ) : 0 ≤ ellStar L n - ellStar L ((K + 1) * n) := by
    rw [ellStar_succ_mul_loss hsum K n]
    exact Finset.sum_nonneg (fun j _ => localModel_over_nat_nonneg hpos (n + j))
  have herr : Tendsto (fun n : ℕ => 1 - ellStar L ((K + 1) * n) / ellStar L n)
      atTop (𝓝 0) := by
    apply squeeze_zero' _ _ hlim
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      rw [heq n hn]
      exact div_nonneg (hnonneg n) (ellStar_nonneg hpos n)
    · filter_upwards [ellStar_succ_mul_loss_eventually_le hpos hL hfixed hsum K,
        eventually_ge_atTop (1 : ℕ)] with n hbound hn
      rw [heq n hn]
      calc
        _ ≤ (2 * (K : ℝ) * L n) / ellStar L n :=
          div_le_div_of_nonneg_right hbound (ellStar_nonneg hpos n)
        _ = (2 * (K : ℝ)) * (L n / ellStar L n) := by ring
  simpa only [sub_sub_cancel, sub_zero] using
    (tendsto_const_nhds (x := (1 : ℝ))).sub herr

theorem ellStar_mul_div_tendsto_one_of_small {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hfixed : ∀ a : ℝ, 0 < a →
      Tendsto (fun x : ℝ => L (a * x) / L x) atTop (𝓝 1))
    (hsum : Summable (fun k : ℕ => L k / (k : ℝ)))
    (hsmall : Tendsto (fun n : ℕ => L n / ellStar L n) atTop (𝓝 0))
    {K : ℕ} (hK : 1 ≤ K) :
    Tendsto (fun n : ℕ => ellStar L (K * n) / ellStar L n) atTop (𝓝 1) := by
  cases K with
  | zero => simp at hK
  | succ k => simpa only [Nat.succ_eq_add_one] using
      ellStar_succ_mul_div_tendsto_one_of_small hpos hL hfixed hsum hsmall k

/-- Pure squeeze helper. A positive antitone sequence with ratio one at integer
scales also has ratio one along arbitrary proportional index maps and filters. -/
theorem ratio_tendsto_one_of_integer_scales {A : ℕ → ℝ}
    (h0 : ∀ n, 0 ≤ A n) (hpos : ∀ n : ℕ, 1 ≤ n → 0 < A n)
    (hanti : Antitone A)
    (hscale : ∀ K : ℕ, 1 ≤ K →
      Tendsto (fun n : ℕ => A (K * n) / A n) atTop (𝓝 1))
    {ι : Type*} {l : Filter ι} {N M : ι → ℕ} {c : ℝ} (hc : 0 < c)
    (hN : Tendsto N l atTop) (hM : Tendsto M l atTop)
    (hMN : Tendsto (fun i : ι => (M i : ℝ) / (N i : ℝ)) l (𝓝 c)) :
    Tendsto (fun i : ι => A (M i) / A (N i)) l (𝓝 1) := by
  obtain ⟨K, hK⟩ := exists_nat_gt (max c (1 / c))
  have hKc : c < (K : ℝ) := (le_max_left _ _).trans_lt hK
  have hKi : 1 / c < (K : ℝ) := (le_max_right _ _).trans_lt hK
  have hKRpos : 0 < (K : ℝ) := hc.trans hKc
  have hKpos : 0 < K := Nat.cast_pos.mp hKRpos
  have hK1 : 1 ≤ K := hKpos
  have hsmall : 1 / (K : ℝ) < c := by
    apply (div_lt_iff₀ hKRpos).mpr
    simpa only [mul_comm] using (div_lt_iff₀ hc).mp hKi
  have hindices : ∀ᶠ i in l, M i ≤ K * N i ∧ N i ≤ K * M i := by
    filter_upwards [hMN.eventually_le_const hKc, hMN.eventually_const_le hsmall,
      hN.eventually_ge_atTop 1] with i hupper hlower hNi
    have hnR : 0 < (N i : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hNi)
    constructor
    · exact_mod_cast (div_le_iff₀ hnR).mp hupper
    · have hr : (N i : ℝ) ≤ (K : ℝ) * (M i : ℝ) := by
        calc
          (N i : ℝ) = (K : ℝ) * ((1 / (K : ℝ)) * (N i : ℝ)) := by
            field_simp [hKRpos.ne']
          _ ≤ (K : ℝ) * (M i : ℝ) :=
            mul_le_mul_of_nonneg_left ((le_div_iff₀ hnR).mp hlower) hKRpos.le
      exact_mod_cast hr
  have hleft := (hscale K hK1).comp hN
  have hright : Tendsto (fun i : ι => A (M i) / A (K * M i)) l (𝓝 1) := by
    have h := ((hscale K hK1).comp hM).inv₀ (show (1 : ℝ) ≠ 0 from one_ne_zero)
    simpa only [Function.comp_def, Pi.inv_apply, inv_div, inv_one] using h
  have hbounds : ∀ᶠ i in l, A (K * N i) / A (N i) ≤ A (M i) / A (N i) ∧
      A (M i) / A (N i) ≤ A (M i) / A (K * M i) := by
    filter_upwards [hindices, hM.eventually_ge_atTop 1] with i hi hMi
    constructor
    · exact div_le_div_of_nonneg_right (hanti hi.1) (h0 (N i))
    · have hKM : 1 ≤ K * M i := Nat.mul_pos hKpos (lt_of_lt_of_le Nat.zero_lt_one hMi)
      exact div_le_div_of_nonneg_left (h0 (M i)) (hpos _ hKM) (hanti hi.2)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hleft hright
    (hbounds.mono (fun _ h => h.1)) (hbounds.mono (fun _ h => h.2))

/-- Explicitly conditional primitive slow variation; the full source wrapper
supplies the separately proved boundary estimate. -/
theorem ellStar_ratio_of_index_ratio_of_small {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hfixed : ∀ a : ℝ, 0 < a →
      Tendsto (fun x : ℝ => L (a * x) / L x) atTop (𝓝 1))
    (hsum : Summable (fun k : ℕ => L k / (k : ℝ)))
    (hsmall : Tendsto (fun n : ℕ => L n / ellStar L n) atTop (𝓝 0))
    {ι : Type*} {l : Filter ι} {N M : ι → ℕ} {c : ℝ} (hc : 0 < c)
    (hN : Tendsto N l atTop) (hM : Tendsto M l atTop)
    (hMN : Tendsto (fun i : ι => (M i : ℝ) / (N i : ℝ)) l (𝓝 c)) :
    Tendsto (fun i : ι => ellStar L (M i) / ellStar L (N i)) l (𝓝 1) :=
  ratio_tendsto_one_of_integer_scales (ellStar_nonneg hpos)
    (fun _ hn => ellStar_pos hpos hsum hn) (ellStar_antitone hpos hsum)
    (fun _ hK => ellStar_mul_div_tendsto_one_of_small hpos hL hfixed hsum hsmall hK)
    hc hN hM hMN

theorem ellStar_floor_mul_div_tendsto_one_of_small {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hfixed : ∀ a : ℝ, 0 < a →
      Tendsto (fun x : ℝ => L (a * x) / L x) atTop (𝓝 1))
    (hsum : Summable (fun k : ℕ => L k / (k : ℝ)))
    (hsmall : Tendsto (fun n : ℕ => L n / ellStar L n) atTop (𝓝 0))
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => ellStar L ⌊c * n⌋₊ / ellStar L n) atTop (𝓝 1) := by
  apply ellStar_ratio_of_index_ratio_of_small hpos hL hfixed hsum hsmall hc tendsto_id
  · exact tendsto_nat_floor_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hc)
  · exact (tendsto_nat_floor_mul_div_atTop hc.le).comp tendsto_natCast_atTop_atTop

/-- Floor extension resolving the source's evaluation at real arguments. -/
noncomputable def ellStarReal (L : ℝ → ℝ) (x : ℝ) : ℝ := ellStar L ⌊x⌋₊

theorem ellStar_pos_all {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hsum : Summable (fun k : ℕ => L k / (k : ℝ))) (n : ℕ) :
    0 < ellStar L n := by
  apply (summable_tailMass hsum n).tsum_pos
    (fun j => localModel_over_nat_nonneg hpos (n + j)) 1
  have hnR : 0 < ((n + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
  exact div_pos (hpos _ hnR) hnR

theorem ellStarReal_pos {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hsum : Summable (fun k : ℕ => L k / (k : ℝ))) (x : ℝ) :
    0 < ellStarReal L x := ellStar_pos_all hpos hsum _

theorem measurable_ellStarReal (L : ℝ → ℝ) : Measurable (ellStarReal L) :=
  (measurable_of_countable (ellStar L)).comp Nat.measurable_floor

theorem ellStarReal_slowlyVarying_of_small {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hfixed : ∀ a : ℝ, 0 < a →
      Tendsto (fun x : ℝ => L (a * x) / L x) atTop (𝓝 1))
    (hsum : Summable (fun k : ℕ => L k / (k : ℝ)))
    (hsmall : Tendsto (fun n : ℕ => L n / ellStar L n) atTop (𝓝 0)) :
    Bienayme.IsSlowlyVaryingAtTop (ellStarReal L) := by
  intro c hc
  have hN : Tendsto (fun x : ℝ => ⌊x⌋₊) atTop atTop := tendsto_nat_floor_atTop
  have hM : Tendsto (fun x : ℝ => ⌊c * x⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_id.const_mul_atTop hc)
  have hMN : Tendsto (fun x : ℝ => (⌊c * x⌋₊ : ℝ) / (⌊x⌋₊ : ℝ)) atTop (𝓝 c) := by
    have h := (tendsto_nat_floor_mul_div_atTop hc.le).div tendsto_nat_floor_div_atTop
      (show (1 : ℝ) ≠ 0 from one_ne_zero)
    have heq : (fun x : ℝ => ((⌊c * x⌋₊ : ℝ) / x) / ((⌊x⌋₊ : ℝ) / x)) =ᶠ[atTop]
        (fun x : ℝ => (⌊c * x⌋₊ : ℝ) / (⌊x⌋₊ : ℝ)) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ), hN.eventually_gt_atTop 0] with x hx hnx
      have hn0 : (⌊x⌋₊ : ℝ) ≠ 0 := (Nat.cast_pos.mpr hnx).ne'
      field_simp [hx.ne', hn0]
    simpa only [div_one] using h.congr' heq
  exact ellStar_ratio_of_index_ratio_of_small hpos hL hfixed hsum hsmall hc hN hM hMN

/-- The source hypotheses supply the boundary estimate required by the
conditional integer-scale argument. -/
theorem ellStar_mul_div_tendsto_one {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hfixed : ∀ a : ℝ, 0 < a →
      Tendsto (fun x : ℝ => L (a * x) / L x) atTop (𝓝 1))
    (hsum : Summable (fun k : ℕ => L k / (k : ℝ))) {K : ℕ} (hK : 1 ≤ K) :
    Tendsto (fun n : ℕ => ellStar L (K * n) / ellStar L n) atTop (𝓝 1) :=
  ellStar_mul_div_tendsto_one_of_small hpos hL hfixed hsum
    (localModel_div_ellStar_tendsto_zero hpos hL hfixed hsum) hK

theorem ellStar_ratio_of_index_ratio {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hfixed : ∀ a : ℝ, 0 < a →
      Tendsto (fun x : ℝ => L (a * x) / L x) atTop (𝓝 1))
    (hsum : Summable (fun k : ℕ => L k / (k : ℝ)))
    {ι : Type*} {l : Filter ι} {N M : ι → ℕ} {c : ℝ} (hc : 0 < c)
    (hN : Tendsto N l atTop) (hM : Tendsto M l atTop)
    (hMN : Tendsto (fun i : ι => (M i : ℝ) / (N i : ℝ)) l (𝓝 c)) :
    Tendsto (fun i : ι => ellStar L (M i) / ellStar L (N i)) l (𝓝 1) :=
  ellStar_ratio_of_index_ratio_of_small hpos hL hfixed hsum
    (localModel_div_ellStar_tendsto_zero hpos hL hfixed hsum) hc hN hM hMN

theorem ellStar_floor_mul_div_tendsto_one {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hfixed : ∀ a : ℝ, 0 < a →
      Tendsto (fun x : ℝ => L (a * x) / L x) atTop (𝓝 1))
    (hsum : Summable (fun k : ℕ => L k / (k : ℝ))) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => ellStar L ⌊c * n⌋₊ / ellStar L n) atTop (𝓝 1) :=
  ellStar_floor_mul_div_tendsto_one_of_small hpos hL hfixed hsum
    (localModel_div_ellStar_tendsto_zero hpos hL hfixed hsum) hc

/-- Full real-variable slow variation of the explicit floor extension of the
manuscript's integer integrated tail. The boundary estimate is discharged. -/
theorem ellStarReal_slowlyVarying {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hfixed : ∀ a : ℝ, 0 < a →
      Tendsto (fun x : ℝ => L (a * x) / L x) atTop (𝓝 1))
    (hsum : Summable (fun k : ℕ => L k / (k : ℝ))) :
    Bienayme.IsSlowlyVaryingAtTop (ellStarReal L) :=
  ellStarReal_slowlyVarying_of_small hpos hL hfixed hsum
    (localModel_div_ellStar_tendsto_zero hpos hL hfixed hsum)

end SubcriticalCauchy
