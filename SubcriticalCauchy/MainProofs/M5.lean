module

public import SubcriticalCauchy.MainProofs.M5Diagonal
public import SubcriticalCauchy.PreorderHeight

/-!
# Proof helpers for the frozen statement M5

The two implications have independent exported helper theorems.  The positive
moment direction uses an arbitrary diverging centreing rate and a diagonal
argument.  The other direction is in `MainProofs.M5Diagonal`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology BigOperators

namespace SubcriticalCauchy.Bienayme

noncomputable section
open BGW BGW.LocallyFinite

attribute [local instance] Classical.propDecidable


lemma m5Conditioned_centered_eq_zero_of_large (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (n : ℕ) (K : ℝ)
    (hK : (n : ℝ) + |m5LogHeight (offspringMean μ).toReal n| ≤ K) :
    conditioned μ n (finiteTreeEvent fun t =>
      K < |(height t : ℝ) - m5LogHeight (offspringMean μ).toReal n|) = 0 := by
  apply m5Conditioned_eq_zero_of_not_size
  intro t htsize htail
  change K < |(height t : ℝ) - m5LogHeight (offspringMean μ).toReal n| at htail
  have hhNat : height t < t.size := by
    obtain ⟨u, hu, heq⟩ := Finset.exists_mem_eq_sup t.vertices.toFinset
      (vertices_nonempty t) List.length
    rw [height, heq]
    exact vertex_length_lt_size ((PlaneTree.mem_vertices_iff _ _).mp (List.mem_toFinset.mp hu))
  rw [htsize] at hhNat
  have hh : (height t : ℝ) < n := by exact_mod_cast hhNat
  have habs : |(height t : ℝ) - m5LogHeight (offspringMean μ).toReal n| ≤
      (height t : ℝ) + |m5LogHeight (offspringMean μ).toReal n| := by
    simpa only [abs_of_nonneg (by positivity : (0 : ℝ) ≤ height t)] using
      (abs_sub (height t : ℝ) (m5LogHeight (offspringMean μ).toReal n))
  linarith

/-- Non-summability makes every fixed centred height tail have mass tending to
one along the diagonal, contradicting the frozen tightness formulation. -/
theorem main_height_not_tight_of_not_summable
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ)
    (hs : ¬ Summable (fun k : ℕ => (k : ℝ) * Real.log k * (μ {k}).toReal)) :
    ¬ (∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ n : ℕ, 1 ≤ n →
        conditioned μ n (finiteTreeEvent fun t =>
          K < |(height t : ℝ) - m5LogHeight (offspringMean μ).toReal n|)
          ≤ ENNReal.ofReal ε) := by
  intro htight
  have hu := survival_div_mean_pow_tendsto_zero μ
    (offspringMean_pos_of_paper μ hμ.to_literal) hμ.1 hs
  obtain ⟨K₀, hK₀⟩ := htight (1 / 2) (by norm_num)
  let K := max K₀ 0
  have hK : ∀ n : ℕ, 1 ≤ n → conditioned μ n (finiteTreeEvent fun t =>
      K < |(height t : ℝ) - m5LogHeight (offspringMean μ).toReal n|) ≤
      ENNReal.ofReal (1 / 2) := by
    intro n hn
    apply le_trans (measure_mono ?_) (hK₀ n hn)
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨t, lt_of_le_of_lt (le_max_left K₀ 0) ht, rfl⟩
  have hsmall := m5Diagonal_height_tendsto_one μ hμ hu
  have hr := m5DiagonalRate_tendsto μ hμ hu
  have hraw : Tendsto (fun n => m5LogHeight (offspringMean μ).toReal n -
      m5DiagonalRate μ n) atTop atTop := by
    apply tendsto_atTop_mono' atTop _
      ((m5LogHeight_tendsto μ hμ).atTop_div_const (by norm_num : (0 : ℝ) < 2))
    exact Eventually.of_forall fun n => by linarith [m5DiagonalRate_le_half μ n]
  have hlarge : ∀ᶠ n in atTop, ENNReal.ofReal (1 / 2 : ℝ) < conditioned μ n
      (finiteTreeEvent fun t => (height t : ℝ) < max
        (m5LogHeight (offspringMean μ).toReal n - m5DiagonalRate μ n) 1) :=
    hsmall.eventually (eventually_gt_nhds (by norm_num))
  have hfinal : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [hlarge, hr (eventually_gt_atTop K),
      hraw (eventually_gt_atTop 1), eventually_ge_atTop 1] with n hsn hrn hrawn hn
    have heq : max (m5LogHeight (offspringMean μ).toReal n - m5DiagonalRate μ n) 1 =
        m5LogHeight (offspringMean μ).toReal n - m5DiagonalRate μ n :=
      max_eq_left (by change 1 < _ at hrawn; linarith)
    have hle : conditioned μ n (finiteTreeEvent fun t => (height t : ℝ) < max
        (m5LogHeight (offspringMean μ).toReal n - m5DiagonalRate μ n) 1) ≤
        conditioned μ n (finiteTreeEvent fun t =>
          K < |(height t : ℝ) - m5LogHeight (offspringMean μ).toReal n|) := by
      apply measure_mono
      rintro _ ⟨t, ht, rfl⟩
      refine ⟨t, ?_, rfl⟩
      change (height t : ℝ) < max
        (m5LogHeight (offspringMean μ).toReal n - m5DiagonalRate μ n) 1 at ht
      change K < |(height t : ℝ) - m5LogHeight (offspringMean μ).toReal n|
      rw [heq] at ht
      have hrate : K < m5DiagonalRate μ n := by exact hrn
      have hrpos : 0 < m5DiagonalRate μ n := (le_max_right K₀ 0).trans_lt hrate
      rw [abs_of_neg (by linarith : (height t : ℝ) -
        m5LogHeight (offspringMean μ).toReal n < 0)]
      linarith
    exact (not_lt_of_ge (hle.trans (hK n hn))) hsn
  exact hfinal.exists.choose_spec


/-- Summability gives the frozen uniform tightness formulation. -/
theorem main_height_tight_of_summable
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ)
    (hs : Summable (fun k : ℕ => (k : ℝ) * Real.log k * (μ {k}).toReal)) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ n : ℕ, 1 ≤ n →
      conditioned μ n (finiteTreeEvent fun t =>
        K < |(height t : ℝ) - m5LogHeight (offspringMean μ).toReal n|)
        ≤ ENNReal.ofReal ε := by
  obtain ⟨c, hc, hu⟩ := (survival_div_mean_pow_tendsto_pos_iff μ
    (offspringMean_pos_of_paper μ hμ.to_literal) hμ.1).mpr hs
  intro ε hε
  by_contra hnone
  have hbadK : ∀ K : ℝ, ∃ n : ℕ, 1 ≤ n ∧ ENNReal.ofReal ε < conditioned μ n
      (finiteTreeEvent fun t =>
        K < |(height t : ℝ) - m5LogHeight (offspringMean μ).toReal n|) := by
    intro K
    by_contra hb
    push Not at hb
    exact hnone ⟨K, hb⟩
  let N : ℕ → ℕ := fun j => Classical.choose (hbadK (j : ℝ))
  have hNspec (j : ℕ) := Classical.choose_spec (hbadK (j : ℝ))
  have hN1 (j : ℕ) : 1 ≤ N j := (hNspec j).1
  have hNbad (j : ℕ) : ENNReal.ofReal ε < conditioned μ (N j)
      (finiteTreeEvent fun t => (j : ℝ) <
        |(height t : ℝ) - m5LogHeight (offspringMean μ).toReal (N j)|) :=
    (hNspec j).2
  have hNtop : Tendsto N atTop atTop := by
    refine tendsto_atTop.2 fun B => ?_
    let C : ℝ := ∑ i ∈ Finset.range (B + 1),
      ((i : ℝ) + |m5LogHeight (offspringMean μ).toReal i|)
    obtain ⟨J, hCJ⟩ := exists_nat_gt C
    filter_upwards [eventually_ge_atTop J] with j hj
    by_contra hnot
    have hNB : N j ≤ B := (Nat.lt_of_not_ge hnot).le
    have hterm : (N j : ℝ) + |m5LogHeight (offspringMean μ).toReal (N j)| ≤ C := by
      dsimp [C]
      exact Finset.single_le_sum
        (f := fun i : ℕ => (i : ℝ) + |m5LogHeight (offspringMean μ).toReal i|)
        (fun i hi => by positivity) (Finset.mem_range.mpr (by omega))
    have hCJl : C < (j : ℝ) := hCJ.trans_le (by exact_mod_cast hj)
    have hz := m5Conditioned_centered_eq_zero_of_large μ (N j) (j : ℝ)
      (hterm.trans_lt hCJl).le
    have hpos : 0 < conditioned μ (N j) (finiteTreeEvent fun t => (j : ℝ) <
        |(height t : ℝ) - m5LogHeight (offspringMean μ).toReal (N j)|) :=
      (ENNReal.ofReal_pos.mpr hε).trans (hNbad j)
    rw [hz] at hpos
    exact (lt_irrefl 0 hpos)
  let J : ℕ → ℕ := fun n => if h : ∃ j, N j = n then Nat.find h else 0
  have hJN (n : ℕ) (hb : ∃ j, N j = n) : N (J n) = n := by
    dsimp [J]
    rw [dite_eq_left hb]
    exact Nat.find_spec hb
  let r : ℕ → ℝ := fun n => if h : ∃ j, N j = n then
    min (J n : ℝ) (m5LogHeight (offspringMean μ).toReal n / 2)
    else min (m5SlowRate (offspringMean μ).toReal n)
      (m5LogHeight (offspringMean μ).toReal n / 2)
  have hrL : ∀ᶠ n in atTop, r n ≤ m5LogHeight (offspringMean μ).toReal n / 2 := by
    apply Eventually.of_forall
    intro n
    dsimp only [r]
    split_ifs <;> exact min_le_right _ _
  have hr : Tendsto r atTop atTop := by
    refine tendsto_atTop.2 fun B => ?_
    obtain ⟨q, hBq⟩ := exists_nat_gt B
    let C : ℕ := ∑ j ∈ Finset.range (q + 1), N j
    have hslow : Tendsto (m5SlowRate (offspringMean μ).toReal) atTop atTop :=
      m5SlowRate_tendsto μ hμ
    have hhalf : Tendsto (fun n => m5LogHeight (offspringMean μ).toReal n / 2)
        atTop atTop := (m5LogHeight_tendsto μ hμ).atTop_div_const (by norm_num)
    filter_upwards [hslow (eventually_gt_atTop (q : ℝ)), hhalf (eventually_gt_atTop (q : ℝ)),
      eventually_gt_atTop C] with n hsn hln hnC
    change (q : ℝ) < m5SlowRate (offspringMean μ).toReal n at hsn
    change (q : ℝ) < m5LogHeight (offspringMean μ).toReal n / 2 at hln
    change C < n at hnC
    by_cases hb : ∃ j, N j = n
    · have hqJ : q < J n := by
        by_contra hnot
        have hJq : J n ≤ q := Nat.le_of_not_gt hnot
        have hle : N (J n) ≤ C := by
          dsimp [C]
          apply Finset.single_le_sum
          · intro i hi
            exact Nat.zero_le _
          · exact Finset.mem_range.mpr (by omega)
        have heq := hJN n hb
        omega
      have hqJ' : (q : ℝ) < (J n : ℝ) := by exact_mod_cast hqJ
      rw [show r n = min (J n : ℝ) (m5LogHeight (offspringMean μ).toReal n / 2) by
        simp only [r, dite_eq_left hb]]
      exact le_min (by linarith) (by linarith)
    · rw [show r n = min (m5SlowRate (offspringMean μ).toReal n)
        (m5LogHeight (offspringMean μ).toReal n / 2) by simp only [r, dite_eq_right hb]]
      exact le_min (by linarith) (by linarith)
  have hconc := m5Centered_tail_tendsto_zero_of_pos_limit μ hμ r hc hu hr hrL
  have hconcN := hconc.comp hNtop
  have hev : ∀ᶠ j : ℕ in atTop, conditioned μ (N j) (finiteTreeEvent fun t =>
      r (N j) ≤ |(height t : ℝ) - m5LogHeight (offspringMean μ).toReal (N j)|) <
      ENNReal.ofReal ε := by
    exact hconcN.eventually (eventually_lt_nhds (ENNReal.ofReal_pos.mpr hε))
  obtain ⟨j, hj⟩ := hev.exists
  let n := N j
  have hb : ∃ i, N i = n := ⟨j, rfl⟩
  have hrJ : r n ≤ (J n : ℝ) := by
    dsimp only [r]
    rw [dite_eq_left hb]
    exact min_le_left _ _
  have hbadJ := hNbad (J n)
  rw [hJN n hb] at hbadJ
  have hle : conditioned μ n (finiteTreeEvent fun t => (J n : ℝ) <
      |(height t : ℝ) - m5LogHeight (offspringMean μ).toReal n|) ≤
      conditioned μ n (finiteTreeEvent fun t =>
        r n ≤ |(height t : ℝ) - m5LogHeight (offspringMean μ).toReal n|) := by
    apply measure_mono
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨t, le_trans hrJ ht.le, rfl⟩
  have hbig := hbadJ.trans_le hle
  exact (lt_asymm (by simpa only [n, Function.comp_apply] using hj) hbig)


/-- Packaged equivalence used by the sole frozen M5 hole. -/
theorem main_height_tight_iff_proof (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) :
    (∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ n : ℕ, 1 ≤ n →
        conditioned μ n (finiteTreeEvent fun t =>
          K < |(height t : ℝ) - m5LogHeight (offspringMean μ).toReal n|)
          ≤ ENNReal.ofReal ε) ↔
      Summable (fun k : ℕ => (k : ℝ) * Real.log k * (μ {k}).toReal) := by
  constructor
  · intro ht
    by_contra hs
    exact main_height_not_tight_of_not_summable μ hμ hs ht
  · exact main_height_tight_of_summable μ hμ

end
end SubcriticalCauchy.Bienayme
