module

public import SubcriticalCauchy.PaperRoute.BergerTight
public import SubcriticalCauchy.LocalMassVariation
public import SubcriticalCauchy.TotalVariationTypical

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Discrete one-big-jump identities for Berger's local limit

The lemmas here are measure-theoretic combinatorics for an arbitrary iid law on
the integers.  No endpoint-local-limit module is used.
-/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Topology BigOperators

namespace SubcriticalCauchy.Bienayme

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Product weights after insertion of one coordinate. -/
lemma berger_insert_weight {m : ℕ} (ν : Measure ℤ) (i : Fin (m + 1))
    (w : ℤ) (y : Fin m → ℤ) :
    (∏ j, ν {Fin.insertNth (α := fun _ => ℤ) i w y j}) =
      ν {w} * ∏ j, ν {y j} := by
  rw [← Fin.prod_insertNth (M := ℝ≥0∞) i (ν {w}) (fun j => ν {y j})]
  apply Finset.prod_congr rfl
  intro k _
  refine Fin.succAboveCases i ?_ (fun j => ?_) k <;> simp

/-- Exact decomposition of a fixed-position cell over the residual vector. -/
lemma berger_fixed_cell {m : ℕ} (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (i : Fin (m + 1)) (T : ℤ) (B : Set ℤ) :
    (Measure.pi fun _ : Fin (m + 1) => ν)
      {x | (∑ j, x j) = T ∧ x i ∈ B} =
      ∑' y : Fin m → ℤ,
        (if T - ∑ j, y j ∈ B then ν {T - ∑ j, y j} else 0) *
          ∏ j, ν {y j} := by
  classical
  let e := Fin.insertNthEquiv (fun _ : Fin (m + 1) => ℤ) i
  let A : Set (Fin (m + 1) → ℤ) := {x | (∑ j, x j) = T ∧ x i ∈ B}
  let g : (Fin (m + 1) → ℤ) → ℝ≥0∞ := fun x =>
    A.indicator (fun v => ∏ j, ν {v j}) x
  have hterm (y : Fin m → ℤ) : (∑' w : ℤ, g (e (w, y))) =
      (if T - ∑ j, y j ∈ B then ν {T - ∑ j, y j} else 0) *
        ∏ j, ν {y j} := by
    let w₀ := T - ∑ j, y j
    have hsum : w₀ + ∑ j, y j = T := by dsimp [w₀]; ring
    have hne (w : ℤ) (hw : w ≠ w₀) : g (e (w, y)) = 0 := by
      apply Set.indicator_of_notMem
      intro hmem
      change (∑ j, Fin.insertNth (α := fun _ => ℤ) i w y j) = T ∧ _ at hmem
      rw [Fin.sum_insertNth] at hmem
      apply hw
      dsimp [w₀]
      omega
    rw [tsum_eq_single w₀ hne]
    by_cases hw : w₀ ∈ B
    · have hmem : e (w₀, y) ∈ A := by
        change (∑ j, Fin.insertNth (α := fun _ => ℤ) i w₀ y j) = T ∧ _
        rw [Fin.sum_insertNth, hsum]
        exact ⟨rfl, by simpa only [e, Fin.insertNthEquiv_apply,
          Fin.insertNth_apply_same] using hw⟩
      change A.indicator (fun v => ∏ j, ν {v j}) (e (w₀, y)) = _
      rw [Set.indicator_of_mem hmem]
      change (∏ j, ν {Fin.insertNth (α := fun _ => ℤ) i w₀ y j}) = _
      rw [berger_insert_weight]
      change ν {w₀} * _ = (if w₀ ∈ B then ν {w₀} else 0) * _
      rw [ite_eq_left hw]
    · have hnotmem : e (w₀, y) ∉ A := by
        intro hmem
        exact hw (by simpa only [e, Fin.insertNthEquiv_apply,
          Fin.insertNth_apply_same] using hmem.2)
      change A.indicator (fun v => ∏ j, ν {v j}) (e (w₀, y)) = _
      rw [Set.indicator_of_notMem hnotmem]
      change 0 = (if w₀ ∈ B then ν {w₀} else 0) * _
      rw [ite_eq_right hw, zero_mul]
  calc
    (Measure.pi fun _ : Fin (m + 1) => ν) A =
        ∑' x, A.indicator (fun x => (Measure.pi fun _ : Fin (m + 1) => ν) {x}) x := by
      rw [Measure.tsum_indicator_apply_singleton _ A (Set.to_countable A).measurableSet]
    _ = ∑' x, g x := by
      apply tsum_congr
      intro x
      by_cases hx : x ∈ A <;> simp [g, hx, Measure.pi_singleton]
    _ = ∑' p : ℤ × (Fin m → ℤ), g (e p) := (e.tsum_eq g).symm
    _ = ∑' w : ℤ, ∑' y : Fin m → ℤ, g (e (w, y)) := ENNReal.tsum_prod (f := fun (w : ℤ) (y : Fin m → ℤ) => g (e (w, y)))
    _ = ∑' y : Fin m → ℤ, ∑' w : ℤ, g (e (w, y)) := ENNReal.tsum_comm
    _ = _ := tsum_congr hterm

/-- Union bound over the position of a jump satisfying `B`. -/
lemma berger_big_jump_union {m : ℕ} (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (T : ℤ) (B : Set ℤ) :
    (Measure.pi fun _ : Fin (m + 1) => ν)
      {x | (∑ j, x j) = T ∧ ∃ i, x i ∈ B} ≤
      (m + 1 : ℝ≥0∞) * ∑' y : Fin m → ℤ,
        (if T - ∑ j, y j ∈ B then ν {T - ∑ j, y j} else 0) *
          ∏ j, ν {y j} := by
  classical
  let A : Fin (m + 1) → Set (Fin (m + 1) → ℤ) := fun i =>
    {x | (∑ j, x j) = T ∧ x i ∈ B}
  calc
    _ ≤ (Measure.pi fun _ : Fin (m + 1) => ν) (⋃ i, A i) := by
      apply measure_mono
      rintro x ⟨hsum, i, hi⟩
      exact Set.mem_iUnion.mpr ⟨i, hsum, hi⟩
    _ ≤ ∑' i, (Measure.pi fun _ : Fin (m + 1) => ν) (A i) := measure_iUnion_le _
    _ = ∑' _i : Fin (m + 1), ∑' y : Fin m → ℤ,
        (if T - ∑ j, y j ∈ B then ν {T - ∑ j, y j} else 0) *
          ∏ j, ν {y j} := by
      apply tsum_congr
      intro i
      exact berger_fixed_cell ν i T B
    _ = _ := by
      rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      push_cast
      rfl

/-- Weight over an arbitrary residual event. -/
lemma berger_weight_event {m : ℕ} (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (G : Set (Fin m → ℤ)) :
    (∑' y : Fin m → ℤ, G.indicator (fun y => ∏ j, ν {y j}) y) =
      (Measure.pi fun _ : Fin m => ν) G := by
  rw [← Measure.tsum_indicator_apply_singleton
    (Measure.pi fun _ : Fin m => ν) G (Set.to_countable G).measurableSet]
  apply tsum_congr
  intro y
  by_cases hy : y ∈ G <;> simp [hy, Measure.pi_singleton]

/-- The total residual product weight is one. -/
lemma berger_total_weight {m : ℕ} (ν : Measure ℤ) [IsProbabilityMeasure ν] :
    (∑' y : Fin m → ℤ, ∏ j, ν {y j}) = 1 := by
  calc
    _ = ∑' y : Fin m → ℤ, Set.univ.indicator (fun y => ∏ j, ν {y j}) y := by
      apply tsum_congr
      intro y
      simp
    _ = (Measure.pi fun _ : Fin m => ν) Set.univ := berger_weight_event ν Set.univ
    _ = 1 := measure_univ

/-- Upper cell bound when every allowed inserted mass is dominated by `C`. -/
lemma berger_near_cell_bound {m : ℕ} (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (T : ℤ) (B : Set ℤ) (C : ℝ≥0∞) (z : ℤ)
    (hmass : ∀ w ∈ B, ν {w} ≤ C * ν {z}) :
    (Measure.pi fun _ : Fin (m + 1) => ν)
      {x | (∑ j, x j) = T ∧ ∃ i, x i ∈ B} ≤
      (m + 1 : ℝ≥0∞) * C * ν {z} := by
  calc
    _ ≤ (m + 1 : ℝ≥0∞) * ∑' y : Fin m → ℤ,
        (if T - ∑ j, y j ∈ B then ν {T - ∑ j, y j} else 0) *
          ∏ j, ν {y j} := berger_big_jump_union ν T B
    _ ≤ (m + 1 : ℝ≥0∞) * ∑' y : Fin m → ℤ,
        (C * ν {z}) * ∏ j, ν {y j} := by
      apply mul_le_mul_right
      apply ENNReal.tsum_le_tsum
      intro y
      by_cases hy : T - ∑ j, y j ∈ B
      · simp only [hy, ↓reduceIte]
        exact mul_le_mul_left (hmass _ hy) _
      · simp [hy]
    _ = (m + 1 : ℝ≥0∞) * C * ν {z} := by
      rw [ENNReal.tsum_mul_left, berger_total_weight, mul_one]
      ring

/-- Upper cell bound with a residual exceptional event. -/
lemma berger_far_cell_bound {m : ℕ} (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (T : ℤ) (B : Set ℤ) (G : Set (Fin m → ℤ)) (C : ℝ≥0∞) (z : ℤ)
    (hmass : ∀ w ∈ B, ν {w} ≤ C * ν {z})
    (hbad : ∀ y : Fin m → ℤ, T - ∑ j, y j ∈ B → y ∈ G) :
    (Measure.pi fun _ : Fin (m + 1) => ν)
      {x | (∑ j, x j) = T ∧ ∃ i, x i ∈ B} ≤
      (m + 1 : ℝ≥0∞) * C * ν {z} * (Measure.pi fun _ : Fin m => ν) G := by
  calc
    _ ≤ (m + 1 : ℝ≥0∞) * ∑' y : Fin m → ℤ,
        (if T - ∑ j, y j ∈ B then ν {T - ∑ j, y j} else 0) *
          ∏ j, ν {y j} := berger_big_jump_union ν T B
    _ ≤ (m + 1 : ℝ≥0∞) * ∑' y : Fin m → ℤ,
        (C * ν {z}) * G.indicator (fun y => ∏ j, ν {y j}) y := by
      apply mul_le_mul_right
      apply ENNReal.tsum_le_tsum
      intro y
      by_cases hy : T - ∑ j, y j ∈ B
      · rw [Set.indicator_of_mem (hbad y hy)]
        simp only [hy, ↓reduceIte]
        exact mul_le_mul_left (hmass _ hy) _
      · simp [hy, Set.indicator]
    _ = (m + 1 : ℝ≥0∞) * C * ν {z} * (Measure.pi fun _ : Fin m => ν) G := by
      rw [ENNReal.tsum_mul_left, berger_weight_event]
      ring

/-- Singleton masses of the increment law, including the boundary atom `-1`. -/
lemma berger_incrementLaw_singleton (μ : Measure ℕ) (z : ℤ) (hz : -1 ≤ z) :
    incrementLaw μ {z} = μ {(z + 1).toNat} := by
  rw [incrementLaw, Measure.map_apply (measurable_of_countable _)
    (measurableSet_singleton _)]
  congr 1
  ext k
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  have hz' : ((z + 1).toNat : ℤ) = z + 1 := Int.toNat_of_nonneg (by omega)
  change ((k : ℤ) - 1 = z ↔ k = (z + 1).toNat)
  omega

/-- Strict maxima identify both an inserted coordinate and its residual. -/
lemma berger_insert_injective {m : ℕ}
    (f : (Fin m → ℤ) → ℤ)
    (G : Set (Fin m → ℤ))
    (hstrict : ∀ y ∈ G, ∀ j, y j < f y) :
    Function.Injective (fun x : G × Fin (m + 1) =>
      Fin.insertNth (α := fun _ => ℤ) x.2 (f x.1.1) x.1.1) := by
  rintro ⟨y, i⟩ ⟨y', i'⟩ h
  have hi : i = i' := by
    by_contra hne
    obtain ⟨j, hij⟩ := Fin.exists_succAbove_eq hne
    obtain ⟨k, hki⟩ := Fin.exists_succAbove_eq (Ne.symm hne)
    have hv₁ := congrFun h i
    have hv₂ := congrFun h i'
    rw [← hij] at hv₁
    rw [← hki] at hv₂
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove] at hv₁ hv₂
    have hlt₁ := hstrict y'.1 y'.2 j
    have hlt₂ := hstrict y.1 y.2 k
    omega
  subst i'
  have hw : f y.1 = f y'.1 := by
    have hv := congrFun h i
    simpa only [Fin.insertNth_apply_same] using hv
  have hy : y.1 = y'.1 := by
    funext j
    have hv := congrFun h (i.succAbove j)
    simpa only [Fin.insertNth_apply_succAbove] using hv
  have hy' : y = y' := Subtype.ext hy
  subst y'
  rfl

/-- Lower bound from all strict-maximum insertions into a residual event. -/
lemma berger_lower_insertions {m : ℕ} (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (T : ℤ) (G : Set (Fin m → ℤ)) (B : Set ℤ) (c : ℝ≥0∞) (z : ℤ)
    (hnear : ∀ y ∈ G, T - ∑ j, y j ∈ B)
    (hstrict : ∀ y ∈ G, ∀ j, y j < T - ∑ k, y k)
    (hmass : ∀ w ∈ B, c * ν {z} ≤ ν {w}) :
    c * (m + 1 : ℝ≥0∞) * ν {z} * (Measure.pi fun _ : Fin m => ν) G ≤
      (Measure.pi fun _ : Fin (m + 1) => ν) {x | ∑ j, x j = T} := by
  classical
  let f : (G × Fin (m + 1)) → (Fin (m + 1) → ℤ) := fun x =>
    Fin.insertNth (α := fun _ => ℤ) x.2 (T - ∑ j, x.1.1 j) x.1.1
  let E : Set (Fin (m + 1) → ℤ) := {x | ∑ j, x j = T}
  have hfmem (x : G × Fin (m + 1)) : f x ∈ E := by
    change (∑ j, f x j) = T
    dsimp [f]
    rw [Fin.sum_insertNth]
    ring
  have hfinj : Function.Injective f := by
    apply berger_insert_injective (fun y => T - ∑ j, y j) G hstrict
  have hsum_const : (∑' x : G × Fin (m + 1),
      c * ν {z} * ∏ j, ν {x.1.1 j}) =
      c * (m + 1 : ℝ≥0∞) * ν {z} * (Measure.pi fun _ : Fin m => ν) G := by
    calc
      _ = ∑' y : G, ∑' _i : Fin (m + 1),
          c * ν {z} * ∏ j, ν {y.1 j} := ENNReal.tsum_prod (f := fun (y : G) (_i : Fin (m + 1)) =>
        c * ν {z} * ∏ j, ν {y.1 j})
      _ = ∑' y : G, (m + 1 : ℝ≥0∞) *
          (c * ν {z} * ∏ j, ν {y.1 j}) := by
        apply tsum_congr
        intro y
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        push_cast
        rfl
      _ = _ := by
        simp_rw [show ∀ y : G, (m + 1 : ℝ≥0∞) *
          (c * ν {z} * ∏ j, ν {y.1 j}) =
          (c * (m + 1 : ℝ≥0∞) * ν {z}) * ∏ j, ν {y.1 j} from
            fun y => by ring]
        rw [ENNReal.tsum_mul_left]
        congr 1
        rw [← berger_weight_event ν G, ← tsum_subtype]
  calc
    c * (m + 1 : ℝ≥0∞) * ν {z} * (Measure.pi fun _ : Fin m => ν) G =
        ∑' x : G × Fin (m + 1), c * ν {z} * ∏ j, ν {x.1.1 j} := hsum_const.symm
    _ ≤ ∑' x : G × Fin (m + 1),
        E.indicator (fun x => ∏ j, ν {x j}) (f x) := by
      apply ENNReal.tsum_le_tsum
      intro x
      rw [Set.indicator_of_mem (hfmem x)]
      change c * ν {z} * ∏ j, ν {x.1.1 j} ≤
        ∏ j, ν {(Fin.insertNth (α := fun _ => ℤ) x.2
          (T - ∑ k, x.1.1 k) x.1.1) j}
      rw [berger_insert_weight]
      have hn := hnear x.1.1 x.1.2
      exact mul_le_mul_left (by simpa only [mul_comm] using hmass _ hn) _
    _ ≤ ∑' x : Fin (m + 1) → ℤ,
        E.indicator (fun x => ∏ j, ν {x j}) x :=
      ENNReal.tsum_comp_le_tsum_of_injective hfinj _
    _ = (Measure.pi fun _ : Fin (m + 1) => ν) E := by
      rw [← Measure.tsum_indicator_apply_singleton
        (Measure.pi fun _ : Fin (m + 1) => ν) E (Set.to_countable E).measurableSet]
      apply tsum_congr
      intro x
      by_cases hx : x ∈ E <;> simp [hx, Measure.pi_singleton]


/-- Singleton mass ratios along integer sequences with a positive limiting ratio. -/
lemma berger_nat_mass_ratio_tendsto
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

/-- Uniform upper comparison for singleton masses on a compact ratio interval. -/
lemma berger_nat_mass_ratio_compact
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ)
    {a b : ℝ} (ha : 0 < a) (_hab : a ≤ b)
    {z : ℕ → ℝ} (hz : Tendsto z atTop atTop) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ j k : ℕ, z n ≤ (j : ℝ) →
      (k : ℝ) / (j : ℝ) ∈ Set.Icc a b →
      (μ {k}).toReal / (μ {j}).toReal < (a ^ 2)⁻¹ + η := by
  classical
  by_contra hnot
  have hbad (N : ℕ) : ∃ (n j k : ℕ), N ≤ n ∧ z n ≤ (j : ℝ) ∧
      (k : ℝ) / (j : ℝ) ∈ Set.Icc a b ∧
      (a ^ 2)⁻¹ + η ≤ (μ {k}).toReal / (μ {j}).toReal := by
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
  have hmass := berger_nat_mass_ratio_tendsto μ hμ hρ0 hjsSubN hksSubN hρ
  have hρpow : (ρ ^ 2)⁻¹ ≤ (a ^ 2)⁻¹ := by
    apply inv_anti₀ (sq_pos_of_pos ha)
    exact pow_le_pow_left₀ ha.le hρmem.1 2
  have hlt : (ρ ^ 2)⁻¹ < (a ^ 2)⁻¹ + η := by linarith
  obtain ⟨n, hn⟩ := (hmass.eventually (gt_mem_nhds hlt)).exists
  exact (not_lt_of_ge (herr (φ n))) hn

/-- Convert a real pointwise comparison to extended nonnegative reals. -/
lemma berger_mul_le_ofReal_of_toReal {p q : ℝ≥0∞} {c : ℝ}
    (hp : p ≠ ∞) (hq : q ≠ ∞) (hc : 0 ≤ c)
    (h : p.toReal ≤ c * q.toReal) :
    p ≤ ENNReal.ofReal c * q := by
  apply (ENNReal.toReal_le_toReal hp (by finiteness)).mp
  simpa [ENNReal.toReal_ofReal hc] using h

/-- Convert a real lower pointwise comparison to extended nonnegative reals. -/
lemma berger_ofReal_mul_le_of_toReal {p q : ℝ≥0∞} {c : ℝ}
    (hp : p ≠ ∞) (hq : q ≠ ∞) (hc : 0 ≤ c)
    (h : c * q.toReal ≤ p.toReal) :
    ENNReal.ofReal c * q ≤ p := by
  apply (ENNReal.toReal_le_toReal (by finiteness) hp).mp
  simpa [ENNReal.toReal_ofReal hc] using h


/-- Potter comparison of singleton masses, uniform over all indices above a
fixed positive proportion of the base index. -/
lemma berger_nat_mass_potter
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ)
    {z : ℕ → ℝ} (hz : Tendsto z atTop atTop)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ j k : ℕ,
      z n ≤ (j : ℝ) → δ * (j : ℝ) ≤ (k : ℝ) →
      (μ {k}).toReal ≤ C * (μ {j}).toReal := by
  obtain ⟨hm, L, hpos, hsv, hmeas, hlocal⟩ := hμ
  obtain ⟨P, hP, N, hN, hp⟩ := potter_bounds hpos hmeas hsv (1 / 2) (by norm_num)
  have hlo := hlocal.eventually_const_lt (by norm_num : (1 / 2 : ℝ) < 1)
  have hhi := hlocal.eventually_lt_const (by norm_num : (1 : ℝ) < 2)
  obtain ⟨B, hB⟩ := eventually_atTop.mp (hlo.and hhi)
  let C := 4 * P * δ ^ (-(5 / 2) : ℝ)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  have hbase : ∀ᶠ n : ℕ in atTop,
      max N (max B 1) ≤ z n ∧ max N (B : ℝ) ≤ δ * z n := by
    filter_upwards [hz.eventually_ge_atTop (max N (max B 1)),
      (hz.const_mul_atTop hδ).eventually_ge_atTop (max N (B : ℝ))] with n hn hBn
    exact ⟨hn, hBn⟩
  filter_upwards [hbase] with n hn j k hj hjk
  obtain ⟨hzN, hzB⟩ := hn
  have hjN : N ≤ (j : ℝ) := (le_max_left _ _).trans hzN |>.trans hj
  have hmaxj : max N (max (B : ℝ) 1) ≤ (j : ℝ) := hzN.trans hj
  have hjB : (B : ℝ) ≤ (j : ℝ) :=
    ((le_max_left (B : ℝ) 1).trans (le_max_right N _)).trans hmaxj
  have hj1 : (1 : ℝ) ≤ (j : ℝ) :=
    ((le_max_right (B : ℝ) 1).trans (le_max_right N _)).trans hmaxj
  have hj0 : (0 : ℝ) < j := zero_lt_one.trans_le hj1
  have hk0 : (0 : ℝ) < k := (mul_pos hδ hj0).trans_le hjk
  have hkB : (B : ℝ) ≤ (k : ℝ) := by
    calc
      (B : ℝ) ≤ max N (B : ℝ) := le_max_right _ _
      _ ≤ δ * z n := hzB
      _ ≤ δ * (j : ℝ) := by gcongr
      _ ≤ (k : ℝ) := hjk
  have hkN : N ≤ (k : ℝ) := by
    calc
      N ≤ max N (B : ℝ) := le_max_left _ _
      _ ≤ δ * z n := hzB
      _ ≤ δ * (j : ℝ) := by gcongr
      _ ≤ (k : ℝ) := hjk
  have hLj := hpos (j : ℝ) hj0
  have hLk := hpos (k : ℝ) hk0
  have hMj : 0 < L (j : ℝ) / (j : ℝ) ^ 2 := div_pos hLj (sq_pos_of_pos hj0)
  have hMk : 0 < L (k : ℝ) / (k : ℝ) ^ 2 := div_pos hLk (sq_pos_of_pos hk0)
  have hjloc := hB j (by exact_mod_cast hjB)
  have hkloc := hB k (by exact_mod_cast hkB)
  have hjk0 : 0 < (k : ℝ) / (j : ℝ) := div_pos hk0 hj0
  have hrδ : δ ≤ (k : ℝ) / (j : ℝ) := (le_div_iff₀ hj0).mpr hjk
  have hpowδ3 : ((k : ℝ) / (j : ℝ)) ^ (-(3 / 2) : ℝ) ≤
      δ ^ (-(3 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hδ hrδ (by norm_num)
  have hpowδ5 : ((k : ℝ) / (j : ℝ)) ^ (-(5 / 2) : ℝ) ≤
      δ ^ (-(5 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hδ hrδ (by norm_num)
  have hpowδ35 : δ ^ (-(3 / 2) : ℝ) ≤ δ ^ (-(5 / 2) : ℝ) := by
    calc
      δ ^ (-(3 / 2) : ℝ) = (δ⁻¹) ^ (3 / 2 : ℝ) := by
        rw [Real.inv_rpow hδ.le, Real.rpow_neg hδ.le]
      _ ≤ (δ⁻¹) ^ (5 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le ((one_le_inv₀ hδ).mpr hδ1) (by norm_num)
      _ = δ ^ (-(5 / 2) : ℝ) := by
        rw [Real.inv_rpow hδ.le, Real.rpow_neg hδ.le]
  have hLratio : L (k : ℝ) / L (j : ℝ) ≤
      P * δ ^ (-(5 / 2) : ℝ) * ((k : ℝ) / (j : ℝ)) ^ 2 := by
    by_cases hkj : (j : ℝ) ≤ (k : ℝ)
    · have hu := (hp (j : ℝ) (k : ℝ) hjN hkj).2
      have hr1 : 1 ≤ (k : ℝ) / (j : ℝ) := (one_le_div₀ hj0).mpr hkj
      have hsmall : ((k : ℝ) / (j : ℝ)) ^ (-(3 / 2) : ℝ) ≤ δ ^ (-(5 / 2) : ℝ) :=
        hpowδ3.trans hpowδ35
      have hprof : ((k : ℝ) / (j : ℝ)) ^ (1 / 2 : ℝ) /
          ((k : ℝ) / (j : ℝ)) ^ (2 : ℝ) =
          ((k : ℝ) / (j : ℝ)) ^ (-(3 / 2) : ℝ) := by
        rw [← Real.rpow_sub hjk0]
        norm_num
      calc
        L (k : ℝ) / L (j : ℝ) ≤ P * ((k : ℝ) / (j : ℝ)) ^ (1 / 2 : ℝ) := hu
        _ = P * (((k : ℝ) / (j : ℝ)) ^ (-(3 / 2) : ℝ) *
            ((k : ℝ) / (j : ℝ)) ^ 2) := by
          rw [← Real.rpow_two]
          rw [← hprof]
          field_simp
        _ ≤ P * (δ ^ (-(5 / 2) : ℝ) * ((k : ℝ) / (j : ℝ)) ^ 2) := by gcongr
        _ = _ := by ring
    · have hkj' : (k : ℝ) ≤ (j : ℝ) := le_of_not_ge hkj
      have hl := (hp (k : ℝ) (j : ℝ) hkN hkj').1
      have hq : 0 < ((j : ℝ) / (k : ℝ)) ^ (-(1 / 2) : ℝ) :=
        Real.rpow_pos_of_pos (div_pos hj0 hk0) _
      have hdiv : 0 < L (j : ℝ) / L (k : ℝ) := div_pos hLj hLk
      have hinv := (inv_le_inv₀ hdiv (mul_pos (inv_pos.mpr hP) hq)).mpr hl
      have hswap : L (k : ℝ) / L (j : ℝ) ≤
          P * ((j : ℝ) / (k : ℝ)) ^ (1 / 2 : ℝ) := by
        calc
          L (k : ℝ) / L (j : ℝ) = (L (j : ℝ) / L (k : ℝ))⁻¹ := by field_simp
          _ ≤ (P⁻¹ * ((j : ℝ) / (k : ℝ)) ^ (-(1 / 2) : ℝ))⁻¹ := hinv
          _ = P * ((j : ℝ) / (k : ℝ)) ^ (1 / 2 : ℝ) := by
            rw [mul_inv, inv_inv, ← Real.rpow_neg (le_of_lt (div_pos hj0 hk0))]
            ring_nf
      have hsmall : ((j : ℝ) / (k : ℝ)) ^ (1 / 2 : ℝ) /
          ((k : ℝ) / (j : ℝ)) ^ 2 ≤ δ ^ (-(5 / 2) : ℝ) := by
        have hid : ((j : ℝ) / (k : ℝ)) ^ (1 / 2 : ℝ) /
            ((k : ℝ) / (j : ℝ)) ^ 2 =
            ((k : ℝ) / (j : ℝ)) ^ (-(5 / 2) : ℝ) := by
          have hinv : (j : ℝ) / (k : ℝ) = ((k : ℝ) / (j : ℝ))⁻¹ := by
            field_simp
          rw [hinv, Real.inv_rpow hjk0.le, ← Real.rpow_neg hjk0.le,
            ← Real.rpow_two, ← Real.rpow_sub hjk0]
          norm_num
        rw [hid]
        exact hpowδ5
      calc
        L (k : ℝ) / L (j : ℝ) ≤ P * ((j : ℝ) / (k : ℝ)) ^ (1 / 2 : ℝ) := hswap
        _ = P * ((((j : ℝ) / (k : ℝ)) ^ (1 / 2 : ℝ) /
            ((k : ℝ) / (j : ℝ)) ^ 2) * ((k : ℝ) / (j : ℝ)) ^ 2) := by
          field_simp
        _ ≤ P * (δ ^ (-(5 / 2) : ℝ) * ((k : ℝ) / (j : ℝ)) ^ 2) := by gcongr
        _ = _ := by ring
  have hpj : (μ {j}).toReal ≤ 2 * (L (j : ℝ) / (j : ℝ) ^ 2) :=
    (div_lt_iff₀ hMj).mp hjloc.2 |>.le
  have hMjile : L (j : ℝ) / (j : ℝ) ^ 2 ≤ 2 * (μ {j}).toReal := by
    have hh := (lt_div_iff₀ hMj).mp hjloc.1
    linarith
  have hpk : (μ {k}).toReal ≤ 2 * (L (k : ℝ) / (k : ℝ) ^ 2) :=
    (div_lt_iff₀ hMk).mp hkloc.2 |>.le
  calc
    (μ {k}).toReal ≤ 2 * (L (k : ℝ) / (k : ℝ) ^ 2) := hpk
    _ = 2 * ((L (k : ℝ) / L (j : ℝ)) / ((k : ℝ) / (j : ℝ)) ^ 2) *
        (L (j : ℝ) / (j : ℝ) ^ 2) := by field_simp
    _ ≤ 2 * (P * δ ^ (-(5 / 2) : ℝ)) * (2 * (μ {j}).toReal) := by
      have hdiv : L (k : ℝ) / L (j : ℝ) / ((k : ℝ) / (j : ℝ)) ^ 2 ≤
          P * δ ^ (-(5 / 2) : ℝ) := (div_le_iff₀ (sq_pos_of_pos hjk0)).mpr (by
        simpa only [mul_comm] using hLratio)
      gcongr
    _ = C * (μ {j}).toReal := by dsimp [C]; ring


lemma berger_increment_shift_cast {z : ℤ} (hz : -1 ≤ z) :
    (((z + 1).toNat : ℕ) : ℝ) = (z : ℝ) + 1 := by
  have hi : ((z + 1).toNat : ℤ) = z + 1 := Int.toNat_of_nonneg (by omega)
  exact_mod_cast hi

/-- Compact-ratio comparison transported to the increment law. -/
lemma berger_increment_mass_ratio_compact
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {base : ℕ → ℝ} (hbase : Tendsto base atTop atTop) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ z w : ℤ, base n ≤ (z : ℝ) →
      ((w : ℝ) + 1) / ((z : ℝ) + 1) ∈ Set.Icc a b →
      (incrementLaw μ {w}).toReal / (incrementLaw μ {z}).toReal <
        (a ^ 2)⁻¹ + η := by
  filter_upwards [berger_nat_mass_ratio_compact μ hμ ha hab hbase η hη,
    hbase.eventually_gt_atTop 0] with n hn hb z w hz hratio
  have hz0 : (0 : ℝ) ≤ z := hb.le.trans hz
  have hz1 : (0 : ℝ) < (z : ℝ) + 1 := by linarith
  have hw1 : (0 : ℝ) < (w : ℝ) + 1 := by
    have hh := (le_div_iff₀ hz1).mp hratio.1
    linarith [mul_pos ha hz1]
  have hz' : -1 ≤ z := by
    have hzℤ : (0 : ℤ) ≤ z := by exact_mod_cast hz0
    omega
  have hw' : -1 ≤ w := by exact_mod_cast (show (-1 : ℝ) ≤ w by linarith)
  let j := (z + 1).toNat
  let k := (w + 1).toNat
  have hjcast : (j : ℝ) = (z : ℝ) + 1 := berger_increment_shift_cast hz'
  have hkcast : (k : ℝ) = (w : ℝ) + 1 := berger_increment_shift_cast hw'
  have hjbase : base n ≤ (j : ℝ) := by rw [hjcast]; linarith
  have hjk : (k : ℝ) / (j : ℝ) ∈ Set.Icc a b := by
    rw [hjcast, hkcast]
    exact hratio
  have h := hn j k hjbase hjk
  dsimp [j, k] at h
  rw [berger_incrementLaw_singleton μ z hz',
    berger_incrementLaw_singleton μ w hw']
  exact h

/-- Potter comparison transported to the increment law. -/
lemma berger_increment_mass_potter
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ)
    {base : ℕ → ℝ} (hbase : Tendsto base atTop atTop)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ z w : ℤ,
      base n ≤ (z : ℝ) → δ * ((z : ℝ) + 1) ≤ (w : ℝ) + 1 →
      (incrementLaw μ {w}).toReal ≤ C * (incrementLaw μ {z}).toReal := by
  obtain ⟨C, hC, hCbound⟩ := berger_nat_mass_potter μ hμ hbase hδ hδ1
  refine ⟨C, hC, ?_⟩
  filter_upwards [hCbound, hbase.eventually_gt_atTop 0] with n hn hb z w hz hδw
  have hz0 : (0 : ℝ) ≤ z := hb.le.trans hz
  have hz' : -1 ≤ z := by
    have hzℤ : (0 : ℤ) ≤ z := by exact_mod_cast hz0
    omega
  have hw' : -1 ≤ w := by
    have hz1 : (0 : ℝ) ≤ (z : ℝ) + 1 := by linarith
    have hw1 : (0 : ℝ) ≤ (w : ℝ) + 1 :=
      (mul_nonneg hδ.le hz1).trans hδw
    exact_mod_cast (show (-1 : ℝ) ≤ w by linarith)
  let j := (z + 1).toNat
  let k := (w + 1).toNat
  have hjcast : (j : ℝ) = (z : ℝ) + 1 := berger_increment_shift_cast hz'
  have hkcast : (k : ℝ) = (w : ℝ) + 1 := berger_increment_shift_cast hw'
  have hjbase : base n ≤ (j : ℝ) := by rw [hjcast]; linarith
  have hjk : δ * (j : ℝ) ≤ (k : ℝ) := by rwa [hjcast, hkcast]
  have h := hn j k hjbase hjk
  dsimp [j, k] at h
  rwa [berger_incrementLaw_singleton μ z hz',
    berger_incrementLaw_singleton μ w hw']

end
end SubcriticalCauchy.Bienayme
