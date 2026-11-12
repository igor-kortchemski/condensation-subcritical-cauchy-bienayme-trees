module

public import SubcriticalCauchy.PaperRoute.BergerConcentration
public import Mathlib.MeasureTheory.Measure.Prod

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Auxiliary estimates for walks with a small maximum
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology BigOperators

namespace SubcriticalCauchy.Bienayme

/-- A product-measure bound from a bound on every vertical fiber and on the
projection to the first coordinate. -/
lemma smallMax_prod_toReal_le_of_left_fiber
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure α) (Q : Measure β) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {A : Set α} {E : Set (α × β)} (hA : MeasurableSet A) (hE : MeasurableSet E)
    (hEA : E ⊆ A ×ˢ Set.univ) {B F : ℝ} (hB : 0 ≤ B)
    (hfiber : ∀ x ∈ A, (Q (Prod.mk x ⁻¹' E)).toReal ≤ B)
    (hFA : (P A).toReal ≤ F) :
    ((P.prod Q) E).toReal ≤ B * F := by
  have hfiber' (x : α) : Q (Prod.mk x ⁻¹' E) ≤ A.indicator (fun _ => ENNReal.ofReal B) x := by
    by_cases hx : x ∈ A
    · simp only [Set.indicator_of_mem hx]
      exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hB).2 (hfiber x hx)
    · have hempty : Prod.mk x ⁻¹' E = ∅ := by
        ext y
        simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
        intro hxy
        exact hx (hEA hxy).1
      simp [Set.indicator_of_notMem hx, hempty]
  have hbound : (P.prod Q) E ≤ ENNReal.ofReal B * P A := by
    rw [Measure.prod_apply hE]
    calc
      (∫⁻ x, Q (Prod.mk x ⁻¹' E) ∂P)
          ≤ ∫⁻ x, A.indicator (fun _ => ENNReal.ofReal B) x ∂P :=
        lintegral_mono hfiber'
      _ = ENNReal.ofReal B * P A := by rw [lintegral_indicator hA, lintegral_const, Measure.restrict_apply_univ]
  calc
    ((P.prod Q) E).toReal ≤ (ENNReal.ofReal B * P A).toReal :=
      ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hbound
    _ = B * (P A).toReal := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB]
    _ ≤ B * F := mul_le_mul_of_nonneg_left hFA hB

/-- The corresponding bound from every horizontal fiber and the projection to
the second coordinate. -/
lemma smallMax_prod_toReal_le_of_right_fiber
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure α) (Q : Measure β) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {A : Set β} {E : Set (α × β)} (hA : MeasurableSet A) (hE : MeasurableSet E)
    (hEA : E ⊆ Set.univ ×ˢ A) {B F : ℝ} (hB : 0 ≤ B)
    (hfiber : ∀ y ∈ A, (P ((fun x => (x, y)) ⁻¹' E)).toReal ≤ B)
    (hFA : (Q A).toReal ≤ F) :
    ((P.prod Q) E).toReal ≤ B * F := by
  have hfiber' (y : β) : P ((fun x => (x, y)) ⁻¹' E) ≤
      A.indicator (fun _ => ENNReal.ofReal B) y := by
    by_cases hy : y ∈ A
    · simp only [Set.indicator_of_mem hy]
      exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hB).2 (hfiber y hy)
    · have hempty : (fun x => (x, y)) ⁻¹' E = ∅ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
        intro hxy
        exact hy (hEA hxy).2
      simp [Set.indicator_of_notMem hy, hempty]
  have hbound : (P.prod Q) E ≤ ENNReal.ofReal B * Q A := by
    rw [Measure.prod_apply_symm hE]
    calc
      (∫⁻ y, P ((fun x => (x, y)) ⁻¹' E) ∂Q)
          ≤ ∫⁻ y, A.indicator (fun _ => ENNReal.ofReal B) y ∂Q :=
        lintegral_mono hfiber'
      _ = ENNReal.ofReal B * Q A := by rw [lintegral_indicator hA, lintegral_const, Measure.restrict_apply_univ]
  calc
    ((P.prod Q) E).toReal ≤ (ENNReal.ofReal B * Q A).toReal :=
      ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hbound
    _ = B * (Q A).toReal := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB]
    _ ≤ B * F := mul_le_mul_of_nonneg_left hFA hB


/-- Split an exact-sum, bounded-jump event according to which block has a
large centered sum.  Each side is estimated by concentration on one block and
a Fuk--Nagaev-type bound on the other. -/
lemma smallMax_twoBlock_toReal_le
    {p q : ℕ} (P : Measure (Fin p → ℤ)) (Q : Measure (Fin q → ℤ))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (t : ℤ) (m z₀ y B F : ℝ)
    (htotal : 2 * z₀ ≤ (t : ℝ) - (p + q : ℕ) * m)
    (hconcP : ∀ s : ℤ, (P {x | ∑ i, x i = s}).toReal ≤ B)
    (hconcQ : ∀ s : ℤ, (Q {x | ∑ i, x i = s}).toReal ≤ B)
    (hlargeP : (P {x | z₀ ≤ (∑ i, (x i : ℝ)) - p * m ∧
      ∀ i, (x i : ℝ) ≤ y}).toReal ≤ F)
    (hlargeQ : (Q {x | z₀ ≤ (∑ i, (x i : ℝ)) - q * m ∧
      ∀ i, (x i : ℝ) ≤ y}).toReal ≤ F) :
    ((P.prod Q) {w | (∑ i, Fin.append (α := ℤ) w.1 w.2 i) = t ∧
      ∀ i, (Fin.append (α := ℤ) w.1 w.2 i : ℝ) ≤ y}).toReal ≤ 2 * B * F := by
  let E : Set ((Fin p → ℤ) × (Fin q → ℤ)) :=
    {w | (∑ i, Fin.append (α := ℤ) w.1 w.2 i) = t ∧ ∀ i, (Fin.append (α := ℤ) w.1 w.2 i : ℝ) ≤ y}
  let A₁ : Set (Fin p → ℤ) := {x | z₀ ≤ (∑ i, (x i : ℝ)) - p * m ∧
    ∀ i, (x i : ℝ) ≤ y}
  let A₂ : Set (Fin q → ℤ) := {x | z₀ ≤ (∑ i, (x i : ℝ)) - q * m ∧
    ∀ i, (x i : ℝ) ≤ y}
  let E₁ := E ∩ (A₁ ×ˢ Set.univ)
  let E₂ := E ∩ (Set.univ ×ˢ A₂)
  have hsum (w : (Fin p → ℤ) × (Fin q → ℤ)) :
      (∑ i, (Fin.append (α := ℤ) w.1 w.2 i : ℝ)) =
        (∑ i, (w.1 i : ℝ)) + (∑ i, (w.2 i : ℝ)) := by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  have hsmall₁ {w : (Fin p → ℤ) × (Fin q → ℤ)} (hw : w ∈ E) :
      ∀ i, (w.1 i : ℝ) ≤ y := by
    intro i
    simpa only [Fin.append_left] using hw.2 (Fin.castAdd q i)
  have hsmall₂ {w : (Fin p → ℤ) × (Fin q → ℤ)} (hw : w ∈ E) :
      ∀ i, (w.2 i : ℝ) ≤ y := by
    intro i
    simpa only [Fin.append_right] using hw.2 (Fin.natAdd p i)
  have hEsub : E ⊆ E₁ ∪ E₂ := by
    intro w hw
    by_cases h₁ : z₀ ≤ (∑ i, (w.1 i : ℝ)) - p * m
    · apply Or.inl
      refine ⟨hw, ⟨⟨h₁, hsmall₁ hw⟩, Set.mem_univ _⟩⟩
    · apply Or.inr
      refine ⟨hw, ⟨Set.mem_univ _, ⟨?_, hsmall₂ hw⟩⟩⟩
      show z₀ ≤ (∑ i, (w.2 i : ℝ)) - q * m
      have hsumint : (∑ i, (Fin.append (α := ℤ) w.1 w.2 i : ℝ)) = (t : ℝ) := by
        exact_mod_cast hw.1
      have h₁' : (∑ i, (w.1 i : ℝ)) - p * m < z₀ := lt_of_not_ge h₁
      rw [hsum] at hsumint
      norm_num only [Nat.cast_add] at htotal
      linarith
  have hE₁meas : MeasurableSet E₁ := (Set.to_countable _).measurableSet
  have hE₂meas : MeasurableSet E₂ := (Set.to_countable _).measurableSet
  have hA₁meas : MeasurableSet A₁ := (Set.to_countable _).measurableSet
  have hA₂meas : MeasurableSet A₂ := (Set.to_countable _).measurableSet
  have hB : 0 ≤ B := (ENNReal.toReal_nonneg.trans (hconcP 0))
  have hleft : ((P.prod Q) E₁).toReal ≤ B * F := by
    apply smallMax_prod_toReal_le_of_left_fiber P Q hA₁meas hE₁meas
      (by intro w hw; exact hw.2) hB
    · intro x hx
      have hsub : Prod.mk x ⁻¹' E₁ ⊆ {b | ∑ i, b i = t - ∑ i, x i} := by
        intro b hb
        have heq := hb.1.1
        simp only [Set.mem_ofPred_eq]
        rw [Fin.sum_univ_add] at heq
        simp only [Fin.append_left, Fin.append_right] at heq
        omega
      exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)).trans
        (hconcQ (t - ∑ i, x i))
    · exact hlargeP
  have hright : ((P.prod Q) E₂).toReal ≤ B * F := by
    apply smallMax_prod_toReal_le_of_right_fiber P Q hA₂meas hE₂meas
      (by intro w hw; exact hw.2) hB
    · intro b hb
      have hsub : (fun x => (x, b)) ⁻¹' E₂ ⊆ {x | ∑ i, x i = t - ∑ i, b i} := by
        intro x hx
        have heq := hx.1.1
        simp only [Set.mem_ofPred_eq]
        rw [Fin.sum_univ_add] at heq
        simp only [Fin.append_left, Fin.append_right] at heq
        omega
      exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)).trans
        (hconcP (t - ∑ i, b i))
    · exact hlargeQ
  calc
    ((P.prod Q) E).toReal ≤ ((P.prod Q) (E₁ ∪ E₂)).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hEsub)
    _ ≤ ((P.prod Q) E₁ + (P.prod Q) E₂).toReal :=
      ENNReal.toReal_mono (by finiteness) (measure_union_le _ _)
    _ = ((P.prod Q) E₁).toReal + ((P.prod Q) E₂).toReal := by
      rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    _ ≤ B * F + B * F := add_le_add hleft hright
    _ = 2 * B * F := by ring


/-- Appending independent finite integer vectors preserves the product law. -/
lemma smallMax_appendEquiv_measurePreserving (ν : Measure ℤ) [SigmaFinite ν]
    (p q : ℕ) :
    MeasurePreserving (Fin.appendEquiv p q)
      ((Measure.pi fun _ : Fin p => ν).prod (Measure.pi fun _ : Fin q => ν))
      (Measure.pi fun _ : Fin (p + q) => ν) := by
  let e₁ := (MeasurableEquiv.sumPiEquivProdPi
    (fun _ : Fin p ⊕ Fin q => ℤ)).symm
  let e₂ := MeasurableEquiv.piCongrLeft (fun _ : Fin (p + q) => ℤ) finSumFinEquiv
  have h₁ := measurePreserving_sumPiEquivProdPi_symm
    (fun _ : Fin p ⊕ Fin q => ν)
  have h₂ := measurePreserving_piCongrLeft (fun _ : Fin (p + q) => ν) finSumFinEquiv
  have hcomp := h₂.comp h₁
  convert hcomp using 1
  ext w i
  refine Fin.addCases (m := p) (n := q) (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.appendEquiv_apply, Fin.append_left, Function.comp_apply,
      MeasurableEquiv.coe_piCongrLeft,
      MeasurableEquiv.coe_sumPiEquivProdPi_symm]
    change w.1 j = (Equiv.piCongrLeft (fun _ => ℤ) finSumFinEquiv)
      ((Equiv.sumPiEquivProdPi fun _ => ℤ).symm w) (finSumFinEquiv (Sum.inl j))
    rw [Equiv.piCongrLeft_sumInl]
  · simp only [Fin.appendEquiv_apply, Fin.append_right, Function.comp_apply,
      MeasurableEquiv.coe_piCongrLeft,
      MeasurableEquiv.coe_sumPiEquivProdPi_symm]
    change w.2 j = (Equiv.piCongrLeft (fun _ => ℤ) finSumFinEquiv)
      ((Equiv.sumPiEquivProdPi fun _ => ℤ).symm w) (finSumFinEquiv (Sum.inr j))
    rw [Equiv.piCongrLeft_sumInr]


/-- The two-block estimate stated for a `Fin n` product, with `n = p + q`. -/
lemma smallMax_pi_toReal_le_of_add_eq (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {p q n : ℕ} (hpq : p + q = n) (t : ℤ) (m z₀ y B F : ℝ)
    (htotal : 2 * z₀ ≤ (t : ℝ) - n * m)
    (hconc : ∀ {j : ℕ} (_ : j = p ∨ j = q) (s : ℤ),
      ((Measure.pi fun _ : Fin j => ν) {x | ∑ i, x i = s}).toReal ≤ B)
    (hlarge : ∀ {j : ℕ} (_ : j = p ∨ j = q),
      ((Measure.pi fun _ : Fin j => ν) {x | z₀ ≤ (∑ i, (x i : ℝ)) - j * m ∧
        ∀ i, (x i : ℝ) ≤ y}).toReal ≤ F) :
    ((Measure.pi fun _ : Fin n => ν) {x | (∑ i, x i) = t ∧
      ∀ i, (x i : ℝ) ≤ y}).toReal ≤ 2 * B * F := by
  let e := finCongr hpq
  let g := MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℤ) e
  have hmp := (measurePreserving_piCongrLeft (fun _ : Fin n => ν) e).comp
    (smallMax_appendEquiv_measurePreserving ν p q)
  let E : Set (Fin n → ℤ) := {x | (∑ i, x i) = t ∧ ∀ i, (x i : ℝ) ≤ y}
  let E₀ : Set ((Fin p → ℤ) × (Fin q → ℤ)) :=
    {w | (∑ i, Fin.append (α := ℤ) w.1 w.2 i) = t ∧
      ∀ i, (Fin.append (α := ℤ) w.1 w.2 i : ℝ) ≤ y}
  have hpre : ((g : (Fin (p + q) → ℤ) → (Fin n → ℤ)) ∘ Fin.appendEquiv p q) ⁻¹' E = E₀ := by
    ext w
    have hsum : (∑ i : Fin n, Fin.append (α := ℤ) w.1 w.2 (e.symm i)) =
        ∑ i : Fin (p + q), Fin.append (α := ℤ) w.1 w.2 i := by
      simpa only [Function.comp_def] using
        Equiv.sum_comp e.symm (fun i => Fin.append (α := ℤ) w.1 w.2 i)
    simp only [Set.mem_preimage, g, E, E₀, Set.mem_ofPred_eq,
      MeasurableEquiv.coe_piCongrLeft, Function.comp_def]
    change ((∑ i : Fin n, Fin.append w.1 w.2 (e.symm i)) = t ∧
      (∀ i : Fin n, (Fin.append (α := ℤ) w.1 w.2 (e.symm i) : ℝ) ≤ y)) ↔ _
    rw [hsum]
    constructor
    · rintro ⟨ht, h⟩
      refine ⟨ht, fun i => ?_⟩
      simpa using h (e i)
    · rintro ⟨ht, h⟩
      refine ⟨ht, fun i => ?_⟩
      simpa using h (e.symm i)
  have hblock := smallMax_twoBlock_toReal_le
    (Measure.pi fun _ : Fin p => ν) (Measure.pi fun _ : Fin q => ν)
    t m z₀ y B F (by simpa [hpq] using htotal)
    (hconc (Or.inl rfl)) (hconc (Or.inr rfl)) (hlarge (Or.inl rfl)) (hlarge (Or.inr rfl))
  have hEmeas : MeasurableSet E := by
    dsimp [E]
    exact (Set.to_countable _).measurableSet
  have hmeasure := hmp.measure_preimage (s := E) hEmeas.nullMeasurableSet
  change ((Measure.pi fun _ : Fin n => ν) E).toReal ≤ 2 * B * F
  rw [← hmeasure]
  change (((Measure.pi fun _ : Fin p => ν).prod (Measure.pi fun _ : Fin q => ν))
    (((g : (Fin (p + q) → ℤ) → (Fin n → ℤ)) ∘ Fin.appendEquiv p q) ⁻¹' E)).toReal ≤ 2 * B * F
  rw [hpre]
  exact hblock


/-- Positive increment atoms are offspring atoms shifted by one. -/
lemma smallMax_incrementLaw_singleton (μ : Measure ℕ) {z : ℤ} (hz : 0 ≤ z) :
    incrementLaw μ {z} = μ {(z + 1).toNat} := by
  rw [incrementLaw, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  congr 1
  ext k
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  have hk : (0 : ℤ) ≤ z + 1 := by omega
  rw [← Int.toNat_of_nonneg hk]
  omega


/-- The local-mass lower bound in the variable `u = z / a`. -/
lemma smallMax_mass_lower {n a z u mass Lₐ D : ℝ}
    (hn : 0 < n) (_ha : 0 < a) (_hz : 0 < z) (hu : 0 < u)
    (hD : 0 < D) (_hLₐ : 0 < Lₐ) (_hzu : z = u * a)
    (hscale : a / 2 ≤ n * Lₐ)
    (hlocal : Lₐ ≤ D * u ^ (1 / 2 : ℝ) * z ^ 2 * mass) :
    a / (2 * D * u ^ (1 / 2 : ℝ) * z ^ 2) ≤ n * mass := by
  have hden : 0 < D * u ^ (1 / 2 : ℝ) * z ^ 2 := by positivity
  calc
    a / (2 * D * u ^ (1 / 2 : ℝ) * z ^ 2)
        ≤ (n * Lₐ) / (D * u ^ (1 / 2 : ℝ) * z ^ 2) := by
      apply (div_le_div_iff₀ (by positivity) hden).2
      nlinarith [mul_le_mul_of_nonneg_right hscale
        (show 0 ≤ D * u ^ (1 / 2 : ℝ) * z ^ 2 by positivity)]
    _ ≤ n * mass := by
      apply (div_le_iff₀ hden).2
      nlinarith [mul_le_mul_of_nonneg_left hlocal hn.le]

/-- If a nonnegative base is bounded below by a constant times `sqrt u`, its
negative eighth real power has polynomial decay of order four. -/
lemma smallMax_rpow_neg_eight_le {u b D : ℝ}
    (hu : 0 < u) (hD : 0 < D) (hb : D * u ^ (1 / 2 : ℝ) ≤ b) :
    b ^ (-8 : ℝ) ≤ D ^ (-8 : ℝ) * u ^ (-4 : ℝ) := by
  have hbase : 0 < D * u ^ (1 / 2 : ℝ) := by positivity
  calc
    b ^ (-8 : ℝ) ≤ (D * u ^ (1 / 2 : ℝ)) ^ (-8 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hbase hb (by norm_num)
    _ = D ^ (-8 : ℝ) * (u ^ (1 / 2 : ℝ)) ^ (-8 : ℝ) := by
      rw [Real.mul_rpow hD.le (Real.rpow_nonneg hu.le _)]
    _ = D ^ (-8 : ℝ) * u ^ (-4 : ℝ) := by
      rw [← Real.rpow_mul hu.le]
      norm_num

/-- Final algebraic comparison.  The expression on the right is a constant
multiple of `u ^ (-3/2)` times the one-big-jump mass. -/
lemma smallMax_final_comparison {F A n a z u mass D : ℝ}
    (_hn : 0 < n) (ha : 0 < a) (_hz : 0 < z) (hu : 0 < u)
    (hA : 0 < A) (hD : 0 < D) (hzu : z = u * a)
    (hF : F ≤ A / a * u ^ (-4 : ℝ))
    (hmass : a / (2 * D * u ^ (1 / 2 : ℝ) * z ^ 2) ≤ n * mass) :
    2 * F ≤ (4 * A * D) * u ^ (-(3 / 2) : ℝ) * (n * mass) := by
  have hid : u ^ (-4 : ℝ) * (u ^ (1 / 2 : ℝ) * u ^ 2) = u ^ (-(3 / 2) : ℝ) := by
    rw [← Real.rpow_two]
    rw [← mul_assoc, ← Real.rpow_add hu, ← Real.rpow_add hu]
    norm_num
  calc
    2 * F ≤ 2 * (A / a * u ^ (-4 : ℝ)) := mul_le_mul_of_nonneg_left hF (by norm_num)
    _ = (4 * A * D) * u ^ (-(3 / 2) : ℝ) *
        (a / (2 * D * u ^ (1 / 2 : ℝ) * z ^ 2)) := by
      rw [hzu]
      field_simp [ha.ne', hD.ne', hu.ne', (Real.rpow_pos_of_pos hu (1 / 2 : ℝ)).ne']
      nlinarith [hid]
    _ ≤ (4 * A * D) * u ^ (-(3 / 2) : ℝ) * (n * mass) := by
      apply mul_le_mul_of_nonneg_left hmass
      positivity

end SubcriticalCauchy.Bienayme
