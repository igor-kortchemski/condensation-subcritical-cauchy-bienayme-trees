module

public import SubcriticalCauchy.PaperRoute.FinalProofTransfer
public import SubcriticalCauchy.IncrementTailAsymptotics
public import SubcriticalCauchy.LatticeWindow
public import Mathlib.MeasureTheory.Measure.TightNormed

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Analytic bridges for the paper route
-/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section

/-- Finite first moment gives the linearly scaled tail estimate used in AL's
maximum-tail hypothesis. -/
theorem final_nat_mul_incrementTail_tendsto_zero
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ < 1)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (δ * n)).toReal) atTop (𝓝 0) := by
  have hmfin : offspringMean μ ≠ ∞ := ne_top_of_lt hm
  have ha : Tendsto (fun n : ℕ => δ * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hδ
  have hmoment := incrementTailMoment_tendsto_zero μ hmfin ha
  have hprod : Tendsto (fun n : ℕ =>
      (δ * (n : ℝ)) * (incrementTail μ (δ * n)).toReal) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ hmoment
    · filter_upwards [ha.eventually_ge_atTop 0] with n hn
      exact mul_nonneg hn ENNReal.toReal_nonneg
    · exact Eventually.of_forall fun n => mul_incrementTail_le_moment μ hmfin _
  have hscaled := hprod.const_mul δ⁻¹
  simp only [mul_zero] at hscaled
  apply hscaled.congr'
  filter_upwards [] with n
  field_simp [hδ.ne']

/-- A real tail of the centered increment is controlled by the offspring
increment tail at any threshold lowered by the centering constant. -/
theorem final_centered_tail_le_incrementTail
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (t s : ℝ)
    (hs : s ≤ t - (1 - (offspringMean μ).toReal)) :
    (centeredIncrementLaw μ (Set.Ioi t)).toReal ≤ (incrementTail μ s).toReal := by
  rw [final_centeredIncrementLaw_eq_map, incrementTail]
  rw [Measure.map_apply (measurable_of_countable _) measurableSet_Ioi]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro k hk
  change t < (k : ℝ) - 1 + (1 - (offspringMean μ).toReal) at hk
  change s ≤ (k : ℝ) - 1
  linarith

/-- **B1.** AL's maximum-tail condition for the centered increment law with
linear thresholds and any scale `c n = o(n)`. -/
theorem final_hmax_linear
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ < 1)
    {ε : ℝ} (hε : 0 < ε) (c : ℕ → ℝ)
    (hc : Tendsto (fun n : ℕ => c n / (n : ℝ)) atTop (𝓝 0)) (A : ℝ)
    (hA : 0 < A) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      (centeredIncrementLaw μ (Set.Ioi (ε * n - A * c n))).toReal) atTop (𝓝 0) := by
  have hδ : 0 < ε / 4 := by positivity
  have htail := final_nat_mul_incrementTail_tendsto_zero μ hm hδ
  apply squeeze_zero' _ _ htail
  · exact Eventually.of_forall fun n => mul_nonneg (Nat.cast_nonneg n) ENNReal.toReal_nonneg
  · have hsmall : ∀ᶠ n : ℕ in atTop, c n / (n : ℝ) < ε / (4 * A) :=
      hc.eventually (Iio_mem_nhds (by positivity))
    filter_upwards [hsmall, eventually_gt_atTop (0 : ℕ),
      tendsto_natCast_atTop_atTop.eventually_ge_atTop
        (4 * (1 - (offspringMean μ).toReal) / ε)] with n hcn hn hγ
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hAc : A * c n ≤ ε * (n : ℝ) / 2 := by
      have hlt := (div_lt_iff₀ hnR).mp hcn
      have hmul := mul_lt_mul_of_pos_left hlt hA
      have hid : A * (ε / (4 * A) * (n : ℝ)) = ε * (n : ℝ) / 4 := by
        field_simp [hA.ne']
      nlinarith
    have hγ' : 1 - (offspringMean μ).toReal ≤ (ε / 4) * (n : ℝ) := by
      have hg := (div_le_iff₀ hε).mp hγ
      nlinarith
    have hthreshold : ε * (n : ℝ) / 2 ≤ ε * (n : ℝ) - A * c n := by linarith
    have hs : (ε / 4) * (n : ℝ) ≤
        (ε * (n : ℝ) - A * c n) - (1 - (offspringMean μ).toReal) := by linarith
    have htaille := final_centered_tail_le_incrementTail μ _ _ hs
    exact (mul_le_mul_of_nonneg_left htaille (Nat.cast_nonneg n))


/-- Positivity of the scale `n ℓ⋆(a n)` at positive indices. -/
theorem final_scale_pos {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hsum : Summable (fun k : ℕ => L k / (k : ℝ))) (a : ℕ → ℝ) :
    ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) * ellStarReal L (a n) := by
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact mul_pos (Nat.cast_pos.mpr hn) (ellStarReal_pos hpos hsum _)

/-- The scale normalized by `n` is exactly the integrated tail. -/
theorem final_scale_div_nat_tendsto_zero {L : ℝ → ℝ} {a : ℕ → ℝ}
    (hell : Tendsto (fun n : ℕ => ellStarReal L (a n)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ((n : ℝ) * ellStarReal L (a n)) / (n : ℝ))
      atTop (𝓝 0) := by
  apply hell.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  field_simp [hn0]

/-- **B3, ratio.** With `ℓ n = ε n` and `c n = n ℓ⋆(a n)`, the
ratio `ℓ n / c n` tends to infinity. -/
theorem final_linear_div_scale_tendsto_atTop {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hsum : Summable (fun k : ℕ => L k / (k : ℝ))) {a : ℕ → ℝ}
    (hell : Tendsto (fun n : ℕ => ellStarReal L (a n)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (ε * (n : ℝ)) / ((n : ℝ) * ellStarReal L (a n)))
      atTop atTop := by
  have hp : Tendsto (fun n : ℕ => ellStarReal L (a n)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hell, Eventually.of_forall fun n => ellStarReal_pos hpos hsum _⟩
  have hinv := tendsto_inv_nhdsGT_zero.comp hp
  have hmul := hinv.const_mul_atTop hε
  apply hmul.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  have he0 : ellStarReal L (a n) ≠ 0 := (ellStarReal_pos hpos hsum _).ne'
  simp only [Function.comp_apply]
  field_simp [hn0, he0]

/-- **B3, scale at infinity.** If `a n → ∞`, `a n / c n → 0`, and
`c n` is eventually positive, then `c n → ∞`. -/
theorem final_scale_tendsto_atTop {a c : ℕ → ℝ}
    (ha : Tendsto a atTop atTop)
    (hac : Tendsto (fun n : ℕ => a n / c n) atTop (𝓝 0))
    (hc : ∀ᶠ n : ℕ in atTop, 0 < c n) : Tendsto c atTop atTop := by
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < a n / c n := by
    filter_upwards [ha.eventually_gt_atTop 0, hc] with n han hcn
    exact div_pos han hcn
  have hp : Tendsto (fun n : ℕ => a n / c n) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hac, hpos⟩
  have hinv := tendsto_inv_nhdsGT_zero.comp hp
  have hprod := ha.atTop_mul_atTop₀ hinv
  apply hprod.congr'
  filter_upwards [hpos] with n hn
  have h0 : a n / c n ≠ 0 := hn.ne'
  have ha0 : a n ≠ 0 := by
    intro ha0
    apply hn.ne'
    simp [ha0]
  simp only [Function.comp_apply]
  field_simp [h0, ha0]


/-- A finite real measure has vanishing mass outside large symmetric intervals. -/
theorem final_measure_abs_tail_tendsto_zero (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {c : ℕ → ℝ} (hc : Tendsto c atTop atTop) :
    Tendsto (fun n : ℕ => (ν {x | c n < |x|}).toReal) atTop (𝓝 0) := by
  have ht : Tendsto (fun r : ℝ => ν {x | r < |x|}) atTop (𝓝 0) := by
    have h := tendsto_measure_norm_gt_of_isTightMeasureSet
      (S := ({ν} : Set (Measure ℝ))) isTightMeasureSet_singleton
    simpa [Real.norm_eq_abs] using h
  exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (ht.comp hc)

/-- **B2, successor form.** Tightness of the full sum and `c n → ∞`
imply tightness of the sum obtained by deleting the last coordinate. -/
theorem final_predecessor_tight_succ
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (c : ℕ → ℝ)
    (hc : Tendsto c atTop atTop)
    (hfull : ∀ τ > 0, ∃ K : ℝ, ∀ᶠ m : ℕ in atTop,
      ((Measure.pi fun _ : Fin (m + 1) => ν)
        {y | K * c (m + 1) < |∑ i, y i|}).toReal ≤ τ) :
    ∀ τ > 0, ∃ A : ℝ, ∀ᶠ m : ℕ in atTop,
      ((Measure.pi fun _ : Fin m => ν)
        {y | A * c (m + 1) < |∑ i, y i|}).toReal ≤ τ := by
  intro τ hτ
  obtain ⟨K, hK⟩ := hfull (τ / 2) (by positivity)
  refine ⟨K + 1, ?_⟩
  have htail := (final_measure_abs_tail_tendsto_zero ν hc).comp (tendsto_add_atTop_nat 1)
  filter_upwards [hK, htail.eventually (Iio_mem_nhds (show 0 < τ / 2 by positivity)),
    Eventually.of_forall (fun m => show (0 : ℝ) ≤ τ / 2 by positivity)] with m hm hmt hτ0
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)
  let P : Measure (Fin (m + 1) → ℝ) := Measure.pi fun _ => ν
  let M : Measure (ℝ × (Fin m → ℝ)) := ν.prod (Measure.pi fun _ => ν)
  have hMP : P.map e = M :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => ν) (Fin.last m)).map_eq
  let E : Set (Fin m → ℝ) := {y | (K + 1) * c (m + 1) < |∑ i, y i|}
  let H : Set (Fin (m + 1) → ℝ) := {y | K * c (m + 1) < |∑ i, y i|}
  let J : Set (Fin (m + 1) → ℝ) := {y | c (m + 1) < |y (Fin.last m)|}
  have hE : MeasurableSet E := by
    dsimp only [E]
    apply measurableSet_lt <;> fun_prop
  have hH : MeasurableSet H := by
    dsimp only [H]
    apply measurableSet_lt <;> fun_prop
  have hJ : MeasurableSet J := by
    dsimp only [J]
    apply measurableSet_lt <;> fun_prop
  have hsubset : e ⁻¹' (Prod.snd ⁻¹' E) ⊆ H ∪ J := by
    intro y hy
    by_cases hyJ : y ∈ J
    · exact Set.mem_union_right _ hyJ
    · apply Set.mem_union_left
      change K * c (m + 1) < |∑ i, y i|
      change (K + 1) * c (m + 1) < |∑ i, (e y).2 i| at hy
      have hlast : |y (Fin.last m)| ≤ c (m + 1) := by
        exact le_of_not_gt hyJ
      have hsum : (∑ i, y i) = (∑ i, (e y).2 i) + (e y).1 := by
        rw [Fin.sum_univ_castSucc]
        simp [e, Fin.init]
      have he1 : (e y).1 = y (Fin.last m) := by simp [e]
      have htri : |(∑ i, (e y).2 i)| ≤ |∑ i, y i| + |y (Fin.last m)| := by
        rw [hsum, he1]
        simpa only [add_sub_cancel_right] using
          abs_sub ((∑ i, (e y).2 i) + y (Fin.last m)) (y (Fin.last m))
      nlinarith
  have hmass : (Measure.pi fun _ : Fin m => ν) E ≤ P H + P J := by
    calc
      (Measure.pi fun _ : Fin m => ν) E = (M.map Prod.snd) E := by
        rw [Measure.map_snd_prod, measure_univ, one_smul]
      _ = M (Prod.snd ⁻¹' E) := Measure.map_apply measurable_snd hE
      _ = P (e ⁻¹' (Prod.snd ⁻¹' E)) := by
        rw [← hMP, Measure.map_apply e.measurable (measurable_snd hE)]
      _ ≤ P (H ∪ J) := measure_mono hsubset
      _ ≤ P H + P J := measure_union_le _ _
  have hsingle : P J = ν {x | c (m + 1) < |x|} := by
    let T : Set ℝ := {x | c (m + 1) < |x|}
    have hT : MeasurableSet T := by measurability
    calc
      P J = M (Prod.fst ⁻¹' T) := by
        rw [← hMP, Measure.map_apply e.measurable (measurable_fst hT)]
        rfl
      _ = (M.map Prod.fst) T := (Measure.map_apply measurable_fst hT).symm
      _ = ν T := by rw [Measure.map_fst_prod, measure_univ, one_smul]
  change ((Measure.pi fun _ : Fin m => ν) E).toReal ≤ τ
  calc
    ((Measure.pi fun _ : Fin m => ν) E).toReal ≤ (P H + P J).toReal :=
      ENNReal.toReal_mono (by finiteness) hmass
    _ = (P H).toReal + (P J).toReal := ENNReal.toReal_add (by finiteness) (by finiteness)
    _ = (P H).toReal + (ν {x | c (m + 1) < |x|}).toReal := by rw [hsingle]
    _ ≤ τ := by
      change (P H).toReal ≤ τ / 2 at hm
      change (ν {x | c (m + 1) < |x|}).toReal < τ / 2 at hmt
      linarith


/-- **B2, AL indexing.** The same predecessor-tightness statement with AL's
`Fin n` and `Fin (n - 1)` indexing. -/
theorem final_predecessor_tight
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (c : ℕ → ℝ)
    (hc : Tendsto c atTop atTop)
    (hfull : ∀ τ > 0, ∃ K : ℝ, ∀ᶠ n : ℕ in atTop,
      ((Measure.pi fun _ : Fin n => ν)
        {y | K * c n < |∑ i, y i|}).toReal ≤ τ) :
    ∀ τ > 0, ∃ A : ℝ, ∀ᶠ n : ℕ in atTop,
      ((Measure.pi fun _ : Fin (n - 1) => ν)
        {y | A * c n < |∑ i, y i|}).toReal ≤ τ := by
  have hfullsucc : ∀ τ > 0, ∃ K : ℝ, ∀ᶠ m : ℕ in atTop,
      ((Measure.pi fun _ : Fin (m + 1) => ν)
        {y | K * c (m + 1) < |∑ i, y i|}).toReal ≤ τ := by
    intro τ hτ
    obtain ⟨K, hK⟩ := hfull τ hτ
    refine ⟨K, ?_⟩
    have hK1 := (tendsto_add_atTop_nat 1).eventually hK
    simpa only [Function.comp_def, Nat.succ_eq_add_one] using hK1
  have hs := final_predecessor_tight_succ ν c hc hfullsucc
  intro τ hτ
  obtain ⟨A, hA⟩ := hs τ hτ
  refine ⟨A, ?_⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 hA
  filter_upwards [eventually_ge_atTop (N + 1)] with n hn
  cases n with
  | zero => omega
  | succ m =>
    have hm : N ≤ m := by omega
    exact hN m hm

end
end SubcriticalCauchy.Bienayme
