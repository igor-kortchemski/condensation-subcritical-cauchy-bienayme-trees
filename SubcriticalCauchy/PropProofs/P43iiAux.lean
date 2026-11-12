module

public import SubcriticalCauchy.PropProofs.P43iiBlocks
public import SubcriticalCauchy.ExteriorTight
public import SubcriticalCauchy.BienaymeSurvivalRatio
public import SubcriticalCauchy.OffspringHypothesis

/-!
# Analytic and deterministic estimates for Proposition 4.3(ii)
-/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Topology BigOperators

namespace SubcriticalCauchy.Bienayme

noncomputable section
open BGW BGW.LocallyFinite

local instance p43iiAuxInst1 : MeasurableSpace (List ℤ) := ⊤
local instance p43iiAuxInst2 : MeasurableSingletonClass (List ℤ) := ⟨fun _ => trivial⟩

/-- One-step backwards shift of a vanishing height-tail product. -/
theorem survival_mul_pred_tendsto_zero (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm0 : 0 < offspringMean μ) (hm1 : offspringMean μ < 1) {j : ℕ → ℕ}
    (hj : Tendsto j atTop atTop)
    (hprod : Tendsto (fun n : ℕ => (n : ℝ) * (survival μ (j n)).toReal)
      atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (n : ℝ) * (survival μ (j n - 1)).toReal)
      atTop (𝓝 0) := by
  have hfin : offspringMean μ ≠ ∞ := ne_top_of_lt (hm1.trans ENNReal.one_lt_top)
  have hmR : 0 < (offspringMean μ).toReal := ENNReal.toReal_pos hm0.ne' hfin
  have hratio : Tendsto (fun n : ℕ =>
      (survival μ (j n - 1 + 1)).toReal / (survival μ (j n - 1)).toReal)
      atTop (𝓝 (offspringMean μ).toReal) :=
    by simpa only [Function.comp_def] using
      (survival_ratio_tendsto μ hm0 hm1).comp ((tendsto_sub_atTop_nat 1).comp hj)
  have hdiv := hprod.div hratio hmR.ne'
  simp only [zero_div] at hdiv
  apply hdiv.congr'
  filter_upwards [hj.eventually (eventually_gt_atTop (0 : ℕ))] with n hn
  simp only [Pi.div_apply, Nat.sub_add_cancel hn]
  rw [div_div_eq_mul_div]
  calc
    (n : ℝ) * (survival μ (j n)).toReal * (survival μ (j n - 1)).toReal /
        (survival μ (j n)).toReal =
      (survival μ (j n)).toReal *
        ((n : ℝ) * (survival μ (j n - 1)).toReal) / (survival μ (j n)).toReal := by ring
    _ = (n : ℝ) * (survival μ (j n - 1)).toReal :=
      mul_div_cancel_left₀ _ (survival_toReal_pos μ hm0 (j n)).ne' 

/-- Any fixed backwards shift preserves the vanishing height-tail product. -/
theorem survival_mul_sub_tendsto_zero (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm0 : 0 < offspringMean μ) (hm1 : offspringMean μ < 1) {j : ℕ → ℕ}
    (hj : Tendsto j atTop atTop) (K : ℕ)
    (hprod : Tendsto (fun n : ℕ => (n : ℝ) * (survival μ (j n)).toReal)
      atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (n : ℝ) * (survival μ (j n - K)).toReal)
      atTop (𝓝 0) := by
  induction K with
  | zero => simpa using hprod
  | succ K ih =>
      have hjK : Tendsto (fun n => j n - K) atTop atTop := by
        simpa only [Function.comp_def] using (tendsto_sub_atTop_nat K).comp hj
      have hp := survival_mul_pred_tendsto_zero μ hm0 hm1 hjK ih
      simpa only [Nat.sub_sub] using hp

/-- A nonnegative real sequence tends to zero if every positive error bound
holds eventually. -/
theorem tendsto_zero_of_nonneg_of_eventually_le {f : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n)
    (hbound : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, f n ≤ ε) :
    Tendsto f atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hbound (ε / 2) (half_pos hε))
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hf n)]
  exact lt_of_le_of_lt (hN n hn) (half_lt_self hε)


/-- Fixed-threshold upper bound, splitting the tree height into its exterior
and attached-forest contributions. -/
theorem conditioned_height_ge_real_le_errors
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ)
    {n K j : ℕ} (hn : n ≠ 0) (hsize : bienaymeLaw μ (sizeEvent n) ≠ 0)
    (hj : K + 2 ≤ j) :
    (conditioned μ n).real (finiteTreeEvent fun t => j ≤ height t) ≤
      (conditioned μ n).real (finiteTreeEvent fun t => K < exteriorSize t) +
      (forestLaw μ (n - 1) (forestBelow (n - 1) (j - K - 1))ᶜ).toReal +
      tvDist
        ((MaximumSwapLaw.bridgeCountsLaw μ n).map (fun ω => cyclicResidual (stepWord ω)))
        ((Measure.pi fun _ : Fin (n - 1) => incrementLaw μ).map List.ofFn) +
      (conditioned μ n).real (finiteTreeEvent fun t => ¬ uniqueWordMaximum t.increments) := by
  let _ : IsProbabilityMeasure (conditioned μ n) := conditioned_isProbability μ n hsize
  have hsub : finiteTreeEvent (fun t => j ≤ height t) ⊆
      finiteTreeEvent (fun t => K < exteriorSize t) ∪
        finiteTreeEvent (fun t => j - K - 1 ≤ attachedForestHeight t) := by
    rintro _ ⟨t, ht, rfl⟩
    by_cases he : K < exteriorSize t
    · exact Or.inl ⟨t, he, rfl⟩
    · refine Or.inr ⟨t, ?_, rfl⟩
      have hh := height_le_exteriorSize_add t
      dsimp only [Set.mem_ofPred_eq] at ht ⊢
      apply (Nat.sub_le_iff_le_add).mpr
      apply (Nat.sub_le_iff_le_add).mpr
      omega
  have hle := (measureReal_mono hsub (measure_ne_top (conditioned μ n) _)).trans
    (measureReal_union_le _ _)
  have hg : 0 < j - K - 1 := by omega
  have hb := conditioned_attachedForestHeight_real_le μ hμ.1 hn hsize hg
  have hf := (forest_height_bounds μ (n - 1) (j - K - 1)).1
  linarith

/-- The probability of height at least `h n` vanishes under the Proposition
4.3(ii) tail hypothesis. -/
theorem height_ge_real_tendsto_zero (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (h : ℕ → ℝ)
    (hh : Tendsto h atTop atTop)
    (hQ : Tendsto (fun n : ℕ => (n : ℝ) * (survival μ ⌈h n⌉₊).toReal) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (conditioned μ n
      (finiteTreeEvent fun t => h n ≤ (height t : ℝ))).toReal) atTop (𝓝 0) := by
  let j : ℕ → ℕ := fun n => ⌈h n⌉₊
  have hj : Tendsto j atTop atTop := tendsto_nat_ceil_atTop.comp hh
  have hm0 := offspringMean_pos_of_paper μ hμ.to_literal
  apply tendsto_zero_of_nonneg_of_eventually_le (fun _ => ENNReal.toReal_nonneg)
  intro ε hε
  let δ := ε / 4
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  obtain ⟨K, hK⟩ := exteriorSize_tight μ hμ δ hδ
  have hshift : Tendsto (fun n : ℕ =>
      (n : ℝ) * (survival μ (j n - K - 1)).toReal) atTop (𝓝 0) := by
    have hs := survival_mul_sub_tendsto_zero μ hm0 hμ.1 hj (K + 1) hQ
    simpa only [Nat.sub_sub] using hs
  have hgTop : Tendsto (fun n => j n - K - 1) atTop atTop := by
    simpa only [Nat.sub_sub, Function.comp_def] using
      (tendsto_sub_atTop_nat (K + 1)).comp hj
  have hQzero : Tendsto (fun n => (survival μ (j n - K - 1)).toReal) atTop (𝓝 0) :=
    (survival_toReal_tendsto_zero μ hμ.1).comp hgTop
  have hQpred : Tendsto (fun n : ℕ => ((n - 1 : ℕ) : ℝ) *
      (survival μ (j n - K - 1)).toReal) atTop (𝓝 0) := by
    have hc := hshift.sub hQzero
    simp only [sub_zero] at hc
    apply hc.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    rw [Nat.cast_sub hn]
    ring
  have htail : Tendsto (fun n : ℕ =>
      (forestLaw μ (n - 1) (forestBelow (n - 1) (j n - K - 1))ᶜ).toReal)
      atTop (𝓝 0) := by
    exact squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
      (Eventually.of_forall fun n => (forest_height_bounds μ (n - 1) (j n - K - 1)).1)
      hQpred
  have htv := cyclicResidual_bridge_tvDist μ hμ
  have htie := conditioned_nonunique_maximum_tendsto_zero μ hμ
  filter_upwards [hK, htail.eventually (Iio_mem_nhds hδ),
    htv.eventually (Iio_mem_nhds hδ), htie.eventually (Iio_mem_nhds hδ),
    eventually_gt_atTop (0 : ℕ), eventually_size_admissible μ hμ.to_literal,
    hj.eventually (eventually_ge_atTop (K + 2))] with n hKn htailn htvn htien hn hsize hjn
  have hb := conditioned_height_ge_real_le_errors μ hμ (Nat.ne_of_gt hn) hsize hjn
  have hsub : finiteTreeEvent (fun t => h n ≤ (height t : ℝ)) ⊆
      finiteTreeEvent (fun t => j n ≤ height t) := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨t, Nat.ceil_le.mpr ht, rfl⟩
  let _ : IsProbabilityMeasure (conditioned μ n) := conditioned_isProbability μ n hsize
  have hle := measureReal_mono hsub (measure_ne_top (conditioned μ n) _)
  have hle' : (conditioned μ n (finiteTreeEvent fun t => h n ≤ (height t : ℝ))).toReal ≤
      (conditioned μ n (finiteTreeEvent fun t => j n ≤ height t)).toReal := hle
  change (conditioned μ n).real (finiteTreeEvent fun t => h n ≤ (height t : ℝ)) ≤ ε
  change (conditioned μ n).real (finiteTreeEvent fun t => j n ≤ height t) ≤
    (conditioned μ n).real (finiteTreeEvent fun t => K < exteriorSize t) +
      (forestLaw μ (n - 1) (forestBelow (n - 1) (j n - K - 1))ᶜ).toReal +
      tvDist
        ((MaximumSwapLaw.bridgeCountsLaw μ n).map (fun ω => cyclicResidual (stepWord ω)))
        ((Measure.pi fun _ : Fin (n - 1) => incrementLaw μ).map List.ofFn) +
      (conditioned μ n).real (finiteTreeEvent fun t => ¬ uniqueWordMaximum t.increments) at hb
  dsimp only [Measure.real] at hKn ⊢
  have htotal : (conditioned μ n (finiteTreeEvent fun t => h n ≤ (height t : ℝ))).toReal ≤
      (conditioned μ n (finiteTreeEvent fun t => K < exteriorSize t)).toReal +
      (forestLaw μ (n - 1) (forestBelow (n - 1) (j n - K - 1))ᶜ).toReal +
      tvDist
        ((MaximumSwapLaw.bridgeCountsLaw μ n).map (fun ω => cyclicResidual (stepWord ω)))
        ((Measure.pi fun _ : Fin (n - 1) => incrementLaw μ).map List.ofFn) +
      (conditioned μ n (finiteTreeEvent fun t => ¬ uniqueWordMaximum t.increments)).toReal :=
    hle'.trans hb
  dsimp only [δ] at hKn htailn htvn htien
  linarith

end
end SubcriticalCauchy.Bienayme
