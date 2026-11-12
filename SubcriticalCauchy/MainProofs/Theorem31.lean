module

public import SubcriticalCauchy.FiniteTreeEvent
public import SubcriticalCauchy.MeasurableHypothesis
public import SubcriticalCauchy.EndpointLocal
public import SubcriticalCauchy.NoLargeJump
public import SubcriticalCauchy.DeletedMaximumDensity
public import SubcriticalCauchy.TotalVariationTypical
public import SubcriticalCauchy.SlowVariationRounding

/-!
# Proof helpers for the frozen statement Theorem31

Owned helper module for the registered hole of Theorem31. It is imported by the
frozen statement file, which must not change except inside its holes; add
the proof and any further imports here.
-/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Topology BigOperators

namespace SubcriticalCauchy.Bienayme

noncomputable section

private theorem localModel_floor_mul_div_tendsto_one
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L) {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun n : ℕ => L ⌊γ * n⌋₊ / L n) atTop (𝓝 1) := by
  have hγn : Tendsto (fun n : ℕ => γ * (n : ℝ)) atTop atTop := by
    simpa only [mul_comm] using tendsto_natCast_atTop_atTop.atTop_mul_const hγ
  have hfloor := (localModel_floor_div_tendsto_one hpos hL hsv).comp hγn
  have hscaled := (hsv γ hγ).comp tendsto_natCast_atTop_atTop
  have h := hfloor.mul hscaled
  simp only [Function.comp_def, one_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ), hγn.eventually_gt_atTop 0] with n hn hγn0
  have hLn : L n ≠ 0 := (hpos _ (by exact_mod_cast hn)).ne'
  have hLγn : L (γ * n) ≠ 0 := (hpos _ hγn0).ne'
  field_simp [hLn, hLγn]

private theorem localModel_div_nat_floor_mass_tendsto
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsSubcriticalCauchyOffspring μ)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1)) {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun n : ℕ =>
      (L n / n) / (n * (μ {⌊γ * n⌋₊}).toReal)) atTop (𝓝 (γ ^ 2)) := by
  let k : ℕ → ℕ := fun n => ⌊γ * (n : ℝ)⌋₊
  have hγn : Tendsto (fun n : ℕ => γ * (n : ℝ)) atTop atTop := by
    simpa only [mul_comm] using tendsto_natCast_atTop_atTop.atTop_mul_const hγ
  have hk : Tendsto k atTop atTop := tendsto_nat_floor_atTop.comp hγn
  have hLratio : Tendsto (fun n : ℕ => L (k n) / L n) atTop (𝓝 1) := by
    exact localModel_floor_mul_div_tendsto_one hpos hL hsv hγ
  have hkdiv : Tendsto (fun n : ℕ => (k n : ℝ) / n) atTop (𝓝 γ) := by
    have hfloor := (tendsto_nat_floor_div_atTop (R := ℝ)).comp hγn
    have h := hfloor.mul_const γ
    simp only [one_mul] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    dsimp [k]
    field_simp [hγ.ne', hnR.ne']
  have hmass : Tendsto (fun n : ℕ =>
      (μ {k n}).toReal / (L n / (n : ℝ) ^ 2)) atTop (𝓝 (1 / γ ^ 2)) := by
    have h := ((hlocal.comp hk).mul hLratio).mul
      ((tendsto_const_nhds (x := (1 : ℝ))).div (hkdiv.pow 2)
        (pow_ne_zero 2 hγ.ne'))
    simp only [one_mul] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ), hk.eventually_gt_atTop 0] with n hn hkn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hkR : (0 : ℝ) < (k n : ℝ) := by exact_mod_cast hkn
    have hLn : L n ≠ 0 := (hpos _ hnR).ne'
    have hLk : L (k n) ≠ 0 := (hpos _ hkR).ne'
    change (μ {k n}).toReal / (L (k n) / (k n : ℝ) ^ 2) *
      (L (k n) / L n) * (1 / ((k n : ℝ) / n) ^ 2) =
        (μ {k n}).toReal / (L n / (n : ℝ) ^ 2)
    field_simp [hγ.ne', hnR.ne', hkR.ne', hLn, hLk]
  have h := (tendsto_const_nhds (x := (1 : ℝ))).div hmass
    (one_div_ne_zero (pow_ne_zero 2 hγ.ne'))
  simp only [one_div_div, div_one] at h
  change Tendsto (fun n : ℕ => (L n / n) / (n * (μ {k n}).toReal))
    atTop (𝓝 (γ ^ 2))
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ), hk.eventually_gt_atTop 0,
    hk.eventually (eventually_mass_pos μ hμ)] with n hn hkn hq
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkR : (0 : ℝ) < (k n : ℝ) := by exact_mod_cast hkn
  have hLn : L n ≠ 0 := (hpos _ hnR).ne'
  have hLk : L (k n) ≠ 0 := (hpos _ hkR).ne'
  have hqR : (μ {k n}).toReal ≠ 0 :=
    (ENNReal.toReal_pos hq.ne' (measure_ne_top _ _)).ne'
  change 1 / ((μ {k n}).toReal / (L n / (n : ℝ) ^ 2)) =
    (L n / n) / (n * (μ {k n}).toReal)
  field_simp [hγ.ne', hnR.ne', hkR.ne', hLn, hLk, hqR]


/-- The iid increment law is the coordinatewise pushforward of the iid count law. -/
private theorem pi_incrementLaw_eq_map_r31 (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (k : ℕ) :
    (Measure.pi fun _ : Fin k => incrementLaw μ) =
      (Measure.pi fun _ : Fin k => μ).map (fun z i => (z i : ℤ) - 1) := by
  symm
  simpa only [incrementLaw] using
    (Measure.pi_map_pi (μ := fun _ : Fin k => μ)
      (f := fun _ : Fin k => fun z : ℕ => (z : ℤ) - 1)
      (fun _ => (measurable_of_countable _).aemeasurable))

private def residualCounts {k : ℕ} (x : Fin k → ℤ) : Fin k → ℕ :=
  fun i => (x i + 1).toNat

private def endpointDensity (μ : Measure ℕ) (n : ℕ) (x : Fin (n - 1) → ℤ) : ℝ :=
  (n : ℝ) * (μ {n - 1 - ∑ i, residualCounts x i}).toReal /
    ((Measure.pi fun _ : Fin n => μ) (BGW.countBridges n)).toReal

private theorem deletedIncrements_law_real_atom (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {n : ℕ} (z : Fin (n - 1) → ℕ) (hz : ∑ i, z i < n - 1)
    (hmax : ∀ i, z i < n - 1 - ∑ i, z i)
    (hZ : 0 < ((Measure.pi fun _ : Fin n => μ) (BGW.countBridges n)).toReal) :
    (((MaximumSwapLaw.bridgeCountsLaw μ n).map (deletedIncrements n))
        {fun i => (z i : ℤ) - 1}).toReal =
      endpointDensity μ n (fun i => (z i : ℤ) - 1) *
        ((Measure.pi fun _ : Fin (n - 1) => incrementLaw μ)
          {fun i => (z i : ℤ) - 1}).toReal := by
  rw [deletedIncrements_law_atom μ z hz hmax, pi_incrementLaw_atom]
  simp only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_prod, endpointDensity, residualCounts, sub_add_cancel,
    Int.toNat_natCast]
  have hZ0 : ((Measure.pi fun _ : Fin n => μ) (BGW.countBridges n)).toReal ≠ 0 := hZ.ne'
  field_simp [hZ0]

/-- The bridge endpoint mass is asymptotic to `n` times the offspring mass at
`⌊(1 - m)n⌋₊`. -/
theorem endpoint_bridge_mass_div_tendsto_one
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsSubcriticalCauchyOffspring μ)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1)) :
    Tendsto (fun n : ℕ =>
      ((Measure.pi fun _ : Fin n => μ) (BGW.countBridges n)).toReal /
        (n * (μ {⌊(1 - (offspringMean μ).toReal) * n⌋₊}).toReal))
      atTop (𝓝 1) := by
  have hm : offspringMean μ < 1 := hμ.1
  have hmfin : offspringMean μ ≠ ∞ := ne_top_of_lt (hm.trans ENNReal.one_lt_top)
  have hm1 : (offspringMean μ).toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hmfin ENNReal.one_ne_top).mpr hm
  let γ : ℝ := 1 - (offspringMean μ).toReal
  let c : ℝ := γ / 64
  have hγ : 0 < γ := sub_pos.mpr hm1
  have hc : 0 < c := div_pos hγ (by norm_num)
  have hcγ : c < γ := by dsimp [c]; linarith
  have hcγle : c ≤ γ / 64 := le_rfl
  have hγn : Tendsto (fun n : ℕ => γ * (n : ℝ)) atTop atTop := by
    simpa only [mul_comm] using tendsto_natCast_atTop_atTop.atTop_mul_const hγ
  have hk : Tendsto (fun n : ℕ => ⌊γ * (n : ℝ)⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp hγn
  have hq : ∀ᶠ n : ℕ in atTop, 0 < μ {⌊γ * (n : ℝ)⌋₊} :=
    hk.eventually (eventually_mass_pos μ hμ)
  have hscale := localModel_div_nat_floor_mass_tendsto μ hμ hpos hL hsv hlocal hγ
  have hnl := endpoint_no_large_jump μ hm hpos hL hsv hlocal c hc hcγle
  have hno : Tendsto (fun n : ℕ =>
      ((Measure.pi fun _ : Fin n => μ)
        {ω | ∑ i, ω i = n - 1 ∧ ∀ i, (ω i : ℝ) ≤ c * n}).toReal /
        (n * (μ {⌊γ * n⌋₊}).toReal)) atTop (𝓝 0) := by
    have h := hnl.mul hscale
    simp only [zero_mul] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ), hq] with n hn hqn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hLn : L n ≠ 0 := (hpos _ hnR).ne'
    have hqR : (μ {⌊γ * (n : ℝ)⌋₊}).toReal ≠ 0 :=
      (ENNReal.toReal_pos hqn.ne' (measure_ne_top _ _)).ne'
    field_simp [hnR.ne', hLn, hqR]
  change Tendsto (fun n : ℕ =>
      ((Measure.pi fun _ : Fin n => μ) (BGW.countBridges n)).toReal /
        (n * (μ {⌊γ * n⌋₊}).toReal)) atTop (𝓝 1)
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    have hτ : 0 < (1 - a) / 2 := div_pos (sub_pos.mpr ha) (by norm_num)
    filter_upwards [endpoint_lower_bound μ hm hpos hL hsv hlocal ((1 - a) / 2) hτ,
      hq, eventually_gt_atTop (0 : ℕ)] with n hlower hqn hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hqR : 0 < (μ {⌊γ * (n : ℝ)⌋₊}).toReal :=
      ENNReal.toReal_pos hqn.ne' (measure_ne_top _ _)
    have hnq : 0 < (n : ℝ) * (μ {⌊γ * (n : ℝ)⌋₊}).toReal := mul_pos hnR hqR
    have hl : (1 - (1 - a) / 2) ≤
        ((Measure.pi fun _ : Fin n => μ) (BGW.countBridges n)).toReal /
          (n * (μ {⌊γ * (n : ℝ)⌋₊}).toReal) := by
      apply (le_div_iff₀ hnq).2
      simpa only [mul_assoc] using hlower
    exact (by linarith : a < 1 - (1 - a) / 2).trans_le hl
  · intro b hb
    let τ : ℝ := (b - 1) / 3
    have hτ : 0 < τ := div_pos (sub_pos.mpr hb) (by norm_num)
    have hbig := endpoint_bigJump_upper_bound μ hm hpos hL hsv hlocal hc hcγ τ hτ
    have hnlt := hno.eventually (gt_mem_nhds hτ)
    filter_upwards [hbig, hnlt, hq, eventually_gt_atTop (0 : ℕ)] with n hupper hn hqn hnpos
    let A : Set (Fin n → ℕ) :=
      {ω | ∑ i, ω i = n - 1 ∧ ∃ i, c * n < (ω i : ℝ)}
    let N : Set (Fin n → ℕ) :=
      {ω | ∑ i, ω i = n - 1 ∧ ∀ i, (ω i : ℝ) ≤ c * n}
    change ((Measure.pi fun _ : Fin n => μ) A).toReal ≤
      (1 + τ) * n * (μ {⌊γ * (n : ℝ)⌋₊}).toReal at hupper
    change ((Measure.pi fun _ : Fin n => μ) N).toReal /
      (n * (μ {⌊γ * (n : ℝ)⌋₊}).toReal) < τ at hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hqR : 0 < (μ {⌊γ * (n : ℝ)⌋₊}).toReal :=
      ENNReal.toReal_pos hqn.ne' (measure_ne_top _ _)
    have hnq : 0 < (n : ℝ) * (μ {⌊γ * (n : ℝ)⌋₊}).toReal := mul_pos hnR hqR
    have hsub : BGW.countBridges n ⊆ A ∪ N := by
      intro ω hω
      change (∑ i, ω i) + 1 = n at hω
      have hsum : ∑ i, ω i = n - 1 := by omega
      by_cases hA : ∃ i, c * n < (ω i : ℝ)
      · exact Or.inl ⟨hsum, hA⟩
      · refine Or.inr ⟨hsum, ?_⟩
        exact fun i => le_of_not_gt (fun hi => hA ⟨i, hi⟩)
    have hZ : ((Measure.pi fun _ : Fin n => μ) (BGW.countBridges n)).toReal ≤
        ((Measure.pi fun _ : Fin n => μ) A).toReal +
          ((Measure.pi fun _ : Fin n => μ) N).toReal := by
      calc
        _ ≤ ((Measure.pi fun _ : Fin n => μ) (A ∪ N)).toReal :=
          ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
        _ ≤ _ := measureReal_union_le A N
    have hAdiv : ((Measure.pi fun _ : Fin n => μ) A).toReal /
        (n * (μ {⌊γ * (n : ℝ)⌋₊}).toReal) ≤ 1 + τ := by
      calc
        _ ≤ ((1 + τ) * n * (μ {⌊γ * (n : ℝ)⌋₊}).toReal) /
            (n * (μ {⌊γ * (n : ℝ)⌋₊}).toReal) :=
          div_le_div_of_nonneg_right hupper hnq.le
        _ = 1 + τ := by
          have hqR' : (μ {⌊(n : ℝ) * γ⌋₊}).toReal ≠ 0 := by
            simpa only [mul_comm] using hqR.ne'
          field_simp [hnq.ne', hqR.ne', hnR.ne', hqR']
    have hsplit : ((Measure.pi fun _ : Fin n => μ) (BGW.countBridges n)).toReal /
        (n * (μ {⌊γ * (n : ℝ)⌋₊}).toReal) ≤
          ((Measure.pi fun _ : Fin n => μ) A).toReal /
            (n * (μ {⌊γ * (n : ℝ)⌋₊}).toReal) +
          ((Measure.pi fun _ : Fin n => μ) N).toReal /
            (n * (μ {⌊γ * (n : ℝ)⌋₊}).toReal) := by
      calc
        _ ≤ (((Measure.pi fun _ : Fin n => μ) A).toReal +
            ((Measure.pi fun _ : Fin n => μ) N).toReal) /
              (n * (μ {⌊γ * (n : ℝ)⌋₊}).toReal) :=
          div_le_div_of_nonneg_right hZ hnq.le
        _ = _ := add_div _ _ _
    dsimp only [τ] at hn hAdiv ⊢
    linarith


/-- Assembly form of Theorem 3.1. -/
theorem deleted_maximum_tvDist (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) :
    Tendsto (fun n : ℕ => tvDist ((MaximumSwapLaw.bridgeCountsLaw μ n).map (deletedIncrements n))
        (Measure.pi fun _ : Fin (n - 1) => incrementLaw μ))
      atTop (𝓝 0) := by
  obtain ⟨hm, L, hpos, hsv, hL, hlocal⟩ := hμ
  have hlit : IsSubcriticalCauchyOffspring μ :=
    ⟨hm, L, hpos, hsv, hlocal⟩
  have hmfin : offspringMean μ ≠ ∞ := ne_top_of_lt (hm.trans ENNReal.one_lt_top)
  have hm1 : (offspringMean μ).toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hmfin ENNReal.one_ne_top).mpr hm
  have hγ : 0 < 1 - (offspringMean μ).toReal := sub_pos.mpr hm1
  obtain ⟨h, hh, hη, hG, hgood⟩ :=
    endpoint_typical_residual_set μ hm hpos hL hsv hlocal
  have hratio := endpoint_bridge_mass_div_tendsto_one μ hlit hpos hL hsv hlocal
  have hfrac : Tendsto (fun n : ℕ =>
      (n * (μ {⌊(1 - (offspringMean μ).toReal) * n⌋₊}).toReal) /
        ((Measure.pi fun _ : Fin n => μ) (BGW.countBridges n)).toReal)
      atTop (𝓝 1) := by
    simpa only [inv_div, inv_one] using hratio.inv₀ one_ne_zero
  let D : (n : ℕ) → Measure (Fin (n - 1) → ℤ) := fun n =>
    (MaximumSwapLaw.bridgeCountsLaw μ n).map (deletedIncrements n)
  let P : (n : ℕ) → Measure (Fin (n - 1) → ℤ) := fun n =>
    Measure.pi fun _ : Fin (n - 1) => incrementLaw μ
  let G : (n : ℕ) → Set (Fin (n - 1) → ℤ) := fun n =>
    (fun z : Fin (n - 1) → ℕ => fun i => (z i : ℤ) - 1) ''
      endpointResidualSet μ h n
  have hcastinj (k : ℕ) :
      Function.Injective (fun z : Fin k → ℕ => fun i => (z i : ℤ) - 1) := by
    intro z w hzw
    funext i
    have hi := congrFun hzw i
    dsimp only at hi
    have heq : (z i : ℤ) = (w i : ℤ) := by linarith
    exact_mod_cast heq
  have hGreal : Tendsto (fun n =>
      ((Measure.pi fun _ : Fin (n - 1) => μ) (endpointResidualSet μ h n)).toReal)
      atTop (𝓝 1) := by
    simpa only [Function.comp_def, ENNReal.toReal_one] using
      (ENNReal.tendsto_toReal (a := (1 : ℝ≥0∞)) (by simp)).comp hG
  have hPG : Tendsto (fun n => (P n).real (G n)) atTop (𝓝 1) := by
    apply hGreal.congr'
    filter_upwards [] with n
    dsimp only [P, G]
    rw [pi_incrementLaw_eq_map_r31]
    change _ = (((Measure.pi fun _ : Fin (n - 1) => μ).map
      (fun z i => (z i : ℤ) - 1))
        ((fun z : Fin (n - 1) → ℕ => fun i => (z i : ℤ) - 1) ''
          endpointResidualSet μ h n)).toReal
    rw [Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet,
      Set.preimage_image_eq _ (hcastinj _)]
  have hGc : Tendsto (fun n => (P n).real (G n)ᶜ) atTop (𝓝 0) := by
    have ht := (tendsto_const_nhds (x := (1 : ℝ))).sub hPG
    simp only [sub_self] at ht
    apply ht.congr'
    filter_upwards [] with n
    let _ : IsProbabilityMeasure (P n) := by
      dsimp only [P]
      let _ : IsProbabilityMeasure (incrementLaw μ) := by
        unfold incrementLaw
        infer_instance
      infer_instance
    rw [measureReal_compl (Set.to_countable _).measurableSet]
    simp
  change Tendsto (fun n => tvDist (D n) (P n)) atTop (𝓝 0)
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    exact Eventually.of_forall fun n => by
      have := tvDist_nonneg (μ := D n) (ν := P n)
      linarith
  · intro b hb
    let δ : ℝ := b / 8
    let τ : ℝ := min 1 (δ / 3)
    have hδ : 0 < δ := div_pos hb (by norm_num)
    have hτ : 0 < τ := lt_min zero_lt_one (div_pos hδ (by norm_num))
    have hτ1 : τ ≤ 1 := min_le_left _ _
    have hτδ : τ ≤ δ / 3 := min_le_right _ _
    have haN := hgood τ hτ
    have hbN0 : Tendsto (fun n : ℕ =>
        |(n * (μ {⌊(1 - (offspringMean μ).toReal) * n⌋₊}).toReal) /
          ((Measure.pi fun _ : Fin n => μ) (BGW.countBridges n)).toReal - 1|)
        atTop (𝓝 0) := by
      simpa only [sub_self, abs_zero] using (hfrac.sub_const 1).abs
    have hbN := hbN0.eventually (gt_mem_nhds hτ)
    have hγn : Tendsto (fun n : ℕ => (1 - (offspringMean μ).toReal) * (n : ℝ))
        atTop atTop := by
      simpa only [mul_comm] using tendsto_natCast_atTop_atTop.atTop_mul_const hγ
    have hk : Tendsto (fun n : ℕ => ⌊(1 - (offspringMean μ).toReal) * (n : ℝ)⌋₊)
        atTop atTop := tendsto_nat_floor_atTop.comp hγn
    have hq := hk.eventually (eventually_mass_pos μ hlit)
    filter_upwards [haN, hbN, hGc.eventually (gt_mem_nhds hδ),
      eventually_size_admissible μ hlit, hq, eventually_gt_atTop (0 : ℕ)]
      with n ha hb hcompl hsize hqn hn
    have hn0 : n ≠ 0 := Nat.ne_of_gt hn
    have hZ0 : (Measure.pi fun _ : Fin n => μ) (BGW.countBridges n) ≠ 0 :=
      (BGW.pi_countBridges_ne_zero_iff μ n).mpr ⟨hn0, hsize⟩
    have hZ : 0 < ((Measure.pi fun _ : Fin n => μ) (BGW.countBridges n)).toReal :=
      ENNReal.toReal_pos hZ0 (measure_ne_top _ _)
    have hqR : 0 < (μ {⌊(1 - (offspringMean μ).toReal) * (n : ℝ)⌋₊}).toReal :=
      ENNReal.toReal_pos hqn.ne' (measure_ne_top _ _)
    let _ : IsProbabilityMeasure (MaximumSwapLaw.bridgeCountsLaw μ n) :=
      BGW.isProbabilityMeasure_cond_pi_countBridges μ hn0 hsize
    let _ : IsProbabilityMeasure (D n) := by
      dsimp only [D]
      infer_instance
    let _ : IsProbabilityMeasure (P n) := by
      dsimp only [P]
      let _ : IsProbabilityMeasure (incrementLaw μ) := by
        unfold incrementLaw
        infer_instance
      infer_instance
    have hQ : ∀ x ∈ G n, ((D n) {x}).toReal =
        endpointDensity μ n x * ((P n) {x}).toReal := by
      intro x hx
      rcases hx with ⟨z, hz, rfl⟩
      have hzz := ha z hz
      exact deletedIncrements_law_real_atom μ z hzz.1 hzz.2.1 hZ
    have hf : ∀ x ∈ G n, |endpointDensity μ n x - 1| ≤ δ := by
      intro x hx
      rcases hx with ⟨z, hz, rfl⟩
      have hzz := ha z hz
      let r : ℕ := n - 1 - ∑ i, z i
      let q : ℝ := (μ {⌊(1 - (offspringMean μ).toReal) * (n : ℝ)⌋₊}).toReal
      let Z : ℝ := ((Measure.pi fun _ : Fin n => μ) (BGW.countBridges n)).toReal
      let a : ℝ := (μ {r}).toReal / q
      let c : ℝ := (n : ℝ) * q / Z
      have ha' : |a - 1| < τ := hzz.2.2
      have hb' : |c - 1| < τ := hb
      have hdensity : endpointDensity μ n (fun i => (z i : ℤ) - 1) = a * c := by
        dsimp only [endpointDensity, residualCounts, a, c, q, Z, r]
        simp only [sub_add_cancel, Int.toNat_natCast]
        have hqR' : (μ {⌊(n : ℝ) - (n : ℝ) * (offspringMean μ).toReal⌋₊}).toReal ≠ 0 := by
          have harg : (n : ℝ) - (n : ℝ) * (offspringMean μ).toReal =
              (1 - (offspringMean μ).toReal) * n := by ring
          rw [harg]
          exact hqR.ne'
        have hqR'' : (μ {⌊(n : ℝ) * (1 - (offspringMean μ).toReal)⌋₊}).toReal ≠ 0 := by
          rw [mul_comm]
          exact hqR.ne'
        field_simp [hqR.ne', hZ.ne', hqR', hqR'']
      rw [hdensity]
      have hab : |a * c - 1| ≤ |a - 1| * |c - 1| + |a - 1| + |c - 1| := by
        calc
          |a * c - 1| = |(a - 1) * (c - 1) + (a - 1) + (c - 1)| := by
            congr 1
            ring
          _ ≤ |(a - 1) * (c - 1)| + |a - 1| + |c - 1| := by
            have h₁ := abs_add_le ((a - 1) * (c - 1) + (a - 1)) (c - 1)
            have h₂ := abs_add_le ((a - 1) * (c - 1)) (a - 1)
            linarith
          _ = |a - 1| * |c - 1| + |a - 1| + |c - 1| := by rw [abs_mul]
      have hprod : |a - 1| * |c - 1| ≤ τ * τ :=
        mul_le_mul ha'.le hb'.le (abs_nonneg _) hτ.le
      have htriangle : |a * c - 1| ≤ τ ^ 2 + 2 * τ := by
        rw [pow_two]
        linarith
      have hτsq : τ ^ 2 ≤ τ := by
        have := mul_nonneg hτ.le (sub_nonneg.mpr hτ1)
        nlinarith
      exact htriangle.trans (by nlinarith)
    calc
      tvDist (D n) (P n) = tvDist (P n) (D n) := tvDist_comm _ _
      _ ≤ 2 * (δ + (P n).real (G n)ᶜ) :=
        tvDist_le_of_density_on_of_nonneg (P n) (D n) (G n)
          (endpointDensity μ n) δ hδ.le hQ hf
      _ < b := by
        dsimp only [δ] at hcompl ⊢
        linarith

end
end SubcriticalCauchy.Bienayme
