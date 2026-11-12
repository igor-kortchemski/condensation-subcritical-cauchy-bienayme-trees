module

public import SubcriticalCauchy.DeletionPositionLawAux
public import SubcriticalCauchy.MainProofs.Theorem31

/-!
# Joint law of the insertion position and the deleted increments
-/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Topology BigOperators

namespace SubcriticalCauchy.Bienayme

noncomputable section

/-- Exact atom of the joint insertion-position and residual law. -/
theorem deletionWithPosition_succ_atom
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {m : ℕ} (i : Fin (m + 1)) (z : Fin m → ℕ) (r : ℕ)
    (hr : ∀ j, z j < r) (hsum : r + ∑ j, z j = m) :
    ((MaximumSwapLaw.bridgeCountsLaw μ (m + 1)).map (deletionWithPosition (m + 1)))
      {((i : ℕ), fun j => (z j : ℤ) - 1)} =
      μ {r} * (∏ j, μ {z j}) /
        (Measure.pi fun _ : Fin (m + 1) => μ) (BGW.countBridges (m + 1)) := by
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  rw [MaximumSwapLaw.bridgeCountsLaw,
    cond_apply (Set.to_countable (BGW.countBridges (m + 1))).measurableSet,
    deletionWithPosition_succ_preimage i z r hr hsum]
  rw [BGW.pi_eq_tsum_indicator μ {Fin.insertNth i r z}]
  have hweight : (∏ j, μ {Fin.insertNth (α := fun _ => ℕ) i r z j}) =
      μ {r} * ∏ j, μ {z j} := by
    rw [← Fin.prod_insertNth (M := ℝ≥0∞) i (μ {r}) (fun j => μ {z j})]
    apply Finset.prod_congr rfl
    intro j _
    refine Fin.succAboveCases i ?_ (fun k => ?_) j <;> simp
  simp only [Set.indicator_singleton, tsum_pi_single, hweight, ENNReal.div_eq_inv_mul]

/-- The iid increment law is the coordinatewise pushforward of the iid count law. -/
private theorem pi_incrementLaw_eq_map_dpl (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (k : ℕ) :
    (Measure.pi fun _ : Fin k => incrementLaw μ) =
      (Measure.pi fun _ : Fin k => μ).map (fun z i => (z i : ℤ) - 1) := by
  symm
  simpa only [incrementLaw] using
    (Measure.pi_map_pi (μ := fun _ : Fin k => μ)
      (f := fun _ : Fin k => fun z : ℕ => (z : ℤ) - 1)
      (fun _ => (measurable_of_countable _).aemeasurable))

private def residualCountsDPL {k : ℕ} (x : Fin k → ℤ) : Fin k → ℕ :=
  fun i => (x i + 1).toNat

private def endpointDensityDPL (μ : Measure ℕ) (n : ℕ)
    (_ : ℕ × (Fin (n - 1) → ℤ)) (x : Fin (n - 1) → ℤ) : ℝ :=
  (n : ℝ) * (μ {n - 1 - ∑ i, residualCountsDPL x i}).toReal /
    ((Measure.pi fun _ : Fin n => μ) (BGW.countBridges n)).toReal

/-- Real-valued form of the joint atom, relative to the product reference. -/
private theorem deletionWithPosition_law_real_atom
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {m : ℕ} (i : Fin (m + 1)) (z : Fin m → ℕ) (r : ℕ)
    (hr : ∀ j, z j < r) (hsum : r + ∑ j, z j = m)
    (hZ : 0 < ((Measure.pi fun _ : Fin (m + 1) => μ)
      (BGW.countBridges (m + 1))).toReal) :
    (((MaximumSwapLaw.bridgeCountsLaw μ (m + 1)).map
        (deletionWithPosition (m + 1)))
        {((i : ℕ), fun j => (z j : ℤ) - 1)}).toReal =
      endpointDensityDPL μ (m + 1) ((i : ℕ), fun j => (z j : ℤ) - 1)
        (fun j => (z j : ℤ) - 1) *
        (((uniformInsertionPosition (m + 1)).prod
          (Measure.pi fun _ : Fin m => incrementLaw μ))
          {((i : ℕ), fun j => (z j : ℤ) - 1)}).toReal := by
  rw [deletionWithPosition_succ_atom μ i z r hr hsum]
  rw [← Set.singleton_prod_singleton, Measure.prod_prod,
    uniformInsertionPosition_succ_atom, pi_incrementLaw_atom]
  simp only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_prod, ENNReal.toReal_inv, endpointDensityDPL, residualCountsDPL,
    Nat.add_sub_cancel, sub_add_cancel, Int.toNat_natCast]
  have hZ0 : ((Measure.pi fun _ : Fin (m + 1) => μ)
      (BGW.countBridges (m + 1))).toReal ≠ 0 := hZ.ne'
  have hr' : r = m - ∑ i, z i := by omega
  rw [hr']
  field_simp [hZ0]
  ring_nf
  all_goals ac_rfl

/-- The insertion position and deleted increments become asymptotically
independent, with uniform position and iid increments. -/
theorem deletionWithPosition_tvDist
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) :
    Tendsto (fun n : ℕ =>
      tvDist ((MaximumSwapLaw.bridgeCountsLaw μ n).map (deletionWithPosition n))
        ((uniformInsertionPosition n).prod
          (Measure.pi fun _ : Fin (n - 1) => incrementLaw μ)))
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
  let D : (n : ℕ) → Measure (ℕ × (Fin (n - 1) → ℤ)) := fun n =>
    (MaximumSwapLaw.bridgeCountsLaw μ n).map (deletionWithPosition n)
  let P : (n : ℕ) → Measure (ℕ × (Fin (n - 1) → ℤ)) := fun n =>
    (uniformInsertionPosition n).prod
      (Measure.pi fun _ : Fin (n - 1) => incrementLaw μ)
  let G : (n : ℕ) → Set (ℕ × (Fin (n - 1) → ℤ)) := fun n =>
    (Set.range fun i : Fin n => (i : ℕ)) ×ˢ
      ((fun z : Fin (n - 1) → ℕ => fun i => (z i : ℤ) - 1) ''
        endpointResidualSet μ h n)
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
  have hUr (n : ℕ) (hn : 0 < n) :
      uniformInsertionPosition n (Set.range fun i : Fin n => (i : ℕ)) = 1 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    simp only [uniformInsertionPosition, Measure.smul_apply, Measure.coe_finsetSum,
      Finset.sum_apply, Measure.dirac_apply]
    have hmem (j : Fin (m + 1)) : (j : ℕ) ∈ Set.range fun i : Fin (m + 1) => (i : ℕ) :=
      ⟨j, rfl⟩
    simp only [Set.indicator_of_mem (hmem _), Pi.one_apply, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul]
    simpa using ENNReal.inv_mul_cancel (a := ((m + 1 : ℕ) : ℝ≥0∞)) (by simp) (by simp)
  have hPG : Tendsto (fun n => (P n).real (G n)) atTop (𝓝 1) := by
    apply hGreal.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    dsimp only [P, G]
    change _ = (((uniformInsertionPosition n).prod
      (Measure.pi fun _ : Fin (n - 1) => incrementLaw μ))
        ((Set.range fun i : Fin n => (i : ℕ)) ×ˢ
          ((fun z : Fin (n - 1) → ℕ => fun i => (z i : ℤ) - 1) ''
            endpointResidualSet μ h n))).toReal
    rw [Measure.prod_prod, hUr n hn, one_mul]
    rw [pi_incrementLaw_eq_map_dpl]
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
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    let _ : IsProbabilityMeasure (uniformInsertionPosition n) := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
      exact uniformInsertionPosition_succ_isProbability m
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
    let _ : IsProbabilityMeasure (uniformInsertionPosition n) := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      exact uniformInsertionPosition_succ_isProbability m
    let _ : IsProbabilityMeasure (P n) := by
      dsimp only [P]
      let _ : IsProbabilityMeasure (incrementLaw μ) := by
        unfold incrementLaw
        infer_instance
      infer_instance
    have hQ : ∀ x ∈ G n, ((D n) {x}).toReal =
        endpointDensityDPL μ n x x.2 * ((P n) {x}).toReal := by
      rintro ⟨k, x⟩ ⟨hi, hz⟩
      obtain ⟨i, hi⟩ := hi
      dsimp only at hi
      subst k
      obtain ⟨z, hz, rfl⟩ := hz
      have hzz := ha z hz
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      exact deletionWithPosition_law_real_atom μ i z (m - ∑ j, z j)
        hzz.2.1 (Nat.sub_add_cancel (Nat.le_of_lt hzz.1)) hZ
    have hf : ∀ x ∈ G n, |endpointDensityDPL μ n x x.2 - 1| ≤ δ := by
      rintro ⟨k, x⟩ ⟨hi, hz⟩
      obtain ⟨i, hi⟩ := hi
      dsimp only at hi
      subst k
      obtain ⟨z, hz, rfl⟩ := hz
      have hzz := ha z hz
      let r : ℕ := n - 1 - ∑ i, z i
      let q : ℝ := (μ {⌊(1 - (offspringMean μ).toReal) * (n : ℝ)⌋₊}).toReal
      let Z : ℝ := ((Measure.pi fun _ : Fin n => μ) (BGW.countBridges n)).toReal
      let a : ℝ := (μ {r}).toReal / q
      let c : ℝ := (n : ℝ) * q / Z
      have ha' : |a - 1| < τ := hzz.2.2
      have hb' : |c - 1| < τ := hb
      have hdensity : endpointDensityDPL μ n
          ((i : ℕ), fun j => (z j : ℤ) - 1) (fun j => (z j : ℤ) - 1) = a * c := by
        dsimp only [endpointDensityDPL, residualCountsDPL, a, c, q, Z, r]
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
          (fun x => endpointDensityDPL μ n x x.2) δ hδ.le hQ hf
      _ < b := by
        dsimp only [δ] at hcompl ⊢
        linarith

end
end SubcriticalCauchy.Bienayme
