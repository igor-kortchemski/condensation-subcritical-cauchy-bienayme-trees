module

public import SubcriticalCauchy.PaperRoute.ALProofAux
public import SubcriticalCauchy.PaperRoute.ALProofTV
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.ConditionalProbability

/-!
# The Armendáriz–Loulakis criterion

The proof first decomposes the large-sum event according to the position of its
strict maximum.  Exchangeability reduces all cells to the last one, where
Fubini supplies the one-coordinate increment law.  The remaining estimates are
the local ratio hypothesis, tightness, and the maximum-tail hypothesis.
-/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Topology BigOperators

namespace SubcriticalCauchy.ArmendarizLoulakis

noncomputable section

/-- Fubini's theorem for the last-coordinate AL event. -/
theorem al_endSet_integral {m : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {B G : Set (Fin m → ℝ)} (hB : MeasurableSet B) (hG : MeasurableSet G) (x : ℝ) :
    ((Measure.pi fun _ : Fin (m + 1) => ν) (alEndSet m B G x)).toReal =
      ∫ r : Fin m → ℝ, ((B ∩ G).indicator
        (fun r => ν {a : ℝ | a + ∑ i, r i ∈ Set.Ioc x (x + 1)}) r).toReal
        ∂(Measure.pi fun _ : Fin m => ν) := by
  let R : Measure (Fin m → ℝ) := Measure.pi fun _ => ν
  let P : Measure (Fin (m + 1) → ℝ) := Measure.pi fun _ => ν
  let S : Set (ℝ × (Fin m → ℝ)) :=
    {p | p.2 ∈ B ∩ G ∧ p.1 + ∑ i, p.2 i ∈ Set.Ioc x (x + 1)}
  have hS : MeasurableSet S := by
    apply MeasurableSet.inter
    · exact (hB.inter hG).preimage measurable_snd
    · apply measurableSet_Ioc.preimage
      exact measurable_fst.add
        (Finset.measurable_fun_sum _ fun i _ => (measurable_pi_apply i).comp measurable_snd)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)
  have he : e ⁻¹' S = alEndSet m B G x := by
    ext z
    change (((fun i => z ((Fin.last m).succAbove i)) ∈ B ∩ G ∧
        z (Fin.last m) + ∑ i, z ((Fin.last m).succAbove i) ∈ Set.Ioc x (x + 1)) ↔ _)
    rw [Fin.succAbove_last]
    change (((fun i : Fin m => z i.castSucc) ∈ B ∩ G ∧
        z (Fin.last m) + ∑ i : Fin m, z i.castSucc ∈ Set.Ioc x (x + 1)) ↔
          (alResidual (Fin.last m) z ∈ B ∩ G ∧ (∑ i, z i) ∈ Set.Ioc x (x + 1)))
    rw [al_residual_last]
    constructor
    · rintro ⟨hBG, hx⟩
      refine ⟨hBG, ?_⟩
      rw [Fin.sum_univ_castSucc]
      simpa [add_comm] using hx
    · rintro ⟨hBG, hx⟩
      refine ⟨hBG, ?_⟩
      rw [Fin.sum_univ_castSucc] at hx
      simpa [add_comm] using hx
  have hMP := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => ν) (Fin.last m)
  have hmass : P (alEndSet m B G x) = (ν.prod R) S := by
    rw [← he]
    exact hMP.measure_preimage hS.nullMeasurableSet
  calc
    (P (alEndSet m B G x)).toReal = ((ν.prod R) S).toReal := congrArg ENNReal.toReal hmass
    _ = (∫⁻ r : Fin m → ℝ, ν ((fun a => (a, r)) ⁻¹' S) ∂R).toReal := by
      rw [Measure.prod_apply_symm hS]
    _ = ∫ r : Fin m → ℝ, (ν ((fun a => (a, r)) ⁻¹' S)).toReal ∂R := by
      symm
      apply integral_toReal (measurable_measure_prodMk_right hS).aemeasurable
      exact Filter.Eventually.of_forall fun _ => measure_lt_top _ _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with r
      by_cases hrB : r ∈ B <;> by_cases hrG : r ∈ G <;> simp [S, hrB, hrG]

/-- Conditions making the last coordinate a strict maximum identify the last
strict-maximum cell with the elementary Fubini event. -/
theorem al_cell_last_eq_endSet {m : ℕ} (B G : Set (Fin m → ℝ)) (x : ℝ)
    (hstrict : ∀ r ∈ B ∩ G, ∀ a : ℝ, a + ∑ i, r i ∈ Set.Ioc x (x + 1) →
      ∀ j : Fin m, r j < a) :
    alCell (Fin.last m) B G x = alEndSet m B G x := by
  ext z
  change (alStrictMaxAt (Fin.last m) z ∧ alResidual (Fin.last m) z ∈ B ∩ G ∧
    (∑ i, z i) ∈ Set.Ioc x (x + 1)) ↔
      (alResidual (Fin.last m) z ∈ B ∩ G ∧ (∑ i, z i) ∈ Set.Ioc x (x + 1))
  constructor
  · rintro ⟨-, hBG, hx⟩
    exact ⟨hBG, hx⟩
  · rintro ⟨hBG, hx⟩
    rw [al_sum_eq_sum_residual_add z (Fin.last m)] at hx
    have hx' : z (Fin.last m) + ∑ i, alResidual (Fin.last m) z i ∈
        Set.Ioc x (x + 1) := by simpa [add_comm] using hx
    refine ⟨?_, hBG, by rw [al_sum_eq_sum_residual_add z (Fin.last m)]; exact hx⟩
    intro j hj
    obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hj
    have := hstrict _ hBG _ hx' j
    simpa only [al_residual_last] using this


/-- The pointwise AL estimate in dimension `m+1`. -/
theorem al_fixed_estimate {m : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (ε A x c : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (h26x : |((Measure.pi fun _ : Fin (m + 1) => ν)
          {z | ∑ i, z i ∈ Set.Ioc x (x + 1)}).toReal /
          (((m + 1 : ℕ) : ℝ) * (ν (Set.Ioc x (x + 1))).toReal) - 1| ≤ ε)
    (h32x : ∀ y : ℝ, |y| ≤ A * c →
      1 - (ν (Set.Ioc (x - y) (x - y + 1))).toReal /
        (ν (Set.Ioc x (x + 1))).toReal ≤ ε)
    (htightx : ((Measure.pi fun _ : Fin m => ν)
      {r | A * c < |∑ i, r i|}).toReal ≤ ε)
    (htailx : ((m + 1 : ℕ) : ℝ) * (ν (Set.Ioi (x - A * c))).toReal ≤ ε) :
    tvDist (((Measure.pi fun _ : Fin (m + 1) => ν)[|
        {z | ∑ i, z i ∈ Set.Ioc x (x + 1)}]).map (alSwapDrop (m + 1)))
      (Measure.pi fun _ : Fin m => ν) ≤ 8 * ε := by
  classical
  let P : Measure (Fin (m + 1) → ℝ) := Measure.pi fun _ => ν
  let R : Measure (Fin m → ℝ) := Measure.pi fun _ => ν
  let E : Set (Fin (m + 1) → ℝ) := {z | ∑ i, z i ∈ Set.Ioc x (x + 1)}
  let G : Set (Fin m → ℝ) :=
    {r | |∑ i, r i| ≤ A * c ∧ ∀ j, r j ≤ x - A * c}
  let N : ℝ := (m + 1 : ℕ)
  let w : ℝ := (ν (Set.Ioc x (x + 1))).toReal
  let q : ℝ := (P E).toReal
  let ρ : ℝ := (1 - ε) / (1 + ε)
  have hsumR : Measurable (fun r : Fin m → ℝ => ∑ i, r i) :=
    Finset.measurable_fun_sum _ fun i _ => measurable_pi_apply i
  have hN : 0 < N := by positivity
  have hE : MeasurableSet E := measurableSet_Ioc.preimage
    (Finset.measurable_fun_sum _ fun i _ => measurable_pi_apply i)
  have habsR : Measurable (fun r : Fin m → ℝ => |∑ i, r i|) := by
    simpa only [Real.norm_eq_abs] using hsumR.norm
  have hG : MeasurableSet G := by
    change MeasurableSet {r : Fin m → ℝ |
      |∑ i, r i| ≤ A * c ∧ ∀ j, r j ≤ x - A * c}
    apply MeasurableSet.inter
    · exact measurableSet_le habsR measurable_const
    · exact (MeasurableSet.iInter fun j =>
          measurableSet_le (measurable_pi_apply j) (measurable_const (a := x - A * c))).congr
        (by ext r; simp only [Set.mem_iInter]; rfl)
  have habs := abs_le.mp h26x
  have hden : 0 < N * w := by
    by_contra h
    have hz : N * w = 0 := le_antisymm (le_of_not_gt h)
      (mul_nonneg hN.le (ENNReal.toReal_nonneg))
    rw [hz, div_zero, zero_sub, abs_neg, abs_one] at h26x
    linarith
  have hw : 0 < w := by
    have hn : w ≠ 0 := fun hw0 => by simp [hw0] at hden
    exact lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hn)
  have hq_lower : (1 - ε) * (N * w) ≤ q := by
    exact (le_div_iff₀ hden).mp (by linarith [habs.1] : 1 - ε ≤ q / (N * w))
  have hq_upper : q ≤ (1 + ε) * (N * w) := by
    have := (div_le_iff₀ hden).mp (by linarith [habs.2] : q / (N * w) ≤ 1 + ε)
    nlinarith
  have hq : 0 < q := lt_of_lt_of_le (mul_pos (sub_pos.mpr hε1) hden) hq_lower
  have hPE : P E ≠ 0 := by
    intro hzero
    change 0 < (P E).toReal at hq
    simp [hzero] at hq
  have hstrict : ∀ r ∈ G, ∀ a : ℝ, a + ∑ i, r i ∈ Set.Ioc x (x + 1) →
      ∀ j : Fin m, r j < a := by
    intro r hr a ha j
    have hsum : ∑ i, r i ≤ A * c := le_trans (le_abs_self _) hr.1
    have hlast : x - ∑ i, r i < a := by linarith [ha.1]
    exact lt_of_le_of_lt (hr.2 j) (by linarith)
  have hGc : R.real Gᶜ ≤ 2 * ε := by
    let U : Set (Fin m → ℝ) := {r | A * c < |∑ i, r i|}
    let V : Set (Fin m → ℝ) := {r | ∃ j, x - A * c < r j}
    have hU : MeasurableSet U := measurableSet_lt measurable_const
      habsR
    have hV : MeasurableSet V := by
      have : V = ⋃ j, {r : Fin m → ℝ | x - A * c < r j} := by ext r; simp [V]
      rw [this]
      exact MeasurableSet.iUnion fun j => measurableSet_lt measurable_const (measurable_pi_apply j)
    have hsub : Gᶜ ⊆ U ∪ V := by
      intro r hr
      by_cases habsr : |∑ i, r i| ≤ A * c
      · right
        by_contra hnot
        apply hr
        refine ⟨habsr, fun j => le_of_not_gt ?_⟩
        intro hj
        exact hnot ⟨j, hj⟩
      · exact Or.inl (lt_of_not_ge habsr)
    have hVU : V = ⋃ j, (fun r : Fin m → ℝ => r j) ⁻¹' Set.Ioi (x - A * c) := by
      ext r
      simp [V]
    have hVle : R.real V ≤ ((m : ℕ) : ℝ) * (ν (Set.Ioi (x - A * c))).toReal := by
      calc
        R.real V = R.real (⋃ j, (fun r : Fin m → ℝ => r j) ⁻¹' Set.Ioi (x - A * c)) := congrArg _ hVU
        _ ≤ ∑ j : Fin m, R.real ((fun r : Fin m → ℝ => r j) ⁻¹' Set.Ioi (x - A * c)) :=
          measureReal_iUnion_fintype_le
            (fun j : Fin m => (fun r : Fin m → ℝ => r j) ⁻¹' Set.Ioi (x - A * c))
        _ = _ := by
          have heval (j : Fin m) : R.real ((fun r : Fin m → ℝ => r j) ⁻¹'
              Set.Ioi (x - A * c)) = (ν (Set.Ioi (x - A * c))).toReal :=
            congrArg ENNReal.toReal
              ((measurePreserving_eval (μ := fun _ : Fin m => ν) j).measure_preimage
                measurableSet_Ioi.nullMeasurableSet)
          simp_rw [heval]
          simp
    calc
      R.real Gᶜ ≤ R.real (U ∪ V) := measureReal_mono hsub
      _ ≤ R.real U + R.real V := measureReal_union_le _ _
      _ ≤ ε + (m : ℝ) * (ν (Set.Ioi (x - A * c))).toReal := add_le_add htightx hVle
      _ ≤ ε + ε := by
        gcongr
        have hm : (m : ℝ) ≤ m + 1 := by norm_num
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hm) ENNReal.toReal_nonneg |>.trans htailx
      _ = 2 * ε := by ring
  have hpoint : ∀ r ∈ G, (1 - ε) * w ≤
      (ν {a : ℝ | a + ∑ i, r i ∈ Set.Ioc x (x + 1)}).toReal := by
    intro r hr
    have hset : {a : ℝ | a + ∑ i, r i ∈ Set.Ioc x (x + 1)} =
        Set.Ioc (x - ∑ i, r i) (x - ∑ i, r i + 1) := by
      ext a
      simp only [Set.mem_ofPred_eq, Set.mem_Ioc]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    rw [hset]
    have hloc := h32x (∑ i, r i) hr.1
    have hw' : 0 < (ν (Set.Ioc x (x + 1))).toReal := hw
    have hfrac : 1 - ε ≤
        (ν (Set.Ioc (x - ∑ i, r i) (x - ∑ i, r i + 1))).toReal / w := by
      linarith
    have := (le_div_iff₀ hw).mp hfrac
    change (1 - ε) * w ≤ _ at this
    exact this
  have hint : ∀ B : Set (Fin m → ℝ), MeasurableSet B →
      (1 - ε) * w * R.real (B ∩ G) ≤ (P (alEndSet m B G x)).toReal := by
    intro B hB
    rw [al_endSet_integral ν hB hG x]
    have hS : MeasurableSet {p : ℝ × (Fin m → ℝ) | p.2 ∈ B ∩ G ∧
        p.1 + ∑ i, p.2 i ∈ Set.Ioc x (x + 1)} := by
      apply MeasurableSet.inter
      · exact (hB.inter hG).preimage measurable_snd
      · apply measurableSet_Ioc.preimage
        exact measurable_fst.add (hsumR.comp measurable_snd)
    have hf : Integrable (fun r => ((B ∩ G).indicator
        (fun r => ν {a : ℝ | a + ∑ i, r i ∈ Set.Ioc x (x + 1)}) r).toReal) R := by
      refine Integrable.of_bound (f := fun r => ((B ∩ G).indicator
        (fun r => ν {a : ℝ | a + ∑ i, r i ∈ Set.Ioc x (x + 1)}) r).toReal) ?_ 1 ?_
      · have heq : (fun r => ((B ∩ G).indicator
            (fun r => ν {a : ℝ | a + ∑ i, r i ∈ Set.Ioc x (x + 1)}) r).toReal) =
            (B ∩ G).indicator (fun r => (ν ((fun a => (a, r)) ⁻¹'
              {p : ℝ × (Fin m → ℝ) | p.2 ∈ B ∩ G ∧
                p.1 + ∑ i, p.2 i ∈ Set.Ioc x (x + 1)})).toReal) := by
          funext r
          by_cases hrB : r ∈ B <;> by_cases hrG : r ∈ G <;> simp [hrB, hrG]
        rw [heq]
        exact ((measurable_measure_prodMk_right hS).ennreal_toReal.indicator
          (hB.inter hG)).aemeasurable.aestronglyMeasurable
      · filter_upwards [] with r
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        by_cases hr : r ∈ B ∩ G
        · simp only [Set.indicator_of_mem hr]
          exact measureReal_le_one
        · simp [hr]
    have hg : Integrable ((B ∩ G).indicator (fun _ : Fin m → ℝ => (1 - ε) * w)) R :=
      (integrable_const _).indicator (hB.inter hG)
    have hle : (B ∩ G).indicator (fun _ : Fin m → ℝ => (1 - ε) * w) ≤
        fun r => ((B ∩ G).indicator
          (fun r => ν {a : ℝ | a + ∑ i, r i ∈ Set.Ioc x (x + 1)}) r).toReal := by
      intro r
      by_cases hr : r ∈ B ∩ G
      · simp only [Set.indicator_of_mem hr]
        exact hpoint r hr.2
      · simp [hr]
    calc
      (1 - ε) * w * R.real (B ∩ G) =
          ∫ r, (B ∩ G).indicator (fun _ : Fin m → ℝ => (1 - ε) * w) r ∂R := by
        rw [integral_indicator_const _ (hB.inter hG), smul_eq_mul]
        ring
      _ ≤ _ := integral_mono hg hf hle
  have hraw : ∀ B : Set (Fin m → ℝ), MeasurableSet B →
      N * ((1 - ε) * w * R.real (B ∩ G)) ≤ (P {z | alSwapDrop (m + 1) z ∈ B ∧
        ∑ i, z i ∈ Set.Ioc x (x + 1)}).toReal := by
    intro B hB
    have hlastB : alCell (Fin.last m) B G x = alEndSet m B G x := by
      apply al_cell_last_eq_endSet
      intro r hr
      exact hstrict r hr.2
    have hcell : (1 - ε) * w * R.real (B ∩ G) ≤
        (P (alCell (Fin.last m) B G x)).toReal := by
      rw [hlastB]
      exact hint B hB
    exact (mul_le_mul_of_nonneg_left hcell (Nat.cast_nonneg _)).trans
      (by simpa [N, P] using al_cells_le_map_event ν hB hG x)
  let η : ℝ := 1 - ρ + ρ * R.real Gᶜ
  let _ : IsProbabilityMeasure P[|E] := cond_isProbabilityMeasure hPE
  let Q : Measure (Fin m → ℝ) := (P[|E]).map (alSwapDrop (m + 1))
  have hρ0 : 0 ≤ ρ := div_nonneg (by linarith) (by linarith)
  have hρ1 : ρ ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  have hstrong : ∀ B : Set (Fin m → ℝ), MeasurableSet B →
      ρ * R.real B - ρ * R.real Gᶜ ≤ Q.real B := by
    intro B hB
    have hsplit : R.real (B ∩ G) + R.real (B \ G) = R.real B :=
      measureReal_inter_add_sdiff hG
    have hdiff : R.real (B \ G) ≤ R.real Gᶜ := measureReal_mono (by intro z hz; exact hz.2)
    have hnorm : ρ * R.real (B ∩ G) ≤ Q.real B := by
      have hQ : Q.real B = q⁻¹ * (P {z | alSwapDrop (m + 1) z ∈ B ∧
          ∑ i, z i ∈ Set.Ioc x (x + 1)}).toReal := by
        rw [show Q.real B = ((P[|E]).map (alSwapDrop (m + 1)) B).toReal from rfl]
        rw [Measure.map_apply (al_alSwapDrop_measurable _) hB]
        rw [cond_apply hE]
        simp only [ENNReal.toReal_mul, ENNReal.toReal_inv]
        congr 2
        apply congrArg (fun s : Set (Fin (m + 1) → ℝ) => P s)
        ext z
        simp only [E, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
        tauto
      rw [hQ]
      calc
        ρ * R.real (B ∩ G) = ((1 + ε) * (N * w))⁻¹ *
            (N * ((1 - ε) * w * R.real (B ∩ G))) := by
          dsimp [ρ]
          field_simp [ne_of_gt hN, ne_of_gt hw]
        _ ≤ q⁻¹ * (N * ((1 - ε) * w * R.real (B ∩ G))) := by
          apply mul_le_mul (inv_anti₀ hq hq_upper) le_rfl
            (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
              (mul_nonneg (by linarith) hw.le) (measureReal_nonneg))) (inv_nonneg.mpr hq.le)
        _ ≤ q⁻¹ * (P {z | alSwapDrop (m + 1) z ∈ B ∧
          ∑ i, z i ∈ Set.Ioc x (x + 1)}).toReal :=
          mul_le_mul_of_nonneg_left (hraw B hB) (inv_nonneg.mpr hq.le)
    have hdecomp : R.real (B ∩ G) = R.real B - R.real (B \ G) := by linarith
    have hdiff' := mul_le_mul_of_nonneg_left hdiff hρ0
    rw [hdecomp] at hnorm
    nlinarith
  have hweak : ∀ B : Set (Fin m → ℝ), MeasurableSet B → R.real B - Q.real B ≤ η := by
    intro B hB
    have hs := hstrong B hB
    have hB1 : R.real B ≤ 1 := measureReal_le_one
    have hr := mul_le_mul_of_nonneg_left hB1 (sub_nonneg.mpr hρ1)
    dsimp [η]
    nlinarith
  have hset : ∀ B : Set (Fin m → ℝ), MeasurableSet B → |Q.real B - R.real B| ≤ η := by
    intro B hB
    rw [abs_le]
    constructor
    · have := hweak B hB
      linarith
    · have hc := hweak Bᶜ hB.compl
      have hQc : Q.real Bᶜ = 1 - Q.real B := probReal_compl_eq_one_sub hB
      have hRc : R.real Bᶜ = 1 - R.real B := probReal_compl_eq_one_sub hB
      linarith
  have htv : tvDist Q R ≤ 2 * η := al_tvDist_le_of_forall_set_prob Q R η hset
  have hρε : 1 - ρ ≤ 2 * ε := by
    dsimp [ρ]
    have he' : 0 < 1 + ε := by linarith
    rw [show 1 - (1 - ε) / (1 + ε) = (2 * ε) / (1 + ε) by field_simp; ring]
    exact (div_le_iff₀ he').mpr (by nlinarith)
  have hGρη : ρ * R.real Gᶜ ≤ 2 * ε := by
    calc
      ρ * R.real Gᶜ ≤ ρ * (2 * ε) := mul_le_mul_of_nonneg_left hGc hρ0
      _ ≤ 1 * (2 * ε) := mul_le_mul_of_nonneg_right hρ1 (by linarith)
      _ = 2 * ε := one_mul _
  calc
    tvDist Q R ≤ 2 * η := htv
    _ ≤ 2 * (2 * ε + 2 * ε) := by dsimp [η]; nlinarith
    _ = 8 * ε := by ring


/-- Helper used by the frozen statement.  Only the positivity of `c`, which lets
us replace `A` by `max A 1`, is needed among the standing H1/H2 assumptions. -/
theorem al_criterion_wrapper (ν : Measure ℝ) [IsProbabilityMeasure ν] (d ℓ c : ℕ → ℝ)
    (hc : ∀ᶠ n : ℕ in atTop, 0 < c n)
    (_hℓc : Tendsto (fun n : ℕ => ℓ n / c n) atTop atTop)
    (h26 : ∀ τ > 0, ∀ᶠ n : ℕ in atTop, ∀ x : ℝ, d n ≤ x →
      |((Measure.pi fun _ : Fin n => ν) {y | ∑ i, y i ∈ Set.Ioc x (x + 1)}).toReal /
          ((n : ℝ) * (ν (Set.Ioc x (x + 1))).toReal) - 1| ≤ τ)
    (h32 : ∀ A > 0, ∀ τ > 0, ∀ᶠ n : ℕ in atTop, ∀ x y : ℝ, ℓ n ≤ x → |y| ≤ A * c n →
      1 - (ν (Set.Ioc (x - y) (x - y + 1))).toReal / (ν (Set.Ioc x (x + 1))).toReal ≤ τ)
    (htight : ∀ τ > 0, ∃ A : ℝ, ∀ᶠ n : ℕ in atTop,
      ((Measure.pi fun _ : Fin (n - 1) => ν) {y | A * c n < |∑ i, y i|}).toReal ≤ τ)
    (hmax : ∀ A > 0,
      Tendsto (fun n : ℕ => (n : ℝ) * (ν (Set.Ioi (ℓ n - A * c n))).toReal) atTop (𝓝 0)) :
    ∀ τ > 0, ∀ᶠ n : ℕ in atTop, ∀ x : ℝ, max (d n) (ℓ n) ≤ x →
      tvDist (((Measure.pi fun _ : Fin n => ν)[|{y | ∑ i, y i ∈ Set.Ioc x (x + 1)}]).map
          (alSwapDrop n))
        (Measure.pi fun _ : Fin (n - 1) => ν) ≤ τ := by
  intro τ hτ
  let ε := min (τ / 16) (1 / 2)
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  have hε1 : ε < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have h8ε : 8 * ε ≤ τ := by
    have he' : ε ≤ τ / 16 := min_le_left _ _
    dsimp [ε] at he' ⊢
    linarith
  obtain ⟨A, hA⟩ := htight ε hε
  let A' := max A 1
  have hA' : 0 < A' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hmax' : ∀ᶠ n : ℕ in atTop,
      ((n : ℝ) * (ν (Set.Ioi (ℓ n - A' * c n))).toReal) ≤ ε := by
    filter_upwards [(hmax A' hA').eventually (Iio_mem_nhds hε)] with n hn
    exact hn.le
  filter_upwards [hc, hA, h32 A' hA' ε hε, h26 ε hε, hmax',
    eventually_gt_atTop 0] with n hcn hAn h32n h26n hmaxn hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  intro x hx
  have hdx : d (m + 1) ≤ x := le_trans (le_max_left _ _) hx
  have hlx : ℓ (m + 1) ≤ x := le_trans (le_max_right _ _) hx
  have htight' : ((Measure.pi fun _ : Fin m => ν)
      {r | A' * c (m + 1) < |∑ i, r i|}).toReal ≤ ε := by
    refine (measureReal_mono ?_).trans hAn
    intro r hr
    change A' * c (m + 1) < |∑ i, r i| at hr
    exact show A * c (m + 1) < |∑ i, r i| from
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_max_left A 1) hcn.le) hr
  have htail' : ((m + 1 : ℕ) : ℝ) * (ν (Set.Ioi (x - A' * c (m + 1)))).toReal ≤ ε := by
    refine (mul_le_mul_of_nonneg_left (measureReal_mono ?_) (Nat.cast_nonneg _)).trans hmaxn
    exact Set.Ioi_subset_Ioi (sub_le_sub_right hlx _)
  exact (al_fixed_estimate ν ε A' x (c (m + 1)) hε hε1 (h26n x hdx)
    (fun y hy => h32n x y hlx hy) htight' htail').trans h8ε

end
end SubcriticalCauchy.ArmendarizLoulakis
