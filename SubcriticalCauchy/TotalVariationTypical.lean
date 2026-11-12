module

public import Mathlib.MeasureTheory.Measure.TotalVariation.Defs
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

/-!
# Total variation on discrete spaces and on a typical set

On a countable discrete space, `tvDist` is the sum of the absolute differences
of the point masses.  We also record contraction under measurable maps and the
estimate used when an explicit density is known on a typical set.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace SubcriticalCauchy.Bienayme

noncomputable section

/-- Point masses sum to the real measure of any set on a countable discrete space. -/
theorem tsum_indicator_measureReal {α : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] (P : Measure α) [IsFiniteMeasure P] (G : Set α) :
    (∑' z, G.indicator (fun z => P.real {z}) z) = P.real G := by
  unfold Measure.real
  rw [← P.tsum_indicator_apply_singleton G (Set.to_countable G).measurableSet,
    ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro z
    by_cases hz : z ∈ G <;> simp [Set.indicator, hz]
  · intro z
    by_cases hz : z ∈ G
    · rw [Set.indicator_of_mem hz]
      exact measure_ne_top _ _
    · simp [Set.indicator_of_notMem hz]

/-- Extended total variation on a countable discrete space is the sum of the
norms of the differences of point masses. -/
theorem etvDist_eq_tsum_enorm {α : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] (P Q : Measure α) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] :
    etvDist P Q = ∑' z, ‖P.real {z} - Q.real {z}‖ₑ := by
  let V := P.toSignedMeasure - Q.toSignedMeasure
  let M : Measure α := Measure.sum fun z => ‖P.real {z} - Q.real {z}‖ₑ • Measure.dirac z
  have hP : Summable fun z => P.real {z} := by
    apply ENNReal.summable_toReal
    rw [show (∑' z, P {z}) = 1 by
      simpa using P.tsum_indicator_apply_singleton Set.univ MeasurableSet.univ]
    simp
  have hQ : Summable fun z => Q.real {z} := by
    apply ENNReal.summable_toReal
    rw [show (∑' z, Q {z}) = 1 by
      simpa using Q.tsum_indicator_apply_singleton Set.univ MeasurableSet.univ]
    simp
  have hVM : V.variation ≤ M := by
    apply VectorMeasure.variation_le_of_forall_enorm_le
    intro E hE
    have hPreal : P.real E = ∑' z, E.indicator (fun z => P.real {z}) z :=
      (tsum_indicator_measureReal P E).symm
    have hQreal : Q.real E = ∑' z, E.indicator (fun z => Q.real {z}) z :=
      (tsum_indicator_measureReal Q E).symm
    have hdiff : P.real E - Q.real E =
        ∑' z, E.indicator (fun z => P.real {z} - Q.real {z}) z := by
      rw [hPreal, hQreal, ← (hP.indicator E).tsum_sub (hQ.indicator E)]
      apply tsum_congr
      intro z
      by_cases hz : z ∈ E <;> simp [Set.indicator, hz]
    rw [Measure.toSignedMeasure_sub_apply hE, hdiff]
    calc
      ‖∑' z, E.indicator (fun z => P.real {z} - Q.real {z}) z‖ₑ ≤
          ∑' z, ‖E.indicator (fun z => P.real {z} - Q.real {z}) z‖ₑ :=
        enorm_tsum_le_tsum_enorm
      _ = M E := by
        simp only [M, Measure.sum_apply _ hE, Measure.smul_apply, smul_eq_mul,
          Measure.dirac_apply]
        apply tsum_congr
        intro z
        by_cases hz : z ∈ E <;> simp [Set.indicator, hz]
  have hupper : etvDist P Q ≤ ∑' z, ‖P.real {z} - Q.real {z}‖ₑ := by
    rw [etvDist_eq_etvDist_toSignedMeasure]
    exact (hVM Set.univ).trans_eq (by simp [M, Measure.sum_apply])
  apply le_antisymm hupper
  apply ENNReal.summable.tsum_le_of_sum_le
  intro s
  let parts : Finset (Set α) := s.image ({·})
  have hsub : ∀ t ∈ parts, t ⊆ Set.univ := fun _ _ => Set.subset_univ _
  have hdisj : (parts : Set (Set α)).PairwiseDisjoint id := by
    intro A hA B hB hAB
    simp only [parts, Finset.coe_image, Set.mem_image] at hA hB
    obtain ⟨a, _, rfl⟩ := hA
    obtain ⟨b, _, rfl⟩ := hB
    exact Set.disjoint_singleton.mpr
      (fun hab => hAB (congrArg (fun x : α => ({x} : Set α)) hab))
  have hfin := VectorMeasure.le_variation V MeasurableSet.univ hsub hdisj
  rw [etvDist_eq_etvDist_toSignedMeasure]
  change (∑ z ∈ s, ‖P.real {z} - Q.real {z}‖ₑ) ≤ V.variation Set.univ
  calc
    (∑ z ∈ s, ‖P.real {z} - Q.real {z}‖ₑ) =
        ∑ t ∈ parts, ‖V t‖ₑ := by
      classical
      simp only [parts, V]
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro a _
        rw [Measure.toSignedMeasure_sub_apply (measurableSet_singleton a)]
      · intro a _ b _ hab
        exact Set.singleton_injective hab
    _ ≤ V.variation Set.univ := hfin

/-- Total variation between probability measures on a countable discrete space
is the sum of the absolute differences of their point masses. -/
theorem tvDist_eq_tsum_abs {α : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] (P Q : Measure α) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] :
    tvDist P Q = ∑' z, |P.real {z} - Q.real {z}| := by
  rw [tvDist, etvDist_eq_tsum_enorm, ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro z
    rw [toReal_enorm, Real.norm_eq_abs]
  · exact fun _ => enorm_ne_top

/-- Extended total variation contracts under a measurable pushforward. -/
theorem etvDist_map_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (P Q : Measure α) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (g : α → β) (hg : Measurable g) :
    etvDist (P.map g) (Q.map g) ≤ etvDist P Q := by
  let V := P.toSignedMeasure - Q.toSignedMeasure
  have hmap : (P.map g).toSignedMeasure - (Q.map g).toSignedMeasure = V.map g := by
    ext s hs
    simp only [Measure.toSignedMeasure_sub_apply hs, VectorMeasure.map_apply _ hg hs,
      Measure.map_apply hg hs, Measure.real, V,
      Measure.toSignedMeasure_sub_apply (hg hs)]
  rw [etvDist_eq_etvDist_toSignedMeasure, etvDist_eq_etvDist_toSignedMeasure]
  change ((P.map g).toSignedMeasure - (Q.map g).toSignedMeasure).variation Set.univ ≤
    V.variation Set.univ
  rw [hmap]
  exact (VectorMeasure.variation_map_le Set.univ).trans_eq (by simp [Measure.map_apply hg])

/-- Total variation contracts under a measurable pushforward. -/
theorem tvDist_map_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (P Q : Measure α) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (g : α → β) (hg : Measurable g) :
    tvDist (P.map g) (Q.map g) ≤ tvDist P Q := by
  exact ENNReal.toReal_mono (etvDist_ne_top P Q) (etvDist_map_le P Q g hg)

/-- If the second probability measure has density `f` with respect to the first
on `G`, and `f` is within `δ` of one there, total variation is bounded by the
density error and the mass of the exceptional set.  Nonnegativity of `δ` is
needed when `G` is empty and the density hypotheses are vacuous. -/
theorem tvDist_le_of_density_on_of_nonneg {α : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] (P Q : Measure α) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (G : Set α) (f : α → ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ)
    (hQ : ∀ z ∈ G, (Q {z}).toReal = f z * (P {z}).toReal)
    (hf : ∀ z ∈ G, |f z - 1| ≤ δ) :
    tvDist P Q ≤ 2 * (δ + (P Gᶜ).toReal) := by
  change tvDist P Q ≤ 2 * (δ + P.real Gᶜ)
  rw [tvDist_eq_tsum_abs]
  have hP : Summable fun z => P.real {z} := by
    apply ENNReal.summable_toReal
    rw [show (∑' z, P {z}) = 1 by
      simpa using P.tsum_indicator_apply_singleton Set.univ MeasurableSet.univ]
    simp
  have hQ' : Summable fun z => Q.real {z} := by
    apply ENNReal.summable_toReal
    rw [show (∑' z, Q {z}) = 1 by
      simpa using Q.tsum_indicator_apply_singleton Set.univ MeasurableSet.univ]
    simp
  have hdiff : Summable fun z => P.real {z} - Q.real {z} := hP.sub hQ'
  have hbound : ∀ z, |P.real {z} - Q.real {z}| ≤
      G.indicator (fun z => δ * P.real {z}) z +
        Gᶜ.indicator (fun z => P.real {z} + Q.real {z}) z := by
    intro z
    by_cases hz : z ∈ G
    · have hzc : z ∉ Gᶜ := by simpa
      simp only [Set.indicator_of_mem hz, Set.indicator_of_notMem hzc, add_zero]
      rw [show Q.real {z} = f z * P.real {z} from hQ z hz]
      calc
        |P.real {z} - f z * P.real {z}| = |1 - f z| * P.real {z} := by
          have heq : P.real {z} - f z * P.real {z} = (1 - f z) * P.real {z} := by ring
          rw [heq, abs_mul, abs_of_nonneg measureReal_nonneg]
        _ = |f z - 1| * P.real {z} := by rw [abs_sub_comm]
        _ ≤ δ * P.real {z} := mul_le_mul_of_nonneg_right (hf z hz) ENNReal.toReal_nonneg
    · have hz' : z ∈ Gᶜ := hz
      simp only [Set.indicator_of_notMem hz, Set.indicator_of_mem hz', zero_add]
      calc
        |P.real {z} - Q.real {z}| ≤ |P.real {z}| + |Q.real {z}| := abs_sub _ _
        _ = P.real {z} + Q.real {z} := by
          rw [abs_of_nonneg measureReal_nonneg, abs_of_nonneg measureReal_nonneg]
  calc
    (∑' z, |P.real {z} - Q.real {z}|) ≤
        ∑' z, (G.indicator (fun z => δ * P.real {z}) z +
          Gᶜ.indicator (fun z => P.real {z} + Q.real {z}) z) :=
      hdiff.abs.tsum_le_tsum hbound ((hP.mul_left δ).indicator G |>.add
        ((hP.add hQ').indicator Gᶜ))
    _ = (∑' z, G.indicator (fun z => δ * P.real {z}) z) +
        ∑' z, Gᶜ.indicator (fun z => P.real {z} + Q.real {z}) z :=
      ((hP.mul_left δ).indicator G).tsum_add ((hP.add hQ').indicator Gᶜ)
    _ ≤ 2 * δ + 2 * P.real Gᶜ := by
      have hG : (∑' z, G.indicator (fun z => δ * P.real {z}) z) ≤ δ := by
        calc
          _ = δ * P.real G := by
            rw [← tsum_indicator_measureReal P G, ← tsum_mul_left]
            apply tsum_congr
            intro z
            by_cases hz : z ∈ G <;> simp [Set.indicator, hz]
          _ ≤ δ * 1 := by
            apply mul_le_mul_of_nonneg_left _ hδ
            calc
              P.real G ≤ P.real Set.univ :=
                measureReal_mono (Set.subset_univ G) (measure_ne_top P Set.univ)
              _ = 1 := by simp [Measure.real]
          _ = δ := mul_one δ
      have hGc : (∑' z, Gᶜ.indicator (fun z => P.real {z} + Q.real {z}) z) ≤
          2 * P.real Gᶜ + δ := by
        rw [Set.indicator_add, (hP.indicator Gᶜ).tsum_add (hQ'.indicator Gᶜ),
          tsum_indicator_measureReal, tsum_indicator_measureReal]
        have hQGc : Q.real Gᶜ = 1 - Q.real G := by
          rw [measureReal_compl (Set.to_countable G).measurableSet]
          simp [Measure.real]
        rw [hQGc]
        have hQG_lower : (∑' z, G.indicator (fun z => P.real {z}) z) - δ ≤
            ∑' z, G.indicator (fun z => Q.real {z}) z := by
          calc
            _ ≤ (∑' z, G.indicator (fun z => P.real {z}) z) -
                ∑' z, G.indicator (fun z => δ * P.real {z}) z := sub_le_sub_left hG _
            _ = ∑' z, (G.indicator (fun z => P.real {z}) z -
                G.indicator (fun z => δ * P.real {z}) z) :=
              ((hP.indicator G).tsum_sub ((hP.mul_left δ).indicator G)).symm
            _ ≤ _ := by
              have hs : Summable (fun z => G.indicator (fun z => P.real {z}) z -
                  G.indicator (fun z => δ * P.real {z}) z) := by
                convert (hP.sub (hP.mul_left δ)).indicator G using 1
                funext z
                by_cases hz : z ∈ G <;> simp [Set.indicator, hz]
              apply hs.tsum_le_tsum _ (hQ'.indicator G)
              intro z
              by_cases hz : z ∈ G
              · simp only [Set.indicator_of_mem hz]
                rw [show Q.real {z} = f z * P.real {z} from hQ z hz]
                have habs := abs_le.mp (hf z hz)
                have hp_le : P.real {z} ≤ 1 := by
                  calc
                    P.real {z} ≤ P.real Set.univ :=
                      measureReal_mono (Set.subset_univ _) (measure_ne_top P Set.univ)
                    _ = 1 := by simp [Measure.real]
                nlinarith [measureReal_nonneg (μ := P) (s := {z})]
              · simp [Set.indicator_of_notMem hz]
        rw [tsum_indicator_measureReal, tsum_indicator_measureReal] at hQG_lower
        have hPGtotal : P.real G + P.real Gᶜ = 1 := by
          have hcompl := measureReal_compl (μ := P) (Set.to_countable G).measurableSet
          simp only [Measure.real, measure_univ, ENNReal.toReal_one] at hcompl
          change P.real Gᶜ = 1 - P.real G at hcompl
          linarith
        linarith
      linarith
    _ = 2 * (δ + P.real Gᶜ) := by ring

end
end SubcriticalCauchy.Bienayme
