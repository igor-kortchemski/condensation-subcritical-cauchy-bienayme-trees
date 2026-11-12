module

public import SubcriticalCauchy.LatticeConcentration
public import SubcriticalCauchy.IncrementTailAsymptotics
public import SubcriticalCauchy.DeletedIncrements

/-!
# Sharp lattice concentration at the Cauchy scaling sequence

This module sharpens the middle-frequency estimate in `LatticeConcentration`
to the scale `a n`, where `n * incrementTail μ (a n) → 1`.  The same Cauchy
envelope is used in all three Fourier regions; the middle estimate now compares
`L (1 / |x|)` with `L (a n)` instead of `L n`.
-/

@[expose] public section

open MeasureTheory AddCircle Filter
open scoped Topology

namespace SubcriticalCauchy.Bienayme

/-- Potter comparison at the scale `a`, followed by the defining scale
asymptotic, gives square-root exponential decay at frequency scale `1 / a`. -/
theorem berger_middle_decay {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x) {c C N A : ℝ}
    (hc : 0 < c) (hC : 0 < C) (hA : 0 < A)
    (hpot : ∀ u v : ℝ, N ≤ u → u ≤ v → L v / L u ≤ C * (v / u) ^ (1 / 2 : ℝ))
    {n j : ℕ} (hn : 0 < n) (hnj : n ≤ 3 * j) (hscale : A / 2 ≤ (n : ℝ) * L A)
    {x r : ℝ} (hr : 0 ≤ r) (hx : 0 < |x|) (hxa : 1 / A ≤ |x|)
    (hxN : N ≤ 1 / |x|) (hdef : c * |x| * L (1 / |x|) ≤ 1 - r ^ 2) :
    r ^ j ≤ Real.exp (-(c / (12 * C)) * Real.sqrt (A * |x|)) := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hua : 1 / |x| ≤ A := (div_le_iff₀ hx).mpr
    (by have := (div_le_iff₀ hA).mp hxa; nlinarith)
  have hLu : 0 < L (1 / |x|) := hpos _ (by positivity)
  have hLA : 0 < L A := hpos _ hA
  have hdef0 : 0 ≤ 1 - r ^ 2 :=
    (by positivity : 0 ≤ c * |x| * L (1 / |x|)).trans hdef
  have hp := hpot (1 / |x|) A hxN hua
  have hdiv : A / (1 / |x|) = A * |x| := by simp [div_eq_mul_inv]
  rw [hdiv, ← Real.sqrt_eq_rpow] at hp
  have hcomp : L A ≤ C * Real.sqrt (A * |x|) * L (1 / |x|) :=
    (div_le_iff₀ hLu).mp hp
  have hs : (Real.sqrt (A * |x|)) ^ 2 = A * |x| := Real.sq_sqrt (by positivity)
  have he : c / (12 * C) * Real.sqrt (A * |x|) ≤
      (j : ℝ) / 2 * (1 - r ^ 2) := by
    calc
      _ = A / 2 * (c / (6 * C * A) * Real.sqrt (A * |x|)) := by
        field_simp
        ring
      _ ≤ ((n : ℝ) * L A) * (c / (6 * C * A) * Real.sqrt (A * |x|)) :=
        mul_le_mul_of_nonneg_right hscale (by positivity)
      _ = c / (6 * C) * ((n : ℝ) / A) * Real.sqrt (A * |x|) * L A := by
        field_simp
      _ ≤ c / (6 * C) * ((n : ℝ) / A) * Real.sqrt (A * |x|) *
          (C * Real.sqrt (A * |x|) * L (1 / |x|)) :=
        mul_le_mul_of_nonneg_left hcomp (by positivity)
      _ = (n : ℝ) / 6 * (c * |x| * L (1 / |x|)) := by
        calc
          _ = c / (6 * C) * ((n : ℝ) / A) * C * L (1 / |x|) *
              (Real.sqrt (A * |x|)) ^ 2 := by ring
          _ = _ := by rw [hs]; field_simp
      _ ≤ (n : ℝ) / 6 * (1 - r ^ 2) :=
        mul_le_mul_of_nonneg_left hdef (by positivity)
      _ ≤ (j : ℝ) / 2 * (1 - r ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ hdef0
        have hh : (n : ℝ) ≤ 3 * (j : ℝ) := by exact_mod_cast hnj
        linarith
  exact (pow_le_exp_sq_defect hr j).trans (Real.exp_le_exp.mpr (by linarith))

/-- Fourier integral bound at the scaling sequence `a n`. -/
theorem berger_fourier_integral_bound
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ < 1)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1))
    {a : ℕ → ℝ}
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) :
    ∃ B : ℝ, ∃ M : ℕ, ∀ n : ℕ, M ≤ n → ∀ j : ℕ, n ≤ 3 * j → j ≤ n →
      (∫ θ : AddCircle (1 : ℝ), ‖latticeFourier (offspringIntegerLaw μ) θ‖ ^ j
        ∂haarAddCircle) ≤ B / a n := by
  obtain ⟨c, hc, x₀, hx₀, hsmall⟩ := lattice_small_frequency μ hm hpos hL hsv hlocal
  obtain ⟨C, hC, N, hN, hpot⟩ := potter_bounds hpos hL hsv (1 / 2) (by norm_num)
  let δ := min x₀ (min (1 / N) (1 / 2))
  have hδ : 0 < δ := lt_min hx₀ (lt_min (by positivity) (by norm_num))
  have hδx₀ : δ ≤ x₀ := min_le_left _ _
  have hδN : δ ≤ 1 / N := (min_le_right _ _).trans (min_le_left _ _)
  obtain ⟨ρ, hρ0, hρ1, hgap⟩ :=
    offspring_lattice_spectral_gap μ hm hpos hL hsv hlocal δ hδ
  have hρsq : ρ ^ 2 < 1 := by
    simpa only [one_pow] using (sq_lt_sq₀ hρ0 zero_le_one).mpr hρ1
  let κ := c / (12 * C)
  let β := (1 - ρ ^ 2) / 6
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hβ : 0 < β := by dsimp [β]; positivity
  let D := 2 + (1 + 24 / κ ^ 4) + (1 + 2 / β ^ 2)
  have hDm : 1 + 24 / κ ^ 4 ≤ D := by
    have hh : 0 ≤ 2 / β ^ 2 := by positivity
    dsimp [D]
    linarith
  have hDo : 1 + 2 / β ^ 2 ≤ D := by
    have hh : 0 ≤ 24 / κ ^ 4 := by positivity
    dsimp [D]
    linarith
  have hD2 : 2 ≤ D := by
    have hh : 0 ≤ 2 / β ^ 2 := by positivity
    have hh' : 0 ≤ 24 / κ ^ 4 := by positivity
    dsimp [D]
    linarith
  have hlit : IsSubcriticalCauchyOffspring μ := ⟨hm, L, hpos, hsv, hlocal⟩
  have hat := scaling_tendsto_atTop μ hlit ha
  have hsub := scaling_div_nat_tendsto_zero μ hlit ha
  have hscale := scaling_div_mul_tendsto_one μ hm hpos hL hsv hlocal ha
  have hevent : ∀ᶠ n : ℕ in atTop,
      0 < a n ∧ a n / 2 ≤ (n : ℝ) * L (a n) ∧ a n ≤ (n : ℝ) := by
    filter_upwards [hat.eventually_gt_atTop 0,
      hscale.eventually (gt_mem_nhds (show (1 : ℝ) < 2 by norm_num)),
      hsub.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
      eventually_gt_atTop 0] with n han hsc hsn hn
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hLa : 0 < L (a n) := hpos _ han
    refine ⟨han, ?_, ?_⟩
    · have hh := (div_lt_iff₀ (mul_pos hnR hLa)).mp hsc
      nlinarith
    · have hh := (div_lt_iff₀ hnR).mp hsn
      simpa using hh.le
  obtain ⟨K, hK⟩ := eventually_atTop.mp hevent
  refine ⟨D * Real.pi, max K 1, ?_⟩
  intro n hn j hnj _hjn
  have hn0 : 0 < n := (le_max_right K 1).trans hn
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn0
  obtain ⟨ha0, hascale, han⟩ := hK n ((le_max_left K 1).trans hn)
  apply haar_integral_le_of_cauchy_weight
    (fun θ => ‖latticeFourier (offspringIntegerLaw μ) θ‖ ^ j)
    ((continuous_latticeFourier _).norm.pow j) ha0 (by linarith : 0 ≤ D)
  intro x hxb
  have hr0 : 0 ≤ ‖latticeFourier (offspringIntegerLaw μ) (x : AddCircle (1 : ℝ))‖ :=
    norm_nonneg _
  have hr1 := norm_latticeFourier_le_one (offspringIntegerLaw μ) (x : AddCircle (1 : ℝ))
  by_cases hnear : |x| ≤ 1 / a n
  · have hnx : a n * |x| ≤ 1 := by
      have hh := (le_div_iff₀ ha0).mp hnear
      nlinarith
    have habs : |a n * x| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg ha0.le]
      simpa only [abs_of_nonneg (abs_nonneg x)] using hnx
    have hsq : (a n * x) ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr habs
    have hp : ‖latticeFourier (offspringIntegerLaw μ) (x : AddCircle (1 : ℝ))‖ ^ j ≤ 1 :=
      pow_le_one₀ hr0 hr1
    have hh := mul_le_mul_of_nonneg_right hp (show 0 ≤ 1 + (a n * x) ^ 2 by positivity)
    calc
      _ ≤ 1 * (1 + (a n * x) ^ 2) := hh
      _ ≤ 2 := by nlinarith only [hsq]
      _ ≤ D := hD2
  · have hx : 0 < |x| := (by positivity : (0 : ℝ) < 1 / a n).trans (lt_of_not_ge hnear)
    by_cases hmiddle : |x| ≤ δ
    · have hxN : N ≤ 1 / |x| := (le_div_iff₀ hx).mpr (by
        have hh := (le_div_iff₀ hN).mp (hmiddle.trans hδN)
        nlinarith)
      have hdec := berger_middle_decay hpos hc hC ha0
        (fun u v hu huv => (hpot u v hu huv).2) hn0 hnj hascale hr0 hx
        (le_of_not_ge hnear) hxN (hsmall x hx (hmiddle.trans hδx₀))
      have hw := cauchy_weight_of_sqrt_decay (n := a n) (l := 1) (κ := κ)
        (x := x) (b := ‖latticeFourier (offspringIntegerLaw μ)
          (x : AddCircle (1 : ℝ))‖ ^ j) ha0.le zero_le_one hκ (by simpa [κ] using hdec)
      simpa only [one_pow, mul_one] using hw.trans hDm
    · have hrgap := hgap x (le_of_not_ge hmiddle) hxb
      have hdec : ‖latticeFourier (offspringIntegerLaw μ) (x : AddCircle (1 : ℝ))‖ ^ j ≤
          Real.exp (-β * (n : ℝ)) := by
        calc
          _ ≤ ρ ^ j := pow_le_pow_left₀ hr0 hrgap j
          _ ≤ Real.exp (-((j : ℝ) / 2) * (1 - ρ ^ 2)) := pow_le_exp_sq_defect hρ0 j
          _ ≤ _ := Real.exp_le_exp.mpr (by
            have hnjR : (n : ℝ) ≤ 3 * (j : ℝ) := by exact_mod_cast hnj
            have hh := mul_le_mul_of_nonneg_right hnjR (sub_nonneg.mpr hρsq.le)
            dsimp [β]
            nlinarith)
      let l := Real.sqrt (a n / (n : ℝ))
      have hl0 : 0 ≤ l := Real.sqrt_nonneg _
      have hl1 : l ≤ 1 := by
        dsimp [l]
        rw [Real.sqrt_le_one]
        exact (div_le_iff₀ hnR).mpr (by simpa using han)
      have hnl : (n : ℝ) * l ^ 2 = a n := by
        dsimp [l]
        rw [Real.sq_sqrt (div_nonneg ha0.le hnR.le)]
        field_simp
      have hw := cauchy_weight_of_linear_decay (n := (n : ℝ)) (l := l) (β := β)
        (x := x) (b := ‖latticeFourier (offspringIntegerLaw μ)
          (x : AddCircle (1 : ℝ))‖ ^ j) hnR.le hl0 hl1 hβ
        (hxb.trans (by norm_num)) hdec
      rw [hnl] at hw
      exact hw.trans hDo

/-- Uniform lattice concentration for iid offspring sums at the scale `a n`. -/
theorem offspringSum_concentration_scale
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ < 1)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1))
    {a : ℕ → ℝ}
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, n ≤ 3 * j → j ≤ n →
      ∀ k : ℕ, ((Measure.pi fun _ : Fin j => μ) {ω | ∑ i, ω i = k}).toReal ≤ C / a n := by
  obtain ⟨C, N, hbound⟩ := berger_fourier_integral_bound μ hm hpos hL hsv hlocal ha
  refine ⟨C, N, ?_⟩
  intro n hn j hnj hjn k
  have hchar (θ : AddCircle (1 : ℝ)) : (∫ a : ℕ, fourier (a : ℤ) θ ∂μ) =
      latticeFourier (offspringIntegerLaw μ) θ := by
    symm
    rw [latticeFourier, offspringIntegerLaw, integral_map (by fun_prop)
      (measurable_of_countable _).aestronglyMeasurable]
  have hh := iid_lattice_inversion_bound μ j k
  simp_rw [hchar] at hh
  exact hh.trans (hbound n hn j hnj hjn)

/-- Uniform lattice concentration for iid increment sums at the scale `a n`. -/
theorem incrementSum_concentration_scale
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ < 1)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1))
    {a : ℕ → ℝ}
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, n ≤ 3 * j → j ≤ n →
      ∀ z : ℤ, ((Measure.pi fun _ : Fin j => incrementLaw μ) {x | ∑ i, x i = z}).toReal
        ≤ C / a n := by
  obtain ⟨C, N, hbound⟩ := offspringSum_concentration_scale μ hm hpos hL hsv hlocal ha
  refine ⟨C, N, ?_⟩
  intro n hn j hnj hjn z
  have hpi : (Measure.pi fun _ : Fin j => incrementLaw μ) =
      (Measure.pi fun _ : Fin j => μ).map (fun ω i => (ω i : ℤ) - 1) := by
    symm
    simpa only [incrementLaw] using
      (Measure.pi_map_pi (μ := fun _ : Fin j => μ)
        (f := fun _ : Fin j => fun k : ℕ => (k : ℤ) - 1)
        (fun _ => (measurable_of_countable _).aemeasurable))
  rw [hpi, Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
  by_cases hz : 0 ≤ z + (j : ℤ)
  · let k := (z + (j : ℤ)).toNat
    have hk : (k : ℤ) = z + (j : ℤ) := Int.toNat_of_nonneg hz
    have hevent : (fun (ω : Fin j → ℕ) (i : Fin j) => (ω i : ℤ) - 1) ⁻¹'
        {x | ∑ i, x i = z} = {ω | ∑ i, ω i = k} := by
      ext ω
      change (∑ i, ((ω i : ℤ) - 1)) = z ↔ ∑ i, ω i = k
      have hsum : (∑ i, ((ω i : ℤ) - 1)) = ((∑ i, ω i : ℕ) : ℤ) - (j : ℤ) := by
        simp [Finset.sum_sub_distrib]
      rw [hsum]
      omega
    rw [hevent]
    exact hbound n hn j hnj hjn k
  · have hevent : (fun (ω : Fin j → ℕ) (i : Fin j) => (ω i : ℤ) - 1) ⁻¹'
        {x | ∑ i, x i = z} = ∅ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      have hsum : (∑ i, ((ω i : ℤ) - 1)) = ((∑ i, ω i : ℕ) : ℤ) - (j : ℤ) := by
        simp [Finset.sum_sub_distrib]
      have hnat : 0 ≤ ((∑ i, ω i : ℕ) : ℤ) := by positivity
      rw [hsum] at h
      omega
    rw [hevent]
    simp only [measure_empty, ENNReal.toReal_zero]
    exact ENNReal.toReal_nonneg.trans (hbound n hn j hnj hjn 0)

end SubcriticalCauchy.Bienayme
