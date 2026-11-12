module

public import SubcriticalCauchy.PotterBounds
public import SubcriticalCauchy.LatticeConcentrationAux
import Mathlib.MeasureTheory.Integral.Pi
public import SubcriticalCauchy.LatticeSmallFrequency
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Fourier reduction of lattice concentration

This module proves the inversion bound for the actual finite iid offspring
sum. The quantitative bound `C / (n * L n ^ 2)` remains an open obligation:
it additionally requires small-frequency and off-zero decay estimates.
-/

@[expose] public section

open MeasureTheory AddCircle
open scoped Topology

namespace SubcriticalCauchy.Bienayme

/-- A character takes finite sums to products. -/
theorem lattice_character_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (θ : AddCircle (1 : ℝ)) :
    fourier (∑ i ∈ s, f i) θ = ∏ i ∈ s, fourier (f i) θ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp only [Finset.sum_insert ha, Finset.prod_insert ha, fourier_add, ih]

/-- The Fourier transform of an iid sum is the corresponding power. -/
theorem iid_latticeFourier (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (j : ℕ) (θ : AddCircle (1 : ℝ)) :
    (∫ ω : Fin j → ℕ, fourier ((∑ i, ω i : ℕ) : ℤ) θ
      ∂(Measure.pi fun _ : Fin j => μ)) =
      (∫ k : ℕ, fourier (k : ℤ) θ ∂μ) ^ j := by
  simp_rw [Nat.cast_sum, lattice_character_sum]
  simpa using (integral_fintype_prod_eq_prod (μ := fun _ : Fin j => μ)
    (fun (_ : Fin j) (k : ℕ) => fourier (k : ℤ) θ))

/-- Uniform atom bound for an iid sum, reduced to a single Fourier integral.
The statement includes the empty product law (`j = 0`). -/
theorem iid_lattice_inversion_bound (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (j k : ℕ) :
    ((Measure.pi fun _ : Fin j => μ) {ω | ∑ i, ω i = k}).toReal ≤
      ∫ θ : AddCircle (1 : ℝ), ‖∫ a : ℕ, fourier (a : ℤ) θ ∂μ‖ ^ j
        ∂haarAddCircle := by
  let P := Measure.pi fun _ : Fin j => μ
  let F : (Fin j → ℕ) → ℤ := fun ω => ((∑ i, ω i : ℕ) : ℤ)
  have hF : Measurable F := by fun_prop
  let ν := P.map F
  have hmass : ν {(k : ℤ)} = P {ω | ∑ i, ω i = k} := by
    rw [Measure.map_apply hF (measurableSet_singleton _)]
    congr 1
    ext ω
    change (((∑ i, ω i : ℕ) : ℤ) = (k : ℤ)) ↔ (∑ i, ω i) = k
    exact Nat.cast_inj
  have hchar (θ : AddCircle (1 : ℝ)) : latticeFourier ν θ =
      (∫ a : ℕ, fourier (a : ℤ) θ ∂μ) ^ j := by
    change (∫ z : ℤ, fourier z θ ∂P.map F) = _
    rw [integral_map hF.aemeasurable (measurable_of_countable _).aestronglyMeasurable]
    exact iid_latticeFourier μ j θ
  have hh := lattice_inversion_bound ν (k : ℤ)
  rw [hmass] at hh
  simpa only [hchar, norm_pow] using hh

/-!
## Completion of the quantitative estimate

The declarations below close the obligation left open by the original Fourier
reduction above. The assembly bounds all three frequency regions by a single
Cauchy envelope, avoiding an improper integral of a square-root exponential.
-/

/-- Probability Haar integration expressed in centered real coordinates. -/
theorem haar_integral_eq_centered_interval (f : AddCircle (1 : ℝ) → ℝ) :
    (∫ θ : AddCircle (1 : ℝ), f θ ∂haarAddCircle) =
      ∫ x : ℝ in -(1 / 2)..(1 / 2), f (x : AddCircle (1 : ℝ)) := by
  rw [AddCircle.integral_haarAddCircle]
  convert (AddCircle.intervalIntegral_preimage (1 : ℝ) (-(1 / 2)) f).symm using 1 <;> norm_num

/-- The elementary exponential estimate for powers of a nonnegative modulus. -/
theorem pow_le_exp_sq_defect {r : ℝ} (hr : 0 ≤ r) (j : ℕ) :
    r ^ j ≤ Real.exp (-((j : ℝ) / 2) * (1 - r ^ 2)) := by
  by_cases hzero : r = 0
  · subst r
    cases j with
    | zero => simp
    | succ j => simpa using (Real.exp_pos (-(((j + 1 : ℕ) : ℝ) / 2))).le
  have hr0 : 0 < r := lt_of_le_of_ne hr (Ne.symm hzero)
  have hh := Real.log_le_sub_one_of_pos (sq_pos_of_pos hr0)
  rw [Real.log_pow] at hh
  have hlog : Real.log r ≤ -(1 - r ^ 2) / 2 := by norm_num at hh; linarith
  calc
    r ^ j = Real.exp ((j : ℝ) * Real.log r) := by rw [Real.exp_nat_mul, Real.exp_log hr0]
    _ ≤ _ := Real.exp_le_exp.mpr (by
      have := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg j)
      nlinarith)

/-- An exponential controls each polynomial with its factorial constant. -/
theorem pow_mul_exp_neg_le_factorial {s : ℝ} (hs : 0 ≤ s) (q : ℕ) :
    s ^ q * Real.exp (-s) ≤ (q.factorial : ℝ) := by
  have hh := mul_le_mul_of_nonneg_right (Real.pow_div_factorial_le_exp s hs q)
    (Real.exp_pos (-s)).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hh
  have hfac : 0 < (q.factorial : ℝ) := by positivity
  have heq : s ^ q / (q.factorial : ℝ) * Real.exp (-s) =
      (s ^ q * Real.exp (-s)) / (q.factorial : ℝ) := by ring
  rw [heq] at hh
  exact (div_le_iff₀ hfac).mp hh |>.trans_eq (one_mul _)

/-- A Cauchy-shaped envelope integrates to a constant divided by its scale.
This form avoids an improper integral of an exponential of a square root. -/
theorem haar_integral_le_of_cauchy_weight (f : AddCircle (1 : ℝ) → ℝ)
    (hf : Continuous f) {A D : ℝ} (hA : 0 < A) (hD : 0 ≤ D)
    (hbound : ∀ x : ℝ, |x| ≤ 1 / 2 →
      f (x : AddCircle (1 : ℝ)) * (1 + (A * x) ^ 2) ≤ D) :
    (∫ θ : AddCircle (1 : ℝ), f θ ∂haarAddCircle) ≤ D * Real.pi / A := by
  have hfr : Continuous (fun x : ℝ => f (x : AddCircle (1 : ℝ))) :=
    hf.comp (AddCircle.continuous_mk' _)
  have hg : Continuous (fun x : ℝ => D * (1 + (A * x) ^ 2)⁻¹) := by
    have hi : Continuous (fun x : ℝ => 1 + (A * x) ^ 2) := by fun_prop
    exact continuous_const.mul (hi.inv₀ (fun x => ne_of_gt (by positivity)))
  rw [haar_integral_eq_centered_interval]
  calc
    _ ≤ ∫ x : ℝ in -(1 / 2)..(1 / 2), D * (1 + (A * x) ^ 2)⁻¹ := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (hfr.intervalIntegrable _ _) (hg.intervalIntegrable _ _)
      intro x hx
      have hh := hbound x (abs_le.mpr hx)
      exact (le_div_iff₀ (by positivity : 0 < 1 + (A * x) ^ 2)).mpr hh
    _ = D * (A⁻¹ * (Real.arctan (A * (1 / 2)) - Real.arctan (A * (-(1 / 2))))) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_mul_left (fun y : ℝ => (1 + y ^ 2)⁻¹) hA.ne',
        integral_inv_one_add_sq]
      rfl
    _ ≤ D * (A⁻¹ * Real.pi) := by
      apply mul_le_mul_of_nonneg_left _ hD
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hA.le)
      linarith [Real.arctan_lt_pi_div_two (A * (1 / 2)),
        Real.neg_pi_div_two_lt_arctan (A * (-(1 / 2)))]
    _ = _ := by ring

/-- Potter converts the small-frequency defect to the square-root decay scale. -/
theorem lattice_middle_decay {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x) {c C N : ℝ}
    (hc : 0 < c) (hC : 0 < C)
    (hpot : ∀ u v : ℝ, N ≤ u → u ≤ v → L v / L u ≤ C * (v / u) ^ (1 / 2 : ℝ))
    {n j : ℕ} (hn : 0 < n) (hnj : n ≤ 3 * j) {x r : ℝ} (hr : 0 ≤ r)
    (hx : 0 < |x|) (hxn : 1 / (n : ℝ) ≤ |x|) (hxN : N ≤ 1 / |x|)
    (hdef : c * |x| * L (1 / |x|) ≤ 1 - r ^ 2) :
    r ^ j ≤ Real.exp (-(c / (6 * C)) * L n * Real.sqrt ((n : ℝ) * |x|)) := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hun : 1 / |x| ≤ (n : ℝ) := (div_le_iff₀ hx).mpr
    (by have := (div_le_iff₀ hnR).mp hxn; nlinarith)
  have hLu : 0 < L (1 / |x|) := hpos _ (by positivity)
  have hdef0 : 0 ≤ 1 - r ^ 2 := (by positivity : 0 ≤ c * |x| * L (1 / |x|)).trans hdef
  have hp := hpot (1 / |x|) n hxN hun
  have hdiv : (n : ℝ) / (1 / |x|) = (n : ℝ) * |x| := by simp [div_eq_mul_inv]
  rw [hdiv, ← Real.sqrt_eq_rpow] at hp
  have hcomp := (div_le_iff₀ hLu).mp hp
  have hs : (Real.sqrt ((n : ℝ) * |x|)) ^ 2 = (n : ℝ) * |x| :=
    Real.sq_sqrt (by positivity)
  have hκ : 0 < c / (6 * C) := by positivity
  have he : c / (6 * C) * L n * Real.sqrt ((n : ℝ) * |x|) ≤
      (j : ℝ) / 2 * (1 - r ^ 2) := by
    calc
      _ ≤ c / (6 * C) * Real.sqrt ((n : ℝ) * |x|) *
          (C * Real.sqrt ((n : ℝ) * |x|) * L (1 / |x|)) := by
        have hh := mul_le_mul_of_nonneg_left hcomp
          (show 0 ≤ c / (6 * C) * Real.sqrt ((n : ℝ) * |x|) by positivity)
        nlinarith
      _ = (n : ℝ) / 6 * (c * |x| * L (1 / |x|)) := by
        calc
          _ = c / (6 * C) * C * L (1 / |x|) * (Real.sqrt ((n : ℝ) * |x|)) ^ 2 := by ring
          _ = _ := by rw [hs]; field_simp
      _ ≤ (n : ℝ) / 6 * (1 - r ^ 2) :=
        mul_le_mul_of_nonneg_left hdef (by positivity)
      _ ≤ (j : ℝ) / 2 * (1 - r ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hh : (n : ℝ) ≤ 3 * (j : ℝ) := by exact_mod_cast hnj
        linarith
  exact (pow_le_exp_sq_defect hr j).trans (Real.exp_le_exp.mpr (by linarith))

/-- Square-root exponential decay admits a Cauchy envelope at scale `n l²`. -/
theorem cauchy_weight_of_sqrt_decay {n l κ x b : ℝ}
    (hn : 0 ≤ n) (hl : 0 ≤ l) (hκ : 0 < κ)
    (hb : b ≤ Real.exp (-κ * l * Real.sqrt (n * |x|))) :
    b * (1 + (n * l ^ 2 * x) ^ 2) ≤ 1 + 24 / κ ^ 4 := by
  let s := κ * l * Real.sqrt (n * |x|)
  have hs : 0 ≤ s := by positivity
  have hs4 : s ^ 4 = κ ^ 4 * (n * l ^ 2 * x) ^ 2 := by
    calc
      _ = κ ^ 4 * l ^ 4 * ((Real.sqrt (n * |x|)) ^ 2) ^ 2 := by dsimp [s]; ring
      _ = _ := by rw [Real.sq_sqrt (by positivity), mul_pow, sq_abs]; ring
  have hpoly := pow_mul_exp_neg_le_factorial hs 4
  norm_num at hpoly
  have hscaled : (n * l ^ 2 * x) ^ 2 * Real.exp (-s) ≤ 24 / κ ^ 4 := by
    calc
      _ = (s ^ 4 * Real.exp (-s)) / κ ^ 4 := by rw [hs4]; field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hpoly (by positivity)
  have hexp : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hb' : b ≤ Real.exp (-s) := by simpa [s, neg_mul] using hb
  have hh := mul_le_mul_of_nonneg_right hb' (show 0 ≤ 1 + (n * l ^ 2 * x) ^ 2 by positivity)
  nlinarith

/-- Linear exponential decay gives the same envelope when the local model is bounded. -/
theorem cauchy_weight_of_linear_decay {n l β x b : ℝ}
    (hn : 0 ≤ n) (hl : 0 ≤ l) (hl1 : l ≤ 1) (hβ : 0 < β) (hx : |x| ≤ 1)
    (hb : b ≤ Real.exp (-β * n)) :
    b * (1 + (n * l ^ 2 * x) ^ 2) ≤ 1 + 2 / β ^ 2 := by
  have hl2 : l ^ 2 ≤ 1 := by nlinarith
  have habs : |n * l ^ 2 * x| ≤ n := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ n * l ^ 2)]
    calc
      n * l ^ 2 * |x| ≤ n * 1 * 1 := by gcongr
      _ = n := by ring
  have hsq : (n * l ^ 2 * x) ^ 2 ≤ n ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hn).mpr habs
  have hpoly := pow_mul_exp_neg_le_factorial (show 0 ≤ β * n by positivity) 2
  norm_num at hpoly
  have hscaled : n ^ 2 * Real.exp (-(β * n)) ≤ 2 / β ^ 2 := by
    calc
      _ = ((β * n) ^ 2 * Real.exp (-(β * n))) / β ^ 2 := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hpoly (by positivity)
  have hexp : Real.exp (-(β * n)) ≤ 1 := Real.exp_le_one_iff.mpr
    (neg_nonpos.mpr (mul_nonneg hβ.le hn))
  have hb' : b ≤ Real.exp (-(β * n)) := by simpa only [neg_mul] using hb
  calc
    _ ≤ Real.exp (-(β * n)) * (1 + (n * l ^ 2 * x) ^ 2) :=
      mul_le_mul_of_nonneg_right hb' (by positivity)
    _ ≤ Real.exp (-(β * n)) * (1 + n ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
    _ ≤ _ := by nlinarith

/-- The Fourier integral concentration estimate, before choosing an atom.
The three frequency regions are bounded by one integrable Cauchy envelope. -/
theorem lattice_fourier_integral_bound
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ < 1)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Filter.Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      Filter.atTop (𝓝 1)) :
    ∃ B : ℝ, ∃ M : ℕ, ∀ n : ℕ, M ≤ n → ∀ j : ℕ, n ≤ 3 * j → 3 * j ≤ 2 * n →
      (∫ θ : AddCircle (1 : ℝ), ‖latticeFourier (offspringIntegerLaw μ) θ‖ ^ j ∂haarAddCircle) ≤
        B / ((n : ℝ) * L n ^ 2) := by
  obtain ⟨c, hc, x₀, hx₀, hsmall⟩ := lattice_small_frequency μ hm hpos hL hsv hlocal
  obtain ⟨C, hC, N, hN, hpot⟩ := potter_bounds hpos hL hsv (1 / 2) (by norm_num)
  let δ := min x₀ (min (1 / N) (1 / 2))
  have hδ : 0 < δ := lt_min hx₀ (lt_min (by positivity) (by norm_num))
  have hδx₀ : δ ≤ x₀ := min_le_left _ _
  have hδN : δ ≤ 1 / N := (min_le_right _ _).trans (min_le_left _ _)
  obtain ⟨ρ, hρ0, hρ1, hgap⟩ := offspring_lattice_spectral_gap μ hm hpos hL hsv hlocal δ hδ
  have hρsq : ρ ^ 2 < 1 := by
    simpa only [one_pow] using (sq_lt_sq₀ hρ0 zero_le_one).mpr hρ1
  let κ := c / (6 * C)
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
  have hzero := localModel_tendsto_zero μ hm hpos hL hsv hlocal
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp
    (hzero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  refine ⟨D * Real.pi, max K 1, ?_⟩
  -- The requested upper sample-size comparison is retained; the proof only
  -- needs the lower comparison, because increasing the power improves decay.
  intro n hn j hnj _hjn
  have hn1 : 1 ≤ n := (le_max_right K 1).trans hn
  have hn0 : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn0
  have hLn : 0 < L n := hpos _ hnR
  have hLn1 : L n ≤ 1 := (hK n ((le_max_left K 1).trans hn)).le
  have hLn2 : L n ^ 2 ≤ 1 := by nlinarith
  let A := (n : ℝ) * L n ^ 2
  have hA : 0 < A := by dsimp [A]; positivity
  apply haar_integral_le_of_cauchy_weight
    (fun θ => ‖latticeFourier (offspringIntegerLaw μ) θ‖ ^ j)
    ((continuous_latticeFourier _).norm.pow j) hA (by linarith : 0 ≤ D)
  intro x hxb
  have hr0 : 0 ≤ ‖latticeFourier (offspringIntegerLaw μ) (x : AddCircle (1 : ℝ))‖ := norm_nonneg _
  have hr1 := norm_latticeFourier_le_one (offspringIntegerLaw μ) (x : AddCircle (1 : ℝ))
  by_cases hnear : |x| ≤ 1 / (n : ℝ)
  · have hnx : (n : ℝ) * |x| ≤ 1 := by
      have hh := (le_div_iff₀ hnR).mp hnear
      nlinarith
    have habs : |A * x| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg hA.le]
      calc
        A * |x| = L n ^ 2 * ((n : ℝ) * |x|) := by dsimp [A]; ring
        _ ≤ 1 * 1 := mul_le_mul hLn2 hnx (by positivity) (by norm_num)
        _ = 1 := one_mul _
    have hsq : (A * x) ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr habs
    have hp : ‖latticeFourier (offspringIntegerLaw μ) (x : AddCircle (1 : ℝ))‖ ^ j ≤ 1 :=
      pow_le_one₀ hr0 hr1
    have hh := mul_le_mul_of_nonneg_right hp (show 0 ≤ 1 + (A * x) ^ 2 by positivity)
    calc
      _ ≤ 1 * (1 + (A * x) ^ 2) := hh
      _ ≤ 2 := by nlinarith only [hsq]
      _ ≤ D := hD2
  · have hx : 0 < |x| := (by positivity : (0 : ℝ) < 1 / (n : ℝ)).trans (lt_of_not_ge hnear)
    by_cases hmiddle : |x| ≤ δ
    · have hxN : N ≤ 1 / |x| := (le_div_iff₀ hx).mpr (by
        have hh := (le_div_iff₀ hN).mp (hmiddle.trans hδN)
        nlinarith)
      have hdec := lattice_middle_decay hpos hc hC
        (fun u v hu huv => (hpot u v hu huv).2) hn0 hnj hr0 hx
        (le_of_not_ge hnear) hxN (hsmall x hx (hmiddle.trans hδx₀))
      exact (cauchy_weight_of_sqrt_decay hnR.le hLn.le hκ hdec).trans hDm
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
      exact (cauchy_weight_of_linear_decay hnR.le hLn.le hLn1 hβ
        (hxb.trans (by norm_num)) hdec).trans hDo

/-- Uniform lattice concentration for iid offspring sums at comparable sample sizes. -/
theorem lattice_concentration
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ < 1)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Filter.Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      Filter.atTop (𝓝 1)) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, n ≤ 3 * j → 3 * j ≤ 2 * n →
      ∀ k : ℕ, ((Measure.pi fun _ : Fin j => μ) {ω | ∑ i, ω i = k}).toReal ≤
        C / ((n : ℝ) * L n ^ 2) := by
  obtain ⟨C, N, hbound⟩ := lattice_fourier_integral_bound μ hm hpos hL hsv hlocal
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

end SubcriticalCauchy.Bienayme
