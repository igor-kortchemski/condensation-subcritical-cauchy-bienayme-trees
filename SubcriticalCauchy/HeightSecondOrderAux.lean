module

public import SubcriticalCauchy.HeightSecondOrderRecurrence

/-!
# Real thresholds rounded to natural generations

Generic analytic lemmas used to compose survival asymptotics with rounded
second-order height thresholds.
-/

@[expose] public section

open MeasureTheory Filter Finset
open scoped ENNReal Topology BigOperators

namespace SubcriticalCauchy.Bienayme

noncomputable section
open BGW BGW.LocallyFinite

variable {μ : Measure ℕ} [IsProbabilityMeasure μ]

/-- Exact logarithmic formula after rounding a real height. -/
theorem log_nat_mul_survival_ceil (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm0 : 0 < offspringMean μ) (hmfin : offspringMean μ ≠ ∞) {n : ℕ} (hn : 0 < n) (h : ℝ) :
    Real.log ((n : ℝ) * (survival μ ⌈h⌉₊).toReal) =
      Real.log n + (⌈h⌉₊ : ℝ) * Real.log (offspringMean μ).toReal +
        Real.log (normalizedSurvival μ ⌈h⌉₊) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hQ : (survival μ ⌈h⌉₊).toReal ≠ 0 := (survival_toReal_pos μ hm0 _).ne'
  have hm : (offspringMean μ).toReal ≠ 0 := (ENNReal.toReal_pos hm0.ne' hmfin).ne'
  rw [Real.log_mul hn0 hQ]
  simp only [normalizedSurvival, Real.log_div hQ (pow_ne_zero _ hm), Real.log_pow]
  ring


/-- The rounding error `⌈h⌉₊ - h` is negligible against any divergent scale. -/
theorem ceil_sub_div_tendsto_zero {h d : ℕ → ℝ} (hd : Tendsto d atTop atTop)
    (hh : ∀ᶠ n in atTop, 0 ≤ h n) :
    Tendsto (fun n => ((⌈h n⌉₊ : ℝ) - h n) / d n) atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards [hd.eventually_gt_atTop 0] with n hd0
    exact div_nonneg (sub_nonneg.mpr (Nat.le_ceil _)) hd0.le
  · filter_upwards [hd.eventually_gt_atTop 0, hh] with n hd0 hn
    exact (div_le_div_iff_of_pos_right hd0).mpr
      (by linarith [Nat.ceil_lt_add_one hn] : ((⌈h n⌉₊ : ℝ) - h n) ≤ 1)
  · exact hd.const_div_atTop 1

/-- Rounding preserves a threshold asymptotic to a divergent real baseline. -/
theorem ceil_div_tendsto_one {h b : ℕ → ℝ} (hb : Tendsto b atTop atTop)
    (hh : ∀ᶠ n in atTop, 0 ≤ h n)
    (hdiv : Tendsto (fun n => h n / b n) atTop (𝓝 1)) :
    Tendsto (fun n => (⌈h n⌉₊ : ℝ) / b n) atTop (𝓝 1) := by
  have he := ceil_sub_div_tendsto_zero hb hh
  have hh := hdiv.add he
  rw [add_zero] at hh
  apply hh.congr'
  filter_upwards [hb.eventually_ne_atTop 0] with n hb0
  field_simp
  ring

/-- Composition of `log u_k / log k` with a logarithmic real threshold. -/
theorem log_normalizedSurvival_ceil_div_loglog
    (h : ℕ → ℝ) {a D : ℝ} (ha : 0 < a)
    (hhTop : Tendsto h atTop atTop)
    (hratio : Tendsto (fun n : ℕ => h n / (Real.log n / a)) atTop (𝓝 1))
    (hU : Tendsto (fun n : ℕ => Real.log (normalizedSurvival μ n) / Real.log n)
      atTop (𝓝 D)) :
    Tendsto (fun n : ℕ => Real.log (normalizedSurvival μ ⌈h n⌉₊) /
      Real.log (Real.log n)) atTop (𝓝 D) := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto (fun n : ℕ => Real.log (Real.log n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hb : Tendsto (fun n : ℕ => Real.log n / a) atTop atTop :=
    (by simpa [div_eq_mul_inv, mul_comm] using
      hlog.const_mul_atTop (div_pos zero_lt_one ha))
  have hceil := ceil_div_tendsto_one hb (hhTop.eventually_ge_atTop 0) hratio
  have hkTop : Tendsto (fun n : ℕ => ⌈h n⌉₊) atTop atTop :=
    tendsto_nat_ceil_atTop.comp hhTop
  have hbase : Tendsto (fun n : ℕ => Real.log (Real.log n / a) /
      Real.log (Real.log n)) atTop (𝓝 1) := by
    have hz := hloglog.const_div_atTop (Real.log a)
    have hh := (tendsto_const_nhds (x := (1 : ℝ))).sub hz
    rw [sub_zero] at hh
    apply hh.congr'
    filter_upwards [hlog.eventually_gt_atTop 0,
      hloglog.eventually_ne_atTop 0] with n hn hn0
    rw [Real.log_div hn.ne' ha.ne']
    field_simp
  have hlogs : Tendsto (fun n : ℕ => Real.log (⌈h n⌉₊ : ℝ) /
      Real.log (Real.log n)) atTop (𝓝 1) := by
    have hz0 := hceil.log one_ne_zero
    have hz : Tendsto (fun n : ℕ =>
        (Real.log (⌈h n⌉₊ : ℝ) - Real.log (Real.log n / a)) /
          Real.log (Real.log n)) atTop (𝓝 0) := by
      have hh := hz0.div_atTop hloglog
      apply hh.congr'
      filter_upwards [hceil.eventually (Ioi_mem_nhds zero_lt_one),
        hb.eventually_gt_atTop 0] with n hk hn
      have hkpos : 0 < (⌈h n⌉₊ : ℝ) := (div_pos_iff_of_pos_right hn).mp hk
      rw [Real.log_div hkpos.ne' (by positivity)]
    have hh := hbase.add hz
    rw [add_zero] at hh
    apply hh.congr'
    filter_upwards [hloglog.eventually_ne_atTop 0] with n hn
    field_simp
    ring
  have hh := (hU.comp hkTop).mul hlogs
  rw [mul_one] at hh
  apply hh.congr'
  have hklog : Tendsto (fun n : ℕ => Real.log (⌈h n⌉₊ : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hkTop)
  filter_upwards [hklog.eventually_ne_atTop 0,
    hloglog.eventually_ne_atTop 0] with n hk hl
  simp only [Function.comp_apply]
  field_simp

/-- Composition of `log u_k / k^(1-β)` with a logarithmic real threshold. -/
theorem log_normalizedSurvival_ceil_div_log_rpow
    (h : ℕ → ℝ) {a D p : ℝ} (ha : 0 < a) (_hp : 0 ≤ p)
    (hhTop : Tendsto h atTop atTop)
    (hratio : Tendsto (fun n : ℕ => h n / (Real.log n / a)) atTop (𝓝 1))
    (hU : Tendsto (fun n : ℕ => Real.log (normalizedSurvival μ n) / (n : ℝ) ^ p)
      atTop (𝓝 D)) :
    Tendsto (fun n : ℕ => Real.log (normalizedSurvival μ ⌈h n⌉₊) /
      Real.log n ^ p) atTop (𝓝 (D * (1 / a) ^ p)) := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hb : Tendsto (fun n : ℕ => Real.log n / a) atTop atTop :=
    (by simpa [div_eq_mul_inv, mul_comm] using
      hlog.const_mul_atTop (div_pos zero_lt_one ha))
  have hceil := ceil_div_tendsto_one hb (hhTop.eventually_ge_atTop 0) hratio
  have hkTop : Tendsto (fun n : ℕ => ⌈h n⌉₊) atTop atTop :=
    tendsto_nat_ceil_atTop.comp hhTop
  have hklog : Tendsto (fun n : ℕ => (⌈h n⌉₊ : ℝ) / Real.log n)
      atTop (𝓝 (1 / a)) := by
    have hh := hceil.div_const a
    rw [one_div] at hh
    rw [one_div]
    apply hh.congr'
    filter_upwards [hlog.eventually_ne_atTop 0] with n hn
    field_simp [ha.ne']
  have hpow : Tendsto (fun n : ℕ => ((⌈h n⌉₊ : ℝ) / Real.log n) ^ p)
      atTop (𝓝 ((1 / a) ^ p)) := hklog.rpow_const (Or.inl (by positivity : (1 : ℝ) / a ≠ 0))
  have hh := (hU.comp hkTop).mul hpow
  apply hh.congr'
  filter_upwards [hkTop.eventually_gt_atTop (0 : ℕ),
    hlog.eventually_gt_atTop 0] with n hk hn
  have hk0 : (0 : ℝ) < ⌈h n⌉₊ := by exact_mod_cast hk
  simp only [Function.comp_apply]
  rw [Real.div_rpow hk0.le hn.le]
  field_simp

end
end SubcriticalCauchy.Bienayme
