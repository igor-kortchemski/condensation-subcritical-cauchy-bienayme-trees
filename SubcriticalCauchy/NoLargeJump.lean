module

public import SubcriticalCauchy.NoLargeJumpAux
public import SubcriticalCauchy.LatticeConcentration

/-!
# No large offspring jump at the bridge endpoint

At the endpoint the two halves of the offspring family cannot both have small
centred excess. The half with large excess is controlled by the truncated
exponential bound, while the other half is controlled by lattice
concentration.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology ENNReal BigOperators

namespace SubcriticalCauchy.Bienayme

/-- At the bridge endpoint, the probability that every offspring is at most
`c * n` is negligible compared with `L n / n`, for every sufficiently small
positive cutoff `c`. -/
theorem endpoint_no_large_jump
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ < 1)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2)) atTop (𝓝 1))
    (c : ℝ) (hc : 0 < c) (hcγ : c ≤ (1 - (offspringMean μ).toReal) / 64) :
    Tendsto (fun n : ℕ =>
        ((Measure.pi fun _ : Fin n => μ)
          {ω | ∑ i, ω i = n - 1 ∧ ∀ i, (ω i : ℝ) ≤ c * n}).toReal / (L n / n))
      atTop (𝓝 0) := by
  have hmfin : offspringMean μ ≠ ∞ := ne_top_of_lt (hm.trans ENNReal.one_lt_top)
  have hm1 : (offspringMean μ).toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hmfin ENNReal.one_ne_top).mpr hm
  let γ : ℝ := 1 - (offspringMean μ).toReal
  let a : ℝ := γ / 4
  have hγ : 0 < γ := sub_pos.mpr hm1
  have ha : 0 < a := div_pos hγ (by norm_num)
  have hexponent : (8 : ℝ) ≤ a / (2 * c) := by
    rw [le_div_iff₀ (mul_pos (by norm_num) hc)]
    dsimp [a, γ] at hcγ ⊢
    nlinarith
  have hL0 : Tendsto (fun n : ℕ => L n) atTop (𝓝 0) :=
    localModel_tendsto_zero μ hm hpos hL hsv hlocal
  have hL1 : ∀ᶠ n : ℕ in atTop, L n < 1 :=
    hL0.eventually (gt_mem_nhds zero_lt_one)
  have htrunc := truncated_exponential_bound μ hm hpos hL hsv hlocal a c ha hc
  obtain ⟨C, N, hconcentration⟩ :=
    lattice_concentration μ hm hpos hL hsv hlocal
  obtain ⟨Nγ, hNγ⟩ := exists_nat_ge (2 / γ)
  have hbound : ∀ᶠ n : ℕ in atTop,
      ((Measure.pi fun _ : Fin n => μ)
        {ω | ∑ i, ω i = n - 1 ∧ ∀ i, (ω i : ℝ) ≤ c * n}).toReal ≤
        2 * (Real.exp 1 * C) * L n ^ 6 / (n : ℝ) := by
    filter_upwards [htrunc, hL1, eventually_ge_atTop N, eventually_ge_atTop Nγ,
      eventually_ge_atTop 3] with n htr hLn1 hnN hnNγ hn3
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hLn : 0 < L n := hpos _ hn0
    have hnreal : 2 / γ ≤ (n : ℝ) := hNγ.trans (Nat.cast_le.mpr hnNγ)
    have hγn : 1 ≤ γ * (n : ℝ) / 2 := by
      have hh := (div_le_iff₀ hγ).mp hnreal
      nlinarith
    have hblock : ∀ j k : ℕ, n = j + k → n ≤ 3 * j → 3 * j ≤ 2 * n →
        n ≤ 3 * k → 3 * k ≤ 2 * n →
        ((Measure.pi fun _ : Fin n => μ)
          {ω | ∑ i, ω i = n - 1 ∧ ∀ i, (ω i : ℝ) ≤ c * n}).toReal ≤
          2 * (Real.exp 1 * C) * L n ^ 6 / (n : ℝ) := by
      intro j k hjk hnj hjn hnk hkn
      subst n
      let A : Set (Fin (j + k) → ℕ) :=
        {ω | ∑ i, ω i = j + k - 1 ∧ ∀ i, (ω i : ℝ) ≤ c * ((j + k : ℕ) : ℝ)}
      let B1 : Set ((Fin j → ℕ) × (Fin k → ℕ)) :=
        {p | a * ((j + k : ℕ) : ℝ) ≤ (∑ i, (p.1 i : ℝ)) - (offspringMean μ).toReal * j ∧
          (∑ i, p.1 i) + (∑ i, p.2 i) = j + k - 1 ∧
          (∀ i, (p.1 i : ℝ) ≤ c * ((j + k : ℕ) : ℝ)) ∧ ∀ i, (p.2 i : ℝ) ≤ c * ((j + k : ℕ) : ℝ)}
      let B2 : Set ((Fin j → ℕ) × (Fin k → ℕ)) :=
        {p | a * ((j + k : ℕ) : ℝ) ≤ (∑ i, (p.2 i : ℝ)) - (offspringMean μ).toReal * k ∧
          (∑ i, p.1 i) + (∑ i, p.2 i) = j + k - 1 ∧
          (∀ i, (p.1 i : ℝ) ≤ c * ((j + k : ℕ) : ℝ)) ∧ ∀ i, (p.2 i : ℝ) ≤ c * ((j + k : ℕ) : ℝ)}
      have hpow : L ((j + k : ℕ) : ℝ) ^ (a / (2 * c)) ≤ L ((j + k : ℕ) : ℝ) ^ (8 : ℕ) := by
        have hh := Real.rpow_le_rpow_of_exponent_ge hLn hLn1.le hexponent
        convert hh using 1; norm_num
      have hfirst (j' : ℕ) (hj' : j' ≤ j + k) :
          ((Measure.pi fun _ : Fin j' => μ)
            {ω | a * ((j + k : ℕ) : ℝ) ≤ (∑ i, (ω i : ℝ)) -
                (offspringMean μ).toReal * j' ∧
              (∑ i, ω i) < j + k ∧ ∀ i, (ω i : ℝ) ≤ c * ((j + k : ℕ) : ℝ)}).toReal ≤
            Real.exp 1 * L ((j + k : ℕ) : ℝ) ^ 8 := by
        calc
          _ ≤ ((Measure.pi fun _ : Fin j' => μ)
              {ω | a * ((j + k : ℕ) : ℝ) ≤ (∑ i, (ω i : ℝ)) -
                  (offspringMean μ).toReal * j' ∧
                ∀ i, (ω i : ℝ) ≤ c * ((j + k : ℕ) : ℝ)}).toReal := by
            apply ENNReal.toReal_mono (measure_ne_top _ _)
            apply measure_mono
            intro ω hω
            exact ⟨hω.1, hω.2.2⟩
          _ ≤ Real.exp 1 * L ((j + k : ℕ) : ℝ) ^ (a / (2 * c)) := htr j' hj'
          _ ≤ Real.exp 1 * L ((j + k : ℕ) : ℝ) ^ (8 : ℕ) :=
            mul_le_mul_of_nonneg_left hpow (Real.exp_pos 1).le
      have hB1 : (((Measure.pi fun _ : Fin j => μ).prod
          (Measure.pi fun _ : Fin k => μ)) B1).toReal ≤
          (Real.exp 1 * L ((j + k : ℕ) : ℝ) ^ 8) *
            (C / (((j + k : ℕ) : ℝ) * L ((j + k : ℕ) : ℝ) ^ 2)) := by
        exact measureReal_first_block_le μ j k (j + k) (by omega) a c
          (offspringMean μ).toReal _ _ (hfirst j (by omega))
          (fun s => hconcentration (j + k) hnN k hnk hkn s)
      have hB2 : (((Measure.pi fun _ : Fin j => μ).prod
          (Measure.pi fun _ : Fin k => μ)) B2).toReal ≤
          (Real.exp 1 * L ((j + k : ℕ) : ℝ) ^ 8) *
            (C / (((j + k : ℕ) : ℝ) * L ((j + k : ℕ) : ℝ) ^ 2)) := by
        exact measureReal_second_block_le μ j k (j + k) (by omega) a c
          (offspringMean μ).toReal _ _ (hfirst k (by omega))
          (fun s => hconcentration (j + k) hnN j hnj hjn s)
      have hsplit : iidBlockEquiv j k ⁻¹' A ⊆ B1 ∪ B2 := by
        intro p hp
        change (∑ i, iidBlockEquiv j k p i) = j + k - 1 ∧
          ∀ i, (iidBlockEquiv j k p i : ℝ) ≤ c * ((j + k : ℕ) : ℝ) at hp
        have htotal : (∑ i, p.1 i) + (∑ i, p.2 i) = j + k - 1 := by
          simpa only [sum_iidBlockEquiv] using hp.1
        have hmax : (∀ i, (p.1 i : ℝ) ≤ c * ((j + k : ℕ) : ℝ)) ∧
            ∀ i, (p.2 i : ℝ) ≤ c * ((j + k : ℕ) : ℝ) := by
          simpa only [iidBlockEquiv_apply, Fin.forall_fin_add, Fin.append_left,
            Fin.append_right] using hp.2
        have htotal_real : (∑ i, (p.1 i : ℝ)) + (∑ i, (p.2 i : ℝ)) =
            ((j + k : ℕ) : ℝ) - 1 := by
          have hh := congrArg (fun q : ℕ => (q : ℝ)) htotal
          simp only [Nat.cast_add, Nat.cast_sum] at hh
          rw [Nat.cast_sub (by omega : 1 ≤ j + k)] at hh
          simpa using hh
        have hcenter :
            ((∑ i, (p.1 i : ℝ)) - (offspringMean μ).toReal * j) +
              ((∑ i, (p.2 i : ℝ)) - (offspringMean μ).toReal * k) =
              γ * ((j + k : ℕ) : ℝ) - 1 := by
          dsimp [γ]
          push_cast at htotal_real hγn ⊢
          nlinarith
        have hlarge : a * ((j + k : ℕ) : ℝ) ≤
              (∑ i, (p.1 i : ℝ)) - (offspringMean μ).toReal * j ∨
            a * ((j + k : ℕ) : ℝ) ≤
              (∑ i, (p.2 i : ℝ)) - (offspringMean μ).toReal * k := by
          by_contra hh
          push Not at hh
          dsimp [a] at hh
          push_cast at hγn hcenter hh
          nlinarith
        rcases hlarge with hlarge | hlarge
        · exact Or.inl ⟨hlarge, htotal, hmax.1, hmax.2⟩
        · exact Or.inr ⟨hlarge, htotal, hmax.1, hmax.2⟩
      calc
        ((Measure.pi fun _ : Fin (j + k) => μ) A).toReal =
            (((Measure.pi fun _ : Fin j => μ).prod (Measure.pi fun _ : Fin k => μ))
              (iidBlockEquiv j k ⁻¹' A)).toReal := by
          exact congrArg ENNReal.toReal
            ((measurePreserving_iidBlockEquiv μ j k).measure_preimage_equiv A).symm
        _ ≤ (((Measure.pi fun _ : Fin j => μ).prod
            (Measure.pi fun _ : Fin k => μ)) (B1 ∪ B2)).toReal := by
          exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsplit)
        _ ≤ (((Measure.pi fun _ : Fin j => μ).prod
              (Measure.pi fun _ : Fin k => μ)) B1).toReal +
            (((Measure.pi fun _ : Fin j => μ).prod
              (Measure.pi fun _ : Fin k => μ)) B2).toReal := by
          exact measureReal_union_le B1 B2
        _ ≤ (Real.exp 1 * L ((j + k : ℕ) : ℝ) ^ 8) *
              (C / (((j + k : ℕ) : ℝ) * L ((j + k : ℕ) : ℝ) ^ 2)) +
            (Real.exp 1 * L ((j + k : ℕ) : ℝ) ^ 8) *
              (C / (((j + k : ℕ) : ℝ) * L ((j + k : ℕ) : ℝ) ^ 2)) := add_le_add hB1 hB2
        _ = 2 * (Real.exp 1 * C) * L ((j + k : ℕ) : ℝ) ^ 6 / ((j + k : ℕ) : ℝ) := by
          field_simp; ring
    exact hblock (n / 2) (n - n / 2) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hratio : ∀ᶠ n : ℕ in atTop,
      ((Measure.pi fun _ : Fin n => μ)
          {ω | ∑ i, ω i = n - 1 ∧ ∀ i, (ω i : ℝ) ≤ c * n}).toReal / (L n / n) ≤
        2 * (Real.exp 1 * C) * L n ^ 5 := by
    filter_upwards [hbound, eventually_ge_atTop 1] with n hn hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hLn : 0 < L n := hpos _ hn0
    calc
      _ ≤ (2 * (Real.exp 1 * C) * L n ^ 6 / (n : ℝ)) / (L n / n) :=
        div_le_div_of_nonneg_right hn (div_nonneg hLn.le hn0.le)
      _ = 2 * (Real.exp 1 * C) * L n ^ 5 := by
        field_simp
  have hlim : Tendsto (fun n : ℕ => 2 * (Real.exp 1 * C) * L n ^ 5) atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds (x := 2 * (Real.exp 1 * C))).mul (hL0.pow 5)
    simpa using hh
  apply squeeze_zero' ?_ hratio hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  exact div_nonneg ENNReal.toReal_nonneg
    (div_nonneg (hpos _ hn0).le hn0.le)

end SubcriticalCauchy.Bienayme
