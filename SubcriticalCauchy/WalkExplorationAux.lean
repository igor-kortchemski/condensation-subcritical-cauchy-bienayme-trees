module

public import SubcriticalCauchy.OffspringWalk
public import Mathlib.Analysis.SpecificLimits.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! # First passage of the iid downward skip-free walk

`walkFirstPassage` is the first visit to `-d`, totalized as zero if that level
is never visited. Negative drift proves existence at every level almost surely,
so this convention disappears from the limiting statements.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SubcriticalCauchy.Bienayme

noncomputable section

theorem passageSearch_exists (ω : ℕ → ℕ) (d : ℕ) :
    ∃ k, walkSum ω k = -(d : ℤ) ∨ ∀ j, walkSum ω j ≠ -(d : ℤ) := by
  classical
  by_cases h : ∃ k, walkSum ω k = -(d : ℤ)
  · obtain ⟨k, hk⟩ := h
    exact ⟨k, Or.inl hk⟩
  · exact ⟨0, Or.inr (not_exists.mp h)⟩

/-- First visit to `-d`; zero on paths that never visit that level. -/
def walkFirstPassage (ω : ℕ → ℕ) (d : ℕ) : ℕ := by
  classical
  exact Nat.find (passageSearch_exists ω d)

theorem walkFirstPassage_spec (ω : ℕ → ℕ) (d : ℕ)
    (h : ∃ k, walkSum ω k = -(d : ℤ)) :
    walkSum ω (walkFirstPassage ω d) = -(d : ℤ) := by
  classical
  have hs := Nat.find_spec (passageSearch_exists ω d)
  rcases hs with hs | hs
  · exact hs
  · obtain ⟨k, hk⟩ := h
    exact (hs k hk).elim

theorem walkFirstPassage_le (ω : ℕ → ℕ) (d k : ℕ)
    (hk : walkSum ω k = -(d : ℤ)) : walkFirstPassage ω d ≤ k := by
  classical
  exact Nat.find_min' (passageSearch_exists ω d) (Or.inl hk)

/-- The totalization is zero exactly as specified on nonhitting paths. -/
theorem walkFirstPassage_of_no_hit (ω : ℕ → ℕ) (d : ℕ)
    (h : ∀ k, walkSum ω k ≠ -(d : ℤ)) : walkFirstPassage ω d = 0 := by
  classical
  exact Nat.eq_zero_of_le_zero (Nat.find_min' (passageSearch_exists ω d) (Or.inr h))

@[simp] theorem walkFirstPassage_zero (ω : ℕ → ℕ) : walkFirstPassage ω 0 = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact walkFirstPassage_le ω 0 0 (by simp [walkSum])

theorem walkSum_succ_sub_one (ω : ℕ → ℕ) (k : ℕ) :
    walkSum ω (k + 1) = walkSum ω k + (ω k : ℤ) - 1 := by
  simp only [walkSum, Finset.sum_range_succ]
  omega

theorem neg_time_le_walkSum (ω : ℕ → ℕ) (k : ℕ) : -(k : ℤ) ≤ walkSum ω k := by
  induction k with
  | zero => simp [walkSum]
  | succ k ih => rw [walkSum_succ_sub_one]; push_cast; omega

/-- Discrete intermediate value property for the actual walk. -/
theorem exists_walkSum_eq_of_le (ω : ℕ → ℕ) (d : ℕ)
    (h : ∃ k, walkSum ω k ≤ -(d : ℤ)) : ∃ k, walkSum ω k = -(d : ℤ) := by
  classical
  refine ⟨Nat.find h, ?_⟩
  have hle := Nat.find_spec h
  cases he : Nat.find h with
  | zero =>
    rw [he] at hle
    simp only [walkSum, Finset.range_zero, Finset.sum_empty] at hle ⊢
    omega
  | succ k =>
    have hprev := Nat.find_min h (show k < Nat.find h by omega)
    rw [he, walkSum_succ_sub_one] at hle
    rw [walkSum_succ_sub_one]
    omega

/-- Negative limiting speed implies every negative integer level is attained. -/
theorem exists_walkSum_eq_of_negative_drift (ω : ℕ → ℕ) {a : ℝ} (ha : a < 0)
    (hω : Tendsto (fun n => walkAverage n ω) atTop (𝓝 a)) (d : ℕ) :
    ∃ k, walkSum ω k = -(d : ℤ) := by
  have hbot : Tendsto (fun n => (walkSum ω n : ℝ)) atTop atBot := by
    have h := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_neg ha hω
    convert h using 1
    funext n
    by_cases hn : n = 0
    · simp [hn, walkSum]
    · dsimp [walkAverage]
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      field_simp
  apply exists_walkSum_eq_of_le
  obtain ⟨k, hk⟩ := (hbot.eventually (eventually_le_atBot (-(d : ℝ)))).exists
  exact ⟨k, by exact_mod_cast hk⟩

/-- First passage to linearly growing levels, pathwise inverse strong law. -/
theorem walkFirstPassage_ratio_tendsto (ω : ℕ → ℕ) {a δ : ℝ}
    (ha : a < 0) (hδ : 0 < δ)
    (hω : Tendsto (fun n => walkAverage n ω) atTop (𝓝 a)) :
    Tendsto (fun n : ℕ => (walkFirstPassage ω ⌊δ * (n : ℝ)⌋₊ : ℝ) / (n : ℝ))
      atTop (𝓝 (δ / (-a))) := by
  let d : ℕ → ℕ := fun n => ⌊δ * (n : ℝ)⌋₊
  let t : ℕ → ℕ := fun n => walkFirstPassage ω (d n)
  have hspec (n : ℕ) : walkSum ω (t n) = -(d n : ℤ) :=
    walkFirstPassage_spec ω (d n) (exists_walkSum_eq_of_negative_drift ω ha hω (d n))
  have hd : Tendsto d atTop atTop :=
    tendsto_nat_floor_atTop.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hδ)
  have hdt (n : ℕ) : d n ≤ t n := by
    have := neg_time_le_walkSum ω (t n)
    rw [hspec] at this
    omega
  have ht : Tendsto t atTop atTop := tendsto_atTop_mono hdt hd
  have hratio : Tendsto (fun n : ℕ => (d n : ℝ) / (n : ℝ)) atTop (𝓝 δ) :=
    (tendsto_nat_floor_mul_div_atTop hδ.le).comp tendsto_natCast_atTop_atTop
  have h := hratio.neg.div (hω.comp ht) (ne_of_lt ha)
  have heq : (fun n : ℕ => -((d n : ℝ) / (n : ℝ)) / walkAverage (t n) ω) =ᶠ[atTop]
      (fun n : ℕ => (t n : ℝ) / (n : ℝ)) := by
    filter_upwards [hd.eventually (eventually_gt_atTop 0),
      eventually_gt_atTop (0 : ℕ)] with n hdn hn
    have htn : (t n : ℝ) ≠ 0 := by exact_mod_cast (show t n ≠ 0 by have := hdt n; omega)
    have hnn : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hdnR : (d n : ℝ) ≠ 0 := by exact_mod_cast (show d n ≠ 0 by omega)
    dsimp [walkAverage]
    rw [hspec]
    push_cast
    field_simp [hdnR, hnn, htn]
  have hlim : -δ / a = δ / (-a) := by rw [div_neg, neg_div]
  rw [hlim] at h
  exact h.congr' heq

/-- Almost sure first-passage law of large numbers for the infinite iid law. -/
theorem iid_walkFirstPassage_ratio_ae_tendsto (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ < 1) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ ω ∂iidOffspringLaw μ,
      Tendsto (fun n : ℕ => (walkFirstPassage ω ⌊δ * (n : ℝ)⌋₊ : ℝ) / (n : ℝ))
        atTop (𝓝 (δ / (1 - (offspringMean μ).toReal))) := by
  have hfin : offspringMean μ ≠ ∞ := ne_top_of_lt (hm.trans ENNReal.one_lt_top)
  have hmR : (offspringMean μ).toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hfin ENNReal.one_ne_top).mpr hm
  filter_upwards [walkAverage_ae_tendsto μ hfin] with ω hω
  simpa only [neg_sub] using walkFirstPassage_ratio_tendsto ω (sub_neg.mpr hmR) hδ hω

@[fun_prop] theorem measurable_walkSum (k : ℕ) :
    Measurable (fun ω : ℕ → ℕ => walkSum ω k) := by
  unfold walkSum
  exact Finset.measurable_fun_sum _ fun i _ =>
    (measurable_of_countable (fun a : ℕ => (a : ℤ) - 1)).comp (measurable_pi_apply i)

@[fun_prop] theorem measurable_walkFirstPassage (d : ℕ) :
    Measurable (fun ω : ℕ → ℕ => walkFirstPassage ω d) := by
  classical
  apply measurable_find (fun ω => passageSearch_exists ω d)
  intro k
  have h (j : ℕ) : MeasurableSet {ω : ℕ → ℕ | walkSum ω j = -(d : ℤ)} :=
    measurableSet_eq_fun (measurable_walkSum j) measurable_const
  have hno : MeasurableSet {ω : ℕ → ℕ | ∀ j, walkSum ω j ≠ -(d : ℤ)} := by
    simpa only [Set.ofPred_forall, ← Set.compl_ofPred] using (MeasurableSet.iInter fun j => (h j).compl)
  exact (h k).union hno

/-- The requested convergence in probability, on the actual infinite product law. -/
theorem iid_walkFirstPassage_ratio_tendstoInMeasure (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ < 1) {δ : ℝ} (hδ : 0 < δ) :
    TendstoInMeasure (iidOffspringLaw μ)
      (fun n : ℕ => fun ω => (walkFirstPassage ω ⌊δ * (n : ℝ)⌋₊ : ℝ) / (n : ℝ)) atTop
      (fun _ => δ / (1 - (offspringMean μ).toReal)) := by
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    exact (((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
      (measurable_walkFirstPassage _)).div_const _).aestronglyMeasurable
  · exact iid_walkFirstPassage_ratio_ae_tendsto μ hm hδ

end
end SubcriticalCauchy.Bienayme
