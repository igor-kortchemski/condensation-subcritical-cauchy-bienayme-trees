module

public import SubcriticalCauchy.BienaymeTilting
public import BGW.LocallyFinite.BridgeLaw

import Mathlib.Tactic.Ring

/-!
# Rotation-invariant statistics of the conditioned tree and bridge

The actual size-conditioned Bienaymé law has the same rotation-invariant
increment events as independent offspring counts conditioned to form a bridge.
Finite-tree events are represented by their images in the locally finite tree
carrier. No default increment statistic is assigned to infinite trees.

This is the exact coding input used in Section 4 before the condensation limit.
It does not include a one-big-jump theorem or any asymptotic conclusion.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SubcriticalCauchy.Bienayme

noncomputable section

attribute [local instance] Classical.propDecidable

open BGW BGW.LocallyFinite

/-- The finite trees whose depth-first increment word satisfies `P`, embedded in
the actual probability space. -/
def finiteIncrementEvent (P : List ℤ → Prop) : Set Tree :=
  PlaneTree.toLocallyFinite '' {t : PlaneTree | P t.increments}

theorem measurableSet_finiteIncrementEvent (P : List ℤ → Prop) :
    MeasurableSet (finiteIncrementEvent P) := by
  exact (Set.to_countable {t : PlaneTree | P t.increments}).image
    PlaneTree.toLocallyFinite |>.measurableSet

theorem toLocallyFinite_mem_finiteIncrementEvent_iff
    (P : List ℤ → Prop) (t : PlaneTree) :
    t.toLocallyFinite ∈ finiteIncrementEvent P ↔ P t.increments := by
  constructor
  · rintro ⟨s, hs, hst⟩
    have hst' : s = t := PlaneTree.toLocallyFinite_injective hst
    simpa only [hst', Set.mem_ofPred_eq] using hs
  · intro ht
    exact ⟨t, ht, rfl⟩

/-- An event under size conditioning is the sum of its finite-tree atoms.
No admissibility assumption is needed: both sides vanish at null sizes. -/
theorem conditioned_apply_eq_tsum (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (n : ℕ) (A : Set Tree) (hA : MeasurableSet A) :
    conditioned μ n A =
      ∑' t : {t : PlaneTree // t.size = n},
        conditioned μ n {t.1.toLocallyFinite} *
          (if t.1.toLocallyFinite ∈ A then 1 else 0) := by
  classical
  let f (t : PlaneTree) : ℝ≥0∞ := conditioned μ n {t.toLocallyFinite} *
    (if t.toLocallyFinite ∈ A then 1 else 0)
  have hat (t : PlaneTree) : conditioned μ n {t.toLocallyFinite} =
      if t.size = n then
        PlaneTree.weight (fun k => μ {k}) t / bienaymeLaw μ (sizeEvent n) else 0 :=
    cond_sizeEvent_singleton μ n t
  have hsupp : Function.support f ⊆
      Set.range (fun t : {t : PlaneTree // t.size = n} => t.1) := by
    intro t ht
    by_cases hsize : t.size = n
    · exact ⟨⟨t, hsize⟩, rfl⟩
    · exfalso
      apply ht
      dsimp only [f]
      rw [hat, ite_eq_right hsize, zero_mul]
  have hsum : (∑' t : {t : PlaneTree // t.size = n}, f t.1) =
      ∑' t : PlaneTree, f t :=
    (Subtype.val_injective : Function.Injective
      (fun t : {t : PlaneTree // t.size = n} => t.1)).tsum_eq hsupp
  change conditioned μ n A = ∑' t : {t : PlaneTree // t.size = n}, f t.1
  rw [hsum]
  change (bienaymeLaw μ (sizeEvent n))⁻¹ *
      (bienaymeLaw μ).restrict (sizeEvent n) A = _
  rw [restrict_sizeEvent_apply μ n A hA, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro t
  dsimp only [f]
  rw [hat]
  by_cases ht : t.size = n
  · simp only [ht, ↓reduceIte, ENNReal.div_eq_inv_mul, mul_assoc]
  · simp only [ht, ↓reduceIte, zero_mul, mul_zero]

/-- The atom formula specialized to an increment event. -/
theorem conditioned_finiteIncrementEvent (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (n : ℕ) (P : List ℤ → Prop) :
    conditioned μ n (finiteIncrementEvent P) =
      ∑' t : {t : PlaneTree // t.size = n},
        conditioned μ n {t.1.toLocallyFinite} *
          (if P t.1.increments then 1 else 0) := by
  classical
  rw [conditioned_apply_eq_tsum μ n _ (measurableSet_finiteIncrementEvent P)]
  simp only [toLocallyFinite_mem_finiteIncrementEvent_iff]

/-- Re-encoding the counts of a rotated finite-tree word returns that word. -/
theorem stepWord_countsOfWord_rotated_increments {n : ℕ}
    (t : PlaneTree) (ht : t.size = n) (i : ℕ) :
    stepWord (countsOfWord n (t.increments.rotate i)) = t.increments.rotate i := by
  apply stepWord_countsOfWord
  · simp only [List.length_rotate, PlaneTree.length_increments, ht]
  · intro a ha
    exact PlaneTree.neg_one_le_increment t (by simpa only [List.mem_rotate] using ha)

/-- Every rotation-invariant increment event has the same mass under the
conditioned bridge and under the actual size-conditioned Bienaymé tree.
There is no subcriticality, support, aperiodicity or admissibility hypothesis. -/
theorem conditioned_bridge_rotation_invariant_event
    (μ : Measure ℕ) [IsProbabilityMeasure μ] {n : ℕ} (hn : n ≠ 0)
    (P : List ℤ → Prop)
    (hrot : ∀ (x : List ℤ) (i : ℕ), P (x.rotate i) ↔ P x) :
    (Measure.pi fun _ : Fin n => μ)[|countBridges n] {ω | P (stepWord ω)} =
      conditioned μ n (finiteIncrementEvent P) := by
  classical
  rw [cond_pi_countBridges_apply_eq_tsum,
    conditioned_finiteIncrementEvent μ n P, ENNReal.tsum_prod']
  apply tsum_congr
  intro t
  let a : ℝ≥0∞ := (bienaymeLaw μ)[|sizeEvent n] {t.1.toLocallyFinite}
  let b : ℝ≥0∞ := if P t.1.increments then 1 else 0
  change (∑' i : Fin n, (n : ℝ≥0∞)⁻¹ * a *
    Set.indicator {ω : Fin n → ℕ | P (stepWord ω)} 1
      (countsOfWord n (t.1.increments.rotate i))) = a * b
  have hind (i : Fin n) :
      Set.indicator {ω : Fin n → ℕ | P (stepWord ω)} 1
        (countsOfWord n (t.1.increments.rotate i)) =
      (if P t.1.increments then (1 : ℝ≥0∞) else 0) := by
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply,
      stepWord_countsOfWord_rotated_increments t.1 t.2, hrot]
  trans (∑' _i : Fin n, (n : ℝ≥0∞)⁻¹ * a * b)
  · apply tsum_congr
    intro i
    exact congrArg (fun z : ℝ≥0∞ => (n : ℝ≥0∞)⁻¹ * a * z) (hind i)
  calc
    (∑' _i : Fin n, (n : ℝ≥0∞)⁻¹ * a * b) =
        (n : ℝ≥0∞) * ((n : ℝ≥0∞)⁻¹ * a * b) := by
      rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ((n : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹) * (a * b) := by ring
    _ = a * b := by
      rw [ENNReal.mul_inv_cancel (by exact_mod_cast hn) (ENNReal.natCast_ne_top n), one_mul]

/-- Decode a list of integer increments to offspring counts. On arbitrary
integers this is totalized by `Int.toNat`; the coding lemmas below justify every
use on actual tree increments and offspring-count vectors. -/
def wordDegrees (x : List ℤ) : List ℕ := x.map (fun z => (z + 1).toNat)

theorem wordDegrees_increments (t : PlaneTree) : wordDegrees t.increments = t.degrees := by
  simp [wordDegrees, PlaneTree.increments, List.map_map, Function.comp_def]

theorem wordDegrees_stepWord {n : ℕ} (ω : Fin n → ℕ) :
    wordDegrees (stepWord ω) = List.ofFn ω := by
  unfold wordDegrees stepWord
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  simp

theorem wordDegrees_rotate (x : List ℤ) (i : ℕ) :
    wordDegrees (x.rotate i) = (wordDegrees x).rotate i :=
  List.map_rotate _ _ _

/-- An event of a finite-tree degree list, represented on the actual
locally finite carrier. Its predicate need not be permutation invariant. -/
def finiteDegreeEvent (Q : List ℕ → Prop) : Set Tree :=
  PlaneTree.toLocallyFinite '' {t : PlaneTree | Q t.degrees}

theorem finiteDegreeEvent_eq_finiteIncrementEvent (Q : List ℕ → Prop) :
    finiteDegreeEvent Q = finiteIncrementEvent (fun x => Q (wordDegrees x)) := by
  simp only [finiteDegreeEvent, finiteIncrementEvent, wordDegrees_increments]

theorem measurableSet_finiteDegreeEvent (Q : List ℕ → Prop) :
    MeasurableSet (finiteDegreeEvent Q) := by
  rw [finiteDegreeEvent_eq_finiteIncrementEvent]
  exact measurableSet_finiteIncrementEvent _

theorem toLocallyFinite_mem_finiteDegreeEvent_iff (Q : List ℕ → Prop) (t : PlaneTree) :
    t.toLocallyFinite ∈ finiteDegreeEvent Q ↔ Q t.degrees := by
  rw [finiteDegreeEvent_eq_finiteIncrementEvent,
    toLocallyFinite_mem_finiteIncrementEvent_iff, wordDegrees_increments]

/-- The multiset of outdegrees of the actual size-conditioned tree has the law
of independent offspring counts conditioned to sum to `n-1`. The predicate may
be any permutation-invariant degree-list event, including joint degree statistics.
No one-big-jump or limit statement is assumed. -/
theorem bridge_degree_permutation_event
    (μ : Measure ℕ) [IsProbabilityMeasure μ] {n : ℕ} (hn : n ≠ 0)
    (Q : List ℕ → Prop)
    (hperm : ∀ ds es : List ℕ, ds.Perm es → (Q ds ↔ Q es)) :
    (Measure.pi fun _ : Fin n => μ)[|countBridges n] {ω | Q (List.ofFn ω)} =
      conditioned μ n (finiteDegreeEvent Q) := by
  let P : List ℤ → Prop := fun x => Q (wordDegrees x)
  have hrot (x : List ℤ) (i : ℕ) : P (x.rotate i) ↔ P x := by
    change Q (wordDegrees (x.rotate i)) ↔ Q (wordDegrees x)
    rw [wordDegrees_rotate]
    exact hperm _ _ (List.rotate_perm _ _)
  have h := conditioned_bridge_rotation_invariant_event μ hn P hrot
  have hA : {ω : Fin n → ℕ | P (stepWord ω)} = {ω | Q (List.ofFn ω)} := by
    ext ω
    change Q (wordDegrees (stepWord ω)) ↔ Q (List.ofFn ω)
    rw [wordDegrees_stepWord]
  have hB : finiteIncrementEvent P = finiteDegreeEvent Q :=
    (finiteDegreeEvent_eq_finiteIncrementEvent Q).symm
  rw [hA, hB] at h
  exact h

end
end SubcriticalCauchy.Bienayme
