module

public import Mathlib.Data.W.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.List.Indexes
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.List.Lex
public import Mathlib.Data.List.Rotate
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Vector.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.TotalVariation.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Frozen statements for subcritical Cauchy Bienaymé trees

This file reconstructs the definitions used by the twenty approved statements
of *Condensation in subcritical Cauchy Bienaymé trees* and states those twenty
results. It imports only Mathlib. Helper theorems occurring in definition
bodies retain their proofs; the twenty target proofs are the Comparator holes.

Conventions. `PlaneTree` addresses are zero-based; the carrier `Tree` numbers children from
`1`. `conditioned μ n` is the `μ`-tree `𝒯_n` conditioned on exactly `n` vertices (zero
measure if that is null). Mathlib's `tvDist` is twice the paper's total variation distance.
Declarations without docstrings (`canonical_pruneRaw`, `vertices_nonempty`, ...) are helpers
whose proofs the definitions need. Namespace blocks and `open` lines mirror the development.
-/

@[expose] public section

set_option autoImplicit false

namespace BGW.LocallyFinite

/-- Vertex addresses as lists of naturals. In `Tree`, `Present`, `generation` the children are
numbered `1, …, degree`; the `PlaneTree` API (`fringe?`, `vertices`) numbers them from `0`. -/
abbrev Address := List ℕ

/-- An offspring-count at every possible address. -/
abbrev Offspring := Address → ℕ

/-- The address `u ++ [j]` has count `0` unless `1 ≤ j ≤ f u`, i.e. unless it is an actual
child of `u`. Applied at every `u`, counts at absent addresses vanish with all descendants. -/
def Canonical (f : Offspring) : Prop :=
  ∀ (u : Address) (j : ℕ), ¬(1 ≤ j ∧ j ≤ f u) → f (u ++ [j]) = 0

/-- Canonical offspring fields describe possibly infinite, locally finite plane trees. -/
abbrev Tree := {f : Offspring // Canonical f}

/-- The offspring count at the root of a locally finite tree. -/
def degree (T : Tree) : ℕ := T.val []

/-- Re-root at child `j`. An absent child is represented by `leaf`; use `Present`
to test whether that child actually exists. -/
def child (T : Tree) (j : ℕ) : Tree :=
  ⟨fun u => T.val (j :: u), fun u k hk => T.property (j :: u) k hk⟩

/-- `Present T u`: the address `u` (children numbered from `1`) is a vertex of `T`: the root,
or a child `j` with `1 ≤ j ≤ degree T` whose subtree contains the rest of `u`. -/
def Present (T : Tree) : Address → Prop
  | [] => True
  | j :: u => 1 ≤ j ∧ j ≤ degree T ∧ Present (child T j) u

/-- Finiteness refers to the vertices, not to the support of the offspring field. -/
def FiniteVertices (T : Tree) : Prop := {u | Present T u}.Finite

end BGW.LocallyFinite

namespace BGW

/-- Finite rooted ordered trees, with no vertex labels. -/
def PlaneTree : Type := WType (fun n : ℕ => Fin n)

/-- Mathlib's `Encodable` instance for W-types: `PlaneTree` is countable (for sums over trees). -/
instance : Encodable PlaneTree := inferInstanceAs (Encodable (WType _))

/-- Finite ordered forests. The empty forest is allowed. -/
abbrev PlaneForest := List PlaneTree

namespace PlaneTree

/-- A tree is determined by the ordered list of subtrees attached to its root. -/
def equivChildren : PlaneTree ≃ List PlaneTree :=
  (WType.equivSigma (fun n : ℕ => Fin n)).trans List.equivSigmaTuple.symm

/-- Attach an ordered list of trees to a new root. -/
def node (ts : List PlaneTree) : PlaneTree := equivChildren.symm ts

/-- The ordered subtrees attached to the root. -/
def children (t : PlaneTree) : List PlaneTree := equivChildren t

@[simp] theorem children_node (ts : List PlaneTree) : (node ts).children = ts :=
  equivChildren.apply_symm_apply ts

@[simp] theorem node_children (t : PlaneTree) : node t.children = t :=
  equivChildren.symm_apply_apply t

/-- Induction over all the children of a root. This is the default `induction` principle. -/
@[elab_as_elim, induction_eliminator] theorem induction_on {motive : PlaneTree → Prop}
    (t : PlaneTree) (node : ∀ ts, (∀ s ∈ ts, motive s) → motive (PlaneTree.node ts)) :
    motive t := by
  induction t with
  | mk n f ih =>
    rw [← node_children (WType.mk n f)]
    apply node
    intro s hs
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hs
    exact ih i

/-- Bottom-up recursion: `fold g` applies `g` to the values already computed at the
children of the root, in child order. -/
def fold {β : Type*} (g : List β → β) : PlaneTree → β :=
  WType.elim β fun ⟨_, f⟩ => g (List.ofFn f)

@[simp] theorem fold_node {β : Type*} (g : List β → β) (ts : List PlaneTree) :
    fold g (node ts) = g (ts.map (fold g)) := by
  change g (List.ofFn (fold g ∘ ts.get)) = _
  rw [← List.map_ofFn, List.ofFn_get]

/-- The tree consisting only of its root. -/
def leaf : PlaneTree := node []

/-- The number of children of the root. -/
def rootDegree (t : PlaneTree) : ℕ := t.children.length

/-- Lookup of a fringe subtree; zero-based: `i :: u` descends to the `i`-th child from `0`.
`none`: not a vertex. The returned tree is re-rooted at `[]`. -/
def fringe? : PlaneTree → List ℕ → Option PlaneTree
  | t, [] => some t
  | t, i :: u => t.children[i]?.bind (fun s => s.fringe? u)

/-- An address belongs to the tree exactly when fringe lookup succeeds. -/
def IsVertex (t : PlaneTree) (u : List ℕ) : Prop := ∃ s, t.fringe? u = some s

@[simp] theorem fringe?_nil (t : PlaneTree) : t.fringe? [] = some t := rfl

/-- Address lookup descends through the specified child. -/
@[simp] theorem fringe?_cons (t : PlaneTree) (i : ℕ) (u : List ℕ) :
    t.fringe? (i :: u) = t.children[i]?.bind (fun s => s.fringe? u) := rfl

@[simp] theorem fringe?_node_cons (ts : List PlaneTree) (i : ℕ) (u : List ℕ) :
    (node ts).fringe? (i :: u) = ts[i]?.bind (fun s => s.fringe? u) := by simp

end PlaneTree
end BGW

namespace BGW.PlaneTree

/-- All vertex addresses (zero-based, see `fringe?`), in root-first depth-first preorder. -/
def vertices : PlaneTree → List (List ℕ) :=
  fold fun vs => [] :: (vs.mapIdx (fun i v => v.map (fun u => i :: u))).flatten

@[simp] theorem vertices_node (ts : List PlaneTree) :
    (node ts).vertices =
      [] :: (ts.mapIdx (fun i t => t.vertices.map (fun u => i :: u))).flatten := by
  simp only [vertices, fold_node, List.mapIdx_eq_ofFn, List.length_map, List.get_eq_getElem,
    List.getElem_map]
  rfl

/-- The enumeration contains exactly the addresses at which fringe lookup succeeds. -/
theorem mem_vertices_iff (t : PlaneTree) (u : List ℕ) :
    u ∈ t.vertices ↔ t.IsVertex u := by
  induction t generalizing u with
  | node ts ih =>
    cases u with
    | nil =>
      constructor
      · intro _
        exact ⟨node ts, fringe?_nil _⟩
      · intro _
        rw [vertices_node]
        exact List.mem_cons_self ..
    | cons i u =>
      rw [vertices_node]
      constructor
      · intro h
        obtain h | h := List.mem_cons.mp h
        · cases h
        · obtain ⟨block, hb, hmem⟩ := List.mem_flatten.mp h
          obtain ⟨j, hj, heq⟩ := List.mem_mapIdx.mp hb
          subst block
          obtain ⟨v, hv, heq⟩ := List.mem_map.mp hmem
          obtain ⟨rfl, rfl⟩ := List.cons.inj heq
          obtain ⟨s, hs⟩ := (ih _ (List.getElem_mem hj) v).mp hv
          refine ⟨s, ?_⟩
          rw [fringe?_node_cons, List.getElem?_eq_getElem hj]
          exact hs
      · rintro ⟨s, hs⟩
        rw [fringe?_node_cons] at hs
        by_cases hi : i < ts.length
        · rw [List.getElem?_eq_getElem hi] at hs
          have hsub : IsVertex ts[i] u := ⟨s, hs⟩
          apply List.mem_cons.mpr
          right
          apply List.mem_flatten.mpr
          refine ⟨_, List.mem_mapIdx.mpr ⟨i, hi, rfl⟩, ?_⟩
          exact List.mem_map_of_mem ((ih _ (List.getElem_mem hi) u).mpr hsub)
        · rw [List.getElem?_eq_none (Nat.le_of_not_gt hi)] at hs
          contradiction

end BGW.PlaneTree

namespace BGW.PlaneTree

/-- Offspring field of the tree on one-based addresses: step `i + 1` enters the `i`-th child
(zero-based index); step `0` or an absent child gives `0`; `[]` gives the root degree. -/
def offspringAt : PlaneTree → List ℕ → ℕ
  | t, [] => t.rootDegree
  | _, 0 :: _ => 0
  | t, (i + 1) :: u => ((t.children[i]?).map (fun s => offspringAt s u)).getD 0

theorem canonical_offspringAt (t : PlaneTree) : LocallyFinite.Canonical t.offspringAt := by
  intro u j
  induction u generalizing t with
  | nil =>
    cases j with
    | zero =>
      intro _
      rfl
    | succ j =>
      intro hj
      have hn : ¬j < t.children.length := by
        intro hlt
        exact hj ⟨Nat.succ_le_succ (Nat.zero_le j), hlt⟩
      change ((t.children[j]?).map (fun s => s.rootDegree)).getD 0 = 0
      rw [List.getElem?_eq_none (Nat.le_of_not_gt hn)]
      rfl
  | cons i u ih =>
    cases i with
    | zero =>
      intro _
      rfl
    | succ i =>
      cases h : t.children[i]? with
      | none =>
        intro _
        change ((t.children[i]?).map (fun s => s.offspringAt (u ++ [j]))).getD 0 = 0
        rw [h]
        rfl
      | some s =>
        intro hj
        have heq : t.offspringAt ((i + 1) :: u) = s.offspringAt u := by
          change ((t.children[i]?).map (fun s => s.offspringAt u)).getD 0 = s.offspringAt u
          rw [h]
          rfl
        rw [heq] at hj
        change ((t.children[i]?).map (fun s => s.offspringAt (u ++ [j]))).getD 0 = 0
        rw [h]
        exact ih s hj

/-- A finite plane tree as a tree of the carrier (children renumbered from `1`); injective. -/
def toLocallyFinite (t : PlaneTree) : LocallyFinite.Tree :=
  ⟨t.offspringAt, t.canonical_offspringAt⟩

end BGW.PlaneTree

namespace BGW.PlaneTree

/-- Outdegrees in root-first depth-first order, every vertex occurrence; leaves give `0`. -/
def degrees : PlaneTree → List ℕ := fold fun ds => ds.length :: ds.flatten

end BGW.PlaneTree

namespace BGW.LocallyFinite

-- In this single file, Lean would reuse `Present.match_1` for this pattern match (an
-- identical matcher); in the development the two live in different modules. Turning off
-- matcher code generation here changes Lean's matcher cache key, so the auxiliary
-- `pruneRaw.match_1` is created exactly as in the development. Kernel terms are unaffected.
-- This only aligns auxiliary declaration names with the development's; no mathematical meaning.
set_option bootstrap.genMatcherCode false in
/-- Keep the offspring count at an address only if every step of the address is a valid child
of the retained counts above it. -/
def pruneRaw (f : Offspring) : Address → ℕ
  | [] => f []
  | j :: u => if 1 ≤ j ∧ j ≤ f [] then pruneRaw (fun v => f (j :: v)) u else 0

theorem canonical_pruneRaw (f : Offspring) : Canonical (pruneRaw f) := by
  intro u j
  induction u generalizing f with
  | nil =>
    simp only [List.nil_append, pruneRaw]
    intro hj
    rw [ite_eq_right hj]
  | cons i u ih =>
    by_cases hi : 1 ≤ i ∧ i ≤ f []
    · simpa only [List.cons_append, pruneRaw, ite_eq_left hi] using ih (fun v => f (i :: v))
    · simp only [List.cons_append, pruneRaw, hi, ↓reduceIte]
      intro _
      trivial

/-- The tree obtained from an offspring field by discarding the counts at absent addresses. -/
def prune (f : Offspring) : Tree := ⟨pruneRaw f, canonical_pruneRaw f⟩

end BGW.LocallyFinite

namespace BGW.LocallyFinite

/-- The finite set of vertices at depth `n`, including the root at depth zero. -/
def generation (T : Tree) : ℕ → Finset Address
  | 0 => {[]}
  | n + 1 => (Finset.range (degree T)).biUnion fun j =>
      (generation (child T (j + 1)) n).image (List.cons (j + 1))

/-- The number of present vertices at depth `n`. -/
def generationSize (T : Tree) (n : ℕ) : ℕ := (generation T n).card

end BGW.LocallyFinite

namespace BGW.LocallyFinite
open MeasureTheory

/-- Independent potential offspring counts, one for each address. -/
noncomputable def offspringFieldLaw (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    Measure Offspring :=
  Measure.infinitePi (fun _ : Address => μ)

/-- The Bienaymé–Galton–Watson law with offspring law `μ` on the carrier `Tree`: the image of
the independent-offspring field under `prune`. Infinite trees are allowed; no conditioning. -/
noncomputable def bienaymeLaw (μ : Measure ℕ) [IsProbabilityMeasure μ] : Measure Tree :=
  (offspringFieldLaw μ).map prune

end BGW.LocallyFinite

namespace BGW.LocallyFinite

/-- The tree is finite and has exactly `n` present addresses (vertices, leaves included). The
finiteness conjunct is needed at `n = 0`: `Set.ncard` of an infinite set is `0`. -/
def sizeEvent (n : ℕ) : Set Tree := {T | FiniteVertices T ∧ {u | Present T u}.ncard = n}

end BGW.LocallyFinite

namespace BGW
open MeasureTheory
open scoped ENNReal BigOperators

/-- Count vectors whose Łukasiewicz walk `∑ (ω i - 1)` ends at `-1` (bridge only). -/
def countBridges (n : ℕ) : Set (Fin n → ℕ) := {ω | ∑ i, ω i + 1 = n}

end BGW

namespace SubcriticalCauchy
noncomputable section
open Filter
open scoped Topology

/-- The tail `∑_{j ≥ 0} T (n + j)` (`tsum`: value `0` if not summable). -/
def tailMass (T : ℕ → ℝ) (n : ℕ) : ℝ := ∑' j : ℕ, T (n + j)

end
end SubcriticalCauchy

namespace SubcriticalCauchy.Bienayme
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
open BGW BGW.LocallyFinite

/-- Having height at least `n`, including generation zero at the root. -/
def survivalEvent (n : ℕ) : Set Tree := {T | 0 < generationSize T n}

/-- The paper's `Q_n = P(H(𝒯) ≥ n)` for an unconditioned `μ`-tree 𝒯, in `ℝ≥0∞`. -/
def survival (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) : ℝ≥0∞ :=
  bienaymeLaw μ (survivalEvent n)

/-- The offspring mean; infinite means are retained rather than totalized. -/
def offspringMean (μ : Measure ℕ) : ℝ≥0∞ := ∫⁻ k : ℕ, (k : ℝ≥0∞) ∂μ

end
end SubcriticalCauchy.Bienayme

namespace SubcriticalCauchy.Bienayme
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BGW.LocallyFinite

/-- The Bienaymé law conditioned on "finite with exactly `n` vertices" (the paper's `𝒯_n`), on
`Tree`. If that event is null (e.g. `n = 0`), Mathlib's convention gives the zero measure. -/
def conditioned (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) : Measure Tree :=
  (bienaymeLaw μ)[|sizeEvent n]

end
end SubcriticalCauchy.Bienayme

namespace SubcriticalCauchy.Bienayme
open BGW.LocallyFinite

/-- The maximal root-to-vertex distance in a finite rooted ordered tree. (The explicit instance
arguments of `Finset.sup` here and below pin the instance path so the term is identical to
the development's; mathematically it is `Finset.sup` on `ℕ`.) -/
def height (t : BGW.PlaneTree) : ℕ :=
  @Finset.sup ℕ (List ℕ) (@Lattice.toSemilatticeSup ℕ Nat.instLattice)
    Nat.instOrderBot t.vertices.toFinset List.length

end SubcriticalCauchy.Bienayme

namespace SubcriticalCauchy.Bienayme
noncomputable section

/-- Outdegree at a vertex address. The zero default at invalid addresses never
enters vertex selection; lookup success is proved for every selected address. -/
def degreeAt (t : BGW.PlaneTree) (u : List ℕ) : ℕ :=
  ((t.fringe? u).map BGW.PlaneTree.rootDegree).getD 0

/-- Largest outdegree, counting actual vertex occurrences. -/
def maxDegree (t : BGW.PlaneTree) : ℕ :=
  @Finset.sup ℕ (List ℕ) (@Lattice.toSemilatticeSup ℕ
    (@DistribLattice.toLattice ℕ instDistribLatticeNat)) Nat.instOrderBot
    t.vertices.toFinset (degreeAt t)

theorem vertices_nonempty (t : BGW.PlaneTree) : t.vertices.toFinset.Nonempty :=
  ⟨[], List.mem_toFinset.mpr ((BGW.PlaneTree.mem_vertices_iff t []).mpr
    ⟨t, BGW.PlaneTree.fringe?_nil t⟩)⟩

/-- All vertex addresses attaining the maximal outdegree. -/
def maximalVertices (t : BGW.PlaneTree) : Finset (List ℕ) :=
  t.vertices.toFinset.filter (fun u => degreeAt t u = maxDegree t)

theorem maximalVertices_nonempty (t : BGW.PlaneTree) : (maximalVertices t).Nonempty := by
  obtain ⟨u, hu, heq⟩ := Finset.exists_mem_eq_sup t.vertices.toFinset
    (vertices_nonempty t) (degreeAt t)
  exact ⟨u, Finset.mem_filter.mpr ⟨hu, heq.symm⟩⟩

/-- First maximal-degree vertex in lexicographic order, including prefix order. -/
def maxDegreeVertex (t : BGW.PlaneTree) : List ℕ :=
  (maximalVertices t).min' (maximalVertices_nonempty t)

theorem maxDegreeVertex_mem (t : BGW.PlaneTree) :
    maxDegreeVertex t ∈ maximalVertices t := Finset.min'_mem _ _

theorem maxDegreeVertex_isVertex (t : BGW.PlaneTree) : t.IsVertex (maxDegreeVertex t) :=
  (BGW.PlaneTree.mem_vertices_iff t (maxDegreeVertex t)).mp
    (List.mem_toFinset.mp (Finset.mem_filter.mp (maxDegreeVertex_mem t)).1)

/-- The subtree rooted at the selected vertex. `Classical.choose` only extracts the witness of
`IsVertex`; it is unique (the value of `fringe?`), so no choice is involved. -/
def maxDegreeFringe (t : BGW.PlaneTree) : BGW.PlaneTree :=
  Classical.choose (maxDegreeVertex_isVertex t)

/-- The ordered subtrees rooted at children of the selected vertex. -/
def attachedForest (t : BGW.PlaneTree) : BGW.PlaneForest := (maxDegreeFringe t).children

/-- The `i`-th child subtree of the selected vertex, numbered from `1`; `none` if `i` exceeds
the degree. For `i = 0` truncated subtraction gives the first child; only `i ≥ 1` is used. -/
def attachedChild (t : BGW.PlaneTree) (i : ℕ) : Option BGW.PlaneTree :=
  (attachedForest t)[i - 1]?

end
end SubcriticalCauchy.Bienayme

namespace SubcriticalCauchy.Bienayme

/-- Largest natural count in a word, with value zero for an empty word. -/
def listMaxDegree (ds : List ℕ) : ℕ :=
  @Finset.sup ℕ ℕ (@Lattice.toSemilatticeSup ℕ
    (@DistribLattice.toLattice ℕ instDistribLatticeNat)) Nat.instOrderBot ds.toFinset id

/-- Second largest count, retaining multiplicities. A missing second entry has
value zero. -/
def listSecondMaxDegree (ds : List ℕ) : ℕ := listMaxDegree (ds.erase (listMaxDegree ds))

/-- The second largest tree outdegree; multiplicity is preserved at ties. -/
def secondMaxDegree (t : BGW.PlaneTree) : ℕ := listSecondMaxDegree t.degrees

end SubcriticalCauchy.Bienayme

namespace SubcriticalCauchy.Bienayme
noncomputable section

/-- Graph distance from the root to the selected maximal-degree vertex. -/
def maxDegreeDepth (t : BGW.PlaneTree) : ℕ := (maxDegreeVertex t).length

end
end SubcriticalCauchy.Bienayme

namespace SubcriticalCauchy.Bienayme
open BGW BGW.LocallyFinite

/-- The event `{t | P t}` of finite plane trees, on the carrier (`toLocallyFinite` is injective). -/
def finiteTreeEvent (P : PlaneTree → Prop) : Set Tree :=
  PlaneTree.toLocallyFinite '' {t : PlaneTree | P t}

end SubcriticalCauchy.Bienayme

namespace SubcriticalCauchy.Bienayme
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
open BGW.LocallyFinite

/-- A forest with `k` independent components, each with the constructed tree law. -/
def forestLaw (μ : Measure ℕ) [IsProbabilityMeasure μ] (k : ℕ) :
    Measure (Fin k → Tree) := Measure.pi (fun _ => bienaymeLaw μ)

end
end SubcriticalCauchy.Bienayme

namespace SubcriticalCauchy.Bienayme
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
open BGW BGW.LocallyFinite

/-- Slow variation in the Introduction's ratio form: `L (a x) / L x → 1` for all `a > 0`;
no measurability. -/
def IsSlowlyVaryingAtTop (L : ℝ → ℝ) : Prop :=
  ∀ a : ℝ, 0 < a → Tendsto (fun x : ℝ => L (a * x) / L x) atTop (𝓝 1)

end
end SubcriticalCauchy.Bienayme

namespace SubcriticalCauchy.Bienayme
open MeasureTheory Filter
open scoped ENNReal Topology

/-- The paper's hypothesis `(H^loc_μ)`, in the version accepted for the main statements: the
mean `m` of `μ` is `< 1`, and there is a positive function `L` on `(0, ∞)`, slowly varying
(`IsSlowlyVaryingAtTop`) and Lebesgue (a.e.) measurable on `(0, ∞)`, with `μ_n ~ L(n)/n²`
(`α = 1`). Measurability is the author's convention of 1 November 2026, not the paper's. -/
def IsMeasurableSubcriticalCauchyOffspring (μ : Measure ℕ) : Prop :=
  offspringMean μ < 1 ∧ ∃ L : ℝ → ℝ,
    (∀ x : ℝ, 0 < x → 0 < L x) ∧ IsSlowlyVaryingAtTop L ∧
      AEMeasurable L (volume.restrict (Set.Ioi 0)) ∧
        Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2)) atTop (𝓝 1)

end SubcriticalCauchy.Bienayme

namespace SubcriticalCauchy.Bienayme
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

/-- The real-valued version of the paper's integer increment. -/
def offspringIncrement (k : ℕ) : ℝ := (k : ℝ) - 1

end
end SubcriticalCauchy.Bienayme

namespace SubcriticalCauchy.Bienayme
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

/-- `P(X ≥ x)` for the increment `X = ξ - 1`, `ξ ~ μ` (closed inequality). -/
def incrementTail (μ : Measure ℕ) (x : ℝ) : ℝ≥0∞ := μ {k : ℕ | x ≤ (k : ℝ) - 1}

end
end SubcriticalCauchy.Bienayme

namespace SubcriticalCauchy.Bienayme

/-- Delete exactly the first occurrence of the maximum count (the paper's first maximum). -/
def deleteMaxCounts (ds : List ℕ) : List ℕ := ds.erase (listMaxDegree ds)

/-- The remaining source increments, in their original relative order. -/
def deletedMaximumWord (ds : List ℕ) : List ℤ :=
  (deleteMaxCounts ds).map (fun d : ℕ => (d : ℤ) - 1)

end SubcriticalCauchy.Bienayme

namespace SubcriticalCauchy.Bienayme.MaximumSwapLaw
noncomputable section
-- Classical decidability is copied from the development; it does not affect the meaning.
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BGW

/-- Law of `(ξ_1, …, ξ_n)` i.i.d. `μ` conditioned on `∑ ξ_i = n - 1` (the bridge `W_n = -1`
of the paper), as a measure on `Fin n → ℕ`; zero if that event is null (Mathlib convention). -/
def bridgeCountsLaw (μ : Measure ℕ) (n : ℕ) : Measure (Fin n → ℕ) :=
  (Measure.pi fun _ : Fin n => μ)[|countBridges n]

end
end SubcriticalCauchy.Bienayme.MaximumSwapLaw

namespace SubcriticalCauchy.Bienayme
noncomputable section
open MeasureTheory

/-- The law of one increment `X = ξ - 1`. -/
def incrementLaw (μ : Measure ℕ) : Measure ℤ := μ.map (fun k : ℕ => (k : ℤ) - 1)

/-- The `n - 1` increments `ω_i - 1` left after deleting the first maximal one, as a vector in
`ℤ`. The `getD` default `0` is never used for `n ≥ 1`; for `n = 0` the index type is empty. -/
def deletedIncrements (n : ℕ) (ω : Fin n → ℕ) : Fin (n - 1) → ℤ :=
  fun i => (deletedMaximumWord (List.ofFn ω)).getD i 0

end
end SubcriticalCauchy.Bienayme

namespace SubcriticalCauchy.Bienayme
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

/-- Mean of the increment truncated in absolute value at `r`. -/
def truncatedIncrementMean (μ : Measure ℕ) (r : ℝ) : ℝ :=
  ∫ k : ℕ, (if |offspringIncrement k| ≤ r then offspringIncrement k else 0) ∂μ

/-- The paper's `b_n = n E[X 1_{|X| ≤ a_n}]`, with real cutoff `a_n` (no rounding). -/
def centering (μ : Measure ℕ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * truncatedIncrementMean μ (a n)

end
end SubcriticalCauchy.Bienayme

namespace SubcriticalCauchy.Bienayme
noncomputable section
open MeasureTheory

/-- `ν` is the law of `𝒞₁`: `E[e^{-λ𝒞₁}] = e^{λ log λ}` for all `λ > 0` (existence:
`exists_cauchyOneLaw`). -/
def IsCauchyOneLaw (ν : Measure ℝ) : Prop :=
  IsProbabilityMeasure ν ∧ ∀ s : ℝ, 0 < s →
    Integrable (fun x => Real.exp (-(s * x))) ν ∧
      -- `∫ x, Real.exp (-(s * x)) ∂ν`, written with an explicit `NormedSpace ℝ ℝ` argument:
      -- with this file's imports instance search could return a different (propositionally
      -- equal) term, so the development's term is spelled out to agree as a kernel term.
      @integral ℝ ℝ _ NormedField.toNormedSpace _ ν (fun x => Real.exp (-(s * x))) =
        Real.exp (s * Real.log s)

end
end SubcriticalCauchy.Bienayme

namespace SubcriticalCauchy.Bienayme
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

/-- Kennedy equivalence: `μ_k = a r^k ν_k` for all `k`, some `a, r > 0` (the paper's `λ` is `r`). -/
def IsTiltEquivalent (μ ν : Measure ℕ) : Prop :=
  ∃ a r : ℝ, 0 < a ∧ 0 < r ∧ ∀ k : ℕ, (μ {k}).toReal = a * r ^ k * (ν {k}).toReal

/-- The heavy tail `μ_n ∼ L(n)/n^{1+α}`, with `L` the slowly varying function. -/
def HasHeavyTail (μ : Measure ℕ) (α : ℝ) (L : ℝ → ℝ) : Prop :=
  Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ (1 + α))) atTop (𝓝 1)

end
end SubcriticalCauchy.Bienayme

namespace SubcriticalCauchy
noncomputable section
open MeasureTheory

namespace ArmendarizLoulakis
/-- The first index of a maximal coordinate. -/
def firstMaxIndex {n : ℕ} (x : Fin (n + 1) → ℝ) : Fin (n + 1) :=
  (Finset.univ.filter fun i => ∀ j, x j ≤ x i).min' (by
    obtain ⟨i, -, hi⟩ := Finset.univ.exists_max_image x Finset.univ_nonempty
    exact ⟨i, by simpa using hi⟩)

/-- Armendáriz–Loulakis' `π ∘ T`: swap the first maximal coordinate of `x : Fin n → ℝ` with the
last and drop the last (zero-based; vacuous for `n = 0`). -/
def alSwapDrop : (n : ℕ) → (Fin n → ℝ) → (Fin (n - 1) → ℝ)
  | 0, _ => fun i => i.elim0
  | n + 1, x => fun i => x (Equiv.swap (firstMaxIndex x) (Fin.last n) i.castSucc)

end ArmendarizLoulakis

namespace Bienayme
/-- The law of `X̄ = X + (1 - m)` on `ℝ` (`m` via `toReal`; used only when `m < 1`). -/
def centeredIncrementLaw (μ : Measure ℕ) : Measure ℝ :=
  (incrementLaw μ).map fun k : ℤ => (k : ℝ) + (1 - (offspringMean μ).toReal)

end Bienayme
end
end SubcriticalCauchy

namespace SubcriticalCauchy.Bienayme
noncomputable section
open MeasureTheory
open BGW BGW.LocallyFinite

/-- The first `k` child subtrees of the maximal vertex, children numbered from `1`. Missing
children (`i > Δ`) are padded with `leaf` (one vertex), whereas the paper pads with the empty
tree `∅`; immaterial for Proposition 4.2, as `Δ ≥ ⌊δ n⌋` with probability tending to one. -/
def attachedSlotsTree (k : ℕ) (t : PlaneTree) : Fin k → Tree :=
  fun i => ((attachedChild t (i.val + 1)).getD PlaneTree.leaf).toLocallyFinite

/-- Law of the first `k` attached subtrees under `𝒯_n`: a countable mixture over finite plane
trees `t` of Dirac masses weighted by `conditioned μ n {t}`. -/
def attachedSlotsLaw (μ : Measure ℕ) [IsProbabilityMeasure μ] (n k : ℕ) :
    Measure (Fin k → Tree) :=
  Measure.sum fun t : PlaneTree =>
    conditioned μ n {t.toLocallyFinite} • Measure.dirac (attachedSlotsTree k t)

end
end SubcriticalCauchy.Bienayme

namespace SubcriticalCauchy
open MeasureTheory Filter
open scoped ENNReal Topology

/-- The paper's `ℓ*(n) = ∑_{k ≥ n} L(k)/k` (`0` if not summable, by `tsum`). -/
noncomputable def ellStar (L : ℝ → ℝ) (n : ℕ) : ℝ :=
  tailMass (fun k : ℕ => L k / (k : ℝ)) n

end SubcriticalCauchy

namespace SubcriticalCauchy
open MeasureTheory Filter
open scoped Topology

/-- `ℓ*` at a real argument: `ℓ*(⌊x⌋)`, for the paper's `ℓ*(a_n)` at real `a_n`. -/
noncomputable def ellStarReal (L : ℝ → ℝ) (x : ℝ) : ℝ := ellStar L ⌊x⌋₊

end SubcriticalCauchy

namespace SubcriticalCauchy.Bienayme
noncomputable section
open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Topology
open BGW BGW.LocallyFinite

-- Targets (Comparator holes): the proofs are in `SubcriticalCauchy`.

/-- Theorem 1.1 (i), first part: `Δ(𝒯_n) / (n (1 - m)) → 1` in probability, where `𝒯_n` is the
`μ`-tree conditioned on `n` vertices. -/
theorem main_maxDegree_condensation (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => conditioned μ n (finiteTreeEvent fun t =>
        ε < |(maxDegree t : ℝ) / ((n : ℝ) * (1 - (offspringMean μ).toReal)) - 1|))
      atTop (𝓝 0) := by
  sorry

/-- Theorem 1.1 (i), second part: `Δ²(𝒯_n) / n → 0` in probability (second largest outdegree). -/
theorem main_secondMaxDegree_negligible (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => conditioned μ n (finiteTreeEvent fun t =>
        ε < (secondMaxDegree t : ℝ) / n))
      atTop (𝓝 0) := by
  sorry

/-- Theorem 1.1 (ii): `P(H_Δ(𝒯_n) = j) → (1 - m) m^j`, `H_Δ` the depth of the first
maximal-degree vertex. -/
theorem main_maxDegreeDepth_geometric (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (j : ℕ) :
    Tendsto (fun n : ℕ => conditioned μ n (finiteTreeEvent fun t => maxDegreeDepth t = j))
      atTop (𝓝 (ENNReal.ofReal
        ((1 - (offspringMean μ).toReal) * (offspringMean μ).toReal ^ j))) := by
  sorry

/-- Theorem 1.1 (iii)(a): `H(𝒯_n) / log n → 1 / log(1/m)` in probability. -/
theorem main_height_log (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => conditioned μ n (finiteTreeEvent fun t =>
        ε < |(height t : ℝ) / Real.log n - 1 / Real.log (1 / (offspringMean μ).toReal)|))
      atTop (𝓝 0) := by
  sorry

/-- Theorem 1.1 (iii)(b): `H(𝒯_n) - log n / log(1/m)` is tight iff `∑ k log k · μ_k < ∞`. -/
theorem main_height_tight_iff (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) :
    (∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ n : ℕ, 1 ≤ n →
        conditioned μ n (finiteTreeEvent fun t =>
          K < |(height t : ℝ) - Real.log n / Real.log (1 / (offspringMean μ).toReal)|)
          ≤ ENNReal.ofReal ε) ↔
      Summable (fun k : ℕ => (k : ℝ) * Real.log k * (μ {k}).toReal) := by
  sorry

/-- Theorem 3.1, by the direct route (D12): given `W_n = -1`, the `n - 1` increments left after
deleting the first maximum are asymptotically i.i.d. increments in total variation. -/
theorem paper_deleted_maximum_tvDist (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) :
    Tendsto (fun n : ℕ => tvDist ((MaximumSwapLaw.bridgeCountsLaw μ n).map (deletedIncrements n))
        (Measure.pi fun _ : Fin (n - 1) => incrementLaw μ))
      atTop (𝓝 0) := by
  sorry

/-- Proposition 4.2: for `δ ∈ [0, 1 - m)`, the first `⌊δ n⌋` subtrees attached to the maximal
vertex of `𝒯_n` are asymptotically independent `μ`-trees in total variation (padding: see
`attachedSlotsTree`). -/
theorem paper_attached_forest_tvDist (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1 - (offspringMean μ).toReal) :
    Tendsto (fun n : ℕ =>
        tvDist (attachedSlotsLaw μ n ⌊δ * n⌋₊) (forestLaw μ ⌊δ * n⌋₊))
      atTop (𝓝 0) := by
  sorry

/-- Proposition 4.3 (i): if `h_n > 0`, `h_n → ∞`, `n Q_{h_n} → ∞` then `P(H(𝒯_n) ≥ h_n) → 1`;
`Q_h` is `survival μ ⌈h⌉₊`, as `H` is integer valued. -/
theorem paper_height_lower (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (h : ℕ → ℝ)
    (hpos : ∀ n, 0 < h n) (hh : Tendsto h atTop atTop)
    (hQ : Tendsto (fun n : ℕ => (n : ℝ) * (survival μ ⌈h n⌉₊).toReal) atTop atTop) :
    Tendsto (fun n : ℕ => conditioned μ n (finiteTreeEvent fun t => h n ≤ (height t : ℝ)))
      atTop (𝓝 1) := by
  sorry

/-- Proposition 4.3 (ii): if `h_n > 0`, `h_n → ∞`, `n Q_{h_n} → 0` then `P(H(𝒯_n) < h_n) → 1`. -/
theorem paper_height_upper (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (h : ℕ → ℝ)
    (hpos : ∀ n, 0 < h n) (hh : Tendsto h atTop atTop)
    (hQ : Tendsto (fun n : ℕ => (n : ℝ) * (survival μ ⌈h n⌉₊).toReal) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => conditioned μ n (finiteTreeEvent fun t => (height t : ℝ) < h n))
      atTop (𝓝 1) := by
  sorry

/-- Existence of the law of `𝒞₁` (Section 2.3), needed to state (2.4). -/
theorem exists_cauchyOneLaw : ∃ ν : Measure ℝ, IsCauchyOneLaw ν := by
  sorry

/-- Equation (2.4), corrected version (R9): `(W_n - b_n)/a_n → 𝒞₁ + (1 - γ_E)` in distribution
(`n P(X ≥ a_n) → 1`); the paper omits the shift `1 - γ_E`. Stated via bounded continuous `f`. -/
theorem paper_stable_limit (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal) atTop (𝓝 1))
    (ν : Measure ℝ) (hν : IsCauchyOneLaw ν) (f : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (fun n : ℕ => ∫ x, f (((∑ i, (x i : ℝ)) - centering μ a n) / a n)
        ∂(Measure.pi fun _ : Fin n => incrementLaw μ))
      atTop (𝓝 (∫ y, f (y + (1 - Real.eulerMascheroniConstant)) ∂ν)) := by
  sorry

/-- Corollary 4.1, corrected version (R9): `(Δ(𝒯_n) + b_n)/a_n → -𝒞₁ - (1 - γ_E)` in
distribution; the paper omits `1 - γ_E`. -/
theorem paper_maxDegree_fluctuations (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal) atTop (𝓝 1))
    (ν : Measure ℝ) (hν : IsCauchyOneLaw ν) (f : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (fun n : ℕ => ∑' t : PlaneTree, (conditioned μ n {t.toLocallyFinite}).toReal *
        f (((maxDegree t : ℝ) + centering μ a n) / a n))
      atTop (𝓝 (∫ y, f (-y - (1 - Real.eulerMascheroniConstant)) ∂ν)) := by
  sorry

/-- Proposition 4.5 (i) (`β = 1`): for `μ_n ~ c/(n² log² n)`,
`H(𝒯_n) = log n/log(1/m) - (c/(m log(1/m)²)) log log n + o(log log n)` in probability. -/
theorem paper_height_second_order_log (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (c : ℝ) (hc : 0 < c)
    (htail : Tendsto (fun n : ℕ =>
        (μ {n}).toReal / (c / ((n : ℝ) ^ 2 * Real.log n ^ 2))) atTop (𝓝 1))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => conditioned μ n (finiteTreeEvent fun t =>
        ε * Real.log (Real.log n) ≤
          |(height t : ℝ) - Real.log n / Real.log (1 / (offspringMean μ).toReal) +
            c / ((offspringMean μ).toReal * Real.log (1 / (offspringMean μ).toReal) ^ 2) *
              Real.log (Real.log n)|))
      atTop (𝓝 0) := by
  sorry

/-- Proposition 4.5 (ii), corrected version (R10), for `μ_n ~ c/(n² log^{1+β} n)`, `0 < β < 1`:
the term is `c/((1-β) β m log(1/m)²) (log n)^{1-β}`; the paper has `log(1/m)^{1+β}` there. -/
theorem paper_height_second_order_pow (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (c β : ℝ) (hc : 0 < c)
    (hβ0 : 0 < β) (hβ1 : β < 1)
    (htail : Tendsto (fun n : ℕ =>
        (μ {n}).toReal / (c / ((n : ℝ) ^ 2 * Real.log n ^ (1 + β)))) atTop (𝓝 1))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => conditioned μ n (finiteTreeEvent fun t =>
        ε * Real.log n ^ (1 - β) ≤
          |(height t : ℝ) - Real.log n / Real.log (1 / (offspringMean μ).toReal) +
            c / ((1 - β) * β * (offspringMean μ).toReal *
                Real.log (1 / (offspringMean μ).toReal) ^ 2) *
              Real.log n ^ (1 - β)|))
      atTop (𝓝 0) := by
  sorry

/-- Berger's local limit ([Ber17], Theorem 2.4, `α = 1`) in the form the paper's proof uses:
`P(W_n = z + ⌊b_n⌋) ~ n P(X = z)` uniformly in `z ≥ R a_n`, `R` large; not the published
theorem. -/
theorem berger_local_limit (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal) atTop (𝓝 1)) :
    ∀ τ > 0, ∃ N : ℕ, ∃ R : ℝ, ∀ n ≥ N, ∀ z : ℤ, R * a n ≤ z →
      |((Measure.pi fun _ : Fin n => incrementLaw μ)
            {x | ∑ i, x i = z + ⌊centering μ a n⌋}).toReal /
          ((n : ℝ) * (incrementLaw μ {z}).toReal) - 1| ≤ τ := by
  sorry

/-- Condition (2.6) of Armendáriz–Loulakis for `X̄ = X + (1 - m)`, uniformly in `x ≥ ε n`:
`P(W̄_n ∈ (x, x+1]) ~ n P(X̄ ∈ (x, x+1])` (the paper's `eq:26` after the shift by `m_n`). -/
theorem paper_eq26 (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (ε : ℝ) (hε : 0 < ε) :
    ∀ τ > 0, ∀ᶠ n : ℕ in atTop, ∀ x : ℝ, ε * n ≤ x →
      |((Measure.pi fun _ : Fin n => centeredIncrementLaw μ)
            {y | ∑ i, y i ∈ Set.Ioc x (x + 1)}).toReal /
          ((n : ℝ) * (centeredIncrementLaw μ (Set.Ioc x (x + 1))).toReal) - 1| ≤ τ := by
  sorry

/-- Condition (3.3) of AL for `X̄` with `b̂_n = n ℓ*(a_n)` (the paper's `eq:33`), together with
tightness of `W̄_n / b̂_n`, `a_n = o(b̂_n)` and `(b_n + (1-m) n)/b̂_n → -1`; stronger than
`eq:33` alone. -/
theorem paper_eq33 (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : offspringMean μ < 1) (L : ℝ → ℝ) (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hsv : IsSlowlyVaryingAtTop L) (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2)) atTop (𝓝 1))
    (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal) atTop (𝓝 1)) :
    (∀ τ > 0, ∃ K : ℝ, ∀ᶠ n : ℕ in atTop,
        ((Measure.pi fun _ : Fin n => centeredIncrementLaw μ)
          {y | K * ((n : ℝ) * ellStarReal L (a n)) < |∑ i, y i|}).toReal ≤ τ) ∧
      Tendsto (fun n : ℕ => a n / ((n : ℝ) * ellStarReal L (a n))) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => (centering μ a n + (1 - (offspringMean μ).toReal) * n) /
          ((n : ℝ) * ellStarReal L (a n))) atTop (𝓝 (-1)) ∧
      ∀ ε > 0, ∀ A > 0, ∀ τ > 0, ∀ᶠ n : ℕ in atTop, ∀ x y : ℝ, ε * n ≤ x →
        |y| ≤ A * ((n : ℝ) * ellStarReal L (a n)) →
        |1 - (centeredIncrementLaw μ (Set.Ioc (x - y) (x - y + 1))).toReal /
            (centeredIncrementLaw μ (Set.Ioc x (x + 1))).toReal| ≤ τ := by
  sorry

/-- Theorem 3.1 again: the same statement as `paper_deleted_maximum_tvDist`, proved by the
paper's route (`al_criterion`, `paper_eq26`, `paper_eq33`, `berger_local_limit`). -/
theorem paper_route_deleted_maximum_tvDist (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) :
    Tendsto (fun n : ℕ => tvDist ((MaximumSwapLaw.bridgeCountsLaw μ n).map (deletedIncrements n))
        (Measure.pi fun _ : Fin (n - 1) => incrementLaw μ))
      atTop (𝓝 0) := by
  sorry

/-- Section 2.2 five-case classification, corrected version (R13): `ν₀ > 0` is added. If
`ν_n ~ L(n)/n^{1+α}`, a Kennedy-equivalent `μ` is critical (finite variance; or infinite
variance, `1 < α ≤ 2`; or `α = 1`) or subcritical (`α > 1`; or `α = 1`). -/
theorem paper_heavyTail_classification (ν : Measure ℕ) [IsProbabilityMeasure ν]
    (hν0 : 0 < ν {0}) (α : ℝ) (hα : 0 ≤ α) {L : ℝ → ℝ}
    (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : HasHeavyTail ν α L) :
    ∃ μ : Measure ℕ, IsProbabilityMeasure μ ∧ IsTiltEquivalent μ ν ∧
      ((offspringMean μ = 1 ∧ ∑' k : ℕ, (k : ℝ≥0∞) ^ 2 * μ {k} < ∞) ∨
        (offspringMean μ = 1 ∧ ∑' k : ℕ, (k : ℝ≥0∞) ^ 2 * μ {k} = ∞ ∧ 1 < α ∧ α ≤ 2 ∧
          HasHeavyTail μ α L) ∨
        (offspringMean μ = 1 ∧ α = 1 ∧ HasHeavyTail μ α L) ∨
        (offspringMean μ < 1 ∧ 1 < α ∧ HasHeavyTail μ α L) ∨
        (offspringMean μ < 1 ∧ α = 1 ∧ HasHeavyTail μ α L)) := by
  sorry

end
end SubcriticalCauchy.Bienayme

namespace SubcriticalCauchy.ArmendarizLoulakis
noncomputable section
open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Topology

/-- **AL criterion** (Armendáriz–Loulakis, Theorem 1, in the form of its proof,
§§2–3): conditions (2.6) at thresholds `d n`, (3.2) at thresholds `ℓ n` with
scale `c n`, tightness of `S_{n-1}/c n`, and a maximum-tail condition give,
uniformly over `x ≥ max (d n) (ℓ n)`, total variation convergence of the
conditional law of `π T X` given `S_n ∈ x + Δ` to the iid law. AL's
Theorem 1 itself asserts only that some threshold `q_n` exists; this criterion
supplies `q_n = max (d n) (ℓ n)` directly, and its hypothesis `hmax` replaces
AL's maximum-tail bound (3.8), which their proof uses only through
`n P(X̄ > ℓ_n - A c_n) → 0`. No `Δ`-subexponentiality is assumed. It is in the form the
proof uses, not the published theorem. `tvDist` is Mathlib's, twice the paper's. -/
theorem al_criterion (ν : Measure ℝ) [IsProbabilityMeasure ν] (d ℓ c : ℕ → ℝ)
    (hc : ∀ᶠ n : ℕ in atTop, 0 < c n)
    (hℓc : Tendsto (fun n : ℕ => ℓ n / c n) atTop atTop)
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
  sorry

end
end SubcriticalCauchy.ArmendarizLoulakis
