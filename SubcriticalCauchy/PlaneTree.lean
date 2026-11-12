module

public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Finite plane trees

A finite rooted ordered tree is a root together with a finite ordered list of
child trees. Its preorder outdegree list records the number of children of each
vertex. This is the finite combinatorial carrier used in Section 2.1 of the paper.
-/

@[expose] public section

namespace SubcriticalCauchy

/-- Finite rooted ordered trees, including the one-vertex tree. -/
inductive PlaneTree where
  | node (children : List PlaneTree)

noncomputable instance : DecidableEq PlaneTree := Classical.decEq _

namespace PlaneTree

/-- Outdegrees in preorder (lexicographic vertex order). -/
def degrees : PlaneTree → List ℕ
  | .node children => children.length :: children.flatMap degrees

/-- Number of vertices. -/
def size (t : PlaneTree) : ℕ := t.degrees.length

/-- Number of edges, computed as the sum of outdegrees. -/
def edges (t : PlaneTree) : ℕ := t.degrees.sum

@[simp] theorem degrees_node (children : List PlaneTree) :
    degrees (.node children) = children.length :: children.flatMap degrees := by
  rw [degrees]

@[simp] theorem size_node (children : List PlaneTree) :
    size (.node children) = (children.map size).sum + 1 := by
  change (degrees (.node children)).length = _
  rw [degrees_node, List.length_cons, List.length_flatMap]
  rfl

theorem size_pos (t : PlaneTree) : 0 < t.size := by
  cases t with
  | node children => simp [size]

/-- Every finite tree has one more vertex than edge. -/
theorem edges_add_one (t : PlaneTree) : t.edges + 1 = t.size := by
  induction t using PlaneTree.rec
    (motive_2 := fun ts => (ts.flatMap degrees).sum + ts.length =
      (ts.flatMap degrees).length) with
  | node children ih =>
    simp only [edges, size, degrees_node, List.sum_cons, List.length_cons]
    omega
  | nil => simp
  | cons t ts iht ih =>
    simp only [List.flatMap_cons, List.sum_append, List.length_cons,
      List.length_append]
    change t.degrees.sum + 1 = t.degrees.length at iht
    omega

theorem edges_eq_size_sub_one (t : PlaneTree) : t.edges = t.size - 1 := by
  have := t.edges_add_one
  omega

/-- Product of offspring weights over the vertices, in preorder. -/
def weight {M : Type*} [CommMonoid M] (μ : ℕ → M) (t : PlaneTree) : M :=
  (t.degrees.map μ).prod

/-- The combinatorial identity behind exponential tilting (Proposition 2.1).
It holds for arbitrary commutative-monoid weights. -/
theorem weight_tilt {M : Type*} [CommMonoid M] {μ ν : ℕ → M} {a r : M}
    (h : ∀ k, μ k = a * r ^ k * ν k) (t : PlaneTree) :
    weight μ t = a ^ t.size * r ^ (t.size - 1) * weight ν t := by
  have hlist (ks : List ℕ) :
      (ks.map μ).prod = a ^ ks.length * r ^ ks.sum * (ks.map ν).prod := by
    induction ks with
    | nil => simp
    | cons k ks ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons,
        List.sum_cons, h k, ih, pow_succ, pow_add]
      ac_rfl
  have hsum : t.degrees.sum = t.size - 1 := t.edges_eq_size_sub_one
  simpa only [weight, size, hsum] using hlist t.degrees

end PlaneTree
end SubcriticalCauchy
