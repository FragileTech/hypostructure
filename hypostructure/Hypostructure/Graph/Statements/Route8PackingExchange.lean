import Hypostructure.Graph.Statements.Spine
import Hypostructure.Graph.LocalRigidity

/-!
# Statements: exchange at the maximum packing `P₀` (route 8, keys `9800`–`9802`)

`P₀ = canonicalWindowPacking` is a maximum window packing (`canonicalWindowPacking_spec`), and
`R` is its remainder.  A window packing only asks for vertex-disjoint supports; its members
may be adjacent.  Hence:

* `Route8PackingExchangeStatement` (key `9800`): for every `Q ⊆ P₀` and every window packing
  `W` of G whose members lie in `(⋃ Q) ∪ R`, `|W| ≤ |Q|` (`W ∪ (P₀ \ Q)` is a packing).
* `Route8ArmExchangeStatement` (key `9801`): at a window `P ∈ P₀` placed by `p`, two
  vertex-disjoint arms `α`, `β` (induced paths inside `R`, on `a + 1` and `b + 1` vertices)
  ending at `x = α (last a) ~ p i` and `y = β (last b) ~ p j`, and two disjoint runs of
  positions `S_x ∋ i`, `S_y ∋ j` (with `i`, `j` an end) of sizes `order − (a+1)` and
  `order − (b+1)`, such that `x — p i` is the only edge between `α` and `p(S_x)` (same for
  `y`), do not exist: `α ∪ p(S_x)` and `β ∪ p(S_y)` would be two disjoint windows inside
  `P ∪ R`.
* `Route8FullArmLandingCapStatement` (key `9802`): two arms on `order − 1` vertices in `R`
  ending at neighbours of distinct positions `p i ≠ p j`, each meeting its landing vertex only
  at its end, intersect (key `9801` with singleton runs).
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

/-- **Key `9800`: the `k`-fold exchange at `P₀`.**  For every subfamily `Q ⊆ P₀` and every
window packing `W` of G whose members lie in `(⋃ Q) ∪ R` (`R` the remainder of `P₀`):
`|W| ≤ |Q|`. -/
def Route8PackingExchangeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  let packing := canonicalWindowPacking data object
  let remainder := object.remainderSupport packing
  ∀ Q ⊆ packing, ∀ W : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder W →
    (∀ S ∈ W, ∀ v ∈ S, (∃ M ∈ Q, v ∈ M) ∨ v ∈ remainder) →
    W.card ≤ Q.card

/-- **Key `9801`: arm exchange at one window of `P₀`.**  For a window `P ∈ P₀` placed by
`p`, arms `α : Fin (a+1) → V`, `β : Fin (b+1) → V` (induced paths inside `R`, i.e. window
placements of their image inside the remainder) with disjoint vertex sets, positions `i`, `j`
with `α (last a) ~ p i`, `β (last b) ~ p j`, runs `[lx, lx+mx]` and `[ly, ly+my]` of positions
(disjoint, inside the window), with `i` an end of the first and `j` an end of the second,
sizes `(a+1) + (mx+1) = order` and `(b+1) + (my+1) = order`, and the side conditions that the
only edge between `α` and `p[lx, lx+mx]` is `α (last a) — p i` (same for `β`): `False`. -/
def Route8ArmExchangeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  let packing := canonicalWindowPacking data object
  let remainder := object.remainderSupport packing
  ∀ P ∈ packing, ∀ p : Fin data.windowOrder → object.Vertex,
    Graph.LocalRigidity.IsWindowPlacement object P p →
    ∀ (a b : Nat) (α : Fin (a + 1) → object.Vertex) (β : Fin (b + 1) → object.Vertex),
      Graph.LocalRigidity.IsWindowPlacement object remainder α →
      Graph.LocalRigidity.IsWindowPlacement object remainder β →
      (∀ k k', α k ≠ β k') →
      ∀ (i j : Fin data.windowOrder) (lx mx ly my : Nat),
        lx + mx < data.windowOrder → ly + my < data.windowOrder →
        (i.1 = lx ∨ i.1 = lx + mx) → (j.1 = ly ∨ j.1 = ly + my) →
        (lx + mx < ly ∨ ly + my < lx) →
        (a + 1) + (mx + 1) = data.windowOrder → (b + 1) + (my + 1) = data.windowOrder →
        object.graph.Adj (α (Fin.last a)) (p i) → object.graph.Adj (β (Fin.last b)) (p j) →
        (∀ k (t : Fin data.windowOrder), lx ≤ t.1 → t.1 ≤ lx + mx →
          object.graph.Adj (α k) (p t) → k = Fin.last a ∧ t = i) →
        (∀ k (t : Fin data.windowOrder), ly ≤ t.1 → t.1 ≤ ly + my →
          object.graph.Adj (β k) (p t) → k = Fin.last b ∧ t = j) →
        False

/-- **Key `9802`: full arms landing on one window of `P₀` intersect.**  For a window
`P ∈ P₀` placed by `p`, two arms `α`, `β` on `order − 1` vertices (induced paths inside `R`)
ending at `α (last a) ~ p i` and `β (last a) ~ p j` with `i ≠ j`, where `p i` is adjacent to
no vertex of `α` other than its end (same for `p j` and `β`): the arms share a vertex. -/
def Route8FullArmLandingCapStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  let packing := canonicalWindowPacking data object
  let remainder := object.remainderSupport packing
  ∀ P ∈ packing, ∀ p : Fin data.windowOrder → object.Vertex,
    Graph.LocalRigidity.IsWindowPlacement object P p →
    ∀ (a : Nat) (α β : Fin (a + 1) → object.Vertex), a + 2 = data.windowOrder →
      Graph.LocalRigidity.IsWindowPlacement object remainder α →
      Graph.LocalRigidity.IsWindowPlacement object remainder β →
      ∀ i j : Fin data.windowOrder, i ≠ j →
        object.graph.Adj (α (Fin.last a)) (p i) → object.graph.Adj (β (Fin.last a)) (p j) →
        (∀ k, object.graph.Adj (α k) (p i) → k = Fin.last a) →
        (∀ k, object.graph.Adj (β k) (p j) → k = Fin.last a) →
        ∃ k k', α k = β k'

end Hypostructure.Graph.Strategy.Spine
