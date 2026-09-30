import Hypostructure.Graph.Statements.Spine
import Hypostructure.Graph.LocalRigidity
import Hypostructure.Graph.WindowExchange.X15Data
import Hypostructure.Graph.WindowExchange.Rungs

/-!
# Statements: exchanges at one window of `P₀` (route 8, keys `9810`–`9812`)

`P₀ = canonicalWindowPacking` is a maximum window packing and `R` its remainder.

* `Route8X15DoubleLandingStatement` (key `9810`, window order 13): an induced copy `e` of
  `X15` inside `R` whose only edges to a window `P ∈ P₀` (placed by `p`) are `e a — p i` and
  `e b — p j`, for two distinct exits `a, b ∈ {4, 6, 9}`, has `{a, b} = {6, 9}` and
  `{i, j}` one of `{0,10}`, `{0,11}`, `{1,11}`, `{1,12}`, `{2,12}`.  The exit `4` never
  double-lands, and the positions `{0, 12}` are excluded by the exchange: `C ∪ P` then holds
  two disjoint induced 13-vertex paths.
* `Route8ArmPairTriggerStatement` (key `9811`): two vertex-disjoint arms in `R` (induced
  paths) landing at positions `i < j` of one window `P ∈ P₀`, on at least `order − 1 − i` and
  `j` vertices, meeting `p[0..i]` resp. `p[j..order−1]` only at their landing edges, do not
  exist.  At order 13: arms of lengths `(12 − i, j)` trigger.
* `Route8X15HeavyPairStatement` (key `9812`, window order 13): two distinct windows
  `P, Q ∈ P₀` whose vertices have degree at most 3, and an induced copy of `X15` inside `R`
  with exits `x ≠ y` landing on `P` and on `Q`: at most 6 rungs `P — Q` when `4 ∈ {x, y}`,
  at most 8 when `{x, y} = {6, 9}`.  So a heavy pair (at least 9 rungs) carries no copy of
  `X15` with exits on both of its windows.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

/-- **Key `9810`: legal double landings of one copy of `X15` on one window of `P₀`.**  At
window order 13, for a window `P ∈ P₀` placed by `p`, an induced copy
`e : X15 ↪g G` with every vertex in `R`, two distinct exits `a, b` of `X15` and positions
`i, j` such that the edges between the copy and `P` are exactly `e a — p i` and
`e b — p j`: `{a, b} = {6, 9}` and `(min i j, max i j)` is `(0,10)`, `(0,11)`, `(1,11)`,
`(1,12)` or `(2,12)`. -/
def Route8X15DoubleLandingStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  let packing := canonicalWindowPacking data object
  let remainder := object.remainderSupport packing
  data.windowOrder = 13 →
  ∀ P ∈ packing, ∀ p : Fin 13 → object.Vertex,
    Graph.LocalRigidity.IsWindowPlacement object P p →
    ∀ e : Graph.WindowExchange.x15Graph ↪g object.graph, (∀ u, e u ∈ remainder) →
    ∀ a b : Fin 15, a.1 ∈ Graph.WindowExchange.x15Exits →
      b.1 ∈ Graph.WindowExchange.x15Exits → a ≠ b →
    ∀ i j : Fin 13,
      (∀ u k, object.graph.Adj (e u) (p k) ↔ (u = a ∧ k = i) ∨ (u = b ∧ k = j)) →
      ((a.1 = 6 ∧ b.1 = 9) ∨ (a.1 = 9 ∧ b.1 = 6)) ∧
        (min i.1 j.1, max i.1 j.1) ∈ [(0, 10), (0, 11), (1, 11), (1, 12), (2, 12)]

/-- **Key `9811`: two arms on one window of `P₀` trigger.**  For a window `P ∈ P₀` placed
by `p`, arms `α : Fin (a+1) → V`, `β : Fin (b+1) → V` (induced paths inside `R`) with
disjoint vertex sets, positions `i < j` with `α (last a) ~ p i`, `β (last b) ~ p j`, lengths
`order ≤ (a+1) + (i+1)` and `order ≤ (b+1) + (order − j)`, and the side conditions that the
only edge between `α` and `p[0..i]` is `α (last a) — p i` and the only edge between `β` and
`p[j..order−1]` is `β (last b) — p j`: `False`. -/
def Route8ArmPairTriggerStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  let packing := canonicalWindowPacking data object
  let remainder := object.remainderSupport packing
  ∀ P ∈ packing, ∀ p : Fin data.windowOrder → object.Vertex,
    Graph.LocalRigidity.IsWindowPlacement object P p →
    ∀ (a b : Nat) (α : Fin (a + 1) → object.Vertex) (β : Fin (b + 1) → object.Vertex),
      Graph.LocalRigidity.IsWindowPlacement object remainder α →
      Graph.LocalRigidity.IsWindowPlacement object remainder β →
      (∀ k k', α k ≠ β k') →
      ∀ i j : Fin data.windowOrder, i.1 < j.1 →
        data.windowOrder ≤ (a + 1) + (i.1 + 1) →
        data.windowOrder ≤ (b + 1) + (data.windowOrder - j.1) →
        object.graph.Adj (α (Fin.last a)) (p i) → object.graph.Adj (β (Fin.last b)) (p j) →
        (∀ k (t : Fin data.windowOrder), t.1 ≤ i.1 →
          object.graph.Adj (α k) (p t) → k = Fin.last a ∧ t = i) →
        (∀ k (t : Fin data.windowOrder), j.1 ≤ t.1 →
          object.graph.Adj (β k) (p t) → k = Fin.last b ∧ t = j) →
        False

/-- **Key `9812`: a copy of `X15` with exits on two windows of `P₀` bounds their rungs.**  At
window order 13, for distinct windows `P, Q ∈ P₀` placed by `p`, `q`, every vertex of which
has degree at most 3, an induced copy `e : X15 ↪g G` with every vertex in `R`, and two
distinct exits `x`, `y` of `X15` with `e x ~ p a` and `e y ~ q b`: the rungs
`{(i, j) : p i ~ q j}` number at most `6` if `4 ∈ {x, y}` and at most `8` otherwise. -/
def Route8X15HeavyPairStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  let packing := canonicalWindowPacking data object
  let remainder := object.remainderSupport packing
  data.windowOrder = 13 →
  ∀ P ∈ packing, ∀ Q ∈ packing, P ≠ Q → ∀ p q : Fin 13 → object.Vertex,
    Graph.LocalRigidity.IsWindowPlacement object P p →
    Graph.LocalRigidity.IsWindowPlacement object Q q →
    (∀ k, object.degree (p k) ≤ 3 ∧ object.degree (q k) ≤ 3) →
    ∀ e : Graph.WindowExchange.x15Graph ↪g object.graph, (∀ u, e u ∈ remainder) →
    ∀ x y : Fin 15, x.1 ∈ Graph.WindowExchange.x15Exits →
      y.1 ∈ Graph.WindowExchange.x15Exits → x ≠ y →
    ∀ a b : Fin 13, object.graph.Adj (e x) (p a) → object.graph.Adj (e y) (q b) →
      Graph.WindowExchange.rungCount p q ≤ if x.1 = 4 ∨ y.1 = 4 then 6 else 8

end Hypostructure.Graph.Strategy.Spine
