import Hypostructure.Graph.Obstruction

/-!
# Induced-path targets for graph CT1

An induced path is one instance of the graph layer's generic induced
obstruction target.  The path length is application data; CT1 only sees the
generic obstruction interface.
-/

namespace Hypostructure.Graph

universe uPrevious uVertex

/-- A literal induced copy of the path on `order` vertices. -/
def HasInducedPath (object : FiniteObject.{uVertex}) (order : Nat) : Prop :=
  HasInducedObstruction (SimpleGraph.pathGraph order) object

/-- The graph contains no induced path on `order` vertices. -/
def InducedPathFree (object : FiniteObject.{uVertex}) (order : Nat) : Prop :=
  InducedObstructionFree (SimpleGraph.pathGraph order) object

/-- Induced `P_order`-freeness stated directly on a labelled graph, at the level
`def:remainder-entropy`'s class `\mathcal G(R)` needs it.

`HasInducedObstruction` reads nothing off a `FiniteObject` except its `graph`
field, so the finite execution data (`vertices`, `decideAdj`) is inessential to
the predicate.  Spelling that out lets a class of *candidate* graphs on a fixed
vertex set be cut out by this constraint without packing every candidate into a
`FiniteObject` first -- there is no new notion here, only the same one at the
arity its consumer needs. -/
def InducedPathFreeGraph {Vertex : Type uVertex}
    (graph : SimpleGraph Vertex) (order : Nat) : Prop :=
  Not (SimpleGraph.IsIndContained (SimpleGraph.pathGraph order) graph)

/-- The two readings agree definitionally on any packed object, so a consumer
may move between them without transporting a proof. -/
theorem inducedPathFree_iff_graph (object : FiniteObject.{uVertex})
    (order : Nat) :
    InducedPathFree object order ↔ InducedPathFreeGraph object.graph order :=
  Iff.rfl

/-- The path on `order` vertices, viewed as a generic induced obstruction. -/
abbrev inducedPathObstruction (order : Nat) :=
  SimpleGraph.pathGraph order

end Hypostructure.Graph
