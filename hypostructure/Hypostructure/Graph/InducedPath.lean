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

/-- A shortest path in an induced-`P_order`-free graph has at most
`order - 2` edges.  Every subpath of a shortest path is shortest; hence a
chord between nonconsecutive vertices is impossible, and the first `order`
vertices of a longer path would induce `P_order`. -/
theorem shortestPath_length_le_order_sub_two
    (object : FiniteObject.{uVertex}) (order : Nat) (orderAtLeast : 3 ≤ order)
    {left right : object.Vertex}
    (shortest : object.graph.Walk left right)
    (shortestPath : shortest.IsPath)
    (shortestLength : shortest.length = object.graph.dist left right)
    (free : InducedPathFree object order) :
    shortest.length ≤ order - 2 := by
  classical
  by_contra tooLong
  have initialSegmentLe : order - 1 ≤ shortest.length := by omega
  let initialSegment := shortest.take (order - 1)
  have initialSegmentPath : initialSegment.IsPath := shortestPath.take _
  have initialSegmentLength : initialSegment.length = order - 1 := by
    simp only [initialSegment, SimpleGraph.Walk.take_length]
    rw [Nat.min_eq_left initialSegmentLe]
  have initialSegmentShortest :=
    SimpleGraph.length_eq_dist_of_subwalk shortestLength
      (SimpleGraph.Walk.isSubwalk_take shortest (order - 1))
  have forbiddenPath :
      SimpleGraph.IsIndContained
        (SimpleGraph.pathGraph (initialSegment.length + 1)) object.graph := by
    have inducedSubgraph : initialSegment.toSubgraph.IsInduced := by
      intro x xMem y yMem adjacent
      have xSupport : x ∈ initialSegment.support :=
        initialSegment.mem_verts_toSubgraph.mp xMem
      have ySupport : y ∈ initialSegment.support :=
        initialSegment.mem_verts_toSubgraph.mp yMem
      obtain ⟨i, xEq, iLe⟩ :=
        SimpleGraph.Walk.mem_support_iff_exists_getVert.mp xSupport
      obtain ⟨j, yEq, jLe⟩ :=
        SimpleGraph.Walk.mem_support_iff_exists_getVert.mp ySupport
      have ijNe : i ≠ j := by
        intro equal
        exact adjacent.ne (calc
          x = initialSegment.getVert i := xEq.symm
          _ = initialSegment.getVert j :=
            congrArg initialSegment.getVert equal
          _ = y := yEq)
      rcases lt_or_gt_of_ne ijNe with iLt | jLt
      · let segment := (initialSegment.drop i).take (j - i)
        have segmentSub : segment.IsSubwalk initialSegment :=
          (SimpleGraph.Walk.isSubwalk_take
            (initialSegment.drop i) (j - i)).trans
            (SimpleGraph.Walk.isSubwalk_drop initialSegment i)
        have segmentShortest :=
          SimpleGraph.length_eq_dist_of_subwalk initialSegmentShortest segmentSub
        have segmentLength : segment.length = j - i := by
          simp only [segment, SimpleGraph.Walk.take_length,
            SimpleGraph.Walk.drop_length]
          rw [Nat.min_eq_left (by omega : j - i ≤ initialSegment.length - i)]
        have segmentTarget :
            (initialSegment.drop i).getVert (j - i) =
              initialSegment.getVert j := by
          rw [SimpleGraph.Walk.drop_getVert]
          congr 1
          omega
        have distanceTarget :
            object.graph.dist (initialSegment.getVert i)
                ((initialSegment.drop i).getVert (j - i)) =
              object.graph.dist (initialSegment.getVert i)
                (initialSegment.getVert j) :=
          congrArg (fun target => object.graph.dist
            (initialSegment.getVert i) target) segmentTarget
        have distanceOne : object.graph.dist
            (initialSegment.getVert i) (initialSegment.getVert j) = 1 := by
          have distanceXY := SimpleGraph.dist_eq_one_iff_adj.mpr adjacent
          simpa only [xEq, yEq] using distanceXY
        have consecutive : j = i + 1 := by omega
        subst j
        simpa [xEq, yEq] using
          initialSegment.toSubgraph_adj_getVert
            (by omega : i < initialSegment.length)
      · have adjacent' := adjacent.symm
        let segment := (initialSegment.drop j).take (i - j)
        have segmentSub : segment.IsSubwalk initialSegment :=
          (SimpleGraph.Walk.isSubwalk_take
            (initialSegment.drop j) (i - j)).trans
            (SimpleGraph.Walk.isSubwalk_drop initialSegment j)
        have segmentShortest :=
          SimpleGraph.length_eq_dist_of_subwalk initialSegmentShortest segmentSub
        have segmentLength : segment.length = i - j := by
          simp only [segment, SimpleGraph.Walk.take_length,
            SimpleGraph.Walk.drop_length]
          rw [Nat.min_eq_left (by omega : i - j ≤ initialSegment.length - j)]
        have segmentTarget :
            (initialSegment.drop j).getVert (i - j) =
              initialSegment.getVert i := by
          rw [SimpleGraph.Walk.drop_getVert]
          congr 1
          omega
        have distanceTarget :
            object.graph.dist (initialSegment.getVert j)
                ((initialSegment.drop j).getVert (i - j)) =
              object.graph.dist (initialSegment.getVert j)
                (initialSegment.getVert i) :=
          congrArg (fun target => object.graph.dist
            (initialSegment.getVert j) target) segmentTarget
        have distanceOne : object.graph.dist
            (initialSegment.getVert j) (initialSegment.getVert i) = 1 := by
          have distanceYX := SimpleGraph.dist_eq_one_iff_adj.mpr adjacent'
          simpa only [xEq, yEq] using distanceYX
        have consecutive : i = j + 1 := by omega
        subst i
        simpa [xEq, yEq] using
          (initialSegment.toSubgraph_adj_getVert
            (by omega : j < initialSegment.length)).symm
    exact initialSegmentPath.pathGraphIsoToSubgraph.isIndContained.trans
      inducedSubgraph.isIndContained
  apply free
  have orderEq : initialSegment.length + 1 = order := by omega
  rw [orderEq] at forbiddenPath
  exact forbiddenPath

end Hypostructure.Graph
