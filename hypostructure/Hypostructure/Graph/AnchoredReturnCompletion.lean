import Hypostructure.Graph.VisibleReceiverEntry
import Hypostructure.Graph.RootedReturn

/-!
# Closing an anchored return across its completion port

An anchored return through a completion port `⃗e = (w,h)` is a simple `h ⤳ w`
path that does not use the edge `wh`.  Restoring that edge closes it into a
simple cycle one longer.  That is `lem:return-equivalence` read at the port's
own oriented edge, and it is the only thing needed to turn a return of accepted
length into the target.

The module is the bridge between the two readings of the same object: the
entry-side reading `Graph.VisibleEntry.AnchoredReturn`, which carries the
support-facing decomposition data, and the length-side reading
`Graph.EdgeRootedReturn`, which carries the dart and the deleted-edge path the
target algebra is stated on.  Nothing here knows a support, a baseline, a
receiver's degree, or an accepted set: the length predicate is a parameter and
the port is any adjacent pair.
-/

namespace Hypostructure.Graph.VisibleEntry

open Hypostructure

universe u

variable {object : FiniteObject.{u}}

namespace AnchoredReturn

variable {receiver outside : object.Vertex}

/-- **An anchored return through a completion port is that port's edge-rooted
return.**  The port is the oriented edge `⃗e = (w,h)`, the return runs from `h`
back to `w`, and it avoids `wh` by definition — which is exactly the data
`EdgeRootedReturn` asks for at the dart `(w,h)`. -/
def toEdgeRootedReturn {ReturnLengthOK : Nat → Prop}
    (adjacent : object.graph.Adj receiver outside)
    (return' : AnchoredReturn object receiver outside)
    (length_ok : ReturnLengthOK return'.path.length) :
    EdgeRootedReturn object ReturnLengthOK where
  dart := ⟨(receiver, outside), adjacent⟩
  path := return'.path.toDeleteEdge s(receiver, outside) return'.avoidsPort
  isPath := return'.isPath.toDeleteEdges _ _ _
  length_ok := by
    simpa [SimpleGraph.Walk.toDeleteEdge, SimpleGraph.Walk.length_transfer]
      using length_ok

end AnchoredReturn

/-- **`lem:return-equivalence` at a completion port.**

*"If `2^j − 1 ∈ R_e(G)`, then `e` together with the corresponding simple return
path gives a simple cycle of length `2^j`."*  Here `e` is the port `⃗e = (w,h)`
and the return is the anchored one, so an anchored return whose length plus the
restored port edge is accepted realizes the target. -/
theorem hasCycleWithLength_of_anchoredReturn (CycleLengthOK : Nat → Prop)
    {receiver outside : object.Vertex}
    (adjacent : object.graph.Adj receiver outside)
    (return' : AnchoredReturn object receiver outside)
    (accepted : ShiftedCycleLength CycleLengthOK return'.path.length) :
    HasCycleWithLength CycleLengthOK object :=
  (hasCycleWithLength_iff_hasEdgeRootedReturn CycleLengthOK object).mpr
    ⟨AnchoredReturn.toEdgeRootedReturn adjacent return' accepted⟩

/-- **A target-avoiding object has no accepted anchored return through a
completion port.**

The hypothesis is the exact-avoidance form: every oriented edge's return-length
set misses the shifted accepted set.  It is the standing invariant of the
branch, not an assumption about this port, and the conclusion is the negation
the port-length test needs. -/
theorem not_shiftedCycleLength_of_returnLengthSets_disjoint
    (CycleLengthOK : Nat → Prop)
    (avoids : ∀ dart : object.graph.Dart,
      Disjoint (returnLengthSet object dart)
        (shiftedAcceptedSet CycleLengthOK))
    {receiver outside : object.Vertex}
    (adjacent : object.graph.Adj receiver outside)
    (return' : AnchoredReturn object receiver outside) :
    ¬ ShiftedCycleLength CycleLengthOK return'.path.length := fun accepted =>
  (not_hasCycleWithLength_iff_returnLengthSets_disjoint CycleLengthOK
        object).mpr avoids
    (hasCycleWithLength_of_anchoredReturn CycleLengthOK adjacent return' accepted)

end Hypostructure.Graph.VisibleEntry
