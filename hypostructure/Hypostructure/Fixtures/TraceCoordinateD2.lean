import Hypostructure.Graph.TraceCoordinateSystem

/-!
# D2 rooted-return coordinate fixtures
-/

namespace Hypostructure.Fixtures.TraceCoordinateD2

open Hypostructure

universe u

example (object : Graph.FiniteObject.{u})
    (return' : Graph.EdgeRootedReturn.Unrestricted object) :
    return' ∈ (Graph.EdgeRootedReturn.schedule object).values :=
  Graph.EdgeRootedReturn.mem_schedule return'

example (object : Graph.FiniteObject.{u}) (dart : object.graph.Dart)
    (length : Nat) :
    length ∈ Graph.EdgeRootedReturn.returnLengthFinset object dart ↔
      length ∈ Graph.returnLengthSet object dart :=
  Graph.EdgeRootedReturn.mem_returnLengthFinset_iff dart length

example (object : Graph.FiniteObject.{u}) (support : Finset object.Vertex)
    (coordinate : Graph.TraceCoordinateSystem.D2.Coordinate object) :
    Graph.TraceCoordinateSystem.Base.Coordinate.d2ReturnLength coordinate ∈
      (Graph.TraceCoordinateSystem.Base.schedule object support).values :=
  Graph.TraceCoordinateSystem.Base.mem_schedule object support _

example (object : Graph.FiniteObject.{u}) (support : Finset object.Vertex)
    (threshold : Nat) (receiver load : object.Vertex)
    (coordinate : Graph.TraceCoordinateSystem.D2.Coordinate object) :
    Graph.TraceCoordinateSystem.D2.uSupported object support threshold receiver load
        coordinate = true ↔
      Graph.TraceCoordinateSystem.D2.USupported object support threshold receiver load
        coordinate :=
  Graph.TraceCoordinateSystem.D2.uSupported_eq_true_iff object support threshold
    receiver load coordinate

end Hypostructure.Fixtures.TraceCoordinateD2
