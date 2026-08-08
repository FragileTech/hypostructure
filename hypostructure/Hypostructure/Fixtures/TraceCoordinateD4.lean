import Hypostructure.Graph.TraceCoordinateSystem

/-!
# D4 raw-curvature coordinate fixtures
-/

namespace Hypostructure.Fixtures.TraceCoordinateD4

open Hypostructure

universe u

example (object : Graph.FiniteObject.{u}) (support : Finset object.Vertex)
    (coordinate : Graph.TraceCoordinateSystem.D4.Coordinate object support) :
    coordinate ∈
      (Graph.TraceCoordinateSystem.D4.schedule object support).values :=
  Graph.TraceCoordinateSystem.D4.mem_schedule object support coordinate

example (object : Graph.FiniteObject.{u}) (support : Finset object.Vertex) :
    (Graph.TraceCoordinateSystem.D4.schedule object support).card =
      object.internalWedgeCount support :=
  Graph.TraceCoordinateSystem.D4.schedule_card object support

example (object : Graph.FiniteObject.{u}) (support : Finset object.Vertex)
    (coordinate : Graph.TraceCoordinateSystem.D4.Coordinate object support) :
    Graph.TraceCoordinateSystem.D4.declaredSupport object support coordinate =
      Graph.FiniteObject.internalWedgeSupport coordinate.1 := rfl

example (object : Graph.FiniteObject.{u}) (support : Finset object.Vertex)
    (LengthOK : Nat → Prop)
    (coordinate : Graph.TraceCoordinateSystem.D4.Coordinate object support) :
    (Graph.TraceCoordinateSystem.D4.event? object support LengthOK coordinate).isSome =
        true ↔
      ∃ return' : Graph.EdgeRootedReturn.Unrestricted object,
        Graph.TraceCoordinateSystem.D4.ClosingReturn object support LengthOK
          coordinate return' :=
  Graph.TraceCoordinateSystem.D4.event?_isSome_iff object support LengthOK coordinate

example (object : Graph.FiniteObject.{u}) (support : Finset object.Vertex)
    (coordinate : Graph.TraceCoordinateSystem.D4.Coordinate object support) :
    Graph.TraceCoordinateSystem.Base.Coordinate.d4RawCurvature coordinate ∈
      (Graph.TraceCoordinateSystem.Base.schedule object support).values :=
  Graph.TraceCoordinateSystem.Base.mem_schedule object support _

example (object : Graph.FiniteObject.{u}) (support : Finset object.Vertex)
    (threshold : Nat) (receiver load : object.Vertex)
    (coordinate : Graph.TraceCoordinateSystem.D4.Coordinate object support) :
    Graph.TraceCoordinateSystem.D4.uSupported object support threshold receiver load
        coordinate = true ↔
      Graph.TraceCoordinateSystem.D4.USupported object support threshold receiver load
        coordinate :=
  Graph.TraceCoordinateSystem.D4.uSupported_eq_true_iff object support threshold
    receiver load coordinate

end Hypostructure.Fixtures.TraceCoordinateD4
