import Hypostructure.Graph.TraceCoordinateSystem

/-!
# D1 trace-coordinate fixtures

The fixture checks that the finite boundary schedule, values, singleton
supports and `u`-support decision are all projections of graph-derived data.
-/

namespace Hypostructure.Fixtures.TraceCoordinateD1

open Hypostructure

universe u

example (object : Graph.FiniteObject.{u}) (support : Finset object.Vertex)
    (coordinate : Graph.TraceCoordinateSystem.D1.Coordinate object support) :
    coordinate ∈
      (Graph.TraceCoordinateSystem.D1.schedule object support).values :=
  Graph.TraceCoordinateSystem.D1.mem_schedule object support coordinate

example (object : Graph.FiniteObject.{u}) (support : Finset object.Vertex)
    (coordinate : Graph.TraceCoordinateSystem.D1.Coordinate object support) :
    Graph.TraceCoordinateSystem.D1.declaredSupport object support coordinate =
      {coordinate.1} := rfl

example (object : Graph.FiniteObject.{u}) (support : Finset object.Vertex)
    (coordinate : Graph.TraceCoordinateSystem.D1.Coordinate object support) :
    Graph.TraceCoordinateSystem.D1.value object support coordinate =
      (Graph.Strategy.InterfaceReplacement.SupportAtom.piece object support).boundaryDegreeProfile
        coordinate := rfl

example (object : Graph.FiniteObject.{u}) (support : Finset object.Vertex)
    (threshold : Nat) (receiver load : object.Vertex)
    (coordinate : Graph.TraceCoordinateSystem.D1.Coordinate object support) :
    Graph.TraceCoordinateSystem.D1.uSupported object support threshold receiver load
        coordinate = true ↔
      Graph.TraceCoordinateSystem.D1.USupported object support threshold receiver load
        coordinate :=
  Graph.TraceCoordinateSystem.D1.uSupported_eq_true_iff object support threshold
    receiver load coordinate

example (object : Graph.FiniteObject.{u}) (support : Finset object.Vertex)
    (coordinate : Graph.TraceCoordinateSystem.Base.Coordinate object support) :
    coordinate ∈
      (Graph.TraceCoordinateSystem.Base.schedule object support).values :=
  Graph.TraceCoordinateSystem.Base.mem_schedule object support coordinate

end Hypostructure.Fixtures.TraceCoordinateD1
