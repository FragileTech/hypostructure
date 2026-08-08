import Hypostructure.Graph.TraceCoordinateSystem

/-!
# D3 packed-window attachment coordinate fixtures
-/

namespace Hypostructure.Fixtures.TraceCoordinateD3

open Hypostructure

universe u

example (object : Graph.FiniteObject.{u})
    (window : Graph.InducedPathMaximalPacking.Window object 13) :
    Graph.InducedPathMaximalPacking.P13.canonicalPlacement
        (Graph.InducedPathMaximalPacking.P13.reverseWindow window) =
      Graph.InducedPathMaximalPacking.P13.canonicalPlacement window :=
  Graph.InducedPathMaximalPacking.P13.canonicalPlacement_reverse window

example (object : Graph.FiniteObject.{u}) (support : Finset object.Vertex)
    (coordinate : Graph.TraceCoordinateSystem.D3.Coordinate object support) :
    coordinate ∈ (Graph.TraceCoordinateSystem.D3.schedule object support).values :=
  Graph.TraceCoordinateSystem.D3.mem_schedule object support coordinate

example (object : Graph.FiniteObject.{u}) (support : Finset object.Vertex)
    (coordinate : Graph.TraceCoordinateSystem.D3.Coordinate object support)
    (index : Fin 13) :
    index ∈ Graph.TraceCoordinateSystem.D3.value object support coordinate ↔
      object.graph.Adj coordinate.1.2
        (Graph.TraceCoordinateSystem.D3.placement object support coordinate.1.1 index) :=
  Graph.TraceCoordinateSystem.D3.mem_attachmentLabel_iff
    object support coordinate.1.1 coordinate.1.2 index

example (object : Graph.FiniteObject.{u}) (support : Finset object.Vertex)
    (coordinate : Graph.TraceCoordinateSystem.D3.Coordinate object support) :
    Graph.TraceCoordinateSystem.Base.Coordinate.d3WindowLabel coordinate ∈
      (Graph.TraceCoordinateSystem.Base.schedule object support).values :=
  Graph.TraceCoordinateSystem.Base.mem_schedule object support _

example (object : Graph.FiniteObject.{u}) (support : Finset object.Vertex)
    (threshold : Nat) (receiver load : object.Vertex)
    (coordinate : Graph.TraceCoordinateSystem.D3.Coordinate object support) :
    Graph.TraceCoordinateSystem.D3.uSupported object support threshold receiver load
        coordinate = true ↔
      Graph.TraceCoordinateSystem.D3.USupported object support threshold receiver load
        coordinate :=
  Graph.TraceCoordinateSystem.D3.uSupported_eq_true_iff object support threshold
    receiver load coordinate

end Hypostructure.Fixtures.TraceCoordinateD3
