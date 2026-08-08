import Hypostructure.Graph.ResponseDelocalization
import Hypostructure.Graph.VisibleReceiverEntry

/-!
# Receiver-entry-return and optional-event fixtures

These checks keep the D1 schedule and the route-8 presentation on their generic
Graph APIs.  They introduce no strategy state or proof-specific carrier.
-/

namespace Hypostructure.Fixtures.ReceiverEntryReturnSchedule

open Hypostructure

universe u

example (object : Graph.FiniteObject.{u}) (support : Finset object.Vertex)
    (receiver outside : object.Vertex)
    (return' : Graph.VisibleEntry.ReceiverEntryReturn object support receiver outside) :
    return' ∈
      (Graph.VisibleEntry.ReceiverEntryReturn.schedule object support receiver outside).values :=
  return'.mem_schedule

example (object : Graph.FiniteObject.{u}) (support : Finset object.Vertex)
    (receiver outside : object.Vertex)
    (return' : Graph.VisibleEntry.ReceiverEntryReturn object support receiver outside)
    (member : return' ∈
      (Graph.VisibleEntry.ReceiverEntryReturn.schedule object support receiver outside).values) :
    Graph.VisibleEntry.firstEntry? support return'.toAnchoredReturn =
      some return'.entry :=
  return'.firstEntry?_of_mem_schedule member

example (object : Graph.FiniteObject.{u}) (support : Finset object.Vertex)
    (threshold : Nat) (receiver outside load : object.Vertex)
    (boundary : object.Vertex)
    (port : outside ∈ Graph.VisibleEntry.completionPorts object support receiver)
    (return' : Graph.VisibleEntry.ReceiverEntryReturn object support receiver outside)
    (owns : return'.OwnsBoundaryEntry (threshold := threshold) boundary load) :
    Graph.VisibleEntry.ownsBoundaryEntry object support threshold receiver load boundary :=
  Graph.VisibleEntry.ownsBoundaryEntry_of_return boundary port return' owns

example (object : Graph.FiniteObject.{u})
    (presented : Graph.Route8.PresentedEntry object)
    (coordinate : presented.Coordinate)
    (noEvent : presented.event? coordinate = none) :
    presented.car coordinate = ∅ := by
  simp [Graph.Route8.PresentedEntry.car, noEvent]

end Hypostructure.Fixtures.ReceiverEntryReturnSchedule
