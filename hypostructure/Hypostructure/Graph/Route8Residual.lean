import Hypostructure.Graph.Route8Closure

/-!
# Route-8 presented entries at one object

`def:typeA-route8-carriers` presents an indexed entry by the support it lives
on, the declared coordinates and values of its reading, and the optional target
events carried by event coordinates.  A `Presentation` is exactly that data,
at one ambient object, and the
carrier vocabulary of `Route8.Entry` is *derived* from it: the entry's carrier
supply is the support's own cut, and a coordinate's carrier support is the set
of cut edges its event uses.

With the presentation in that shape, `lem:typeA-carrier-cut-parity` is a
theorem about the object rather than a clause: `Route8.two_le_card_crossingCarriers`
applies to every coordinate whose event both meets the support and leaves it,
so the small-core collapse of `Route8.Entry.collapse_of_alpha_le_one` has its
hypothesis discharged by the ambient graph.

This module intentionally does not define a route-8 residual carrier.  The
Strategy branch records the selected residual only through `ExactLedger` facts;
later route-8 accounting must read those facts directly instead of transporting
a secondary object.
-/

namespace Hypostructure.Graph.Route8

open Hypostructure
open Hypostructure.Core.Finite

universe u

/-! ## Cut edges of a support -/

variable {object : FiniteObject.{u}}

attribute [local instance] vertexDecEq

/-- The object's vertex schedule is a finite type. -/
def vertexFintype (object : FiniteObject.{u}) : Fintype object.Vertex :=
  @FinEnum.instFintype _ object.vertices

attribute [local instance] vertexFintype

/-- The object's edge set is finite: its vertices are, and its adjacency is
decidable. -/
noncomputable def edgeFintype (object : FiniteObject.{u}) :
    Fintype object.graph.edgeSet := by
  letI := vertexFintype object
  letI := vertexDecEq object
  classical
  exact SimpleGraph.fintypeEdgeSet (G := object.graph)

attribute [local instance] edgeFintype

/-- The support's own cut: the edges of the object with exactly one endpoint
inside it.  This is `∂_E X` read as an unoriented incidence set; its cardinality
is the support's positive deficiency when every support vertex sits at the
baseline. -/
noncomputable def cutEdges (object : FiniteObject.{u})
    (support : Finset object.Vertex) : Finset (Sym2 object.Vertex) :=
  letI : DecidablePred fun edge : Sym2 object.Vertex =>
      ∃ inside ∈ edge, ∃ outside ∈ edge, inside ∈ support ∧ outside ∉ support :=
    fun _ => Classical.propDecidable _
  object.graph.edgeFinset.filter fun edge =>
    ∃ inside ∈ edge, ∃ outside ∈ edge, inside ∈ support ∧ outside ∉ support

theorem mem_cutEdges {support : Finset object.Vertex}
    {edge : Sym2 object.Vertex} :
    edge ∈ cutEdges object support ↔
      edge ∈ object.graph.edgeFinset ∧
        ∃ inside ∈ edge, ∃ outside ∈ edge,
          inside ∈ support ∧ outside ∉ support := by
  rw [cutEdges]
  simp only [Finset.mem_filter]

/-- A closed walk's crossings are cut edges of the support. -/
theorem crossingCarriers_subset_cutEdges {support : Finset object.Vertex}
    {base : object.Vertex} (walk : object.graph.Walk base base) :
    crossingCarriers support walk ⊆ cutEdges object support := by
  intro edge member
  rw [crossingCarriers, List.mem_toFinset, CutParity.crossingEdges,
    List.mem_map] at member
  obtain ⟨dart, filtered, shape⟩ := member
  rw [List.mem_filter] at filtered
  have crossing : CutParity.crosses (G := object.graph)
      (S := (support : Set object.Vertex)) dart = true := by
    simpa using filtered.2
  have adjacency : object.graph.Adj dart.fst dart.snd := dart.adj
  refine mem_cutEdges.mpr ⟨?_, ?_⟩
  · rw [← shape]
    exact SimpleGraph.mem_edgeFinset.mpr dart.edge_mem
  · -- exactly one endpoint of the dart lies in the support
    rw [CutParity.crosses, CutParity.side, CutParity.side, bne_iff_ne, ne_eq,
      decide_eq_decide] at crossing
    rw [← shape]
    by_cases first : dart.fst ∈ support
    · refine ⟨dart.fst, ?_, dart.snd, ?_, first, ?_⟩
      · simp [SimpleGraph.Dart.edge]
      · simp [SimpleGraph.Dart.edge]
      · intro second
        exact crossing (by simp [first, second] : dart.fst ∈ (support : Set object.Vertex) ↔
          dart.snd ∈ (support : Set object.Vertex))
    · have second : dart.snd ∈ support := by
        by_contra missing
        exact crossing (by
          constructor
          · intro inside; exact absurd inside first
          · intro inside; exact absurd inside missing)
      refine ⟨dart.snd, ?_, dart.fst, ?_, second, first⟩
      · simp [SimpleGraph.Dart.edge]
      · simp [SimpleGraph.Dart.edge]

/-- The cut as an exact finite schedule, which is the shape a carrier core is
selected against. -/
noncomputable def cutSchedule (object : FiniteObject.{u})
    (support : Finset object.Vertex) : Enumeration (Sym2 object.Vertex) :=
  Enumeration.ofNodupList (cutEdges object support).toList
    (Finset.nodup_toList _)

@[simp] theorem cutSchedule_toFinset (support : Finset object.Vertex) :
    (cutSchedule object support).toFinset = cutEdges object support := by
  ext edge
  simp [cutSchedule, Enumeration.toFinset, Enumeration.ofNodupList]

/-! ## Presented entries -/

/-- A simple closed target event attached to one declared coordinate.  This is
separate from the coordinate's value and declared support: D1 boundary-degree
coordinates, for example, have both of those but do not themselves assert a
cycle event. -/
structure CoordinateEvent (object : FiniteObject.{u}) where
  base : object.Vertex
  walk : object.graph.Walk base base
  isCycle : walk.IsCycle

/-- **`def:typeA-route8-carriers`, presented at one object.**

One indexed entry: the support it lives on, its declared coordinate family,
each coordinate's value and finite declared support, the optional target event
of event coordinates, and the boundaried reading that retains a given set of
coordinates.  Carrier data is not stored -- it is read off the optional events
below. -/
structure PresentedEntry (object : FiniteObject.{u}) where
  /-- `V(X)`: the support the entry's boundary incidences leave. -/
  support : Finset object.Vertex
  /-- The labelled interface the entry's readings are presented on. -/
  interface : Boundary.{u}
  /-- The declared coordinate index of the reading `ρ_u(B_u)`. -/
  Coordinate : Type u
  /-- Decidable equality on the declared coordinates. -/
  coordinateDecEq : DecidableEq Coordinate
  /-- The declared coordinate family. -/
  coordinates : Finset Coordinate
  /-- The value type of each declared coordinate.  It is dependent because the
  D1--D8 families do not share an artificial common codomain. -/
  Value : Coordinate → Type u
  /-- The actual value of every declared coordinate. -/
  value : (r : Coordinate) → Value r
  /-- The finite support declared by every coordinate, independently of
  whether that coordinate carries a target event. -/
  declaredSupport : Coordinate → Finset object.Vertex
  /-- The target event, only when the coordinate is an event coordinate. -/
  event? : Coordinate → Option (CoordinateEvent object)
  /-- The reading retaining exactly a set of declared coordinates. -/
  state : Finset Coordinate → BoundaryPiece interface

namespace PresentedEntry

variable (presented : PresentedEntry object)

attribute [instance] PresentedEntry.coordinateDecEq

/-- The carrier support a declared coordinate records: the cut edges of the
entry's support that its event uses. -/
noncomputable def car (r : presented.Coordinate) : Finset (Sym2 object.Vertex) :=
  match presented.event? r with
  | none => ∅
  | some event => crossingCarriers presented.support event.walk

/-- A declared coordinate is *crossing* when its event both meets the entry's
support and leaves it.  This is the manuscript's *mixed internal* event: it uses
an edge inside the basin and an edge outside the support. -/
def Crossing (r : presented.Coordinate) : Prop :=
  exists event : CoordinateEvent object,
    presented.event? r = some event /\
      (exists inside, inside ∈ event.walk.support /\ inside ∈ presented.support) /\
        exists outside, outside ∈ event.walk.support /\ outside ∉ presented.support

/-- The declared coordinates whose events cross the entry's own cut. -/
noncomputable def crossingCoordinates : Finset presented.Coordinate :=
  letI : DecidablePred presented.Crossing := fun _ => Classical.propDecidable _
  presented.coordinates.filter presented.Crossing

theorem mem_crossingCoordinates {r : presented.Coordinate} :
    r ∈ presented.crossingCoordinates ↔
      r ∈ presented.coordinates ∧ presented.Crossing r := by
  rw [crossingCoordinates]
  simp only [Finset.mem_filter]

/-- **`lem:typeA-carrier-cut-parity` at a presented entry.**  A crossing
coordinate records at least two distinct carriers. -/
theorem two_le_card_car {r : presented.Coordinate}
    (crossing : presented.Crossing r) :
    2 ≤ (presented.car r).card := by
  obtain ⟨event, eventEq, ⟨inside, insideMember, insideSupport⟩,
    outside, outsideMember, outsideSupport⟩ := crossing
  rw [car, eventEq]
  exact two_le_card_crossingCarriers presented.support event.isCycle
    insideMember insideSupport outsideMember outsideSupport

/-- Every crossing coordinate records at least two carriers. -/
theorem two_le_card_car_of_mem {r : presented.Coordinate}
    (member : r ∈ presented.crossingCoordinates) :
    2 ≤ (presented.car r).card :=
  presented.two_le_card_car (presented.mem_crossingCoordinates.mp member).2

/-- The carrier vocabulary of the presented entry: `Route8.Entry` at the
support's own cut. -/
noncomputable def toEntry (Target : FiniteObject.{u} → Prop) :
    Entry Target (Sym2 object.Vertex) where
  boundary := presented.interface
  carriers := cutSchedule object presented.support
  Coordinate := presented.Coordinate
  coordinateDecEq := presented.coordinateDecEq
  coordinates := presented.coordinates
  car := presented.car
  car_subset := by
    intro r _member
    rw [cutSchedule_toFinset]
    rw [car]
    split
    · exact Finset.empty_subset _
    · rename_i event _eventEq
      exact crossingCarriers_subset_cutEdges event.walk
  state := presented.state

end PresentedEntry

end Hypostructure.Graph.Route8
