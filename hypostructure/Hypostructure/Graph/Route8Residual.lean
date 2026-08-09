import Hypostructure.Graph.CanonicalSupportSelection
import Hypostructure.Graph.Route8Closure
import Hypostructure.Graph.TraceCoordinateSystem

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

/-! ## Trace basins and graph-owned route-8 entries -/

namespace TraceBasin

open TraceCoordinateSystem

attribute [local instance] vertexDecEq

/-- The canonical trace seed of `def:typeA-trace-basin`: the vertex support of
the selected trace `T_u`, when the route from `load` to `receiver` exists. -/
noncomputable def traceSeed? (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (receiver load : object.Vertex) : Option (Finset object.Vertex) :=
  match object.tracePath? support threshold load receiver with
  | none => none
  | some trace => some trace.1.support.toFinset

/-- A candidate basin carries the selected trace and is connected inside the
ambient object.  The finite declared `u`-supported coordinate family is derived
from `TraceCoordinateSystem.Base`; no coordinate family is supplied by a caller.

The restriction/equality part of `def:typeA-trace-basin` is recorded by asking
that every graph-derived `u`-supported coordinate is either carried by the basin
or is one of the boundary-profile determined coordinates exposed by the
selected basin boundary.  This is the graph-local predicate consumed by the
route-8 ledger facts. -/
def TraceComplete (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (receiver load : object.Vertex) (basin : Finset object.Vertex) : Prop :=
  basin ⊆ support ∧
    (∃ trace : object.graph.Path load receiver,
      object.tracePath? support threshold load receiver = some trace ∧
        trace.1.support.toFinset ⊆ basin) ∧
    SupportComponents.Connected.ConnectedOn object basin ∧
    ∀ coordinate :
        TraceCoordinateSystem.Base.Coordinate object support,
      coordinate ∈ (TraceCoordinateSystem.Base.schedule object support).values →
        TraceCoordinateSystem.Base.USupported object support threshold receiver
          load coordinate →
          TraceCoordinateSystem.Base.declaredSupport object support coordinate ⊆ basin ∨
            ∃ boundaryVertex ∈
                Strategy.InterfaceReplacement.SupportAtom.cutBoundary object basin,
              boundaryVertex ∈
                TraceCoordinateSystem.Base.declaredSupport object support coordinate

/-- The finite family of trace-complete connected candidate basins. -/
noncomputable def candidates (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (receiver load : object.Vertex) : Finset (Finset object.Vertex) := by
  classical
  exact support.powerset.filter
    (TraceComplete object support threshold receiver load)

theorem mem_candidates_iff {object : FiniteObject.{u}}
    {support basin : Finset object.Vertex} {threshold : Nat}
    {receiver load : object.Vertex} :
    basin ∈ candidates object support threshold receiver load ↔
      TraceComplete object support threshold receiver load basin := by
  classical
  simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · exact fun member => member.2
  · intro complete
    exact ⟨complete.1, complete⟩

/-- The minimum-cardinality trace-complete basins. -/
noncomputable def minimalCandidates (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (receiver load : object.Vertex) : Finset (Finset object.Vertex) := by
  classical
  exact (candidates object support threshold receiver load).filter fun basin =>
    ∀ other ∈ candidates object support threshold receiver load,
      basin.card ≤ other.card

/-- The trace basin `B_u`: the first minimum trace-complete connected basin in
the object's finite support order. -/
noncomputable def select? (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (receiver load : object.Vertex) : Option (Finset object.Vertex) :=
  (minimalCandidates object support threshold receiver load).toList.head?

theorem select?_mem_candidates {object : FiniteObject.{u}}
    {support basin : Finset object.Vertex} {threshold : Nat}
    {receiver load : object.Vertex}
    (selected :
      select? object support threshold receiver load = some basin) :
    basin ∈ candidates object support threshold receiver load := by
  classical
  have member : basin ∈
      (minimalCandidates object support threshold receiver load).toList :=
    List.mem_of_mem_head? selected
  have inMinimal :
      basin ∈ minimalCandidates object support threshold receiver load := by
    simpa using member
  exact (Finset.mem_filter.1 inMinimal).1

theorem select?_traceComplete {object : FiniteObject.{u}}
    {support basin : Finset object.Vertex} {threshold : Nat}
    {receiver load : object.Vertex}
    (selected :
      select? object support threshold receiver load = some basin) :
    TraceComplete object support threshold receiver load basin :=
  mem_candidates_iff.mp (select?_mem_candidates selected)

theorem select?_card_le {object : FiniteObject.{u}}
    {support basin other : Finset object.Vertex} {threshold : Nat}
    {receiver load : object.Vertex}
    (selected :
      select? object support threshold receiver load = some basin)
    (candidate :
      other ∈ candidates object support threshold receiver load) :
    basin.card ≤ other.card := by
  classical
  have member : basin ∈
      (minimalCandidates object support threshold receiver load).toList :=
    List.mem_of_mem_head? selected
  have inMinimal :
      basin ∈ minimalCandidates object support threshold receiver load := by
    simpa using member
  exact (Finset.mem_filter.1 inMinimal).2 other candidate

/-- Selection succeeds as soon as a trace-complete candidate exists. -/
theorem select?_isSome {object : FiniteObject.{u}}
    {support : Finset object.Vertex} {threshold : Nat}
    {receiver load : object.Vertex}
    (witness :
      (candidates object support threshold receiver load).Nonempty) :
    (select? object support threshold receiver load).isSome := by
  classical
  obtain ⟨least, member, minimal⟩ :=
    Finset.exists_min_image
      (candidates object support threshold receiver load) Finset.card witness
  have inMinimal :
      least ∈ minimalCandidates object support threshold receiver load :=
    Finset.mem_filter.2 ⟨member, minimal⟩
  have nonempty :
      (minimalCandidates object support threshold receiver load).toList ≠ [] := by
    intro empty
    have : least ∈
        (minimalCandidates object support threshold receiver load).toList := by
      simpa using inMinimal
    rw [empty] at this
    exact absurd this (List.not_mem_nil)
  cases list :
      (minimalCandidates object support threshold receiver load).toList with
  | nil => exact absurd list nonempty
  | cons head tail => simp [select?, list]

/-- Alternative (a): a trace-local non-carrier quotient is target-defective. -/
def TraceLocalTargetDefect (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (LengthOK : Nat → Prop) (receiver load : object.Vertex)
    (basin : Finset object.Vertex) : Prop :=
  ∃ replacement : BoundaryPiece
      (Strategy.InterfaceReplacement.SupportAtom.boundary object basin),
    replacement.boundaryDegreeProfile =
        (Strategy.InterfaceReplacement.SupportAtom.piece object basin).boundaryDegreeProfile ∧
      Response.TargetDefect (HasCycleWithLength LengthOK) replacement
        (Strategy.InterfaceReplacement.SupportAtom.piece object basin)

/-- Alternative (b): a nontrivial target-complete trace-local compression. -/
def TraceTargetCompleteCompression (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (LengthOK : Nat → Prop) (receiver load : object.Vertex)
    (basin : Finset object.Vertex) : Prop :=
  ∃ replacement : BoundaryPiece
      (Strategy.InterfaceReplacement.SupportAtom.boundary object basin),
    replacement.boundaryDegreeProfile =
        (Strategy.InterfaceReplacement.SupportAtom.piece object basin).boundaryDegreeProfile ∧
      Response.ContextEquivalent (HasCycleWithLength LengthOK) replacement
        (Strategy.InterfaceReplacement.SupportAtom.piece object basin)

/-- Alternative (c): a trace equality delocalizes to a larger support. -/
def TraceDelocalization (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (LengthOK : Nat → Prop) (receiver load : object.Vertex)
    (basin : Finset object.Vertex) : Prop :=
  ∃ larger : Finset object.Vertex,
    basin ⊂ larger ∧
      larger ⊆ object.vertexFinset ∧
      SupportComponents.Connected.ConnectedOn object larger

/-- Alternative (d): two outside connector germs have a surviving first
separator.  The concrete germ schedule is the graph-owned exit-seven schedule;
the proposition records only the existence of such a survivor for this basin. -/
def TraceSurvivingSeparator (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (LengthOK : Nat → Prop) (receiver load : object.Vertex)
    (basin : Finset object.Vertex) : Prop :=
  ∃ separator : object.Vertex,
    separator ∉ support ∧ threshold < object.degree separator

/-- The selected basin is target-complete-minimal precisely when none of the
four trace-local failure alternatives of `def:typeA-trace-basin` occurs. -/
def TargetCompleteMinimal (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (LengthOK : Nat → Prop) (receiver load : object.Vertex)
    (basin : Finset object.Vertex) : Prop :=
  TraceComplete object support threshold receiver load basin ∧
    ¬ TraceLocalTargetDefect object support threshold LengthOK receiver load basin ∧
    ¬ TraceTargetCompleteCompression object support threshold LengthOK receiver load basin ∧
    ¬ TraceDelocalization object support threshold LengthOK receiver load basin ∧
    ¬ TraceSurvivingSeparator object support threshold LengthOK receiver load basin

end TraceBasin

namespace PresentedEntry

open TraceCoordinateSystem

/-- Convert a graph-derived D4 target event into the route-8 event shape. -/
noncomputable def eventOfBase (object : FiniteObject.{u})
    (support : Finset object.Vertex) (LengthOK : Nat → Prop) :
    (coordinate : Base.Coordinate object support) →
      Option (CoordinateEvent object)
  | .d1 _ => none
  | .d2ReturnLength _ => none
  | .d3WindowLabel _ => none
  | .d4RawCurvature coordinate =>
      match TraceCoordinateSystem.D4.event? object support LengthOK coordinate with
      | none => none
      | some event =>
          some
            { base := event.certificate.vertex
              walk := event.certificate.walk
              isCycle := event.certificate.isCycle }

/-- The graph-owned presented entry assigned to a selected trace basin.  The
coordinate family, values, supports and target events are all read from the
declared trace-coordinate system of the selected support. -/
noncomputable def ofTraceBasin (object : FiniteObject.{u})
    (support basin : Finset object.Vertex) (threshold : Nat)
    (LengthOK : Nat → Prop) : PresentedEntry object where
  support := support
  interface := Strategy.InterfaceReplacement.SupportAtom.boundary object basin
  Coordinate := TraceCoordinateSystem.Base.Coordinate object support
  coordinateDecEq := TraceCoordinateSystem.Base.coordinateDecEq object support
  coordinates := (TraceCoordinateSystem.Base.schedule object support).toFinset
  Value := fun _ => PUnit.{u + 1}
  value := fun _ => PUnit.unit
  declaredSupport := TraceCoordinateSystem.Base.declaredSupport object support
  event? := eventOfBase object support LengthOK
  state := fun _ =>
    Strategy.InterfaceReplacement.SupportAtom.piece object basin

end PresentedEntry

namespace TraceBasin

/-- The concrete route-8 entry of `def:typeA-route8-carriers` for the selected
load/basin. -/
def Route8Entry (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (LengthOK : Nat → Prop) (receiver load : object.Vertex) : Prop :=
  ∃ basin : Finset object.Vertex,
    select? object support threshold receiver load = some basin ∧
      TargetCompleteMinimal object support threshold LengthOK receiver load basin

end TraceBasin

end Hypostructure.Graph.Route8
