import Hypostructure.Graph.CanonicalSupportSelection
import Hypostructure.Graph.Route8Closure
import Hypostructure.Graph.TraceCoordinateSystem
import Hypostructure.Graph.CanonicalRealization
import Hypostructure.Graph.MinimumDegreeCycleTarget
import Hypostructure.Graph.ExitFourPeeling

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


/-! ## The selected support is itself a trace-complete candidate

`def:typeA-trace-basin` selects `B_u` among the trace-complete connected
candidate basins, and `lem:density-mersenne`'s silent analysis reads that
selection at every unpaid silent routed load.  The selection is total: the
selected support is always a candidate.  The declared support of a
`u`-supported base coordinate either sits inside the support — a D1 coordinate
is a cut-boundary vertex, a D4 wedge is internal, and a packed D3 window lies
wholly in the component — or reaches it from outside and then marks a
cut-boundary vertex: a return crossing the cut leaves a declared vertex on the
boundary, and an attachment outside the support exposes its adjacent window
vertex.  Nothing here chooses a basin; `select?` still returns the canonical
minimum-cardinality candidate. -/

/-- A walk starting inside a support and meeting its complement carries a
cut-boundary vertex. -/
theorem exists_cutBoundary_of_walk_from_inside {support : Finset object.Vertex} :
    ∀ {left right : object.Vertex} (walk : object.graph.Walk left right),
      left ∈ support →
      (∃ outsider ∈ walk.support, outsider ∉ support) →
      ∃ crossing ∈ walk.support,
        crossing ∈
          Strategy.InterfaceReplacement.SupportAtom.cutBoundary object support := by
  intro left right walk
  induction walk with
  | nil =>
      intro inside witness
      obtain ⟨outsider, member, outside⟩ := witness
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at member
      subst member
      exact absurd inside outside
  | @cons head next tail adjacent rest ih =>
      intro inside witness
      obtain ⟨outsider, member, outside⟩ := witness
      by_cases nextInside : next ∈ support
      · have restWitness : outsider ∈ rest.support := by
          rw [SimpleGraph.Walk.support_cons] at member
          rcases List.mem_cons.mp member with rfl | tailMember
          · exact absurd inside outside
          · exact tailMember
        obtain ⟨crossing, crossingMember, crossingBoundary⟩ :=
          ih nextInside ⟨outsider, restWitness, outside⟩
        refine ⟨crossing, ?_, crossingBoundary⟩
        rw [SimpleGraph.Walk.support_cons]
        exact List.mem_cons_of_mem _ crossingMember
      · refine ⟨head, SimpleGraph.Walk.start_mem_support _, ?_⟩
        exact (Strategy.InterfaceReplacement.SupportAtom.mem_cutBoundary_iff
          object support head).2 ⟨inside, next, adjacent, nextInside⟩

/-- A walk starting outside a support and meeting it carries a cut-boundary
vertex. -/
theorem exists_cutBoundary_of_walk_from_outside {support : Finset object.Vertex} :
    ∀ {left right : object.Vertex} (walk : object.graph.Walk left right),
      left ∉ support →
      (∃ insider ∈ walk.support, insider ∈ support) →
      ∃ crossing ∈ walk.support,
        crossing ∈
          Strategy.InterfaceReplacement.SupportAtom.cutBoundary object support := by
  intro left right walk
  induction walk with
  | nil =>
      intro outside witness
      obtain ⟨insider, member, inside⟩ := witness
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at member
      subst member
      exact absurd inside outside
  | @cons head next tail adjacent rest ih =>
      intro outside witness
      obtain ⟨insider, member, inside⟩ := witness
      by_cases nextInside : next ∈ support
      · refine ⟨next, ?_, ?_⟩
        · rw [SimpleGraph.Walk.support_cons]
          exact List.mem_cons_of_mem _ (SimpleGraph.Walk.start_mem_support rest)
        · exact (Strategy.InterfaceReplacement.SupportAtom.mem_cutBoundary_iff
            object support next).2 ⟨nextInside, head, adjacent.symm, outside⟩
      · have restWitness : insider ∈ rest.support := by
          rw [SimpleGraph.Walk.support_cons] at member
          rcases List.mem_cons.mp member with rfl | tailMember
          · exact absurd inside outside
          · exact tailMember
        obtain ⟨crossing, crossingMember, crossingBoundary⟩ :=
          ih nextInside ⟨insider, restWitness, inside⟩
        refine ⟨crossing, ?_, crossingBoundary⟩
        rw [SimpleGraph.Walk.support_cons]
        exact List.mem_cons_of_mem _ crossingMember

/-- A walk meeting both a support and its complement carries a cut-boundary
vertex. -/
theorem exists_cutBoundary_of_walk_crossing {support : Finset object.Vertex}
    {left right insider outsider : object.Vertex}
    (walk : object.graph.Walk left right)
    (insiderMember : insider ∈ walk.support)
    (insiderInside : insider ∈ support)
    (outsiderMember : outsider ∈ walk.support)
    (outsiderOutside : outsider ∉ support) :
    ∃ crossing ∈ walk.support,
      crossing ∈
        Strategy.InterfaceReplacement.SupportAtom.cutBoundary object support := by
  by_cases startInside : left ∈ support
  · exact exists_cutBoundary_of_walk_from_inside walk startInside
      ⟨outsider, outsiderMember, outsiderOutside⟩
  · exact exists_cutBoundary_of_walk_from_outside walk startInside
      ⟨insider, insiderMember, insiderInside⟩

/-- **The selected support is a trace-complete candidate basin** at every load
the canonical routing traces to the receiver. -/
theorem traceComplete_support (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    {receiver load : object.Vertex}
    (connected : SupportComponents.Connected.ConnectedOn object support)
    (routed : object.TraceTo support threshold load receiver) :
    TraceComplete object support threshold receiver load support := by
  classical
  obtain ⟨trace, selected⟩ := Option.isSome_iff_exists.mp
    (object.isSome_tracePath?_of_traceTo routed)
  have receiverInside : receiver ∈ support :=
    (object.mem_support_of_traceTo routed).2
  refine ⟨Finset.Subset.refl support, ⟨trace, selected, ?_⟩, connected, ?_⟩
  · intro vertex member
    exact (object.isTracePath_of_tracePath?_eq_some selected).1 vertex
      (List.mem_toFinset.mp member)
  · intro coordinate _scheduled uSupported
    cases coordinate with
    | d1 boundaryCoordinate =>
        refine Or.inr ⟨boundaryCoordinate.1, boundaryCoordinate.2, ?_⟩
        show boundaryCoordinate.1 ∈
          D1.declaredSupport object support boundaryCoordinate
        unfold D1.declaredSupport
        exact Finset.mem_singleton_self _
    | d2ReturnLength returnCoordinate =>
        have uSupportedReturn : D2.USupported object support threshold receiver
            load returnCoordinate := uSupported
        by_cases contained :
            Base.declaredSupport object support
              (.d2ReturnLength returnCoordinate) ⊆ support
        · exact Or.inl contained
        · obtain ⟨escapee, escapeeDeclared, escapeeOutside⟩ :=
            Finset.not_subset.mp contained
          have escapeeWalk :
              escapee ∈ returnCoordinate.ambientPath.support := by
            have declared : escapee ∈
                D2.declaredSupport object returnCoordinate := escapeeDeclared
            unfold D2.declaredSupport at declared
            exact List.mem_toFinset.mp declared
          have anchor : ∃ insider ∈ returnCoordinate.ambientPath.support,
              insider ∈ support := by
            rcases uSupportedReturn with meets | owned
            · obtain ⟨trace', selected', vertex, vertexDeclared, vertexTrace⟩ :=
                meets
              refine ⟨vertex, ?_, ?_⟩
              · have declared : vertex ∈
                    D2.declaredSupport object returnCoordinate := vertexDeclared
                unfold D2.declaredSupport at declared
                exact List.mem_toFinset.mp declared
              · exact (object.isTracePath_of_tracePath?_eq_some selected').1
                  vertex vertexTrace
            · obtain ⟨outside, _port, fstEq, _sndEq, _return', _scheduled',
                _owns⟩ := owned
              refine ⟨returnCoordinate.dart.fst,
                SimpleGraph.Walk.end_mem_support _, ?_⟩
              rw [fstEq]
              exact receiverInside
          obtain ⟨insider, insiderWalk, insiderInside⟩ := anchor
          obtain ⟨crossing, crossingWalk, crossingBoundary⟩ :=
            exists_cutBoundary_of_walk_crossing returnCoordinate.ambientPath
              insiderWalk insiderInside escapeeWalk escapeeOutside
          refine Or.inr ⟨crossing, crossingBoundary, ?_⟩
          show crossing ∈ D2.declaredSupport object returnCoordinate
          unfold D2.declaredSupport
          exact List.mem_toFinset.mpr crossingWalk
    | d3WindowLabel windowCoordinate =>
        obtain ⟨⟨window, attachment⟩, isAttachment⟩ := windowCoordinate
        by_cases attachmentInside : attachment ∈ support
        · refine Or.inl ?_
          intro vertex vertexMember
          have declared : vertex ∈
              D3.declaredSupport object support
                ⟨(window, attachment), isAttachment⟩ := vertexMember
          unfold D3.declaredSupport at declared
          simp only [Finset.mem_union, Finset.mem_singleton] at declared
          rcases declared with inWindow | rfl
          · rw [D3.placement_support] at inWindow
            exact window.2 inWindow
          · exact attachmentInside
        · obtain ⟨index, indexMember⟩ := isAttachment.2
          have adjacency : object.graph.Adj attachment
              (D3.placement object support window index) :=
            (D3.mem_attachmentLabel_iff object support window attachment
              index).mp indexMember
          have anchorWindow : D3.placement object support window index ∈
              InducedPathMaximalPacking.support object 13
                (D3.placement object support window) := by
            unfold InducedPathMaximalPacking.support
            exact Finset.mem_image.mpr ⟨index, Finset.mem_univ index, rfl⟩
          have anchorInside :
              D3.placement object support window index ∈ support := by
            have copy := anchorWindow
            rw [D3.placement_support] at copy
            exact window.2 copy
          refine Or.inr ⟨D3.placement object support window index, ?_, ?_⟩
          · exact (Strategy.InterfaceReplacement.SupportAtom.mem_cutBoundary_iff
              object support _).2
              ⟨anchorInside, attachment, adjacency.symm, attachmentInside⟩
          · show D3.placement object support window index ∈
              D3.declaredSupport object support
                ⟨(window, attachment), isAttachment⟩
            unfold D3.declaredSupport
            simp only [Finset.mem_union]
            exact Or.inl anchorWindow
    | d4RawCurvature wedgeCoordinate =>
        refine Or.inl ?_
        intro vertex vertexMember
        have declared : vertex ∈
            D4.declaredSupport object support wedgeCoordinate := vertexMember
        unfold D4.declaredSupport FiniteObject.internalWedgeSupport at declared
        rcases Finset.mem_insert.mp declared with rfl | inPair
        · have familyMember := wedgeCoordinate.2
          unfold FiniteObject.internalWedgeFamily at familyMember
          exact (Finset.mem_sigma.mp familyMember).1
        · have inNeighbors :=
            (Finset.mem_powersetCard.mp wedgeCoordinate.1.2.2).1 inPair
          unfold FiniteObject.internalNeighborFinset at inNeighbors
          simp only [Finset.mem_inter] at inNeighbors
          exact inNeighbors.2

/-- Basin selection succeeds at every load the canonical routing traces to the
receiver. -/
theorem select?_isSome_of_traceTo (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    {receiver load : object.Vertex}
    (connected : SupportComponents.Connected.ConnectedOn object support)
    (routed : object.TraceTo support threshold load receiver) :
    (select? object support threshold receiver load).isSome :=
  select?_isSome ⟨support, mem_candidates_iff.mpr
    (traceComplete_support object support threshold connected routed)⟩

/-- **Basin selection is total on `ℒ(w)`**: every routed load of a receiver of
a connected support has its selected trace basin. -/
theorem exists_select?_eq_some_of_mem_routedLoads (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    {receiver load : object.Vertex}
    (connected : SupportComponents.Connected.ConnectedOn object support)
    (routedLoad : load ∈ object.routedLoads support threshold receiver) :
    ∃ basin, select? object support threshold receiver load = some basin :=
  Option.isSome_iff_exists.mp
    (select?_isSome_of_traceTo object support threshold connected
      (object.traceTo_of_traceReceiver?_eq_some
        ((object.mem_routedLoads).mp routedLoad).2.2))


end TraceBasin

namespace PresentedEntry

open TraceCoordinateSystem

/-- The declared coordinate algebra of one selected trace basin.  The base
coordinate families are restricted to the coordinates supported at the routed
load, and `traceIncidence` is the manuscript's distinguished coordinate
recording the labelled canonical trace `T_u`. -/
inductive TraceCoordinate (object : FiniteObject.{u})
    (support : Finset object.Vertex) where
  | base (coordinate : TraceCoordinateSystem.Base.Coordinate object support)
  | traceIncidence

noncomputable instance traceCoordinateDecEq (object : FiniteObject.{u})
    (support : Finset object.Vertex) :
    DecidableEq (TraceCoordinate object support) :=
  Classical.decEq _

/-- The exact declared `u`-supported coordinate family, including the
distinguished trace-incidence coordinate required by
`def:typeA-trace-basin`. -/
noncomputable def traceCoordinates (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (receiver load : object.Vertex) :
    Finset (TraceCoordinate object support) := by
  classical
  exact insert .traceIncidence
    (((TraceCoordinateSystem.Base.schedule object support).toFinset.filter
      (fun coordinate =>
        TraceCoordinateSystem.Base.uSupported object support threshold receiver
          load coordinate)).image TraceCoordinate.base)

/-- The base-coordinate part retained by a trace-coordinate restriction. -/
noncomputable def retainedBaseCoordinates (object : FiniteObject.{u})
    (support : Finset object.Vertex)
    (retained : Finset (TraceCoordinate object support)) :
    Finset (TraceCoordinateSystem.Base.Coordinate object support) := by
  classical
  exact (TraceCoordinateSystem.Base.schedule object support).toFinset.filter
    (fun coordinate => TraceCoordinate.base coordinate ∈ retained)

/-- The dependent value type of the selected trace-coordinate algebra. -/
def TraceValue (object : FiniteObject.{u})
    (support : Finset object.Vertex) :
    TraceCoordinate object support → Type u
  | .base coordinate =>
      ULift.{u} (TraceCoordinateSystem.Base.Value object support coordinate)
  | .traceIncidence => ULift.{u} (Finset object.Vertex)

/-- The graph-derived value of a selected trace coordinate. -/
noncomputable def traceValue (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (receiver load : object.Vertex) :
    (coordinate : TraceCoordinate object support) →
      TraceValue object support coordinate
  | .base coordinate =>
      ULift.up (TraceCoordinateSystem.Base.value object support coordinate)
  | .traceIncidence =>
      ULift.up
        ((TraceBasin.traceSeed? object support threshold receiver load).getD ∅)

/-- Declared support in the selected trace-coordinate algebra. -/
noncomputable def traceDeclaredSupport (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (receiver load : object.Vertex) :
    TraceCoordinate object support → Finset object.Vertex
  | .base coordinate =>
      TraceCoordinateSystem.Base.declaredSupport object support coordinate
  | .traceIncidence =>
      (TraceBasin.traceSeed? object support threshold receiver load).getD ∅

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

/-- Target events of the selected trace-coordinate algebra.  The distinguished
trace coordinate records `T_u` itself and is not a target event. -/
noncomputable def eventOfTraceCoordinate (object : FiniteObject.{u})
    (support : Finset object.Vertex) (LengthOK : Nat → Prop) :
    TraceCoordinate object support → Option (CoordinateEvent object)
  | .base coordinate => eventOfBase object support LengthOK coordinate
  | .traceIncidence => none

/-- **`\rho_u(B_u)|_D` realized at the object.**

The vertices a set of declared coordinates keeps alive: the union of their
declared supports.  A coordinate the restriction forgets stops contributing its
declared support to the reading, which is precisely what
`def:typeA-route8-carriers` forgets when it passes from `\mathcal C` to
`\mathcal C \setminus \{c\}`. -/
noncomputable def retainedVertices (object : FiniteObject.{u})
    (support : Finset object.Vertex)
    (retained : Finset (TraceCoordinateSystem.Base.Coordinate object support)) :
    Finset object.Vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact retained.biUnion (TraceCoordinateSystem.Base.declaredSupport object support)

/-- **The basin piece a set of declared coordinates presents.**

`def:typeA-route8-carriers`: a `D`-restriction retains "the full boundary degree
profile" and, apart from that profile, exactly the declared coordinates carried
inside `D`; "thus every carrier restriction is taken inside the original
boundary-degree fibre".  An edge incident with a labelled boundary vertex is
therefore owned by every restriction, and only the internal edges follow the
retained declared supports. -/
noncomputable def retainedBasinPiece (object : FiniteObject.{u})
    (basin retained : Finset object.Vertex) :
    BoundaryPiece
      (Strategy.InterfaceReplacement.SupportAtom.boundary object basin) where
  Internal :=
    Strategy.InterfaceReplacement.SupportAtom.PieceInternal object basin
  internalVertices := by
    letI : FinEnum object.Vertex := object.vertices
    exact FinEnum.Subtype.finEnum fun vertex =>
      vertex ∈ basin ∧
        vertex ∉
          Strategy.InterfaceReplacement.SupportAtom.cutBoundary object basin
  graph :=
    SimpleGraph.comap
        (Strategy.InterfaceReplacement.SupportAtom.pieceDecode object basin)
        object.graph ⊓
      SimpleGraph.fromRel fun left right =>
        left.isLeft = true ∨ right.isLeft = true ∨
          (Strategy.InterfaceReplacement.SupportAtom.pieceDecode object basin
              left ∈ retained ∧
            Strategy.InterfaceReplacement.SupportAtom.pieceDecode object basin
              right ∈ retained)
  decideAdj := Classical.decRel _

/-- Every restriction keeps the basin's own boundary-degree profile. -/
theorem retainedBasinPiece_boundaryDegreeProfile (object : FiniteObject.{u})
    (basin retained : Finset object.Vertex) :
    (retainedBasinPiece object basin retained).boundaryDegreeProfile =
      (Strategy.InterfaceReplacement.SupportAtom.piece object
        basin).boundaryDegreeProfile := by
  funext vertex
  simp only [BoundaryPiece.boundaryDegreeProfile, BoundaryPiece.boundaryDegree,
    FiniteObject.degree_eq_ncard_neighborSet]
  congr 1
  ext other
  simp only [SimpleGraph.mem_neighborSet]
  constructor
  · intro adjacent
    exact adjacent.1
  · intro adjacent
    exact ⟨adjacent, fun same => adjacent.ne (congrArg _ same),
      Or.inl (Or.inl rfl)⟩

/-- The decode map of a retained basin piece is injective: boundary labels and
internal vertices are disjoint ambient classes, and each carries its ambient
vertex. -/
theorem retainedBasinPiece_decode_injective (object : FiniteObject.{u})
    (basin : Finset object.Vertex) :
    Function.Injective
      (Strategy.InterfaceReplacement.SupportAtom.pieceDecode object basin) := by
  intro left right equal
  rcases left with leftLabel | leftInside <;>
    rcases right with rightLabel | rightInside
  · exact congrArg Sum.inl (Subtype.ext equal)
  · have valueEq : leftLabel.1 = rightInside.1 := equal
    exact absurd (valueEq ▸ leftLabel.2) rightInside.2.2
  · have valueEq : rightLabel.1 = leftInside.1 := equal.symm
    exact absurd (valueEq ▸ rightLabel.2) leftInside.2.2
  · exact congrArg Sum.inr (Subtype.ext equal)

/-- **An accepted internal cycle of a retained reading is an accepted cycle of
the object**: the reading's graph is a restriction of the ambient graph, and
its decode map is injective. -/
theorem hasCycleWithLength_of_retainedBasinPiece_cycle
    (object : FiniteObject.{u}) (basin retained : Finset object.Vertex)
    {LengthOK : Nat → Prop}
    {base : (Strategy.InterfaceReplacement.SupportAtom.boundary object
      basin).Vertex ⊕ (retainedBasinPiece object basin retained).Internal}
    {c : (retainedBasinPiece object basin retained).graph.Walk base base}
    (cycle : c.IsCycle) (accepted : LengthOK c.length) :
    HasCycleWithLength LengthOK object := by
  classical
  let decodeHom : (retainedBasinPiece object basin retained).graph →g
      object.graph :=
    ⟨Strategy.InterfaceReplacement.SupportAtom.pieceDecode object basin,
      fun adjacent => adjacent.1⟩
  refine ⟨⟨_, c.map decodeHom, ?_, ?_⟩⟩
  · exact cycle.map (retainedBasinPiece_decode_injective object basin)
  · rw [SimpleGraph.Walk.length_map]
    exact accepted

/-- **A label path of a retained reading is an object path**: the decode map
is an injective graph homomorphism, so paths transfer with their length. -/
theorem exists_object_path_of_retainedBasinPiece_path (object : FiniteObject.{u})
    (basin retained : Finset object.Vertex)
    {start finish : (Strategy.InterfaceReplacement.SupportAtom.boundary object
      basin).Vertex ⊕ (retainedBasinPiece object basin retained).Internal}
    (q : (retainedBasinPiece object basin retained).graph.Walk start finish)
    (isPath : q.IsPath) :
    ∃ walk : object.graph.Walk
        (Strategy.InterfaceReplacement.SupportAtom.pieceDecode object basin
          start)
        (Strategy.InterfaceReplacement.SupportAtom.pieceDecode object basin
          finish),
      walk.IsPath ∧ walk.length = q.length := by
  classical
  let decodeHom : (retainedBasinPiece object basin retained).graph →g
      object.graph :=
    ⟨Strategy.InterfaceReplacement.SupportAtom.pieceDecode object basin,
      fun adjacent => adjacent.1⟩
  exact ⟨q.map decodeHom,
    SimpleGraph.Walk.map_isPath_of_injective
      (retainedBasinPiece_decode_injective object basin) isPath,
    SimpleGraph.Walk.length_map _ _⟩

/-- The canonical encode of a basin vertex into a retained piece carrier:
boundary labels to the left, internal vertices to the right. -/
noncomputable def pieceEncode (object : FiniteObject.{u})
    (basin : Finset object.Vertex) (vertex : object.Vertex)
    (inside : vertex ∈ basin) :
    (Strategy.InterfaceReplacement.SupportAtom.boundary object basin).Vertex ⊕
      Strategy.InterfaceReplacement.SupportAtom.PieceInternal object basin := by
  classical
  exact if member : vertex ∈
      Strategy.InterfaceReplacement.SupportAtom.cutBoundary object basin then
    Sum.inl ⟨vertex, member⟩
  else Sum.inr ⟨vertex, inside, member⟩

@[simp] theorem pieceDecode_pieceEncode (object : FiniteObject.{u})
    (basin : Finset object.Vertex) (vertex : object.Vertex)
    (inside : vertex ∈ basin) :
    Strategy.InterfaceReplacement.SupportAtom.pieceDecode object basin
      (pieceEncode object basin vertex inside) = vertex := by
  unfold pieceEncode
  split <;> rfl

/-- Encoding a cut-boundary vertex yields its boundary label. -/
theorem pieceEncode_of_mem_cutBoundary (object : FiniteObject.{u})
    (basin : Finset object.Vertex) (vertex : object.Vertex)
    (inside : vertex ∈ basin)
    (member : vertex ∈
      Strategy.InterfaceReplacement.SupportAtom.cutBoundary object basin) :
    pieceEncode object basin vertex inside = Sum.inl ⟨vertex, member⟩ := by
  unfold pieceEncode
  rw [dif_pos member]

/-- **A support channel is a walk of every retained reading that keeps its
vertices**: encode each channel vertex by its ownership class.  Length and
decoded support are preserved. -/
theorem exists_retainedBasinPiece_walk_of_channel (object : FiniteObject.{u})
    (basin retained : Finset object.Vertex)
    {entry receiver : object.Vertex}
    (channel : object.graph.Walk entry receiver)
    (inside : ∀ vertex ∈ channel.support, vertex ∈ basin)
    (kept : ∀ vertex ∈ channel.support, vertex ∈ retained) :
    ∃ q : (retainedBasinPiece object basin retained).graph.Walk
        (pieceEncode object basin entry
          (inside entry channel.start_mem_support))
        (pieceEncode object basin receiver
          (inside receiver channel.end_mem_support)),
      q.length = channel.length ∧
        q.support.map
            (Strategy.InterfaceReplacement.SupportAtom.pieceDecode object
              basin) =
          channel.support := by
  classical
  induction channel with
  | nil =>
      refine ⟨.nil, rfl, ?_⟩
      rw [SimpleGraph.Walk.support_nil]
      show [Strategy.InterfaceReplacement.SupportAtom.pieceDecode object basin
        (pieceEncode object basin _ _)] = [_]
      rw [pieceDecode_pieceEncode]
  | @cons first second finish adjacent rest ih =>
      have consMem : ∀ vertex ∈ rest.support,
          vertex ∈ (SimpleGraph.Walk.cons adjacent rest).support := by
        intro vertex member
        rw [SimpleGraph.Walk.support_cons]
        exact List.mem_cons_of_mem _ member
      have restInside : ∀ vertex ∈ rest.support, vertex ∈ basin :=
        fun vertex member => inside vertex (consMem vertex member)
      have restKept : ∀ vertex ∈ rest.support, vertex ∈ retained :=
        fun vertex member => kept vertex (consMem vertex member)
      obtain ⟨q, qLength, qSupport⟩ := ih restInside restKept
      have firstMem : first ∈ (SimpleGraph.Walk.cons adjacent rest).support :=
        SimpleGraph.Walk.start_mem_support _
      have secondMem : second ∈ (SimpleGraph.Walk.cons adjacent rest).support :=
        consMem second rest.start_mem_support
      have edge : (retainedBasinPiece object basin retained).graph.Adj
          (pieceEncode object basin first (inside first firstMem))
          (pieceEncode object basin second (inside second secondMem)) := by
        refine ⟨?_, ?_⟩
        · show object.graph.Adj
            (Strategy.InterfaceReplacement.SupportAtom.pieceDecode object basin
              (pieceEncode object basin first (inside first firstMem)))
            (Strategy.InterfaceReplacement.SupportAtom.pieceDecode object basin
              (pieceEncode object basin second (inside second secondMem)))
          rw [pieceDecode_pieceEncode, pieceDecode_pieceEncode]
          exact adjacent
        · rw [SimpleGraph.fromRel_adj]
          refine ⟨?_, Or.inl (Or.inr (Or.inr ⟨?_, ?_⟩))⟩
          · intro same
            have decoded := congrArg
              (Strategy.InterfaceReplacement.SupportAtom.pieceDecode object
                basin) same
            rw [pieceDecode_pieceEncode, pieceDecode_pieceEncode] at decoded
            exact adjacent.ne decoded
          · rw [pieceDecode_pieceEncode]
            exact kept first firstMem
          · rw [pieceDecode_pieceEncode]
            exact kept second secondMem
      refine ⟨SimpleGraph.Walk.cons edge q, ?_, ?_⟩
      · rw [SimpleGraph.Walk.length_cons, qLength,
          SimpleGraph.Walk.length_cons]
      · rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_cons]
        show Strategy.InterfaceReplacement.SupportAtom.pieceDecode object basin
            (pieceEncode object basin first (inside first firstMem)) ::
            q.support.map
              (Strategy.InterfaceReplacement.SupportAtom.pieceDecode object
                basin) =
          first :: rest.support
        rw [pieceDecode_pieceEncode, qSupport]

/-- **A support channel path is a path of every retained reading that keeps
its vertices**, between its two encoded endpoints, of the same length. -/
theorem exists_retainedBasinPiece_path_of_channel (object : FiniteObject.{u})
    (basin retained : Finset object.Vertex)
    {entry receiver : object.Vertex}
    (channel : object.graph.Walk entry receiver)
    (isPath : channel.IsPath)
    (inside : ∀ vertex ∈ channel.support, vertex ∈ basin)
    (kept : ∀ vertex ∈ channel.support, vertex ∈ retained) :
    ∃ q : (retainedBasinPiece object basin retained).graph.Walk
        (pieceEncode object basin entry
          (inside entry channel.start_mem_support))
        (pieceEncode object basin receiver
          (inside receiver channel.end_mem_support)),
      q.IsPath ∧ q.length = channel.length := by
  obtain ⟨q, qLength, qSupport⟩ :=
    exists_retainedBasinPiece_walk_of_channel object basin retained channel
      inside kept
  refine ⟨q, ?_, qLength⟩
  rw [SimpleGraph.Walk.isPath_def]
  have nodup : (q.support.map
      (Strategy.InterfaceReplacement.SupportAtom.pieceDecode object
        basin)).Nodup := by
    rw [qSupport]
    exact isPath.support_nodup
  exact nodup.of_map

/-- **The reading a set of declared coordinates presents at the basin.**

This is the manuscript's response state `\rho_u(B_u)` restricted to the retained
declared coordinates: the basin's own boundaried piece with exactly the internal
edges the retained declared supports own, replaced by *the* canonical piece of
its cut state (`def:proper-quotient-representative`, `Graph/CanonicalRealization`).

Two clauses of `def:typeA-route8-carriers` are theorems about it rather than
assumptions: the restriction stays inside the original boundary-degree fibre
(`retainedPiece_boundaryDegreeProfile` composed with the canonical
representative's own profile clause -- see `ofTraceBasin_boundaryDegreeProfile`),
and it is a response quotient of the same interface, so it can be tested against
the unrestricted reading by an outside context. -/
noncomputable def retainedReading (object : FiniteObject.{u})
    (support basin : Finset object.Vertex) (threshold : Nat)
    (LengthOK : Nat → Prop)
    (retained : Finset (TraceCoordinateSystem.Base.Coordinate object support)) :
    BoundaryPiece
      (Strategy.InterfaceReplacement.SupportAtom.boundary object basin) :=
  (CanonicalPiece.cutStateRepresentative
    (minimumDegreeAtLeast_isomorphismInvariant threshold)
    (cycleTargetInterface LengthOK).isomorphismInvariant
    (retainedBasinPiece object basin
      (retainedVertices object support retained))).toPiece

/-- **Every restriction of the reading has the basin's boundary-degree
profile.**  `def:typeA-route8-carriers`: *"every carrier restriction is taken
inside the original boundary-degree fibre"*. -/
theorem retainedReading_boundaryDegreeProfile (object : FiniteObject.{u})
    (support basin : Finset object.Vertex) (threshold : Nat)
    (LengthOK : Nat → Prop)
    (retained : Finset (TraceCoordinateSystem.Base.Coordinate object support)) :
    (retainedReading object support basin threshold LengthOK
        retained).boundaryDegreeProfile =
      (Strategy.InterfaceReplacement.SupportAtom.piece object
        basin).boundaryDegreeProfile := by
  rw [retainedReading]
  refine Eq.trans ?_
    (retainedBasinPiece_boundaryDegreeProfile object basin
      (retainedVertices object support retained))
  exact (CanonicalPiece.cutStateRepresentative_reading
    (minimumDegreeAtLeast_isomorphismInvariant threshold)
    (cycleTargetInterface LengthOK).isomorphismInvariant _).1

end PresentedEntry

namespace TraceBasin

open TraceCoordinateSystem

/-- **Alternative (b) of `def:typeA-trace-basin`.**

A trace-local response quotient is represented by the declared coordinates it
retains.  Omitted coordinates are the forgotten coordinates, or the
non-representative members of identified coordinate classes.  The quotient is
nontrivial only when one omitted coordinate has genuinely internal declared
support.  `PresentedEntry.retainedReading` preserves every boundary incidence.
The exit-`(5)` compression datum also records the proper connected support and
the strictly smaller baseline realization required by
`def:target-complete-compression`. -/
def TraceTargetCompleteCompression (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (LengthOK : Nat → Prop) (receiver load : object.Vertex)
    (basin : Finset object.Vertex) : Prop :=
  let coordinates :=
    PresentedEntry.traceCoordinates object support threshold receiver load
  ∃ retained : Finset (PresentedEntry.TraceCoordinate object support),
    retained ⊆ coordinates ∧
      (∃ changed ∈ coordinates,
        changed ∉ retained ∧
          ((changed = .traceIncidence ∧
              ∃ trace : object.graph.Path load receiver,
                object.tracePath? support threshold load receiver = some trace ∧
                  0 < trace.1.length ∧ trace.1.support.toFinset ⊆ basin) ∨
            (∃ vertex ∈
              PresentedEntry.traceDeclaredSupport object support threshold receiver
                load changed,
            vertex ∈ basin ∧
              vertex ∉
                Strategy.InterfaceReplacement.SupportAtom.cutBoundary object basin) ∨
            ∃ left ∈
                PresentedEntry.traceDeclaredSupport object support threshold receiver
                  load changed,
              ∃ right ∈
                  PresentedEntry.traceDeclaredSupport object support threshold receiver
                    load changed,
                left ∈ basin ∧ right ∈ basin ∧ object.graph.Adj left right)) ∧
      Response.TargetComplete BoundaryPiece.boundaryDegreeProfile
        (HasCycleWithLength LengthOK)
        (PresentedEntry.retainedReading object support basin threshold LengthOK
          (PresentedEntry.retainedBaseCoordinates object support retained))
        (Strategy.InterfaceReplacement.SupportAtom.piece object basin) ∧
      ∃ connected : SupportComponents.Connected.ConnectedOn object basin,
        ∃ proper : ∃ vertex, vertex ∉ basin,
          let atom :=
            Strategy.InterfaceReplacement.SupportAtom.properAtom object basin
              connected proper
          MinimumDegreeAtLeast threshold
              (glue
                (PresentedEntry.retainedReading object support basin threshold
                  LengthOK
                  (PresentedEntry.retainedBaseCoordinates object support retained))
                atom.decomposition.outside) ∧
            (glue
                (PresentedEntry.retainedReading object support basin threshold
                  LengthOK
                  (PresentedEntry.retainedBaseCoordinates object support retained))
                atom.decomposition.outside).LexicographicallySmaller object

/-- **The response quotient of alternative (b)**, as a predicate on the retained
declared coordinates: retained inside the declared family, nontrivial, and
target-complete for the full declared reading `\rho_u(B_u)`.  This is the
quotient constructed by `lem:typeA-one-terminal-collapse`. -/
def TraceResponseQuotient (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (LengthOK : Nat → Prop) (receiver load : object.Vertex)
    (basin : Finset object.Vertex)
    (retained : Finset (PresentedEntry.TraceCoordinate object support)) : Prop :=
  let coordinates :=
    PresentedEntry.traceCoordinates object support threshold receiver load
  retained ⊆ coordinates ∧
    (∃ changed ∈ coordinates,
      changed ∉ retained ∧
        ((changed = .traceIncidence ∧
            ∃ trace : object.graph.Path load receiver,
              object.tracePath? support threshold load receiver = some trace ∧
                0 < trace.1.length ∧ trace.1.support.toFinset ⊆ basin) ∨
          (∃ vertex ∈
            PresentedEntry.traceDeclaredSupport object support threshold receiver
              load changed,
          vertex ∈ basin ∧
            vertex ∉
              Strategy.InterfaceReplacement.SupportAtom.cutBoundary object basin) ∨
          ∃ left ∈
              PresentedEntry.traceDeclaredSupport object support threshold receiver
                load changed,
            ∃ right ∈
                PresentedEntry.traceDeclaredSupport object support threshold receiver
                  load changed,
              left ∈ basin ∧ right ∈ basin ∧ object.graph.Adj left right)) ∧
    Response.TargetComplete BoundaryPiece.boundaryDegreeProfile
      (HasCycleWithLength LengthOK)
      (PresentedEntry.retainedReading object support basin threshold LengthOK
        (PresentedEntry.retainedBaseCoordinates object support retained))
      (PresentedEntry.retainedReading object support basin threshold LengthOK
        (PresentedEntry.retainedBaseCoordinates object support coordinates))

end TraceBasin

namespace PresentedEntry

/-- The graph-owned presented entry assigned to a selected trace basin.  The
coordinate family, values, supports and target events are all read from the
declared trace-coordinate system of the selected support, and the reading of a
retained coordinate set is the canonical realization
`retainedReading` of `\rho_u(B_u)|_D`. -/
noncomputable def ofTraceBasin (object : FiniteObject.{u})
    (support basin : Finset object.Vertex) (threshold : Nat)
    (LengthOK : Nat → Prop) (receiver load : object.Vertex) :
    PresentedEntry object where
  support := support
  interface := Strategy.InterfaceReplacement.SupportAtom.boundary object basin
  Coordinate := TraceCoordinate object support
  coordinateDecEq := traceCoordinateDecEq object support
  coordinates := traceCoordinates object support threshold receiver load
  Value := TraceValue object support
  value := traceValue object support threshold receiver load
  declaredSupport := traceDeclaredSupport object support threshold receiver load
  event? := eventOfTraceCoordinate object support LengthOK
  state := fun retained =>
    retainedReading object support basin threshold LengthOK
      (retainedBaseCoordinates object support retained)

/-- **Every carrier restriction of a presented trace-basin entry sits in the
basin's own boundary-degree fibre.**  This is the clause node `[124]` consumes:
a carrier-deletion quotient of the entry preserves the boundary-degree profile,
so it is a *response quotient* and therefore a legitimate member of the
canonical exit-`(4)` family `\mathcal Q_4(w)`. -/
theorem ofTraceBasin_boundaryDegreeProfile (object : FiniteObject.{u})
    (support basin : Finset object.Vertex) (threshold : Nat)
    (LengthOK : Nat → Prop) (receiver load : object.Vertex)
    (left right : Finset (TraceCoordinate object support)) :
    ((ofTraceBasin object support basin threshold LengthOK receiver load).state
        left).boundaryDegreeProfile =
      ((ofTraceBasin object support basin threshold LengthOK receiver load).state
        right).boundaryDegreeProfile := by
  show (retainedReading object support basin threshold LengthOK
      (retainedBaseCoordinates object support left)).boundaryDegreeProfile =
    (retainedReading object support basin threshold LengthOK
      (retainedBaseCoordinates object support right)).boundaryDegreeProfile
  rw [retainedReading_boundaryDegreeProfile,
    retainedReading_boundaryDegreeProfile]

end PresentedEntry

end Hypostructure.Graph.Route8
