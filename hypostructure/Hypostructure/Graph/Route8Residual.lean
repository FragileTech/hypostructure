import Hypostructure.Graph.CanonicalSupportSelection
import Hypostructure.Graph.Route8Closure
import Hypostructure.Graph.TraceCoordinateSystem
import Hypostructure.Graph.CanonicalRealization
import Hypostructure.Graph.MinimumDegreeCycleTarget
import Hypostructure.Graph.ExitFourPeeling
import Hypostructure.Graph.InternalVertexFold
import Hypostructure.Graph.BoundaryOverlap

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

/-- **A crossing carrier is witnessed on the walk itself.**  Every crossing edge
is the edge of a dart of the walk, so the endpoint it keeps inside the support is
a vertex the walk visits.  This is what lets a coordinate whose declared support
*is* its own path record its own crossings. -/
theorem exists_inside_mem_support_of_mem_crossingCarriers
    {support : Finset object.Vertex} {base : object.Vertex}
    {walk : object.graph.Walk base base} {edge : Sym2 object.Vertex}
    (member : edge ∈ crossingCarriers support walk) :
    ∃ inside ∈ edge, inside ∈ support ∧ inside ∈ walk.support := by
  classical
  rw [crossingCarriers, List.mem_toFinset, CutParity.crossingEdges,
    List.mem_map] at member
  obtain ⟨dart, filtered, shape⟩ := member
  rw [List.mem_filter] at filtered
  have crossing : CutParity.crosses (G := object.graph)
      (S := (support : Set object.Vertex)) dart = true := by
    simpa using filtered.2
  rw [CutParity.crosses, CutParity.side, CutParity.side, bne_iff_ne, ne_eq,
    decide_eq_decide] at crossing
  by_cases first : dart.fst ∈ support
  · refine ⟨dart.fst, ?_, first, ?_⟩
    · rw [← shape]
      simp [SimpleGraph.Dart.edge]
    · exact walk.dart_fst_mem_support_of_mem_darts filtered.1
  · have second : dart.snd ∈ support := by
      by_contra missing
      exact crossing (by
        constructor
        · intro inside; exact absurd inside first
        · intro inside; exact absurd inside missing)
    refine ⟨dart.snd, ?_, second, ?_⟩
    · rw [← shape]
      simp [SimpleGraph.Dart.edge]
    · exact walk.dart_snd_mem_support_of_mem_darts filtered.1

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
coordinates.  Carrier data is not supplied by a caller: it is derived from the
coordinate's declared support and, for an event coordinate, from the event's
actual cut crossings. -/
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

/-- The boundary incidences explicitly met by a coordinate's declared support.

This is the literal carrier source in `def:typeA-route8-carriers`: D1 boundary
vertices, completion-port/first-entry vertices in D2, window-interface
vertices in D3, wedge vertices in D4, and the terminal receiver of the trace
coordinate all retain the cut incidences incident with those declared
vertices.  In particular a coordinate with no target event need not have an
empty carrier set. -/
noncomputable def declaredCarriers (r : presented.Coordinate) :
    Finset (Sym2 object.Vertex) := by
  classical
  exact (cutEdges object presented.support).filter fun edge =>
    exists inside, inside ∈ edge /\ inside ∈ presented.support /\
      inside ∈ presented.declaredSupport r

/-- **`def:typeA-route8-carriers`**: *"every declared
`u`-supported coordinate of `\rho_u(B_u)` that uses the ambient exterior of `X`
RECORDS the oriented boundary incidence of `X` through which it leaves `X` ...
when that incidence is represented by an edge `xy` in `E(G)` with `x \in V(X)`
and `y \notin V(X)`, its boundary incidence is the element `c=(x,xy)` in
`\partial_E X` ... boundary incidences are not extra data attached to `B_u`;
they are the `\partial_E X`-labels already recorded by the declared coordinate
signature."*

Two distinct such recorded incidences are two distinct declared carriers.  This
is the signature half of `lem:typeA-carrier-cut-parity` and it
reads nothing off any cycle, in any object: only the coordinate's declared
support is used. -/
theorem two_le_card_declaredCarriers (r : presented.Coordinate)
    {first second : Sym2 object.Vertex} (distinct : first ≠ second)
    (firstCut : first ∈ cutEdges object presented.support)
    (secondCut : second ∈ cutEdges object presented.support)
    (firstDeclared : ∃ inside ∈ first, inside ∈ presented.support ∧
      inside ∈ presented.declaredSupport r)
    (secondDeclared : ∃ inside ∈ second, inside ∈ presented.support ∧
      inside ∈ presented.declaredSupport r) :
    2 ≤ (presented.declaredCarriers r).card := by
  classical
  have firstMem : first ∈ presented.declaredCarriers r := by
    rw [declaredCarriers, Finset.mem_filter]
    exact ⟨firstCut, firstDeclared⟩
  have secondMem : second ∈ presented.declaredCarriers r := by
    rw [declaredCarriers, Finset.mem_filter]
    exact ⟨secondCut, secondDeclared⟩
  have subset : ({first, second} : Finset (Sym2 object.Vertex)) ⊆
      presented.declaredCarriers r := by
    intro edge edgeMem
    rcases Finset.mem_insert.mp edgeMem with rfl | tail
    · exact firstMem
    · rw [Finset.mem_singleton.mp tail]
      exact secondMem
  have card : ({first, second} : Finset (Sym2 object.Vertex)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using distinct),
      Finset.card_singleton]
  exact card ▸ Finset.card_le_card subset

/-- The full carrier support of a declared coordinate.  The first summand is
the manuscript's declared-support carrier.  The second records the cut
crossings of an actual event coordinate, which are themselves part of that
coordinate's declared event support.  Keeping both sources is essential:
target avoidance can remove the second summand but never the first. -/
noncomputable def car (r : presented.Coordinate) : Finset (Sym2 object.Vertex) :=
  presented.declaredCarriers r ∪
    match presented.event? r with
    | none => ∅
    | some event => crossingCarriers presented.support event.walk

/-- Declared carriers are carriers: the signature half of
`lem:typeA-carrier-cut-parity` feeds the entry's carrier accounting without ever
touching the event summand of `car`. -/
theorem declaredCarriers_subset_car (r : presented.Coordinate) :
    presented.declaredCarriers r ⊆ presented.car r := by
  rw [car]
  exact Finset.subset_union_left

/-- **Two recorded boundary incidences give two carriers.**  This is the step
`lem:typeA-carrier-cut-parity` needs, with the event summand of `car` playing no
part, so it is available for an event living in a glued realization. -/
theorem two_le_card_car_of_two_incidences (r : presented.Coordinate)
    {first second : Sym2 object.Vertex} (distinct : first ≠ second)
    (firstCut : first ∈ cutEdges object presented.support)
    (secondCut : second ∈ cutEdges object presented.support)
    (firstDeclared : ∃ inside ∈ first, inside ∈ presented.support ∧
      inside ∈ presented.declaredSupport r)
    (secondDeclared : ∃ inside ∈ second, inside ∈ presented.support ∧
      inside ∈ presented.declaredSupport r) :
    2 ≤ (presented.car r).card :=
  (presented.two_le_card_declaredCarriers r distinct firstCut secondCut
    firstDeclared secondDeclared).trans
    (Finset.card_le_card (presented.declaredCarriers_subset_car r))

theorem declaredCarriers_subset_cutEdges (r : presented.Coordinate) :
    presented.declaredCarriers r ⊆ cutEdges object presented.support := by
  classical
  intro edge member
  exact (Finset.mem_filter.mp member).1

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
  have eventTwo : 2 ≤
      (crossingCarriers presented.support event.walk).card :=
    two_le_card_crossingCarriers presented.support event.isCycle
      insideMember insideSupport outsideMember outsideSupport
  have eventSubset : crossingCarriers presented.support event.walk ⊆
      presented.car r := by
    intro edge member
    rw [car, eventEq]
    exact Finset.mem_union_right _ member
  exact eventTwo.trans (Finset.card_le_card eventSubset)

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
    refine Finset.union_subset (presented.declaredCarriers_subset_cutEdges r) ?_
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

/-- **The ambient cycle a declared datum sits on.**

`lem:typeA-carrier-cut-parity` realizes
every surviving `u`-supported target event by *"a simple edge-rooted return or a
simple cycle"*, and `lem:typeA-carrier-cut-parity` records each of its cut crossings in the
declared support of *"a completion-port incidence, a first-entry incidence, a
connector endpoint, a boundary-degree entry, or a packed-window interface
incidence"*.  So the common currency of a declared event is one ambient simple
cycle meeting the coordinate's own declared datum, the data `def:typeA-trace-basin`
assigns family by family: the boundary vertex (`D1`), the port and channel
(`D2`), the window (`D3`), the length-two wedge (`D4`).

The cycle is an `EdgeRootedReturn.Unrestricted`, i.e. `AnyLength _ := True`
(`RootedReturn.lean`): it carries no accepted-length obligation, so
`K .selection` (`¬ HasCycleWithLength LengthOK object`) does not forbid it.  The
context-dependence of `def:typeA-trace-basin` lives in `TraceBasin.declaredAlgebra`, not
here. -/
noncomputable def meetingReturn? (object : FiniteObject.{u})
    (declared : Finset object.Vertex) :
    Option (EdgeRootedReturn.Unrestricted object) :=
  (EdgeRootedReturn.schedule object).values.find? fun return' =>
    @decide (∃ vertex ∈ declared, vertex ∈ return'.cycle.support)
      (Classical.propDecidable _)

/-- The declared event carried by a coordinate whose declared datum is
`declared`: the first ambient simple cycle in the exact rooted-return schedule
that meets that datum. -/
noncomputable def cycleEventOfDeclaredSupport (object : FiniteObject.{u})
    (declared : Finset object.Vertex) : Option (CoordinateEvent object) :=
  (meetingReturn? object declared).map fun return' =>
    { base := return'.dart.fst
      walk := return'.cycle
      isCycle := return'.cycle_isCycle }

/-- The declared event fires as soon as the ambient graph carries one simple
cycle through the declared datum.  No accepted length is asked for, so nothing
on the branch forbids it. -/
theorem exists_cycleEventOfDeclaredSupport (object : FiniteObject.{u})
    {declared : Finset object.Vertex}
    (return' : EdgeRootedReturn.Unrestricted object) {vertex : object.Vertex}
    (declaredMember : vertex ∈ declared)
    (cycleMember : vertex ∈ return'.cycle.support) :
    ∃ event : CoordinateEvent object,
      cycleEventOfDeclaredSupport object declared = some event := by
  classical
  cases found : meetingReturn? object declared with
  | none =>
      have absent := List.find?_eq_none.mp found return'
        (EdgeRootedReturn.mem_schedule return')
      simp only [decide_eq_true_eq] at absent
      exact absurd ⟨vertex, declaredMember, cycleMember⟩ absent
  | some chosen =>
      refine ⟨{ base := chosen.dart.fst
                walk := chosen.cycle
                isCycle := chosen.cycle_isCycle }, ?_⟩
      simp [cycleEventOfDeclaredSupport, found]

/-- **The declared event of a base coordinate.**

`def:typeA-trace-basin` fixes each family's declared datum:
*"a return coordinate is supported on its port and channel, a `P_13` label
coordinate on its window, an obstruction coordinate on its length-two wedge, and
a boundary-degree coordinate on the corresponding boundary vertex."*  Every
family therefore carries a declared event, in the one currency the branch
permits -- an ambient simple cycle through that datum, with no accepted-length
obligation.

* `D1` and `D3` take the first scheduled cycle meeting their declared support.
* `D2` **is** an edge-rooted return, so restoring its root edge closes its own
  simple cycle (`EdgeRootedReturn.cycle_isCycle`) and that cycle is its event.
* `D4` carries the sharper wedge-closing condition -- the cycle must use both
  edges of the indexed wedge -- under the trivial length filter, exactly as `D2`
  carries none.  A `LengthOK` filter would make
  `TraceCoordinateSystem.D4.TargetEvent` carry a `CycleCertificate object
  LengthOK`, which `K .selection` refutes outright;
  `TraceCoordinateSystem.D4.event? object support (fun _ => True)` is an ordinary
  ambient cycle and is not forbidden. -/
noncomputable def eventOfBase (object : FiniteObject.{u})
    (support : Finset object.Vertex) (_LengthOK : Nat → Prop) :
    (coordinate : Base.Coordinate object support) →
      Option (CoordinateEvent object)
  | .d1 coordinate =>
      cycleEventOfDeclaredSupport object
        (TraceCoordinateSystem.D1.declaredSupport object support coordinate)
  | .d2ReturnLength coordinate =>
      some
        { base := coordinate.dart.fst
          walk := coordinate.cycle
          isCycle := coordinate.cycle_isCycle }
  | .d3WindowLabel coordinate =>
      cycleEventOfDeclaredSupport object
        (TraceCoordinateSystem.D3.declaredSupport object support coordinate)
  | .d4RawCurvature coordinate =>
      match TraceCoordinateSystem.D4.event? object support (fun _ => True)
          coordinate with
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

/-- **`D1` fires** (`def:typeA-trace-basin`, *"a boundary-degree coordinate on the
corresponding boundary vertex"*): any ambient simple cycle through that boundary
vertex is the coordinate's declared event. -/
theorem exists_eventOfBase_d1 (object : FiniteObject.{u})
    (support : Finset object.Vertex) (LengthOK : Nat → Prop)
    (coordinate : TraceCoordinateSystem.D1.Coordinate object support)
    (return' : EdgeRootedReturn.Unrestricted object)
    (cycleMember : coordinate.1 ∈ return'.cycle.support) :
    ∃ event : CoordinateEvent object,
      eventOfBase object support LengthOK (.d1 coordinate) = some event :=
  exists_cycleEventOfDeclaredSupport object return'
    (by simp [TraceCoordinateSystem.D1.declaredSupport]) cycleMember

/-- **`D2` fires** unconditionally: the coordinate *is* the return, and its own
closed cycle is the event. -/
theorem exists_eventOfBase_d2 (object : FiniteObject.{u})
    (support : Finset object.Vertex) (LengthOK : Nat → Prop)
    (coordinate : TraceCoordinateSystem.D2.Coordinate object) :
    ∃ event : CoordinateEvent object,
      eventOfBase object support LengthOK (.d2ReturnLength coordinate) =
        some event :=
  ⟨_, rfl⟩

/-- **`D3` fires** (`def:typeA-trace-basin`, *"a `P_13` label coordinate on its window"*): any
ambient simple cycle meeting the packed window or its outside attachment is the
coordinate's declared event. -/
theorem exists_eventOfBase_d3 (object : FiniteObject.{u})
    (support : Finset object.Vertex) (LengthOK : Nat → Prop)
    (coordinate : TraceCoordinateSystem.D3.Coordinate object support)
    (return' : EdgeRootedReturn.Unrestricted object) {vertex : object.Vertex}
    (declaredMember :
      vertex ∈ TraceCoordinateSystem.D3.declaredSupport object support coordinate)
    (cycleMember : vertex ∈ return'.cycle.support) :
    ∃ event : CoordinateEvent object,
      eventOfBase object support LengthOK (.d3WindowLabel coordinate) =
        some event :=
  exists_cycleEventOfDeclaredSupport object return' declaredMember cycleMember

/-- **`D4` fires** (`def:typeA-trace-basin`, *"an obstruction coordinate on its length-two
wedge"*): any ambient simple cycle using both edges of the indexed wedge is the
coordinate's declared event. -/
theorem exists_eventOfBase_d4 (object : FiniteObject.{u})
    (support : Finset object.Vertex) (LengthOK : Nat → Prop)
    (coordinate : TraceCoordinateSystem.D4.Coordinate object support)
    (return' : EdgeRootedReturn.Unrestricted object)
    (closes : ∀ endpoint ∈ coordinate.1.2.1,
      s(coordinate.1.1, endpoint) ∈ return'.cycle.edges) :
    ∃ event : CoordinateEvent object,
      eventOfBase object support LengthOK (.d4RawCurvature coordinate) =
        some event := by
  classical
  have isSome :
      (TraceCoordinateSystem.D4.event? object support (fun _ => True)
        coordinate).isSome = true :=
    (TraceCoordinateSystem.D4.event?_isSome_iff object support (fun _ => True)
      coordinate).mpr ⟨return', trivial, closes⟩
  cases found :
      TraceCoordinateSystem.D4.event? object support (fun _ => True)
        coordinate with
  | none =>
      rw [found] at isSome
      exact absurd isSome (by simp)
  | some event =>
      refine ⟨{ base := event.certificate.vertex
                walk := event.certificate.walk
                isCycle := event.certificate.isCycle }, ?_⟩
      simp [eventOfBase, found]

/-- **Every declared family carries an event.**  `def:typeA-trace-basin`: *"The family
`\mathcal R_u(B_u)` is the complete declared coordinate family for the
`u`-supported target events used in the route-8 branch."*  Completeness at the
level of the event map: no family is silent by construction; each one fires on
the ambient datum `def:typeA-trace-basin` assigns it. -/
theorem exists_eventOfTraceCoordinate_of_families (object : FiniteObject.{u})
    (support : Finset object.Vertex) (LengthOK : Nat → Prop)
    (coordinate : Base.Coordinate object support)
    (witness :
      (∀ boundaryVertex, coordinate = .d1 boundaryVertex →
        ∃ return' : EdgeRootedReturn.Unrestricted object,
          boundaryVertex.1 ∈ return'.cycle.support) ∧
      (∀ window, coordinate = .d3WindowLabel window →
        ∃ return' : EdgeRootedReturn.Unrestricted object,
          ∃ vertex ∈
            TraceCoordinateSystem.D3.declaredSupport object support window,
            vertex ∈ return'.cycle.support) ∧
      (∀ wedge, coordinate = .d4RawCurvature wedge →
        ∃ return' : EdgeRootedReturn.Unrestricted object,
          ∀ endpoint ∈ wedge.1.2.1,
            s(wedge.1.1, endpoint) ∈ return'.cycle.edges)) :
    ∃ event : CoordinateEvent object,
      eventOfTraceCoordinate object support LengthOK (.base coordinate) =
        some event := by
  obtain ⟨d1Witness, d3Witness, d4Witness⟩ := witness
  cases coordinate with
  | d1 boundaryVertex =>
      obtain ⟨return', cycleMember⟩ := d1Witness boundaryVertex rfl
      exact exists_eventOfBase_d1 object support LengthOK boundaryVertex return'
        cycleMember
  | d2ReturnLength return' =>
      exact exists_eventOfBase_d2 object support LengthOK return'
  | d3WindowLabel window =>
      obtain ⟨return', vertex, declaredMember, cycleMember⟩ := d3Witness window rfl
      exact exists_eventOfBase_d3 object support LengthOK window return'
        declaredMember cycleMember
  | d4RawCurvature wedge =>
      obtain ⟨return', closes⟩ := d4Witness wedge rfl
      exact exists_eventOfBase_d4 object support LengthOK wedge return' closes

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
inside `D`; "thus every incidence restriction is taken inside the original
boundary-degree fibre".  The manuscript states the restriction in terms of
coordinates, not edges.  This Lean realization keeps every edge incident with a
labelled boundary vertex and keeps an internal edge only when both endpoints
decode into `retained`; that edge rule is an encoding choice made here, not a
statement of the manuscript. -/
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
(`retainedReading_boundaryDegreeProfile` composed with the canonical
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
profile.**  `def:typeA-route8-carriers`: *"every incidence restriction is taken
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

/-- **A boundary-only basin has a coordinate-independent reading.**

`lem:typeA-unified-visible-ownership`:
*"In the retained boundaried piece, coordinates can alter only an edge whose two
decoded ends are interior vertices.  There are no such decoded vertices in a
boundary-only basin.  Thus the retained piece, and therefore its response state,
is identical for every retained coordinate set."*

This is the manuscript's own discharge of the degenerate basin, and it is where
the exit-`(5)` identification does *not* apply: a boundary-only basin has no
interior entries to identify. -/
theorem retainedBasinPiece_eq_piece_of_cutBoundary (object : FiniteObject.{u})
    (basin retained : Finset object.Vertex)
    (allBoundary : basin ⊆
      Strategy.InterfaceReplacement.SupportAtom.cutBoundary object basin) :
    retainedBasinPiece object basin retained =
      Strategy.InterfaceReplacement.SupportAtom.piece object basin := by
  classical
  have graphEq :
      (SimpleGraph.comap
          (Strategy.InterfaceReplacement.SupportAtom.pieceDecode object basin)
          object.graph ⊓
        SimpleGraph.fromRel fun left right =>
          left.isLeft = true ∨ right.isLeft = true ∨
            (Strategy.InterfaceReplacement.SupportAtom.pieceDecode object basin
                left ∈ retained ∧
              Strategy.InterfaceReplacement.SupportAtom.pieceDecode object basin
                right ∈ retained)) =
        SimpleGraph.comap
          (Strategy.InterfaceReplacement.SupportAtom.pieceDecode object basin)
          object.graph := by
    apply SimpleGraph.ext
    funext left right
    apply propext
    constructor
    · exact fun adjacent => adjacent.1
    · intro adjacent
      refine ⟨adjacent, ?_⟩
      rw [SimpleGraph.fromRel_adj]
      refine ⟨adjacent.ne, ?_⟩
      rcases left with left | left
      · exact Or.inl (Or.inl rfl)
      · exfalso
        exact left.2.2 (allBoundary left.2.1)
  unfold retainedBasinPiece Strategy.InterfaceReplacement.SupportAtom.piece
  rw [graphEq]

/-- **The exit-`(5)` case split.**  Either the basin carries an interior entry
-- the non-degenerate branch, on which `def:typeA-trace-basin`'s identification
quotients live -- or it is boundary-only, and then
`retainedBasinPiece_eq_piece_of_cutBoundary` makes every reading the basin's own
piece.  Nothing is assumed: the split is the excluded middle on
`basin ⊆ cutBoundary`. -/
theorem nonempty_pieceInternal_or_cutBoundary (object : FiniteObject.{u})
    (basin : Finset object.Vertex) :
    Nonempty (Strategy.InterfaceReplacement.SupportAtom.PieceInternal object
        basin) ∨
      basin ⊆
        Strategy.InterfaceReplacement.SupportAtom.cutBoundary object basin := by
  classical
  by_cases boundaryOnly : basin ⊆
      Strategy.InterfaceReplacement.SupportAtom.cutBoundary object basin
  · exact Or.inr boundaryOnly
  · obtain ⟨vertex, inside, outsideBoundary⟩ := Finset.not_subset.mp boundaryOnly
    exact Or.inl ⟨⟨vertex, inside, outsideBoundary⟩⟩

/-- **The retained piece keeps every label-incident edge.** -/
theorem retainedBasinPiece_adj_of_label (object : FiniteObject.{u})
    (basin retained : Finset object.Vertex)
    (label : (Strategy.InterfaceReplacement.SupportAtom.boundary object
      basin).Vertex)
    (other : (Strategy.InterfaceReplacement.SupportAtom.boundary object
        basin).Vertex ⊕
      Strategy.InterfaceReplacement.SupportAtom.PieceInternal object basin)
    (adjacent : (Strategy.InterfaceReplacement.SupportAtom.piece object
      basin).graph.Adj (.inl label) other) :
    (retainedBasinPiece object basin retained).graph.Adj (.inl label)
      other := by
  refine ⟨adjacent, ?_⟩
  rw [SimpleGraph.fromRel_adj]
  exact ⟨adjacent.ne, Or.inl (Or.inl rfl)⟩

/-! ## The identification-based realization at the basin

`def:typeA-trace-basin`: a response quotient is obtained by *"identifying or
forgetting entries of the finite coordinate family"*, and a realization is *"a
boundaried response state with the same boundary degree profile"*.  Folding two
interior basin vertices is that identification: it spends a vertex, keeps every
surviving degree, and leaves the labelled boundary untouched.  Nothing here
fixes the threshold; `2 ≤ threshold` is all the arithmetic needs. -/

/-- **The identified pair of `def:typeA-trace-basin`.**  The adjacent-pair
disjunct of the nontriviality clause delivers two distinct *interior* basin
vertices: the two entries an identification merges.  Interiority is what
"preserves the full boundary degree profile" asks of the pair, and
distinctness is `SimpleGraph.Adj.ne`. -/
theorem exists_identifiedPair_of_interiorPair (object : FiniteObject.{u})
    (support basin : Finset object.Vertex) (threshold : Nat)
    (receiver load : object.Vertex)
    (changed : PresentedEntry.TraceCoordinate object support)
    (interiorPair : ∃ left ∈ PresentedEntry.traceDeclaredSupport object support
        threshold receiver load changed,
      ∃ right ∈ PresentedEntry.traceDeclaredSupport object support threshold
          receiver load changed,
        (left ∈ basin ∧
            left ∉ Strategy.InterfaceReplacement.SupportAtom.cutBoundary object
              basin) ∧
          (right ∈ basin ∧
              right ∉ Strategy.InterfaceReplacement.SupportAtom.cutBoundary object
                basin) ∧
            object.graph.Adj left right) :
    ∃ keep remove :
        (Strategy.InterfaceReplacement.SupportAtom.piece object basin).Internal,
      keep ≠ remove := by
  obtain ⟨left, _leftMember, right, _rightMember, leftInterior, rightInterior,
    adjacent⟩ := interiorPair
  exact ⟨⟨left, leftInterior⟩, ⟨right, rightInterior⟩,
    fun equal => adjacent.ne (congrArg Subtype.val equal)⟩

/-- The glued basin piece inherits the object's own minimum-degree baseline
through the owned decomposition's reconstruction isomorphism. -/
theorem le_minDegree_glue_basinPiece (object : FiniteObject.{u})
    (basin : Finset object.Vertex) (threshold : Nat)
    (connected : SupportComponents.Connected.ConnectedOn object basin)
    (proper : ∃ vertex, vertex ∉ basin)
    (baseline : MinimumDegreeAtLeast threshold object) :
    threshold ≤ (glue (Strategy.InterfaceReplacement.SupportAtom.piece object basin)
      (Strategy.InterfaceReplacement.SupportAtom.properAtom object basin connected proper).decomposition.outside).minDegree :=
  ((minimumDegreeAtLeast_isomorphismInvariant threshold).iff_of_iso
    ⟨(Strategy.InterfaceReplacement.SupportAtom.properAtom object basin connected
      proper).decomposition.reconstructionIso⟩).mpr baseline

/-- **Every interior basin vertex already carries the object's baseline inside
the piece.**  The piece owns every incidence of an interior vertex, so its piece
degree is its glued degree, and the glued basin inherits the residual's own
minimum-degree baseline. -/
theorem le_degree_basinPiece_of_baseline (object : FiniteObject.{u})
    (basin : Finset object.Vertex) (threshold : Nat)
    (connected : SupportComponents.Connected.ConnectedOn object basin)
    (proper : ∃ vertex, vertex ∉ basin)
    (baseline : MinimumDegreeAtLeast threshold object)
    (internal : (Strategy.InterfaceReplacement.SupportAtom.piece object basin).Internal) :
    threshold ≤ (Strategy.InterfaceReplacement.SupportAtom.piece object
      basin).pack.degree (.inr internal) := by
  have step :=
    (le_minDegree_glue_basinPiece object basin threshold connected proper
      baseline).trans
      ((glue (Strategy.InterfaceReplacement.SupportAtom.piece object basin)
        (Strategy.InterfaceReplacement.SupportAtom.properAtom object basin connected
          proper).decomposition.outside).minDegree_le_degree (.inr (.inl internal)))
  rwa [glue_degree_pieceInternal] at step

/-- **Both exit-`(5)` conjuncts, on one realization.**  The fold removes a
vertex (descent) and reconnects rather than deleting (baseline), so a single
realization serves both.  `baseline` is the residual's own
`inputs.current.baseline`; `2 ≤ threshold` is supplied by the registered
cubic-baseline fact.  The two origin degrees are read off that same baseline
(`le_degree_basinPiece_of_baseline`), so they are not separate inputs. -/
theorem foldRealization_baseline_and_smaller (object : FiniteObject.{u})
    (basin : Finset object.Vertex) (threshold : Nat) (two : 2 ≤ threshold)
    (connected : SupportComponents.Connected.ConnectedOn object basin)
    (proper : ∃ vertex, vertex ∉ basin)
    (keep remove : (Strategy.InterfaceReplacement.SupportAtom.piece object basin).Internal)
    (different : keep ≠ remove)
    (baseline : MinimumDegreeAtLeast threshold object)
    (noCommon : ∀ x,
      ¬ ((Strategy.InterfaceReplacement.SupportAtom.piece object basin).graph.Adj (.inr keep) x ∧
        (Strategy.InterfaceReplacement.SupportAtom.piece object basin).graph.Adj (.inr remove) x)) :
    MinimumDegreeAtLeast threshold
        (glue ((Strategy.InterfaceReplacement.SupportAtom.piece object basin).identifyInternal keep remove different)
          (Strategy.InterfaceReplacement.SupportAtom.properAtom object basin connected proper).decomposition.outside) ∧
      (glue ((Strategy.InterfaceReplacement.SupportAtom.piece object basin).identifyInternal keep remove different)
        (Strategy.InterfaceReplacement.SupportAtom.properAtom object basin connected
          proper).decomposition.outside).LexicographicallySmaller object := by
  classical
  refine ⟨le_minDegree_glue_identifyInternal _ keep remove different _ threshold
      two ⟨.inr (.inl ⟨keep, different⟩)⟩
      (le_minDegree_glue_basinPiece object basin threshold connected proper
        baseline)
      (le_degree_basinPiece_of_baseline object basin threshold connected proper
        baseline keep)
      (le_degree_basinPiece_of_baseline object basin threshold connected proper
        baseline remove)
      noCommon, ?_⟩
  refine (FiniteObject.lexicographicallySmaller_congr_right
    ⟨(Strategy.InterfaceReplacement.SupportAtom.properAtom object basin connected
      proper).decomposition.reconstructionIso⟩).mp ?_
  exact lexicographicallySmaller_glue_identifyInternal _ keep remove different _

/-- **The three conjuncts compose to `False`.**  `complete` is conjunct 3 of
`def:typeA-trace-basin` read at the fold realization, whose `profile_eq` half is
already discharged by
`boundaryDegreeProfile_identifyInternal_of_noCommonLabel`; `avoids` and
`minimal` are the two halves of the selection fact. -/
theorem foldRealization_refutes (object : FiniteObject.{u})
    (basin : Finset object.Vertex) (threshold : Nat) (two : 2 ≤ threshold)
    (LengthOK : Nat → Prop)
    (connected : SupportComponents.Connected.ConnectedOn object basin)
    (proper : ∃ vertex, vertex ∉ basin)
    (keep remove : (Strategy.InterfaceReplacement.SupportAtom.piece object basin).Internal)
    (different : keep ≠ remove)
    (baseline : MinimumDegreeAtLeast threshold object)
    (noCommon : ∀ x,
      ¬ ((Strategy.InterfaceReplacement.SupportAtom.piece object basin).graph.Adj (.inr keep) x ∧
        (Strategy.InterfaceReplacement.SupportAtom.piece object basin).graph.Adj (.inr remove) x))
    (complete : Response.TargetComplete BoundaryPiece.boundaryDegreeProfile
      (HasCycleWithLength LengthOK)
      ((Strategy.InterfaceReplacement.SupportAtom.piece object basin).identifyInternal keep remove different)
      (Strategy.InterfaceReplacement.SupportAtom.piece object basin))
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (minimal : ∀ representative : FiniteObject.{u},
      representative.LexicographicallySmaller object →
      MinimumDegreeAtLeast threshold representative →
      HasCycleWithLength LengthOK representative) :
    False := by
  classical
  obtain ⟨dBaseline, dSmaller⟩ :=
    foldRealization_baseline_and_smaller object basin threshold two connected
      proper keep remove different baseline noCommon
  have cycled := minimal _ dSmaller dBaseline
  have pieceCycled : HasCycleWithLength LengthOK
      (glue (Strategy.InterfaceReplacement.SupportAtom.piece object basin)
        (Strategy.InterfaceReplacement.SupportAtom.properAtom object basin connected
          proper).decomposition.outside) :=
    (complete.contextEquivalent _).mp cycled
  exact avoids
    (((cycleTargetInterface LengthOK).isomorphismInvariant.iff_of_iso
      ⟨(Strategy.InterfaceReplacement.SupportAtom.properAtom object basin connected
        proper).decomposition.reconstructionIso⟩).mp pieceCycled)

/-- **Both exit-`(5)` conjuncts for a contracted cubic triangle.**

`def:typeA-trace-basin` admits an identification only when it "preserves the
full boundary degree profile", so a pair whose common neighbour is a labelled
cut-boundary vertex is inadmissible; the admissible case with a common
neighbour has that neighbour *interior*, and then `keep`, `remove` and it form a
triangle of interior vertices.  Contracting the whole triangle — fold
`keep` with `remove`, then fold the common neighbour into the merged vertex —
spends two internal vertices, restores the merged degree to the baseline
(`le_minDegree_glue_triangleContraction`), and needs no repair edge: the
intermediate degree-two vertex is exactly the one the second fold removes. -/
theorem triangleContraction_baseline_and_smaller (object : FiniteObject.{u})
    (basin : Finset object.Vertex) (threshold : Nat) (three : 3 ≤ threshold)
    (connected : SupportComponents.Connected.ConnectedOn object basin)
    (proper : ∃ vertex, vertex ∉ basin)
    (keep remove common :
      (Strategy.InterfaceReplacement.SupportAtom.piece object basin).Internal)
    (keepRemove : keep ≠ remove) (commonRemove : common ≠ remove)
    (second :
      (⟨keep, keepRemove⟩ :
        ((Strategy.InterfaceReplacement.SupportAtom.piece object
          basin).identifyInternal keep remove keepRemove).Internal) ≠
        ⟨common, commonRemove⟩)
    (edgeKC : (Strategy.InterfaceReplacement.SupportAtom.piece object
      basin).graph.Adj (.inr keep) (.inr common))
    (edgeRC : (Strategy.InterfaceReplacement.SupportAtom.piece object
      basin).graph.Adj (.inr remove) (.inr common))
    (edgeKR : (Strategy.InterfaceReplacement.SupportAtom.piece object
      basin).graph.Adj (.inr keep) (.inr remove))
    (baseline : MinimumDegreeAtLeast threshold object)
    (uniqueKR : ∀ y, (Strategy.InterfaceReplacement.SupportAtom.piece object
        basin).graph.Adj (.inr keep) y →
      (Strategy.InterfaceReplacement.SupportAtom.piece object
        basin).graph.Adj (.inr remove) y → y = .inr common)
    (uniqueKC : ∀ y, (Strategy.InterfaceReplacement.SupportAtom.piece object
        basin).graph.Adj (.inr keep) y →
      (Strategy.InterfaceReplacement.SupportAtom.piece object
        basin).graph.Adj (.inr common) y → y = .inr remove)
    (uniqueRC : ∀ y, (Strategy.InterfaceReplacement.SupportAtom.piece object
        basin).graph.Adj (.inr remove) y →
      (Strategy.InterfaceReplacement.SupportAtom.piece object
        basin).graph.Adj (.inr common) y → y = .inr keep) :
    MinimumDegreeAtLeast threshold
        (glue (((Strategy.InterfaceReplacement.SupportAtom.piece object
            basin).identifyInternal keep remove keepRemove).identifyInternal
            ⟨keep, keepRemove⟩ ⟨common, commonRemove⟩ second)
          (Strategy.InterfaceReplacement.SupportAtom.properAtom object basin
            connected proper).decomposition.outside) ∧
      (glue (((Strategy.InterfaceReplacement.SupportAtom.piece object
          basin).identifyInternal keep remove keepRemove).identifyInternal
          ⟨keep, keepRemove⟩ ⟨common, commonRemove⟩ second)
        (Strategy.InterfaceReplacement.SupportAtom.properAtom object basin
          connected proper).decomposition.outside).LexicographicallySmaller
        object := by
  classical
  refine ⟨le_minDegree_glue_triangleContraction _ keep remove common keepRemove
      commonRemove second edgeKC edgeRC edgeKR _ threshold three
      (le_minDegree_glue_basinPiece object basin threshold connected proper
        baseline)
      uniqueKR uniqueKC uniqueRC, ?_⟩
  refine (FiniteObject.lexicographicallySmaller_congr_right
    ⟨(Strategy.InterfaceReplacement.SupportAtom.properAtom object basin connected
      proper).decomposition.reconstructionIso⟩).mp ?_
  exact lexicographicallySmaller_glue_identifyInternal_twice _ keep remove
    keepRemove _ _ second _

/-- **The contracted triangle is a target-complete compression of the basin**,
once the contraction is target-complete against the basin's own piece. -/
theorem compressibleSupport_of_triangleContraction (object : FiniteObject.{u})
    (basin : Finset object.Vertex) (threshold : Nat) (three : 3 ≤ threshold)
    (LengthOK : Nat → Prop)
    (connected : SupportComponents.Connected.ConnectedOn object basin)
    (proper : ∃ vertex, vertex ∉ basin)
    (keep remove common :
      (Strategy.InterfaceReplacement.SupportAtom.piece object basin).Internal)
    (keepRemove : keep ≠ remove) (commonRemove : common ≠ remove)
    (second :
      (⟨keep, keepRemove⟩ :
        ((Strategy.InterfaceReplacement.SupportAtom.piece object
          basin).identifyInternal keep remove keepRemove).Internal) ≠
        ⟨common, commonRemove⟩)
    (edgeKC : (Strategy.InterfaceReplacement.SupportAtom.piece object
      basin).graph.Adj (.inr keep) (.inr common))
    (edgeRC : (Strategy.InterfaceReplacement.SupportAtom.piece object
      basin).graph.Adj (.inr remove) (.inr common))
    (edgeKR : (Strategy.InterfaceReplacement.SupportAtom.piece object
      basin).graph.Adj (.inr keep) (.inr remove))
    (baseline : MinimumDegreeAtLeast threshold object)
    (uniqueKR : ∀ y, (Strategy.InterfaceReplacement.SupportAtom.piece object
        basin).graph.Adj (.inr keep) y →
      (Strategy.InterfaceReplacement.SupportAtom.piece object
        basin).graph.Adj (.inr remove) y → y = .inr common)
    (uniqueKC : ∀ y, (Strategy.InterfaceReplacement.SupportAtom.piece object
        basin).graph.Adj (.inr keep) y →
      (Strategy.InterfaceReplacement.SupportAtom.piece object
        basin).graph.Adj (.inr common) y → y = .inr remove)
    (uniqueRC : ∀ y, (Strategy.InterfaceReplacement.SupportAtom.piece object
        basin).graph.Adj (.inr remove) y →
      (Strategy.InterfaceReplacement.SupportAtom.piece object
        basin).graph.Adj (.inr common) y → y = .inr keep)
    (complete : Response.TargetComplete BoundaryPiece.boundaryDegreeProfile
      (HasCycleWithLength LengthOK)
      (((Strategy.InterfaceReplacement.SupportAtom.piece object
        basin).identifyInternal keep remove keepRemove).identifyInternal
        ⟨keep, keepRemove⟩ ⟨common, commonRemove⟩ second)
      (Strategy.InterfaceReplacement.SupportAtom.piece object basin)) :
    Strategy.InterfaceReplacement.CompressibleSupport
      (MinimumDegreeAtLeast threshold) (HasCycleWithLength LengthOK) object
      basin := by
  obtain ⟨dBaseline, dSmaller⟩ :=
    triangleContraction_baseline_and_smaller object basin threshold three
      connected proper keep remove common keepRemove commonRemove second edgeKC
      edgeRC edgeKR baseline uniqueKR uniqueKC uniqueRC
  exact ⟨connected, proper, _, complete.profile_eq, dBaseline, dSmaller,
    complete.contextEquivalent⟩

/-- **The fold realization is a target-complete compression of the basin.**

This is the exit-`(5)` datum of `def:typeA-saturated-exits` in the shape
`cor:uncompressible` reads it: `lem:replacement`'s proper-support compression,
whose smaller boundaried piece is the identification.  Both conjuncts of
`def:target-complete-compression` come from
`foldRealization_baseline_and_smaller`, and the two response clauses are the
two fields of conjunct 3. -/
theorem compressibleSupport_of_foldRealization (object : FiniteObject.{u})
    (basin : Finset object.Vertex) (threshold : Nat) (two : 2 ≤ threshold)
    (LengthOK : Nat → Prop)
    (connected : SupportComponents.Connected.ConnectedOn object basin)
    (proper : ∃ vertex, vertex ∉ basin)
    (keep remove : (Strategy.InterfaceReplacement.SupportAtom.piece object basin).Internal)
    (different : keep ≠ remove)
    (baseline : MinimumDegreeAtLeast threshold object)
    (noCommon : ∀ x,
      ¬ ((Strategy.InterfaceReplacement.SupportAtom.piece object basin).graph.Adj (.inr keep) x ∧
        (Strategy.InterfaceReplacement.SupportAtom.piece object basin).graph.Adj (.inr remove) x))
    (complete : Response.TargetComplete BoundaryPiece.boundaryDegreeProfile
      (HasCycleWithLength LengthOK)
      ((Strategy.InterfaceReplacement.SupportAtom.piece object basin).identifyInternal keep remove different)
      (Strategy.InterfaceReplacement.SupportAtom.piece object basin)) :
    Strategy.InterfaceReplacement.CompressibleSupport
      (MinimumDegreeAtLeast threshold) (HasCycleWithLength LengthOK) object
      basin := by
  obtain ⟨dBaseline, dSmaller⟩ :=
    foldRealization_baseline_and_smaller object basin threshold two connected
      proper keep remove different baseline noCommon
  exact ⟨connected, proper,
    (Strategy.InterfaceReplacement.SupportAtom.piece object basin).identifyInternal
      keep remove different,
    complete.profile_eq, dBaseline, dSmaller, complete.contextEquivalent⟩

/-- **`cor:uncompressible` refutes target-completeness of the identification.**
The standing uncompressibility fact `K .uncompressible` forbids every proper-support
compression, hence every target-complete identification of the basin's own
piece. -/
theorem not_targetComplete_foldRealization (object : FiniteObject.{u})
    (basin : Finset object.Vertex) (threshold : Nat) (two : 2 ≤ threshold)
    (LengthOK : Nat → Prop)
    (connected : SupportComponents.Connected.ConnectedOn object basin)
    (proper : ∃ vertex, vertex ∉ basin)
    (keep remove : (Strategy.InterfaceReplacement.SupportAtom.piece object basin).Internal)
    (different : keep ≠ remove)
    (baseline : MinimumDegreeAtLeast threshold object)
    (noCommon : ∀ x,
      ¬ ((Strategy.InterfaceReplacement.SupportAtom.piece object basin).graph.Adj (.inr keep) x ∧
        (Strategy.InterfaceReplacement.SupportAtom.piece object basin).graph.Adj (.inr remove) x))
    (uncompressible : ∀ candidate : Finset object.Vertex,
      ¬ Strategy.InterfaceReplacement.CompressibleSupport
          (MinimumDegreeAtLeast threshold) (HasCycleWithLength LengthOK) object
          candidate) :
    ¬ Response.TargetComplete BoundaryPiece.boundaryDegreeProfile
      (HasCycleWithLength LengthOK)
      ((Strategy.InterfaceReplacement.SupportAtom.piece object basin).identifyInternal keep remove different)
      (Strategy.InterfaceReplacement.SupportAtom.piece object basin) :=
  fun complete => uncompressible basin
    (compressibleSupport_of_foldRealization object basin threshold two LengthOK
      connected proper keep remove different baseline noCommon complete)

/-- **The retained reading is target-monotone toward the basin piece**
(`lem:typeA-internal-quotient-mixed`'s one-sidedness, realized): an accepted
cycle of a gluing of the retained reading yields one of the same gluing of the
basin's full piece.  `glue_swap_target_iff` moves the certificate from the
canonical representative to the retained piece — the basin piece with only the
retained-owned internal edges — and `glueGraph_mono` with the identity
embedding transports it to the unrestricted piece. -/
theorem hasCycleWithLength_glue_of_retainedReading (object : FiniteObject.{u})
    (support basin : Finset object.Vertex) (threshold : Nat)
    (LengthOK : Nat → Prop)
    (retained : Finset (TraceCoordinateSystem.Base.Coordinate object support))
    (outside : OutsideContext
      (Strategy.InterfaceReplacement.SupportAtom.boundary object basin))
    (accepted : HasCycleWithLength LengthOK
      (glue (retainedReading object support basin threshold LengthOK retained)
        outside)) :
    HasCycleWithLength LengthOK
      (glue (Strategy.InterfaceReplacement.SupportAtom.piece object basin)
        outside) := by
  classical
  have swapped : HasCycleWithLength LengthOK
      (glue (retainedBasinPiece object basin
        (retainedVertices object support retained)) outside) :=
    (CanonicalPiece.glue_swap_target_iff
      (minimumDegreeAtLeast_isomorphismInvariant threshold)
      (cycleTargetInterface LengthOK).isomorphismInvariant
      (retainedBasinPiece object basin
        (retainedVertices object support retained)) outside).mp accepted
  obtain ⟨certificate⟩ := swapped
  have le : (retainedBasinPiece object basin
        (retainedVertices object support retained)).graph ≤
      (Strategy.InterfaceReplacement.SupportAtom.piece object basin).graph :=
    inf_le_left
  have glueLe : (glue (retainedBasinPiece object basin
        (retainedVertices object support retained)) outside).graph ≤
      (glue (Strategy.InterfaceReplacement.SupportAtom.piece object basin)
        outside).graph :=
    glueGraph_mono
      (piece := Strategy.InterfaceReplacement.SupportAtom.piece object basin)
      outside _
      (retainedBasinPiece object basin
        (retainedVertices object support retained)).decideAdj le
  refine ⟨CycleCertificate.mapHom ?_ ?_ certificate⟩
  · exact SimpleGraph.Hom.ofLE glueLe
  · intro a b equal
    exact equal

/-! ## (A) The realization map of `def:typeA-trace-basin`

`def:typeA-trace-basin`: *"A realization of such a quotient is a
boundaried response state with the same boundary degree profile whose image
under the quotient map is the given quotient."*

`PresentedEntry.state` runs from a set of declared coordinates to a boundaried
piece and `PresentedEntry.value` reads a coordinate off the ambient object; the
direction this sentence needs is the missing one, from a boundaried state back
to the declared entries it carries.  `ResponseQuotientMap` supplies it: a
response quotient of `\rho_u(B_u)` presents its realization as the image of the
basin's own state under a label-fixing surjection whose incidences are exactly
the images of the basin's incidences, and `declaredEntry` then reads a declared
coordinate of `\mathcal R_u(B_u)` off that state as the image of the
coordinate's declared support.  The basin's own reading is `identityQuotient`,
so `declaredEntry` restricts along the quotient map exactly as
`\operatorname{res}_{X,S}` does in the manuscript. -/

/-- **The quotient map of a response quotient at the basin's interface.**  It
identifies or forgets entries of `\mathcal R_u(B_u)` -- hence the surjection --
and it moves no boundary label, so the labelled interface of the realization is
the basin's own. -/
structure ResponseQuotientMap (object : FiniteObject.{u})
    (basin : Finset object.Vertex)
    (realization : BoundaryPiece
      (Strategy.InterfaceReplacement.SupportAtom.boundary object basin)) where
  /-- The map carrying `\rho_u(B_u)` onto the realization. -/
  toFun :
    ((Strategy.InterfaceReplacement.SupportAtom.boundary object basin).Vertex ⊕
        (Strategy.InterfaceReplacement.SupportAtom.piece object basin).Internal) →
      ((Strategy.InterfaceReplacement.SupportAtom.boundary object basin).Vertex ⊕
        realization.Internal)
  /-- No boundary label is renamed. -/
  labels : ∀ label, toFun (.inl label) = .inl label
  /-- No interior entry is pushed onto the labelled interface: the quotient
  identifies interior entries with interior entries, which is what *"preserves
  the full boundary degree profile"* asks of the quotient map. -/
  interior : ∀ internal, ∃ image, toFun (.inr internal) = .inr image
  /-- The realization is the image: every entry of it is hit. -/
  surjective : Function.Surjective toFun
  /-- A surviving incidence of `\rho_u(B_u)` is an incidence of the image. -/
  forward : ∀ left right,
    (Strategy.InterfaceReplacement.SupportAtom.piece object basin).graph.Adj left
        right →
      toFun left ≠ toFun right →
        realization.graph.Adj (toFun left) (toFun right)
  /-- The image invents no incidence. -/
  image : ∀ left right, realization.graph.Adj left right →
    ∃ source target, toFun source = left ∧ toFun target = right ∧
      (Strategy.InterfaceReplacement.SupportAtom.piece object basin).graph.Adj
        source target

/-- **The declared coordinate reading of a boundaried response state.**  The
entry of `coordinate` carried by the realization is the image of the
coordinate's declared support: the entries of `\mathcal R_u(B_u)` the quotient
map leaves standing, at the names the quotient gives them. -/
noncomputable def declaredEntry (object : FiniteObject.{u})
    (support basin : Finset object.Vertex) (threshold : Nat)
    (receiver load : object.Vertex)
    {realization : BoundaryPiece
      (Strategy.InterfaceReplacement.SupportAtom.boundary object basin)}
    (quotient : ResponseQuotientMap object basin realization)
    (coordinate : TraceCoordinate object support) :
    Set ((Strategy.InterfaceReplacement.SupportAtom.boundary object basin).Vertex ⊕
      realization.Internal) :=
  quotient.toFun ''
    {vertex |
      Strategy.InterfaceReplacement.SupportAtom.pieceDecode object basin vertex ∈
        traceDeclaredSupport object support threshold receiver load coordinate}

/-- The basin's own response state, read by the identity quotient. -/
def identityQuotient (object : FiniteObject.{u})
    (basin : Finset object.Vertex) :
    ResponseQuotientMap object basin
      (Strategy.InterfaceReplacement.SupportAtom.piece object basin) where
  toFun := id
  labels := fun _ => rfl
  interior := fun internal => ⟨internal, rfl⟩
  surjective := Function.surjective_id
  forward := fun _ _ adjacent _ => adjacent
  image := fun left right adjacent => ⟨left, right, rfl, rfl, adjacent⟩

/-- The basin's own reading of a declared coordinate is the coordinate's own
declared support, carried at the basin's interface. -/
theorem declaredEntry_identityQuotient (object : FiniteObject.{u})
    (support basin : Finset object.Vertex) (threshold : Nat)
    (receiver load : object.Vertex)
    (coordinate : TraceCoordinate object support) :
    declaredEntry object support basin threshold receiver load
        (identityQuotient object basin) coordinate =
      {vertex |
        Strategy.InterfaceReplacement.SupportAtom.pieceDecode object basin vertex ∈
          traceDeclaredSupport object support threshold receiver load
            coordinate} := by
  unfold declaredEntry identityQuotient
  exact Set.image_id _

/-- Folding is undone by decoding: every surviving folded entry is the
canonical representative of its own decode. -/
theorem foldRetain_foldDecode {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) (remove : piece.Internal)
    (vertex : boundary.Vertex ⊕ piece.InternalExcept remove) :
    piece.foldRetain remove (piece.foldDecode remove vertex)
        (piece.foldDecode_ne_remove remove vertex) = vertex := by
  cases vertex with
  | inl label => rfl
  | inr internal => rfl

open scoped Classical in
/-- The carrier map of an interior identification: the removed entry is sent to
the surviving one, every other entry to its own representative. -/
noncomputable def foldMap {boundary : Boundary.{u}} (piece : BoundaryPiece boundary)
    (keep remove : piece.Internal) (different : keep ≠ remove) :
    (boundary.Vertex ⊕ piece.Internal) →
      (boundary.Vertex ⊕ (piece.identifyInternal keep remove different).Internal) :=
  fun vertex =>
    if collapsed : vertex = .inr remove then piece.foldedKeep keep remove different
    else piece.foldRetain remove vertex collapsed

theorem foldMap_of_ne {boundary : Boundary.{u}} (piece : BoundaryPiece boundary)
    (keep remove : piece.Internal) (different : keep ≠ remove)
    {vertex : boundary.Vertex ⊕ piece.Internal} (survives : vertex ≠ .inr remove) :
    foldMap piece keep remove different vertex =
      piece.foldRetain remove vertex survives := by
  rw [foldMap, dif_neg survives]

theorem foldMap_remove {boundary : Boundary.{u}} (piece : BoundaryPiece boundary)
    (keep remove : piece.Internal) (different : keep ≠ remove) :
    foldMap piece keep remove different (.inr remove) =
      piece.foldedKeep keep remove different := by
  rw [foldMap, dif_pos rfl]

theorem foldMap_foldDecode {boundary : Boundary.{u}} (piece : BoundaryPiece boundary)
    (keep remove : piece.Internal) (different : keep ≠ remove)
    (vertex : boundary.Vertex ⊕
      (piece.identifyInternal keep remove different).Internal) :
    foldMap piece keep remove different (piece.foldDecode remove vertex) = vertex := by
  rw [foldMap_of_ne piece keep remove different
    (piece.foldDecode_ne_remove remove vertex)]
  exact foldRetain_foldDecode piece remove vertex

theorem foldMap_remove_eq {boundary : Boundary.{u}} (piece : BoundaryPiece boundary)
    (keep remove : piece.Internal) (different : keep ≠ remove)
    {vertex : boundary.Vertex ⊕
      (piece.identifyInternal keep remove different).Internal}
    (decoded : piece.foldDecode remove vertex = .inr keep) :
    foldMap piece keep remove different (.inr remove) = vertex := by
  rw [foldMap_remove piece keep remove different]
  exact piece.foldDecode_injective remove
    ((piece.foldDecode_foldedKeep keep remove different).trans decoded.symm)

/-- The identification map is injective away from the pair it identifies. -/
theorem foldMap_eq_cases {boundary : Boundary.{u}} (piece : BoundaryPiece boundary)
    (keep remove : piece.Internal) (different : keep ≠ remove)
    {left right : boundary.Vertex ⊕ piece.Internal}
    (equal : foldMap piece keep remove different left =
      foldMap piece keep remove different right) :
    left = right ∨
      (left = .inr remove ∧ right = .inr keep) ∨
      (left = .inr keep ∧ right = .inr remove) := by
  by_cases leftCollapsed : left = .inr remove
  · by_cases rightCollapsed : right = .inr remove
    · exact Or.inl (leftCollapsed.trans rightCollapsed.symm)
    · subst leftCollapsed
      rw [foldMap_remove, foldMap_of_ne _ _ _ _ rightCollapsed] at equal
      have decoded := congrArg (piece.foldDecode remove) equal
      rw [BoundaryPiece.foldDecode_foldedKeep, BoundaryPiece.foldDecode_foldRetain]
        at decoded
      exact Or.inr (Or.inl ⟨rfl, decoded.symm⟩)
  · by_cases rightCollapsed : right = .inr remove
    · subst rightCollapsed
      rw [foldMap_remove, foldMap_of_ne _ _ _ _ leftCollapsed] at equal
      have decoded := congrArg (piece.foldDecode remove) equal
      rw [BoundaryPiece.foldDecode_foldedKeep, BoundaryPiece.foldDecode_foldRetain]
        at decoded
      exact Or.inr (Or.inr ⟨decoded, rfl⟩)
    · rw [foldMap_of_ne _ _ _ _ leftCollapsed, foldMap_of_ne _ _ _ _ rightCollapsed]
        at equal
      have decoded := congrArg (piece.foldDecode remove) equal
      rw [BoundaryPiece.foldDecode_foldRetain, BoundaryPiece.foldDecode_foldRetain]
        at decoded
      exact Or.inl decoded

/-- **An interior identification is a response quotient map.**  It merges the
two identified entries, renames no label, and its incidences are exactly the
images of the basin's own -- which is `BoundaryPiece.identifyInternal_adj` read
in both directions. -/
noncomputable def foldQuotient (object : FiniteObject.{u})
    (basin : Finset object.Vertex)
    (keep remove :
      (Strategy.InterfaceReplacement.SupportAtom.piece object basin).Internal)
    (different : keep ≠ remove) :
    ResponseQuotientMap object basin
      ((Strategy.InterfaceReplacement.SupportAtom.piece object
        basin).identifyInternal keep remove different) where
  toFun :=
    foldMap (Strategy.InterfaceReplacement.SupportAtom.piece object basin) keep
      remove different
  labels := fun label => by
    rw [foldMap_of_ne _ _ _ _ (Sum.inl_ne_inr)]
    rfl
  interior := by
    intro internal
    by_cases collapsed :
        (Sum.inr internal :
          (Strategy.InterfaceReplacement.SupportAtom.boundary object basin).Vertex ⊕
            (Strategy.InterfaceReplacement.SupportAtom.piece object basin).Internal) =
          .inr remove
    · rw [collapsed, foldMap_remove]
      exact ⟨⟨keep, different⟩, rfl⟩
    · rw [foldMap_of_ne _ _ _ _ collapsed]
      exact ⟨⟨internal, fun same => collapsed (congrArg Sum.inr same)⟩, rfl⟩
  surjective := fun target =>
    ⟨(Strategy.InterfaceReplacement.SupportAtom.piece object basin).foldDecode
      remove target,
      foldMap_foldDecode _ keep remove different target⟩
  forward := by
    intro left right adjacent distinct
    rw [BoundaryPiece.identifyInternal_adj]
    refine ⟨distinct, ?_⟩
    by_cases leftCollapsed : left = .inr remove
    · subst leftCollapsed
      have rightSurvives : right ≠ .inr remove := fun same => adjacent.ne same.symm
      rw [foldMap_remove, foldMap_of_ne _ _ _ _ rightSurvives,
        BoundaryPiece.foldDecode_foldedKeep, BoundaryPiece.foldDecode_foldRetain]
      exact Or.inr (Or.inl ⟨rfl, adjacent⟩)
    · by_cases rightCollapsed : right = .inr remove
      · subst rightCollapsed
        rw [foldMap_remove, foldMap_of_ne _ _ _ _ leftCollapsed,
          BoundaryPiece.foldDecode_foldedKeep, BoundaryPiece.foldDecode_foldRetain]
        exact Or.inr (Or.inr ⟨rfl, adjacent.symm⟩)
      · rw [foldMap_of_ne _ _ _ _ leftCollapsed, foldMap_of_ne _ _ _ _ rightCollapsed,
          BoundaryPiece.foldDecode_foldRetain, BoundaryPiece.foldDecode_foldRetain]
        exact Or.inl adjacent
  image := by
    intro left right adjacent
    rw [BoundaryPiece.identifyInternal_adj] at adjacent
    obtain ⟨_distinct, source⟩ := adjacent
    rcases source with old | ⟨decodedLeft, moved⟩ | ⟨decodedRight, moved⟩
    · exact ⟨_, _, foldMap_foldDecode _ keep remove different left,
        foldMap_foldDecode _ keep remove different right, old⟩
    · exact ⟨.inr remove, _,
        foldMap_remove_eq _ keep remove different decodedLeft,
        foldMap_foldDecode _ keep remove different right, moved⟩
    · exact ⟨_, .inr remove,
        foldMap_foldDecode _ keep remove different left,
        foldMap_remove_eq _ keep remove different decodedRight,
        moved.symm⟩

end PresentedEntry

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

/-- **Every boundary incidence of `X` is recorded by a declared coordinate.**

`def:typeA-route8-carriers`: *"boundary
incidences are not extra data attached to `B_u`; they are the `\partial_E X`
labels already recorded by the declared coordinate signature"*, and
`lem:typeA-carrier-cut-parity` lists *"a boundary-degree entry"* among
the recording kinds.  In this coordinate system that entry is the `D1` family:
`TraceCoordinateSystem.D1.Coordinate` is literally a labelled vertex of the
support's cut boundary and its declared support is that vertex alone
(`def:typeA-trace-basin`, *"a boundary-degree coordinate on the corresponding boundary
vertex"*).  So the inside endpoint of every cut incidence carries a coordinate
whose declared carriers contain that incidence -- no coordinate family needs
widening. -/
theorem exists_declaredCarrier_of_mem_cutEdges (object : FiniteObject.{u})
    (support basin : Finset object.Vertex) (threshold : Nat)
    (LengthOK : Nat → Prop) (receiver load : object.Vertex)
    {edge : Sym2 object.Vertex} (member : edge ∈ cutEdges object support) :
    ∃ coordinate : TraceCoordinate object support,
      edge ∈ (ofTraceBasin object support basin threshold LengthOK receiver
        load).declaredCarriers coordinate := by
  classical
  obtain ⟨edgeMem, inside, insideEdge, outside, outsideEdge, insideSupport,
    outsideSupport⟩ := mem_cutEdges.mp member
  obtain ⟨other, shape⟩ := Sym2.mem_iff_exists.mp insideEdge
  have adjacent : object.graph.Adj inside other := by
    have edgeAdj := SimpleGraph.mem_edgeFinset.mp edgeMem
    rw [shape] at edgeAdj
    exact edgeAdj
  have otherOutside : other ∉ support := by
    have outsideMem : outside ∈ s(inside, other) := shape ▸ outsideEdge
    rcases Sym2.mem_iff.mp outsideMem with rfl | rfl
    · exact absurd insideSupport outsideSupport
    · exact outsideSupport
  have boundaryMem : inside ∈
      Strategy.InterfaceReplacement.SupportAtom.cutBoundary object support :=
    (Strategy.InterfaceReplacement.SupportAtom.mem_cutBoundary_iff object support
      inside).2 ⟨insideSupport, other, adjacent, otherOutside⟩
  refine ⟨.base (.d1 ⟨inside, boundaryMem⟩), ?_⟩
  rw [declaredCarriers, Finset.mem_filter]
  refine ⟨member, inside, insideEdge, insideSupport, ?_⟩
  show inside ∈ TraceCoordinateSystem.D1.declaredSupport object support
    ⟨inside, boundaryMem⟩
  rw [TraceCoordinateSystem.D1.declaredSupport]
  exact Finset.mem_singleton_self _

/-- **A return coordinate's declared support is its own cycle.**

`def:typeA-trace-basin`: *"a return coordinate is supported on its
port and channel"*, and `TraceCoordinateSystem.D2.declaredSupport` is literally
the return path's ambient support.  Restoring the root edge adds no new vertex,
so every vertex the return's cycle visits is declared by the coordinate. -/
theorem mem_d2DeclaredSupport_of_mem_cycle_support {object : FiniteObject.{u}}
    (return' : EdgeRootedReturn.Unrestricted object) {vertex : object.Vertex}
    (member : vertex ∈ return'.cycle.support) :
    vertex ∈ TraceCoordinateSystem.D2.declaredSupport object return' := by
  classical
  rw [TraceCoordinateSystem.D2.declaredSupport, List.mem_toFinset]
  rw [EdgeRootedReturn.cycle, SimpleGraph.Walk.support_cons, List.mem_cons]
    at member
  rcases member with rfl | tail
  · exact return'.ambientPath.end_mem_support
  · exact tail

/-- **The cut-parity route fires.**

`lem:typeA-carrier-cut-parity`: *"If a
surviving `u`-supported target event is realized by a simple edge-rooted return
or a simple cycle which uses an internal edge of `B_u` and also uses an edge
outside `X` ..."*.  A `D2` coordinate is that return, and `eventOfBase` carries
its own closed cycle as the declared event, so the hypothesis of
`PresentedEntry.Crossing` is satisfiable: this theorem exhibits the witness, and
`two_le_card_car` applies to it. -/
theorem crossing_d2ReturnLength (object : FiniteObject.{u})
    (support basin : Finset object.Vertex) (threshold : Nat)
    (LengthOK : Nat → Prop) (receiver load : object.Vertex)
    (return' : EdgeRootedReturn.Unrestricted object)
    {insideVertex outsideVertex : object.Vertex}
    (insideMember : insideVertex ∈ return'.cycle.support)
    (insideSupport : insideVertex ∈ support)
    (outsideMember : outsideVertex ∈ return'.cycle.support)
    (outsideSupport : outsideVertex ∉ support) :
    (ofTraceBasin object support basin threshold LengthOK receiver
      load).Crossing (.base (.d2ReturnLength return')) :=
  ⟨{ base := return'.dart.fst
     walk := return'.cycle
     isCycle := return'.cycle_isCycle },
    rfl, ⟨insideVertex, insideMember, insideSupport⟩,
    outsideVertex, outsideMember, outsideSupport⟩

/-- **And it carries content**: the mixed return records at least two distinct
carriers, which is `lem:typeA-carrier-cut-parity`'s conclusion
(`lem:typeA-carrier-cut-parity`, *"its declared support contains at least two distinct boundary
incidences"*) read at the coordinate. -/
theorem two_le_card_car_d2ReturnLength (object : FiniteObject.{u})
    (support basin : Finset object.Vertex) (threshold : Nat)
    (LengthOK : Nat → Prop) (receiver load : object.Vertex)
    (return' : EdgeRootedReturn.Unrestricted object)
    {insideVertex outsideVertex : object.Vertex}
    (insideMember : insideVertex ∈ return'.cycle.support)
    (insideSupport : insideVertex ∈ support)
    (outsideMember : outsideVertex ∈ return'.cycle.support)
    (outsideSupport : outsideVertex ∉ support) :
    2 ≤ ((ofTraceBasin object support basin threshold LengthOK receiver
      load).car (.base (.d2ReturnLength return'))).card :=
  (ofTraceBasin object support basin threshold LengthOK receiver
    load).two_le_card_car
    (crossing_d2ReturnLength object support basin threshold LengthOK receiver
      load return' insideMember insideSupport outsideMember outsideSupport)

/-- **`lem:typeA-carrier-cut-parity` at a return coordinate, with no event and
no gluing.**

`lem:typeA-internal-quotient-mixed`: the surviving `u`-supported
event is *"a simple edge-rooted return or a simple cycle, WHOSE DECLARED SUPPORT
contains an internal edge of `B_u`, and which uses an edge outside `X`"*.  A
`D2` coordinate **is** such a return, and its declared support is its own path,
so the attribution is definitional rather than a transport.

Cut parity is then applied to the return's own ambient cycle: it meets `X` and
leaves `X`, so it crosses `\partial_E X` at two distinct incidences, and both are
declared by this very coordinate.  Nothing is read off any cycle in a glued
object, and `K .selection` does not forbid the return -- an
`EdgeRootedReturn.Unrestricted` carries no accepted-length obligation, so it is
not a `CycleCertificate`. -/
theorem two_le_alpha_of_mixed_return (object : FiniteObject.{u})
    (support basin : Finset object.Vertex) (threshold : Nat)
    (LengthOK : Nat → Prop) (receiver load : object.Vertex)
    (return' : EdgeRootedReturn.Unrestricted object)
    (coreRetained :
      (TraceCoordinate.base (.d2ReturnLength return') :
        TraceCoordinate object support) ∈
        ((ofTraceBasin object support basin threshold LengthOK receiver
          load).toEntry (HasCycleWithLength LengthOK)).retained
          (((ofTraceBasin object support basin threshold LengthOK receiver
            load).toEntry (HasCycleWithLength LengthOK)).essentialCore))
    {insideVertex outsideVertex : object.Vertex}
    (insideMember : insideVertex ∈ return'.cycle.support)
    (insideSupport : insideVertex ∈ support)
    (outsideMember : outsideVertex ∈ return'.cycle.support)
    (outsideSupport : outsideVertex ∉ support) :
    2 ≤ ((ofTraceBasin object support basin threshold LengthOK receiver
      load).toEntry (HasCycleWithLength LengthOK)).alpha := by
  classical
  set presented := ofTraceBasin object support basin threshold LengthOK receiver
    load with presentedDef
  set coordinate : TraceCoordinate object support :=
    .base (.d2ReturnLength return') with coordinateDef
  have parity : 2 ≤ (crossingCarriers support return'.cycle).card :=
    two_le_card_crossingCarriers support return'.cycle_isCycle insideMember
      insideSupport outsideMember outsideSupport
  obtain ⟨first, firstMem, second, secondMem, distinct⟩ :=
    Finset.one_lt_card.mp parity
  have declared : ∀ edge ∈ crossingCarriers support return'.cycle,
      edge ∈ cutEdges object support ∧
        ∃ inside ∈ edge, inside ∈ presented.support ∧
          inside ∈ presented.declaredSupport coordinate := by
    intro edge edgeMem
    refine ⟨crossingCarriers_subset_cutEdges return'.cycle edgeMem, ?_⟩
    obtain ⟨inside, insideEdge, insideInSupport, insideWalk⟩ :=
      exists_inside_mem_support_of_mem_crossingCarriers edgeMem
    exact ⟨inside, insideEdge, insideInSupport,
      mem_d2DeclaredSupport_of_mem_cycle_support return' insideWalk⟩
  obtain ⟨firstCut, firstDeclared⟩ := declared first firstMem
  obtain ⟨secondCut, secondDeclared⟩ := declared second secondMem
  exact Entry.two_le_alpha_of_two_le_card_car _ coreRetained
    (presented.two_le_card_car_of_two_incidences coordinate distinct firstCut
      secondCut firstDeclared secondDeclared)

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

namespace TraceBasin

/-- **The declared `u`-supported target algebra**, as an interface-aware target.

`def:typeA-trace-basin`: *"The
family `\mathcal R_u(B_u)` is THE COMPLETE DECLARED COORDINATE FAMILY for the
`u`-supported target events used in the route-8 branch: once the boundary degree
profile and all entries of `\mathcal R_u(B_u)` are fixed, every compatible
outside context has the same truth value for each such declared event.
Response-support quotients below are tested only against this declared
`u`-supported target algebra."*

So the algebra ranges over the **whole** declared family, not one clause of it:
it holds at a boundaried state, seen through a compatible outside context, when
*some* declared `u`-supported coordinate -- `D1` boundary-degree entry, `D2`
return, `D3` packed-window label, or `D4` raw obstruction -- carries an event
that is mixed for `X` (`lem:typeA-internal-quotient-mixed`: *"uses an internal edge of `B_u` ... and an
edge outside `X`"*), is retained by the canonical core (`lem:typeA-internal-quotient-mixed`: *"the event
survives in `\rho_u(B_u)|_{\mathcal C}`"*), and is *visible* against the
context: the outside context closes an accepted cycle through one of the
boundary labels the coordinate's ambient datum carries.

That last clause is where the context-dependence of `def:typeA-trace-basin` lives; the ambient
datum itself, supplied by `PresentedEntry.eventOfBase`, exists in the
counterexample and carries no accepted length.  No quotient map is needed: the
labels of `\partial B_u` carry their own ambient names, so the algebra locates a
declared coordinate at an arbitrary realization using only the data an
`InterfaceTarget` is given. -/
noncomputable def declaredAlgebra (object : FiniteObject.{u})
    (support basin : Finset object.Vertex) (threshold : Nat)
    (LengthOK : Nat → Prop) (receiver load : object.Vertex) :
    Response.InterfaceTarget
      (Strategy.InterfaceReplacement.SupportAtom.boundary object basin) :=
  fun piece outside =>
    ∃ coordinate : PresentedEntry.TraceCoordinate object support,
      coordinate ∈
        ((PresentedEntry.ofTraceBasin object support basin threshold LengthOK
          receiver load).toEntry (HasCycleWithLength LengthOK)).retained
          (((PresentedEntry.ofTraceBasin object support basin threshold LengthOK
            receiver load).toEntry
              (HasCycleWithLength LengthOK)).essentialCore) ∧
        ∃ event : CoordinateEvent object,
          PresentedEntry.eventOfTraceCoordinate object support LengthOK
              coordinate = some event ∧
            (∃ inside ∈ event.walk.support, inside ∈ support) ∧
              (∃ outsideVertex ∈ event.walk.support,
                outsideVertex ∉ support) ∧
                ∃ certificate : CycleCertificate (glue piece outside) LengthOK,
                  ∃ label :
                      (Strategy.InterfaceReplacement.SupportAtom.boundary object
                        basin).Vertex,
                    label.1 ∈ event.walk.support ∧
                      Sum.inl label ∈ certificate.walk.support

/-- **(B') `lem:typeA-internal-quotient-mixed`, as a theorem**
(`lem:typeA-internal-quotient-mixed`).

`lem:typeA-internal-quotient-mixed`: *"The two realizations have the same image in
`\rho_{\mathcal C}^\circ`, so a distinguishing event must use at least one
coordinate forgotten by `\rho_u(B_u)|_{\mathcal C}\to\rho_{\mathcal C}^\circ`."*

Once quotients are tested against the declared algebra, as `def:typeA-trace-basin` directs,
the attribution is immediate: a state at which the algebra holds exhibits the
declared coordinate itself, in whichever of the four families it lies.  A bare
`HasCycleWithLength` target cannot do this: an accepted cycle of a glued
realization has no reason to be any declared coordinate's event. -/
theorem distinguishingEventCrosses {object : FiniteObject.{u}}
    {support basin : Finset object.Vertex} {threshold : Nat}
    {LengthOK : Nat → Prop} {receiver load : object.Vertex}
    {left : BoundaryPiece
      (Strategy.InterfaceReplacement.SupportAtom.boundary object basin)}
    {outside : OutsideContext
      (Strategy.InterfaceReplacement.SupportAtom.boundary object basin)}
    (holds : declaredAlgebra object support basin threshold LengthOK receiver
      load left outside) :
    ∃ coordinate : PresentedEntry.TraceCoordinate object support,
      coordinate ∈
        ((PresentedEntry.ofTraceBasin object support basin threshold LengthOK
          receiver load).toEntry (HasCycleWithLength LengthOK)).retained
          (((PresentedEntry.ofTraceBasin object support basin threshold LengthOK
            receiver load).toEntry
              (HasCycleWithLength LengthOK)).essentialCore) ∧
        (PresentedEntry.ofTraceBasin object support basin threshold LengthOK
          receiver load).Crossing coordinate := by
  obtain ⟨coordinate, coreRetained, event, eventEq, insideWitness,
    outsideWitness, _visible⟩ := holds
  exact ⟨coordinate, coreRetained, event, eventEq, insideWitness,
    outsideWitness⟩

/-- **`lem:typeA-one-terminal-collapse`, step 3** : *"We claim
that `\rho_u(B_u)|_{\mathcal C}\to\rho_{\mathcal C}^\circ` is target-complete.
Suppose not.  By `lem:typeA-internal-quotient-mixed`, there is a surviving
`u`-supported target event ... which uses an internal edge of `B_u` and an edge
outside `X`.  Hence `lem:typeA-carrier-cut-parity` applies and forces its
declared support to contain at least two distinct boundary incidences from
`\mathcal C`, contradicting `|\mathcal C|\le1`.  Thus the quotient is
target-complete."*

Discharged over the complete declared family: the attribution is
`distinguishingEventCrosses`, the cut parity is
`PresentedEntry.two_le_card_car` (`lem:typeA-carrier-cut-parity` at a presented
entry, applicable to every family because every declared event is a simple
ambient cycle), and the only hypothesis is `alphaSmall`, which the three route-8
rows have in scope.  It is indifferent to how strong target-completeness is
taken to be, because it refutes the *failure* side. -/
theorem allQuotientRealizations_declaredEquivalent_of_alpha_le_one
    {object : FiniteObject.{u}} {support basin : Finset object.Vertex}
    {threshold : Nat} {LengthOK : Nat → Prop} {receiver load : object.Vertex}
    (small : ((PresentedEntry.ofTraceBasin object support basin threshold
      LengthOK receiver load).toEntry (HasCycleWithLength LengthOK)).alpha ≤ 1)
    (left right : BoundaryPiece
      (Strategy.InterfaceReplacement.SupportAtom.boundary object basin)) :
    Response.ContextEquivalentOn
      (declaredAlgebra object support basin threshold LengthOK receiver load)
      left right := by
  classical
  have absent : ∀ piece outside,
      ¬ declaredAlgebra object support basin threshold LengthOK receiver load
          piece outside := by
    intro piece outside holds
    obtain ⟨coordinate, coreRetained, crossing⟩ := distinguishingEventCrosses holds
    have alphaTwo :=
      Entry.two_le_alpha_of_two_le_card_car _ coreRetained
        ((PresentedEntry.ofTraceBasin object support basin threshold LengthOK
          receiver load).two_le_card_car crossing)
    omega
  intro outside
  constructor
  · intro holds
    exact absurd holds (absent left outside)
  · intro holds
    exact absurd holds (absent right outside)

end TraceBasin

namespace TraceBasin

open TraceCoordinateSystem

/-- **The fold changes no label-to-label incidence.**  The two extra disjuncts
of `BoundaryPiece.identifyInternal_adj` ask a boundary label to decode to an
internal vertex. -/
theorem identifyInternal_labelAdj_iff {boundary : Boundary.{u}}
    (piece : BoundaryPiece boundary) (keep remove : piece.Internal)
    (different : keep ≠ remove) (left right : boundary.Vertex) :
    (piece.identifyInternal keep remove different).graph.Adj (.inl left)
        (.inl right) ↔
      piece.graph.Adj (.inl left) (.inl right) := by
  rw [BoundaryPiece.identifyInternal_adj]
  constructor
  · rintro ⟨_, old | ⟨decoded, _⟩ | ⟨decoded, _⟩⟩
    · exact old
    · exact absurd decoded (by simp [BoundaryPiece.foldDecode])
    · exact absurd decoded (by simp [BoundaryPiece.foldDecode])
  · intro adjacent
    exact ⟨fun equality => adjacent.ne (congrArg Sum.inl (Sum.inl.inj equality)),
      Or.inl adjacent⟩

/-- **A realization of a response quotient of `\rho_u(B_u)`**
(`def:typeA-trace-basin`): *"a
boundaried response state with the same boundary degree profile whose image
under the quotient map is the given quotient"*.

Both halves of the sentence are literal here.  The boundary degree profile is
the basin's own, and being *the image under the quotient map* is
`PresentedEntry.ResponseQuotientMap`: the state is carried onto by
`\rho_u(B_u)` through a label-fixing surjection whose incidences are exactly
the images of the basin's own, so every declared entry the state carries is
`PresentedEntry.declaredEntry` of an entry of `\mathcal R_u(B_u)` and the state
carries no entry the basin does not.  In particular a state that adjoins fresh
internal structure to the basin piece is *not* a realization: nothing of
`\rho_u(B_u)` maps onto the adjoined entries.

The class is indexed by the quotient's retained family: a realization must not
only be an image of `\rho_u(B_u)`, it must leave the *retained* entries of
`\mathcal R_u(B_u)` standing, i.e. the quotient map may identify two entries
inside one declared support only when that coordinate has been forgotten.  This
is the second half of *"whose image under the quotient map is the given
quotient"*, and it is what `not_declaredFamilyDeterminacy_of_undeclaredFoldPair`
showed to be necessary: without the index every interior fold realizes every
quotient, so the all-realizations clause is refuted outright by
`K .uncompressible` and alternative `(b)` becomes unsatisfiable rather than
merely hard. -/
def QuotientRealization (object : FiniteObject.{u})
    (support basin : Finset object.Vertex) (threshold : Nat)
    (receiver load : object.Vertex)
    (retained : Finset (PresentedEntry.TraceCoordinate object support))
    (realization : BoundaryPiece
      (Strategy.InterfaceReplacement.SupportAtom.boundary object basin)) :
    Prop :=
  realization.boundaryDegreeProfile =
      (Strategy.InterfaceReplacement.SupportAtom.piece object
        basin).boundaryDegreeProfile ∧
    ∃ quotient : PresentedEntry.ResponseQuotientMap object basin realization,
      ∀ coordinate ∈ retained, ∀ first second,
        Strategy.InterfaceReplacement.SupportAtom.pieceDecode object basin
            first ∈
          PresentedEntry.traceDeclaredSupport object support threshold receiver
            load coordinate →
        Strategy.InterfaceReplacement.SupportAtom.pieceDecode object basin
            second ∈
          PresentedEntry.traceDeclaredSupport object support threshold receiver
            load coordinate →
        quotient.toFun first = quotient.toFun second → first = second

/-- **`\rho_u(B_u)` realizes every one of its own response quotients.**  The
identity quotient map identifies nothing, so no retained entry is collapsed. -/
theorem quotientRealization_self (object : FiniteObject.{u})
    (support basin : Finset object.Vertex) (threshold : Nat)
    (receiver load : object.Vertex)
    (retained : Finset (PresentedEntry.TraceCoordinate object support)) :
    QuotientRealization object support basin threshold receiver load retained
      (Strategy.InterfaceReplacement.SupportAtom.piece object basin) :=
  ⟨rfl, PresentedEntry.identityQuotient object basin,
    fun _ _ _ _ _ _ collapsed => collapsed⟩

/-- **A realization moves no label-to-label incidence.**  The quotient map fixes
every label, so a label-to-label incidence of the realization is the image of
one of `\rho_u(B_u)`, and conversely. -/
theorem quotientRealization_labelAdj_iff {object : FiniteObject.{u}}
    {basin : Finset object.Vertex}
    {realization : BoundaryPiece
      (Strategy.InterfaceReplacement.SupportAtom.boundary object basin)}
    (quotient : PresentedEntry.ResponseQuotientMap object basin realization)
    (left right : (Strategy.InterfaceReplacement.SupportAtom.boundary object
      basin).Vertex) :
    realization.graph.Adj (.inl left) (.inl right) ↔
      (Strategy.InterfaceReplacement.SupportAtom.piece object
        basin).graph.Adj (.inl left) (.inl right) := by
  constructor
  · intro adjacent
    obtain ⟨source, target, sourceEq, targetEq, sourceAdj⟩ :=
      quotient.image _ _ adjacent
    cases source with
    | inl sourceLabel =>
        cases target with
        | inl targetLabel =>
            have leftEq : sourceLabel = left := by
              have := (quotient.labels sourceLabel).symm.trans sourceEq
              exact Sum.inl.inj this
            have rightEq : targetLabel = right := by
              have := (quotient.labels targetLabel).symm.trans targetEq
              exact Sum.inl.inj this
            exact leftEq ▸ rightEq ▸ sourceAdj
        | inr targetInternal =>
            obtain ⟨image, imageEq⟩ := quotient.interior targetInternal
            rw [imageEq] at targetEq
            exact absurd targetEq (by exact Sum.inr_ne_inl)
    | inr sourceInternal =>
        obtain ⟨image, imageEq⟩ := quotient.interior sourceInternal
        rw [imageEq] at sourceEq
        exact absurd sourceEq (by exact Sum.inr_ne_inl)
  · intro adjacent
    have distinct :
        quotient.toFun (.inl left) ≠ quotient.toFun (.inl right) := by
      rw [quotient.labels, quotient.labels]
      exact fun same => adjacent.ne (congrArg Sum.inl (Sum.inl.inj same))
    have image := quotient.forward _ _ adjacent distinct
    rwa [quotient.labels, quotient.labels] at image

/-- **An interior identification realizes exactly the quotients that forget the
identified pair.**  It is in the basin's boundary-degree fibre and it is the
image of `\rho_u(B_u)` under the identification map; and it leaves every
retained entry standing precisely when no retained declared support carries both
identified entries.  That side condition is not a cost: it is
`def:typeA-trace-basin`'s *"identifying or forgetting entries"* read at the pair
being identified. -/
theorem quotientRealization_identifyInternal (object : FiniteObject.{u})
    (support basin : Finset object.Vertex) (threshold : Nat)
    (receiver load : object.Vertex)
    (retained : Finset (PresentedEntry.TraceCoordinate object support))
    (keep remove :
      (Strategy.InterfaceReplacement.SupportAtom.piece object basin).Internal)
    (different : keep ≠ remove)
    (noCommonLabel : ∀ label : (Strategy.InterfaceReplacement.SupportAtom.boundary
      object basin).Vertex,
      ¬ ((Strategy.InterfaceReplacement.SupportAtom.piece object basin).graph.Adj
            (.inr keep) (.inl label) ∧
        (Strategy.InterfaceReplacement.SupportAtom.piece object basin).graph.Adj
          (.inr remove) (.inl label)))
    (undeclared : ∀ coordinate ∈ retained,
      ¬ (keep.1 ∈ PresentedEntry.traceDeclaredSupport object support threshold
            receiver load coordinate ∧
        remove.1 ∈ PresentedEntry.traceDeclaredSupport object support threshold
          receiver load coordinate)) :
    QuotientRealization object support basin threshold receiver load retained
      ((Strategy.InterfaceReplacement.SupportAtom.piece object
        basin).identifyInternal keep remove different) := by
  refine ⟨BoundaryPiece.boundaryDegreeProfile_identifyInternal_of_noCommonLabel _
      keep remove different noCommonLabel,
    PresentedEntry.foldQuotient object basin keep remove different, ?_⟩
  intro coordinate member first second firstDeclared secondDeclared collapsed
  rcases PresentedEntry.foldMap_eq_cases _ keep remove different collapsed with
    same | ⟨firstEq, secondEq⟩ | ⟨firstEq, secondEq⟩
  · exact same
  · subst firstEq
    subst secondEq
    exact absurd ⟨secondDeclared, firstDeclared⟩ (undeclared coordinate member)
  · subst firstEq
    subst secondEq
    exact absurd ⟨firstDeclared, secondDeclared⟩ (undeclared coordinate member)

/-- **The ambient no-common-neighbour condition is the piece's.**  Every
incidence of the basin's piece decodes to an ambient incidence, so a pair of
interior entries with no ambient common neighbour has none in the piece.  This
is the adapter that lets `FiniteObject.FoldPlan`'s first arm feed the exit-`(5)`
closure directly. -/
theorem noCommon_piece_of_noCommon (object : FiniteObject.{u})
    (basin : Finset object.Vertex)
    (keep remove :
      (Strategy.InterfaceReplacement.SupportAtom.piece object basin).Internal)
    (noCommon : ∀ common, ¬ object.IsCommonNeighbor keep.1 remove.1 common) :
    ∀ x, ¬ ((Strategy.InterfaceReplacement.SupportAtom.piece object
          basin).graph.Adj (.inr keep) x ∧
      (Strategy.InterfaceReplacement.SupportAtom.piece object basin).graph.Adj
        (.inr remove) x) := by
  intro x common
  exact noCommon
    (Strategy.InterfaceReplacement.SupportAtom.pieceDecode object basin x)
    ⟨common.1, common.2⟩

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
                (left ∈ basin ∧
                    left ∉
                      Strategy.InterfaceReplacement.SupportAtom.cutBoundary object
                        basin) ∧
                  (right ∈ basin ∧
                      right ∉
                        Strategy.InterfaceReplacement.SupportAtom.cutBoundary object
                          basin) ∧
                    object.graph.Adj left right)) ∧
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
              (left ∈ basin ∧
                  left ∉
                    Strategy.InterfaceReplacement.SupportAtom.cutBoundary object
                      basin) ∧
                (right ∈ basin ∧
                    right ∉
                      Strategy.InterfaceReplacement.SupportAtom.cutBoundary object
                        basin) ∧
                  object.graph.Adj left right)) ∧
    (∀ realization,
      QuotientRealization object support basin threshold receiver load retained
          realization →
        Response.ContextEquivalentOn
          (declaredAlgebra object support basin threshold LengthOK receiver load)
          realization
          (Strategy.InterfaceReplacement.SupportAtom.piece object basin))

/-- **`False` from the all-realizations clause at an identification.**

`def:typeA-trace-basin`: *"The quotient is target-complete for `\rho_u(B_u)` if,
for every outside `\partial B_u`-context compatible with the boundary profile,
all realizations of the quotient give the same target predicate as
`\rho_u(B_u)` after gluing."*

Given, as a hypothesis, that an interior identification of the basin's own piece
is one such realization, the all-realizations clause hands its target predicate straight to
`PresentedEntry.not_targetComplete_foldRealization`, which `K .uncompressible`
refutes.  The realization predicate is a parameter: the bridge asks only that
the identification be one of the quotient's realizations, and nothing else
about the class. -/
theorem false_of_allRealizations_contextEquivalent {object : FiniteObject.{u}}
    {basin : Finset object.Vertex} {threshold : Nat} (two : 2 ≤ threshold)
    {LengthOK : Nat → Prop}
    (connected : SupportComponents.Connected.ConnectedOn object basin)
    (proper : ∃ vertex, vertex ∉ basin)
    (baseline : MinimumDegreeAtLeast threshold object)
    (keep remove :
      (Strategy.InterfaceReplacement.SupportAtom.piece object basin).Internal)
    (different : keep ≠ remove)
    (noCommon : ∀ x,
      ¬ ((Strategy.InterfaceReplacement.SupportAtom.piece object basin).graph.Adj
            (.inr keep) x ∧
        (Strategy.InterfaceReplacement.SupportAtom.piece object basin).graph.Adj
          (.inr remove) x))
    (uncompressible : ∀ candidate : Finset object.Vertex,
      ¬ Strategy.InterfaceReplacement.CompressibleSupport
          (MinimumDegreeAtLeast threshold) (HasCycleWithLength LengthOK) object
          candidate)
    {Realization : BoundaryPiece
      (Strategy.InterfaceReplacement.SupportAtom.boundary object basin) → Prop}
    (identificationRealizes : Realization
      ((Strategy.InterfaceReplacement.SupportAtom.piece object
        basin).identifyInternal keep remove different))
    (allRealizations : ∀ realization, Realization realization →
      Response.ContextEquivalent (HasCycleWithLength LengthOK) realization
        (Strategy.InterfaceReplacement.SupportAtom.piece object basin)) :
    False :=
  PresentedEntry.not_targetComplete_foldRealization object basin threshold two
    LengthOK connected proper keep remove different baseline noCommon
    uncompressible
    ⟨BoundaryPiece.boundaryDegreeProfile_identifyInternal_of_noCommonLabel _ keep
      remove different (fun label common => noCommon (.inl label) common),
      allRealizations _ identificationRealizes⟩


/-- **`False` from the all-realizations clause, for the indexed realization class.**

`def:typeA-trace-basin`: *"The quotient is target-complete for `\rho_u(B_u)` if,
for every outside `\partial B_u`-context compatible with the boundary profile,
all realizations of the quotient give the same target predicate as
`\rho_u(B_u)` after gluing."*  The interior identification is one of the
quotient's realizations as soon as no retained declared support carries both
identified entries, so the clause hands its target predicate to
`PresentedEntry.not_targetComplete_foldRealization`, which `K .uncompressible`
refutes. -/
theorem false_of_allQuotientRealizations_contextEquivalent
    {object : FiniteObject.{u}} {support basin : Finset object.Vertex}
    {threshold : Nat} (two : 2 ≤ threshold) {LengthOK : Nat → Prop}
    {receiver load : object.Vertex}
    {retained : Finset (PresentedEntry.TraceCoordinate object support)}
    (connected : SupportComponents.Connected.ConnectedOn object basin)
    (proper : ∃ vertex, vertex ∉ basin)
    (baseline : MinimumDegreeAtLeast threshold object)
    (keep remove :
      (Strategy.InterfaceReplacement.SupportAtom.piece object basin).Internal)
    (different : keep ≠ remove)
    (noCommon : ∀ x,
      ¬ ((Strategy.InterfaceReplacement.SupportAtom.piece object basin).graph.Adj
            (.inr keep) x ∧
        (Strategy.InterfaceReplacement.SupportAtom.piece object basin).graph.Adj
          (.inr remove) x))
    (undeclared : ∀ coordinate ∈ retained,
      ¬ (keep.1 ∈ PresentedEntry.traceDeclaredSupport object support threshold
            receiver load coordinate ∧
        remove.1 ∈ PresentedEntry.traceDeclaredSupport object support threshold
          receiver load coordinate))
    (uncompressible : ∀ candidate : Finset object.Vertex,
      ¬ Strategy.InterfaceReplacement.CompressibleSupport
          (MinimumDegreeAtLeast threshold) (HasCycleWithLength LengthOK) object
          candidate)
    (allRealizations : ∀ realization,
      QuotientRealization object support basin threshold receiver load retained
          realization →
        Response.ContextEquivalent (HasCycleWithLength LengthOK) realization
          (Strategy.InterfaceReplacement.SupportAtom.piece object basin)) :
    False :=
  false_of_allRealizations_contextEquivalent two connected proper baseline keep
    remove different noCommon uncompressible
    (Realization := QuotientRealization object support basin threshold receiver
      load retained)
    (quotientRealization_identifyInternal object support basin threshold receiver
      load retained keep remove different
      (fun label common => noCommon (.inl label) common) undeclared)
    allRealizations

/-- An interior pair `keep`/`remove` of the basin piece with no ambient common
neighbour, not held together by any retained declared support, yields `False`
given `uncompressible` and the all-realizations clause `allRealizations`.

The no-common-neighbour hypothesis is the first arm of the Lean construct
`FiniteObject.FoldPlan`; `noCommon_piece_of_noCommon` transports it to the
basin's piece.  The plan's second arm (the `BoundaryPiece.addEdge` repair) is
not handled here: `PresentedEntry.compressibleSupport_of_triangleContraction`
covers the triangle repair only.

**Not on the critical path for `\alpha(\xi)\ge2`.**  `lem:typeA-one-terminal-collapse`
never *constructs* a fold: it uses the occurrence of
alternative `(b)` against the absence of exits `(4)`--`(7)`.  The fold pair is
needed only to *refute* `(b)`, which that lemma does not do.  So neither the
four origins of `FiniteObject.exists_foldPlan_of_distinctFour_of_cubic` nor the
missing `addEdge` compressibility lemma is required by the route-8 rows; do not
re-derive them for that purpose. -/
theorem false_of_interiorFoldPair {object : FiniteObject.{u}}
    {support basin : Finset object.Vertex} {threshold : Nat} (two : 2 ≤ threshold)
    {LengthOK : Nat → Prop} {receiver load : object.Vertex}
    {retained : Finset (PresentedEntry.TraceCoordinate object support)}
    (connected : SupportComponents.Connected.ConnectedOn object basin)
    (proper : ∃ vertex, vertex ∉ basin)
    (baseline : MinimumDegreeAtLeast threshold object)
    (keep remove :
      (Strategy.InterfaceReplacement.SupportAtom.piece object basin).Internal)
    (different : keep.1 ≠ remove.1)
    (noCommon : ∀ common, ¬ object.IsCommonNeighbor keep.1 remove.1 common)
    (undeclared : ∀ coordinate ∈ retained,
      ¬ (keep.1 ∈ PresentedEntry.traceDeclaredSupport object support threshold
            receiver load coordinate ∧
        remove.1 ∈ PresentedEntry.traceDeclaredSupport object support threshold
          receiver load coordinate))
    (uncompressible : ∀ candidate : Finset object.Vertex,
      ¬ Strategy.InterfaceReplacement.CompressibleSupport
          (MinimumDegreeAtLeast threshold) (HasCycleWithLength LengthOK) object
          candidate)
    (allRealizations : ∀ realization,
      QuotientRealization object support basin threshold receiver load retained
          realization →
        Response.ContextEquivalent (HasCycleWithLength LengthOK) realization
          (Strategy.InterfaceReplacement.SupportAtom.piece object basin)) :
    False :=
  false_of_allQuotientRealizations_contextEquivalent two connected proper
    baseline keep remove (fun same => different (congrArg Subtype.val same))
    (noCommon_piece_of_noCommon object basin keep remove noCommon)
    undeclared uncompressible allRealizations

/-- **(B) The declared family determines the target, at one response quotient.**

`def:typeA-trace-basin`: *"The family
`\mathcal R_u(B_u)` is the complete declared coordinate family for the
`u`-supported target events used in the route-8 branch: once the boundary degree
profile and all entries of `\mathcal R_u(B_u)` are fixed, every compatible
outside context has the same truth value for each such declared event."*

Read at one quotient: two realizations of the *same* response quotient carry the
same boundary degree profile and the same retained entries of
`\mathcal R_u(B_u)`, so the sentence says they answer every outside
`\partial B_u`-context alike. -/
def DeclaredFamilyDeterminacy (object : FiniteObject.{u})
    (support basin : Finset object.Vertex) (threshold : Nat)
    (LengthOK : Nat → Prop) (receiver load : object.Vertex)
    (retained : Finset (PresentedEntry.TraceCoordinate object support)) : Prop :=
  ∀ left right : BoundaryPiece
      (Strategy.InterfaceReplacement.SupportAtom.boundary object basin),
    QuotientRealization object support basin threshold receiver load retained
        left →
      QuotientRealization object support basin threshold receiver load retained
          right →
        Response.ContextEquivalent (HasCycleWithLength LengthOK) left right

/-- **Determinacy (B) at an identification yields `False`.**  Together with a free
fold pair this refutes (B); see `not_declaredFamilyDeterminacy_of_undeclaredFoldPair`.

The interior identification and `\rho_u(B_u)` itself are two realizations of the
same response quotient, once no retained declared support carries both
identified entries.  Determinacy makes them context-equivalent, which is exactly
the fold realization `K .uncompressible` refutes through
`PresentedEntry.not_targetComplete_foldRealization`. -/
theorem false_of_declaredFamilyDeterminacy {object : FiniteObject.{u}}
    {support basin : Finset object.Vertex} {threshold : Nat} (two : 2 ≤ threshold)
    {LengthOK : Nat → Prop} {receiver load : object.Vertex}
    {retained : Finset (PresentedEntry.TraceCoordinate object support)}
    (connected : SupportComponents.Connected.ConnectedOn object basin)
    (proper : ∃ vertex, vertex ∉ basin)
    (baseline : MinimumDegreeAtLeast threshold object)
    (keep remove :
      (Strategy.InterfaceReplacement.SupportAtom.piece object basin).Internal)
    (different : keep ≠ remove)
    (noCommon : ∀ x,
      ¬ ((Strategy.InterfaceReplacement.SupportAtom.piece object basin).graph.Adj
            (.inr keep) x ∧
        (Strategy.InterfaceReplacement.SupportAtom.piece object basin).graph.Adj
          (.inr remove) x))
    (undeclared : ∀ coordinate ∈ retained,
      ¬ (keep.1 ∈ PresentedEntry.traceDeclaredSupport object support threshold
            receiver load coordinate ∧
        remove.1 ∈ PresentedEntry.traceDeclaredSupport object support threshold
          receiver load coordinate))
    (uncompressible : ∀ candidate : Finset object.Vertex,
      ¬ Strategy.InterfaceReplacement.CompressibleSupport
          (MinimumDegreeAtLeast threshold) (HasCycleWithLength LengthOK) object
          candidate)
    (determinacy : DeclaredFamilyDeterminacy object support basin threshold
      LengthOK receiver load retained) :
    False :=
  false_of_allQuotientRealizations_contextEquivalent two connected proper
    baseline keep remove different noCommon undeclared uncompressible
    (fun realization realizes =>
      determinacy realization _ realizes
        (quotientRealization_self object support basin threshold receiver load
          retained))

/-- **Determinacy is refutable even against the indexed class, so no total
construction site can discharge it.**

Indexing the realization class does *not* move this: `\rho_u(B_u)` realizes
every one of its own quotients (`quotientRealization_self`), and the interior
identification realizes the quotients that forget the identified pair, so the
two are always available together.  `PresentedEntry.ofTraceBasin` is built for
every object, including uncompressible ones carrying a legal interior fold, so
determinacy cannot be a field discharged there; it is a branch stipulation whose
only carrier is a hypothesis of the row that uses it. -/
theorem not_declaredFamilyDeterminacy_of_undeclaredFoldPair
    {object : FiniteObject.{u}}
    {support basin : Finset object.Vertex} {threshold : Nat} (two : 2 ≤ threshold)
    {LengthOK : Nat → Prop} {receiver load : object.Vertex}
    {retained : Finset (PresentedEntry.TraceCoordinate object support)}
    (connected : SupportComponents.Connected.ConnectedOn object basin)
    (proper : ∃ vertex, vertex ∉ basin)
    (baseline : MinimumDegreeAtLeast threshold object)
    (keep remove :
      (Strategy.InterfaceReplacement.SupportAtom.piece object basin).Internal)
    (different : keep ≠ remove)
    (noCommon : ∀ x,
      ¬ ((Strategy.InterfaceReplacement.SupportAtom.piece object basin).graph.Adj
            (.inr keep) x ∧
        (Strategy.InterfaceReplacement.SupportAtom.piece object basin).graph.Adj
          (.inr remove) x))
    (undeclared : ∀ coordinate ∈ retained,
      ¬ (keep.1 ∈ PresentedEntry.traceDeclaredSupport object support threshold
            receiver load coordinate ∧
        remove.1 ∈ PresentedEntry.traceDeclaredSupport object support threshold
          receiver load coordinate))
    (uncompressible : ∀ candidate : Finset object.Vertex,
      ¬ Strategy.InterfaceReplacement.CompressibleSupport
          (MinimumDegreeAtLeast threshold) (HasCycleWithLength LengthOK) object
          candidate) :
    ¬ DeclaredFamilyDeterminacy object support basin threshold LengthOK receiver
      load retained :=
  fun determinacy =>
    false_of_declaredFamilyDeterminacy two connected proper baseline keep remove
      different noCommon undeclared uncompressible determinacy

end TraceBasin


end Hypostructure.Graph.Route8
