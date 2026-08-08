import Hypostructure.Graph.DeclaredCoordinateSignature
import Hypostructure.Graph.CurvatureTargetRank
import Hypostructure.Graph.InducedPathMaximalPacking
import Hypostructure.Graph.RootedReturn
import Hypostructure.Graph.Strategy.InterfaceReplacement
import Hypostructure.Graph.VisibleReceiverEntry

/-!
# Finite trace-coordinate systems

This module constructs the base coordinate families of a trace response from
the finite graph data that define them.  Coordinate schedules, values, supports
and support tests are derived functions; callers provide none of them.
-/

namespace Hypostructure.Graph.TraceCoordinateSystem

open Hypostructure
open Hypostructure.Core.Finite

universe u

variable (object : FiniteObject.{u}) (support : Finset object.Vertex)

namespace D1

noncomputable abbrev boundary :=
  Strategy.InterfaceReplacement.SupportAtom.boundary object support

/-- A D1 coordinate is exactly one labelled vertex of the support's canonical
cut boundary. -/
abbrev Coordinate := (boundary object support).Vertex

/-- The exact finite D1 schedule, in the canonical order owned by the boundary
interface. -/
noncomputable def schedule : Enumeration (Coordinate object support) :=
  Enumeration.ofFinEnum (boundary object support).vertices

@[simp] theorem mem_schedule (coordinate : Coordinate object support) :
    coordinate ∈ (schedule object support).values :=
  Enumeration.mem_ofFinEnum_values (boundary object support).vertices coordinate

/-- The uncapped boundary-degree value of a D1 coordinate. -/
noncomputable def value (coordinate : Coordinate object support) : Nat :=
  (Strategy.InterfaceReplacement.SupportAtom.piece object support).boundaryDegreeProfile
    coordinate

/-- The manuscript-declared support of a boundary-degree entry is its labelled
boundary vertex alone. -/
noncomputable def declaredSupport (coordinate : Coordinate object support) :
    Finset object.Vertex :=
  {coordinate.1}

@[simp] theorem mem_declaredSupport_iff
    (coordinate : Coordinate object support) (vertex : object.Vertex) :
    vertex ∈ declaredSupport object support coordinate ↔ vertex = coordinate.1 := by
  simp [declaredSupport]

/-- The singleton support of a D1 coordinate meets the canonical trace selected
for the routed load.  The trace itself is read through `tracePath?`; it is not
supplied by the caller. -/
def MeetsCanonicalTrace (threshold : Nat) (receiver load : object.Vertex)
    (coordinate : Coordinate object support) : Prop :=
  exists trace : object.graph.Path load receiver,
    object.tracePath? support threshold load receiver = some trace /\
      coordinate.1 ∈ trace.1.support

/-- The paper's D1 specialization of `u`-supported: direct intersection with
the canonical trace, or ownership by a scheduled receiver-entry return whose
channel contains that trace or owns its terminal receiver edge. -/
def USupported (threshold : Nat) (receiver load : object.Vertex)
    (coordinate : Coordinate object support) : Prop :=
  MeetsCanonicalTrace object support threshold receiver load coordinate \/
    VisibleEntry.ownsBoundaryEntry object support threshold receiver load coordinate.1

/-- Decidable finite D1 support test. -/
noncomputable def uSupported (threshold : Nat) (receiver load : object.Vertex)
    (coordinate : Coordinate object support) : Bool :=
  @decide (USupported object support threshold receiver load coordinate)
    (Classical.propDecidable _)

@[simp] theorem uSupported_eq_true_iff
    (threshold : Nat) (receiver load : object.Vertex)
    (coordinate : Coordinate object support) :
    uSupported object support threshold receiver load coordinate = true ↔
      USupported object support threshold receiver load coordinate := by
  simp [uSupported]

end D1

namespace D2

/-- A D2 return-length coordinate is one unrestricted edge-rooted return from
the object's complete finite schedule. -/
abbrev Coordinate := EdgeRootedReturn.Unrestricted object

/-- Exact finite D2 return-length schedule. -/
noncomputable def schedule : Enumeration (Coordinate object) :=
  EdgeRootedReturn.schedule object

@[simp] theorem mem_schedule (coordinate : Coordinate object) :
    coordinate ∈ (schedule object).values :=
  EdgeRootedReturn.mem_schedule coordinate

/-- The coordinate's canonical numerical value is the length of its deleted-edge
simple return path. -/
def value (coordinate : Coordinate object) : Nat :=
  coordinate.path.length

/-- The declared vertex support of the return coordinate is the support of the
same return transferred unchanged to the ambient graph. -/
noncomputable def declaredSupport (coordinate : Coordinate object) :
    Finset object.Vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact coordinate.ambientPath.support.toFinset

/-- Direct trace intersection for a D2 return coordinate. -/
def MeetsCanonicalTrace (threshold : Nat) (receiver load : object.Vertex)
    (coordinate : Coordinate object) : Prop :=
  exists trace : object.graph.Path load receiver,
    object.tracePath? support threshold load receiver = some trace /\
      exists vertex,
        vertex ∈ declaredSupport object coordinate /\ vertex ∈ trace.1.support

/-- The paper's receiver-entry ownership alternative for return coordinates.
The oriented root must be the completion port `(receiver,outside)`, and the
coordinate's declared return support must belong to an actual scheduled
receiver-entry return visible for the routed load. -/
def OwnedByReceiverEntryReturn (threshold : Nat)
    (receiver load : object.Vertex) (coordinate : Coordinate object) : Prop :=
  exists outside, outside ∈ VisibleEntry.completionPorts object support receiver /\
    coordinate.dart.fst = receiver /\ coordinate.dart.snd = outside /\
      exists return' : VisibleEntry.ReceiverEntryReturn object support receiver outside,
        return' ∈ (VisibleEntry.ReceiverEntryReturn.schedule
          object support receiver outside).values /\
        return'.OwnsDeclaredSupport (threshold := threshold)
          (declaredSupport object coordinate) load

/-- D2 return coordinates are `u`-supported exactly by direct trace
intersection or the canonical receiver-entry ownership alternative. -/
def USupported (threshold : Nat) (receiver load : object.Vertex)
    (coordinate : Coordinate object) : Prop :=
  MeetsCanonicalTrace object support threshold receiver load coordinate \/
    OwnedByReceiverEntryReturn object support threshold receiver load coordinate

/-- Decidable finite D2 support test. -/
noncomputable def uSupported (threshold : Nat) (receiver load : object.Vertex)
    (coordinate : Coordinate object) : Bool :=
  @decide (USupported object support threshold receiver load coordinate)
    (Classical.propDecidable _)

@[simp] theorem uSupported_eq_true_iff
    (threshold : Nat) (receiver load : object.Vertex)
    (coordinate : Coordinate object) :
    uSupported object support threshold receiver load coordinate = true ↔
      USupported object support threshold receiver load coordinate := by
  simp [uSupported]

end D2

namespace D3

open InducedPathMaximalPacking

/-- The canonical maximal packing of induced P13 windows. -/
noncomputable abbrev packing (object : FiniteObject.{u}) : Profile object 13 :=
  maximalProfile object 13

/-- A window selected by the canonical maximal P13 packing. -/
abbrev SelectedWindow (object : FiniteObject.{u}) :=
  { window : Window object 13 // window ∈ (packing object).selected }

/-- A selected P13 window lying wholly in the current canonical component. -/
abbrev PackedWindow (object : FiniteObject.{u})
    (componentSupport : Finset object.Vertex) :=
  { window : SelectedWindow object //
      InducedPathMaximalPacking.support object 13 window.1 ⊆ componentSupport }

/-- Exact schedule of canonically selected P13 windows. -/
noncomputable def selectedWindowSchedule (object : FiniteObject.{u}) :
    Enumeration (SelectedWindow object) := by
  classical
  exact Enumeration.ofNodupList (packing object).selected.attach
    (packing object).selected_nodup.attach

/-- Exact restriction of the canonical packing to one component support. -/
noncomputable def packedWindowSchedule (object : FiniteObject.{u})
    (componentSupport : Finset object.Vertex) :
    Enumeration (PackedWindow object componentSupport) :=
  (selectedWindowSchedule object).subtype
    (fun window =>
      InducedPathMaximalPacking.support object 13 window.1 ⊆ componentSupport)
    (fun _ => Classical.propDecidable _)

@[simp] theorem mem_packedWindowSchedule
    (window : PackedWindow object support) :
    window ∈ (packedWindowSchedule object support).values := by
  classical
  simp only [packedWindowSchedule, Enumeration.mem_subtype_values]
  simp [selectedWindowSchedule, packing]

/-- The unique schedule-first orientation of a packed P13 support. -/
noncomputable def placement (window : PackedWindow object support) :
    Window object 13 :=
  P13.canonicalPlacement window.1.1

theorem placement_support (window : PackedWindow object support) :
    InducedPathMaximalPacking.support object 13 (placement object support window) =
      InducedPathMaximalPacking.support object 13 window.1.1 :=
  P13.canonicalPlacement_support window.1.1

/-- Raw attachment label of an outside vertex: exactly the ordered positions
of the canonical P13 placement adjacent to that vertex. -/
noncomputable def attachmentLabel (window : PackedWindow object support)
    (outside : object.Vertex) : Finset (Fin 13) := by
  letI : DecidableRel object.graph.Adj := object.decideAdj
  exact Finset.univ.filter fun index =>
    object.graph.Adj outside (placement object support window index)

@[simp] theorem mem_attachmentLabel_iff
    (window : PackedWindow object support) (outside : object.Vertex)
    (index : Fin 13) :
    index ∈ attachmentLabel object support window outside ↔
      object.graph.Adj outside (placement object support window index) := by
  simp [attachmentLabel]

/-- Actual outside attachment pairs, excluding vertices of the window and
requiring a nonempty adjacency label. -/
noncomputable def IsOutsideAttachment
    (pair : PackedWindow object support × object.Vertex) : Prop :=
  pair.2 ∉ InducedPathMaximalPacking.support object 13
      (placement object support pair.1) ∧
    (attachmentLabel object support pair.1 pair.2).Nonempty

/-- A D3 coordinate is one actual outside attachment to one packed P13 window. -/
abbrev Coordinate (object : FiniteObject.{u})
    (componentSupport : Finset object.Vertex) :=
  { pair : PackedWindow object componentSupport × object.Vertex //
      IsOutsideAttachment object componentSupport pair }

/-- Exact finite D3 schedule, retaining packing order and then vertex order. -/
noncomputable def schedule : Enumeration (Coordinate object support) :=
  ((packedWindowSchedule object support).product
      (Enumeration.ofFinEnum object.vertices)).subtype
    (IsOutsideAttachment object support)
    (fun _ => Classical.propDecidable _)

@[simp] theorem mem_schedule (coordinate : Coordinate object support) :
    coordinate ∈ (schedule object support).values := by
  classical
  simp only [schedule, Enumeration.mem_subtype_values,
    Enumeration.mem_product_values]
  exact ⟨mem_packedWindowSchedule object support coordinate.1.1,
    Enumeration.mem_ofFinEnum_values object.vertices coordinate.1.2⟩

/-- The D3 value is the actual raw attachment label, not a supplied bit-vector
or an abstract Type-B label. -/
noncomputable def value (coordinate : Coordinate object support) :
    Finset (Fin 13) :=
  attachmentLabel object support coordinate.1.1 coordinate.1.2

/-- A raw window-label query inspects the whole ordered P13 support and its
outside attachment vertex. -/
noncomputable def declaredSupport (coordinate : Coordinate object support) :
    Finset object.Vertex := by
  classical
  exact InducedPathMaximalPacking.support object 13
      (placement object support coordinate.1.1) ∪ {coordinate.1.2}

/-- Direct intersection of the D3 declared support with the canonical trace. -/
def MeetsCanonicalTrace (threshold : Nat) (receiver load : object.Vertex)
    (coordinate : Coordinate object support) : Prop :=
  exists trace : object.graph.Path load receiver,
    object.tracePath? support threshold load receiver = some trace /\
      exists vertex,
        vertex ∈ declaredSupport object support coordinate /\
          vertex ∈ trace.1.support

/-- Receiver-return ownership is read from the complete scheduled family and
the same D3 declared support; callers do not provide a return witness. -/
def OwnedByReceiverEntryReturn (threshold : Nat)
    (receiver load : object.Vertex) (coordinate : Coordinate object support) : Prop :=
  VisibleEntry.ownsDeclaredSupport object support threshold receiver load
    (declaredSupport object support coordinate)

/-- Paper D3 `u`-support: trace intersection or canonical receiver-return
ownership. -/
def USupported (threshold : Nat) (receiver load : object.Vertex)
    (coordinate : Coordinate object support) : Prop :=
  MeetsCanonicalTrace object support threshold receiver load coordinate \/
    OwnedByReceiverEntryReturn object support threshold receiver load coordinate

/-- Decidable finite D3 support test. -/
noncomputable def uSupported (threshold : Nat) (receiver load : object.Vertex)
    (coordinate : Coordinate object support) : Bool :=
  @decide (USupported object support threshold receiver load coordinate)
    (Classical.propDecidable _)

@[simp] theorem uSupported_eq_true_iff
    (threshold : Nat) (receiver load : object.Vertex)
    (coordinate : Coordinate object support) :
    uSupported object support threshold receiver load coordinate = true ↔
      USupported object support threshold receiver load coordinate := by
  simp [uSupported]

end D3

namespace D4

/-- A D4 coordinate is exactly one raw internal wedge carried by the current
component.  The membership proof records that its centre, not only its two
neighbours, belongs to the component. -/
abbrev Coordinate (object : FiniteObject.{u})
    (componentSupport : Finset object.Vertex) :=
  { test : object.InternalWedge componentSupport //
      test ∈ object.internalWedgeFamily componentSupport }

/-- Exact finite schedule of the component's raw curvature tests. -/
noncomputable def schedule : Enumeration (Coordinate object support) := by
  classical
  exact Enumeration.ofNodupList
    (object.internalWedgeFamily support).attach.toList
    (Finset.nodup_toList _)

@[simp] theorem mem_schedule (coordinate : Coordinate object support) :
    coordinate ∈ (schedule object support).values := by
  classical
  simp [schedule]

/-- The coordinate schedule counts exactly the wedge supply `W₂`. -/
theorem schedule_card :
    (schedule object support).card = object.internalWedgeCount support := by
  classical
  rw [schedule, Enumeration.card_eq_length]
  simp [object.internalWedgeFamily_card support]

/-- Raw curvature tests carry one common presence datum.  Their wedge labels,
not an invented numerical value, remain distinct in the exact profile. -/
abbrev Value (_coordinate : Coordinate object support) := Unit

def value (_coordinate : Coordinate object support) : Unit := ()

/-- Clause D4 declares precisely the centre and two endpoints of the wedge. -/
noncomputable def declaredSupport (coordinate : Coordinate object support) :
    Finset object.Vertex :=
  FiniteObject.internalWedgeSupport coordinate.1

/-- A scheduled simple cycle closes a wedge when its length is accepted and it
contains both edges from the wedge centre to its two endpoints. -/
def ClosingReturn (LengthOK : Nat → Prop)
    (coordinate : Coordinate object support)
    (return' : EdgeRootedReturn.Unrestricted object) : Prop :=
  LengthOK return'.cycle.length ∧
    ∀ endpoint ∈ coordinate.1.2.1,
      s(coordinate.1.1, endpoint) ∈ return'.cycle.edges

/-- Complete finite schedule of accepted simple cycles that close one fixed
raw wedge, inherited by filtering the complete rooted-return schedule. -/
noncomputable def closingReturnSchedule (LengthOK : Nat → Prop)
    (coordinate : Coordinate object support) :
    Enumeration { return' : EdgeRootedReturn.Unrestricted object //
      ClosingReturn object support LengthOK coordinate return' } :=
  (EdgeRootedReturn.schedule object).subtype
    (ClosingReturn object support LengthOK coordinate)
    (fun _ => Classical.propDecidable _)

@[simp] theorem mem_closingReturnSchedule (LengthOK : Nat → Prop)
    (coordinate : Coordinate object support)
    (closing : { return' : EdgeRootedReturn.Unrestricted object //
      ClosingReturn object support LengthOK coordinate return' }) :
    closing ∈ (closingReturnSchedule object support LengthOK coordinate).values := by
  classical
  simp only [closingReturnSchedule, Enumeration.mem_subtype_values]
  exact EdgeRootedReturn.mem_schedule closing.1

/-- A D4 target event is intrinsically an accepted simple cycle containing the
two edges of the indexed wedge. -/
structure TargetEvent (LengthOK : Nat → Prop)
    (coordinate : Coordinate object support) where
  certificate : CycleCertificate object LengthOK
  closesWedge : ∀ endpoint ∈ coordinate.1.2.1,
    s(coordinate.1.1, endpoint) ∈ certificate.walk.edges

namespace TargetEvent

/-- Turn one filtered rooted return into its typed wedge-closing event. -/
def ofClosingReturn (LengthOK : Nat → Prop)
    (coordinate : Coordinate object support)
    (closing : { return' : EdgeRootedReturn.Unrestricted object //
      ClosingReturn object support LengthOK coordinate return' }) :
    TargetEvent object support LengthOK coordinate where
  certificate := {
    vertex := closing.1.dart.fst
    walk := closing.1.cycle
    isCycle := closing.1.cycle_isCycle
    length_ok := closing.2.1 }
  closesWedge := closing.2.2

end TargetEvent

/-- The optional event is the first wedge-closing accepted cycle in the exact
rooted-return schedule.  No event is attached when the wedge closes none. -/
noncomputable def event? (LengthOK : Nat → Prop)
    (coordinate : Coordinate object support) :
    Option (TargetEvent object support LengthOK coordinate) :=
  match (closingReturnSchedule object support LengthOK coordinate).values with
  | [] => none
  | first :: _ => some (TargetEvent.ofClosingReturn object support LengthOK
      coordinate first)

/-- Event presence is exhaustive: it occurs exactly when some actual scheduled
simple cycle closes the wedge at an accepted length. -/
theorem event?_isSome_iff (LengthOK : Nat → Prop)
    (coordinate : Coordinate object support) :
    (event? object support LengthOK coordinate).isSome = true ↔
      ∃ return' : EdgeRootedReturn.Unrestricted object,
        ClosingReturn object support LengthOK coordinate return' := by
  classical
  cases scheduleEq :
      (closingReturnSchedule object support LengthOK coordinate).values with
  | nil =>
      constructor
      · simp [event?, scheduleEq]
      · rintro ⟨return', closes⟩
        have member := mem_closingReturnSchedule object support LengthOK coordinate
          (⟨return', closes⟩ : { return' : EdgeRootedReturn.Unrestricted object //
            ClosingReturn object support LengthOK coordinate return' })
        simp [scheduleEq] at member
  | cons first rest =>
      constructor
      · intro _
        exact ⟨first.1, first.2⟩
      · intro _
        simp [event?, scheduleEq]

/-- Direct intersection of the raw wedge support with the canonical trace. -/
def MeetsCanonicalTrace (threshold : Nat) (receiver load : object.Vertex)
    (coordinate : Coordinate object support) : Prop :=
  exists trace : object.graph.Path load receiver,
    object.tracePath? support threshold load receiver = some trace /\
      exists vertex,
        vertex ∈ declaredSupport object support coordinate /\
          vertex ∈ trace.1.support

/-- Receiver-return ownership uses the same complete scheduled family as D1--D3. -/
def OwnedByReceiverEntryReturn (threshold : Nat)
    (receiver load : object.Vertex) (coordinate : Coordinate object support) : Prop :=
  VisibleEntry.ownsDeclaredSupport object support threshold receiver load
    (declaredSupport object support coordinate)

def USupported (threshold : Nat) (receiver load : object.Vertex)
    (coordinate : Coordinate object support) : Prop :=
  MeetsCanonicalTrace object support threshold receiver load coordinate \/
    OwnedByReceiverEntryReturn object support threshold receiver load coordinate

noncomputable def uSupported (threshold : Nat) (receiver load : object.Vertex)
    (coordinate : Coordinate object support) : Bool :=
  @decide (USupported object support threshold receiver load coordinate)
    (Classical.propDecidable _)

@[simp] theorem uSupported_eq_true_iff
    (threshold : Nat) (receiver load : object.Vertex)
    (coordinate : Coordinate object support) :
    uSupported object support threshold receiver load coordinate = true ↔
      USupported object support threshold receiver load coordinate := by
  simp [uSupported]

end D4

/-! ## Constructed base family

The base family is an inductive sum so later manuscript families can be added
without changing the dependent value and support interface.  At this stage its
only constructor is the fully constructed D1 family.
-/

namespace Base

inductive Coordinate where
  | d1 (coordinate : D1.Coordinate object support)
  | d2ReturnLength (coordinate : D2.Coordinate object)
  | d3WindowLabel (coordinate : D3.Coordinate object support)
  | d4RawCurvature (coordinate : D4.Coordinate object support)

noncomputable instance coordinateDecEq :
    DecidableEq (Coordinate object support) :=
  Classical.decEq _

/-- The exact base schedule currently constructed from the graph. -/
noncomputable def schedule : Enumeration (Coordinate object support) :=
  { values :=
      (((D1.schedule object support).values.map Coordinate.d1 ++
        (D2.schedule object).values.map Coordinate.d2ReturnLength) ++
          (D3.schedule object support).values.map Coordinate.d3WindowLabel) ++
            (D4.schedule object support).values.map Coordinate.d4RawCurvature
    nodup := by
      rw [List.nodup_append]
      refine ⟨?_,
        (D4.schedule object support).nodup.map
          (by intro left right equal; cases equal; rfl), ?_⟩
      · rw [List.nodup_append]
        refine ⟨?_,
          (D3.schedule object support).nodup.map
            (by intro left right equal; cases equal; rfl), ?_⟩
        · rw [List.nodup_append]
          refine ⟨
            (D1.schedule object support).nodup.map
              (by intro left right equal; cases equal; rfl),
            (D2.schedule object).nodup.map
              (by intro left right equal; cases equal; rfl), ?_⟩
          intro left leftMember right rightMember
          obtain ⟨leftCoordinate, _leftMember, rfl⟩ := List.mem_map.mp leftMember
          obtain ⟨rightCoordinate, _rightMember, rfl⟩ := List.mem_map.mp rightMember
          intro equal
          cases equal
        intro left leftMember right rightMember
        rw [List.mem_append] at leftMember
        obtain ⟨rightCoordinate, _rightMember, rfl⟩ := List.mem_map.mp rightMember
        rcases leftMember with leftMember | leftMember
        · obtain ⟨leftCoordinate, _leftMember, rfl⟩ := List.mem_map.mp leftMember
          intro equal
          cases equal
        · obtain ⟨leftCoordinate, _leftMember, rfl⟩ := List.mem_map.mp leftMember
          intro equal
          cases equal
      intro left leftMember right rightMember
      rw [List.mem_append] at leftMember
      obtain ⟨rightCoordinate, _rightMember, rfl⟩ := List.mem_map.mp rightMember
      rcases leftMember with leftMember | leftMember
      · rw [List.mem_append] at leftMember
        rcases leftMember with leftMember | leftMember
        · obtain ⟨leftCoordinate, _leftMember, rfl⟩ := List.mem_map.mp leftMember
          intro equal
          cases equal
        · obtain ⟨leftCoordinate, _leftMember, rfl⟩ := List.mem_map.mp leftMember
          intro equal
          cases equal
      · obtain ⟨leftCoordinate, _leftMember, rfl⟩ := List.mem_map.mp leftMember
        intro equal
        cases equal
    decEq := coordinateDecEq object support }

@[simp] theorem mem_schedule (coordinate : Coordinate object support) :
    coordinate ∈ (schedule object support).values := by
  cases coordinate with
  | d1 coordinate =>
      rw [schedule]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_map.mpr
          ⟨coordinate, D1.mem_schedule object support coordinate, rfl⟩)))
  | d2ReturnLength coordinate =>
      rw [schedule]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.mpr ⟨coordinate, D2.mem_schedule object coordinate, rfl⟩)))
  | d3WindowLabel coordinate =>
      rw [schedule]
      exact List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.mpr
          ⟨coordinate, D3.mem_schedule object support coordinate, rfl⟩))
  | d4RawCurvature coordinate =>
      rw [schedule]
      exact List.mem_append_right _
        (List.mem_map.mpr
          ⟨coordinate, D4.mem_schedule object support coordinate, rfl⟩)

/-- The value type is indexed by the coordinate kind; no common finite value
alphabet is invented. -/
def Value : Coordinate object support → Type
  | .d1 _ => Nat
  | .d2ReturnLength _ => Nat
  | .d3WindowLabel _ => Finset (Fin 13)
  | .d4RawCurvature coordinate => D4.Value object support coordinate

/-- The graph-derived value of each constructed base coordinate. -/
noncomputable def value :
    (coordinate : Coordinate object support) → Value object support coordinate
  | .d1 coordinate => D1.value object support coordinate
  | .d2ReturnLength coordinate => D2.value object coordinate
  | .d3WindowLabel coordinate => D3.value object support coordinate
  | .d4RawCurvature coordinate => D4.value object support coordinate

/-- The manuscript signature kind of each constructed base coordinate. -/
def kind : Coordinate object support → DeclaredSignature.Kind
  | .d1 _ => .boundaryDegree
  | .d2ReturnLength _ => .returnData
  | .d3WindowLabel _ => .windowLabel
  | .d4RawCurvature _ => .rawCurvature

/-- The graph-derived finite declared support of each constructed base
coordinate. -/
noncomputable def declaredSupport :
    Coordinate object support → Finset object.Vertex
  | .d1 coordinate => D1.declaredSupport object support coordinate
  | .d2ReturnLength coordinate => D2.declaredSupport object coordinate
  | .d3WindowLabel coordinate => D3.declaredSupport object support coordinate
  | .d4RawCurvature coordinate => D4.declaredSupport object support coordinate

/-- The exact `u`-supported proposition for every constructed base coordinate. -/
def USupported (threshold : Nat) (receiver load : object.Vertex) :
    Coordinate object support → Prop
  | .d1 coordinate =>
      D1.USupported object support threshold receiver load coordinate
  | .d2ReturnLength coordinate =>
      D2.USupported object support threshold receiver load coordinate
  | .d3WindowLabel coordinate =>
      D3.USupported object support threshold receiver load coordinate
  | .d4RawCurvature coordinate =>
      D4.USupported object support threshold receiver load coordinate

/-- Coordinate-indexed optional target events.  Only D4 raw wedges currently
carry one, and only when an actual accepted simple cycle closes the wedge. -/
def Event (LengthOK : Nat → Prop) : Coordinate object support → Type u
  | .d1 _ => PUnit
  | .d2ReturnLength _ => PUnit
  | .d3WindowLabel _ => PUnit
  | .d4RawCurvature coordinate => D4.TargetEvent object support LengthOK coordinate

noncomputable def event? (LengthOK : Nat → Prop) :
    (coordinate : Coordinate object support) →
      Option (Event object support LengthOK coordinate)
  | .d1 _ => none
  | .d2ReturnLength _ => none
  | .d3WindowLabel _ => none
  | .d4RawCurvature coordinate => D4.event? object support LengthOK coordinate

/-- Decidable support test for the constructed base schedule. -/
noncomputable def uSupported (threshold : Nat) (receiver load : object.Vertex)
    (coordinate : Coordinate object support) : Bool :=
  @decide (USupported object support threshold receiver load coordinate)
    (Classical.propDecidable _)

@[simp] theorem uSupported_eq_true_iff
    (threshold : Nat) (receiver load : object.Vertex)
    (coordinate : Coordinate object support) :
    uSupported object support threshold receiver load coordinate = true ↔
      USupported object support threshold receiver load coordinate := by
  simp [uSupported]

@[simp] theorem kind_d1 (coordinate : D1.Coordinate object support) :
    kind object support (.d1 coordinate) = .boundaryDegree := rfl

@[simp] theorem value_d1 (coordinate : D1.Coordinate object support) :
    value object support (.d1 coordinate) = D1.value object support coordinate := rfl

@[simp] theorem declaredSupport_d1
    (coordinate : D1.Coordinate object support) :
    declaredSupport object support (.d1 coordinate) =
      D1.declaredSupport object support coordinate := rfl

@[simp] theorem uSupported_d1
    (threshold : Nat) (receiver load : object.Vertex)
    (coordinate : D1.Coordinate object support) :
    uSupported object support threshold receiver load (.d1 coordinate) =
      D1.uSupported object support threshold receiver load coordinate := by
  simp [uSupported, D1.uSupported, USupported]

@[simp] theorem kind_d2ReturnLength (coordinate : D2.Coordinate object) :
    kind object support (.d2ReturnLength coordinate) = .returnData := rfl

@[simp] theorem value_d2ReturnLength (coordinate : D2.Coordinate object) :
    value object support (.d2ReturnLength coordinate) = D2.value object coordinate := rfl

@[simp] theorem declaredSupport_d2ReturnLength
    (coordinate : D2.Coordinate object) :
    declaredSupport object support (.d2ReturnLength coordinate) =
      D2.declaredSupport object coordinate := rfl

@[simp] theorem uSupported_d2ReturnLength
    (threshold : Nat) (receiver load : object.Vertex)
    (coordinate : D2.Coordinate object) :
    uSupported object support threshold receiver load (.d2ReturnLength coordinate) =
      D2.uSupported object support threshold receiver load coordinate := by
  simp [uSupported, D2.uSupported, USupported]

@[simp] theorem kind_d3WindowLabel (coordinate : D3.Coordinate object support) :
    kind object support (.d3WindowLabel coordinate) = .windowLabel := rfl

@[simp] theorem value_d3WindowLabel (coordinate : D3.Coordinate object support) :
    value object support (.d3WindowLabel coordinate) =
      D3.value object support coordinate := rfl

@[simp] theorem declaredSupport_d3WindowLabel
    (coordinate : D3.Coordinate object support) :
    declaredSupport object support (.d3WindowLabel coordinate) =
      D3.declaredSupport object support coordinate := rfl

@[simp] theorem uSupported_d3WindowLabel
    (threshold : Nat) (receiver load : object.Vertex)
    (coordinate : D3.Coordinate object support) :
    uSupported object support threshold receiver load (.d3WindowLabel coordinate) =
      D3.uSupported object support threshold receiver load coordinate := by
  simp [uSupported, D3.uSupported, USupported]

@[simp] theorem kind_d4RawCurvature
    (coordinate : D4.Coordinate object support) :
    kind object support (.d4RawCurvature coordinate) = .rawCurvature := rfl

@[simp] theorem value_d4RawCurvature
    (coordinate : D4.Coordinate object support) :
    value object support (.d4RawCurvature coordinate) = () := rfl

@[simp] theorem declaredSupport_d4RawCurvature
    (coordinate : D4.Coordinate object support) :
    declaredSupport object support (.d4RawCurvature coordinate) =
      D4.declaredSupport object support coordinate := rfl

@[simp] theorem event?_d4RawCurvature (LengthOK : Nat → Prop)
    (coordinate : D4.Coordinate object support) :
    event? object support LengthOK (.d4RawCurvature coordinate) =
      D4.event? object support LengthOK coordinate := rfl

@[simp] theorem uSupported_d4RawCurvature
    (threshold : Nat) (receiver load : object.Vertex)
    (coordinate : D4.Coordinate object support) :
    uSupported object support threshold receiver load (.d4RawCurvature coordinate) =
      D4.uSupported object support threshold receiver load coordinate := by
  simp [uSupported, D4.uSupported, USupported]

end Base

end Hypostructure.Graph.TraceCoordinateSystem
