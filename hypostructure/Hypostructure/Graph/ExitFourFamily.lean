import Hypostructure.Graph.TypeAVisibleResponseAssembly
import Hypostructure.Graph.Route8Census
import Hypostructure.Graph.DecoratedHandoffEnvelope

/-!
# The canonical exit-(4) quotient family

This file implements `def:typeA-exit4-family` literally.  A family member is
one of the five constructions Q1--Q5 listed by the manuscript.  There is no
caller-provided coordinate universe, generation predicate, or detached pair of
boundary pieces: every quotient and its declared routed-load support are
computed from the graph data owned by its clause.
-/

namespace Hypostructure.Graph.ExitFour

open Hypostructure

universe u

variable {object : FiniteObject.{u}}

attribute [local instance] vertexDecEq

/-- The five and only five constructions in `def:typeA-exit4-family`. -/
inductive ReceiverClause where
  | visibleEntry
  | silentBasin
  | traceBasin
  | continuationSwitch
  | carrierDeletion
  deriving DecidableEq, Repr

/-! ## Q1: visible receiver-entry identification -/

/-- The response piece carried by an actual visible receiver-entry coordinate.
All interface incidences are retained; the internal response is the selected
receiver-entry channel. -/
noncomputable def visibleResponsePiece
    {support : Finset object.Vertex} {receiver : object.Vertex}
    (coordinate : VisibleEntry.ResponseCoordinate object support receiver) :
    BoundaryPiece
      (Strategy.InterfaceReplacement.SupportAtom.boundary object support) :=
  Route8.PresentedEntry.retainedBasinPiece object support
    coordinate.channel.support.toFinset

/-- Visible response pieces lie in the selected support's exact boundary-degree
fibre. -/
theorem visibleResponsePiece_boundaryDegreeProfile
    {support : Finset object.Vertex} {receiver : object.Vertex}
    (coordinate : VisibleEntry.ResponseCoordinate object support receiver) :
    (visibleResponsePiece coordinate).boundaryDegreeProfile =
      (Strategy.InterfaceReplacement.SupportAtom.piece object
        support).boundaryDegreeProfile :=
  Route8.PresentedEntry.retainedBasinPiece_boundaryDegreeProfile object support
    coordinate.channel.support.toFinset

/-- **The selected receiver-entry channel is a path of its own visible
response piece**, between the entry label and the receiver label, of the
channel's own length: `def:typeA-channel-spectrum`'s `Q` read on the retained
reading. -/
theorem exists_visibleResponsePiece_channelPath
    {support : Finset object.Vertex} {receiver : object.Vertex}
    (coordinate : VisibleEntry.ResponseCoordinate object support receiver) :
    ∃ q : (visibleResponsePiece coordinate).graph.Walk
        (Sum.inl coordinate.entry)
        (Sum.inl coordinate.receiverBoundary),
      q.IsPath ∧ q.length = coordinate.channel.length := by
  classical
  obtain ⟨q, qPath, qLength⟩ :=
    Route8.PresentedEntry.exists_retainedBasinPiece_path_of_channel object
      support coordinate.channel.support.toFinset coordinate.channel
      coordinate.isChannel.1 coordinate.isChannel.2
      (fun vertex member => List.mem_toFinset.mpr member)
  have startEq : Route8.PresentedEntry.pieceEncode object support
        coordinate.entry.1
        (coordinate.isChannel.2 coordinate.entry.1
          coordinate.channel.start_mem_support) =
      Sum.inl coordinate.entry := by
    exact Route8.PresentedEntry.pieceEncode_of_mem_cutBoundary object support
      coordinate.entry.1 _ coordinate.entry.2
  have endEq : Route8.PresentedEntry.pieceEncode object support receiver
        (coordinate.isChannel.2 receiver
          coordinate.channel.end_mem_support) =
      Sum.inl coordinate.receiverBoundary := by
    exact Route8.PresentedEntry.pieceEncode_of_mem_cutBoundary object support
      receiver _ coordinate.receiverBoundary.2
  refine ⟨q.copy startEq endEq, ?_, ?_⟩
  · exact (SimpleGraph.Walk.isPath_copy q startEq endEq).mpr qPath
  · exact (SimpleGraph.Walk.length_copy q startEq endEq).trans qLength

/-- Q1, with the pair and both response realizations derived from one selected
visible-four package.  The declared support is exactly the two loads whose
coordinates are identified. -/
structure Q1TargetDefect (Target : FiniteObject.{u} → Prop)
    (support : Finset object.Vertex) (threshold scale : Nat)
    (receiver load : object.Vertex) where
  originPeeled : Finset object.Vertex
  package : VisibleFourUnpeeledPackage support threshold scale receiver
    originPeeled
  pair : package.Q1OriginPair
  supports : load = pair.left.1 ∨ load = pair.right.1
  targetDefect : Response.TargetDefect Target
    (visibleResponsePiece pair.leftResponseCoordinate)
    (visibleResponsePiece pair.rightResponseCoordinate)

/-! ## Q2: the whole silent/excess basin -/

/-- `B(w)`: the exact excess loads, their canonical traces to `w`, and `w`.
The cut interface of this support is the completion-port boundary datum named
by the manuscript. -/
noncomputable def excessTraceSupport (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold scale : Nat)
    (receiver : object.Vertex) (peeled : Finset object.Vertex) :
    Finset object.Vertex := by
  classical
  let excess := unpeeledExcess support threshold scale receiver peeled
  exact insert receiver
    (excess ∪ excess.biUnion fun routed =>
      (Route8.TraceBasin.traceSeed? object support threshold receiver routed).getD ∅)

/-- The literal boundary response of `B(w)`: all boundary incidences and no
internal response coordinate. -/
noncomputable def excessBoundaryResponse (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold scale : Nat)
    (receiver : object.Vertex) (peeled : Finset object.Vertex) :
    BoundaryPiece
      (Strategy.InterfaceReplacement.SupportAtom.boundary object
        (excessTraceSupport object support threshold scale receiver peeled)) :=
  Route8.PresentedEntry.retainedBasinPiece object
    (excessTraceSupport object support threshold scale receiver peeled) ∅

/-- Q2, the target-defective replacement of the whole silent/excess basin.
The chosen load belongs to the exact visible-first excess, which is Q2's
declared routed-load support. -/
structure Q2TargetDefect (Target : FiniteObject.{u} → Prop)
    (support : Finset object.Vertex) (threshold scale : Nat)
    (receiver load : object.Vertex) where
  originPeeled : Finset object.Vertex
  silent : SilentUnpeeledExcessAt support threshold scale receiver originPeeled
  supports : load ∈ unpeeledExcess support threshold scale receiver originPeeled
  basin_subset :
    excessTraceSupport object support threshold scale receiver originPeeled ⊆
      support
  connected : SupportComponents.Connected.ConnectedOn object
    (excessTraceSupport object support threshold scale receiver originPeeled)
  proper : ∃ vertex,
    vertex ∉ excessTraceSupport object support threshold scale receiver
      originPeeled
  targetDefect : Response.TargetDefect Target
    (excessBoundaryResponse object support threshold scale receiver originPeeled)
    (Strategy.InterfaceReplacement.SupportAtom.piece object
      (excessTraceSupport object support threshold scale receiver originPeeled))

/-! ## Q3: a trace-local quotient -/

/-- The omitted trace coordinate is genuinely support-internal, exactly the
nontriviality test in `def:typeA-trace-basin`. -/
def TraceCoordinateInternal (object : FiniteObject.{u})
    (support basin : Finset object.Vertex) (threshold : Nat)
    (receiver load : object.Vertex)
    (coordinate : Route8.PresentedEntry.TraceCoordinate object support) : Prop :=
  (coordinate = .traceIncidence ∧
      ∃ trace : object.graph.Path load receiver,
        object.tracePath? support threshold load receiver = some trace ∧
          0 < trace.1.length ∧ trace.1.support.toFinset ⊆ basin) ∨
    (∃ vertex ∈ Route8.PresentedEntry.traceDeclaredSupport object support
        threshold receiver load coordinate,
      vertex ∈ basin ∧
        vertex ∉ Strategy.InterfaceReplacement.SupportAtom.cutBoundary object
          basin) ∨
    ∃ left ∈ Route8.PresentedEntry.traceDeclaredSupport object support threshold
        receiver load coordinate,
      ∃ right ∈ Route8.PresentedEntry.traceDeclaredSupport object support
          threshold receiver load coordinate,
        left ∈ basin ∧ right ∈ basin ∧ object.graph.Adj left right

/-- Q3, represented by an actual retained subset of the selected load's
declared trace-coordinate family. -/
structure Q3TargetDefect (Target : FiniteObject.{u} → Prop)
    (support : Finset object.Vertex) (threshold : Nat)
    (receiver load : object.Vertex) where
  LengthOK : Nat → Prop
  target_eq : Target = HasCycleWithLength LengthOK
  basin : Finset object.Vertex
  selected : Route8.TraceBasin.select? object support threshold receiver load =
    some basin
  retained : Finset (Route8.PresentedEntry.TraceCoordinate object support)
  retained_subset : retained ⊆
    Route8.PresentedEntry.traceCoordinates object support threshold receiver load
  nontrivial : ∃ changed ∈
      Route8.PresentedEntry.traceCoordinates object support threshold receiver load,
    changed ∉ retained ∧
      TraceCoordinateInternal object support basin threshold receiver load changed
  targetDefect : Response.TargetDefect Target
    (Route8.PresentedEntry.retainedReading object support basin threshold LengthOK
      (Route8.PresentedEntry.retainedBaseCoordinates object support retained))
    (Strategy.InterfaceReplacement.SupportAtom.piece object basin)

/-! ## Q4: continuation/cubic-switch quotient -/

/-- The finite family `K` of routed loads whose declared connector coordinates
are tested by continuation routing. -/
structure ContinuationFamily (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (receiver : object.Vertex) where
  outside : object.Vertex
  loads : Finset object.Vertex
  loads_routed : loads ⊆ object.routedLoads support threshold receiver
  germ : ∀ routed, routed ∈ loads →
    DecoratedHandoff.RootedGerm object support receiver outside

/-- Q4, with an actual separating pair in the finite connector family and the
switch reading produced from that separation. -/
structure Q4TargetDefect (Target : FiniteObject.{u} → Prop)
    (support : Finset object.Vertex) (threshold : Nat)
    (receiver load : object.Vertex) where
  family : ContinuationFamily object support threshold receiver
  supports : load ∈ family.loads
  leftLoad : object.Vertex
  rightLoad : object.Vertex
  leftMem : leftLoad ∈ family.loads
  rightMem : rightLoad ∈ family.loads
  distinct : leftLoad ≠ rightLoad
  separation : DecoratedHandoff.Separation object support receiver family.outside
  leftPath : separation.left.path = (family.germ leftLoad leftMem).path
  rightPath : separation.right.path = (family.germ rightLoad rightMem).path
  reading : DecoratedHandoff.SwitchReading separation
  internal : separation.separator ∉
    Strategy.InterfaceReplacement.SupportAtom.cutBoundary object
      separation.switchSupport
  targetDefect : Response.TargetDefect Target reading.quotient reading.full

/-! ## Q5: essential-incidence deletion in the exact route-8 census -/

/-- The graph-derived reading of the selected census entry. -/
noncomputable def q5Presented (object : FiniteObject.{u}) (threshold : Nat)
    (LengthOK : Nat → Prop) (index : Route8Census.Index object) :=
  Route8Census.presented object threshold LengthOK index

/-- The carrier presentation of that same reading. -/
noncomputable def q5Entry (object : FiniteObject.{u}) (threshold : Nat)
    (LengthOK : Nat → Prop) (index : Route8Census.Index object) :=
  (q5Presented object threshold LengthOK index).toEntry
    (HasCycleWithLength LengthOK)

/-- Its canonical essential-incidence core. -/
noncomputable def q5Core (object : FiniteObject.{u}) (threshold : Nat)
    (LengthOK : Nat → Prop) (index : Route8Census.Index object) :=
  Route8Census.core object threshold LengthOK index

/-- The Q5 reading after deleting one essential incidence. -/
noncomputable def q5DeletedReading (object : FiniteObject.{u}) (threshold : Nat)
    (LengthOK : Nat → Prop) (index : Route8Census.Index object)
    (carrier : Sym2 object.Vertex) :=
  (q5Entry object threshold LengthOK index).restriction
    ((q5Core object threshold LengthOK index).erase carrier)

/-- The undeleted essential-core reading. -/
noncomputable def q5CoreReading (object : FiniteObject.{u}) (threshold : Nat)
    (LengthOK : Nat → Prop) (index : Route8Census.Index object) :=
  (q5Entry object threshold LengthOK index).restriction
    (q5Core object threshold LengthOK index)

/-- The deletion witness records an actual forgotten declared coordinate whose
carrier support uses the deleted incidence. -/
def Q5DeclaredWitness (object : FiniteObject.{u}) (threshold : Nat)
    (LengthOK : Nat → Prop) (index : Route8Census.Index object)
    (carrier : Sym2 object.Vertex) : Prop :=
  ∃ coordinate ∈ (q5Presented object threshold LengthOK index).coordinates,
    (q5Presented object threshold LengthOK index).car coordinate ⊆
        q5Core object threshold LengthOK index ∧
      carrier ∈ (q5Presented object threshold LengthOK index).car coordinate

/-- The ambient collection in Q5 is either the full negative zero-surplus
census or the complete indexed-entry family of a canonical negative
zero-surplus component subcollection. -/
def Q5CanonicalCollection (object : FiniteObject.{u})
    (packing : Finset (Finset object.Vertex)) (threshold scale : Nat)
    (collection : Finset (Route8Census.Index object)) : Prop :=
  collection = Route8Census.entries object packing threshold scale ∨
    ∃ components : Finset (SupportComponents.Connected.Component object
        (object.remainderSupport packing)),
      components ⊆ object.canonicalPieces (object.remainderSupport packing) ∧
      (∀ component ∈ components,
        let piece := object.pieceSupport (object.remainderSupport packing)
          component
        object.NegativeNetCharge piece threshold scale ∧
          object.ambientSurplus piece threshold = 0) ∧
      collection = Route8Census.entriesOfComponents object packing components
        threshold scale

/-- Q5 on the concrete object-level census.  The ambient collection consists
of actual `(X,w,u)` indices from the unified Type A census; the selected entry
is the exact `(support,receiver,load)` tuple, its private-core condition is the
paper's `pi <= delta-1` (two at the registered baseline), and both realizations
are the canonical essential-core restrictions of its graph-derived reading. -/
def Q5TargetDefect (Target : FiniteObject.{u} → Prop)
    (support : Finset object.Vertex) (threshold scale : Nat)
    (receiver load : object.Vertex) : Prop :=
  ∃ packing : Finset (Finset object.Vertex),
    ∃ collection : Finset (Route8Census.Index object),
      Q5CanonicalCollection object packing threshold scale collection ∧
      ∃ index ∈ collection,
        index.1 = support ∧ index.2.1 = receiver ∧ index.2.2 = load ∧
        ∃ LengthOK : Nat → Prop,
          Target = HasCycleWithLength LengthOK ∧
          Route8.TraceBasin.select? object index.1 threshold index.2.1
              index.2.2 = some (Route8Census.basin object threshold index) ∧
          Route8.IndexedTwoCarrierCore collection
              (q5Core object threshold LengthOK) (threshold - 1) index ∧
          ∃ carrier ∈ q5Core object threshold LengthOK index,
            Response.TargetDefect Target
                (q5DeletedReading object threshold LengthOK index carrier)
                (q5CoreReading object threshold LengthOK index) ∧
            (q5DeletedReading object threshold LengthOK index carrier).boundaryDegreeProfile =
                (q5CoreReading object threshold LengthOK index).boundaryDegreeProfile ∧
            Q5DeclaredWitness object threshold LengthOK index carrier

/-! ## The closed family and peeling witness -/

/-- A member of `Q_4(w)` is definitionally one of Q1--Q5. -/
inductive CanonicalMember (Target : FiniteObject.{u} → Prop)
    (support : Finset object.Vertex) (threshold scale : Nat)
    (receiver load : object.Vertex) : Type (u + 1) where
  | q1 : Q1TargetDefect Target support threshold scale receiver load →
      CanonicalMember Target support threshold scale receiver load
  | q2 : Q2TargetDefect Target support threshold scale receiver load →
      CanonicalMember Target support threshold scale receiver load
  | q3 : Q3TargetDefect Target support threshold receiver load →
      CanonicalMember Target support threshold scale receiver load
  | q4 : Q4TargetDefect Target support threshold receiver load →
      CanonicalMember Target support threshold scale receiver load
  | q5 : Q5TargetDefect Target support threshold scale receiver load →
      CanonicalMember Target support threshold scale receiver load

namespace CanonicalMember

/-- Read which manuscript clause generated a closed family member. -/
def clause {Target : FiniteObject.{u} → Prop}
    {support : Finset object.Vertex} {threshold scale : Nat}
    {receiver load : object.Vertex} :
    CanonicalMember Target support threshold scale receiver load → ReceiverClause
  | .q1 _ => .visibleEntry
  | .q2 _ => .silentBasin
  | .q3 _ => .traceBasin
  | .q4 _ => .continuationSwitch
  | .q5 _ => .carrierDeletion

end CanonicalMember

/-- `def:typeA-exit4-peeling`: one unpeeled routed load together with the exact
canonical target-defective quotient whose declared support contains it. -/
structure Witness (Target : FiniteObject.{u} → Prop)
    (support : Finset object.Vertex) (threshold scale : Nat)
    (receiver : object.Vertex) (peeled : Finset object.Vertex) where
  load : object.Vertex
  unpeeled : load ∈ unpeeledLoads support threshold receiver peeled
  member : CanonicalMember Target support threshold scale receiver load

namespace Witness

variable {Target : FiniteObject.{u} → Prop}
variable {support : Finset object.Vertex} {threshold scale : Nat}
variable {receiver : object.Vertex} {peeled : Finset object.Vertex}

/-- Construct the Q5 peeling witness from the exact census deletion datum. -/
def ofCarrierDeletion {load : object.Vertex}
    (unpeeled : load ∈ unpeeledLoads support threshold receiver peeled)
    (datum : Q5TargetDefect Target support threshold scale receiver load) :
    Witness Target support threshold scale receiver peeled where
  load := load
  unpeeled := unpeeled
  member := .q5 datum

/-- A committed no-exit-(4) fact rules out the exact Q5 datum for an eligible
load. -/
theorem carrierDeletion_contradicts_noExitFour
    {eligible : object.Vertex → Prop}
    (noExitFour : ¬ ∃ witness :
      Witness Target support threshold scale receiver peeled,
        eligible witness.load)
    {load : object.Vertex}
    (unpeeled : load ∈ unpeeledLoads support threshold receiver peeled)
    (datum : Q5TargetDefect Target support threshold scale receiver load)
    (eligibleLoad : eligible load) : False :=
  noExitFour ⟨ofCarrierDeletion unpeeled datum, eligibleLoad⟩

theorem routed
    (witness : Witness Target support threshold scale receiver peeled) :
    witness.load ∈ object.routedLoads support threshold receiver :=
  ((mem_unpeeledLoads (object := object) support threshold receiver).mp
    witness.unpeeled).1

theorem fresh
    (witness : Witness Target support threshold scale receiver peeled) :
    witness.load ∉ peeled :=
  ((mem_unpeeledLoads (object := object) support threshold receiver).mp
    witness.unpeeled).2

noncomputable def nextPeeled
    (witness : Witness Target support threshold scale receiver peeled) :
    Finset object.Vertex :=
  Finset.cons witness.load peeled witness.fresh

theorem nextPeeled_subset_routedLoads
    (witness : Witness Target support threshold scale receiver peeled)
    (inside : peeled ⊆ object.routedLoads support threshold receiver) :
    witness.nextPeeled ⊆ object.routedLoads support threshold receiver := by
  intro vertex member
  simp [nextPeeled] at member
  rcases member with rfl | member
  · exact witness.routed
  · exact inside member

theorem residualLoad_nextPeeled
    (witness : Witness Target support threshold scale receiver peeled) :
    residualLoad support threshold receiver witness.nextPeeled + 1 =
      residualLoad support threshold receiver peeled := by
  classical
  simpa [nextPeeled] using
    residualLoad_insert support threshold receiver witness.unpeeled

end Witness

/-! ## Witnessed peeling sets -/

def PeeledByWitnesses (Target : FiniteObject.{u} → Prop)
    (support : Finset object.Vertex) (threshold scale : Nat)
    (receiver : object.Vertex) (peeled : Finset object.Vertex) : Prop :=
  ∀ load ∈ peeled, ∃ prior : Finset object.Vertex, prior ⊆ peeled ∧
    ∃ witness : Witness Target support threshold scale receiver prior,
      witness.load = load

theorem peeledByWitnesses_empty (Target : FiniteObject.{u} → Prop)
    (support : Finset object.Vertex) (threshold scale : Nat)
    (receiver : object.Vertex) :
    PeeledByWitnesses Target support threshold scale receiver ∅ :=
  fun _load member => absurd member (Finset.notMem_empty _)

theorem peeledByWitnesses_nextPeeled
    {Target : FiniteObject.{u} → Prop}
    {support : Finset object.Vertex} {threshold scale : Nat}
    {receiver : object.Vertex} {peeled : Finset object.Vertex}
    (witnessed :
      PeeledByWitnesses Target support threshold scale receiver peeled)
    (witness : Witness Target support threshold scale receiver peeled) :
    PeeledByWitnesses Target support threshold scale receiver
      witness.nextPeeled := by
  intro load member
  have member' : load = witness.load ∨ load ∈ peeled := by
    simpa [Witness.nextPeeled] using member
  rcases member' with rfl | member'
  · exact ⟨peeled, Finset.subset_cons _, witness, rfl⟩
  · obtain ⟨prior, priorSubset, witness', equal⟩ := witnessed load member'
    exact ⟨prior, priorSubset.trans (Finset.subset_cons _), witness', equal⟩


/-! ## The Q2 semantic step

`lem:typeA-unpeeled-silent-routing`, after the visible loads are exhausted: the
whole silent/excess basin `B(w)` is one boundaried response state, and its
identification with the ambient piece is target-defective — exit `(4)` through
a Q2 quotient supported on the residual excess — or target-complete, the
identification entering exits `(5)`–`(8)`. -/

/-- An unpeeled excess load is an unpeeled routed load. -/
theorem unpeeledExcess_subset_unpeeledLoads
    (support : Finset object.Vertex) (threshold scale : Nat)
    (receiver : object.Vertex) (peeled : Finset object.Vertex) :
    unpeeledExcess support threshold scale receiver peeled ⊆
      unpeeledLoads support threshold receiver peeled :=
  Finset.sdiff_subset

/-- **The Q2 exit-(4) witness of a target-defective excess basin**
(`lem:typeA-unpeeled-silent-routing`, the exit-(4) sentence): a compatible
outside context distinguishing the basin's literal boundary response from the
basin itself makes the replacement quotient target-defective of type (Q2), and
its declared routed-load support is the residual excess. -/
def witnessOfExcessTargetDefect {Target : FiniteObject.{u} → Prop}
    {support : Finset object.Vertex} {threshold scale : Nat}
    {receiver : object.Vertex} {peeled : Finset object.Vertex}
    (silent : SilentUnpeeledExcessAt support threshold scale receiver peeled)
    {load : object.Vertex}
    (excessMember : load ∈ unpeeledExcess support threshold scale receiver
      peeled)
    (basin_subset :
      excessTraceSupport object support threshold scale receiver peeled ⊆
        support)
    (connected : SupportComponents.Connected.ConnectedOn object
      (excessTraceSupport object support threshold scale receiver peeled))
    (proper : ∃ vertex,
      vertex ∉ excessTraceSupport object support threshold scale receiver
        peeled)
    (targetDefect : Response.TargetDefect Target
      (excessBoundaryResponse object support threshold scale receiver peeled)
      (Strategy.InterfaceReplacement.SupportAtom.piece object
        (excessTraceSupport object support threshold scale receiver peeled))) :
    Witness Target support threshold scale receiver peeled where
  load := load
  unpeeled := unpeeledExcess_subset_unpeeledLoads support threshold scale
    receiver peeled excessMember
  member := .q2 ⟨peeled, silent, excessMember, basin_subset, connected, proper,
    targetDefect⟩

/-- **The Q2 semantic dichotomy** (`lem:typeA-unpeeled-silent-routing`): at a
silent unpeeled excess state, either the excess basin's boundary response is
distinguished from the basin by a compatible outside context — and then the
state supplies an exit-(4) witness at one of its own residual excess loads —
or the identification is target-complete, entering exits `(5)`–`(8)`.  The
common boundary-degree fibre is
`retainedBasinPiece_boundaryDegreeProfile`; the exhaustiveness is
`lem:context-universality` (`Response.contextEquivalent_or_targetDefect`). -/
theorem exists_witness_or_excess_targetComplete
    {Target : FiniteObject.{u} → Prop}
    {support : Finset object.Vertex} {threshold scale : Nat}
    {receiver : object.Vertex} {peeled : Finset object.Vertex}
    (silent : SilentUnpeeledExcessAt support threshold scale receiver peeled)
    (basin_subset :
      excessTraceSupport object support threshold scale receiver peeled ⊆
        support)
    (connected : SupportComponents.Connected.ConnectedOn object
      (excessTraceSupport object support threshold scale receiver peeled))
    (proper : ∃ vertex,
      vertex ∉ excessTraceSupport object support threshold scale receiver
        peeled) :
    (∃ witness : Witness Target support threshold scale receiver peeled,
        witness.load ∈ unpeeledExcess support threshold scale receiver peeled) ∨
      Response.TargetComplete Graph.BoundaryPiece.boundaryDegreeProfile Target
        (excessBoundaryResponse object support threshold scale receiver peeled)
        (Strategy.InterfaceReplacement.SupportAtom.piece object
          (excessTraceSupport object support threshold scale receiver
            peeled)) := by
  classical
  rcases Response.contextEquivalent_or_targetDefect Target
      (excessBoundaryResponse object support threshold scale receiver peeled)
      (Strategy.InterfaceReplacement.SupportAtom.piece object
        (excessTraceSupport object support threshold scale receiver peeled)) with
    equivalent | targetDefect
  · refine Or.inr ⟨?_, equivalent⟩
    exact Route8.PresentedEntry.retainedBasinPiece_boundaryDegreeProfile object
      (excessTraceSupport object support threshold scale receiver peeled) _
  · obtain ⟨load, excessMember⟩ := silent.2.1
    exact Or.inl
      ⟨witnessOfExcessTargetDefect silent excessMember basin_subset connected
        proper targetDefect, excessMember⟩


/-! ## The excess basin's structural clauses

The Q2 dichotomy consumes three structural facts about `B(w)`: it lies inside
the support, it is connected — every excess load reaches the receiver along
its own canonical trace, and every seed vertex reaches it along the trace's
tail — and it is proper whenever the support is. -/

/-- Every vertex of a trace seed lies in the support. -/
theorem traceSeed_subset_support
    {support : Finset object.Vertex} {threshold : Nat}
    {receiver routed vertex : object.Vertex}
    (member : vertex ∈
      (Route8.TraceBasin.traceSeed? object support threshold receiver
        routed).getD ∅) :
    vertex ∈ support := by
  classical
  unfold Route8.TraceBasin.traceSeed? at member
  rcases selected : object.tracePath? support threshold routed receiver with
    _ | trace
  · rw [selected] at member
    simp at member
  · rw [selected] at member
    simp only [Option.getD_some] at member
    exact (object.isTracePath_of_tracePath?_eq_some selected).1 vertex
      (List.mem_toFinset.mp member)

/-- **`B(w)` lies inside the support.** -/
theorem excessTraceSupport_subset
    (support : Finset object.Vertex) (threshold scale : Nat)
    (receiver : object.Vertex) (peeled : Finset object.Vertex)
    (receiverInside : receiver ∈ support) :
    excessTraceSupport object support threshold scale receiver peeled ⊆
      support := by
  classical
  intro vertex member
  simp only [excessTraceSupport, Finset.mem_insert, Finset.mem_union,
    Finset.mem_biUnion] at member
  rcases member with rfl | inExcess | ⟨routed, _routedExcess, inSeed⟩
  · exact receiverInside
  · exact (object.mem_routedLoads.mp
      ((mem_unpeeledLoads (object := object) support threshold receiver).mp
        (unpeeledExcess_subset_unpeeledLoads support threshold scale receiver
          peeled inExcess)).1).1
  · exact traceSeed_subset_support inSeed

/-- **`B(w)` is proper whenever the support is.** -/
theorem excessTraceSupport_proper
    (support : Finset object.Vertex) (threshold scale : Nat)
    (receiver : object.Vertex) (peeled : Finset object.Vertex)
    (receiverInside : receiver ∈ support)
    (properSupport : ∃ vertex, vertex ∉ support) :
    ∃ vertex,
      vertex ∉ excessTraceSupport object support threshold scale receiver
        peeled :=
  let ⟨vertex, outside⟩ := properSupport
  ⟨vertex, fun member => outside
    (excessTraceSupport_subset support threshold scale receiver peeled
      receiverInside member)⟩

/-- **`B(w)` is connected through the receiver**: every excess load reaches
the receiver along its own canonical trace, and every seed vertex along the
trace's tail. -/
theorem excessTraceSupport_connectedOn
    (support : Finset object.Vertex) (threshold scale : Nat)
    (receiver : object.Vertex) (peeled : Finset object.Vertex) :
    SupportComponents.Connected.ConnectedOn object
      (excessTraceSupport object support threshold scale receiver peeled) := by
  classical
  have receiverMember : receiver ∈
      excessTraceSupport object support threshold scale receiver peeled := by
    simp [excessTraceSupport]
  have seedMember : ∀ routed ∈ unpeeledExcess support threshold scale receiver
      peeled, ∀ vertex ∈
        (Route8.TraceBasin.traceSeed? object support threshold receiver
          routed).getD ∅,
      vertex ∈ excessTraceSupport object support threshold scale receiver
        peeled := by
    intro routed routedExcess vertex member
    simp only [excessTraceSupport, Finset.mem_insert, Finset.mem_union,
      Finset.mem_biUnion]
    exact Or.inr (Or.inr ⟨routed, routedExcess, member⟩)
  have traceOf : ∀ routed ∈ unpeeledExcess support threshold scale receiver
      peeled, ∃ trace : object.graph.Path routed receiver,
        object.tracePath? support threshold routed receiver = some trace := by
    intro routed routedExcess
    have routedLoad := ((mem_unpeeledLoads (object := object) support threshold
      receiver).mp (unpeeledExcess_subset_unpeeledLoads support threshold scale
        receiver peeled routedExcess)).1
    exact Option.isSome_iff_exists.mp
      (object.isSome_tracePath?_of_traceTo
        (object.traceTo_of_traceReceiver?_eq_some
          (object.mem_routedLoads.mp routedLoad).2.2))
  have traceSeedOf : ∀ routed ∈ unpeeledExcess support threshold scale receiver
      peeled, ∀ trace : object.graph.Path routed receiver,
        object.tracePath? support threshold routed receiver = some trace →
      ∀ vertex ∈ trace.1.support,
        vertex ∈
          (Route8.TraceBasin.traceSeed? object support threshold receiver
            routed).getD ∅ := by
    intro routed _routedExcess trace selected vertex member
    unfold Route8.TraceBasin.traceSeed?
    rw [selected]
    simpa using member
  -- every basin vertex reaches the receiver by a walk inside the basin
  have toReceiver : ∀ vertex ∈
      excessTraceSupport object support threshold scale receiver peeled,
      ∃ walk : object.graph.Walk vertex receiver,
        ∀ v ∈ walk.support,
          v ∈ excessTraceSupport object support threshold scale receiver
            peeled := by
    intro vertex member
    have memberCases := member
    simp only [excessTraceSupport, Finset.mem_insert, Finset.mem_union,
      Finset.mem_biUnion] at memberCases
    rcases memberCases with rfl | inExcess | ⟨routed, routedExcess, inSeed⟩
    · refine ⟨SimpleGraph.Walk.nil, ?_⟩
      intro v vMember
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at vMember
      subst vMember
      exact receiverMember
    · obtain ⟨trace, selected⟩ := traceOf vertex inExcess
      refine ⟨trace.1, ?_⟩
      intro v vMember
      exact seedMember vertex inExcess v
        (traceSeedOf vertex inExcess trace selected v vMember)
    · obtain ⟨trace, selected⟩ := traceOf routed routedExcess
      have inTrace : vertex ∈ trace.1.support := by
        have inSeed' := inSeed
        unfold Route8.TraceBasin.traceSeed? at inSeed'
        rw [selected] at inSeed'
        simpa using inSeed'
      refine ⟨trace.1.dropUntil vertex inTrace, ?_⟩
      intro v vMember
      exact seedMember routed routedExcess v
        (traceSeedOf routed routedExcess trace selected v
          (SimpleGraph.Walk.support_dropUntil_subset_support trace.1 inTrace
            vMember))
  refine ⟨⟨receiver, receiverMember⟩, ?_⟩
  intro left right leftMember rightMember
  obtain ⟨walkLeft, walkLeftInside⟩ := toReceiver left leftMember
  obtain ⟨walkRight, walkRightInside⟩ := toReceiver right rightMember
  refine ⟨(walkLeft.append walkRight.reverse).bypass,
    SimpleGraph.Walk.bypass_isPath _, ?_⟩
  intro v vMember
  have vAppend : v ∈ (walkLeft.append walkRight.reverse).support :=
    SimpleGraph.Walk.support_bypass_subset_support _ vMember
  rcases (SimpleGraph.Walk.mem_support_append_iff walkLeft
      walkRight.reverse).mp vAppend with inLeft | inRight
  · exact walkLeftInside v inLeft
  · refine walkRightInside v ?_
    rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at inRight


/-! ## The rooted germ of a receiver-entry return

`def:typeA-continuation-classes`' germ `Γ = (x₀, …, x_g)` is the return's own
outside connector, rooted at the receiver: `w, h, x₁, …, x_g`.  Every field of
`DecoratedHandoff.RootedGerm` is read off the return's structure; the one
hypothesis is that the first entry is not the receiver itself, which is what
keeps the rooted list simple. -/

/-- **The rooted outside-connector germ of a receiver-entry return.** -/
noncomputable def germOfReturn {support : Finset object.Vertex}
    {threshold : Nat} {receiver outside : object.Vertex}
    (return' : VisibleEntry.ReceiverEntryReturn object support receiver outside)
    (port : outside ∈ VisibleEntry.completionPorts object support receiver)
    (receiverInside : receiver ∈ support)
    (entryFresh : return'.entry ≠ receiver) :
    DecoratedHandoff.RootedGerm object support receiver outside where
  path := receiver :: return'.connector.support
  chain := by
    refine (List.isChain_cons_iff _ _ _).mpr (Or.inr
      ⟨outside, return'.connector.support.tail, ?_, ?_, ?_⟩)
    · exact (VisibleEntry.mem_completionPorts.mp port).1
    · rw [SimpleGraph.Walk.cons_tail_support]
      exact SimpleGraph.Walk.isChain_adj_support return'.connector
    · exact (SimpleGraph.Walk.cons_tail_support return'.connector).symm
  nodup := by
    refine List.nodup_cons.mpr ⟨?_, ?_⟩
    · intro member
      exact return'.connectorOutside receiver member
        (fun equal => entryFresh equal.symm) receiverInside
    · have compositeNodup := return'.isPath.support_nodup
      rw [SimpleGraph.Walk.support_append] at compositeNodup
      exact (List.nodup_append.mp compositeNodup).1
  rooted := rfl
  issued := by
    show return'.connector.support.head? = some outside
    rw [← SimpleGraph.Walk.cons_tail_support return'.connector]
    rfl
  terminal := return'.entry
  terminal_last := by
    show (List.cons receiver return'.connector.support).getLast? =
      some return'.entry
    have step : (List.cons receiver return'.connector.support).getLast? =
        return'.connector.support.getLast? := by
      show ([receiver] ++ return'.connector.support).getLast? =
        return'.connector.support.getLast?
      exact List.getLast?_append_of_ne_nil _
        (SimpleGraph.Walk.support_ne_nil return'.connector)
    rw [step, List.getLast?_eq_some_getLast
      (h := SimpleGraph.Walk.support_ne_nil return'.connector)]
    exact congrArg some (SimpleGraph.Walk.getLast_support return'.connector)
  terminal_inside :=
    return'.isChannel.2 return'.entry return'.channel.start_mem_support
  interior := by
    intro vertex member inside
    by_contra fresh
    exact return'.connectorOutside vertex member fresh inside

@[simp] theorem germOfReturn_path {support : Finset object.Vertex}
    {threshold : Nat} {receiver outside : object.Vertex}
    (return' : VisibleEntry.ReceiverEntryReturn object support receiver outside)
    (port : outside ∈ VisibleEntry.completionPorts object support receiver)
    (receiverInside : receiver ∈ support)
    (entryFresh : return'.entry ≠ receiver) :
    (germOfReturn (threshold := threshold) return' port receiverInside
        entryFresh).path =
      receiver :: return'.connector.support :=
  rfl

end Hypostructure.Graph.ExitFour
