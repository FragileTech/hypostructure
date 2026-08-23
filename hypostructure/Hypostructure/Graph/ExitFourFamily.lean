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

end Hypostructure.Graph.ExitFour
