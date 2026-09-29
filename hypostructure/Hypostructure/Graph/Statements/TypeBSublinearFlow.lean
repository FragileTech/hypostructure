import Hypostructure.Graph.Statements.TypeBSublinearGaps

/-!
# Statements: ports, flow values and the size profile of the Type B sublinear failure
(keys 8309--8313)
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

section Flow

variable (data : Parameters) (object : Graph.FiniteObject.{u})

/-- **Fact (key 8309)** (gap H05): the ports of a receiver are window stubs.  For
a receiver of a canonical piece sitting at the baseline, `missingPorts` is the
number of its incidences leaving the remainder `R(P₀)` (its neighbours in `R(P₀)`
lie in its piece), and the positive deficiency of the piece is the sum of its
receivers' ports. -/
def ReceiverPortsAreWindowStubsStatement : Prop :=
  ∀ component ∈ object.canonicalPieces
      (object.remainderSupport (canonicalWindowPacking data object)),
    (∀ receiver : object.Vertex,
      object.IsReceiver
        (object.pieceSupport
          (object.remainderSupport (canonicalWindowPacking data object)) component)
        data.threshold receiver →
      object.degree receiver = data.threshold →
      object.missingPorts
          (object.pieceSupport
            (object.remainderSupport (canonicalWindowPacking data object)) component)
          data.threshold receiver =
        object.degree receiver -
          object.internalDegree
            (object.remainderSupport (canonicalWindowPacking data object)) receiver) ∧
    object.positiveDeficiency
        (object.pieceSupport
          (object.remainderSupport (canonicalWindowPacking data object)) component)
        data.threshold =
      ∑ receiver ∈ object.receivers
          (object.pieceSupport
            (object.remainderSupport (canonicalWindowPacking data object)) component)
          data.threshold,
        object.missingPorts
          (object.pieceSupport
            (object.remainderSupport (canonicalWindowPacking data object)) component)
          data.threshold receiver

/-- **Fact (key 8310)** (gap H05): the structure of a saturated receiver.  A
saturated receiver of a canonical piece has a trace basin of at least
`s · missingPorts` full vertices, each a vertex of the piece spending the whole
baseline inside it and tracing to the receiver. -/
def SaturatedReceiverBasinStatement : Prop :=
  ∀ component ∈ object.canonicalPieces
      (object.remainderSupport (canonicalWindowPacking data object)),
    ∀ receiver : object.Vertex,
      object.IsReceiver
        (object.pieceSupport
          (object.remainderSupport (canonicalWindowPacking data object)) component)
        data.threshold receiver →
      object.Saturated
        (object.pieceSupport
          (object.remainderSupport (canonicalWindowPacking data object)) component)
        data.threshold data.dischargeScale receiver →
      data.dischargeScale *
          object.missingPorts
            (object.pieceSupport
              (object.remainderSupport (canonicalWindowPacking data object)) component)
            data.threshold receiver ≤
        (object.routedLoads
          (object.pieceSupport
            (object.remainderSupport (canonicalWindowPacking data object)) component)
          data.threshold receiver).card ∧
      ∀ vertex ∈ object.routedLoads
          (object.pieceSupport
            (object.remainderSupport (canonicalWindowPacking data object)) component)
          data.threshold receiver,
        vertex ∈ object.pieceSupport
            (object.remainderSupport (canonicalWindowPacking data object)) component ∧
          object.internalDegree
              (object.pieceSupport
                (object.remainderSupport (canonicalWindowPacking data object))
                component) vertex = data.threshold ∧
          object.TraceTo
            (object.pieceSupport
              (object.remainderSupport (canonicalWindowPacking data object)) component)
            data.threshold vertex receiver

open scoped Classical in
/-- **Fact (key 8311)** (gap H07, load network): the value of the load network.
With routing landing outside `excluded`, the flat vertices are exactly the total
load (`Σ_w L(w) = #flat`), so if every receiver outside `excluded` is unsaturated
the flow of flat vertices plus the number of receivers is at most the cut
`s · Σ_w missingPorts(w)`. -/
def LoadFlowValueStatement : Prop :=
  ∀ piece excluded : Finset object.Vertex,
    (∀ vertex ∈ piece \ excluded,
      object.internalDegree piece vertex = data.threshold →
      ∃ receiver : object.Vertex,
        object.traceReceiver? piece data.threshold vertex = some receiver ∧
          object.IsReceiver piece data.threshold receiver ∧
            receiver ∉ excluded) →
    (∀ receiver ∈ object.receivers piece data.threshold \ excluded,
      1 + object.restrictedLoad piece excluded data.threshold receiver ≤
        data.dischargeScale * object.missingPorts piece data.threshold receiver) →
    ((piece \ excluded).filter fun vertex =>
        object.internalDegree piece vertex = data.threshold).card +
      (object.receivers piece data.threshold \ excluded).card ≤
    data.dischargeScale *
      ∑ receiver ∈ object.receivers piece data.threshold \ excluded,
        object.missingPorts piece data.threshold receiver

open scoped Classical in
/-- **Fact (key 8312)** (gap H07, cover network): the value of the cover network.
The absorbed cardinalities are at most the closed counts plus the number of
unpaid absorbed vertices, an absorbed core has at most two vertices, and cover
holds when nothing is unpaid. -/
def CoverFlowValueStatement : Prop :=
  let handoffPieces := (object.canonicalPieces
      (object.remainderSupport (canonicalWindowPacking data object))).filter
      (TypeBGroupedHandoffPiece data object)
  let absorbed := fun component : Graph.SupportComponents.Connected.Component object
      (object.remainderSupport (canonicalWindowPacking data object)) =>
    canonicalGroupedAbsorbedCore data object
      (object.pieceSupport
        (object.remainderSupport (canonicalWindowPacking data object)) component)
  let unpaid := (handoffPieces.biUnion absorbed).filter fun vertex =>
    ∀ centre ∈ canonicalGroupedCentres data object,
      vertex ∉ Graph.TypeBFanIncidence.closedNeighbours object data.threshold
        (typeBFanEnvelope (canonicalGroupedBridgeUnion data object)
          (canonicalGroupedCentres data object) centre) centre
  (∑ component ∈ handoffPieces, (absorbed component).card ≤
      ∑ centre ∈ canonicalGroupedCentres data object,
        Graph.TypeBFanIncidence.closedCount object data.threshold
          (typeBFanEnvelope (canonicalGroupedBridgeUnion data object)
            (canonicalGroupedCentres data object) centre) centre +
        unpaid.card) ∧
    (unpaid = ∅ → TypeBSublinearCoverArm data object) ∧
    (∀ component ∈ handoffPieces, (absorbed component).card ≤ 2) ∧
    unpaid.card ≤ 2 * handoffPieces.card

/-- **Fact (key 8313)** (gap B01): the component size profile of the remainder.
The canonical pieces partition `R(P₀)`, every piece has a receiver, hence a
positive deficiency, so the number of pieces is at most `def⁺(R(P₀))`. -/
def PieceSizeProfileStatement : Prop :=
  (∑ component ∈ object.canonicalPieces
      (object.remainderSupport (canonicalWindowPacking data object)),
      (object.pieceSupport
        (object.remainderSupport (canonicalWindowPacking data object))
        component).card =
    (object.remainderSupport (canonicalWindowPacking data object)).card) ∧
  (∀ component ∈ object.canonicalPieces
      (object.remainderSupport (canonicalWindowPacking data object)),
    ∃ receiver, object.IsReceiver
      (object.pieceSupport
        (object.remainderSupport (canonicalWindowPacking data object)) component)
      data.threshold receiver) ∧
  (object.canonicalPieces
      (object.remainderSupport (canonicalWindowPacking data object))).card ≤
    object.positiveDeficiency
      (object.remainderSupport (canonicalWindowPacking data object)) data.threshold

end Flow

end Hypostructure.Graph.Strategy.Spine
