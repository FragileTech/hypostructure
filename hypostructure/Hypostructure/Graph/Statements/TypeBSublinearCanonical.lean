import Hypostructure.Graph.Statements.TypeBLanes

/-!
# Statements: the Type B sublinear hypotheses in G's canonical form

G audit of `TypeBSublinearOutcome` (keys 8300--8349).  The tested hypotheses
`TypeBSublinearHypotheses` (`prop:typeB-bridge-sublinear`) carry four existential
quantifiers (the handoff pieces, the grouped centres, the fan envelope map and
the absorbed-core map).  Each is pinned by an equation or an `↔` to G's own
canonical object, so none is free data; this module restates the hypotheses with
those objects substituted (no `∃` left), splits them into their four
independent arms, and states the exact decomposition of their failure.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

section Canonical

variable (data : Parameters) (object : Graph.FiniteObject.{u})

/-- Arm (i) of the sublinear hypotheses: every negative positive-surplus canonical
piece of `R(P₀)` is a bridge-residual component. -/
def TypeBSublinearBridgeArm : Prop :=
  ∀ component ∈ object.canonicalPieces
      (object.remainderSupport (canonicalWindowPacking data object)),
    let piece := object.pieceSupport
      (object.remainderSupport (canonicalWindowPacking data object)) component
    object.NegativeNetCharge piece data.threshold data.dischargeScale →
    0 < object.ambientSurplus piece data.threshold →
    Graph.TypeBEnvelopeCharge.BridgeResidualComponentAt object piece
      data.threshold data.dischargeScale

/-- Arm (ii): the grouped centres `H_𝔠` of G (the canonical surviving separators of
the decorated handoff pieces) are high. -/
def TypeBSublinearCentresHighArm : Prop :=
  ∀ centre ∈ canonicalGroupedCentres data object, data.threshold < object.degree centre

open scoped Classical in
/-- The routing and load clauses of arm (iii) at one decorated handoff piece, with
the absorbed core `canonicalGroupedAbsorbedCore` substituted.  The clause
`absorbedAt piece ⊆ piece` is not part of it: it holds at G
(`canonicalGroupedAbsorbedCore_subset`). -/
def TypeBHandoffPieceClauses (piece : Finset object.Vertex) : Prop :=
  (∀ vertex ∈ piece \ canonicalGroupedAbsorbedCore data object piece,
      object.internalDegree piece vertex ≤ data.threshold) ∧
    (∀ vertex ∈ piece \ canonicalGroupedAbsorbedCore data object piece,
      object.internalDegree piece vertex = data.threshold →
      ∃ receiver : object.Vertex,
        object.traceReceiver? piece data.threshold vertex = some receiver ∧
          object.IsReceiver piece data.threshold receiver ∧
            receiver ∉ canonicalGroupedAbsorbedCore data object piece) ∧
    ∀ receiver ∈ object.receivers piece data.threshold \
        canonicalGroupedAbsorbedCore data object piece,
      1 + object.restrictedLoad piece
          (canonicalGroupedAbsorbedCore data object piece)
          data.threshold receiver ≤
        data.dischargeScale * object.missingPorts piece data.threshold receiver

open scoped Classical in
/-- Arm (iii): the clauses hold at every decorated handoff canonical piece of
`R(P₀)`. -/
def TypeBSublinearHandoffArm : Prop :=
  ∀ component ∈ object.canonicalPieces
      (object.remainderSupport (canonicalWindowPacking data object)),
    TypeBGroupedHandoffPiece data object component →
      TypeBHandoffPieceClauses data object
        (object.pieceSupport
          (object.remainderSupport (canonicalWindowPacking data object)) component)

open scoped Classical in
/-- Arm (iv): the absorbed cardinalities of the decorated handoff pieces are
covered by the closed counts of the grouped centres in their canonical fan
envelopes. -/
def TypeBSublinearCoverArm : Prop :=
  ∑ component ∈ (object.canonicalPieces
        (object.remainderSupport (canonicalWindowPacking data object))).filter
      (TypeBGroupedHandoffPiece data object),
      (canonicalGroupedAbsorbedCore data object
        (object.pieceSupport
          (object.remainderSupport (canonicalWindowPacking data object))
          component)).card ≤
    ∑ centre ∈ canonicalGroupedCentres data object,
      Graph.TypeBFanIncidence.closedCount object data.threshold
        (typeBFanEnvelope (canonicalGroupedBridgeUnion data object)
          (canonicalGroupedCentres data object) centre) centre

open scoped Classical in
/-- The first clause of `BridgeResidualComponentAt` fails at a piece.  G's
canonical routing is total on the remainder (`PieceRoutingTotalStatement`), so
the failure is that the canonical trace of a flat off-centre vertex lands on a
centre of the piece. -/
def BridgeTraceIntoCentre (piece : Finset object.Vertex) : Prop :=
  ∃ vertex ∈ piece \ Graph.TypeBRefinedSupport.centres object data.threshold piece,
    object.internalDegree piece vertex = data.threshold ∧
    ∃ receiver ∈ Graph.TypeBRefinedSupport.centres object data.threshold piece,
      object.traceReceiver? piece data.threshold vertex = some receiver

open scoped Classical in
/-- The second clause of `BridgeResidualComponentAt` fails at a piece: a
non-centre receiver with `s · missingPorts < 1 + restrictedLoad`. -/
def BridgeLoadFails (piece : Finset object.Vertex) : Prop :=
  ∃ receiver ∈ object.receivers piece data.threshold \
      Graph.TypeBRefinedSupport.centres object data.threshold piece,
    data.dischargeScale * object.missingPorts piece data.threshold receiver <
      1 + object.restrictedLoad piece
        (Graph.TypeBRefinedSupport.centres object data.threshold piece)
        data.threshold receiver

open scoped Classical in
/-- The routing clause of the handoff clauses fails at a piece: the canonical
trace of a flat vertex outside the absorbed core lands in the absorbed core. -/
def HandoffTraceIntoAbsorbed (piece : Finset object.Vertex) : Prop :=
  ∃ vertex ∈ piece \ canonicalGroupedAbsorbedCore data object piece,
    object.internalDegree piece vertex = data.threshold ∧
    ∃ receiver ∈ canonicalGroupedAbsorbedCore data object piece,
      object.traceReceiver? piece data.threshold vertex = some receiver

open scoped Classical in
/-- The load clause of the handoff clauses fails at a piece. -/
def HandoffLoadFails (piece : Finset object.Vertex) : Prop :=
  ∃ receiver ∈ object.receivers piece data.threshold \
      canonicalGroupedAbsorbedCore data object piece,
    data.dischargeScale * object.missingPorts piece data.threshold receiver <
      1 + object.restrictedLoad piece (canonicalGroupedAbsorbedCore data object piece)
        data.threshold receiver

open scoped Classical in
/-- An absorbed vertex of a decorated handoff piece that is a cubic-closed
neighbour of no grouped centre in its canonical fan envelope (it is unpaid in
the cover count). -/
def UnpaidAbsorbedVertex (piece : Finset object.Vertex) (vertex : object.Vertex) :
    Prop :=
  vertex ∈ canonicalGroupedAbsorbedCore data object piece ∧
    ∀ centre ∈ canonicalGroupedCentres data object,
      vertex ∉ Graph.TypeBFanIncidence.closedNeighbours object data.threshold
        (typeBFanEnvelope (canonicalGroupedBridgeUnion data object)
          (canonicalGroupedCentres data object) centre) centre

/-- **Fact (key 8300).**  The tested hypotheses of `prop:typeB-bridge-sublinear`
are exactly the conjunction of the three arms over G's canonical objects. -/
def TypeBSublinearCanonicalFormStatement : Prop :=
  TypeBSublinearHypotheses data object ↔
    TypeBSublinearBridgeArm data object ∧ TypeBSublinearCentresHighArm data object ∧
      TypeBSublinearHandoffArm data object ∧ TypeBSublinearCoverArm data object

/-- **Fact (key 8301).**  Lean improvement: the clause `absorbedAt piece ⊆ piece`
of the hypotheses is empty as a failure arm at G, since G's canonical absorbed
core of a piece is a subset of the piece. -/
def GroupedAbsorbedCoreSubsetStatement : Prop :=
  ∀ piece : Finset object.Vertex,
    canonicalGroupedAbsorbedCore data object piece ⊆ piece

open scoped Classical in
/-- **Fact (key 8303).**  Lean improvement: the grouped centres of G are high, so
the height clause of the hypotheses is empty as a failure arm at G (a surviving
first separator has degree at least `4`, `lem:typeA-cubic-switch-absorption`). -/
def GroupedCentresHighStatement : Prop :=
  TypeBSublinearCentresHighArm data object

/-- **Fact (key 8304).**  Lean improvement: the degree clause of the handoff
clauses is empty as a failure arm at G.  A decorated handoff piece has zero
ambient surplus, so no vertex of it has internal degree above the baseline. -/
def HandoffDegreeClauseEmptyStatement : Prop :=
  ∀ component ∈ object.canonicalPieces
      (object.remainderSupport (canonicalWindowPacking data object)),
    TypeBGroupedHandoffPiece data object component →
      ∀ vertex ∈ object.pieceSupport
          (object.remainderSupport (canonicalWindowPacking data object)) component,
        object.internalDegree
          (object.pieceSupport
            (object.remainderSupport (canonicalWindowPacking data object)) component)
          vertex ≤ data.threshold

/-- **Fact (key 8305).**  G's canonical routing is total on every canonical piece
of the remainder: a vertex of a piece spending the whole baseline inside it is
routed by `traceReceiver?` to a receiver of the piece (the remainder carries no
baseline subgraph, `K .remainderNormalized`).  The `none` and non-receiver
outcomes of the routing clauses are therefore empty at G. -/
def PieceRoutingTotalStatement : Prop :=
  ∀ component ∈ object.canonicalPieces
      (object.remainderSupport (canonicalWindowPacking data object)),
    ∀ vertex ∈ object.pieceSupport
        (object.remainderSupport (canonicalWindowPacking data object)) component,
      object.internalDegree
          (object.pieceSupport
            (object.remainderSupport (canonicalWindowPacking data object)) component)
          vertex = data.threshold →
      ∃ receiver : object.Vertex,
        object.traceReceiver?
            (object.pieceSupport
              (object.remainderSupport (canonicalWindowPacking data object)) component)
            data.threshold vertex = some receiver ∧
          object.IsReceiver
            (object.pieceSupport
              (object.remainderSupport (canonicalWindowPacking data object)) component)
            data.threshold receiver

open scoped Classical in
/-- **Fact (key 8306).**  The incidence payment of the cover arm: the cover
inequality fails only if some absorbed vertex of a decorated handoff piece is a
cubic-closed neighbour of no grouped centre in its canonical fan envelope
(the pieces are pairwise disjoint, so paying every absorbed vertex by a closed
neighbour of a centre is an injection into the closed-neighbour count). -/
def CoverPaymentStatement : Prop :=
  ¬ TypeBSublinearCoverArm data object →
    ∃ component ∈ object.canonicalPieces
        (object.remainderSupport (canonicalWindowPacking data object)),
      TypeBGroupedHandoffPiece data object component ∧
        ∃ vertex, UnpaidAbsorbedVertex data object
          (object.pieceSupport
            (object.remainderSupport (canonicalWindowPacking data object)) component)
          vertex

open scoped Classical in
/-- **Fact (key 8302).**  Given the failed hypotheses (`K .typeBSublinearResidual`),
the exact decomposition of the failure at G, after the empty arms (grouped centre
not high, degree clause of the handoff clauses, routing to no receiver) are
removed:
(A) a negative positive-surplus canonical piece of `R(P₀)` that G's route-`8`
collection `canonicalBridgeRoute8Pieces` contains, whose flat vertex traces into a
centre or which has a non-centre receiver over capacity; or
(B) a decorated handoff piece whose flat vertex traces into the absorbed core or
which has a receiver outside the absorbed core over capacity; or
(C) bridge and handoff arms hold and an absorbed vertex of a handoff piece is
unpaid in the cover count. -/
def TypeBSublinearFailureArmsStatement : Prop :=
    (∃ component ∈ canonicalBridgeRoute8Pieces data object
        (object.remainderSupport (canonicalWindowPacking data object)),
      object.NegativeNetCharge
          (object.pieceSupport
            (object.remainderSupport (canonicalWindowPacking data object))
            component) data.threshold data.dischargeScale ∧
        0 < object.ambientSurplus
          (object.pieceSupport
            (object.remainderSupport (canonicalWindowPacking data object))
            component) data.threshold ∧
        (BridgeTraceIntoCentre data object
            (object.pieceSupport
              (object.remainderSupport (canonicalWindowPacking data object))
              component) ∨
          BridgeLoadFails data object
            (object.pieceSupport
              (object.remainderSupport (canonicalWindowPacking data object))
              component))) ∨
    (∃ component ∈ object.canonicalPieces
        (object.remainderSupport (canonicalWindowPacking data object)),
      TypeBGroupedHandoffPiece data object component ∧
        (HandoffTraceIntoAbsorbed data object
            (object.pieceSupport
              (object.remainderSupport (canonicalWindowPacking data object))
              component) ∨
          HandoffLoadFails data object
            (object.pieceSupport
              (object.remainderSupport (canonicalWindowPacking data object))
              component))) ∨
    (TypeBSublinearBridgeArm data object ∧ TypeBSublinearHandoffArm data object ∧
      ∃ component ∈ object.canonicalPieces
          (object.remainderSupport (canonicalWindowPacking data object)),
        TypeBGroupedHandoffPiece data object component ∧
          ∃ vertex, UnpaidAbsorbedVertex data object
            (object.pieceSupport
              (object.remainderSupport (canonicalWindowPacking data object))
              component) vertex)

end Canonical

end Hypostructure.Graph.Strategy.Spine
