import Hypostructure.Graph.Statements.TypeBSublinearFlow

/-!
# Statements: where the canonical trace lands, and the corrected mass bound
(keys 8314--8316)
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

section Landing

variable (data : Parameters) (object : Graph.FiniteObject.{u})

/-- **Fact (key 8314)** (gap H05, corrected bound): the mass bound with the
surplus.  A canonical piece of the remainder either has a flat vertex whose
trace lands on a centre, or a saturated non-centre receiver, or satisfies
`|Y| ≤ s · def⁺(Y) + σ(Y)`: the load side costs `c = 1` per unit of surplus (each
centre is one vertex and carries at least one unit of `σ`), and the ports cost
nothing (they are the window stubs of 8309). -/
def BridgePieceMassDichotomyStatement : Prop :=
  ∀ component ∈ object.canonicalPieces
      (object.remainderSupport (canonicalWindowPacking data object)),
    BridgeTraceIntoCentre data object
        (object.pieceSupport
          (object.remainderSupport (canonicalWindowPacking data object)) component) ∨
      BridgeLoadFails data object
        (object.pieceSupport
          (object.remainderSupport (canonicalWindowPacking data object)) component) ∨
      (object.pieceSupport
          (object.remainderSupport (canonicalWindowPacking data object))
          component).card ≤
        data.dischargeScale *
            object.positiveDeficiency
              (object.pieceSupport
                (object.remainderSupport (canonicalWindowPacking data object))
                component) data.threshold +
          object.ambientSurplus
            (object.pieceSupport
              (object.remainderSupport (canonicalWindowPacking data object))
              component) data.threshold

/-- **Fact (key 8315)** (gap H04, arm A landing): what a trace into a centre
forces.  If the canonical trace of a flat vertex of a canonical piece lands on a
centre `c` of the piece, then `c` is high, is a receiver (internal degree below
the baseline), the trace is a path of the piece with baseline interior, and `c` has
two distinct neighbours in the packed windows, both at the baseline (the
neighbourhood normal form of `c`). -/
def TraceIntoCentreStructureStatement : Prop :=
  ∀ component ∈ object.canonicalPieces
      (object.remainderSupport (canonicalWindowPacking data object)),
    ∀ vertex : object.Vertex,
      object.internalDegree
          (object.pieceSupport
            (object.remainderSupport (canonicalWindowPacking data object)) component)
          vertex = data.threshold →
      ∀ centre ∈ Graph.TypeBRefinedSupport.centres object data.threshold
          (object.pieceSupport
            (object.remainderSupport (canonicalWindowPacking data object)) component),
        object.traceReceiver?
            (object.pieceSupport
              (object.remainderSupport (canonicalWindowPacking data object)) component)
            data.threshold vertex = some centre →
        data.threshold < object.degree centre ∧
          object.internalDegree
              (object.pieceSupport
                (object.remainderSupport (canonicalWindowPacking data object))
                component) centre < data.threshold ∧
          object.TraceTo
            (object.pieceSupport
              (object.remainderSupport (canonicalWindowPacking data object)) component)
            data.threshold vertex centre ∧
          ∃ first second : object.Vertex, first ≠ second ∧
            object.graph.Adj centre first ∧ object.graph.Adj centre second ∧
            first ∈ Graph.FiniteObject.windowSupport
              (canonicalWindowPacking data object) ∧
            second ∈ Graph.FiniteObject.windowSupport
              (canonicalWindowPacking data object) ∧
            object.degree first = data.threshold ∧
            object.degree second = data.threshold

open scoped Classical in
/-- **Fact (key 8316)** (gap H04, arm B landing): what a trace into the absorbed
core forces.  If the canonical trace of a flat vertex of a decorated handoff piece
lands on `r` in the absorbed core, then `r` is a cubic vertex of the piece, the
trace is a path of the piece with baseline interior, and `r` is adjacent to a
grouped centre `z` that is high, lies outside the piece, and lies in the packed
windows. -/
def TraceIntoAbsorbedStructureStatement : Prop :=
  ∀ component ∈ object.canonicalPieces
      (object.remainderSupport (canonicalWindowPacking data object)),
    TypeBGroupedHandoffPiece data object component →
    ∀ vertex : object.Vertex,
      object.internalDegree
          (object.pieceSupport
            (object.remainderSupport (canonicalWindowPacking data object)) component)
          vertex = data.threshold →
      ∀ receiver ∈ canonicalGroupedAbsorbedCore data object
          (object.pieceSupport
            (object.remainderSupport (canonicalWindowPacking data object)) component),
        object.traceReceiver?
            (object.pieceSupport
              (object.remainderSupport (canonicalWindowPacking data object)) component)
            data.threshold vertex = some receiver →
        receiver ∈ object.pieceSupport
            (object.remainderSupport (canonicalWindowPacking data object)) component ∧
          object.degree receiver = data.threshold ∧
          object.TraceTo
            (object.pieceSupport
              (object.remainderSupport (canonicalWindowPacking data object)) component)
            data.threshold vertex receiver ∧
          ∃ centre ∈ canonicalGroupedCentres data object,
            object.graph.Adj centre receiver ∧
            data.threshold < object.degree centre ∧
            centre ∉ object.pieceSupport
              (object.remainderSupport (canonicalWindowPacking data object)) component ∧
            centre ∈ Graph.FiniteObject.windowSupport
              (canonicalWindowPacking data object)

end Landing

end Hypostructure.Graph.Strategy.Spine
