import Hypostructure.Graph.Statements.TypeBSublinearCanonical

/-!
# Statements: the load and cover gaps of the Type B sublinear failure (keys 8307--8308)
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

section Gaps

variable (data : Parameters) (object : Graph.FiniteObject.{u})

open scoped Classical in
/-- **Fact (key 8307)** (gap H05): a load failure of the sublinear test is a
saturated receiver of the piece.  The restricted load is a sub-count of the
routed load, so `s · missingPorts < 1 + restrictedLoad` gives
`s · missingPorts ≤ routedLoad`, the saturation of the Type A analysis
(`Graph.FiniteObject.Saturated`), at a receiver outside the centres (bridge
pieces) or outside the absorbed core (decorated handoff pieces). -/
def LoadFailureSaturatedStatement : Prop :=
  ∀ piece : Finset object.Vertex,
    (BridgeLoadFails data object piece →
      ∃ receiver ∈ object.receivers piece data.threshold \
          Graph.TypeBRefinedSupport.centres object data.threshold piece,
        object.Saturated piece data.threshold data.dischargeScale receiver) ∧
    (HandoffLoadFails data object piece →
      ∃ receiver ∈ object.receivers piece data.threshold \
          canonicalGroupedAbsorbedCore data object piece,
        object.Saturated piece data.threshold data.dischargeScale receiver)

open scoped Classical in
/-- **Fact (key 8308)** (gap H06, H07): the Hall violator of the cover network.
An unpaid absorbed vertex of a decorated handoff piece is adjacent to its
grouped centre `z` and has a neighbour other than `z` outside the fan envelope
of `z`; that neighbour lies in the packed windows. -/
def UnpaidAbsorbedWindowPortStatement : Prop :=
  ∀ component ∈ object.canonicalPieces
      (object.remainderSupport (canonicalWindowPacking data object)),
    TypeBGroupedHandoffPiece data object component →
    ∀ vertex,
      UnpaidAbsorbedVertex data object
        (object.pieceSupport
          (object.remainderSupport (canonicalWindowPacking data object)) component)
        vertex →
      ∃ centre ∈ canonicalGroupedCentres data object,
        object.graph.Adj centre vertex ∧
        ∃ other, object.graph.Adj vertex other ∧ other ≠ centre ∧
          other ∈ Graph.FiniteObject.windowSupport (canonicalWindowPacking data object)

end Gaps

end Hypostructure.Graph.Strategy.Spine
