import Hypostructure.Graph.Statements.Spine

/-!
# Statements: TypeA

Proof-agnostic statement definitions of the minimum-degree cycle spine:
Type A statements: receiver routing, saturation, visible entry, the seven saturated exits and exit-(4) descent.
Every registered constant is an explicit `Parameters` argument; this module
imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u v

/-- Exit `(6)` at the selected Type A support and receiver: some eligible
silent routed load of the receiver has a selected trace basin at which an
equality of declared coordinates of `ρ_u(B_u)` becomes target-complete only
after adjoining a larger connected support (`def:typeA-trace-basin` (c),
identified with exit `(6)` by `lem:typeA-reduced-silent-residual`).  The
eligible loads are exactly those tested by exit `(5)` on the same peeling set. -/
def ExitSixDelocalizes (data : Parameters) (object : Graph.FiniteObject.{u})
    (piece : Finset object.Vertex) (receiver : object.Vertex)
    (peeled : Finset object.Vertex) : Prop :=
  ∃ load : object.Vertex,
    (((∃ package :
          Graph.ExitFour.VisibleFourUnpeeledPackage piece data.threshold
            data.dischargeScale receiver peeled,
        (¬ ∃ witness : Graph.ExitFour.Witness
            (Graph.HasCycleWithLength data.LengthOK) piece data.threshold data.dischargeScale
            receiver peeled,
          ∃ selected ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
              data.threshold data.dischargeScale receiver package.outside
              peeled,
            witness.load = selected) ∧
          load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
            data.threshold data.dischargeScale receiver package.outside
            peeled) ∨
      (Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold
          data.dischargeScale receiver peeled ∧
        (¬ ∃ witness : Graph.ExitFour.Witness
            (Graph.HasCycleWithLength data.LengthOK) piece data.threshold data.dischargeScale
            receiver peeled,
          witness.load ∈ Graph.ExitFour.unpeeledExcess piece data.threshold
            data.dischargeScale receiver peeled) ∧
        load ∈ Graph.ExitFour.unpeeledExcess piece data.threshold
          data.dischargeScale receiver peeled)) ∧
      ∃ basin : Finset object.Vertex,
        Graph.Route8.TraceBasin.select? object piece data.threshold
            receiver load = some basin ∧
          Graph.Route8.TraceBasin.TraceDelocalization object piece
            data.threshold data.LengthOK receiver load basin)

/-- The complete node-`[94]` certificate at its exact support and selected
receiver.  This is deliberately support- and receiver-indexed: carrying only
an unindexed existential through the shared visible/silent exit chain loses
the identity needed when node `[184]` speaks about the unified entry family. -/
def SilentExitOriginAt (data : Parameters) (object : Graph.FiniteObject.{u})
    (piece : Finset object.Vertex) (receiver : object.Vertex) : Prop :=
  (∀ otherReceiver : object.Vertex,
      object.IsReceiver piece data.threshold otherReceiver →
        object.Saturated piece data.threshold data.dischargeScale
          otherReceiver →
        ¬ Graph.ExitFour.VisibleFourUnpeeledAt piece data.threshold
          data.dischargeScale otherReceiver ∅) ∧
    object.Saturated piece data.threshold data.dischargeScale receiver ∧
    Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold
      data.dischargeScale receiver ∅ ∧
    piece.card ≤
      (∑ other ∈ object.receivers piece data.threshold,
        (Graph.VisibleEntry.silentExcess object piece data.threshold
          data.dischargeScale other).card) +
        data.dischargeScale * object.positiveDeficiency piece data.threshold

/-- The literal exit-`(4)`-free alternative at one selected receiver and
peeling set.  On the visible arm, retain the Q1 semantic conclusion for the
same selected package, as well as the original no-witness statement. -/
def ExitFourFreeAt (data : Parameters) (object : Graph.FiniteObject.{u})
    (piece : Finset object.Vertex) (receiver : object.Vertex)
    (peeled : Finset object.Vertex) : Prop :=
  (∃ package : Graph.ExitFour.VisibleFourUnpeeledPackage piece data.threshold
      data.dischargeScale receiver peeled,
    (¬ ∃ witness : Graph.ExitFour.Witness
        (Graph.HasCycleWithLength data.LengthOK) piece data.threshold
        data.dischargeScale receiver peeled,
      ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
          data.threshold data.dischargeScale receiver package.outside peeled,
        witness.load = load) ∧
    ∀ pair : package.Q1OriginPair,
      Graph.Response.TargetComplete Graph.BoundaryPiece.boundaryDegreeProfile
        (Graph.HasCycleWithLength data.LengthOK)
        (Graph.ExitFour.visibleResponsePiece pair.leftResponseCoordinate)
        (Graph.ExitFour.visibleResponsePiece pair.rightResponseCoordinate)) ∨
  (Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold
      data.dischargeScale receiver peeled ∧
    ¬ ∃ witness : Graph.ExitFour.Witness
        (Graph.HasCycleWithLength data.LengthOK) piece data.threshold
        data.dischargeScale receiver peeled,
      witness.load ∈ Graph.ExitFour.unpeeledExcess piece data.threshold
        data.dischargeScale receiver peeled)

/-- Exit `(5)` at one selected receiver and peeling set.  This abbreviation is
used only by the provenance-preserving silent lane; it is definitionally the
same local predicate used by the shared exit chain. -/
def ExitFiveAt (data : Parameters) (object : Graph.FiniteObject.{u})
    (piece : Finset object.Vertex) (receiver : object.Vertex)
    (peeled : Finset object.Vertex) : Prop :=
  ∃ load : object.Vertex,
    (((∃ package : Graph.ExitFour.VisibleFourUnpeeledPackage piece
          data.threshold data.dischargeScale receiver peeled,
        (¬ ∃ witness : Graph.ExitFour.Witness
            (Graph.HasCycleWithLength data.LengthOK) piece data.threshold
            data.dischargeScale receiver peeled,
          ∃ selected ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
              data.threshold data.dischargeScale receiver package.outside
              peeled,
            witness.load = selected) ∧
        load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece data.threshold
          data.dischargeScale receiver package.outside peeled) ∨
      (Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold
          data.dischargeScale receiver peeled ∧
        (¬ ∃ witness : Graph.ExitFour.Witness
            (Graph.HasCycleWithLength data.LengthOK) piece data.threshold
            data.dischargeScale receiver peeled,
          witness.load ∈ Graph.ExitFour.unpeeledExcess piece data.threshold
            data.dischargeScale receiver peeled) ∧
        load ∈ Graph.ExitFour.unpeeledExcess piece data.threshold
          data.dischargeScale receiver peeled)) ∧
      ∃ basin : Finset object.Vertex,
        Graph.Route8.TraceBasin.select? object piece data.threshold receiver
            load = some basin ∧
          Graph.Route8.TraceBasin.TraceTargetCompleteCompression object piece
            data.threshold data.LengthOK receiver load basin)

/-- The exact selected saturated Type A state after exits `(4)`, `(5)`, and
`(6)` have failed, with one additional local clause on its selected packing and
support.  This is a fact-schema abbreviation only: rows still read it from the
incoming `ExactLedger` and commit descendants through `Decision.run` or
`factOnly`. -/
abbrev SelectedNoExitSixWith (data : Parameters) (object : Graph.FiniteObject.{u})
    (extra : (packing : Finset (Finset object.Vertex)) →
      Finset object.Vertex → Prop) : Prop :=
  let exitFiveAt := ExitFiveAt data object
  (∃ packing : Finset (Finset object.Vertex),
    packing = canonicalWindowPacking data object ∧
      object.IsWindowPacking data.windowOrder packing ∧
      (∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
        ∃ member ∈ packing, ¬ Disjoint window member) ∧
      ∃ component ∈ object.canonicalPieces
          (object.remainderSupport packing),
        let piece := object.pieceSupport
          (object.remainderSupport packing) component
        object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
          object.ambientSurplus piece data.threshold = 0 ∧
          ∃ receiver : object.Vertex,
            object.IsReceiver piece data.threshold receiver ∧
              ∃ peeled : Finset object.Vertex,
                peeled ⊆ object.routedLoads piece data.threshold receiver ∧
                  Graph.ExitFour.SaturatedAfter piece data.threshold
                    data.dischargeScale receiver peeled ∧
                  ExitFourFreeAt data object piece receiver peeled ∧
                  ¬ exitFiveAt piece receiver peeled ∧
                  ¬ ExitSixDelocalizes data object piece receiver peeled ∧
                  extra packing piece)

/-- The same selected no-exit-`(6)` residual, but with the selected receiver
and current peeling set exposed to the next local route-`8` fact.  This is a
schema helper only: the framework still carries the full `ExactLedger`, and
rows still read the predecessor facts by key. -/
abbrev SelectedNoExitSixReceiverWith (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (extra : (packing : Finset (Finset object.Vertex)) →
      (piece : Finset object.Vertex) → object.Vertex →
      Finset object.Vertex → Prop) : Prop :=
  let exitFiveAt := ExitFiveAt data object
  (∃ packing : Finset (Finset object.Vertex),
    packing = canonicalWindowPacking data object ∧
      object.IsWindowPacking data.windowOrder packing ∧
      (∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
        ∃ member ∈ packing, ¬ Disjoint window member) ∧
      ∃ component ∈ object.canonicalPieces
          (object.remainderSupport packing),
        let piece := object.pieceSupport
          (object.remainderSupport packing) component
        object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
          object.ambientSurplus piece data.threshold = 0 ∧
          ∃ receiver : object.Vertex,
            object.IsReceiver piece data.threshold receiver ∧
              ∃ peeled : Finset object.Vertex,
                peeled ⊆ object.routedLoads piece data.threshold receiver ∧
                  Graph.ExitFour.SaturatedAfter piece data.threshold
                    data.dischargeScale receiver peeled ∧
                  ExitFourFreeAt data object piece receiver peeled ∧
                  ¬ exitFiveAt piece receiver peeled ∧
                  ¬ ExitSixDelocalizes data object piece receiver peeled ∧
                  extra packing piece receiver peeled)

/-- The terminal saturated outcome of the silent exit-`(4)` descent, retaining
the node-`[94]` origin on the same support and receiver. -/
abbrev SelectedSilentExitFourFree (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ packing : Finset (Finset object.Vertex),
    packing = canonicalWindowPacking data object ∧
      object.IsWindowPacking data.windowOrder packing ∧
      (∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
        ∃ member ∈ packing, ¬ Disjoint window member) ∧
      ∃ component ∈ object.canonicalPieces
          (object.remainderSupport packing),
        let piece := object.pieceSupport
          (object.remainderSupport packing) component
        object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
          object.ambientSurplus piece data.threshold = 0 ∧
          ∃ receiver : object.Vertex,
            object.IsReceiver piece data.threshold receiver ∧
              SilentExitOriginAt data object piece receiver ∧
              ∃ peeled : Finset object.Vertex,
                peeled ⊆ object.routedLoads piece data.threshold receiver ∧
                  Graph.ExitFour.SaturatedAfter piece data.threshold
                    data.dischargeScale receiver peeled ∧
                  ExitFourFreeAt data object piece receiver peeled

/-- The silent-origin state after exits `(4)` and `(5)` have failed. -/
abbrev SelectedSilentExitFiveFree (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ packing : Finset (Finset object.Vertex),
    packing = canonicalWindowPacking data object ∧
      object.IsWindowPacking data.windowOrder packing ∧
      (∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
        ∃ member ∈ packing, ¬ Disjoint window member) ∧
      ∃ component ∈ object.canonicalPieces
          (object.remainderSupport packing),
        let piece := object.pieceSupport
          (object.remainderSupport packing) component
        object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
          object.ambientSurplus piece data.threshold = 0 ∧
          ∃ receiver : object.Vertex,
            object.IsReceiver piece data.threshold receiver ∧
              SilentExitOriginAt data object piece receiver ∧
              ∃ peeled : Finset object.Vertex,
                peeled ⊆ object.routedLoads piece data.threshold receiver ∧
                  Graph.ExitFour.SaturatedAfter piece data.threshold
                    data.dischargeScale receiver peeled ∧
                  ExitFourFreeAt data object piece receiver peeled ∧
                  ¬ ExitFiveAt data object piece receiver peeled

/-- The silent-origin state after exits `(4)`--`(6)` have failed. -/
abbrev SelectedSilentExitSixFree (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  SelectedNoExitSixReceiverWith data object
    (fun _packing piece receiver _peeled =>
      SilentExitOriginAt data object piece receiver)

/-- The exact silent-origin route-`8` entry after exit `(7)` also fails.  The
origin and no-handoff assertion are scoped to the same selected support. -/
abbrev SelectedSilentExitSevenFree (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  SelectedNoExitSixReceiverWith data object
    (fun packing piece receiver _peeled =>
      SilentExitOriginAt data object piece receiver ∧
        ¬ HandoffProduced data object packing piece)

/-- The exact finite exit-`(4)` descent theorem committed before the route-`8`
arm.  This is a schema abbreviation only: the fact is still read from the
ledger by key and transported by the framework. -/
abbrev TypeAExitFourFiniteDescentFact (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ packing : Finset (Finset object.Vertex),
    packing = canonicalWindowPacking data object ∧
      object.IsWindowPacking data.windowOrder packing ∧
      (∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
        ∃ member ∈ packing, ¬ Disjoint window member) ∧
      ∃ component ∈ object.canonicalPieces
          (object.remainderSupport packing),
        let piece := object.pieceSupport
          (object.remainderSupport packing) component
        object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
          object.ambientSurplus piece data.threshold = 0 ∧
          ∃ receiver : object.Vertex,
            object.IsReceiver piece data.threshold receiver ∧
              ∃ startPeeled : Finset object.Vertex,
                startPeeled ⊆ object.routedLoads piece data.threshold
                    receiver ∧
                  Graph.ExitFour.SaturatedAfter piece data.threshold
                    data.dischargeScale receiver startPeeled ∧
                  ∀ Retained Terminal : Finset object.Vertex → Prop,
                    Retained startPeeled →
                    (∀ peeled,
                      peeled ⊆ object.routedLoads piece data.threshold
                          receiver →
                      Retained peeled →
                      Graph.ExitFour.SaturatedAfter piece data.threshold
                        data.dischargeScale receiver peeled →
                      Terminal peeled ∨
                        ∃ load ∈ object.routedLoads piece data.threshold
                            receiver,
                          ∃ fresh : load ∉ peeled,
                            Retained (Finset.cons load peeled fresh)) →
                    (∃ finalPeeled ⊆
                        object.routedLoads piece data.threshold receiver,
                      Retained finalPeeled ∧ Terminal finalPeeled) ∨
                    (∃ finalPeeled ⊆
                        object.routedLoads piece data.threshold receiver,
                      Retained finalPeeled ∧
                        ¬ Graph.ExitFour.SaturatedAfter piece data.threshold
                          data.dischargeScale receiver finalPeeled)

/-! ## Key statements

The statement each vocabulary key of this family publishes, stated over the
registered parameters and the selected object. -/

/-- Node `[62]`, no arm — node `[63]`, Type A: the selected negative support
carries no assigned high-degree surplus. -/
noncomputable abbrev TypeALowSurplusStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[62]`, no -- node `[63]`, Type A: the selected support carries no
  -- assigned surplus.  The packing keeps its maximality: `def:typeA-support`
  -- is `def:admissible` with `σ(X) = 0`, and the inherited clauses the Type
  -- A ladder spends -- window-freeness and the empty internal `δ`-core --
  -- are node `[27]`'s conclusions about the remainder of a maximal packing.
  (∃ packing : Finset (Finset object.Vertex),
    packing = canonicalWindowPacking data object ∧
      object.IsWindowPacking data.windowOrder packing ∧
      (∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
        ∃ member ∈ packing, ¬ Disjoint window member) ∧
      ∃ component ∈ object.canonicalPieces
          (object.remainderSupport packing),
        let piece := object.pieceSupport
          (object.remainderSupport packing) component
        object.NegativeNetCharge piece data.threshold
            data.dischargeScale ∧
          object.ambientSurplus piece data.threshold = 0)

/-- Node `[87]`: the selected Type A support is induced-`P_windowOrder`-free;
every two of its vertices have an internal path of length at most
`windowOrder - 2`, and the subcubic breadth-first bound gives
`1 + threshold * (2^(windowOrder - 2) - 1)` vertices.  At the registered
`windowOrder = 13`, `threshold = 3`, these are diameter at most `11` and
cardinality at most `6142`. -/
noncomputable abbrev TypeABoundedSupportStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[87]`, on the selected incoming Type A support only.  Node `[27]`
  -- supplies induced-window freeness on this subregion.  A shortest path
  -- inside the piece is induced, so it has at most `windowOrder - 2`
  -- edges; zero surplus against the standing baseline makes the piece
  -- subcubic, and the rooted breadth-first count gives the displayed cap.
  (∃ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing ∧
      (∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
        ∃ member ∈ packing, ¬ Disjoint window member) ∧
      ∃ component ∈ object.canonicalPieces
          (object.remainderSupport packing),
        let piece := object.pieceSupport
          (object.remainderSupport packing) component
        object.NegativeNetCharge piece data.threshold
            data.dischargeScale ∧
          object.ambientSurplus piece data.threshold = 0 ∧
          Graph.InducedPathFree (object.induce piece) data.windowOrder ∧
          (∀ left ∈ piece, ∀ right ∈ piece,
            ∃ path : object.graph.Walk left right,
              path.IsPath ∧
                (∀ vertex ∈ path.support, vertex ∈ piece) ∧
                path.length ≤ data.windowOrder - 2) ∧
          piece.card ≤
            1 + data.threshold *
              (2 ^ (data.windowOrder - 2) - 1))

/-- Node `[62]`, yes arm — node `[64]`, Type B: the selected negative support
carries assigned high-degree surplus. -/
noncomputable abbrev TypeBHighSurplusStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[62]`, yes -- node `[64]`, Type B: it carries some.
  (∃ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing ∧
      (∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
        ∃ member ∈ packing, ¬ Disjoint window member) ∧
      ∃ component ∈ object.canonicalPieces
          (object.remainderSupport packing),
        let piece := object.pieceSupport
          (object.remainderSupport packing) component
        object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
          0 < object.ambientSurplus piece data.threshold)

/-- Node `[88]`: the routing and threshold algebra of a Type A support.
`lem:typeA-receiver-loads` — every vertex spending the whole baseline inside
the support is routed by the canonical trace to exactly one receiver — and
`lem:typeA-threshold-algebra` — a receiver of internal degree `δ − 1 − j` has
`q(w) = j + 1`, so its saturation threshold is `H_j = s·(j+1)`, never above
`s·δ`.  For the manuscript's baseline and discharge scale this is
`H₀ ≤ 4`, `H₁ ≤ 8`, `H₂ ≤ 12`. -/
noncomputable abbrev TypeAReceiverRoutingStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[88]`.  Stated at every Type A support the object carries, in
  -- the same way node `[27]` is stated at every subregion of a remainder:
  -- a support is data and cannot travel, so what the ledger records is the
  -- statement about all of them.
  --
  -- `def:typeA-support` is `def:admissible` with `σ(X) = 0`; the two
  -- clauses below are `def:typeA-receiver-load`'s own consequences at such
  -- a support.
  (∀ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing →
    (∀ window : Finset object.Vertex,
      object.InducesWindow data.windowOrder window →
      ∃ member ∈ packing, ¬ Disjoint window member) →
    ∀ piece : Finset object.Vertex,
      piece ⊆ object.remainderSupport packing →
      object.ambientSurplus piece data.threshold = 0 →
      -- `lem:typeA-receiver-loads`: `r(u)` is defined for every vertex of
      -- internal degree `δ`, and it is a receiver.  Uniqueness is the
      -- routing being a function of `u`.
      (∀ vertex ∈ piece,
        object.internalDegree piece vertex = data.threshold →
        ∃ receiver : object.Vertex,
          object.traceReceiver? piece data.threshold vertex = some receiver ∧
            object.IsReceiver piece data.threshold receiver) ∧
        -- `lem:typeA-threshold-algebra`: `H_j = s·q(w) = s·(j+1) ≤ s·δ`.
        (∀ receiver : object.Vertex,
          object.IsReceiver piece data.threshold receiver →
          data.dischargeScale *
                object.missingPorts piece data.threshold receiver =
              data.dischargeScale *
                (data.threshold - 1 -
                  object.internalDegree piece receiver + 1) ∧
            data.dischargeScale *
                object.missingPorts piece data.threshold receiver ≤
              data.dischargeScale * data.threshold))

/-- Node `[89]`, yes arm — the entry of node `[93]`: some receiver of a Type A
support has reached its saturation threshold, `L(w) ≥ s·q(w)`. -/
noncomputable abbrev TypeASaturatedReceiverStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[89]`, yes: the selected canonical Type A component retains an
  -- actual saturated receiver.
  (∃ packing : Finset (Finset object.Vertex),
    packing = canonicalWindowPacking data object ∧
      object.IsWindowPacking data.windowOrder packing ∧
      (∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
        ∃ member ∈ packing, ¬ Disjoint window member) ∧
      ∃ component ∈ object.canonicalPieces
          (object.remainderSupport packing),
        let piece := object.pieceSupport
          (object.remainderSupport packing) component
        object.NegativeNetCharge piece data.threshold
            data.dischargeScale ∧
          object.ambientSurplus piece data.threshold = 0 ∧
          ∃ receiver : object.Vertex,
            object.IsReceiver piece data.threshold receiver ∧
              object.Saturated piece data.threshold data.dischargeScale
                receiver)

/-- Node `[89]`, no arm — node `[90]`: every receiver of every Type A support
is unsaturated, `L(w) ≤ s·q(w) − 1`.  This is the capacity the `3/7/11`
discharging of node `[91]` spends. -/
noncomputable abbrev TypeAUnsaturatedReceiversStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[89]`, no -- node `[90]`: every receiver of that same selected
  -- canonical component satisfies `L(w) ≤ s·q(w) − 1`.
  (∃ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing ∧
      (∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
        ∃ member ∈ packing, ¬ Disjoint window member) ∧
      ∃ component ∈ object.canonicalPieces
          (object.remainderSupport packing),
        let piece := object.pieceSupport
          (object.remainderSupport packing) component
        object.NegativeNetCharge piece data.threshold
            data.dischargeScale ∧
          object.ambientSurplus piece data.threshold = 0 ∧
      ∀ receiver : object.Vertex,
        object.IsReceiver piece data.threshold receiver →
        1 + object.routedLoad piece data.threshold receiver ≤
          data.dischargeScale *
            object.missingPorts piece data.threshold receiver)

/-- Node `[91]`: the `3/7/11` discharging conclusion on every unsaturated
Type A support, in the exact integral form
`|V(X)| ≤ s * def⁺(X)`. -/
noncomputable abbrev TypeAUnsaturatedDischargeStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[91]`, `lem:typeA-unsaturated-discharge`, on the same selected
  -- canonical component carried by node `[90]`.
  (∃ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing ∧
    (∀ window : Finset object.Vertex,
      object.InducesWindow data.windowOrder window →
      ∃ member ∈ packing, ¬ Disjoint window member) ∧
    ∃ component ∈ object.canonicalPieces
        (object.remainderSupport packing),
      let piece := object.pieceSupport
        (object.remainderSupport packing) component
      object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
        object.ambientSurplus piece data.threshold = 0 ∧
        piece.card ≤
          data.dischargeScale *
            object.positiveDeficiency piece data.threshold)

/-- Node `[86]`, `lem:typeA-exclusion` (via `lem:density-mersenne`), at the
minimal counterexample: every negative zero-surplus canonical piece of a
maximal packing's remainder carries an exit-`(4)` witness for a routed load,
an admissible silent-core residual profile, or a produced decorated Type B
handoff. -/
noncomputable abbrev TypeAExclusionStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[86]`, `lem:typeA-exclusion` via `lem:density-mersenne`, stated
  -- at the minimal counterexample the branch carries, exactly at the
  -- paper's generality: over every connected admissible sub-support of
  -- its own maximal-packing remainders — "every admissible subcubic
  -- P₁₃-free target-safe boundaried piece", so the same fact serves the
  -- canonical pieces at `K .route8PiecesClassified` and the post-ledger
  -- core components of the Type B bridge pieces.  A negative zero-surplus
  -- piece leaves through the target-defect exit, the silent-core residual
  -- profile, or the decorated handoff.
  (∀ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing →
    (∀ window : Finset object.Vertex,
      object.InducesWindow data.windowOrder window →
      ∃ member ∈ packing, ¬ Disjoint window member) →
    ∀ piece : Finset object.Vertex,
      piece ⊆ object.remainderSupport packing →
      Graph.SupportComponents.Connected.ConnectedOn object piece →
      object.NegativeNetCharge piece data.threshold data.dischargeScale →
      object.ambientSurplus piece data.threshold = 0 →
      ((∃ receiver : object.Vertex,
          object.IsReceiver piece data.threshold receiver ∧
            Nonempty (Graph.ExitFour.Witness
              (Graph.HasCycleWithLength data.LengthOK) piece data.threshold
              data.dischargeScale receiver ∅)) ∨
        (∀ receiver ∈ Graph.VisibleEntry.saturatedReceivers object piece
              data.threshold data.dischargeScale,
            (∀ load ∈ Graph.VisibleEntry.silentExcess object piece
                data.threshold data.dischargeScale receiver,
              Graph.Route8.TraceBasin.Route8Entry object piece
                data.threshold data.LengthOK receiver load ∨
                ∃ basin : Finset object.Vertex,
                  Graph.Route8.TraceBasin.select? object piece
                      data.threshold receiver load = some basin ∧
                    ∃ retained,
                      Graph.Route8.TraceBasin.TraceResponseQuotient object
                        piece data.threshold data.LengthOK receiver load
                        basin retained) ∧
            ∀ outside ∈ Graph.VisibleEntry.completionPorts object piece
                receiver,
              data.dischargeScale ≤
                (Graph.VisibleEntry.visibleLoadsAt object piece
                  data.threshold receiver outside).card →
              ∀ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
                  data.threshold data.dischargeScale receiver outside ∅,
                Graph.Route8.TraceBasin.Route8Entry object piece
                  data.threshold data.LengthOK receiver load ∨
                  ∃ basin : Finset object.Vertex,
                    Graph.Route8.TraceBasin.select? object piece
                        data.threshold receiver load = some basin ∧
                      ∃ retained,
                        Graph.Route8.TraceBasin.TraceResponseQuotient object
                          piece data.threshold data.LengthOK receiver load
                          basin retained) ∨
        HandoffProduced data object packing piece) ∧
      -- The additive per-load publication
      -- (`lem:typeA-reduced-silent-residual` with the exit-(7) routing of
      -- `lem:typeA-exits-discharged`): at every saturated receiver, each
      -- unpaid silent-excess load and each selected visible unpeeled load
      -- of an overloaded completion port realizes the four-way split the
      -- executor derives before collapsing — the exit-(4) witness, the
      -- route-8 entry, the exit-(5) trace-response quotient, or the
      -- exit-(7) surviving separator whose recorded envelope is the
      -- produced decorated handoff.
      (∀ receiver ∈ Graph.VisibleEntry.saturatedReceivers object piece
          data.threshold data.dischargeScale,
        (∀ load ∈ Graph.VisibleEntry.silentExcess object piece
            data.threshold data.dischargeScale receiver,
          (∃ witness : Graph.ExitFour.Witness
              (Graph.HasCycleWithLength data.LengthOK) piece
              data.threshold data.dischargeScale receiver ∅,
            witness.load = load) ∨
            Graph.Route8.TraceBasin.Route8Entry object piece
              data.threshold data.LengthOK receiver load ∨
            (∃ basin : Finset object.Vertex,
              Graph.Route8.TraceBasin.select? object piece
                  data.threshold receiver load = some basin ∧
                ∃ retained,
                  Graph.Route8.TraceBasin.TraceResponseQuotient object
                    piece data.threshold data.LengthOK receiver load
                    basin retained) ∨
            ((∃ basin : Finset object.Vertex,
                Graph.Route8.TraceBasin.TraceSurvivingSeparator object
                  piece data.threshold data.LengthOK receiver load
                  basin) ∧
              HandoffProduced data object packing piece)) ∧
        ∀ outside ∈ Graph.VisibleEntry.completionPorts object piece
            receiver,
          data.dischargeScale ≤
            (Graph.VisibleEntry.visibleLoadsAt object piece
              data.threshold receiver outside).card →
          ∀ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
              data.threshold data.dischargeScale receiver outside ∅,
            (∃ witness : Graph.ExitFour.Witness
                (Graph.HasCycleWithLength data.LengthOK) piece
                data.threshold data.dischargeScale receiver ∅,
              witness.load = load) ∨
              Graph.Route8.TraceBasin.Route8Entry object piece
                data.threshold data.LengthOK receiver load ∨
              (∃ basin : Finset object.Vertex,
                Graph.Route8.TraceBasin.select? object piece
                    data.threshold receiver load = some basin ∧
                  ∃ retained,
                    Graph.Route8.TraceBasin.TraceResponseQuotient object
                      piece data.threshold data.LengthOK receiver load
                      basin retained) ∨
              ((∃ basin : Finset object.Vertex,
                  Graph.Route8.TraceBasin.TraceSurvivingSeparator object
                    piece data.threshold data.LengthOK receiver load
                    basin) ∧
                HandoffProduced data object packing piece)))

/-- Nodes `[89]`, `[93]`, `[94]`, `[109]`, `lem:typeA-port-return`: every
completion port of the selected object carries at least one anchored return.
`lem:bridgeless` says the port edge is on a cycle, and deleting it from that
cycle leaves the return.  This is what makes every saturated port test
nonvacuous: the alternatives at nodes `[95]`--`[107]` quantify over the
anchored returns of a port, and without this fact "no return of the port has
property `p`" would be satisfied by a port with no returns at all. -/
noncomputable abbrev TypeAPortReturnStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- `lem:typeA-port-return`, on the selected saturated Type A support
  -- carried by the literal incoming residual: every completion port of
  -- every receiver of that support carries an anchored return.
  (∃ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing ∧
      (∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
        ∃ member ∈ packing, ¬ Disjoint window member) ∧
      ∃ component ∈ object.canonicalPieces
          (object.remainderSupport packing),
        let piece := object.pieceSupport
          (object.remainderSupport packing) component
        object.NegativeNetCharge piece data.threshold
            data.dischargeScale ∧
          object.ambientSurplus piece data.threshold = 0 ∧
          (∃ selectedReceiver : object.Vertex,
            object.IsReceiver piece data.threshold selectedReceiver ∧
              object.Saturated piece data.threshold data.dischargeScale
                selectedReceiver) ∧
          ∀ receiver : object.Vertex,
            object.IsReceiver piece data.threshold receiver →
            ∀ outside ∈ Graph.VisibleEntry.completionPorts object piece
                receiver,
              Nonempty
                (Graph.VisibleEntry.AnchoredReturn object receiver outside))

/-- Every eligible completion port of the selected Type A support carries an
anchored return of power-of-two length.  The manuscript has no such
corollary and no label for it. -/
noncomputable abbrev PortPowerReturnStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  (∃ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing ∧
      (∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
        ∃ member ∈ packing, ¬ Disjoint window member) ∧
      ∃ component ∈ object.canonicalPieces
          (object.remainderSupport packing),
        let piece := object.pieceSupport
          (object.remainderSupport packing) component
        object.NegativeNetCharge piece data.threshold
            data.dischargeScale ∧
          object.ambientSurplus piece data.threshold = 0 ∧
          (∃ selectedReceiver : object.Vertex,
            object.IsReceiver piece data.threshold selectedReceiver ∧
              object.Saturated piece data.threshold data.dischargeScale
                selectedReceiver) ∧
          ∀ receiver : object.Vertex,
            object.IsReceiver piece data.threshold receiver →
            ∀ outside ∈ Graph.VisibleEntry.completionPorts object piece
                receiver,
              (∀ common : object.Vertex,
                object.graph.Adj receiver common →
                object.graph.Adj outside common →
                object.degree common ≠ data.threshold) →
              ∃ return' : Graph.VisibleEntry.AnchoredReturn object receiver outside,
                ∃ exponent : Nat,
                  2 ≤ exponent ∧ return'.path.length = 2 ^ exponent)

/-- Node `[93]`, yes arm — the entry of the saturated exit chain at node
`[95]`: some completion port of a saturated receiver of the Type A support
carries `s` visible receiver-entry returns, in the sense of
`def:typeA-visible-load`.  This is the hypothesis of
`lem:typeA-visible-entry`, whose conclusion is the exit list
`def:typeA-saturated-exits` (1)--(7); the exits themselves are the nodes
`[95]`--`[107]` this arm enters. -/
noncomputable abbrev TypeAVisibleEntryStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[93]`, yes: `def:typeA-visible-load`'s count at a completion port
  -- of a saturated receiver of the Type A support has reached the
  -- registered multiple.  This is the hypothesis of
  -- `lem:typeA-visible-entry`; its conclusion is the exit list the arm
  -- enters.
  (∃ packing : Finset (Finset object.Vertex),
    packing = canonicalWindowPacking data object ∧
      object.IsWindowPacking data.windowOrder packing ∧
      (∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
        ∃ member ∈ packing, ¬ Disjoint window member) ∧
      ∃ component ∈ object.canonicalPieces
          (object.remainderSupport packing),
        let piece := object.pieceSupport
          (object.remainderSupport packing) component
        object.NegativeNetCharge piece data.threshold
            data.dischargeScale ∧
          object.ambientSurplus piece data.threshold = 0 ∧
          ∃ receiver : object.Vertex,
            object.IsReceiver piece data.threshold receiver ∧
              object.Saturated piece data.threshold data.dischargeScale
                receiver ∧
              Nonempty
                (Graph.ExitFour.VisibleFourUnpeeledPackage piece
                  data.threshold data.dischargeScale receiver ∅))

/-- Node `[93]`, no arm — node `[94]`, `lem:typeA-silent-excess-count`: no
saturated receiver of the Type A support has a completion port carrying `s`
visible receiver-entry returns, so the visible-first excess basins of
`def:typeA-excess-basin` are silent and carry the whole excess,
`S_sil^exc(X) ≥ s·D_A(X)`.  Cleared of the division and the subtraction,
`|V(X)| ≤ S_sil^exc(X) + s·def⁺(X)`. -/
noncomputable abbrev TypeAVisibleFirstExcessStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[93]`, no -- node `[94]`, `lem:typeA-silent-excess-count`:
  -- `S_sil^exc(X) ≥ s·D_A(X)` at every Type A support, with
  -- `s·D_A(X) = |V(X)| − s·def⁺(X)` written without division or
  -- subtraction.
  (∃ packing : Finset (Finset object.Vertex),
    packing = canonicalWindowPacking data object ∧
      object.IsWindowPacking data.windowOrder packing ∧
      (∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
        ∃ member ∈ packing, ¬ Disjoint window member) ∧
      ∃ component ∈ object.canonicalPieces
          (object.remainderSupport packing),
        let piece := object.pieceSupport
          (object.remainderSupport packing) component
        object.NegativeNetCharge piece data.threshold
            data.dischargeScale ∧
          object.ambientSurplus piece data.threshold = 0 ∧
          (∀ otherReceiver : object.Vertex,
            object.IsReceiver piece data.threshold otherReceiver →
              object.Saturated piece data.threshold data.dischargeScale
                otherReceiver →
              ¬ Graph.ExitFour.VisibleFourUnpeeledAt piece
                data.threshold data.dischargeScale otherReceiver ∅) ∧
          ∃ receiver : object.Vertex,
            object.IsReceiver piece data.threshold receiver ∧
              object.Saturated piece data.threshold data.dischargeScale
                receiver ∧
              Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold
                  data.dischargeScale receiver ∅ ∧
              piece.card ≤
                (∑ other ∈ object.receivers piece data.threshold,
                  (Graph.VisibleEntry.silentExcess object piece
                    data.threshold data.dischargeScale other).card) +
                  data.dischargeScale *
                    object.positiveDeficiency piece data.threshold)

/-- Node `[95]`, yes arm — exit `(1)` of `def:typeA-saturated-exits`: *"an
anchored return through a completion port of `w` has length in `Mers`"*, at a
saturated receiver `w` of a Type A support.  `Mers` is the shifted accepted
set: the return's length plus the restored port edge is an accepted cycle
length.  `lem:return-equivalence` closes the port edge over the return, so
this alternative *is* a target cycle, which is why `lem:typeA-exits-discharged`
lists exit `(1)` among the closed exits. -/
noncomputable abbrev TypeAExitOneReturnStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  (∃ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing ∧
      (∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
        ∃ member ∈ packing, ¬ Disjoint window member) ∧
      ∃ component ∈ object.canonicalPieces
          (object.remainderSupport packing),
        let piece := object.pieceSupport
          (object.remainderSupport packing) component
        object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
          object.ambientSurplus piece data.threshold = 0 ∧
          ∃ receiver : object.Vertex,
            object.IsReceiver piece data.threshold receiver ∧
              object.Saturated piece data.threshold data.dischargeScale receiver ∧
              ∃ package : Graph.ExitFour.VisibleFourUnpeeledPackage piece
                  data.threshold data.dischargeScale receiver ∅,
                ∃ return' : Graph.VisibleEntry.AnchoredReturn object receiver
                    package.outside,
                  Graph.ShiftedCycleLength data.LengthOK return'.path.length)

/-- Node `[95]`, no arm — the entry of node `[97]`: no anchored return through
any completion port of any saturated receiver of any Type A support has
accepted length, so exit `(1)` is not the exit this branch realizes and the
saturated exit list continues at exit `(2)`. -/
noncomputable abbrev TypeAExitOneFreeStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  (∃ packing : Finset (Finset object.Vertex),
    packing = canonicalWindowPacking data object ∧
      object.IsWindowPacking data.windowOrder packing ∧
      (∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
        ∃ member ∈ packing, ¬ Disjoint window member) ∧
      ∃ component ∈ object.canonicalPieces
          (object.remainderSupport packing),
        let piece := object.pieceSupport
          (object.remainderSupport packing) component
        object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
          object.ambientSurplus piece data.threshold = 0 ∧
          ∃ receiver : object.Vertex,
            object.IsReceiver piece data.threshold receiver ∧
              object.Saturated piece data.threshold data.dischargeScale receiver ∧
              ∃ package : Graph.ExitFour.VisibleFourUnpeeledPackage piece
                  data.threshold data.dischargeScale receiver ∅,
                ∀ return' : Graph.VisibleEntry.AnchoredReturn object receiver
                    package.outside,
                  ¬ Graph.ShiftedCycleLength data.LengthOK return'.path.length)

/-- Node `[97]`, yes arm — exit `(2)` of `def:typeA-saturated-exits`: *"two
anchored receiver-entry returns through one completion port are internally
vertex-disjoint as anchored paths and their lengths sum to a power of two"*,
at a saturated receiver `w` of a Type A support.  Both returns run between the
two ends of the same port, so `lem:typeA-common-port-return-cycle` glues them
into a simple cycle of length `|P₁| + |P₂|`; the exit's own side condition is
that this sum is accepted, which is why `lem:typeA-exits-discharged` lists
exit `(2)` among the closed exits. -/
noncomputable abbrev TypeAExitTwoThetaStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  (∃ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing ∧
      (∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
        ∃ member ∈ packing, ¬ Disjoint window member) ∧
      ∃ component ∈ object.canonicalPieces
          (object.remainderSupport packing),
        let piece := object.pieceSupport
          (object.remainderSupport packing) component
        object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
          object.ambientSurplus piece data.threshold = 0 ∧
          ∃ receiver : object.Vertex,
            object.IsReceiver piece data.threshold receiver ∧
              object.Saturated piece data.threshold data.dischargeScale receiver ∧
              ∃ package : Graph.ExitFour.VisibleFourUnpeeledPackage piece
                  data.threshold data.dischargeScale receiver ∅,
                Graph.VisibleEntry.ExitTwoThrough object piece data.LengthOK
                  receiver package.outside)

/-- Node `[97]`, no arm — the entry of node `[99]`: at every saturated
receiver of every Type A support, no two receiver-entry returns through one
of its completion ports are internally vertex-disjoint with accepted total
length, so exit `(2)` is not the exit this branch realizes and the saturated
exit list continues at exit `(3)`. -/
noncomputable abbrev TypeAExitTwoFreeStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  (∃ packing : Finset (Finset object.Vertex),
    packing = canonicalWindowPacking data object ∧
      object.IsWindowPacking data.windowOrder packing ∧
      (∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
        ∃ member ∈ packing, ¬ Disjoint window member) ∧
      ∃ component ∈ object.canonicalPieces
          (object.remainderSupport packing),
        let piece := object.pieceSupport
          (object.remainderSupport packing) component
        object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
          object.ambientSurplus piece data.threshold = 0 ∧
          ∃ receiver : object.Vertex,
            object.IsReceiver piece data.threshold receiver ∧
              object.Saturated piece data.threshold data.dischargeScale receiver ∧
              ∃ package : Graph.ExitFour.VisibleFourUnpeeledPackage piece
                  data.threshold data.dischargeScale receiver ∅,
                ¬ Graph.VisibleEntry.ExitTwoThrough object piece data.LengthOK
                  receiver package.outside)

/-- Node `[99]`, yes arm — exit `(3)` of `def:typeA-saturated-exits`: *"a
shared `P₁₃` window violates the corresponding legal-label relation `C_s`"*.
`lem:typeA-visible-entry` reads it as *"if two traces pass through a common
`P₁₃` window, their labels are governed by the relations `C_s` of
`lem:labels`; failure of the corresponding `C_s` test is the stated label
collision"*: two outside vertices attach to one packed window, the simple path
joining them avoids that window, and the cycle their attachment coordinates
close through the window has accepted length.  `lem:typeA-exits-discharged`
lists exit `(3)` among the closed exits, and this is why: the collision *is* a
target event. -/
noncomputable abbrev TypeAExitThreeCollisionStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  (∃ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing ∧
      (∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
        ∃ member ∈ packing, ¬ Disjoint window member) ∧
      ∃ component ∈ object.canonicalPieces
          (object.remainderSupport packing),
        let piece := object.pieceSupport
          (object.remainderSupport packing) component
        object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
          object.ambientSurplus piece data.threshold = 0 ∧
          ∃ receiver : object.Vertex,
            object.IsReceiver piece data.threshold receiver ∧
              object.Saturated piece data.threshold data.dischargeScale receiver ∧
              ∃ package : Graph.ExitFour.VisibleFourUnpeeledPackage piece
                  data.threshold data.dischargeScale receiver ∅,
                Graph.WindowLabelCollision.LabelCollision object
                  data.windowOrder data.LengthOK packing)

/-- Node `[99]`, no arm — the entry of node `[101]`: every shared window of
the packing satisfies its legal-label relation at every outside connector, so
exit `(3)` is not the exit this branch realizes and the saturated exit list
continues at exit `(4)`. -/
noncomputable abbrev TypeAExitThreeFreeStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  (∃ packing : Finset (Finset object.Vertex),
    packing = canonicalWindowPacking data object ∧
      object.IsWindowPacking data.windowOrder packing ∧
      (∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
        ∃ member ∈ packing, ¬ Disjoint window member) ∧
      ∃ component ∈ object.canonicalPieces
          (object.remainderSupport packing),
        let piece := object.pieceSupport
          (object.remainderSupport packing) component
        object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
          object.ambientSurplus piece data.threshold = 0 ∧
          ∃ receiver : object.Vertex,
            object.IsReceiver piece data.threshold receiver ∧
              object.Saturated piece data.threshold data.dischargeScale receiver ∧
              ∃ package : Graph.ExitFour.VisibleFourUnpeeledPackage piece
                  data.threshold data.dischargeScale receiver ∅,
                Graph.WindowLabelCollision.LabelCollisionFree object
                  data.windowOrder data.LengthOK packing)

/-- **The shared entry of nodes `[101]`--`[107]`**, and the hypothesis of
`lem:typeA-exit4-residual-routing`: *"let `w` be a saturated Type A receiver
with a peeling set `P₄(w)`; if `L₄(w) ≥ 4q(w)`, then the unpeeled routed loads
at `w` realize one of exits (1)--(8)"*.

Figure 8 draws one segment `[101]`--`[107]` with *two* entries: node `[99]`'s
no arm, which is `lem:typeA-unpeeled-visible-routing` after exits `(1)`--`(3)`
have been denied, and node `[94]`, which is
`lem:typeA-unpeeled-silent-routing`.  `lem:typeA-exit4-residual-routing` is
the manuscript's own statement that the two combine, and this is its
hypothesis: the exit segment is asked under it and under nothing else, so the
segment is one chain of nodes rather than two copies.

It is a refinement of the residual node `[89]` already committed, not a new
assumption: at the empty peeling set `L₄(w) = L(w)`, so
`ExitFour.saturatedAfter_empty` reads it straight off
`typeASaturatedReceiver`.  No exit-(4) fact is currently produced from this
entry: the required coordinate-specific response realization is absent. -/
noncomputable abbrev TypeASaturatedExitEntryStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- The shared entry of nodes `[101]`--`[107]`, and the hypothesis of
  -- `lem:typeA-exit4-residual-routing`: a saturated Type A receiver with a
  -- peeling set whose residual load is still at or above the saturation
  -- threshold.  `def:typeA-exit4-peeling`'s `P₄(w) ⊆ ℒ(w)` and
  -- `L₄(w) ≥ s·q(w)` are the two clauses the routing lemma uses; the
  -- witnesses attached to the peeled loads are node `[102]`'s fact.
  (∃ packing : Finset (Finset object.Vertex),
    packing = canonicalWindowPacking data object ∧
      object.IsWindowPacking data.windowOrder packing ∧
      (∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
        ∃ member ∈ packing, ¬ Disjoint window member) ∧
      ∃ component ∈ object.canonicalPieces
          (object.remainderSupport packing),
        let piece := object.pieceSupport
          (object.remainderSupport packing) component
        object.NegativeNetCharge piece data.threshold
            data.dischargeScale ∧
          object.ambientSurplus piece data.threshold = 0 ∧
          ∃ receiver : object.Vertex,
            object.IsReceiver piece data.threshold receiver ∧
              ∃ peeled : Finset object.Vertex,
                peeled ⊆ object.routedLoads piece data.threshold receiver ∧
                  Graph.ExitFour.SaturatedAfter piece data.threshold
                    data.dischargeScale receiver peeled ∧
                  Graph.ExitFour.PeeledByWitnesses
                    (Graph.HasCycleWithLength data.LengthOK) piece
                    data.threshold data.dischargeScale receiver peeled)

/-- Node `[107]`, yes arm: the selected saturated-handoff residual, after
exits `(4)`--`(6)` have failed, produces the exit-`(7)` decorated handoff
envelope.  Node `[108]` records the handoff, and node `[65]` commits its
admissibility interface. -/
noncomputable abbrev TypeAExitSevenProducedStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[107]`, yes: exit `(7)` is produced on the exact selected
  -- no-exit-`(6)` residual.
  SelectedNoExitSixWith data object
    (fun packing piece => HandoffProduced data object packing piece)

/-- Node `[108]`, on node `[107]`'s yes arm — exit `(7)` of
`def:typeA-saturated-exits`: *"a high-degree decorated handoff fan envelope
is produced"*, at the visible saturated port node `[93]` delivered.  This is
the Type B handoff exit, and it is the one exit of the list that neither
closes nor stays in Type A:
`lem:typeA-exits-discharged` says the branch *"is reclassified as a decorated
handoff fan envelope and leaves the Type A charge calculation"*.

The envelope is `def:decorated-fan-envelope`'s `𝔛 = (Y, H)` with `Y` the Type
A support itself and `H` the surviving first separator of two declared outside
connector germs through the port — `def:typeA-trace-basin` clause (d), routed
by `lem:typeA-continuation-routing`, with ambient degree at least `4` by
`lem:typeA-cubic-switch-absorption` and handed over by
`lem:typeA-high-degree-handoff`.  This node records only that produced
envelope.  Node `[65]` proves `lem:decorated-fan-admissibility` from this fact
and the inherited selection, normalization, and uncompressibility facts on
the same ledger.  By `rem:typeA-typeB-stratification` no conclusion of
`lem:typeB-exclusion` is used, and none is available on this cursor. -/
noncomputable abbrev TypeAExitSevenHandoffStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[108]`: the produced envelope is committed as the Type B
  -- handoff.  Its admissibility is the fact proved at node `[65]`.
  SelectedNoExitSixWith data object
    (fun packing piece => HandoffProduced data object packing piece)

/-- Node `[107]`, no arm — the entry of node `[109]`: no high-degree decorated
handoff fan envelope is produced at any visible port of any saturated receiver
of any Type A support, so exit `(7)` is not the exit this branch realizes and
the saturated exit list continues at exit `(8)`, the route-8 residual of
`def:typeA-silent-core-residual`. -/
noncomputable abbrev TypeAExitSevenFreeStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[107]`, no: the same selected residual has no decorated
  -- handoff envelope and therefore enters the route-8 test.
  SelectedNoExitSixWith data object
    (fun packing piece => ¬ HandoffProduced data object packing piece)

/-- Node `[102]`: the exit-`(4)` witness has been charged to the peeling
ledger by adjoining its routed load to `P₄(w)`, preserving the routed-load
condition and dropping the residual load by one. -/
noncomputable abbrev TypeAExitFourPeeledStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[102]`: `lem:typeA-exit4-discharge`, read on the exact witness
  -- committed at node `[101]`.  The next peeling set is obtained by
  -- inserting that witness's routed load; it remains a subset of the routed
  -- loads and the residual load drops by exactly one.
  (∃ packing : Finset (Finset object.Vertex),
    packing = canonicalWindowPacking data object ∧
      object.IsWindowPacking data.windowOrder packing ∧
      (∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
        ∃ member ∈ packing, ¬ Disjoint window member) ∧
      ∃ component ∈ object.canonicalPieces
          (object.remainderSupport packing),
        let piece := object.pieceSupport
          (object.remainderSupport packing) component
        object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
          object.ambientSurplus piece data.threshold = 0 ∧
          ∃ receiver : object.Vertex,
            object.IsReceiver piece data.threshold receiver ∧
              ∃ peeled : Finset object.Vertex,
                peeled ⊆ object.routedLoads piece data.threshold receiver ∧
                  Graph.ExitFour.SaturatedAfter piece data.threshold
                    data.dischargeScale receiver peeled ∧
                  Graph.ExitFour.PeeledByWitnesses
                    (Graph.HasCycleWithLength data.LengthOK) piece
                    data.threshold data.dischargeScale receiver peeled ∧
                  ∃ witness : Graph.ExitFour.Witness
                      (Graph.HasCycleWithLength data.LengthOK) piece
                      data.threshold data.dischargeScale receiver peeled,
                    witness.load ∈ Graph.ExitFour.unpeeledLoads piece
                        data.threshold receiver peeled ∧
                      Graph.ExitFour.Witness.nextPeeled witness ⊆
                        object.routedLoads piece data.threshold receiver ∧
                      Graph.ExitFour.residualLoad piece data.threshold
                          receiver
                          (Graph.ExitFour.Witness.nextPeeled witness) + 1 =
                        Graph.ExitFour.residualLoad piece data.threshold
                          receiver peeled)

/-- `lem:typeA-exit4-residual-routing`, exit-`(4)` arm at the exact current
saturated receiver/peeling state. -/
noncomputable abbrev TypeASaturatedHandoffExitFourStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- `lem:typeA-exit4-residual-routing`, exit `(4)` at the current peeling
  -- state.  In the visible case the witness supports one of the selected
  -- four visible loads; in the silent case it supports a load from the
  -- canonical residual excess set `E₄(w)`.
  (∃ packing : Finset (Finset object.Vertex),
    packing = canonicalWindowPacking data object ∧
      object.IsWindowPacking data.windowOrder packing ∧
      (∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
        ∃ member ∈ packing, ¬ Disjoint window member) ∧
      ∃ component ∈ object.canonicalPieces
          (object.remainderSupport packing),
        let piece := object.pieceSupport
          (object.remainderSupport packing) component
        object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
          object.ambientSurplus piece data.threshold = 0 ∧
          ∃ receiver : object.Vertex,
            object.IsReceiver piece data.threshold receiver ∧
              ∃ peeled : Finset object.Vertex,
                peeled ⊆ object.routedLoads piece data.threshold receiver ∧
                  Graph.ExitFour.SaturatedAfter piece data.threshold
                    data.dischargeScale receiver peeled ∧
                  Graph.ExitFour.PeeledByWitnesses
                    (Graph.HasCycleWithLength data.LengthOK) piece
                    data.threshold data.dischargeScale receiver peeled ∧
                  ((∃ package :
                      Graph.ExitFour.VisibleFourUnpeeledPackage piece
                        data.threshold data.dischargeScale receiver peeled,
                    ∃ witness : Graph.ExitFour.Witness
                        (Graph.HasCycleWithLength data.LengthOK) piece
                        data.threshold data.dischargeScale receiver peeled,
                      ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads
                          piece data.threshold data.dischargeScale receiver
                          package.outside peeled,
                        witness.load = load) ∨
                    (Graph.ExitFour.SilentUnpeeledExcessAt piece
                        data.threshold data.dischargeScale receiver peeled ∧
                      ∃ witness : Graph.ExitFour.Witness
                          (Graph.HasCycleWithLength data.LengthOK) piece
                          data.threshold data.dischargeScale receiver peeled,
                        witness.load ∈ Graph.ExitFour.unpeeledExcess piece
                          data.threshold data.dischargeScale receiver peeled)))

/-- `lem:typeA-exit4-residual-routing`, no exit-`(4)` at the exact current
saturated receiver/peeling state; this is the predecessor of exit `(5)`. -/
noncomputable abbrev TypeASaturatedHandoffExitFourFreeStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- The selected current saturated-handoff state has no exit-`(4)`
  -- witness of the corresponding visible or silent kind.
  (∃ packing : Finset (Finset object.Vertex),
    packing = canonicalWindowPacking data object ∧
      object.IsWindowPacking data.windowOrder packing ∧
      (∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
        ∃ member ∈ packing, ¬ Disjoint window member) ∧
      ∃ component ∈ object.canonicalPieces
          (object.remainderSupport packing),
        let piece := object.pieceSupport
          (object.remainderSupport packing) component
        object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
          object.ambientSurplus piece data.threshold = 0 ∧
          ∃ receiver : object.Vertex,
            object.IsReceiver piece data.threshold receiver ∧
              ∃ peeled : Finset object.Vertex,
                peeled ⊆ object.routedLoads piece data.threshold receiver ∧
                  Graph.ExitFour.SaturatedAfter piece data.threshold
                    data.dischargeScale receiver peeled ∧
                  ExitFourFreeAt data object piece receiver peeled)

/-- Node `[102]`, no-loop arm: after the exit-`(4)` peel, the selected
receiver is no longer saturated at the peeled residual, so its remaining
receiver charge is nonnegative by `lem:typeA-exit4-peeling-charge`. -/
noncomputable abbrev TypeAExitFourReceiverDischargedStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[102]` → `[89]`, the retest after the exit-`(4)` descent
  -- (`lem:typeA-exit4-finite-descent`, `lem:typeA-exit4-peeling-charge`):
  -- the peeling set reached by charging exit-`(4)` witnesses leaves the
  -- selected receiver unsaturated at the peeled residual, i.e. its
  -- remaining receiver charge `q(w) − ¼ − ¼·L₄(w)` is nonnegative in the
  -- cleared scale.  The peeled loads are the receiver's target-defect
  -- entries for the pressure ledger.
  (∃ packing : Finset (Finset object.Vertex),
    packing = canonicalWindowPacking data object ∧
      object.IsWindowPacking data.windowOrder packing ∧
      (∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
        ∃ member ∈ packing, ¬ Disjoint window member) ∧
      ∃ component ∈ object.canonicalPieces
          (object.remainderSupport packing),
        let piece := object.pieceSupport
          (object.remainderSupport packing) component
        object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
          object.ambientSurplus piece data.threshold = 0 ∧
          ∃ receiver : object.Vertex,
            object.IsReceiver piece data.threshold receiver ∧
              ∃ peeled : Finset object.Vertex,
                peeled ⊆ object.routedLoads piece data.threshold receiver ∧
                  Graph.ExitFour.PeeledByWitnesses
                    (Graph.HasCycleWithLength data.LengthOK) piece
                    data.threshold data.dischargeScale receiver peeled ∧
                  ¬ Graph.ExitFour.SaturatedAfter piece data.threshold
                      data.dischargeScale receiver peeled ∧
                  1 + Graph.ExitFour.residualLoad piece data.threshold
                      receiver peeled ≤
                    data.dischargeScale *
                      object.missingPorts piece data.threshold receiver)

/-- Node `[103]`, yes arm: the exact selected saturated-handoff residual
after no exit `(4)` carries exit `(5)`, a target-complete proper-support
compression. -/
noncomputable abbrev TypeAExitFiveStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[103]`, yes: one load in the exact visible/silent post-exit-`(4)`
  -- residual has a selected trace basin whose declared `u`-supported
  -- response algebra admits alternative (b), including the paper's
  -- proper-realization / trace-response-only split.
  let exitFiveAt := ExitFiveAt data object
  (∃ packing : Finset (Finset object.Vertex),
    packing = canonicalWindowPacking data object ∧
      object.IsWindowPacking data.windowOrder packing ∧
      (∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
        ∃ member ∈ packing, ¬ Disjoint window member) ∧
      ∃ component ∈ object.canonicalPieces
          (object.remainderSupport packing),
        let piece := object.pieceSupport
          (object.remainderSupport packing) component
        object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
          object.ambientSurplus piece data.threshold = 0 ∧
          ∃ receiver : object.Vertex,
            object.IsReceiver piece data.threshold receiver ∧
              ∃ peeled : Finset object.Vertex,
                peeled ⊆ object.routedLoads piece data.threshold receiver ∧
                  Graph.ExitFour.SaturatedAfter piece data.threshold
                    data.dischargeScale receiver peeled ∧
                  exitFiveAt piece receiver peeled)

/-- Node `[103]`, no arm: the exact selected saturated-handoff residual
after no exit `(4)` carries no target-complete proper-support compression,
so the branch may continue to exit `(6)`. -/
noncomputable abbrev TypeAExitFiveFreeStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[103]`, no: the same exact post-exit-`(4)` residual is retained,
  -- and none of its eligible loads has alternative (b) at its selected
  -- trace basin.
  let exitFiveAt := ExitFiveAt data object
  (∃ packing : Finset (Finset object.Vertex),
    packing = canonicalWindowPacking data object ∧
      object.IsWindowPacking data.windowOrder packing ∧
      (∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
        ∃ member ∈ packing, ¬ Disjoint window member) ∧
      ∃ component ∈ object.canonicalPieces
          (object.remainderSupport packing),
        let piece := object.pieceSupport
          (object.remainderSupport packing) component
        object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
          object.ambientSurplus piece data.threshold = 0 ∧
          ∃ receiver : object.Vertex,
            object.IsReceiver piece data.threshold receiver ∧
              ∃ peeled : Finset object.Vertex,
                peeled ⊆ object.routedLoads piece data.threshold receiver ∧
                  Graph.ExitFour.SaturatedAfter piece data.threshold
                    data.dischargeScale receiver peeled ∧
                  ExitFourFreeAt data object piece receiver peeled ∧
                  ¬ exitFiveAt piece receiver peeled)

/-- Node `[105]`, yes arm: the selected saturated-handoff residual, after
exits `(4)` and `(5)` have failed, has a response equality that becomes
target-complete only after adjoining a larger connected support. -/
noncomputable abbrev TypeAExitSixStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[105]`, yes: the selected saturated handoff state, after exits
  -- `(4)` and `(5)` have failed, carries an equality of declared response
  -- coordinates that becomes target-complete only after adjoining a larger
  -- connected support.  The witness is tied to the incoming residual; it is
  -- not an arbitrary route-8 object.
  let exitFiveAt := ExitFiveAt data object
  (∃ packing : Finset (Finset object.Vertex),
    packing = canonicalWindowPacking data object ∧
      object.IsWindowPacking data.windowOrder packing ∧
      (∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
        ∃ member ∈ packing, ¬ Disjoint window member) ∧
      ∃ component ∈ object.canonicalPieces
          (object.remainderSupport packing),
        let piece := object.pieceSupport
          (object.remainderSupport packing) component
        object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
          object.ambientSurplus piece data.threshold = 0 ∧
          ∃ receiver : object.Vertex,
            object.IsReceiver piece data.threshold receiver ∧
              ∃ peeled : Finset object.Vertex,
                peeled ⊆ object.routedLoads piece data.threshold receiver ∧
                  Graph.ExitFour.SaturatedAfter piece data.threshold
                    data.dischargeScale receiver peeled ∧
                  ExitFourFreeAt data object piece receiver peeled ∧
                  (¬ exitFiveAt piece receiver peeled ∧
                    ExitSixDelocalizes data object piece receiver peeled))

/-- Node `[105]`, no arm: that same selected residual has no exit-`(6)`
delocalization, so it can continue to exit `(7)`. -/
noncomputable abbrev TypeAExitSixFreeStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[105]`, no: the same selected saturated handoff state has no
  -- exit-`(6)` delocalization witness.
  let exitFiveAt := ExitFiveAt data object
  (∃ packing : Finset (Finset object.Vertex),
    packing = canonicalWindowPacking data object ∧
      object.IsWindowPacking data.windowOrder packing ∧
      (∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
        ∃ member ∈ packing, ¬ Disjoint window member) ∧
      ∃ component ∈ object.canonicalPieces
          (object.remainderSupport packing),
        let piece := object.pieceSupport
          (object.remainderSupport packing) component
        object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
          object.ambientSurplus piece data.threshold = 0 ∧
          ∃ receiver : object.Vertex,
            object.IsReceiver piece data.threshold receiver ∧
              ∃ peeled : Finset object.Vertex,
                peeled ⊆ object.routedLoads piece data.threshold receiver ∧
                  Graph.ExitFour.SaturatedAfter piece data.threshold
                    data.dischargeScale receiver peeled ∧
                  ExitFourFreeAt data object piece receiver peeled ∧
                  (¬ exitFiveAt piece receiver peeled ∧
                    ¬ ExitSixDelocalizes data object piece receiver peeled))

/-- Node `[106]`, proper scope: the enlarging support is proper in `G`, so
`lem:proper-smearing` gives the replacement contradiction. -/
noncomputable abbrev TypeAExitSixProperStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[106]`, proper scope: `lem:proper-smearing` returns a
  -- proper-support replacement for the selected delocalization.
  (∃ support : Finset object.Vertex,
    Graph.Strategy.InterfaceReplacement.ReplacementSupport
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object support)

/-- Node `[106]`, global scope: `lem:no-silent-global-smearing` gives a
strictly smaller closed representative. -/
noncomputable abbrev TypeAExitSixGlobalStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[106]`, global scope: `lem:no-silent-global-smearing` returns a
  -- strictly smaller closed representative.
  (∃ representative : Graph.FiniteObject.{u},
    representative.LexicographicallySmaller object ∧
      Graph.MinimumDegreeAtLeast data.threshold representative ∧
        (Graph.HasCycleWithLength data.LengthOK representative →
          Graph.HasCycleWithLength data.LengthOK object))

end Hypostructure.Graph.Strategy.Spine
