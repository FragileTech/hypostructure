import Hypostructure.Graph.Statements.TypeA

/-!
# Statements: TypeB

Proof-agnostic statement definitions of the minimum-degree cycle spine:
Type B statements: fan entry, local dichotomy, certificates, lanes, B2, hybrid, bridge mass and triangular ports.
Every registered constant is an explicit `Parameters` argument; this module
imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u v

/-- `cor:uncompressible` at node `[14]`, as the envelope's admissibility reads
it. -/
abbrev handoffUncompressible (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Finset object.Vertex → Prop :=
  fun support =>
    ¬ Graph.Strategy.InterfaceReplacement.CompressibleSupport
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object support

/-- The counted core satisfies the paper's single compound core-safety clause:
it is `P₁₃`-free and has no internal sub-support of minimum degree at least the
registered baseline.  Keeping the conjunction in the existing predicate avoids
introducing a second certificate carrier for `lem:decorated-fan-admissibility`. -/
abbrev handoffWindowFree (data : Parameters) (object : Graph.FiniteObject.{u}) :
    Finset object.Vertex → Prop :=
  fun support =>
    (∀ window : Finset object.Vertex, window ⊆ support →
      ¬ object.InducesWindow data.windowOrder window) ∧
    ∀ internal : Finset object.Vertex, internal ⊆ support →
      ¬ Graph.MinimumDegreeAtLeast data.threshold (object.induce internal)

/-- The exact case-(ii) handoff of `lem:absorbed-germ-fan-data` for one selected
branch-excess half-edge.  Besides retaining the literal first-high corridor
datum, it carries the manuscript destination: an actual
`DecoratedHandoff.Envelope` whose counted core is the connected first-failure
prefix, lies in the canonical remainder, and satisfies the common decorated
handoff admissibility interface.  The routing and first-high indices retain
the source coordinates used by the later Type B decisions; the envelope is
the handoff payload. -/
noncomputable def AbsorbedGermFanEnvelopeWitness (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object)
    (centre : object.Vertex) : Prop := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  exact ∃ routing : ColdFailureRoutingStatement data object,
    ∃ epsilon : ColdEligibleHalfEdge data object,
    let classified := coldRoutedClassified data object routing
    let corridor := coldOccurrenceCorridorAt data object classified epsilon
    let traceEnd := coldRoutedTraceEnd data object routing epsilon
    germ = coldOccurrenceIncidence data object classified epsilon ∧
    ∃ firstIndex : corridor.Segment,
      centre = corridor.head firstIndex ∧
      firstIndex.1 ≤ traceEnd ∧
      data.threshold < object.degree centre ∧
        (∀ earlier : corridor.Segment, earlier.1 < firstIndex.1 →
          object.degree (corridor.head earlier) ≤ data.threshold) ∧
        (∀ neighbour : object.Vertex, object.graph.Adj centre neighbour →
          object.degree neighbour = data.threshold) ∧
      let core := corridor.prefixSupport traceEnd
      Graph.SupportComponents.Connected.ConnectedOn object core ∧
        core ⊆ object.remainderSupport
          (canonicalWindowPacking data object) ∧
        ∃ envelope : Graph.DecoratedHandoff.Envelope object data.LengthOK
            (handoffHighDegree data object)
            (handoffAbsorbing data object
              (canonicalWindowPacking data object)),
          envelope.core = core ∧
            envelope.decorations = {centre} ∧
            Graph.DecoratedHandoff.Admissible object data.LengthOK
              (handoffUncompressible data object)
              (handoffWindowFree data object) envelope ∧
            ∃ first second : object.Vertex,
              first ≠ second ∧
                first ∈ envelope.assigned centre ∧
                second ∈ envelope.assigned centre

/-- Node `[177]`, `lem:absorbed-germ-fan-data` (ii), the decorated handoff fan
support at the first high centre.  For every selected branch-excess half-edge
`ε` outside the subcubic candidate set, the retained first-failure prefix is a
connected subset of the canonical remainder and supplies the counted core.
The retained high vertex is its decoration; its actual neighbours are the
assigned first-neighbour set, with simple arms landing in that core and the
common fan-safe and admissibility conditions.  Thus every indexed datum has
the concrete decorated-envelope payload consumed at the Type B entry. -/
noncomputable def AbsorbedGermDecoratedAssignedSupportStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  let Eligible := ColdEligibleHalfEdge data object
  exact ∃ routing : ColdFailureRoutingStatement data object,
    let classified := coldRoutedClassified data object routing
    let incidence := coldOccurrenceIncidence data object classified
    let candidates := coldRoutedCandidates data object routing
    ∀ epsilon : Eligible,
      Sum.inl epsilon ∉ candidates →
      ∃ centre, AbsorbedGermFanEnvelopeWitness data object
        (incidence epsilon) centre

/-- **The ordinary Type B support of node `[64]`** (`def:admissible` with
`σ(X) > 0`): a connected piece of the remainder of a maximal packing carrying
negative net charge and positive assigned surplus, together with a clause `P`
about the packing and the piece.  A support is data and cannot travel, so each
`[64]`-entry fact is stated at every such support the object carries. -/
def TypeBSupportWith (data : Parameters) (object : Graph.FiniteObject.{u})
    (P : Finset (Finset object.Vertex) → Finset object.Vertex → Prop) : Prop :=
  ∃ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing ∧
      (∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
        ∃ member ∈ packing, ¬ Disjoint window member) ∧
      ∃ component ∈ object.canonicalPieces (object.remainderSupport packing),
        let piece := object.pieceSupport (object.remainderSupport packing) component
        object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
          0 < object.ambientSurplus piece data.threshold ∧
          P packing piece

/-- **`def:typeB-assigned-ledger`: the assigned centres `H_X` of a connected
Type B support `X = (Y_X, H_X)`.**  `Y_X` is the counted remainder core (a
canonical piece of the remainder) and `H_X` the high-degree fan centres whose
surplus units are assigned to `X`.  There are exactly two ways the manuscript
produces one, and both enter the same nodes `[67]`--`[85]` (Part VI's ordinary
entry `[64]`/`[65]` and its dashed handoff input `[66]`):

* the ordinary Type B support of node `[64]` (`def:admissible` with `σ(X) > 0`):
  `H_X` is the piece's own set of high centres (`def:canonical-decomp`);
* the decorated handoff fan envelope of `def:decorated-fan-envelope` reached
  from exit `(7)` at `[108]`: `Y_X` is the Type A support (`σ(Y_X) = 0`) and
  `H_X` its decorations, each with a nonempty assigned first-neighbour set of
  actual neighbours (`lem:decorated-fan-admissibility`). -/
def TypeBAssignedCentres (data : Parameters) (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex))
    (piece centres : Finset object.Vertex) : Prop :=
  (object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
      0 < object.ambientSurplus piece data.threshold ∧
      centres = Graph.TypeBRefinedSupport.centres object data.threshold piece) ∨
  (object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
      object.ambientSurplus piece data.threshold = 0 ∧
      ∃ envelope : Graph.DecoratedHandoff.Envelope object data.LengthOK
          (handoffHighDegree data object) (handoffAbsorbing data object packing),
        envelope.core = piece ∧ envelope.decorations = centres ∧
          centres.Nonempty ∧
          ∀ centre ∈ centres,
            (envelope.assigned centre).Nonempty ∧
              ∀ first ∈ envelope.assigned centre, object.graph.Adj centre first)

/-- **A Type B fan support with its assigned centres**, the common notion nodes
`[71]`--`[75]` are stated on: a canonical piece `Y_X` of the remainder of a
maximal packing together with assigned centres `H_X` in either of the two
manuscript forms, and a clause `P` about the packing, the core and the centres.
A support is data and cannot travel, so each fact is stated at every such
support the object carries. -/
def TypeBFanSupportWith (data : Parameters) (object : Graph.FiniteObject.{u})
    (P : Finset (Finset object.Vertex) → Finset object.Vertex →
      Finset object.Vertex → Prop) : Prop :=
  ∃ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing ∧
      (∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
        ∃ member ∈ packing, ¬ Disjoint window member) ∧
      ∃ component ∈ object.canonicalPieces (object.remainderSupport packing),
        let piece := object.pieceSupport (object.remainderSupport packing) component
        ∃ centres : Finset object.Vertex,
          TypeBAssignedCentres data object packing piece centres ∧
            P packing piece centres

/-- **The Type B envelope produced by
`lem:same-token-bottleneck-routing`.**  This is the downstream payload consumed
by the common Type B entry.  The exact-ledger handoff below additionally keeps
the certified source witness from which this envelope was routed. -/
def SameTokenTypeBHandoffEnvelopeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing ∧
      packing.card = object.windowPackingNumber data.windowOrder ∧
      ∃ core : Finset object.Vertex,
        ∃ envelope : Graph.DecoratedHandoff.Envelope object data.LengthOK
            (handoffHighDegree data object)
            (handoffAbsorbing data object packing),
          envelope.core = core ∧ envelope.decorations.Nonempty

/-- **Node `[65]`, the common Type B entry.**  The manuscript has three literal
input forms at this node.  The ordinary `[64]` lane carries a canonical
assigned support.  Node `[177]` carries indexed assigned supports containing
an actual connected remainder core, decorated envelope, and admissibility
proof.  Node `[144]` carries its own maximal packing and decorated same-token
handoff envelope.  All alternatives therefore expose the concrete Type B data
used by their common continuation; no corridor-tail-only proposition is an
entry contract. -/
def TypeBFanEntryStatement (data : Parameters) (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBFanSupportWith data object (fun _packing _piece centres =>
    centres.Nonempty ∧
      ∀ centre ∈ centres, Graph.IsHighCentre object data.threshold centre) ∨
  AbsorbedGermDecoratedAssignedSupportStatement data object ∨
  SameTokenTypeBHandoffEnvelopeStatement data object

/-- Node `[68]`, yes arm, for the indexed `[177]` input.  The complete family
of decorated handoff witnesses is retained, and one of its actual centres is
heavy.  This is the paper's test `d_G(h) > 4`, written relative to the registered
baseline rather than with an EG-specific numeral. -/
noncomputable def AbsorbedGermFanHeavyCentreStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  exact AbsorbedGermDecoratedAssignedSupportStatement data object ∧
    ∃ (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object)
        (centre : object.Vertex),
      AbsorbedGermFanEnvelopeWitness data object germ centre ∧
        data.threshold + 1 < object.degree centre

/-- Node `[68]`, no arm, for the indexed `[177]` input.  For every selected
half-edge the preserved decorated handoff witness can be chosen with its centre
at the unique high-but-not-heavy degree, namely `threshold + 1`. -/
noncomputable def AbsorbedGermFanDegreeFourCentresStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  exact AbsorbedGermDecoratedAssignedSupportStatement data object ∧
    ∀ (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object)
        (centre : object.Vertex),
      AbsorbedGermFanEnvelopeWitness data object germ centre →
        object.degree centre = data.threshold + 1

/-- Node `[68]`, yes arm, on each paper-prescribed Type B input.  The
same-token lane retains its literal packing, core, and decorated envelope and
tests heaviness on the envelope's actual decorations. -/
def TypeBFanHeavyCentreStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBFanSupportWith data object (fun _packing _piece centres =>
    ∃ centre ∈ centres, data.threshold + 1 < object.degree centre) ∨
  AbsorbedGermFanHeavyCentreStatement data object ∨
  ∃ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing ∧
      packing.card = object.windowPackingNumber data.windowOrder ∧
      ∃ core : Finset object.Vertex,
        ∃ envelope : Graph.DecoratedHandoff.Envelope object data.LengthOK
            (handoffHighDegree data object)
            (handoffAbsorbing data object packing),
          envelope.core = core ∧ envelope.decorations.Nonempty ∧
            ∃ centre ∈ envelope.decorations,
              data.threshold + 1 < object.degree centre

/-- Node `[68]`, no arm, on each paper-prescribed Type B input.  On the
same-token lane every retained decoration is high by the envelope, so failure
of the heavy test forces the unique high-but-not-heavy degree
`data.threshold + 1`. -/
def TypeBFanDegreeFourCentresStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBFanSupportWith data object (fun _packing _piece centres =>
    ∀ centre ∈ centres, object.degree centre = data.threshold + 1) ∨
  AbsorbedGermFanDegreeFourCentresStatement data object ∨
  ∃ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing ∧
      packing.card = object.windowPackingNumber data.windowOrder ∧
      ∃ core : Finset object.Vertex,
        ∃ envelope : Graph.DecoratedHandoff.Envelope object data.LengthOK
            (handoffHighDegree data object)
            (handoffAbsorbing data object packing),
          envelope.core = core ∧ envelope.decorations.Nonempty ∧
            ∀ centre ∈ envelope.decorations,
              object.degree centre = data.threshold + 1

/-- Node `[69]` on the indexed `[177]` lane.  The original absorbed-germ
witness and its indices remain the carrier; at the heavy centre selected by
`[68]`, `cor:heavy-center-local-dichotomy` supplies exactly the same local
alternative as on an ordinary Type B support. -/
noncomputable def AbsorbedGermFanLocalDichotomyStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  exact AbsorbedGermDecoratedAssignedSupportStatement data object ∧
    ∃ (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object)
        (centre : object.Vertex),
      AbsorbedGermFanEnvelopeWitness data object germ centre ∧
        data.threshold + 1 < object.degree centre ∧
        ((∃ left right : object.Vertex,
            Graph.FanCompatible object centre left right) ∨
          (object.degree centre - 2 ≤
              (Graph.triangularEndpoints object centre).card ∧
            3 ≤ (Graph.triangularEndpoints object centre).card))

/-- Node `[79]` on the indexed `[177]` lane.  For every selected cold
half-edge, the degree-`threshold + 1` decorated centre chosen by `[68]` carries
`cor:degree-four-local-activation` and the exact registered-scale fan profile.
No canonical remainder piece is inserted into this statement. -/
noncomputable def AbsorbedGermFanDegreeFourProfileStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  exact AbsorbedGermDecoratedAssignedSupportStatement data object ∧
    ∀ (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object)
        (centre : object.Vertex),
      AbsorbedGermFanEnvelopeWitness data object germ centre →
          object.degree centre = data.threshold + 1 ∧
          ((∃ left right : object.Vertex,
              Graph.FanCompatible object centre left right) ∨
            data.threshold - 1 ≤
              (Graph.triangularEndpoints object centre).card) ∧
          object.degree centre - data.threshold = 1 ∧
          ∀ fanEnvelope : Finset object.Vertex,
            Graph.TypeBFanIncidence.closedCount object data.threshold
                fanEnvelope centre ≤ data.threshold + 1 ∧
              Graph.TypeBFanIncidence.scaledDeficit object data.threshold
                  data.dischargeScale fanEnvelope centre =
                (data.dischargeScale : Int) *
                    (Graph.TypeBFanIncidence.closedCount object data.threshold
                      fanEnvelope centre : Int) -
                  (data.dischargeScale : Int) * (data.threshold : Int) +
                  ((data.threshold : Int) + 2)

/-- Node `[69]` on every paper-prescribed Type B input.  The same-token form
retains the exact packing, core, and envelope from `[144]` and applies the
paper's local dichotomy to each of its actual heavy decorations. -/
def TypeBFanLocalDichotomyStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBFanSupportWith data object (fun _packing _piece centres =>
      ∀ centre ∈ centres, data.threshold + 1 < object.degree centre →
        (∃ left right : object.Vertex,
          Graph.FanCompatible object centre left right) ∨
        (object.degree centre - 2 ≤
            (Graph.triangularEndpoints object centre).card ∧
          3 ≤ (Graph.triangularEndpoints object centre).card)) ∨
    AbsorbedGermFanLocalDichotomyStatement data object ∨
    ∃ packing : Finset (Finset object.Vertex),
      object.IsWindowPacking data.windowOrder packing ∧
        packing.card = object.windowPackingNumber data.windowOrder ∧
        ∃ core : Finset object.Vertex,
          ∃ envelope : Graph.DecoratedHandoff.Envelope object data.LengthOK
              (handoffHighDegree data object)
              (handoffAbsorbing data object packing),
            envelope.core = core ∧ envelope.decorations.Nonempty ∧
              ∀ centre ∈ envelope.decorations,
                data.threshold + 1 < object.degree centre →
                  (∃ left right : object.Vertex,
                    Graph.FanCompatible object centre left right) ∨
                  (object.degree centre - 2 ≤
                      (Graph.triangularEndpoints object centre).card ∧
                    3 ≤ (Graph.triangularEndpoints object centre).card)

/-- `lem:same-center-open-port-compatibility` on the selected residual object.
The paper's port hypotheses are all explicit; the conclusion is the canonical
fan-compatible pair used by the heavy-centre alternative. -/
def SameCenterOpenPortCompatibilityStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ centre : object.Vertex,
    Graph.IsHighCentre object data.threshold centre →
      ∀ left right : object.Vertex,
        object.graph.Adj centre left →
        object.graph.Adj centre right →
        left ≠ right →
        ¬ object.graph.Adj left right →
        Graph.IsOpenPort object centre left →
        Graph.IsOpenPort object centre right →
        Graph.FanCompatible object centre left right

/-- Node `[79]` on every paper-prescribed Type B input.  The same-token form
keeps the original envelope and records the paper's degree-four activation and
registered-scale profile at each decoration. -/
noncomputable def TypeBFanDegreeFourProfileStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBFanSupportWith data object (fun _packing _piece centres =>
      ∀ centre ∈ centres,
        object.degree centre = data.threshold + 1 ∧
        ((∃ left right : object.Vertex,
            Graph.FanCompatible object centre left right) ∨
          data.threshold - 1 ≤ (Graph.triangularEndpoints object centre).card) ∧
        object.degree centre - data.threshold = 1 ∧
        ∀ fanEnvelope : Finset object.Vertex,
          Graph.TypeBFanIncidence.closedCount object data.threshold
              fanEnvelope centre ≤ data.threshold + 1 ∧
            Graph.TypeBFanIncidence.scaledDeficit object data.threshold
                data.dischargeScale fanEnvelope centre =
              (data.dischargeScale : Int) *
                  (Graph.TypeBFanIncidence.closedCount object data.threshold
                    fanEnvelope centre : Int) -
                (data.dischargeScale : Int) * (data.threshold : Int) +
                ((data.threshold : Int) + 2)) ∨
    AbsorbedGermFanDegreeFourProfileStatement data object ∨
    ∃ packing : Finset (Finset object.Vertex),
      object.IsWindowPacking data.windowOrder packing ∧
        packing.card = object.windowPackingNumber data.windowOrder ∧
        ∃ core : Finset object.Vertex,
          ∃ envelope : Graph.DecoratedHandoff.Envelope object data.LengthOK
              (handoffHighDegree data object)
              (handoffAbsorbing data object packing),
            envelope.core = core ∧ envelope.decorations.Nonempty ∧
              ∀ centre ∈ envelope.decorations,
                object.degree centre = data.threshold + 1 ∧
                ((∃ left right : object.Vertex,
                    Graph.FanCompatible object centre left right) ∨
                  data.threshold - 1 ≤
                    (Graph.triangularEndpoints object centre).card) ∧
                object.degree centre - data.threshold = 1 ∧
                ∀ fanEnvelope : Finset object.Vertex,
                  Graph.TypeBFanIncidence.closedCount object data.threshold
                      fanEnvelope centre ≤ data.threshold + 1 ∧
                    Graph.TypeBFanIncidence.scaledDeficit object data.threshold
                        data.dischargeScale fanEnvelope centre =
                      (data.dischargeScale : Int) *
                          (Graph.TypeBFanIncidence.closedCount object data.threshold
                            fanEnvelope centre : Int) -
                        (data.dischargeScale : Int) * (data.threshold : Int) +
                        ((data.threshold : Int) + 2)

/-- `def:triangular-fan-core` on the active object.  Ports are represented by
their endpoints because the centre is fixed.  The shoulder finset is exactly
`N_G(x) \setminus {h}`; the core is the paper's induced vertex set, so the
ambient graph supplies its induced adjacency.  The four incidence relations
record precisely completion, central, cross-triangular, and outside edges. -/
def TriangularFanCoreStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ centre : object.Vertex,
    data.threshold + 1 < object.degree centre →
      ∀ ports : Finset object.Vertex,
        ports.Nonempty →
          ports ⊆ Graph.triangularEndpoints object centre →
            ∃ shoulders : object.Vertex → Finset object.Vertex,
              ∃ core : Finset object.Vertex,
                ∃ completion central crossTriangular outside :
                    object.Vertex → object.Vertex → object.Vertex → Prop,
                  (∀ endpoint ∈ ports,
                    (∀ vertex : object.Vertex,
                      vertex ∈ shoulders endpoint ↔
                        Graph.IsShoulder object centre endpoint vertex) ∧
                    (shoulders endpoint).card = 2 ∧
                    ∃ left right : object.Vertex,
                      left ∈ shoulders endpoint ∧
                        right ∈ shoulders endpoint ∧ left ≠ right ∧
                          object.graph.Adj left right) ∧
                  (∀ vertex : object.Vertex,
                    vertex ∈ core ↔
                      vertex = centre ∨ vertex ∈ ports ∨
                        ∃ endpoint ∈ ports, vertex ∈ shoulders endpoint) ∧
                  (∀ endpoint shoulder target : object.Vertex,
                    completion endpoint shoulder target ↔
                      endpoint ∈ ports ∧ shoulder ∈ shoulders endpoint ∧
                        object.graph.Adj shoulder target ∧ target ≠ endpoint ∧
                          target ∉ shoulders endpoint) ∧
                  (∀ endpoint shoulder target : object.Vertex,
                    central endpoint shoulder target ↔
                      completion endpoint shoulder target ∧ target = centre) ∧
                  (∀ endpoint shoulder target : object.Vertex,
                    crossTriangular endpoint shoulder target ↔
                      completion endpoint shoulder target ∧
                        ∃ other ∈ ports,
                          other ≠ endpoint ∧ target ∈ shoulders other) ∧
                  ∀ endpoint shoulder target : object.Vertex,
                    outside endpoint shoulder target ↔
                      completion endpoint shoulder target ∧ target ∉ core ∧
                    ¬ object.graph.Adj centre target

/-- `lem:triangular-shoulder-completion`, stated directly on the active graph.
`completion` is the paper's incidence predicate: an edge at a shoulder other
than the two edges inside its triangular port. -/
def TriangularShoulderCompletionStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ centre : object.Vertex,
    data.threshold + 1 < object.degree centre →
      ∀ endpoint ∈ Graph.triangularEndpoints object centre,
        ∃ left right : object.Vertex,
          Graph.IsShoulder object centre endpoint left ∧
          Graph.IsShoulder object centre endpoint right ∧ left ≠ right ∧
          object.graph.Adj left right ∧
          (∀ shoulder, shoulder = left ∨ shoulder = right →
            ∃ target : object.Vertex,
              object.graph.Adj shoulder target ∧ target ≠ endpoint ∧
                target ≠ left ∧ target ≠ right) ∧
          ¬ (object.graph.Adj centre left ∧ object.graph.Adj centre right) ∧
          (∀ shoulder, shoulder = left ∨ shoulder = right →
            object.graph.Adj centre shoulder →
              object.degree shoulder = data.threshold ∧
              ∀ target : object.Vertex,
                (object.graph.Adj shoulder target ∧ target ≠ endpoint ∧
                  target ≠ left ∧ target ≠ right) ↔ target = centre) ∧
          ∀ shoulder target,
            shoulder = left ∨ shoulder = right →
            object.graph.Adj shoulder target → target ≠ endpoint →
              target ≠ left → target ≠ right →
                object.graph.Adj centre target → target = centre

/-- `lem:triangular-port-return`, with `R_p` the endpoint-to-centre return and
`Q_p = R_p.tail`.  Thus the restored cycle has length `|Q_p| + 2 = |R_p| + 1`.
The final conjunct is precisely the noncentral shoulder-completion incidence
used by the next first-landing lemma. -/
def TriangularPortReturnStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ centre : object.Vertex,
    data.threshold + 1 < object.degree centre →
      ∀ endpoint ∈ Graph.triangularEndpoints object centre,
        ∃ left right : object.Vertex,
          Graph.IsShoulder object centre endpoint left ∧
          Graph.IsShoulder object centre endpoint right ∧ left ≠ right ∧
          ∃ return' : Graph.FiniteObject.SurplusPort.PortReturn
              object centre endpoint left right,
            endpoint ∉ return'.path.tail.support ∧
            ¬ data.LengthOK (return'.path.length + 1) ∧
            (return'.path.tail.length ≠ 1 →
              ∃ shoulder target : object.Vertex,
                (shoulder = left ∨ shoulder = right) ∧
                object.graph.Adj shoulder target ∧ target ≠ endpoint ∧
                target ≠ left ∧ target ≠ right ∧ target ≠ centre ∧
                s(shoulder, target) ∈ return'.path.tail.edges)

/-- `lem:triangular-first-landing`, stated for the literal predicates supplied
by `def:triangular-fan-core`.  The three displayed arms include their mutual
exclusions, so “exactly one” is part of the proposition rather than prose. -/
def TriangularFirstLandingStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ centre : object.Vertex,
    data.threshold + 1 < object.degree centre →
      ∀ ports : Finset object.Vertex,
        ports.Nonempty →
          ports ⊆ Graph.triangularEndpoints object centre →
            ∀ shoulders : object.Vertex → Finset object.Vertex,
              ∀ core : Finset object.Vertex,
                ∀ completion central crossTriangular outside :
                    object.Vertex → object.Vertex → object.Vertex → Prop,
                  (∀ endpoint ∈ ports,
                    (∀ vertex : object.Vertex,
                      vertex ∈ shoulders endpoint ↔
                        Graph.IsShoulder object centre endpoint vertex) ∧
                    (shoulders endpoint).card = 2 ∧
                    ∃ left right : object.Vertex,
                      left ∈ shoulders endpoint ∧
                        right ∈ shoulders endpoint ∧ left ≠ right ∧
                          object.graph.Adj left right) →
                  (∀ vertex : object.Vertex,
                    vertex ∈ core ↔
                      vertex = centre ∨ vertex ∈ ports ∨
                        ∃ endpoint ∈ ports, vertex ∈ shoulders endpoint) →
                  (∀ endpoint shoulder target : object.Vertex,
                    completion endpoint shoulder target ↔
                      endpoint ∈ ports ∧ shoulder ∈ shoulders endpoint ∧
                        object.graph.Adj shoulder target ∧ target ≠ endpoint ∧
                          target ∉ shoulders endpoint) →
                  (∀ endpoint shoulder target : object.Vertex,
                    central endpoint shoulder target ↔
                      completion endpoint shoulder target ∧ target = centre) →
                  (∀ endpoint shoulder target : object.Vertex,
                    crossTriangular endpoint shoulder target ↔
                      completion endpoint shoulder target ∧
                        ∃ other ∈ ports,
                          other ≠ endpoint ∧ target ∈ shoulders other) →
                  (∀ endpoint shoulder target : object.Vertex,
                    outside endpoint shoulder target ↔
                      completion endpoint shoulder target ∧ target ∉ core ∧
                        ¬ object.graph.Adj centre target) →
                  ∀ endpoint shoulder target : object.Vertex,
                    completion endpoint shoulder target →
                      ((central endpoint shoulder target ∧
                          ¬ crossTriangular endpoint shoulder target ∧
                          ¬ outside endpoint shoulder target) ∨
                        (crossTriangular endpoint shoulder target ∧
                          ¬ central endpoint shoulder target ∧
                          ¬ outside endpoint shoulder target) ∨
                        (outside endpoint shoulder target ∧
                          ¬ central endpoint shoulder target ∧
                          ¬ crossTriangular endpoint shoulder target)) ∧
                      (object.graph.Adj centre target → target = centre) ∧
                      target ∉ ports

/-- `lem:triangular-cross-shoulder` on the target-safe selected object.
An edge between two distinct shoulder pairs is represented by the literal
cross-incidence predicate in both orientations.  The first conclusion is the
paper's high-shoulder arm after its quadrilateral arm is discharged by target
safety; the second is the stated matching-size consequence on the residual
where every shoulder has degree below four. -/
def TriangularCrossShoulderStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ centre : object.Vertex,
    data.threshold + 1 < object.degree centre →
      ∀ ports : Finset object.Vertex,
        ports.Nonempty →
          ports ⊆ Graph.triangularEndpoints object centre →
            ∀ shoulders : object.Vertex → Finset object.Vertex,
              ∀ crossTriangular :
                  object.Vertex → object.Vertex → object.Vertex → Prop,
                (∀ endpoint ∈ ports,
                  (∀ vertex : object.Vertex,
                    vertex ∈ shoulders endpoint ↔
                      Graph.IsShoulder object centre endpoint vertex) ∧
                  (shoulders endpoint).card = 2 ∧
                  ∃ left right : object.Vertex,
                    left ∈ shoulders endpoint ∧
                      right ∈ shoulders endpoint ∧ left ≠ right ∧
                        object.graph.Adj left right) →
                (∀ endpoint shoulder target : object.Vertex,
                  crossTriangular endpoint shoulder target ↔
                    endpoint ∈ ports ∧ shoulder ∈ shoulders endpoint ∧
                      object.graph.Adj shoulder target ∧ target ≠ endpoint ∧
                        target ∉ shoulders endpoint ∧
                        ∃ other ∈ ports,
                          other ≠ endpoint ∧ target ∈ shoulders other) →
                ∀ first ∈ ports, ∀ second ∈ ports, first ≠ second →
                  let between := fun source target =>
                    crossTriangular first source target ∧
                      crossTriangular second target source
                  (∀ source target source' target',
                    between source target → between source' target' →
                      (source ≠ source' ∨ target ≠ target') →
                        ∃ shoulder,
                          (shoulder ∈ shoulders first ∨
                            shoulder ∈ shoulders second) ∧
                          4 ≤ object.degree shoulder) ∧
                  ((∀ shoulder,
                      (shoulder ∈ shoulders first ∨
                        shoulder ∈ shoulders second) →
                      object.degree shoulder < 4) →
                    ∀ source target source' target',
                      between source target → between source' target' →
                        source = source' ∧ target = target')

/-- `def:open-port-suppression`, identified with the generic simultaneous
tight-vertex suppression construction.  `CompatibleFamily` contains clauses
(a)--(c), `CenterCapacity` is clause (d), and `suppressed_adj` is the displayed
definition of `G / Q`. -/
noncomputable def OpenPortSuppressionStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  exact ∀ family : Graph.TightVertexSuppression.CompatibleFamily object,
    (∀ index,
      data.threshold <
        object.degree (family.configuration index).center) →
      (∀ index other,
        object.graph.Adj (family.configuration index).vertex other ↔
          other = (family.configuration index).center ∨
            other = (family.configuration index).left ∨
              other = (family.configuration index).right) ∧
      (∀ ⦃first second⦄, first ≠ second →
        Disjoint
          ({(family.configuration first).vertex,
            (family.configuration first).left,
            (family.configuration first).right} : Set object.Vertex)
          {(family.configuration second).vertex,
            (family.configuration second).left,
            (family.configuration second).right}) ∧
      (∀ first second,
        (family.configuration first).center ≠
            (family.configuration second).vertex ∧
          (family.configuration first).center ≠
            (family.configuration second).left ∧
          (family.configuration first).center ≠
            (family.configuration second).right) ∧
      Function.Injective (fun index =>
        s((family.configuration index).left,
          (family.configuration index).right)) ∧
      (∀ index,
        ¬ object.graph.Adj (family.configuration index).left
          (family.configuration index).right) ∧
      (family.CenterCapacity data.threshold ↔
        ∀ centre, data.threshold < object.degree centre →
          family.centerLoad centre ≤ object.degree centre - data.threshold) ∧
      family.deletedVertices = Finset.univ.image
        (fun index => (family.configuration index).vertex) ∧
      ∀ left right : family.suppressed.Vertex,
        family.suppressed.graph.Adj left right ↔
          object.graph.Adj left.1 right.1 ∨
            ∃ index,
              (left.1 = (family.configuration index).left ∧
                right.1 = (family.configuration index).right) ∨
              (left.1 = (family.configuration index).right ∧
                right.1 = (family.configuration index).left)

/-- `lem:open-port-suppression-safe`.  The capacity hypothesis is written in
the paper's clause-(d) form; the preceding definition fact identifies it with
the canonical simultaneous-suppression `CenterCapacity`.  The suppressed
graph is already a `FiniteObject`, so its finiteness and simplicity are
present in the type and the mathematical conclusion left to prove is the
paper's pointwise minimum-degree assertion. -/
noncomputable def OpenPortSuppressionSafeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  exact ∀ family : Graph.TightVertexSuppression.CompatibleFamily object,
    (∀ index,
      data.threshold <
        object.degree (family.configuration index).center) →
    (∀ centre, data.threshold < object.degree centre →
      family.centerLoad centre ≤ object.degree centre - data.threshold) →
    ∀ vertex : family.suppressed.Vertex,
      3 ≤ family.suppressed.degree vertex

/-- `lem:single-open-port-suppression-witness`.  `OpenPortWitness` states that
the path is simple, avoids the deleted port vertex, and has accepted restored
length.  Via `lengthOK_iff_powerOfTwo`, this is exactly a path of length
`2^j - 1` for some `j ≥ 2`. -/
noncomputable def SingleOpenPortSuppressionWitnessStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  exact ∀ configuration : Graph.TightVertexSuppression.Configuration object,
    data.threshold < object.degree configuration.center →
      Nonempty (Graph.FiniteObject.SurplusPort.OpenPortWitness object
        data.LengthOK configuration.vertex configuration.left
          configuration.right)

/-- `lem:suppressed-family-critical-cycle`.  The first conjunct is the
minimality-produced accepted cycle using a nonempty set of added chords.  The
second is the paper's conclusion for every accepted suppressed cycle: its
simultaneous expansion is a simple source cycle, has one extra edge per used
chord, and its lifted length is not accepted. -/
noncomputable def SuppressedFamilyCriticalCycleStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  exact ∀ family : Graph.TightVertexSuppression.CompatibleFamily object,
    Nonempty family.Index →
    (∀ index,
      data.threshold <
        object.degree (family.configuration index).center) →
    (∀ centre, data.threshold < object.degree centre →
      family.centerLoad centre ≤ object.degree centre - data.threshold) →
    (∃ certificate : Graph.CycleCertificate family.suppressed data.LengthOK,
      (family.usedChords certificate.walk).Nonempty) ∧
    ∀ certificate : Graph.CycleCertificate family.suppressed data.LengthOK,
      (family.usedChords certificate.walk).Nonempty ∧
        ∃ expanded : Graph.TightVertexSuppression.CompatibleFamily.ExpandedCycle
            family certificate,
          expanded.walk.length = certificate.walk.length +
              (family.usedChords certificate.walk).card ∧
            ¬ data.LengthOK expanded.walk.length

/-- `def:typeB-fan-safe`, without collapsing clauses (ii)--(v).  For any
literal predicates expressing the label, target-defect, target-compression,
and delocalization failures, the canonical fan-safe relation is the geometric
return prohibition together with the denial of each of those four failures. -/
def TypeBFanSafeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ (labelFailure targetDefect targetCompression delocalization :
      object.Vertex → object.Vertex → object.Vertex → Prop)
    (centre first second : object.Vertex),
    Graph.DecoratedHandoff.FanSafe object data.LengthOK
        (fun h u v => labelFailure h u v ∨ targetDefect h u v ∨
          targetCompression h u v ∨ delocalization h u v)
        centre first second ↔
      (∀ return' : Graph.DecoratedHandoff.FanReturn object centre first second,
        ¬ data.LengthOK (return'.walk.length + 2)) ∧
      ¬ labelFailure centre first second ∧
      ¬ targetDefect centre first second ∧
      ¬ targetCompression centre first second ∧
      ¬ delocalization centre first second

/-- `def:fan-closed-port`, using the canonical upstream assigned Type-B
profile.  The equivalence exposes clauses (a)--(c) of the manuscript; clause
(c) is the derived incidence classification proved by
`TypeBFanClosedPorts.IsFanClosed.incidence_classified`. -/
def FanClosedPortStatement (_data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ (profile : Graph.TypeBFanClosedPorts.Profile object)
      (endpoint : object.Vertex),
    profile.IsFanClosed endpoint ↔
      endpoint ∈ profile.remainder ∧
      (∀ shoulder,
        Graph.IsShoulder object profile.marked.fan.hub endpoint shoulder →
          shoulder ∈ profile.envelope) ∧
      (∀ shoulder,
        Graph.IsShoulder object profile.marked.fan.hub endpoint shoulder →
          profile.IsWindowIncidence endpoint shoulder ∨
            profile.IsNonWindowIncidence endpoint shoulder)

/-- `lem:compatible-pair-fan-closure`, in the exact canonical upstream form. -/
def CompatiblePairFanClosureStatement (_data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ (profile : Graph.TypeBFanClosedPorts.Profile object)
      (left right : object.Vertex),
    Graph.FanCompatible object profile.marked.fan.hub left right →
    left ∈ profile.remainder →
    right ∈ profile.remainder →
    (∀ shoulder,
      Graph.IsShoulder object profile.marked.fan.hub left shoulder →
        shoulder ∈ profile.envelope) →
    (∀ shoulder,
      Graph.IsShoulder object profile.marked.fan.hub right shoulder →
        shoulder ∈ profile.envelope) →
    profile.IsFanClosed left ∧ profile.IsFanClosed right ∧ left ≠ right

/-- `prop:fan-closed-port-typeB-routing`, in the canonical upstream form. -/
def FanClosedPortTypeBRoutingStatement (_data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ (profile : Graph.TypeBFanClosedPorts.Profile object)
      (ledger : Graph.ReceiverLoad.LoadCapacityProfile)
      (normal : Graph.NormalForm object 3 profile.marked.fan.hub),
    ledger.loadMultiplier = 4 →
    ∀ ports : Finset object.Vertex,
      (∀ vertex ∈ ports, profile.IsFanClosed vertex) →
      2 ≤ ports.card →
      ports.card ≤ profile.closedCount ∧
        (ports.card : ℚ) -
            (3 - ((object.degree profile.marked.fan.hub : ℚ) + 1) *
              (1 / (ledger.loadMultiplier : ℚ)))
          ≤ profile.closedNeighbourDeficit ledger ∧
        ((object.degree profile.marked.fan.hub : ℚ) + 1) *
            (1 / (ledger.loadMultiplier : ℚ)) - 1
          ≤ profile.closedNeighbourDeficit ledger ∧
        0 < profile.closedNeighbourDeficit ledger

/-- `cor:compatible-pair-typeB-routing`, in the canonical upstream form. -/
def CompatiblePairTypeBRoutingStatement (_data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ (profile : Graph.TypeBFanClosedPorts.Profile object)
      (ledger : Graph.ReceiverLoad.LoadCapacityProfile)
      (normal : Graph.NormalForm object 3 profile.marked.fan.hub),
    ledger.loadMultiplier = 4 →
    ∀ left right : object.Vertex,
      Graph.FanCompatible object profile.marked.fan.hub left right →
      left ∈ profile.remainder →
      right ∈ profile.remainder →
      (∀ shoulder,
        Graph.IsShoulder object profile.marked.fan.hub left shoulder →
          shoulder ∈ profile.envelope) →
      (∀ shoulder,
        Graph.IsShoulder object profile.marked.fan.hub right shoulder →
          shoulder ∈ profile.envelope) →
      2 ≤ profile.closedCount ∧
        ((object.degree profile.marked.fan.hub : ℚ) + 1) *
            (1 / (ledger.loadMultiplier : ℚ)) - 1
          ≤ profile.closedNeighbourDeficit ledger ∧
      0 < profile.closedNeighbourDeficit ledger

/-- `prop:triangular-port-typeB-routing`, in the canonical upstream form.
The family has the manuscript's exact size `k - 2`; every endpoint is recorded
on the remainder side and both of its triangular shoulder incidences are
assigned to the fan envelope. -/
def TriangularPortTypeBRoutingStatement (_data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ (profile : Graph.TypeBFanClosedPorts.Profile object)
      (ledger : Graph.ReceiverLoad.LoadCapacityProfile)
      (normal : Graph.NormalForm object 3 profile.marked.fan.hub),
    ledger.loadMultiplier = 4 →
    ∀ ports : Finset object.Vertex,
      ports ⊆ Graph.triangularEndpoints object profile.marked.fan.hub →
      ports.card = object.degree profile.marked.fan.hub - 2 →
      5 ≤ object.degree profile.marked.fan.hub →
      (∀ endpoint ∈ ports, endpoint ∈ profile.remainder) →
      (∀ endpoint ∈ ports, ∀ shoulder,
        Graph.IsShoulder object profile.marked.fan.hub endpoint shoulder →
          shoulder ∈ profile.envelope) →
      ports.card ≤ profile.closedCount ∧
        (5 * (object.degree profile.marked.fan.hub : ℚ) - 19) / 4 ≤
          profile.closedNeighbourDeficit ledger ∧
        0 < profile.closedNeighbourDeficit ledger

/-- Node `[70]` on the indexed `[177]` lane.  The fan-certificate cap is
pointwise and therefore applies directly to every actual decorated centre;
the corridor/envelope indices are retained and no canonical support is
manufactured. -/
noncomputable def AbsorbedGermFanCertificateCapStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  exact AbsorbedGermDecoratedAssignedSupportStatement data object ∧
    ∀ (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object)
        (centre : object.Vertex),
      AbsorbedGermFanEnvelopeWitness data object germ centre →
        ∀ _marking : Graph.FanCertificateLabelling object data.windowOrder centre,
          object.degree centre ≤ Graph.WindowCurvature.fanPackingCap data.windowOrder

/-- Node `[70]` on every paper-prescribed Type B input.  The same-token form
retains the exact `[144]` envelope and states the label-packing cap pointwise
on its actual decorations. -/
noncomputable def TypeBFanCertificateCapStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBFanSupportWith data object (fun _packing _piece centres =>
      ∀ centre ∈ centres,
        ∀ _marking : Graph.FanCertificateLabelling object data.windowOrder centre,
          object.degree centre ≤
            Graph.WindowCurvature.fanPackingCap data.windowOrder) ∨
    AbsorbedGermFanCertificateCapStatement data object ∨
    ∃ packing : Finset (Finset object.Vertex),
      object.IsWindowPacking data.windowOrder packing ∧
        packing.card = object.windowPackingNumber data.windowOrder ∧
        ∃ core : Finset object.Vertex,
          ∃ envelope : Graph.DecoratedHandoff.Envelope object data.LengthOK
              (handoffHighDegree data object)
              (handoffAbsorbing data object packing),
            envelope.core = core ∧ envelope.decorations.Nonempty ∧
              ∀ centre ∈ envelope.decorations,
                ∀ _marking : Graph.FanCertificateLabelling object
                    data.windowOrder centre,
                  object.degree centre ≤
                    Graph.WindowCurvature.fanPackingCap data.windowOrder

/-- Node `[71]`/`[80]`, yes arm, on the indexed `[177]` lane.  The complete
absorbed family is retained, and every actual centre witnessing one of its
selected corridor entries carries the paper's fan-certificate labelling and
the cap already proved at `[70]`. -/
noncomputable def AbsorbedGermFanCertificateMarkedStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  exact AbsorbedGermDecoratedAssignedSupportStatement data object ∧
    ∀ (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object)
        (centre : object.Vertex),
      AbsorbedGermFanEnvelopeWitness data object germ centre →
        ∃ _marking : Graph.FanCertificateLabelling object data.windowOrder centre,
          object.degree centre ≤ Graph.WindowCurvature.fanPackingCap data.windowOrder

/-- Node `[71]`/`[80]`, no arm, on the indexed `[177]` lane.  The full
absorbed family remains available and one of its literal corridor-indexed
centres has no fan-certificate labelling. -/
noncomputable def AbsorbedGermFanCertificateResidualStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  exact AbsorbedGermDecoratedAssignedSupportStatement data object ∧
    ∃ (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object)
        (centre : object.Vertex),
      AbsorbedGermFanEnvelopeWitness data object germ centre ∧
        IsEmpty (Graph.FanCertificateLabelling object data.windowOrder centre)

/-- Nodes `[71]`/`[80]`, yes arm, on every paper-prescribed Type B input.
The same-token form retains the exact packing, core, and envelope and records
the certificate labelling, together with `[70]`'s cap, at every actual
decoration. -/
noncomputable def TypeBFanCertificateMarkedStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBFanSupportWith data object (fun _packing _piece centres =>
      ∀ centre ∈ centres,
        ∃ _marking : Graph.FanCertificateLabelling object data.windowOrder centre,
          object.degree centre ≤
            Graph.WindowCurvature.fanPackingCap data.windowOrder) ∨
    AbsorbedGermFanCertificateMarkedStatement data object ∨
    ∃ packing : Finset (Finset object.Vertex),
      object.IsWindowPacking data.windowOrder packing ∧
        packing.card = object.windowPackingNumber data.windowOrder ∧
        ∃ core : Finset object.Vertex,
          ∃ envelope : Graph.DecoratedHandoff.Envelope object data.LengthOK
              (handoffHighDegree data object)
              (handoffAbsorbing data object packing),
            envelope.core = core ∧ envelope.decorations.Nonempty ∧
              ∀ centre ∈ envelope.decorations,
                ∃ _marking : Graph.FanCertificateLabelling object
                    data.windowOrder centre,
                  object.degree centre ≤
                    Graph.WindowCurvature.fanPackingCap data.windowOrder

/-- Nodes `[71]`/`[80]`, no arm, on every paper-prescribed Type B input.  The
same-token form retains the exact incoming envelope and one of its literal
high-degree decorations at which no fan-certificate labelling exists. -/
noncomputable def TypeBFanCertificateResidualStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBFanSupportWith data object (fun _packing _piece centres =>
      ∃ centre ∈ centres,
        Graph.IsHighCentre object data.threshold centre ∧
          IsEmpty (Graph.FanCertificateLabelling object data.windowOrder centre)) ∨
    AbsorbedGermFanCertificateResidualStatement data object ∨
    ∃ packing : Finset (Finset object.Vertex),
      object.IsWindowPacking data.windowOrder packing ∧
        packing.card = object.windowPackingNumber data.windowOrder ∧
        ∃ core : Finset object.Vertex,
          ∃ envelope : Graph.DecoratedHandoff.Envelope object data.LengthOK
              (handoffHighDegree data object)
              (handoffAbsorbing data object packing),
            envelope.core = core ∧ envelope.decorations.Nonempty ∧
              ∃ centre ∈ envelope.decorations,
                Graph.IsHighCentre object data.threshold centre ∧
                  IsEmpty (Graph.FanCertificateLabelling object
                    data.windowOrder centre)

/-- Node `[74]`/`[82]` on the indexed `[177]` lane.  The marked absorbed
family is retained while the hybrid B1 calculation is recorded at each actual
centre selected by its corridor witness. -/
noncomputable def AbsorbedGermFanHybridEntryStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  exact AbsorbedGermFanCertificateMarkedStatement data object ∧
    ∀ (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object)
        (centre : object.Vertex),
      AbsorbedGermFanEnvelopeWitness data object germ centre →
        ∀ envelope windowSupport : Finset object.Vertex,
          (∀ left ∈ Graph.TypeBFanIncidence.closedNeighbours object
              data.threshold envelope centre,
            ∀ right ∈ Graph.TypeBFanIncidence.closedNeighbours object
                data.threshold envelope centre,
              left ≠ right →
              ∀ shared : object.Vertex,
                shared ∈ Graph.TypeBHybridIncidence.nonHubIncidences object
                  centre left →
                shared ∉ Graph.TypeBHybridIncidence.nonHubIncidences object
                  centre right) ∧
          Graph.TypeBHybridIncidence.windowIncidences object data.threshold
                envelope windowSupport centre +
              Graph.TypeBHybridIncidence.nonWindowIncidences object
                data.threshold envelope windowSupport centre =
            (data.threshold - 1) *
              Graph.TypeBFanIncidence.closedCount object data.threshold envelope centre ∧
          2 * Graph.TypeBFanIncidence.scaledDeficit object data.threshold
                  data.dischargeScale envelope centre ≤
              (data.dischargeScale : Int) *
                ((Graph.TypeBHybridIncidence.windowIncidences object
                    data.threshold envelope windowSupport centre : Int) +
                  (Graph.TypeBHybridIncidence.nonWindowIncidences object
                    data.threshold envelope windowSupport centre : Int)) ∧
          Graph.TypeBHybridIncidence.nonWindowDemand object data.threshold
                data.dischargeScale envelope windowSupport centre ≤
              (data.dischargeScale : Int) *
                (Graph.TypeBHybridIncidence.nonWindowIncidences object
                  data.threshold envelope windowSupport centre : Int) ∧
          (2 ≤ Graph.TypeBFanIncidence.closedCount object data.threshold
              envelope centre →
            0 < Graph.TypeBFanIncidence.scaledDeficit object data.threshold
              data.dischargeScale envelope centre)

/-- Node `[74]`/`[82]` on every paper-prescribed Type B carrier.  The
same-token form retains `[144]`'s exact packing, core, and marked envelope and
publishes the local B1 incidence calculation at each actual decoration. -/
noncomputable def TypeBFanHybridEntryStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBFanSupportWith data object (fun _packing _piece centres =>
      ∀ centre ∈ centres,
        Graph.IsHighCentre object data.threshold centre →
          ∀ envelope windowSupport : Finset object.Vertex,
            (∀ left ∈ Graph.TypeBFanIncidence.closedNeighbours object
                data.threshold envelope centre,
              ∀ right ∈ Graph.TypeBFanIncidence.closedNeighbours object
                  data.threshold envelope centre,
                left ≠ right →
                ∀ shared : object.Vertex,
                  shared ∈ Graph.TypeBHybridIncidence.nonHubIncidences object
                    centre left →
                  shared ∉ Graph.TypeBHybridIncidence.nonHubIncidences object
                    centre right) ∧
            Graph.TypeBHybridIncidence.windowIncidences object data.threshold
                  envelope windowSupport centre +
                Graph.TypeBHybridIncidence.nonWindowIncidences object
                  data.threshold envelope windowSupport centre =
              (data.threshold - 1) *
                Graph.TypeBFanIncidence.closedCount object data.threshold
                  envelope centre ∧
            2 * Graph.TypeBFanIncidence.scaledDeficit object data.threshold
                    data.dischargeScale envelope centre ≤
                (data.dischargeScale : Int) *
                  ((Graph.TypeBHybridIncidence.windowIncidences object
                      data.threshold envelope windowSupport centre : Int) +
                    (Graph.TypeBHybridIncidence.nonWindowIncidences object
                      data.threshold envelope windowSupport centre : Int)) ∧
            Graph.TypeBHybridIncidence.nonWindowDemand object data.threshold
                  data.dischargeScale envelope windowSupport centre ≤
                (data.dischargeScale : Int) *
                  (Graph.TypeBHybridIncidence.nonWindowIncidences object
                    data.threshold envelope windowSupport centre : Int) ∧
            (2 ≤ Graph.TypeBFanIncidence.closedCount object data.threshold
                envelope centre →
              0 < Graph.TypeBFanIncidence.scaledDeficit object data.threshold
                data.dischargeScale envelope centre)) ∨
    AbsorbedGermFanHybridEntryStatement data object ∨
    ∃ packing : Finset (Finset object.Vertex),
      object.IsWindowPacking data.windowOrder packing ∧
        packing.card = object.windowPackingNumber data.windowOrder ∧
        ∃ core : Finset object.Vertex,
          ∃ handoff : Graph.DecoratedHandoff.Envelope object data.LengthOK
              (handoffHighDegree data object)
              (handoffAbsorbing data object packing),
            handoff.core = core ∧ handoff.decorations.Nonempty ∧
              (∀ centre ∈ handoff.decorations,
                ∃ _marking : Graph.FanCertificateLabelling object
                    data.windowOrder centre,
                  object.degree centre ≤
                    Graph.WindowCurvature.fanPackingCap data.windowOrder) ∧
              ∀ centre ∈ handoff.decorations,
                ∀ envelope windowSupport : Finset object.Vertex,
                  (∀ left ∈ Graph.TypeBFanIncidence.closedNeighbours object
                      data.threshold envelope centre,
                    ∀ right ∈ Graph.TypeBFanIncidence.closedNeighbours object
                        data.threshold envelope centre,
                      left ≠ right →
                      ∀ shared : object.Vertex,
                        shared ∈ Graph.TypeBHybridIncidence.nonHubIncidences
                          object centre left →
                        shared ∉ Graph.TypeBHybridIncidence.nonHubIncidences
                          object centre right) ∧
                  Graph.TypeBHybridIncidence.windowIncidences object
                        data.threshold envelope windowSupport centre +
                      Graph.TypeBHybridIncidence.nonWindowIncidences object
                        data.threshold envelope windowSupport centre =
                    (data.threshold - 1) *
                      Graph.TypeBFanIncidence.closedCount object data.threshold
                        envelope centre ∧
                  2 * Graph.TypeBFanIncidence.scaledDeficit object
                          data.threshold data.dischargeScale envelope centre ≤
                      (data.dischargeScale : Int) *
                        ((Graph.TypeBHybridIncidence.windowIncidences object
                            data.threshold envelope windowSupport centre : Int) +
                          (Graph.TypeBHybridIncidence.nonWindowIncidences object
                            data.threshold envelope windowSupport centre : Int)) ∧
                  Graph.TypeBHybridIncidence.nonWindowDemand object
                        data.threshold data.dischargeScale envelope windowSupport
                        centre ≤
                      (data.dischargeScale : Int) *
                        (Graph.TypeBHybridIncidence.nonWindowIncidences object
                          data.threshold envelope windowSupport centre : Int) ∧
                  (2 ≤ Graph.TypeBFanIncidence.closedCount object data.threshold
                      envelope centre →
                    0 < Graph.TypeBFanIncidence.scaledDeficit object
                      data.threshold data.dischargeScale envelope centre)

/-- Node `[72]`/`[81]`, direct-cycle arm, on the indexed `[177]` lane. -/
noncomputable def AbsorbedGermFanDirectCycleStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  exact AbsorbedGermFanCertificateMarkedStatement data object ∧
    ∃ (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object)
        (centre : object.Vertex),
      AbsorbedGermFanEnvelopeWitness data object germ centre ∧
        Graph.TypeBDirectCycle.DirectCycleConfiguration object data.windowOrder
          data.LengthOK (canonicalWindowPacking data object) centre

/-- Node `[72]`/`[81]`, direct-cycle-free arm, on the indexed `[177]` lane. -/
noncomputable def AbsorbedGermFanDirectCycleFreeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  exact AbsorbedGermFanCertificateMarkedStatement data object ∧
    ∀ (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object)
        (centre : object.Vertex),
      AbsorbedGermFanEnvelopeWitness data object germ centre →
        Graph.TypeBDirectCycle.DirectCycleFree object data.windowOrder data.LengthOK
          (canonicalWindowPacking data object) centre

/-- Node `[72]`/`[81]`, direct-cycle arm, on every paper-prescribed Type B
carrier.  The same-token form tests the actual decorations against the exact
packing retained from `[144]`. -/
noncomputable def TypeBFanDirectCycleStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBFanSupportWith data object (fun packing _piece centres =>
      ∃ centre ∈ centres,
        Graph.IsHighCentre object data.threshold centre ∧
          Graph.TypeBDirectCycle.DirectCycleConfiguration object
            data.windowOrder data.LengthOK packing centre) ∨
    AbsorbedGermFanDirectCycleStatement data object ∨
    ∃ packing : Finset (Finset object.Vertex),
      object.IsWindowPacking data.windowOrder packing ∧
        packing.card = object.windowPackingNumber data.windowOrder ∧
        ∃ core : Finset object.Vertex,
          ∃ envelope : Graph.DecoratedHandoff.Envelope object data.LengthOK
              (handoffHighDegree data object)
              (handoffAbsorbing data object packing),
            envelope.core = core ∧ envelope.decorations.Nonempty ∧
              (∀ centre ∈ envelope.decorations,
                ∃ _marking : Graph.FanCertificateLabelling object
                    data.windowOrder centre,
                  object.degree centre ≤
                    Graph.WindowCurvature.fanPackingCap data.windowOrder) ∧
              ∃ centre ∈ envelope.decorations,
                Graph.IsHighCentre object data.threshold centre ∧
                  Graph.TypeBDirectCycle.DirectCycleConfiguration object
                    data.windowOrder data.LengthOK packing centre

/-- Node `[72]`/`[81]`, direct-cycle-free arm, on every paper-prescribed Type B
carrier.  The same-token form retains the marked envelope and records the
absence of every direct configuration at its actual decorations. -/
noncomputable def TypeBFanDirectCycleFreeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBFanSupportWith data object (fun packing _piece centres =>
      ∀ centre ∈ centres,
        Graph.IsHighCentre object data.threshold centre →
          Graph.TypeBDirectCycle.DirectCycleFree object data.windowOrder
            data.LengthOK packing centre) ∨
    AbsorbedGermFanDirectCycleFreeStatement data object ∨
    ∃ packing : Finset (Finset object.Vertex),
      object.IsWindowPacking data.windowOrder packing ∧
        packing.card = object.windowPackingNumber data.windowOrder ∧
        ∃ core : Finset object.Vertex,
          ∃ envelope : Graph.DecoratedHandoff.Envelope object data.LengthOK
              (handoffHighDegree data object)
              (handoffAbsorbing data object packing),
            envelope.core = core ∧ envelope.decorations.Nonempty ∧
              (∀ centre ∈ envelope.decorations,
                ∃ _marking : Graph.FanCertificateLabelling object
                    data.windowOrder centre,
                  object.degree centre ≤
                    Graph.WindowCurvature.fanPackingCap data.windowOrder) ∧
              ∀ centre ∈ envelope.decorations,
                Graph.IsHighCentre object data.threshold centre →
                  Graph.TypeBDirectCycle.DirectCycleFree object
                    data.windowOrder data.LengthOK packing centre

/-- Node `[72]`/`[81]`, B2 yes arm, on the literal indexed `[177]` fan datum.
For every retained cold-corridor witness, its actual heavy centre admits the
paper's candidate entry on that same first-failure support.  The singleton is
the one centre whose discarded half-edge is being charged; no decorated Type A
core is manufactured. -/
noncomputable def AbsorbedGermFanB2ChoiceStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  let packing := canonicalWindowPacking data object
  exact AbsorbedGermFanDirectCycleFreeStatement data object ∧
    ∀ (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object)
        (centre : object.Vertex),
      AbsorbedGermFanEnvelopeWitness data object germ centre →
        Graph.TypeBRefinedSupport.HasDisjointChoice object data.threshold
          data.dischargeScale packing germ.support {centre} {centre}

/-- Node `[72]`/`[81]`, B2 no arm, on the literal indexed `[177]` fan datum.
The published failure is the paper's genuine minimal overlap obstruction on
the same first-failure support and its actual heavy centre. -/
noncomputable def AbsorbedGermFanB2ObstructionStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  let packing := canonicalWindowPacking data object
  exact AbsorbedGermFanDirectCycleFreeStatement data object ∧
    ∃ (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object)
        (centre : object.Vertex),
      AbsorbedGermFanEnvelopeWitness data object germ centre ∧
        Nonempty (Graph.TypeBRefinedSupport.OverlapObstruction object
          data.threshold data.dischargeScale packing germ.support {centre})

/-- Nodes `[74]`/`[82]` on the indexed `[177]` lane.  This is the literal
successful B2(a)--(c) datum on the first-failure support: it retains the
chosen `DisjointChoice`, hence all of its candidate and pairwise-disjoint
carrier fields, and records the candidate's nonnegative augmented payment.
It deliberately does not manufacture a canonical remainder piece or assert
the post-ledger Type A component conclusions that require one. -/
noncomputable def AbsorbedGermFanB2PaidStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  let packing := canonicalWindowPacking data object
  exact AbsorbedGermFanB2ChoiceStatement data object ∧
    ∀ (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object)
        (centre : object.Vertex),
      AbsorbedGermFanEnvelopeWitness data object germ centre →
        ∃ choice : Graph.TypeBRefinedSupport.DisjointChoice object
            data.threshold data.dischargeScale packing germ.support {centre} {centre},
          ∀ member : centre ∈ ({centre} : Finset object.Vertex),
            (choice.entry centre member).EntryRefines data.threshold
              data.dischargeScale germ.support centre

/-- Node `[84]` on the indexed `[177]` B2-failure lane.  The mass estimate is
attached to the same corridor indices, actual heavy centre, first-failure
support, and minimal overlap obstruction; no canonical support is substituted. -/
noncomputable def AbsorbedGermFanB2ObstructionMassStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  let packing := canonicalWindowPacking data object
  exact AbsorbedGermFanDirectCycleFreeStatement data object ∧
    ∃ (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object)
        (centre : object.Vertex),
      AbsorbedGermFanEnvelopeWitness data object germ centre ∧
        Nonempty (Graph.TypeBRefinedSupport.OverlapObstruction object
          data.threshold data.dischargeScale packing germ.support {centre}) ∧
        ∀ envelope : Finset object.Vertex,
          Graph.TypeBEnvelopeCharge.envelopeNegativePart object data.threshold
              data.dischargeScale envelope centre ≤
            data.bridgeMassFactor * data.dischargeScale *
              (object.degree centre - data.threshold)

/-- Node `[75]`/`[84]` on the indexed `[177]` certificate-residual lane. -/
noncomputable def AbsorbedGermFanCertificateResidualMassStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  exact AbsorbedGermDecoratedAssignedSupportStatement data object ∧
    ∃ (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object)
        (centre : object.Vertex),
      AbsorbedGermFanEnvelopeWitness data object germ centre ∧
        IsEmpty (Graph.FanCertificateLabelling object data.windowOrder centre) ∧
        ∀ envelope : Finset object.Vertex,
          Graph.TypeBEnvelopeCharge.envelopeNegativePart object data.threshold
              data.dischargeScale envelope centre ≤
            data.bridgeMassFactor * data.dischargeScale *
              (object.degree centre - data.threshold)

/-- Node `[75]`/`[84]`, certificate-residual mass, on either Type B carrier. -/
noncomputable def TypeBFanCertificateResidualMassStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBFanSupportWith data object (fun _packing _piece centres =>
      ∃ centre ∈ centres,
        Graph.IsHighCentre object data.threshold centre ∧
          IsEmpty (Graph.FanCertificateLabelling object data.windowOrder centre) ∧
          ∀ envelope : Finset object.Vertex,
            Graph.TypeBEnvelopeCharge.envelopeNegativePart object data.threshold
                data.dischargeScale envelope centre ≤
              data.bridgeMassFactor * data.dischargeScale *
                (object.degree centre - data.threshold)) ∨
    AbsorbedGermFanCertificateResidualMassStatement data object ∨
    (∃ packing : Finset (Finset object.Vertex),
      object.IsWindowPacking data.windowOrder packing ∧
        packing.card = object.windowPackingNumber data.windowOrder ∧
        ∃ core : Finset object.Vertex,
          ∃ handoff : Graph.DecoratedHandoff.Envelope object data.LengthOK
              (handoffHighDegree data object)
              (handoffAbsorbing data object packing),
            handoff.core = core ∧ handoff.decorations.Nonempty ∧
              ∃ centre ∈ handoff.decorations,
                Graph.IsHighCentre object data.threshold centre ∧
                  IsEmpty (Graph.FanCertificateLabelling object
                    data.windowOrder centre) ∧
                  ∀ envelope : Finset object.Vertex,
                    Graph.TypeBEnvelopeCharge.envelopeNegativePart object
                        data.threshold data.dischargeScale envelope centre ≤
                      data.bridgeMassFactor * data.dischargeScale *
                        (object.degree centre - data.threshold))

/-- The assigned centres of either manuscript form are high centres, and they
include every high centre of the counted core (`def:typeB-assigned-ledger`):
for the ordinary support they are exactly the core's high centres; for a
decorated handoff envelope the core has `σ = 0`, hence no high centre, and the
decorations are high by `def:decorated-fan-envelope`. -/
theorem TypeBAssignedCentres.high (data : Parameters) (object : Graph.FiniteObject.{u})
    {packing : Finset (Finset object.Vertex)} {piece centres : Finset object.Vertex}
    (assigned : TypeBAssignedCentres data object packing piece centres) :
    ∀ centre ∈ centres, Graph.IsHighCentre object data.threshold centre := by
  intro centre member
  rcases assigned with ⟨_, _, rfl⟩ | ⟨_, _, envelope, _, rfl, _, _⟩
  · exact (Graph.TypeBRefinedSupport.mem_centres.mp member).2
  · exact envelope.decorations_high centre member

theorem TypeBAssignedCentres.centres_subset (data : Parameters)
    (object : Graph.FiniteObject.{u})
    {packing : Finset (Finset object.Vertex)} {piece centres : Finset object.Vertex}
    (assigned : TypeBAssignedCentres data object packing piece centres) :
    Graph.TypeBRefinedSupport.centres object data.threshold piece ⊆ centres := by
  rcases assigned with ⟨_, _, rfl⟩ | ⟨_, zero, _⟩
  · exact Finset.Subset.refl _
  · intro centre member
    exfalso
    obtain ⟨inPiece, high⟩ := Graph.TypeBRefinedSupport.mem_centres.mp member
    have : object.degree centre - data.threshold = 0 := by
      unfold Graph.FiniteObject.ambientSurplus at zero
      exact Finset.sum_eq_zero_iff.mp zero centre inPiece
    exact absurd high (by
      show ¬ data.threshold < object.degree centre
      omega)

/-- **The assigned Type B support as the B2 ledger reads it**: a canonical piece
of the remainder of a maximal packing (`CanonicalPiece`, whose vertex set is
the counted core `Y_X`) with assigned centres `H_X` in either manuscript form,
and a clause `P` about the packing, the piece and the centres. -/
def TypeBAssignedLedgerWith (data : Parameters) (object : Graph.FiniteObject.{u})
    (P : (packing : Finset (Finset object.Vertex)) →
      Graph.TypeBRefinedSupport.CanonicalPiece object packing →
      Finset object.Vertex → Prop) : Prop :=
  ∃ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing ∧
      (∀ window : Finset object.Vertex,
        object.InducesWindow data.windowOrder window →
        ∃ member ∈ packing, ¬ Disjoint window member) ∧
      ∃ canonicalPiece : Graph.TypeBRefinedSupport.CanonicalPiece object packing,
        ∃ centres : Finset object.Vertex,
          TypeBAssignedCentres data object packing canonicalPiece.vertices centres ∧
            P packing canonicalPiece centres

/-- Node `[72]`/`[81]`, B2 yes arm, on every paper-prescribed Type B input.
The same-token form retains `[144]`'s literal maximal packing, core, marked
envelope, and direct-cycle-free readings.  Its B2 support is the manuscript's
assigned support `X = (Y_X, H_X)`, namely `Y_X = core` and
`H_X = envelope.decorations`; no canonical remainder component is substituted. -/
noncomputable def TypeBB2ChoiceStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBAssignedLedgerWith data object (fun packing canonicalPiece centres =>
    Graph.TypeBRefinedSupport.HasDisjointChoice object data.threshold
      data.dischargeScale packing canonicalPiece.vertices centres centres) ∨
  AbsorbedGermFanB2ChoiceStatement data object ∨
  ∃ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing ∧
      packing.card = object.windowPackingNumber data.windowOrder ∧
      ∃ core : Finset object.Vertex,
        ∃ envelope : Graph.DecoratedHandoff.Envelope object data.LengthOK
            (handoffHighDegree data object)
            (handoffAbsorbing data object packing),
          envelope.core = core ∧ envelope.decorations.Nonempty ∧
            (∀ centre ∈ envelope.decorations,
              ∃ _marking : Graph.FanCertificateLabelling object
                  data.windowOrder centre,
                object.degree centre ≤
                  Graph.WindowCurvature.fanPackingCap data.windowOrder) ∧
            (∀ centre ∈ envelope.decorations,
              Graph.IsHighCentre object data.threshold centre →
                Graph.TypeBDirectCycle.DirectCycleFree object
                  data.windowOrder data.LengthOK packing centre) ∧
            Graph.TypeBRefinedSupport.HasDisjointChoice object data.threshold
              data.dischargeScale packing core envelope.decorations
                envelope.decorations

/-- Node `[72]`/`[81]`, B2 no arm, on every paper-prescribed Type B input.
The same-token form publishes the paper's minimal failed demand subfamily on
the exact assigned support `(core, envelope.decorations)` while retaining every
incoming `[144]` fact. -/
noncomputable def TypeBB2ObstructionStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBAssignedLedgerWith data object (fun packing canonicalPiece centres =>
    Nonempty (Graph.TypeBRefinedSupport.OverlapObstruction object
      data.threshold data.dischargeScale packing canonicalPiece.vertices
      centres)) ∨
  AbsorbedGermFanB2ObstructionStatement data object ∨
  ∃ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing ∧
      packing.card = object.windowPackingNumber data.windowOrder ∧
      ∃ core : Finset object.Vertex,
        ∃ envelope : Graph.DecoratedHandoff.Envelope object data.LengthOK
            (handoffHighDegree data object)
            (handoffAbsorbing data object packing),
          envelope.core = core ∧ envelope.decorations.Nonempty ∧
            (∀ centre ∈ envelope.decorations,
              ∃ _marking : Graph.FanCertificateLabelling object
                  data.windowOrder centre,
                object.degree centre ≤
                  Graph.WindowCurvature.fanPackingCap data.windowOrder) ∧
            (∀ centre ∈ envelope.decorations,
              Graph.IsHighCentre object data.threshold centre →
                Graph.TypeBDirectCycle.DirectCycleFree object
                  data.windowOrder data.LengthOK packing centre) ∧
            Nonempty (Graph.TypeBRefinedSupport.OverlapObstruction object
              data.threshold data.dischargeScale packing core
                envelope.decorations)

/-- `prop:typeB-global-local-bridge` on the literal B2-obstruction carrier.
The canonical arm enriches its actual obstruction with the complete five-clause
reflection.  The two auxiliary handoff arms are retained verbatim: neither is
silently converted into a canonical remainder component. -/
noncomputable def TypeBGlobalLocalBridgeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  TypeBAssignedLedgerWith data object (fun packing canonicalPiece centres =>
    ∃ obstruction : Graph.TypeBRefinedSupport.OverlapObstruction object
        data.threshold data.dischargeScale packing canonicalPiece.vertices centres,
      Graph.TypeBRefinedSupport.GlobalLocalReflectionACE data.typeABPresentation
        object data.windowOrder data.LengthOK data.threshold data.dischargeScale
        canonicalPiece centres obstruction) ∨
  AbsorbedGermFanB2ObstructionStatement data object ∨
  (∃ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing ∧
      packing.card = object.windowPackingNumber data.windowOrder ∧
      ∃ core : Finset object.Vertex,
        ∃ envelope : Graph.DecoratedHandoff.Envelope object data.LengthOK
            (handoffHighDegree data object)
            (handoffAbsorbing data object packing),
          envelope.core = core ∧ envelope.decorations.Nonempty ∧
            (∀ centre ∈ envelope.decorations,
              ∃ _marking : Graph.FanCertificateLabelling object
                  data.windowOrder centre,
                object.degree centre ≤
                  Graph.WindowCurvature.fanPackingCap data.windowOrder) ∧
            (∀ centre ∈ envelope.decorations,
              Graph.IsHighCentre object data.threshold centre →
                Graph.TypeBDirectCycle.DirectCycleFree object
                  data.windowOrder data.LengthOK packing centre) ∧
            Nonempty (Graph.TypeBRefinedSupport.OverlapObstruction object
              data.threshold data.dischargeScale packing core
                envelope.decorations))

/-- **The envelope produced is admissible Type B fan-envelope data**
(`lem:decorated-fan-admissibility`).  This is the handoff interface, and by
`rem:typeA-typeB-stratification` it uses no conclusion of
`lem:typeB-exclusion`. -/
def HandoffAdmissible (data : Parameters) (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex))
    (piece : Finset object.Vertex) : Prop :=
  ∃ envelope : Graph.DecoratedHandoff.Envelope object data.LengthOK
      (handoffHighDegree data object) (handoffAbsorbing data object packing),
    envelope.core = piece ∧ envelope.decorations.Nonempty ∧
      Graph.DecoratedHandoff.Admissible object data.LengthOK
        (handoffUncompressible data object) (handoffWindowFree data object)
        envelope

/-- `def:decorated-fan-envelope`, the selected-handoff instance of
`def:typeB-assigned-ledger`, and `lem:decorated-fan-admissibility`: the complete
envelope, its high-degree centre set, each centre's nonempty assigned
first-neighbour support, and the admissibility data consumed by the Type B
calculation.  The paper's separate multi-core grouped-envelope support is
formed later from the actual post-ledger component family. -/
def DecoratedTypeBAssignedSupport (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex))
    (piece : Finset object.Vertex) : Prop :=
  ∃ envelope : Graph.DecoratedHandoff.Envelope object data.LengthOK
      (handoffHighDegree data object) (handoffAbsorbing data object packing),
    envelope.core = piece ∧ envelope.decorations.Nonempty ∧
      (∀ centre ∈ envelope.decorations,
        Graph.IsHighCentre object data.threshold centre) ∧
      (∀ centre ∈ envelope.decorations,
        (envelope.assigned centre).Nonempty ∧
          ∀ first ∈ envelope.assigned centre,
            object.graph.Adj centre first) ∧
      Graph.DecoratedHandoff.Admissible object data.LengthOK
        (handoffUncompressible data object) (handoffWindowFree data object)
        envelope

open scoped Classical in
/-- **`prop:typeB-bridge-sublinear`'s hypotheses on this branch**, in the
`[113]`-tested form: (i) every negative positive-surplus canonical piece
carries the flat off-centre routing/unsaturation pair
(`lem:typeB-postledger-core-hygiene`'s region, `lem:typeA-receiver-loads` /
`lem:typeA-unsaturated-discharge` read off the centres), and (ii) the
negative zero-surplus handoff pieces carry the grouped decorated-envelope
fan-assignment data of `def:typeB-assigned-ledger`: a high-degree centre
family, per-piece absorbed cores with the off-absorbed pair, and the absorbed
cardinalities covered by the centres' cubic-closed counts
(`lem:decorated-envelope-deficit-bound`'s hypotheses).  The census `[123]`
cases on this statement exactly as `[113]` cases on its deficit reading. -/
def TypeBSublinearHypotheses (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop := by
  classical
  exact ∀ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing →
    (∀ window : Finset object.Vertex,
      object.InducesWindow data.windowOrder window →
      ∃ member ∈ packing, ¬ Disjoint window member) →
    (∀ component ∈ object.canonicalPieces (object.remainderSupport packing),
      let piece := object.pieceSupport (object.remainderSupport packing)
        component
      object.NegativeNetCharge piece data.threshold data.dischargeScale →
      0 < object.ambientSurplus piece data.threshold →
      Graph.TypeBEnvelopeCharge.BridgeResidualComponentAt object piece
        data.threshold data.dischargeScale) ∧
    ∃ handoffPieces : Finset (Graph.SupportComponents.Connected.Component
        object (object.remainderSupport packing)),
      (∀ component,
        component ∈ handoffPieces ↔
          component ∈ object.canonicalPieces (object.remainderSupport packing) ∧
            (let piece := object.pieceSupport (object.remainderSupport packing)
              component
            object.NegativeNetCharge piece data.threshold data.dischargeScale ∧
              object.ambientSurplus piece data.threshold = 0 ∧
              HandoffProduced data object packing piece)) ∧
      ∃ centres : Finset object.Vertex,
        (∀ centre ∈ centres, data.threshold < object.degree centre) ∧
        ∃ fanEnvelope : object.Vertex → Finset object.Vertex,
        ∃ absorbedAt : Finset object.Vertex → Finset object.Vertex,
          (∀ component ∈ handoffPieces,
            let piece := object.pieceSupport (object.remainderSupport packing)
              component
            absorbedAt piece ⊆ piece ∧
              (∀ vertex ∈ piece \ absorbedAt piece,
                object.internalDegree piece vertex ≤ data.threshold) ∧
              (∀ vertex ∈ piece \ absorbedAt piece,
                object.internalDegree piece vertex = data.threshold →
                ∃ receiver : object.Vertex,
                  object.traceReceiver? piece data.threshold vertex =
                      some receiver ∧
                    object.IsReceiver piece data.threshold receiver ∧
                      receiver ∉ absorbedAt piece) ∧
              ∀ receiver ∈ object.receivers piece data.threshold \
                  absorbedAt piece,
                1 + object.restrictedLoad piece (absorbedAt piece)
                    data.threshold receiver ≤
                  data.dischargeScale *
                    object.missingPorts piece data.threshold receiver) ∧
          ∑ component ∈ handoffPieces,
              (absorbedAt (object.pieceSupport
                (object.remainderSupport packing) component)).card ≤
            ∑ centre ∈ centres,
              Graph.TypeBFanIncidence.closedCount object data.threshold
                (fanEnvelope centre) centre

/-! ## Key statements

The statement each vocabulary key of this family publishes, stated over the
registered parameters and the selected object. -/

/-- Node `[65]` at the `[64]` entry: the ordinary Type B assigned support.
`def:canonical-decomp` assigns every surplus unit `d_G(h) − 3` of a high
centre `h ∈ V_{≥4}(G) ∩ V(R)` to the piece containing `h`, so the Type B
support's assigned fan centres are its own high centres, and `σ(X) > 0` says
it has one; the fan of a centre is `N_G(h)`. -/
noncomputable abbrev TypeBAssignedSupportStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[65]` at the `[64]` entry: the assigned fan centres of the
  -- ordinary Type B support are its high centres, and there is one.
  TypeBSupportWith data object (fun _packing piece =>
    ∃ centre ∈ piece, Graph.IsHighCentre object data.threshold centre)

/-- `prop:typeB-bridge-reduction` with `lem:typeB-bridge-to-overlap`
(`def:typeB-bridge-statements`), in the contrapositive the branch carries:
every negative positive-surplus canonical piece of a maximal packing's
remainder carries the B2 disjoint ledger with strictly negative remaining
scaled core charge — every remaining component the post-ledger Type A
hygiene carrier of `lem:typeB-postledger-core-hygiene`, with the B2(d)
grouped decorated envelope coverage — or a minimal Type B overlap
obstruction among the piece's own high centres. -/
noncomputable abbrev TypeBBridgeReductionStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- `prop:typeB-bridge-reduction` with `lem:typeB-bridge-to-overlap`
  -- (`def:typeB-bridge-statements`), in the contrapositive the branch
  -- carries at every negative positive-surplus canonical piece: the exact
  -- B2 refinement with a nonnegative remaining core would give `N₀ ≥ 0`,
  -- so a negative piece carries the B2 disjoint ledger with strictly
  -- negative remaining scaled core charge — every remaining component the
  -- post-ledger Type A hygiene carrier of
  -- `lem:typeB-postledger-core-hygiene`, with the B2(d) grouped decorated
  -- envelope coverage — or a minimal Type B overlap obstruction among the
  -- piece's own high centres (`lem:typeB-bridge-to-overlap`).
  (∀ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing →
    (∀ window : Finset object.Vertex,
      object.InducesWindow data.windowOrder window →
      ∃ member ∈ packing, ¬ Disjoint window member) →
    ∀ canonicalPiece : Graph.TypeBRefinedSupport.CanonicalPiece object
        packing,
      object.NegativeNetCharge canonicalPiece.vertices data.threshold
        data.dischargeScale →
      0 < object.ambientSurplus canonicalPiece.vertices data.threshold →
      (∃ ledger : Graph.TypeBRefinedSupport.DisjointLedger object
          data.threshold data.dischargeScale packing
            canonicalPiece.vertices
            (Graph.TypeBRefinedSupport.centres object data.threshold
              canonicalPiece.vertices),
        ledger.ExactAugmentedLedgerRefinement ∧
          (¬ (0 : Int) ≤ ∑ vertex ∈ ledger.remainingCore,
            Graph.TypeBRefinedSupport.scaledCoreCharge object
              data.threshold data.dischargeScale canonicalPiece.vertices
              vertex) ∧
          (∀ component : Graph.SupportComponents.Connected.Component
                object ledger.remainingCore,
              component ∈ Graph.SupportComponents.Connected.order object
                  ledger.remainingCore →
                Graph.TypeBPostLedgerCore.PostLedgerComponent
                  data.typeABPresentation ledger component) ∧
          ∀ components :
              Finset (Graph.TypeBMaximalCompletion.RemainingComponent
                ledger),
            (∀ component ∈ components,
              component ∈ Graph.SupportComponents.Connected.order object
                ledger.remainingCore) →
              ∀ production : ∀ component :
                  Graph.TypeBMaximalCompletion.SelectedComponent ledger
                    components,
                Graph.TypeBMaximalCompletion.ComponentExitSeven ledger
                  component.1 data.LengthOK (handoffHighDegree data object)
                  (handoffAbsorbing data object packing),
                ∃ grouped :
                  Graph.DecoratedHandoff.GroupedEnvelopes object
                    data.LengthOK (handoffUncompressible data object)
                    (handoffWindowFree data object)
                    (handoffHighDegree data object)
                    (handoffAbsorbing data object packing)
                    (Graph.TypeBMaximalCompletion.SelectedComponent
                      ledger components),
                  (∀ component :
                      Graph.TypeBMaximalCompletion.SelectedComponent
                        ledger components,
                    (grouped.envelope component).core =
                      Graph.SupportComponents.Connected.vertices object
                        ledger.remainingCore component.1) ∧
                    ∀ centre : object.Vertex,
                      centre ∈ grouped.centres ↔
                        ∃ component :
                          Graph.TypeBMaximalCompletion.SelectedComponent
                            ledger components,
                          centre =
                            (production component).separation.separator) ∨
        Nonempty (Graph.TypeBRefinedSupport.OverlapObstruction object
          data.threshold data.dischargeScale packing
            canonicalPiece.vertices
            (Graph.TypeBRefinedSupport.centres object data.threshold
              canonicalPiece.vertices)))

/-- The exact negation of the sublinear hypotheses, retained as the tested
residual state (the manuscript's Part IX bridge-residual continuation). -/
noncomputable abbrev TypeBSublinearResidualStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ¬ TypeBSublinearHypotheses data object

/-- Node `[65]` on the decorated lane: the exact exit-`(7)` envelope, its
Type-B centres and assigned first-neighbour supports, and every clause of
`lem:decorated-fan-admissibility`, all published on the same residual for the
common Type B continuation. -/
noncomputable abbrev TypeBDecoratedAssignedSupportStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  SelectedNoExitSixWith data object
    (fun packing piece =>
      DecoratedTypeBAssignedSupport data object packing piece)

/-- Node `[67]`, the standing law: every high centre of the object has its
neighbourhood in the normal form of `lem:heavy-neighbourhood-normal-form` --
cubic neighbours, a matching inside `N_G(h)`, and no common neighbour outside
`{h}` for a nonadjacent pair.  Both arms of the degree split run on it. -/
noncomputable abbrev HighCentreNormalFormStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[67]`: `lem:heavy-neighbourhood-normal-form`, at every high
  -- centre of the object at once.  It is not about one support, so it is
  -- stated of the object and both arms of the split read it.
  (∀ centre : object.Vertex,
    Graph.IsHighCentre object data.threshold centre →
    Graph.NormalForm object data.threshold centre)

/-- The B2-success arm: the selected canonical piece carries the one disjoint
candidate ledger, its exact augmented-ledger refinement, the inherited Type A
hygiene of every remaining component, and the grouped exit-`(7)` handoff
coverage used by B2(d). -/
noncomputable abbrev TypeBDisjointLedgerStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  (TypeBAssignedLedgerWith data object (fun packing canonicalPiece centres =>
          ∃ ledger : Graph.TypeBRefinedSupport.DisjointLedger object
              data.threshold data.dischargeScale packing
                canonicalPiece.vertices centres,
            ledger.ExactAugmentedLedgerRefinement ∧
              (∀ component : Graph.SupportComponents.Connected.Component
                    object ledger.remainingCore,
                  component ∈ Graph.SupportComponents.Connected.order object
                      ledger.remainingCore →
                    Graph.TypeBPostLedgerCore.PostLedgerComponent
                      data.typeABPresentation ledger component) ∧
              ∀ components :
                  Finset (Graph.TypeBMaximalCompletion.RemainingComponent
                    ledger),
                (∀ component ∈ components,
                  component ∈ Graph.SupportComponents.Connected.order object
                    ledger.remainingCore) →
                  ∀ production : ∀ component :
                      Graph.TypeBMaximalCompletion.SelectedComponent ledger
                        components,
                    Graph.TypeBMaximalCompletion.ComponentExitSeven ledger
                      component.1 data.LengthOK (handoffHighDegree data object)
                      (handoffAbsorbing data object packing),
                    ∃ grouped :
                      Graph.DecoratedHandoff.GroupedEnvelopes object
                        data.LengthOK (handoffUncompressible data object)
                        (handoffWindowFree data object)
                        (handoffHighDegree data object)
                        (handoffAbsorbing data object packing)
                        (Graph.TypeBMaximalCompletion.SelectedComponent
                          ledger components),
                      (∀ component :
                          Graph.TypeBMaximalCompletion.SelectedComponent
                            ledger components,
                        (grouped.envelope component).core =
                          Graph.SupportComponents.Connected.vertices object
                            ledger.remainingCore component.1) ∧
                        ∀ centre : object.Vertex,
                          centre ∈ grouped.centres ↔
                            ∃ component :
                              Graph.TypeBMaximalCompletion.SelectedComponent
                                ledger components,
                              centre =
                                (production component).separation.separator)) ∨
    AbsorbedGermFanB2PaidStatement data object ∨
    (∃ packing : Finset (Finset object.Vertex),
      object.IsWindowPacking data.windowOrder packing ∧
        packing.card = object.windowPackingNumber data.windowOrder ∧
        ∃ core : Finset object.Vertex,
          ∃ envelope : Graph.DecoratedHandoff.Envelope object data.LengthOK
              (handoffHighDegree data object)
              (handoffAbsorbing data object packing),
            envelope.core = core ∧ envelope.decorations.Nonempty ∧
              (∀ centre ∈ envelope.decorations,
                ∃ _marking : Graph.FanCertificateLabelling object
                    data.windowOrder centre,
                  object.degree centre ≤
                    Graph.WindowCurvature.fanPackingCap data.windowOrder) ∧
              (∀ centre ∈ envelope.decorations,
                Graph.IsHighCentre object data.threshold centre →
                  Graph.TypeBDirectCycle.DirectCycleFree object
                    data.windowOrder data.LengthOK packing centre) ∧
              ∃ choice : Graph.TypeBRefinedSupport.DisjointChoice object
                  data.threshold data.dischargeScale packing core
                    envelope.decorations envelope.decorations,
                ∀ centre (member : centre ∈ envelope.decorations),
                  (choice.entry centre member).EntryRefines data.threshold
                    data.dischargeScale core centre)

/-- Nodes `[83]`/`[84]`: the fan-mass bound instantiated at the selected
minimal overlap obstruction. -/
noncomputable abbrev TypeBOverlapObstructionMassStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  (TypeBAssignedLedgerWith data object (fun packing canonicalPiece centres =>
          Nonempty (Graph.TypeBRefinedSupport.OverlapObstruction object
            data.threshold data.dischargeScale packing
              canonicalPiece.vertices centres) ∧
          ∀ centre ∈ centres,
            ∀ envelope : Finset object.Vertex,
              Graph.TypeBEnvelopeCharge.envelopeNegativePart object
                  data.threshold data.dischargeScale envelope centre ≤
                data.bridgeMassFactor * data.dischargeScale *
                  (object.degree centre - data.threshold))) ∨
    AbsorbedGermFanB2ObstructionMassStatement data object ∨
    (∃ packing : Finset (Finset object.Vertex),
      object.IsWindowPacking data.windowOrder packing ∧
        packing.card = object.windowPackingNumber data.windowOrder ∧
        ∃ core : Finset object.Vertex,
          ∃ envelope : Graph.DecoratedHandoff.Envelope object data.LengthOK
              (handoffHighDegree data object)
              (handoffAbsorbing data object packing),
            envelope.core = core ∧ envelope.decorations.Nonempty ∧
              (∀ centre ∈ envelope.decorations,
                ∃ _marking : Graph.FanCertificateLabelling object
                    data.windowOrder centre,
                  object.degree centre ≤
                    Graph.WindowCurvature.fanPackingCap data.windowOrder) ∧
              (∀ centre ∈ envelope.decorations,
                Graph.IsHighCentre object data.threshold centre →
                  Graph.TypeBDirectCycle.DirectCycleFree object
                    data.windowOrder data.LengthOK packing centre) ∧
              Nonempty (Graph.TypeBRefinedSupport.OverlapObstruction object
                data.threshold data.dischargeScale packing core
                  envelope.decorations) ∧
              ∀ centre ∈ envelope.decorations,
                ∀ localEnvelope : Finset object.Vertex,
                  Graph.TypeBEnvelopeCharge.envelopeNegativePart object
                      data.threshold data.dischargeScale localEnvelope centre ≤
                    data.bridgeMassFactor * data.dischargeScale *
                      (object.degree centre - data.threshold))

/-- Nodes `[76]`/`[85]`: the fan-mass bound instantiated at the selected
failure of the disjoint B2 ledger. -/
noncomputable abbrev TypeBExclusionResidualMassStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  TypeBAssignedLedgerWith data object (fun packing canonicalPiece centres =>
      ∃ ledger : Graph.TypeBRefinedSupport.DisjointLedger object
          data.threshold data.dischargeScale packing
            canonicalPiece.vertices centres,
        ledger.ExactAugmentedLedgerRefinement ∧
          (¬ (0 : Int) ≤ ∑ vertex ∈ ledger.remainingCore,
            Graph.TypeBRefinedSupport.scaledCoreCharge object
              data.threshold data.dischargeScale canonicalPiece.vertices
              vertex) ∧
          ∀ centre ∈ centres,
            ∀ envelope : Finset object.Vertex,
              Graph.TypeBEnvelopeCharge.envelopeNegativePart object
              data.threshold data.dischargeScale envelope centre ≤
                data.bridgeMassFactor * data.dischargeScale *
                  (object.degree centre - data.threshold))

/-- Nodes `[73]`/`[75]` and `[83]`/`[84]`: the Type B residual fan-mass facts
for certificate residuals, overlap obstructions, and grouped decorated
envelope residuals. -/
noncomputable abbrev TypeBBridgeMassStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ((∀ packing : Finset (Finset object.Vertex),
    object.IsWindowPacking data.windowOrder packing →
    ∀ piece : Finset object.Vertex,
      piece ⊆ object.remainderSupport packing →
      Graph.SupportComponents.Connected.ConnectedOn object piece →
      object.NegativeNetCharge piece data.threshold data.dischargeScale →
      0 < object.ambientSurplus piece data.threshold →
      (∀ centre ∈ piece, Graph.IsHighCentre object data.threshold centre →
        ∀ envelope : Finset object.Vertex,
          Graph.TypeBEnvelopeCharge.envelopeNegativePart object data.threshold
              data.dischargeScale envelope centre ≤
            data.bridgeMassFactor * data.dischargeScale *
              (object.degree centre - data.threshold)) ∧
        (Graph.TypeBEnvelopeCharge.BridgeResidualComponentAt object piece
            data.threshold data.dischargeScale →
          piece.card + data.dischargeScale *
                object.ambientSurplus piece data.threshold ≤
            data.dischargeScale * object.positiveDeficiency piece data.threshold +
              data.bridgeMassFactor * data.dischargeScale *
                object.ambientSurplus piece data.threshold)) ∧
    (∀ packing : Finset (Finset object.Vertex),
      object.IsWindowPacking data.windowOrder packing →
      ∀ route8 : Finset (Graph.SupportComponents.Connected.Component object
          (object.remainderSupport packing)),
        (∀ piece ∈ route8,
          object.ambientSurplus (object.pieceSupport
            (object.remainderSupport packing) piece) data.threshold = 0) →
        (∀ piece ∈ object.canonicalPieces (object.remainderSupport packing),
          piece ∉ route8 →
          Graph.TypeBEnvelopeCharge.BridgeResidualComponentAt object
            (object.pieceSupport (object.remainderSupport packing) piece)
            data.threshold data.dischargeScale) →
        ∑ piece ∈ object.canonicalPieces (object.remainderSupport packing),
            ((object.pieceSupport (object.remainderSupport packing) piece).card +
                data.dischargeScale * object.ambientSurplus
                  (object.pieceSupport (object.remainderSupport packing) piece)
                  data.threshold -
              data.dischargeScale * object.positiveDeficiency
                (object.pieceSupport (object.remainderSupport packing) piece)
                data.threshold) ≤
          Graph.TypeBEnvelopeCharge.route8Deficit object
              (object.remainderSupport packing) data.threshold
              data.dischargeScale route8 +
            data.bridgeMassFactor * data.dischargeScale *
              object.degreeSurplus data.threshold) ∧
    ∀ packing : Finset (Finset object.Vertex),
      object.IsWindowPacking data.windowOrder packing →
      ∀ ordinary grouped : Finset object.Vertex,
        ordinary ⊆ object.remainderSupport packing →
        grouped ⊆ object.remainderSupport packing →
        ∀ ordinaryRoute8 : Finset
            (Graph.SupportComponents.Connected.Component object ordinary),
        ∀ groupedRoute8 : Finset
            (Graph.SupportComponents.Connected.Component object grouped),
          (∀ piece ∈ ordinaryRoute8,
            object.ambientSurplus (object.pieceSupport ordinary piece)
              data.threshold = 0) →
          (∀ piece ∈ groupedRoute8,
            object.ambientSurplus (object.pieceSupport grouped piece)
              data.threshold = 0) →
          (∀ piece ∈ object.canonicalPieces ordinary, piece ∉ ordinaryRoute8 →
            Graph.TypeBEnvelopeCharge.BridgeResidualComponentAt object
              (object.pieceSupport ordinary piece) data.threshold
              data.dischargeScale) →
          (∀ piece ∈ object.canonicalPieces grouped, piece ∉ groupedRoute8 →
            Graph.TypeBEnvelopeCharge.BridgeResidualComponentAt object
              (object.pieceSupport grouped piece) data.threshold
              data.dischargeScale) →
          ∑ piece ∈ object.canonicalPieces ordinary,
              ((object.pieceSupport ordinary piece).card +
                  data.dischargeScale * object.ambientSurplus
                    (object.pieceSupport ordinary piece) data.threshold -
                data.dischargeScale * object.positiveDeficiency
                  (object.pieceSupport ordinary piece) data.threshold) +
            ∑ piece ∈ object.canonicalPieces grouped,
              ((object.pieceSupport grouped piece).card +
                  data.dischargeScale * object.ambientSurplus
                    (object.pieceSupport grouped piece) data.threshold -
                data.dischargeScale * object.positiveDeficiency
                  (object.pieceSupport grouped piece) data.threshold) ≤
              Graph.TypeBEnvelopeCharge.route8Deficit object ordinary
                data.threshold data.dischargeScale ordinaryRoute8 +
              Graph.TypeBEnvelopeCharge.route8Deficit object grouped
                data.threshold data.dischargeScale groupedRoute8 +
                2 * (data.bridgeMassFactor * data.dischargeScale *
                  object.degreeSurplus data.threshold))

/-- `prop:typeB-bridge-sublinear`: after route-`8` non-window cores have been
extracted into the Type A ledger, the remaining Type B bridge residual mass is
paid by the assigned high-centre surplus. -/
noncomputable abbrev TypeBBridgeSublinearStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- `prop:typeB-bridge-sublinear` in exact finite form.  `ordinary` is the
  -- canonical assigned-support role and `grouped` is the decorated-envelope
  -- role from `def:typeB-residual-mass`.  Empty route-8 subcollections are
  -- the proposition's hypothesis that the non-window cores contain no
  -- admissible route-8 profile.  The factor `2` is precisely the paper's
  -- at-most-twice convention: a high-centre surplus unit occurs at most once
  -- in each of the two roles.
  ((∀ packing : Finset (Finset object.Vertex),
      object.IsWindowPacking data.windowOrder packing →
      ∀ ordinary grouped : Finset object.Vertex,
        ordinary ⊆ object.remainderSupport packing →
        grouped ⊆ object.remainderSupport packing →
        (∀ piece ∈ object.canonicalPieces ordinary,
          Graph.TypeBEnvelopeCharge.BridgeResidualComponentAt object
            (object.pieceSupport ordinary piece)
            data.threshold data.dischargeScale) →
        (∀ piece ∈ object.canonicalPieces grouped,
          Graph.TypeBEnvelopeCharge.BridgeResidualComponentAt object
            (object.pieceSupport grouped piece)
            data.threshold data.dischargeScale) →
        ∑ piece ∈ object.canonicalPieces ordinary,
            ((object.pieceSupport ordinary piece).card +
                data.dischargeScale * object.ambientSurplus
                  (object.pieceSupport ordinary piece)
                  data.threshold -
              data.dischargeScale * object.positiveDeficiency
                (object.pieceSupport ordinary piece) data.threshold) +
          ∑ piece ∈ object.canonicalPieces grouped,
            ((object.pieceSupport grouped piece).card +
                data.dischargeScale * object.ambientSurplus
                  (object.pieceSupport grouped piece) data.threshold -
              data.dischargeScale * object.positiveDeficiency
                (object.pieceSupport grouped piece) data.threshold) ≤
            2 * (data.bridgeMassFactor * data.dischargeScale *
              object.degreeSurplus data.threshold)) ∧
    object.degreeSurplus data.threshold ≤
      data.surplusThreshold object.vertexCount)

/-- Node `[76]`/`[85]`, closed arm: the selected Type B ledger gives
nonnegative net charge. -/
noncomputable abbrev TypeBExcludedStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Nodes `[74]`/`[82]`, the successful B2 reduction.  A canonical
  -- assigned support publishes the paper's literal `N₀(X) ≥ 0`.
  -- The indexed `[177]` lane publishes its literal paid B2 entry: that
  -- lane has no canonical negative remainder support and must not be
  -- relabelled as the B2-failure residual of `[84]`.
  (TypeBAssignedLedgerWith data object
      (fun _packing canonicalPiece _centres =>
        object.NonNegativeNetCharge canonicalPiece.vertices data.threshold
          data.dischargeScale)) ∨
    AbsorbedGermFanB2PaidStatement data object ∨
    (∃ packing : Finset (Finset object.Vertex),
      object.IsWindowPacking data.windowOrder packing ∧
        packing.card = object.windowPackingNumber data.windowOrder ∧
        ∃ core : Finset object.Vertex,
          ∃ envelope : Graph.DecoratedHandoff.Envelope object data.LengthOK
              (handoffHighDegree data object)
              (handoffAbsorbing data object packing),
            envelope.core = core ∧ envelope.decorations.Nonempty ∧
              (∀ centre ∈ envelope.decorations,
                ∃ _marking : Graph.FanCertificateLabelling object
                    data.windowOrder centre,
                  object.degree centre ≤
                    Graph.WindowCurvature.fanPackingCap data.windowOrder) ∧
              (∀ centre ∈ envelope.decorations,
                Graph.IsHighCentre object data.threshold centre →
                  Graph.TypeBDirectCycle.DirectCycleFree object
                    data.windowOrder data.LengthOK packing centre) ∧
              ∃ choice : Graph.TypeBRefinedSupport.DisjointChoice object
                  data.threshold data.dischargeScale packing core
                    envelope.decorations envelope.decorations,
                ∀ centre (member : centre ∈ envelope.decorations),
                  (choice.entry centre member).EntryRefines data.threshold
                    data.dischargeScale core centre)

/-- Node `[76]`/`[85]`, surviving arm: the Type B exclusion hypotheses are not
all discharged on the selected B2 branch. -/
noncomputable abbrev TypeBExclusionResidualStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  TypeBAssignedLedgerWith data object (fun packing canonicalPiece centres =>
          ∃ ledger : Graph.TypeBRefinedSupport.DisjointLedger object
              data.threshold data.dischargeScale packing
                canonicalPiece.vertices centres,
            ledger.ExactAugmentedLedgerRefinement ∧
              (∀ component : Graph.SupportComponents.Connected.Component
                    object ledger.remainingCore,
                  component ∈ Graph.SupportComponents.Connected.order object
                      ledger.remainingCore →
                    Graph.TypeBPostLedgerCore.PostLedgerComponent
                      data.typeABPresentation ledger component) ∧
              ¬ (0 : Int) ≤ ∑ vertex ∈ ledger.remainingCore,
                Graph.TypeBRefinedSupport.scaledCoreCharge object
                  data.threshold data.dischargeScale canonicalPiece.vertices
                  vertex)

end Hypostructure.Graph.Strategy.Spine
