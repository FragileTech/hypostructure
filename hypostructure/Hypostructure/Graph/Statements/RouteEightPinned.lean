import Hypostructure.Graph.Statements.CanonicalRouteEight
import Hypostructure.Graph.Statements.CanonicalTypeB

/-!
# Route 8: statements pinned at the canonical objects of `G`

Every statement below is the conclusion of its contract lemma instantiated at
the selected counterexample `G` and at the objects of `G` that an upstream
ledger key has already fixed (`Statements/CanonicalRouteEight.lean`):

* `P₀ = canonicalRoute8Partition` (node `[349]`, the committed demand ledger);
* `A₀ = canonicalRoute8Absorption P₀` (node `[351]`);
* `b₀ = canonicalRoute8WindowBlocker P₀ A₀` (node `[352]`);
* `ξ = canonicalRoute8TerminalEntry` (node `[334]`: `ξ†` on the `[123]` rate
  arm, `ξ*` of `P₀` on the `[181]` arm);
* `ι₂ = canonicalRoute8TwoCarrierIndex` (nodes `[117]`/`[118]`);
* `ι₁ = canonicalRoute8SmallCoreEntry` (nodes `[115]`/`[116]`).

Each pins its object in the positive form `∃ x, obj = some x ∧ Q x`: false,
never vacuous, when the object is absent; and the unique upstream witness when
it is present.  The upstream spec is recovered by the `_spec_of_eq_some`
lemmas and is not republished.

This module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

noncomputable section

section Route8Pinned

variable (data : Parameters) (object : Graph.FiniteObject.{u})

attribute [local instance] Graph.Route8.vertexDecEq
attribute [local instance 10] Classical.propDecidable

/-! ## The committed node-`[181]` ledger -/

/-- **Node `[351]`, `def:typeA-pressure-absorbers` with
`lem:typeA-pressure-absorber-no-overcount`** at the committed ledger `P₀`:
the canonical maximal same-support absorption `A₀` with empty type-(A2) set
and the display `3Ñ ≤ e(R, W) + B_dep + 𝖯_open`. -/
def Route8DemandAbsorptionStatement : Prop :=
  ∃ P, canonicalRoute8Partition data object = some P ∧
    ∃ x, canonicalRoute8Absorption data object P = some x ∧
      Route8AbsorptionSpec data object P x.1 x.2

/-- **Node `[517]`, (O2) of `lem:typeA-routed-overload-not-open`** at
`(P₀, A₀)`: no open demand unit has an unused eligible boundary incidence of
its own support. -/
def Route8OpenBoundarySaturatedStatement : Prop :=
  ∃ P, canonicalRoute8Partition data object = some P ∧
    ∃ x, canonicalRoute8Absorption data object P = some x ∧
      ∀ unit ∈ P.demandUnits \ (x.1.absorbed ∪ x.2),
        ∀ carrier : Sym2 object.Vertex,
          carrier ∈ Graph.Route8.cutEdges object unit.1.1 →
          (∀ index ∈ P.three ∪ P.two, carrier ∉ P.assigned index) →
          ∃ other ∈ x.1.absorbed, x.1.absorber other = carrier

/-- **Node `[518]`**: the demand units of `P₀` number exactly its external
demand defect, `|𝒰_press| = 𝖯_ext` (`def:typeA-pressure-absorbers`). -/
def Route8DemandUnitCountStatement : Prop :=
  ∃ P, canonicalRoute8Partition data object = some P ∧
    P.demandUnits.card = P.externalDefect

/-- **Node `[352]`, `def:typeA-open-window-blocker` with
`lem:typeA-open-window-blocker-count`** at `(P₀, A₀)`: the canonical blocker
`b₀` of every open unit and `𝖯_open = Σ_P B_open(P)`. -/
def Route8WindowBlockersStatement : Prop :=
  ∃ P, canonicalRoute8Partition data object = some P ∧
    ∃ x, canonicalRoute8Absorption data object P = some x ∧
      ∃ y, canonicalRoute8WindowBlocker data object P x.1 x.2 = some y ∧
        Route8WindowBlockerSpec data object P x.1 x.2 y.1 y.2

/-- **The recorded `P`-avoiding corridor** of `def:typeA-recorded-window-shadow-hit`
(tex 16229-16236) between the boundary endpoints `first`, `second` of two
open units on the packed window `window`, with canonical boundary incidences
`first p_a`, `second p_b`: a simple `first`-`second` path of `G - V(P)`, whose
end edges attach at `p_a`, `p_b` and are distinct.  It is ONE fixed corridor of
G (the canonical choice among these paths), not every such path. -/
def RecordedCorridorSpec {n : Nat}
    (window : SimpleGraph.pathGraph n ↪g object.graph)
    (first second : object.Vertex) (a b : Fin n)
    (corridor : object.graph.Walk first second) : Prop :=
  corridor.IsPath ∧
    (∀ i : Fin n, window i ∉ corridor.support) ∧
    object.graph.Adj (window a) first ∧
    object.graph.Adj second (window b) ∧
    s(first, window a) ≠ s(second, window b)

/-- The canonical recorded corridor (`none` when no such corridor exists). -/
def canonicalRecordedCorridor {n : Nat}
    (window : SimpleGraph.pathGraph n ↪g object.graph)
    (first second : object.Vertex) (a b : Fin n) :
    Option (object.graph.Walk first second) :=
  if h : ∃ corridor, RecordedCorridorSpec object window first second a b corridor
  then some (Classical.choose h) else none

theorem recordedCorridorSpec_of_eq_some {n : Nat}
    {window : SimpleGraph.pathGraph n ↪g object.graph}
    {first second : object.Vertex} {a b : Fin n}
    {corridor : object.graph.Walk first second}
    (pinned : canonicalRecordedCorridor object window first second a b =
      some corridor) :
    RecordedCorridorSpec object window first second a b corridor := by
  unfold canonicalRecordedCorridor at pinned
  split_ifs at pinned with h
  · cases pinned
    exact Classical.choose_spec h

/-- **`def:typeA-recorded-window-shadow-hit` with
`lem:typeA-window-shadow-hit-routes`, certificate (O1)** at the open demand
units of `(P₀, A₀)` and their canonical window blockers `b₀`: for two distinct
open units on the same packed window `P`, at any presentation of `P` as an
induced path, whose canonical boundary incidences are `x p_a` and `y p_b`, the
recorded corridor `Q` (`canonicalRecordedCorridor`) with `b ∈ Sh_{s(Q)}(a)`
closes the simple cycle `x Q y p_b P p_a x` of accepted length
`s(Q) + 2 + |a − b|`. -/
def WindowShadowHitCycleStatement : Prop :=
  ∃ P, canonicalRoute8Partition data object = some P ∧
    ∃ x, canonicalRoute8Absorption data object P = some x ∧
      ∃ y, canonicalRoute8WindowBlocker data object P x.1 x.2 = some y ∧
        ∀ υ ∈ P.demandUnits \ (x.1.absorbed ∪ x.2),
          ∀ υ' ∈ P.demandUnits \ (x.1.absorbed ∪ x.2),
            υ ≠ υ' → y.2 υ = y.2 υ' →
            ∀ window : SimpleGraph.pathGraph data.windowOrder ↪g object.graph,
              (∀ vertex, vertex ∈ y.2 υ ↔ ∃ i, window i = vertex) →
              ∀ (first second : object.Vertex) (a b : Fin data.windowOrder),
                y.1 υ = s(first, window a) → y.1 υ' = s(second, window b) →
                ∀ corridor,
                  canonicalRecordedCorridor object window first second a b =
                    some corridor →
                  b.1 ∈ Graph.WindowAttachmentShadow.shadow data.LengthOK
                    data.windowOrder corridor.length a.1 →
                  ∃ cycle : object.graph.Walk (window a) (window a),
                    cycle.IsCycle ∧
                      cycle.length = corridor.length + 2 + Nat.dist a.1 b.1 ∧
                      data.LengthOK cycle.length

/-- **`lem:typeA-window-shadow-hit-routes`** on the selected object: no two
open demand units of `(P₀, A₀)` on the same packed window have a recorded
window-signature hit along their recorded corridor. -/
def WindowShadowHitExcludedStatement : Prop :=
  ∃ P, canonicalRoute8Partition data object = some P ∧
    ∃ x, canonicalRoute8Absorption data object P = some x ∧
      ∃ y, canonicalRoute8WindowBlocker data object P x.1 x.2 = some y ∧
        ∀ υ ∈ P.demandUnits \ (x.1.absorbed ∪ x.2),
          ∀ υ' ∈ P.demandUnits \ (x.1.absorbed ∪ x.2),
            υ ≠ υ' → y.2 υ = y.2 υ' →
            ∀ window : SimpleGraph.pathGraph data.windowOrder ↪g object.graph,
              (∀ vertex, vertex ∈ y.2 υ ↔ ∃ i, window i = vertex) →
              ∀ (first second : object.Vertex) (a b : Fin data.windowOrder),
                y.1 υ = s(first, window a) → y.1 υ' = s(second, window b) →
                ∀ corridor,
                  canonicalRecordedCorridor object window first second a b =
                    some corridor →
                  b.1 ∉ Graph.WindowAttachmentShadow.shadow data.LengthOK
                    data.windowOrder corridor.length a.1

/-- **(168.1) of `thm:typeA-unpaid-exit4-reduction`** (node `[181]`) at the
committed ledger `P₀`: every unpaid entry `ξ ∈ Ξ₂(P₀) ∪ Ξ_res(P₀)` has at most
`δ − 1` (the manuscript's two) private essential incidences. -/
def Route8UnpaidTwoCarrierStatement : Prop :=
  ∃ P, canonicalRoute8Partition data object = some P ∧
    ∀ index ∈ P.two ∪ P.residual,
      Graph.Route8.IndexedTwoCarrierCore
        (route8UnifiedEntries data object) (route8DemandCore data object)
        (data.threshold - 1) index

/-- **Node `[349]`, the committed ledger, pinned**: G's lexicographically first
maximizing 2/3-demand ledger `canonicalRoute8DemandRecord` exists. -/
def Route8DemandLedgerPinnedStatement : Prop :=
  ∃ ledger, canonicalRoute8DemandRecord data object = some ledger

theorem route8DemandLedger_of_pinned
    (pinned : Route8DemandLedgerPinnedStatement data object) :
    Route8DemandLedgerStatement data object :=
  let ⟨ledger, _⟩ := pinned
  ⟨ledger⟩

/-- **Node `[181]`, yes (outcome (i))**: some unpaid entry of `P₀` has no
exit-`(4)` witness; it is pinned as G's canonical such entry `ξ*`
(`canonicalRoute8UnpaidEntry`). -/
def Route8UnpaidWitnessFreeStatement : Prop :=
  ∃ P, canonicalRoute8Partition data object = some P ∧
    ∃ index, canonicalRoute8UnpaidEntry data object P = some index ∧
      Route8UnpaidWitnessFreeSpec data object P index

/-- **Node `[181]`, no = node `[183]` (outcome (ii), (168.2))**: the exact
negation at `P₀` -- every unpaid entry of `P₀` carries its canonical
exit-`(4)` witness. -/
def Route8UnpaidExitFourResidualStatement : Prop :=
  ∃ P, canonicalRoute8Partition data object = some P ∧
    ∀ index ∈ P.two ∪ P.residual,
      ∃ witness : Graph.ExitFour.Witness
          (Graph.HasCycleWithLength data.LengthOK) index.1 data.threshold
          data.dischargeScale index.2.1 ∅,
        witness.load = index.2.2

/-! ## The terminal two-support entry `ξ` (node `[334]` → `[124]`) -/

/-- Clauses (T1)--(T5) of `def:typeA-terminal-two-carrier` at one unified
entry: it is a unified entry, two-support, carries the census facts, its basin
is target-complete-minimal, and its load has no exit-`(4)` witness. -/
def Route8TerminalTrueEntry (index : Graph.Route8Census.Index object) : Prop :=
  index ∈ route8UnifiedEntries data object ∧
    Graph.Route8.IndexedTwoCarrierCore
      (route8UnifiedEntries data object) (route8DemandCore data object)
      (data.threshold - 1) index ∧
    Route8UnifiedEntryFacts data object index ∧
    Graph.Route8.TraceBasin.TargetCompleteMinimal object index.1
      data.threshold data.LengthOK index.2.1 index.2.2
      (Graph.Route8Census.basin object data.threshold index) ∧
    ¬ ∃ witness : Graph.ExitFour.Witness
        (Graph.HasCycleWithLength data.LengthOK) index.1 data.threshold
        data.dischargeScale index.2.1 ∅,
      witness.load = index.2.2

/-- **Node `[334]`**: the terminal entry `ξ` is a true two-support route-`8`
entry. -/
def Route8UnifiedTrueTwoCarrierEntryStatement : Prop :=
  ∃ index, canonicalRoute8TerminalEntry data object = some index ∧
    Route8TerminalTrueEntry data object index

/-- **Node `[124]` on the unified collection, `lem:typeA-carrier-deletion-exit`
at `ξ`**: the terminal entry carries its canonical exit-`(4)` witness. -/
def Route8UnifiedTwoCarrierExitStatement : Prop :=
  ∃ index, canonicalRoute8TerminalEntry data object = some index ∧
    ∃ witness : Graph.ExitFour.Witness
        (Graph.HasCycleWithLength data.LengthOK) index.1 data.threshold
        data.dischargeScale index.2.1 ∅,
      witness.load = index.2.2

/-! ## The terminal two-support entry `ι₂` of `𝒳_A` (nodes `[118]`, `[124]`) -/

/-- **Node `[118]`, (T2) at `ι₂`**: the two-support entry of `𝒳_A` fixed by
node `[117]` has no exit-`(4)` witness. -/
def Route8TrueTwoCarrierEntryStatement : Prop :=
  ∃ index, canonicalRoute8TwoCarrierIndex data object = some index ∧
    ¬ ∃ witness : Graph.ExitFour.Witness
        (Graph.HasCycleWithLength data.LengthOK) index.1 data.threshold
        data.dischargeScale index.2.1 ∅,
      witness.load = index.2.2

/-- **Node `[118]`, (T5) at `ι₂`**: the declared carrier-deletion witnesses of
the canonical essential core of `ι₂`. -/
def Route8CarrierDeletionWitnesses : Prop :=
  ∃ index, canonicalRoute8TwoCarrierIndex data object = some index ∧
    let entry := (Graph.Route8Census.presented object data.threshold
      data.LengthOK index).toEntry (Graph.HasCycleWithLength data.LengthOK)
    Graph.Route8.TwoCarrierDeletionWitnesses
      (Target := Graph.HasCycleWithLength data.LengthOK) entry.carriers
      entry.coordinates entry.car entry.state
      (Graph.Route8Census.entriesOfComponents object
        (canonicalWindowPacking data object)
        (route8SurvivorComponents data object) data.threshold
        data.dischargeScale)
      (Graph.Route8Census.core object data.threshold data.LengthOK)
      (data.threshold - 1) index

/-- **Node `[124]` on `𝒳_A`, `lem:typeA-carrier-deletion-exit` at `ι₂`**:
the two-support entry carries its canonical exit-`(4)` witness. -/
def Route8SurvivorTwoCarrierExitStatement : Prop :=
  ∃ index, canonicalRoute8TwoCarrierIndex data object = some index ∧
    ∃ witness : Graph.ExitFour.Witness
        (Graph.HasCycleWithLength data.LengthOK) index.1 data.threshold
        data.dischargeScale index.2.1 ∅,
      witness.load = index.2.2

/-! ## The small-core entry `ι₁` (node `[116]`) -/

/-- **Node `[116]`, `lem:typeA-one-terminal-collapse` at `ι₁`**: the
small-core entry fixed by node `[115]` realizes, in order, one of the
trace-basin alternatives of exits `(4)`--`(7)`. -/
def Route8SmallCoreCollapse : Prop :=
  ∃ entry, canonicalRoute8SmallCoreEntry data object = some entry ∧
    let piece := object.pieceSupport
      (object.remainderSupport (canonicalWindowPacking data object)) entry.1
    let basin := Graph.Route8Census.basin object data.threshold
      (piece, entry.2.1, entry.2.2)
    Graph.Route8.TraceBasin.TraceLocalTargetDefect object piece
        data.threshold data.LengthOK entry.2.1 entry.2.2 basin ∨
      (∃ retained,
        Graph.Route8.TraceBasin.TraceResponseQuotient object piece
          data.threshold data.LengthOK entry.2.1 entry.2.2 basin retained) ∨
      Graph.Route8.TraceBasin.TraceDelocalization object piece
        data.threshold data.LengthOK entry.2.1 entry.2.2 basin ∨
      Graph.Route8.TraceBasin.TraceSurvivingSeparator object piece
        data.threshold data.LengthOK entry.2.1 entry.2.2 basin

/-! ## Node `[186]` -/

/-- The peeling set recorded for the receiver `w` of the support `X` at one
stage of the node-`[123]` descent: the loads of the chain entries at `(X, w)`. -/
def route8RecordedPeeled (stage : List (Graph.Route8Census.Index object))
    (piece : Finset object.Vertex) (receiver : object.Vertex) :
    Finset object.Vertex :=
  (stage.toFinset.filter fun index => index.1 = piece ∧ index.2.1 = receiver).image
    fun index => index.2.2

/-- **`lem:typeA-unified-joint-balance`** (node `[186]`) on the ledger fixed
at node `[181]`: the peel chain is `route8DescentChain`, the partition is
`P₀`, the absorption is `A₀`; `unused` is determined by `N = D + unused`.
With universal saturated-load visibility and the silent-terminal exclusion
(168.22) at every recorded peeling set of the descent.  The node-`[185]` fact
stays on the ledger and is not republished.  The demand weights are the
registered baseline `δ` (an entry of `Ξ₃` holds `δ` private incidences, an entry
of `Ξ₂` holds `δ − 1`), and the stub multiplier is `δ`. -/
def Route8JointBalanceStatement : Prop :=
  let packing := canonicalWindowPacking data object
  let support := object.remainderSupport packing
  let entries := route8UnifiedEntries data object
  let components := route8UnifiedComponents data object
  let supply := Graph.Route8Census.supply object packing
  let bridgeAllowance := data.bridgeMassFactor * data.dischargeScale *
    data.surplusThreshold object.vertexCount
  (∀ component ∈ components,
      let piece := object.pieceSupport support component
      ∀ receiver ∈ Graph.VisibleEntry.saturatedReceivers object piece
          data.threshold data.dischargeScale,
        object.routedLoads piece data.threshold receiver ⊆
          Graph.VisibleEntry.visibleLoads object piece data.threshold receiver) ∧
    (∀ component ∈ components,
      let piece := object.pieceSupport support component
      ∀ receiver ∈ Graph.VisibleEntry.saturatedReceivers object piece
          data.threshold data.dischargeScale,
        ∀ stage ∈ (route8DescentChain data object).inits,
          ¬ Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold
            data.dischargeScale receiver
            (route8RecordedPeeled object stage piece receiver)) ∧
    ∃ P, canonicalRoute8Partition data object = some P ∧
      ∃ x, canonicalRoute8Absorption data object P = some x ∧
        ∃ unused : Nat,
          let peeled := (route8DescentChain data object).toFinset
          let deficit := Graph.TypeBEnvelopeCharge.route8Deficit object
            support data.threshold data.dischargeScale components
          let openUnits := P.demandUnits \ x.1.absorbed
          peeled.card ≤ deficit ∧
            deficit ≤ entries.card ∧
            entries.card = deficit + unused ∧
            support.card ≤ deficit +
              data.dischargeScale * supply.card + bridgeAllowance ∧
            data.threshold * entries.card ≤ supply.card + openUnits.card ∧
            data.threshold * support.card ≤
              (data.threshold * data.dischargeScale + 1) * supply.card +
                data.threshold * bridgeAllowance + openUnits.card ∧
            data.threshold * support.card ≤
              (data.threshold * data.dischargeScale + 1) * supply.card +
                data.threshold * (2 * bridgeAllowance) +
                data.threshold * peeled.card ∧
            data.threshold * entries.card =
              (data.threshold * P.three.card +
                (data.threshold - 1) * P.two.card) + P.demandUnits.card ∧
            P.demandUnits.card = x.1.absorbed.card + openUnits.card ∧
            data.threshold * P.three.card + (data.threshold - 1) * P.two.card +
                x.1.absorbed.card ≤
              supply.card

end Route8Pinned

end

/-- `thm:branch-kill`'s all-pieces classification: every negative piece of
the canonical decomposition is silent-first when it has no ambient surplus,
and is a Type B bridge component when it has positive surplus.  This is not
node `[111]`. -/
noncomputable abbrev Route8PiecesClassifiedStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- `thm:branch-kill`'s all-pieces classification, exactly as stated: at a
  -- negative zero-surplus piece, an exit-(4) witness for a routed load,
  -- the route-8 residual profile — per saturated receiver, every unpaid
  -- silent-excess and overloaded-port visible load is a route-8 entry or
  -- realizes the exit-(5) plain response quotient (cased), the exact
  -- per-load conclusion `K .typeAExclusion`'s arm 2 delivers
  -- (`lem:typeA-reduced-silent-residual`, `rem:unified-covers-exit4`) —
  -- or a produced decorated Type B handoff; at a negative positive-surplus
  -- piece, the Type B bridge component pair.
  Graph.Route8Deficit.PieceClassification object
    (Graph.HasCycleWithLength data.LengthOK)
    (fun piece =>
      (∃ receiver : object.Vertex,
        receiver ∈ Graph.VisibleEntry.saturatedReceivers object piece
          data.threshold data.dischargeScale) ∧
      ∀ receiver ∈ Graph.VisibleEntry.saturatedReceivers object piece
          data.threshold data.dischargeScale,
        (∀ load ∈ Graph.VisibleEntry.silentExcess object piece
            data.threshold data.dischargeScale receiver,
          Graph.Route8.TraceBasin.Route8Entry object piece data.threshold
              data.LengthOK receiver load ∨
            ∃ basin : Finset object.Vertex,
              Graph.Route8.TraceBasin.select? object piece data.threshold
                  receiver load = some basin ∧
                ∃ retained,
                  Graph.Route8.TraceBasin.TraceResponseQuotient object
                    piece data.threshold data.LengthOK receiver load basin
                    retained) ∧
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
                        basin retained)
    (fun piece =>
      SeparatorHandoffAt data object piece)
    (fun piece =>
      -- `def:typeB-bridge-statements` at the piece: G's canonical B2
      -- disjoint ledger of the piece (`canonicalTypeBDisjointChoice`, the
      -- ledger `K .typeBBridgeReduction` fixed) with strictly negative
      -- remaining scaled core charge, or a minimal
      -- overlap obstruction (`K .typeBBridgeReduction`'s dichotomy; the
      -- post-ledger hygiene and grouped coverage stay on that key and are
      -- not republished here).
      (∃ ledger, canonicalTypeBDisjointChoice data object piece
          (Graph.TypeBRefinedSupport.centres object data.threshold piece) =
            some ledger ∧
        ledger.ExactAugmentedLedgerRefinement ∧
          ¬ 0 ≤ RemainingCoreCharge data object ledger) ∨
        Nonempty (Graph.TypeBRefinedSupport.OverlapObstruction object
          data.threshold data.dischargeScale
          (canonicalWindowPacking data object) piece
          (Graph.TypeBRefinedSupport.centres object data.threshold piece)))
    (canonicalWindowPacking data object) data.threshold data.dischargeScale

end Hypostructure.Graph.Strategy.Spine
