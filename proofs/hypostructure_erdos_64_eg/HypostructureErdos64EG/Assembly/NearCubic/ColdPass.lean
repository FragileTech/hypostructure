import Hypostructure.Graph.Strategy.ColdCorridorRows.Basic
import Hypostructure.Graph.Strategy.ColdCorridorRows.ColdFamilyClosure
import Hypostructure.Graph.Strategy.ColdCorridorRows.ColdMass
import Hypostructure.Graph.Strategy.ColdCorridorRows.CorridorState
import Hypostructure.Graph.Strategy.ColdCorridorRows.EntryDichotomies
import Hypostructure.Graph.Strategy.ColdCorridorRows.FailureClauses
import Hypostructure.Graph.Strategy.ColdCorridorRows.FirstFailureOccurrence
import Hypostructure.Graph.Strategy.ColdCorridorRows.FirstFailureRouting
import Hypostructure.Graph.Strategy.ColdCorridorRows.GermCandidates
import Hypostructure.Graph.Strategy.ColdCorridorRows.GermExtraction
import Hypostructure.Graph.Strategy.ColdCorridorRows.GermFamilyPositive
import Hypostructure.Graph.Strategy.ColdCorridorRows.GermTrichotomy
import Hypostructure.Graph.Strategy.ColdCorridorRows.HandoffTransfer
import Hypostructure.Graph.Strategy.ColdCorridorRows.ReturnCorridor
import Hypostructure.Graph.Strategy.EntropyClosure
import Hypostructure.Graph.Strategy.SpineRows.Bridgeless
import Hypostructure.Graph.Strategy.SpineRows.HotColdPartition
import Hypostructure.Graph.Strategy.SpineRows.LiveHotBarrierCap
import HypostructureErdos64EG.Assembly.Basic

/-!
# Assembly: NearCubic / ColdPass

The hot/cold split `[22]`--`[23]` and the cold branch `[145]`--`[154]` of Part
XI, written once.  Each composition is generic over the incoming ledger index
`known`, with `FactKeys.Has` requirements and one `List.Disjoint` covering
hypothesis for freshness; the realized package `[158]` yes-arm and the dense
hot/cold pass `[162]` run the same definitions on their literal residuals.  The
arm decisions `[146]` and `[153]` and the `[154]` G2 test are taken by the
callers, whose continuations differ.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- **Nodes `[22]`--`[23]`.**  The canonical hot/cold partition of the fixed
packing (`def:cold-window-ledger`) and the live-hot entropy cap test `[22]`.
The overflow arm `[23]` closes: `liveHotBarrierCapRow` reads the retained hot
package, the package-rate inequality and the skeleton state-count bound and
publishes the opposite cap, and Core closes the pair.  The returned ledger is
the cap arm, the no-edge of `[22]` that continues at `[145]`. -/
-- EG-NODE [22] hot/cold split $\mathcal P=\mathcal P_{\rm hot}\sqcup\mathcal P_{\rm cold}$: live-hot entropy cap closes?
-- EG-NODE [23] live-hot $P_{13}$ window entropy overflow
-- EG-NODE [145] cold-branch continuation from the no-edge of [22], after the spine estimate
noncomputable def nearCubicHotColdCap
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .skeletonDominates) known]
    [FactKeys.Has (K .windowPackageSeparated) known]
    (fresh : List.Disjoint
      [K .hotColdPartition, K .barrierCap, K .barrierOverflow, closed] known := by
        key_fresh) :
    ExactLedger EGInput.{u} selected (K .barrierCap :: K .hotColdPartition :: known) :=
  let partitioned :=
    (hotColdPartitionRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by key_fresh)
  match barrierDichotomy (data := spineData) partitioned
      (by key_fresh) (by key_fresh) with
  | .left capHistory => capHistory
  | .right overflowHistory =>
      (((liveHotBarrierCapRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile)
        (data := spineData)).runAndCloseIncompatible overflowHistory
          (K .barrierOverflow) (K .barrierCap)
          (by key_fresh) (by key_fresh)).elimClosed (by infer_instance)).elim

/-- **Nodes `[148]`--`[152]`** on the no-arm of `[146]`.  The live-hot entropy
test `[148]`; its overflow arm `[149]` closes against the exact cap that `[22]`'s
live-hot cap and the near-cubic spine give (`coldHotEntropyCapRow`).  On the cap
arm: hot failure forces cold mass `[150]`, all but `o(n)` cold windows are
ambient-cubic `[151]`, and the selected interior-stub excess `[152]`.  The
returned ledger is the `[152]` residual on which `[153]` is decided. -/
-- EG-NODE [148] live-hot entropy cap closes?
-- EG-NODE [149] \(P_{13}\) density cap
-- EG-NODE [150] hot failure forces cold mass: \(C\ge(\theta-\theta_{\rm win})n-o(n)\)
-- EG-NODE [151] all but \(o(n)\) cold windows ambient-cubic
-- EG-NODE [152] selected interior-stub excess: \(b_{\rm int}(\mathfrak S_{\rm cold})\ge9C-o(n)\)
noncomputable def nearCubicColdStubs
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .barrierCap) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .selection) known]
    (fresh : List.Disjoint
      [K .coldHotEntropyOverflow, K .coldHotEntropyCap, closed, K .coldMass,
        K .coldAmbientCubic, K .coldSelectedBranchExcess,
        K .coldAmbientCubicStubExcess, K .coldStubExcess] known := by key_fresh) :
    ExactLedger EGInput.{u} selected
      (K .coldSelectedBranchExcess :: K .coldAmbientCubicStubExcess ::
        K .coldStubExcess :: K .coldAmbientCubic :: K .coldMass ::
        K .coldHotEntropyCap :: known) :=
  match coldHotEntropyDichotomy (data := spineData) history
      (by key_fresh) (by key_fresh) with
  | .left overflowHistory =>
      (((coldHotEntropyCapRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile)
        (data := spineData)).runAndCloseIncompatible overflowHistory
          (K .coldHotEntropyOverflow) (K .coldHotEntropyCap)
          (by key_fresh) (by key_fresh)).elimClosed (by infer_instance)).elim
  | .right hotCapHistory =>
      let mass :=
        (coldMassRow (data := spineData)).run hotCapHistory (by key_fresh)
      let cubic :=
        (coldAmbientCubicRow (data := spineData)).run mass (by key_fresh)
      (coldStubExcessRow (data := spineData)).run cubic (by key_fresh)

/-- **Node `[153]`, linear arm: the return corridors and their states.**
The cold return corridors of `def:cold-corridor-first-failure` (which exist by
`lem:bridgeless`), the declared handoff interfaces, and the cold corridor
states. -/
-- EG-NODE [153] linear first-failure extraction? \(N_{\rm conf}\ge9C/D_{\rm cold}-o(n)\)
noncomputable def nearCubicColdCorridorState
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .hotColdPartition) known]
    (fresh : List.Disjoint
      [K .coldReturnCorridors, K .coldCorridorState] known := by key_fresh) :
    ExactLedger EGInput.{u} selected
      (K .coldCorridorState :: K .coldReturnCorridors :: known) :=
  let corridors :=
    (coldReturnCorridorRow (data := spineData)).run history (by key_fresh)
  (coldCorridorStateRow (data := spineData)).run corridors (by key_fresh)

/-- **Node `[153]`, linear arm: first failures and the candidate family.**
`lem:cold-corridor-first-failure`: the first failure of every corridor and its
routing (F1)--(F5); `lem:cold-germ-extraction`: the exchange bound and the
vertex-disjoint candidate family. -/
noncomputable def nearCubicColdCandidates
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    [FactKeys.Has (K .coldCorridorState) known]
    (fresh : List.Disjoint
      [K .coldFirstFailureOccurrence, K .coldFailureCycle, K .coldFailureDefect,
        K .coldFailureDefectRoute, K .coldFailureCompression,
        K .coldFailureHandoff, K .coldHandoffTransfer, K .coldFailureRouting,
        K .coldExchangeBound, K .coldGermExtraction, K .coldGermCandidates]
      known := by key_fresh) :
    ExactLedger EGInput.{u} selected
      (K .coldGermCandidates :: K .coldExchangeBound :: K .coldGermExtraction ::
        K .coldFailureRouting :: K .coldHandoffTransfer :: K .coldFailureHandoff ::
        K .coldFailureCompression :: K .coldFailureDefect ::
        K .coldFailureDefectRoute :: K .coldFailureCycle ::
        K .coldFirstFailureOccurrence :: known) :=
  let occurrence :=
    (coldFirstFailureOccurrenceRow (data := spineData)).run history (by key_fresh)
  let failureCycle :=
    (coldFailureCycleRow (data := spineData)).run occurrence (by key_fresh)
  let failureDefect :=
    (coldFailureDefectRow (data := spineData)).run failureCycle (by key_fresh)
  let failureCompression :=
    (coldFailureCompressionRow (data := spineData)).run failureDefect
      (by key_fresh)
  let failureHandoff :=
    (coldFailureHandoffRow (data := spineData)).run failureCompression
      (by key_fresh)
  let handoffTransfer :=
    (coldHandoffTransferRow (data := spineData)).run failureHandoff
      (by key_fresh)
  let routed :=
    (coldFirstFailureRoutingRow (data := spineData)).run handoffTransfer
      (by key_fresh)
  let extracted :=
    (coldGermExtractionRow (data := spineData)).run routed (by key_fresh)
  (coldGermCandidatesRow (data := spineData)).run extracted (by key_fresh)

/-- **Node `[153]`, linear arm: the extracted family is positive**
(`lem:cold-germ-extraction` on the linear arm). -/
noncomputable def nearCubicColdGermFamily
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    [FactKeys.Has (K .coldCorridorState) known]
    [FactKeys.Has (K .coldMassLinear) known]
    [FactKeys.Has (K .coldSelectedBranchExcess) known]
    [FactKeys.Has (K .coldStubExcess) known]
    (fresh : List.Disjoint
      [K .coldFirstFailureOccurrence, K .coldFailureCycle, K .coldFailureDefect,
        K .coldFailureDefectRoute, K .coldFailureCompression,
        K .coldFailureHandoff, K .coldHandoffTransfer, K .coldFailureRouting,
        K .coldExchangeBound, K .coldGermExtraction, K .coldGermCandidates,
        K .coldGermFamilyPositive] known := by key_fresh) :
    ExactLedger EGInput.{u} selected
      (K .coldGermFamilyPositive :: K .coldGermCandidates ::
        K .coldExchangeBound :: K .coldGermExtraction :: K .coldFailureRouting ::
        K .coldHandoffTransfer :: K .coldFailureHandoff ::
        K .coldFailureCompression :: K .coldFailureDefect ::
        K .coldFailureDefectRoute :: K .coldFailureCycle ::
        K .coldFirstFailureOccurrence :: known) :=
  (coldGermFamilyPositiveRow (data := spineData)).run
    (nearCubicColdCandidates history) (by key_fresh)

/-- **Node `[154]`, first test, and its terminal `[155]`.**  G1, a hit-realized
configuration, is a power-of-two cycle and closes against the counterexample
condition retained in `K .selection`; the returned ledger is the no-G1 arm. -/
-- EG-NODE [154] bounded configuration case?
-- EG-NODE [155] G1: power-of-two cycle
noncomputable def nearCubicColdNoHit
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .coldGermFamilyPositive) known]
    (fresh : List.Disjoint
      [K .coldGermSomeRealizing, K .coldGermNoneRealizing, closed] known := by
        key_fresh) :
    ExactLedger EGInput.{u} selected (K .coldGermNoneRealizing :: known) :=
  match coldGermRealizationDichotomy (data := spineData) history
      (by key_fresh) (by key_fresh) with
  | .left hitHistory =>
      ((closeIncompatible hitHistory (K .coldGermSomeRealizing) (K .selection)
        (by key_fresh)).elimClosed (by infer_instance)).elim
  | .right unhitHistory => unhitHistory

/-- **Nodes `[156]`--`[157]`: the bounded-configuration trichotomy and the finite
same-interface table** (`lem:cold-bounded-germ-trichotomy`,
`lem:cold-same-interface-table`), and the local cold-terminal exclusion of
`thm:cold-branch-quantitative-closure`. -/
-- EG-NODE [156] G2: target defect, exit (4), or handoff
-- EG-NODE [157] G3 or same-interface table: compression
noncomputable def nearCubicColdTable
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .coldGermCandidates) known]
    [FactKeys.Has (K .coldGermExtraction) known]
    (fresh : List.Disjoint
      [K .coldGermRealized, K .coldGermDistinguished, K .coldGermSilent,
        K .coldGermRouted, K .coldSameInterfaceTable, K .coldBranchClosed]
      known := by key_fresh) :
    ExactLedger EGInput.{u} selected
      (K .coldBranchClosed :: K .coldSameInterfaceTable :: K .coldGermRealized ::
        K .coldGermDistinguished :: K .coldGermSilent :: K .coldGermRouted ::
        known) :=
  let trichotomy :=
    (coldGermTrichotomyRow (data := spineData)).run history (by key_fresh)
  let table :=
    (coldSameInterfaceTableRow (data := spineData)).run trichotomy (by key_fresh)
  (coldBranchClosedRow (data := spineData)).run table (by key_fresh)

end HypostructureErdos64EG
