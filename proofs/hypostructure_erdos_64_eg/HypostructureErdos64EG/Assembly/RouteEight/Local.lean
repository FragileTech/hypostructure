import Hypostructure.Graph.Strategy.SpineRows.Route8OpenBoundarySaturated
import Hypostructure.Graph.Strategy.SpineRows.WindowShadowHitCycle
import Hypostructure.Graph.Strategy.SpineRows.WindowShadowHitExcluded
import Hypostructure.Graph.Strategy.SpineRows.Route8DemandAbsorption
import Hypostructure.Graph.Strategy.SpineRows.Route8DemandPartition
import Hypostructure.Graph.Strategy.SpineRows.Route8JointBalance
import Hypostructure.Graph.Strategy.SpineRows.Route8PeelingDescent
import Hypostructure.Graph.Strategy.SpineRows.Route8QuotientDichotomy
import Hypostructure.Graph.Strategy.SpineRows.Route8StageOutcomeDichotomy
import Hypostructure.Graph.Strategy.SpineRows.Route8TwoCarrierExit
import Hypostructure.Graph.Strategy.SpineRows.Route8UnifiedDeficit
import Hypostructure.Graph.Strategy.SpineRows.Route8UnifiedEntryCensus
import Hypostructure.Graph.Strategy.SpineRows.Route8UnifiedVisibleOverload
import Hypostructure.Graph.Strategy.SpineRows.Route8UnifiedVisibleResidual
import Hypostructure.Graph.Strategy.SpineRows.Route8UnpaidExitFourDichotomy
import Hypostructure.Graph.Strategy.SpineRows.Route8WindowBlockers
import Hypostructure.Graph.Strategy.SpineRows.TypeBSublinearDichotomy
import Hypostructure.Graph.Strategy.TypeAExitRun
import HypostructureErdos64EG.Assembly.RouteEight.Boundary

/-!
# Assembly: RouteEight / Local

The unified route-`8` residual of Part IX, from the Type B sublinear-bridge
decision through nodes `[123]`, `[124]`, `[181]` and `[183]`--`[186]`.  One
composition, generic over the incoming exact ledger: every caller that reaches
the unified target-defect/route-`8` ledger runs it on its own literal
residual.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- **Node `[123]`: finite exact descent terminates in true route 8?**

The descent row records the terminal stage of `thm:large-budget-route8-only`;
the decision is its reduced-rate test.  A passing stage carries the terminal
true two-support entry, closed at node `[124]` by the framework
(`thm:typeA-two-carrier-nogo` against `lem:typeA-carrier-deletion-exit`).  The
failed stage runs the demand, absorption and unique-window blocker ledgers
(with the recorded window-signature hits at its open units) and is the
node-`[181]` residual
(`def:typeA-peeled-demand-residual`), returned with every inherited key. -/
-- EG-NODE [123] finite exact descent terminates in true route 8?
-- EG-NODE [124] local exclusion theorem: no two-support route-8 obstruction
noncomputable def selectedRouteEightDescent
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .route8UnifiedDeficit) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .minDegreeBaseline) known]
    [FactKeys.Has (K .route8UnifiedEntryCensus) known]
    [FactKeys.Has (K .selection) known]
    (peelingFresh : K .route8PeelingDescent ∉ known := by key_fresh)
    (stageRateFresh : K .route8StageRate ∉ known := by key_fresh)
    (stageFailedFresh : K .route8StageRateFailed ∉ known := by key_fresh)
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known := by
      key_fresh)
    (unifiedExitFresh : K .route8UnifiedTwoCarrierExit ∉ known := by
      key_fresh)
    (closureFresh : closed ∉ known := by key_fresh)
    (demandLedgerFresh : K .route8DemandLedger ∉ known := by key_fresh)
    (demandAbsorptionFresh : K .route8DemandAbsorption ∉ known := by
      key_fresh)
    (openBoundarySaturatedFresh : K .route8OpenBoundarySaturated ∉ known := by
      key_fresh)
    (demandUnitCountFresh : K .route8DemandUnitCount ∉ known := by key_fresh)
    (windowBlockersFresh : K .route8WindowBlockers ∉ known := by key_fresh)
    (windowShadowCycleFresh : K .windowShadowHitCycle ∉ known := by
      key_fresh)
    (windowShadowExcludedFresh : K .windowShadowHitExcluded ∉ known := by
      key_fresh) :
    ExactLedger EGInput.{u} selected
      ([K .windowShadowHitExcluded, K .windowShadowHitCycle,
        K .route8WindowBlockers, K .route8OpenBoundarySaturated,
        K .route8DemandUnitCount, K .route8DemandAbsorption,
        K .route8DemandLedger, K .route8StageRateFailed,
        K .route8PeelingDescent] ++ known) := by
  let descended :=
    (route8PeelingDescentRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by key_fresh)
  match route8StageOutcomeDichotomy (data := spineData) descended
      (by key_fresh) (by key_fresh) with
  | .left rateHistory =>
      -- `[123]` yes → `[124]`.
      let trueEntry :=
        (route8StageTrueEntryRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          rateHistory (by key_fresh)
      exact (((route8UnifiedTwoCarrierExitRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).runAndCloseIncompatible trueEntry
          (K .route8UnifiedTrueTwoCarrierEntry)
          (K .route8UnifiedTwoCarrierExit)
          (by key_fresh) (by key_fresh)).elimClosed (by infer_instance)).elim
  | .right failedStage =>
      -- `[123]` no ("failed reduced rate") → the ledgers of `[181]`.
      let ledger :=
        (route8DemandLedgerRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          failedStage (by key_fresh)
      let absorbed :=
        (route8DemandAbsorptionRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          ledger (by key_fresh)
      let saturated :=
        (route8OpenBoundarySaturatedRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          absorbed (by key_fresh)
      let blocked :=
        (route8WindowBlockersRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          saturated (by key_fresh)
      let shadowCycle :=
        (windowShadowHitCycleRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          blocked (by key_fresh)
      exact
        (windowShadowHitExcludedRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          shadowCycle (by key_fresh)

/-- **Nodes `[181]`/`[183]`: maximal-ledger exit-`(4)` reduction**
(`thm:typeA-unpaid-exit4-reduction`).

The incoming node-`[181]` ledger is retained verbatim.  The one-entry
augmentation (168.1) at the committed ledger `P₀` of node `[349]` is published
first; the decision then reads `[349]` and asks whether some unpaid entry of
`P₀` lacks an exit-`(4)` witness.  Such an entry is
exactly the terminal input of `thm:typeA-two-carrier-nogo` and is closed at
node `[124]`; the only survivor is node `[183]`, (168.2). -/
-- EG-NODE [181] maximal-ledger augmentation: some unpaid entry lacks an exit-\textup{(4)} witness?
-- EG-NODE [183] shortest-trace boundary-support test on the retained unified entries
noncomputable def selectedRouteEightUnpaidReduction
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .route8UnifiedEntryCensus) known]
    [FactKeys.Has (K .route8DemandLedger) known]
    [FactKeys.Has (K .route8StageRateFailed) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .minDegreeBaseline) known]
    (unpaidTwoFresh : K .route8UnpaidTwoCarrier ∉ known := by key_fresh)
    (witnessFreeFresh : K .route8UnpaidWitnessFree ∉ known := by key_fresh)
    (residualFresh : K .route8UnpaidExitFourResidual ∉ known := by key_fresh)
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known := by
      key_fresh)
    (unifiedExitFresh : K .route8UnifiedTwoCarrierExit ∉ known := by
      key_fresh)
    (closureFresh : closed ∉ known := by key_fresh) :
    ExactLedger EGInput.{u} selected
      (K .route8UnpaidExitFourResidual :: K .route8UnpaidTwoCarrier :: known) := by
  let twoCarrier :=
    (route8UnpaidTwoCarrierRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by key_fresh)
  match route8UnpaidExitFourDichotomy (data := spineData) twoCarrier
      (by key_fresh) (by key_fresh) with
  | .left witnessFree =>
      -- `[181]` yes → `[124]`.
      let trueEntry :=
        (route8UnpaidTrueEntryRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          witnessFree (by key_fresh)
      exact (((route8UnifiedTwoCarrierExitRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).runAndCloseIncompatible trueEntry
          (K .route8UnifiedTrueTwoCarrierEntry)
          (K .route8UnifiedTwoCarrierExit)
          (by key_fresh) (by key_fresh)).elimClosed (by infer_instance)).elim
  | .right residualHistory =>
      exact residualHistory

set_option maxHeartbeats 8000000 in
/-- **The unified target-defect/route-`8` residual** (`rem:why-unified`),
from the Type B sublinear-bridge decision to node `[186]`.

The negative Type B bridge arm is the Type B residual; the sublinear arm
publishes the unified deficit (`lem:typeA-unified-deficit`) and asks the
quotient-freeness test of the unified census.  Its failure `[348]` is the
route-`8` quotient residual, returned at `[187]` as `thm:main` returns it; on
the free arm the unified entry census is published and
the branch runs node `[123]`, node `[181]`, and the reductions `[183]`--`[185]`
to the joint balance at node `[186]`.  `arm` names the path's prefix, entropy
arm and net-charge continuation; each residual is returned as the product of
its generic facts with those blocks. -/
-- EG-NODE [184] visible-first prefix test on the unchanged all-visible entries
-- EG-NODE [185] canonical actual visible-four packages; non-overloaded count zero
-- EG-NODE [186] OPEN: joint balance and silent-terminal exclusion; visible-entry history retained
noncomputable def selectedRouteEightUnifiedResidual
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    (arm : Route8Arms selected)
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .minDegreeBaseline) known]
    [FactKeys.Has (K .typeBBridgeSublinear) known]
    (sublinearLedgerFresh : K .typeBSublinearLedger ∉ known := by key_fresh)
    (sublinearResidualFresh : K .typeBSublinearResidual ∉ known := by
      key_fresh)
    (unifiedDeficitFresh : K .route8UnifiedDeficit ∉ known := by key_fresh)
    (quotientFreeFresh : K .route8QuotientFree ∉ known := by key_fresh)
    (quotientResidualFresh : K .route8QuotientResidual ∉ known := by
      key_fresh)
    (unifiedCensusFresh : K .route8UnifiedEntryCensus ∉ known := by key_fresh)
    (peelingFresh : K .route8PeelingDescent ∉ known := by key_fresh)
    (stageRateFresh : K .route8StageRate ∉ known := by key_fresh)
    (stageFailedFresh : K .route8StageRateFailed ∉ known := by key_fresh)
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known := by
      key_fresh)
    (unifiedExitFresh : K .route8UnifiedTwoCarrierExit ∉ known := by
      key_fresh)
    (closureFresh : closed ∉ known := by key_fresh)
    (demandLedgerFresh : K .route8DemandLedger ∉ known := by key_fresh)
    (demandAbsorptionFresh : K .route8DemandAbsorption ∉ known := by
      key_fresh)
    (openBoundarySaturatedFresh : K .route8OpenBoundarySaturated ∉ known := by
      key_fresh)
    (demandUnitCountFresh : K .route8DemandUnitCount ∉ known := by key_fresh)
    (windowBlockersFresh : K .route8WindowBlockers ∉ known := by key_fresh)
    (windowShadowCycleFresh : K .windowShadowHitCycle ∉ known := by
      key_fresh)
    (windowShadowExcludedFresh : K .windowShadowHitExcluded ∉ known := by
      key_fresh)
    (unpaidTwoFresh : K .route8UnpaidTwoCarrier ∉ known := by key_fresh)
    (witnessFreeFresh : K .route8UnpaidWitnessFree ∉ known := by key_fresh)
    (unpaidExitFourFresh : K .route8UnpaidExitFourResidual ∉ known := by
      key_fresh)
    (unifiedVisibleFresh : K .route8UnifiedVisibleResidual ∉ known := by
      key_fresh)
    (unifiedVisibleOverloadFresh : K .route8UnifiedVisibleOverload ∉ known := by
      key_fresh)
    (jointBalanceFresh : K .route8JointBalance ∉ known := by key_fresh)
    [FactKeys.Has (K .barrierCap) known]
    [FactKeys.Has (K .barrierEnumeration) known]
    [FactKeys.Has (K .boundaryDemand) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .coldAmbientCubic) known]
    [FactKeys.Has (K .coldAmbientCubicStubExcess) known]
    [FactKeys.Has (K .coldCorridorState) known]
    [FactKeys.Has (K .coldFailureCompression) known]
    [FactKeys.Has (K .coldFailureCycle) known]
    [FactKeys.Has (K .coldFirstFailureOccurrence) known]
    [FactKeys.Has (K .coldHandoffTransfer) known]
    [FactKeys.Has (K .coldHotEntropyCap) known]
    [FactKeys.Has (K .coldMass) known]
    [FactKeys.Has (K .coldReturnCorridors) known]
    [FactKeys.Has (K .coldSelectedBranchExcess) known]
    [FactKeys.Has (K .coldStubExcess) known]
    [FactKeys.Has (K .curvatureFullRank) known]
    [FactKeys.Has (K .curvatureTargetRank) known]
    [FactKeys.Has (K .cycleRankConstraint) known]
    [FactKeys.Has (K .degreeProfileFibres) known]
    [FactKeys.Has (K .exactResponseProfile) known]
    [FactKeys.Has (K .forcedCurvatureCost) known]
    [FactKeys.Has (K .highCentreNormalForm) known]
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .localAlgebra) known]
    [FactKeys.Has (K .everyWitnessSpectrumSplit) known]
    [FactKeys.Has (K .twoHighForcedPath) known]
    [FactKeys.Has (K .sameHighForcedPath) known]
    [FactKeys.Has (K .packingOrderBound) known]
    [FactKeys.Has (K .noSuppressionChordViolation) known]
    [FactKeys.Has (K .specWitnessStructure) known]
    [FactKeys.Has (K .remainderDeficiencyBelowCut) known]
    [FactKeys.Has (K .windowCutCapacity) known]
    [FactKeys.Has (K .primitiveCarrierCount) known]
    [FactKeys.Has (K .singleBoundaryShape) known]
    [FactKeys.Has (K .neighbourhoodPairCount) known]
    [FactKeys.Has (K .starCycleConstraint) known]
    [FactKeys.Has (K .meetingCycleConstraint) known]
    [FactKeys.Has (K .highDegreePairSum) known]
    [FactKeys.Has (K .vertexDeletionComponents) known]
    [FactKeys.Has (K .cyclesThroughVertex) known]
    [FactKeys.Has (K .cutVertexBlockPaths) known]
    [FactKeys.Has (K .cycleDoubleCount) known]
    [FactKeys.Has (K .surplusDartIdentity) known]
    [FactKeys.Has (K .highDegreeCountBound) known]
    [FactKeys.Has (K .admissibleQuotientsLabelInjective) known]
    [FactKeys.Has (K .maximalPacking) known]
    [FactKeys.Has (K .netChargeLocalization) known]
    [FactKeys.Has (K .netDeficiencyCap) known]
    [FactKeys.Has (K .noProperBaseline) known]
    [FactKeys.Has (K .returnAvoidance) known]
    [FactKeys.Has (K .route8BasinBurden) known]
    [FactKeys.Has (K .route8CarrierCore) known]
    [FactKeys.Has (K .route8ExtractedEntryCensus) known]
    [FactKeys.Has (K .route8PiecesClassified) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .route8UnifiedNegative) known]
    [FactKeys.Has (K .sameCenterOpenPortCompatibility) known]
    [FactKeys.Has (K .skeletonDominates) known]
    [FactKeys.Has (K .slackIndependent) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    [FactKeys.Has (K .stubSupply) known]
    [FactKeys.Has (K .targetCompleteContextUniversality) known]
    [FactKeys.Has (K .targetRankCircuit) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .triangularPortReturn) known]
    [FactKeys.Has (K .triangularShoulderCompletion) known]
    [FactKeys.Has (K .typeAExclusion) known]
    [FactKeys.Has (K .typeBAbsorbedCharge) known]
    [FactKeys.Has (K .typeBBridgeMass) known]
    [FactKeys.Has (K .typeBBridgeReduction) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .wedgeSupply) known]
    [FactKeys.Has (K .windowPackageSeparated) known]
    [FactKeys.Has (K .windowPresent) known] :
    SelectedRouteEightBoundary selected := by
  match typeBSublinearDichotomy (data := spineData) history
      (by key_fresh) (by key_fresh) with
  | .right residualHistory =>
      exact Or.inl (typeBSublinearProductReturn residualHistory arm.1 arm.2)
  | .left sublinearHistory =>
      let unifiedDeficit :=
        (route8UnifiedDeficitRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          sublinearHistory (by key_fresh)
      match route8QuotientDichotomy (data := spineData) unifiedDeficit
          (by key_fresh) (by key_fresh) with
      | .right residualHistory =>
          -- `[348]` → `[187]`: `thm:main` returns the failure of route-8
          -- quotient freeness as an open outcome (tex 369-372, 388-390).
          exact Or.inr (Or.inl
            (route8QuotientProductReturn residualHistory arm.1 arm.2))
      | .left quotientFreeHistory =>
          let census :=
            (route8UnifiedEntryCensusRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run quotientFreeHistory (by key_fresh)
          let peeled := selectedRouteEightDescent census
          let unpaid := selectedRouteEightUnpaidReduction peeled
          -- `[183]` → `[184]`: the silent coordinate is zero.
          let visibleResidual :=
            (route8UnifiedVisibleResidualRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run unpaid (by key_fresh)
          -- `[184]` → `[185]`: the non-overloaded coordinate is zero.
          let visibleOverload :=
            (route8UnifiedVisibleOverloadRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run visibleResidual (by key_fresh)
          -- `[185]` → `[186]`: the simultaneous exact account.
          let jointBalance :=
            (route8JointBalanceRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run visibleOverload (by key_fresh)
          exact Or.inr (Or.inr
            (route8JointBalanceProductReturn jointBalance arm.1 arm.2))

end HypostructureErdos64EG
