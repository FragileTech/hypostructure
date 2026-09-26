import Hypostructure.Graph.Strategy.SpineRows.BridgeFanMass
import Hypostructure.Graph.Strategy.SpineRows.Route8ExtractedEntryCensus
import Hypostructure.Graph.Strategy.SpineRows.Route8PiecesClassified
import Hypostructure.Graph.Strategy.SpineRows.Route8QuotientDichotomy
import Hypostructure.Graph.Strategy.SpineRows.Route8UnifiedDeficit
import Hypostructure.Graph.Strategy.SpineRows.Route8UnifiedEntryCensus
import Hypostructure.Graph.Strategy.SpineRows.Route8UnifiedNegative
import Hypostructure.Graph.Strategy.SpineRows.TypeAExclusion
import Hypostructure.Graph.Strategy.SpineRows.TypeBBridgeReduction
import Hypostructure.Graph.Strategy.SpineRows.TypeBBridgeSublinear
import Hypostructure.Graph.Strategy.SpineRows.TypeBSublinearDichotomy
import HypostructureErdos64EG.Assembly.RouteEight.Boundary
import HypostructureErdos64EG.Assembly.RouteEight.Local

/-!
# Assembly: TypeA / ExitFourDischargedRetest

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- **`[102]` → `[89]`, the retest of the peeled receiver.**  `K
.typeAExitFourReceiverDischarged` records the outcome of the recompute-`L₄`
loop: a witnessed peeling set `P₄(w)` at which the receiver is unsaturated
(`lem:typeA-exit4-peeling-charge`: the remaining receiver charge
`q(w) − ¼ − ¼L₄(w)` is nonnegative).  Its peeled loads and their remaining
negative mass enter node `[123]`'s unified target-defect/route-8 pressure
ledger, where `lem:typeA-pressure-is-exit4-peel` reads the witnesses. -/
-- EG-NODE none (establishes no manuscript DAG node)
noncomputable def selectedTypeAExitFourDischargedRetest
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeAExitFourReceiverDischarged) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .negativeSupport) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .typeAReceiverRouting) known]
    (unifiedNegativeFresh : K .route8UnifiedNegative ∉ known)
    (typeAExclusionFresh : K .typeAExclusion ∉ known)
    (typeBBridgeReductionFresh : K .typeBBridgeReduction ∉ known)
    (piecesClassifiedFresh : K .route8PiecesClassified ∉ known)
    (bridgeMassFresh : K .typeBBridgeMass ∉ known)
    (bridgeSublinearFresh : K .typeBBridgeSublinear ∉ known)
    (sublinearLedgerFresh : K .typeBSublinearLedger ∉ known)
    (sublinearResidualFresh : K .typeBSublinearResidual ∉ known)
    (unifiedDeficitFresh : K .route8UnifiedDeficit ∉ known)
    (quotientFreeFresh : K .route8QuotientFree ∉ known)
    (quotientResidualFresh : K .route8QuotientResidual ∉ known)
    (unifiedCensusFresh : K .route8UnifiedEntryCensus ∉ known)
    (extractedCensusFresh : K .route8ExtractedEntryCensus ∉ known)
    (peelingFresh : K .route8PeelingDescent ∉ known)
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known)
    (stageFailedFresh : K .route8StageRateFailed ∉ known)
    (terminalFresh : K .route8TerminalNoGo ∉ known)
    (demandLedgerFresh : K .route8DemandLedger ∉ known)
    (demandAbsorptionFresh : K .route8DemandAbsorption ∉ known)
    (openBoundarySaturatedFresh : K .route8OpenBoundarySaturated ∉ known)
    (demandUnitCountFresh : K .route8DemandUnitCount ∉ known)
    (windowBlockersFresh : K .route8WindowBlockers ∉ known)
    (windowShadowSignatureFresh : K .windowShadowSignature ∉ known)
    (windowShadowTailFresh : K .windowShadowSingletonTail ∉ known)
    (windowShadowCycleFresh : K .windowShadowHitCycle ∉ known)
    (windowShadowExcludedFresh : K .windowShadowHitExcluded ∉ known)
    (demandResidualFresh : K .route8PeeledDemandResidual ∉ known)
    (unpaidExitFourFresh : K .route8UnpaidExitFourResidual ∉ known := by
      key_fresh)
    (unifiedVisibleFresh : K .route8UnifiedVisibleResidual ∉ known := by
      key_fresh)
    (unifiedVisibleOverloadFresh : K .route8UnifiedVisibleOverload ∉ known := by
      key_fresh)
    (jointBalanceFresh : K .route8JointBalance ∉ known := by
      key_fresh)
   :
    SelectedRouteEightBoundary selected := by
  -- Read the discharged receiver fact from the accumulated ledger.
  let _discharged := history.get (K .typeAExitFourReceiverDischarged)
  -- `[123]`: publish `def:typeA-unified-negative` on this residual.
  let unifiedNegative :=
    (route8UnifiedNegativeRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by key_fresh)
  let typeAExcluded :=
    (typeAExclusionRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      unifiedNegative (by key_fresh)
  let typeBReduced :=
    (typeBBridgeReductionRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      typeAExcluded (by key_fresh)
  let classified :=
    (route8PiecesClassifiedRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      typeBReduced (by key_fresh)
  let extractedCensus :=
    (route8ExtractedEntryCensusRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      classified (by key_fresh)
  let bridgeMass :=
    (bridgeFanMassRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      extractedCensus (by key_fresh)
  let bridgeSublinear :=
    (typeBBridgeSublinearRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      bridgeMass (by key_fresh)
  match typeBSublinearDichotomy (data := spineData) bridgeSublinear
      (by key_fresh)
      (by key_fresh) with
  | .right residualHistory =>
      exact Or.inl (residualHistory.get (K .typeBSublinearResidual)).down
  | .left sublinearHistory =>
      let unifiedDeficit :=
        (route8UnifiedDeficitRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          sublinearHistory (by key_fresh)
      match route8QuotientDichotomy (data := spineData) unifiedDeficit
          (by key_fresh)
          (by key_fresh) with
      | .right residualHistory =>
          exact Or.inr (Or.inl
            (residualHistory.get (K .route8QuotientResidual)).down)
      | .left quotientFreeHistory =>
          let census :=
            (route8UnifiedEntryCensusRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run quotientFreeHistory
                (by key_fresh)
          let peeled := selectedLargeBudgetPressureCensus census
            (peelingFresh := by key_fresh)
            (unifiedTrueFresh := by key_fresh)
            (stageFailedFresh := by key_fresh)
            (terminalFresh := by key_fresh)
            (demandLedgerFresh := by key_fresh)
            (demandAbsorptionFresh := by
              key_fresh)
            (openBoundarySaturatedFresh := by
              key_fresh)
            (demandUnitCountFresh := by
              key_fresh)
            (windowBlockersFresh := by key_fresh)
            (windowShadowSignatureFresh := by key_fresh)
            (windowShadowTailFresh := by key_fresh)
            (windowShadowCycleFresh := by key_fresh)
            (windowShadowExcludedFresh := by key_fresh)
            (demandResidualFresh := by key_fresh)
          let unpaidExitFour :=
            selectedRouteEightUnpaidExitFourReduction peeled
              (unifiedTrueFresh := by key_fresh)
              (residualFresh := by key_fresh)
              (terminalFresh := by key_fresh)
          let visibleResidual :=
            selectedRouteEightVisibleResidual unpaidExitFour
              (visibleFresh := by key_fresh)
          let visibleOverload :=
            selectedRouteEightVisibleOverload visibleResidual
              (overloadFresh := by
                key_fresh)
          let jointBalance :=
            selectedRouteEightJointBalance visibleOverload
              (by key_fresh)
          exact Or.inr (Or.inr
            (jointBalance.get (K .route8JointBalance)).down)

end HypostructureErdos64EG
