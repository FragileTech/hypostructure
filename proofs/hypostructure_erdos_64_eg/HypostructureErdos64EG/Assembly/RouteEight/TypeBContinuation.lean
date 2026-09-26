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
# Assembly: RouteEight / TypeBContinuation

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/- The ordinary negative-support wrapper is retained separately from the
absorbed `[177]` carrier.  Its existing enclosing branches already provide the
selected Type A routing fact and use their own Part IX continuation. -/
noncomputable def selectedTypeBRoute8Continuation
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .typeAReceiverRouting) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .highCentreNormalForm) known]
    [FactKeys.Has (K .cubicBaseline) known]
    (bridgeMassFresh : K .typeBBridgeMass ∉ known := by key_fresh)
    (bridgeSublinearFresh : K .typeBBridgeSublinear ∉ known := by key_fresh)
    (unifiedNegativeFresh : K .route8UnifiedNegative ∉ known := by key_fresh)
    (typeAExclusionFresh : K .typeAExclusion ∉ known := by key_fresh)
    (typeBBridgeReductionFresh : K .typeBBridgeReduction ∉ known := by
      key_fresh)
    (piecesClassifiedFresh : K .route8PiecesClassified ∉ known := by
      key_fresh)
    (sublinearLedgerFresh : K .typeBSublinearLedger ∉ known := by
      key_fresh)
    (sublinearResidualFresh : K .typeBSublinearResidual ∉ known := by
      key_fresh)
    (unifiedDeficitFresh : K .route8UnifiedDeficit ∉ known := by
      key_fresh)
    (quotientFreeFresh : K .route8QuotientFree ∉ known := by key_fresh)
    (quotientResidualFresh : K .route8QuotientResidual ∉ known := by
      key_fresh)
    (unifiedCensusFresh : K .route8UnifiedEntryCensus ∉ known := by
      key_fresh)
    (extractedCensusFresh : K .route8ExtractedEntryCensus ∉ known := by
      key_fresh)
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known := by key_fresh)
    (peelingFresh : K .route8PeelingDescent ∉ known := by key_fresh)
    (stageFailedFresh : K .route8StageRateFailed ∉ known := by key_fresh)
    (demandLedgerFresh : K .route8DemandLedger ∉ known := by key_fresh)
    (demandAbsorptionFresh : K .route8DemandAbsorption ∉ known := by
      key_fresh)
    (openBoundarySaturatedFresh : K .route8OpenBoundarySaturated ∉ known := by
      key_fresh)
    (demandUnitCountFresh : K .route8DemandUnitCount ∉ known := by
      key_fresh)
    (windowBlockersFresh : K .route8WindowBlockers ∉ known := by key_fresh)
    (windowShadowSignatureFresh : K .windowShadowSignature ∉ known := by key_fresh)
    (windowShadowTailFresh : K .windowShadowSingletonTail ∉ known := by key_fresh)
    (windowShadowCycleFresh : K .windowShadowHitCycle ∉ known := by key_fresh)
    (windowShadowExcludedFresh : K .windowShadowHitExcluded ∉ known := by key_fresh)
    (demandResidualFresh : K .route8PeeledDemandResidual ∉ known := by
      key_fresh)
    (unifiedTerminalFresh : K .route8TerminalNoGo ∉ known := by key_fresh)
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
  let bridgeMass :=
    (bridgeFanMassRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by key_fresh)
  let bridgeSublinear :=
    (typeBBridgeSublinearRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      bridgeMass (by key_fresh)
  let unifiedNegative :=
    (route8UnifiedNegativeRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      bridgeSublinear (by key_fresh)
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
  match typeBSublinearDichotomy (data := spineData) extractedCensus
      (by key_fresh)
      (by key_fresh) with
  | .right residualHistory =>
      exact Or.inl (residualHistory.get (K .typeBSublinearResidual)).down
  | .left sublinearHistory =>
      let deficit :=
        (route8UnifiedDeficitRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          sublinearHistory (by key_fresh)
      match route8QuotientDichotomy (data := spineData) deficit
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
