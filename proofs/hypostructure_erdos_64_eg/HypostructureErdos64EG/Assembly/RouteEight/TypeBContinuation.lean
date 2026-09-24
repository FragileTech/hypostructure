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
    (bridgeMassFresh : K .typeBBridgeMass ∉ known := by simp [K_eq_iff])
    (bridgeSublinearFresh : K .typeBBridgeSublinear ∉ known := by simp [K_eq_iff])
    (unifiedNegativeFresh : K .route8UnifiedNegative ∉ known := by simp [K_eq_iff])
    (typeAExclusionFresh : K .typeAExclusion ∉ known := by simp [K_eq_iff])
    (typeBBridgeReductionFresh : K .typeBBridgeReduction ∉ known := by
      simp [K_eq_iff])
    (piecesClassifiedFresh : K .route8PiecesClassified ∉ known := by
      simp [K_eq_iff])
    (sublinearLedgerFresh : K .typeBSublinearLedger ∉ known := by
      simp [K_eq_iff])
    (sublinearResidualFresh : K .typeBSublinearResidual ∉ known := by
      simp [K_eq_iff])
    (unifiedDeficitFresh : K .route8UnifiedDeficit ∉ known := by
      simp [K_eq_iff])
    (quotientFreeFresh : K .route8QuotientFree ∉ known := by simp [K_eq_iff])
    (quotientResidualFresh : K .route8QuotientResidual ∉ known := by
      simp [K_eq_iff])
    (unifiedCensusFresh : K .route8UnifiedEntryCensus ∉ known := by
      simp [K_eq_iff])
    (extractedCensusFresh : K .route8ExtractedEntryCensus ∉ known := by
      simp [K_eq_iff])
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known := by simp [K_eq_iff])
    (peelingFresh : K .route8PeelingDescent ∉ known := by simp [K_eq_iff])
    (stageFailedFresh : K .route8StageRateFailed ∉ known := by simp [K_eq_iff])
    (demandLedgerFresh : K .route8DemandLedger ∉ known := by simp [K_eq_iff])
    (demandAbsorptionFresh : K .route8DemandAbsorption ∉ known := by
      simp [K_eq_iff])
    (openBoundarySaturatedFresh : K .route8OpenBoundarySaturated ∉ known := by
      simp [K_eq_iff])
    (demandUnitCountFresh : K .route8DemandUnitCount ∉ known := by
      simp [K_eq_iff])
    (windowBlockersFresh : K .route8WindowBlockers ∉ known := by simp [K_eq_iff])
    (windowShadowSignatureFresh : K .windowShadowSignature ∉ known := by simp [K_eq_iff])
    (windowShadowTailFresh : K .windowShadowSingletonTail ∉ known := by simp [K_eq_iff])
    (windowShadowCycleFresh : K .windowShadowHitCycle ∉ known := by simp [K_eq_iff])
    (windowShadowExcludedFresh : K .windowShadowHitExcluded ∉ known := by simp [K_eq_iff])
    (demandResidualFresh : K .route8PeeledDemandResidual ∉ known := by
      simp [K_eq_iff])
    (unifiedTerminalFresh : K .route8TerminalNoGo ∉ known := by simp [K_eq_iff])
    (unpaidExitFourFresh : K .route8UnpaidExitFourResidual ∉ known := by
      simp [K_eq_iff])
    (unifiedVisibleFresh : K .route8UnifiedVisibleResidual ∉ known := by
      simp [K_eq_iff])
    (unifiedVisibleOverloadFresh : K .route8UnifiedVisibleOverload ∉ known := by
      simp [K_eq_iff])
    (jointBalanceFresh : K .route8JointBalance ∉ known := by
      simp [K_eq_iff])
   :
    SelectedRouteEightBoundary selected := by
  let bridgeMass :=
    (bridgeFanMassRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [K_eq_iff, bridgeMassFresh])
  let bridgeSublinear :=
    (typeBBridgeSublinearRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      bridgeMass (by simp [K_eq_iff, bridgeSublinearFresh])
  let unifiedNegative :=
    (route8UnifiedNegativeRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      bridgeSublinear (by simp [K_eq_iff, unifiedNegativeFresh])
  let typeAExcluded :=
    (typeAExclusionRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      unifiedNegative (by simp [K_eq_iff, typeAExclusionFresh])
  let typeBReduced :=
    (typeBBridgeReductionRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      typeAExcluded (by simp [K_eq_iff, typeBBridgeReductionFresh])
  let classified :=
    (route8PiecesClassifiedRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      typeBReduced (by simp [K_eq_iff, piecesClassifiedFresh])
  let extractedCensus :=
    (route8ExtractedEntryCensusRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      classified (by simp [K_eq_iff, extractedCensusFresh])
  match typeBSublinearDichotomy (data := spineData) extractedCensus
      (by simp [K_eq_iff, sublinearLedgerFresh])
      (by simp [K_eq_iff, sublinearResidualFresh]) with
  | .right residualHistory =>
      exact Or.inl (residualHistory.get (K .typeBSublinearResidual)).down
  | .left sublinearHistory =>
      let deficit :=
        (route8UnifiedDeficitRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          sublinearHistory (by simp [K_eq_iff, unifiedDeficitFresh])
      match route8QuotientDichotomy (data := spineData) deficit
          (by simp [K_eq_iff, quotientFreeFresh])
          (by simp [K_eq_iff, quotientResidualFresh]) with
      | .right residualHistory =>
          exact Or.inr (Or.inl
            (residualHistory.get (K .route8QuotientResidual)).down)
      | .left quotientFreeHistory =>
          let census :=
            (route8UnifiedEntryCensusRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run quotientFreeHistory
                (by simp [K_eq_iff, unifiedCensusFresh])
          let peeled := selectedLargeBudgetPressureCensus census
            (peelingFresh := by simp [K_eq_iff, peelingFresh])
            (unifiedTrueFresh := by simp [K_eq_iff, unifiedTrueFresh])
            (stageFailedFresh := by simp [K_eq_iff, stageFailedFresh])
            (terminalFresh := by simp [K_eq_iff, unifiedTerminalFresh])
            (demandLedgerFresh := by simp [K_eq_iff, demandLedgerFresh])
            (demandAbsorptionFresh := by
              simp [K_eq_iff, demandAbsorptionFresh])
            (openBoundarySaturatedFresh := by
              simp [K_eq_iff, openBoundarySaturatedFresh])
            (demandUnitCountFresh := by
              simp [K_eq_iff, demandUnitCountFresh])
            (windowBlockersFresh := by simp [K_eq_iff, windowBlockersFresh])
            (windowShadowSignatureFresh := by simp [K_eq_iff, windowShadowSignatureFresh])
            (windowShadowTailFresh := by simp [K_eq_iff, windowShadowTailFresh])
            (windowShadowCycleFresh := by simp [K_eq_iff, windowShadowCycleFresh])
            (windowShadowExcludedFresh := by simp [K_eq_iff, windowShadowExcludedFresh])
            (demandResidualFresh := by simp [K_eq_iff, demandResidualFresh])
          let unpaidExitFour :=
            selectedRouteEightUnpaidExitFourReduction peeled
              (unifiedTrueFresh := by simp [K_eq_iff, unifiedTrueFresh])
              (residualFresh := by simp [K_eq_iff, unpaidExitFourFresh])
              (terminalFresh := by simp [K_eq_iff, unifiedTerminalFresh])
          let visibleResidual :=
            selectedRouteEightVisibleResidual unpaidExitFour
              (visibleFresh := by simp [K_eq_iff, unifiedVisibleFresh])
          let visibleOverload :=
            selectedRouteEightVisibleOverload visibleResidual
              (overloadFresh := by
                simp [K_eq_iff, unifiedVisibleOverloadFresh])
          let jointBalance :=
            selectedRouteEightJointBalance visibleOverload
              (by simp [K_eq_iff, jointBalanceFresh])
          exact Or.inr (Or.inr
            (jointBalance.get (K .route8JointBalance)).down)

end HypostructureErdos64EG
