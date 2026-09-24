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
      simp [K_eq_iff])
    (unifiedVisibleFresh : K .route8UnifiedVisibleResidual ∉ known := by
      simp [K_eq_iff])
    (unifiedVisibleOverloadFresh : K .route8UnifiedVisibleOverload ∉ known := by
      simp [K_eq_iff])
    (jointBalanceFresh : K .route8JointBalance ∉ known := by
      simp [K_eq_iff])
   :
    SelectedRouteEightBoundary selected := by
  -- Read the discharged receiver fact from the accumulated ledger.
  let _discharged := history.get (K .typeAExitFourReceiverDischarged)
  -- `[123]`: publish `def:typeA-unified-negative` on this residual.
  let unifiedNegative :=
    (route8UnifiedNegativeRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [K_eq_iff, unifiedNegativeFresh])
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
  let bridgeMass :=
    (bridgeFanMassRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      extractedCensus (by simp [K_eq_iff, bridgeMassFresh])
  let bridgeSublinear :=
    (typeBBridgeSublinearRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      bridgeMass (by simp [K_eq_iff, bridgeSublinearFresh])
  match typeBSublinearDichotomy (data := spineData) bridgeSublinear
      (by simp [K_eq_iff, sublinearLedgerFresh])
      (by simp [K_eq_iff, sublinearResidualFresh]) with
  | .right residualHistory =>
      exact Or.inl (residualHistory.get (K .typeBSublinearResidual)).down
  | .left sublinearHistory =>
      let unifiedDeficit :=
        (route8UnifiedDeficitRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          sublinearHistory (by simp [K_eq_iff, unifiedDeficitFresh])
      match route8QuotientDichotomy (data := spineData) unifiedDeficit
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
            (terminalFresh := by simp [K_eq_iff, terminalFresh])
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
              (terminalFresh := by simp [K_eq_iff, terminalFresh])
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
