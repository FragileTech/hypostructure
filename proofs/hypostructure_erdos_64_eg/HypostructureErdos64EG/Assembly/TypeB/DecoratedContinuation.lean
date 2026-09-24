import Hypostructure.Graph.Strategy.SpineRows.FanCertificateCap
import Hypostructure.Graph.Strategy.SpineRows.HighCentreNormalForm
import Hypostructure.Graph.Strategy.SpineRows.SameCenterOpenPortCompatibility
import Hypostructure.Graph.Strategy.SpineRows.TriangularCrossShoulder
import Hypostructure.Graph.Strategy.SpineRows.TriangularFanCore
import Hypostructure.Graph.Strategy.SpineRows.TriangularFirstLanding
import Hypostructure.Graph.Strategy.SpineRows.TriangularPortReturn
import Hypostructure.Graph.Strategy.SpineRows.TriangularPortTypeBRouting
import Hypostructure.Graph.Strategy.SpineRows.TriangularShoulderCompletion
import Hypostructure.Graph.Strategy.SpineRows.TypeBFanDegreeDichotomy
import Hypostructure.Graph.Strategy.SpineRows.TypeBFanDegreeFourProfile
import Hypostructure.Graph.Strategy.SpineRows.TypeBFanLocalDichotomy
import HypostructureErdos64EG.Assembly.TypeB.NearCubicCertificate

/-!
# Assembly: TypeB / DecoratedContinuation

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- **Type B `[67]`--`[70]` on the decorated envelope** (`def:decorated-fan-envelope`,
`def:typeB-assigned-ledger`), on the `[108]`/`[65]` decorated residual
(index-polymorphic).  `[67]` `lem:heavy-neighbourhood-normal-form` and the
registered cubic baseline (object-level rows), `[68]` the single degree split at
the common assigned centres (`typeBFanDegreeDichotomy`), heavy → `[69]`
`cor:heavy-center-local-dichotomy` (`typeBFanLocalDichotomyRow`),
degree-four → `[78]`--`[79]` `cor:degree-four-local-activation`
(`typeBFanDegreeFourProfileRow`); both arms then read `[70]` `lem:fan-certificate`
(`fanCertificateCapRow`); both arms then enter `[71]`/`[80]` on the common
Type B fan support. -/
-- EG-NODE [67] high-degree centers independent; fan neighbours cubic
-- EG-NODE [68] some center has \(d_G(h)>4\)?
-- EG-NODE [69] degree \(>4\) local dichotomy: fan-compatible open pair or \(k-2\) triangular ports gives fan-closed ports
-- EG-NODE [70] fan-safe graph, \(P_{13}\) certificate graph, and certificate-marked cap \(d_G(h)\le8\)
-- EG-NODE [78] degree-\(4\) branch: \(d_G(h)=4\)
-- EG-NODE [79] degree-\(4\) fan profile: center surplus \(1\), \(0\le c\le4\), \(D_B=c-\frac74\)
noncomputable def selectedTypeBDecoratedContinuation
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeBDecoratedAssignedSupport) known]
    [FactKeys.Has (K .typeBFanEntry) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .negativeSupport) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .typeAReceiverRouting) known]
    (normalFormFresh : K .highCentreNormalForm ∉ known)
    (decoratedHeavyFresh : K .typeBFanHeavyCentre ∉ known)
    (decoratedDegreeFourFresh : K .typeBFanDegreeFourCentres ∉ known)
    (decoratedLocalFresh : K .typeBFanLocalDichotomy ∉ known)
    (decoratedCompatibilityFresh :
      K .sameCenterOpenPortCompatibility ∉ known)
    (decoratedProfileFresh : K .typeBFanDegreeFourProfile ∉ known)
    (decoratedTriangularCoreFresh : K .triangularFanCore ∉ known)
    (fanCapFresh : K .fanCertificateCap ∉ known)
    (decoratedMarkedFresh : K .fanCertificateMarked ∉ known)
    (decoratedResidualFresh : K .fanCertificateResidual ∉ known)
    (decoratedCertificateMassFresh : K .fanCertificateResidualMass ∉ known)
    (decoratedCycleFresh : K .typeBDirectCycle ∉ known)
    (decoratedFreeFresh : K .typeBDirectCycleFree ∉ known)
    (decoratedB2ChoiceFresh : K .typeBB2Choice ∉ known)
    (decoratedB2ObstructionFresh : K .typeBOverlapObstruction ∉ known)
    (decoratedHybridFresh : K .typeBHybridEntry ∉ known)
    (decoratedLedgerFresh : K .typeBDisjointLedger ∉ known)
    (decoratedBridgeMassFresh : K .typeBBridgeMass ∉ known)
    (decoratedBridgeSublinearFresh : K .typeBBridgeSublinear ∉ known)
    (unifiedNegativeFresh : K .route8UnifiedNegative ∉ known)
    (typeAExclusionFresh : K .typeAExclusion ∉ known)
    (typeBBridgeReductionFresh : K .typeBBridgeReduction ∉ known)
    (piecesClassifiedFresh : K .route8PiecesClassified ∉ known)
    (sublinearLedgerFresh : K .typeBSublinearLedger ∉ known)
    (sublinearResidualFresh : K .typeBSublinearResidual ∉ known)
    (unifiedDeficitFresh : K .route8UnifiedDeficit ∉ known)
    (quotientFreeFresh : K .route8QuotientFree ∉ known)
    (quotientResidualFresh : K .route8QuotientResidual ∉ known)
    (unifiedCensusFresh : K .route8UnifiedEntryCensus ∉ known)
    (extractedCensusFresh : K .route8ExtractedEntryCensus ∉ known)
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known)
    (peelingFresh : K .route8PeelingDescent ∉ known)
    (stageFailedFresh : K .route8StageRateFailed ∉ known)
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
    (unpaidExitFourFresh : K .route8UnpaidExitFourResidual ∉ known)
    (unifiedVisibleFresh : K .route8UnifiedVisibleResidual ∉ known)
    (unifiedVisibleOverloadFresh : K .route8UnifiedVisibleOverload ∉ known)
    (jointBalanceFresh : K .route8JointBalance ∉ known := by
      simp [K_eq_iff])
    (unifiedTerminalFresh : K .route8TerminalNoGo ∉ known)
    (decoratedExcludedFresh : K .typeBExcluded ∉ known)
    (decoratedExclusionResidualFresh : K .typeBExclusionResidual ∉ known)
    (decoratedExclusionMassFresh : K .typeBExclusionResidualMass ∉ known)
    (decoratedObstructionMassFresh : K .typeBOverlapObstructionMass ∉ known)
    (fanClosedFresh : K .fanClosedPort ∉ known := by simp [K_eq_iff])
    (compatibleClosureFresh : K .compatiblePairFanClosure ∉ known := by simp [K_eq_iff])
    (fanClosedRoutingFresh : K .fanClosedPortTypeBRouting ∉ known := by simp [K_eq_iff])
    (compatibleRoutingFresh : K .compatiblePairTypeBRouting ∉ known := by simp [K_eq_iff])
    (shoulderCompletionFresh : K .triangularShoulderCompletion ∉ known := by simp [K_eq_iff])
    (portReturnFresh : K .triangularPortReturn ∉ known := by simp [K_eq_iff])
    (firstLandingFresh : K .triangularFirstLanding ∉ known := by simp [K_eq_iff])
    (crossShoulderFresh : K .triangularCrossShoulder ∉ known := by simp [K_eq_iff])
    (triangularRoutingFresh : K .triangularPortTypeBRouting ∉ known := by simp [K_eq_iff])
    (decoratedGlobalLocalBridgeFresh : K .typeBGlobalLocalBridge ∉ known)
   :
    SelectedRouteEightBoundary selected := by
  -- `[67]`
  let normalForm :=
    (highCentreNormalFormRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [K_eq_iff, normalFormFresh])
  -- `[68]` at the decorated envelope's assigned centres.
  match typeBFanDegreeDichotomy (data := spineData) normalForm
      (by simp [K_eq_iff, decoratedHeavyFresh])
      (by simp [K_eq_iff, decoratedDegreeFourFresh]) with
  | .left heavyHistory =>
      -- `[69]`: the compatibility lemma is a first-class ledger fact consumed
      -- by the heavy-centre dichotomy on this same decorated envelope.
      let compatibleHistory :=
        (sameCenterOpenPortCompatibilityRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          heavyHistory
            (by simp [K_eq_iff, decoratedCompatibilityFresh])
      let localDichotomy :=
        (typeBFanLocalDichotomyRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          compatibleHistory (by simp [K_eq_iff, decoratedLocalFresh])
      let portRouted := Assembly.Internal.selectedTypeBPortRoutingPrefix localDichotomy
        (by simp [K_eq_iff, fanClosedFresh])
        (by simp [K_eq_iff, compatibleClosureFresh])
        (by simp [K_eq_iff, fanClosedRoutingFresh])
        (by simp [K_eq_iff, compatibleRoutingFresh])
      -- `[70]`
      let capped :=
        (fanCertificateCapRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          portRouted (by simp [K_eq_iff, fanCapFresh])
      exact selectedTypeBNearCubicCertificateAfterPortRouting capped
        (by simp [K_eq_iff, decoratedMarkedFresh])
        (by simp [K_eq_iff, decoratedResidualFresh])
        (by simp [K_eq_iff, decoratedCertificateMassFresh])
        (by simp [K_eq_iff, decoratedCycleFresh])
        (by simp [K_eq_iff, decoratedFreeFresh])
        (by simp [K_eq_iff, decoratedB2ChoiceFresh])
        (by simp [K_eq_iff, decoratedB2ObstructionFresh])
        (by simp [K_eq_iff, decoratedHybridFresh])
        (by simp [K_eq_iff, decoratedLedgerFresh])
        (by simp [K_eq_iff, decoratedExcludedFresh])
        (by simp [K_eq_iff, decoratedExclusionResidualFresh])
        (by simp [K_eq_iff, decoratedExclusionMassFresh])
        (by simp [K_eq_iff, decoratedObstructionMassFresh])
        (by simp [K_eq_iff, decoratedBridgeMassFresh])
        (by simp [K_eq_iff, decoratedBridgeSublinearFresh])
        (by simp [K_eq_iff, unifiedNegativeFresh])
        (typeAExclusionFresh := by simp [K_eq_iff, typeAExclusionFresh])
        (typeBBridgeReductionFresh := by
          simp [K_eq_iff, typeBBridgeReductionFresh])
        (piecesClassifiedFresh := by simp [K_eq_iff, piecesClassifiedFresh])
        (sublinearLedgerFresh := by simp [K_eq_iff, sublinearLedgerFresh])
        (sublinearResidualFresh := by simp [K_eq_iff, sublinearResidualFresh])
        (unifiedDeficitFresh := by simp [K_eq_iff, unifiedDeficitFresh])
        (quotientFreeFresh := by simp [K_eq_iff, quotientFreeFresh])
        (quotientResidualFresh := by simp [K_eq_iff, quotientResidualFresh])
        (unifiedCensusFresh := by simp [K_eq_iff, unifiedCensusFresh])
        (extractedCensusFresh := by simp [K_eq_iff, extractedCensusFresh])
        (unifiedTrueFresh := by simp [K_eq_iff, unifiedTrueFresh])
        (peelingFresh := by simp [K_eq_iff, peelingFresh])
        (stageFailedFresh := by simp [K_eq_iff, stageFailedFresh])
        (demandLedgerFresh := by simp [K_eq_iff, demandLedgerFresh])
        (demandAbsorptionFresh := by simp [K_eq_iff, demandAbsorptionFresh])
        (openBoundarySaturatedFresh := by simp [K_eq_iff, openBoundarySaturatedFresh])
        (demandUnitCountFresh := by simp [K_eq_iff, demandUnitCountFresh])
        (windowBlockersFresh := by simp [K_eq_iff, windowBlockersFresh])
        (windowShadowSignatureFresh := by simp [K_eq_iff, windowShadowSignatureFresh])
        (windowShadowTailFresh := by simp [K_eq_iff, windowShadowTailFresh])
        (windowShadowCycleFresh := by simp [K_eq_iff, windowShadowCycleFresh])
        (windowShadowExcludedFresh := by simp [K_eq_iff, windowShadowExcludedFresh])
        (demandResidualFresh := by simp [K_eq_iff, demandResidualFresh])
        (unpaidExitFourFresh := by simp [K_eq_iff, unpaidExitFourFresh])
        (unifiedVisibleFresh := by simp [K_eq_iff, unifiedVisibleFresh])
        (unifiedVisibleOverloadFresh := by
          simp [K_eq_iff, unifiedVisibleOverloadFresh])
        (jointBalanceFresh := by simp [K_eq_iff, jointBalanceFresh])
        (unifiedTerminalFresh := by simp [K_eq_iff, unifiedTerminalFresh])
        (globalLocalBridgeFresh := by
          simp [K_eq_iff, decoratedGlobalLocalBridgeFresh])
  | .right degreeFourHistory =>
      -- `[78]`--`[79]`
      let profile :=
        (typeBFanDegreeFourProfileRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          degreeFourHistory (by simp [K_eq_iff, decoratedProfileFresh])
      let triangularCore :=
        (triangularFanCoreRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          profile (by simp [K_eq_iff, decoratedTriangularCoreFresh])
      let completed :=
        (triangularShoulderCompletionRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          triangularCore (by simp [K_eq_iff, shoulderCompletionFresh])
      let returned :=
        (triangularPortReturnRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          completed (by simp [K_eq_iff, portReturnFresh])
      let firstLanded :=
        (triangularFirstLandingRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          returned (by simp [K_eq_iff, firstLandingFresh])
      let crossShouldered :=
        (triangularCrossShoulderRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          firstLanded (by simp [K_eq_iff, crossShoulderFresh])
      let portRouted := Assembly.Internal.selectedTypeBPortRoutingPrefix crossShouldered
        (by simp [K_eq_iff, fanClosedFresh])
        (by simp [K_eq_iff, compatibleClosureFresh])
        (by simp [K_eq_iff, fanClosedRoutingFresh])
        (by simp [K_eq_iff, compatibleRoutingFresh])
      let triangularRouted :=
        (triangularPortTypeBRoutingRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          portRouted (by simp [K_eq_iff, triangularRoutingFresh])
      -- `[70]`/`[80]`
      let capped :=
        (fanCertificateCapRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          triangularRouted (by simp [K_eq_iff, fanCapFresh])
      exact selectedTypeBNearCubicCertificateAfterPortRouting capped
        (by simp [K_eq_iff, decoratedMarkedFresh])
        (by simp [K_eq_iff, decoratedResidualFresh])
        (by simp [K_eq_iff, decoratedCertificateMassFresh])
        (by simp [K_eq_iff, decoratedCycleFresh])
        (by simp [K_eq_iff, decoratedFreeFresh])
        (by simp [K_eq_iff, decoratedB2ChoiceFresh])
        (by simp [K_eq_iff, decoratedB2ObstructionFresh])
        (by simp [K_eq_iff, decoratedHybridFresh])
        (by simp [K_eq_iff, decoratedLedgerFresh])
        (by simp [K_eq_iff, decoratedExcludedFresh])
        (by simp [K_eq_iff, decoratedExclusionResidualFresh])
        (by simp [K_eq_iff, decoratedExclusionMassFresh])
        (by simp [K_eq_iff, decoratedObstructionMassFresh])
        (by simp [K_eq_iff, decoratedBridgeMassFresh])
        (by simp [K_eq_iff, decoratedBridgeSublinearFresh])
        (by simp [K_eq_iff, unifiedNegativeFresh])
        (typeAExclusionFresh := by simp [K_eq_iff, typeAExclusionFresh])
        (typeBBridgeReductionFresh := by
          simp [K_eq_iff, typeBBridgeReductionFresh])
        (piecesClassifiedFresh := by simp [K_eq_iff, piecesClassifiedFresh])
        (sublinearLedgerFresh := by simp [K_eq_iff, sublinearLedgerFresh])
        (sublinearResidualFresh := by simp [K_eq_iff, sublinearResidualFresh])
        (unifiedDeficitFresh := by simp [K_eq_iff, unifiedDeficitFresh])
        (quotientFreeFresh := by simp [K_eq_iff, quotientFreeFresh])
        (quotientResidualFresh := by simp [K_eq_iff, quotientResidualFresh])
        (unifiedCensusFresh := by simp [K_eq_iff, unifiedCensusFresh])
        (extractedCensusFresh := by simp [K_eq_iff, extractedCensusFresh])
        (unifiedTrueFresh := by simp [K_eq_iff, unifiedTrueFresh])
        (peelingFresh := by simp [K_eq_iff, peelingFresh])
        (stageFailedFresh := by simp [K_eq_iff, stageFailedFresh])
        (demandLedgerFresh := by simp [K_eq_iff, demandLedgerFresh])
        (demandAbsorptionFresh := by simp [K_eq_iff, demandAbsorptionFresh])
        (openBoundarySaturatedFresh := by simp [K_eq_iff, openBoundarySaturatedFresh])
        (demandUnitCountFresh := by simp [K_eq_iff, demandUnitCountFresh])
        (windowBlockersFresh := by simp [K_eq_iff, windowBlockersFresh])
        (windowShadowSignatureFresh := by simp [K_eq_iff, windowShadowSignatureFresh])
        (windowShadowTailFresh := by simp [K_eq_iff, windowShadowTailFresh])
        (windowShadowCycleFresh := by simp [K_eq_iff, windowShadowCycleFresh])
        (windowShadowExcludedFresh := by simp [K_eq_iff, windowShadowExcludedFresh])
        (demandResidualFresh := by simp [K_eq_iff, demandResidualFresh])
        (unpaidExitFourFresh := by simp [K_eq_iff, unpaidExitFourFresh])
        (unifiedVisibleFresh := by simp [K_eq_iff, unifiedVisibleFresh])
        (unifiedVisibleOverloadFresh := by
          simp [K_eq_iff, unifiedVisibleOverloadFresh])
        (jointBalanceFresh := by simp [K_eq_iff, jointBalanceFresh])
        (unifiedTerminalFresh := by simp [K_eq_iff, unifiedTerminalFresh])
        (globalLocalBridgeFresh := by
          simp [K_eq_iff, decoratedGlobalLocalBridgeFresh])

end HypostructureErdos64EG
