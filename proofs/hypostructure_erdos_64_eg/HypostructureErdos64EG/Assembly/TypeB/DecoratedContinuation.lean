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
    (demandResidualFresh : K .route8StageRate ∉ known)
    (unpaidExitFourFresh : K .route8UnpaidExitFourResidual ∉ known)
    (unifiedVisibleFresh : K .route8UnifiedVisibleResidual ∉ known)
    (unifiedVisibleOverloadFresh : K .route8UnifiedVisibleOverload ∉ known)
    (jointBalanceFresh : K .route8JointBalance ∉ known := by
      key_fresh)
    (unifiedTerminalFresh : K .route8UnifiedTwoCarrierExit ∉ known)
    (decoratedExcludedFresh : K .typeBExcluded ∉ known)
    (decoratedExclusionResidualFresh : K .typeBExclusionResidual ∉ known)
    (decoratedExclusionMassFresh : K .typeBExclusionResidualMass ∉ known)
    (decoratedObstructionMassFresh : K .typeBOverlapObstructionMass ∉ known)
    (fanClosedFresh : K .fanClosedPort ∉ known := by key_fresh)
    (compatibleClosureFresh : K .compatiblePairFanClosure ∉ known := by key_fresh)
    (fanClosedRoutingFresh : K .fanClosedPortTypeBRouting ∉ known := by key_fresh)
    (compatibleRoutingFresh : K .compatiblePairTypeBRouting ∉ known := by key_fresh)
    (shoulderCompletionFresh : K .triangularShoulderCompletion ∉ known := by key_fresh)
    (portReturnFresh : K .triangularPortReturn ∉ known := by key_fresh)
    (firstLandingFresh : K .triangularFirstLanding ∉ known := by key_fresh)
    (crossShoulderFresh : K .triangularCrossShoulder ∉ known := by key_fresh)
    (triangularRoutingFresh : K .triangularPortTypeBRouting ∉ known := by key_fresh)
    (decoratedGlobalLocalBridgeFresh : K .typeBGlobalLocalBridge ∉ known)
    (unpaidTwoFresh : K .route8UnpaidTwoCarrier ∉ known := by key_fresh)
    (witnessFreeFresh : K .route8UnpaidWitnessFree ∉ known := by key_fresh)
    (route8ClosureFresh : closed ∉ known := by key_fresh)
   :
    SelectedRouteEightBoundary selected := by
  -- `[67]`
  let normalForm :=
    (highCentreNormalFormRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by key_fresh)
  -- `[68]` at the decorated envelope's assigned centres.
  match typeBFanDegreeDichotomy (data := spineData) normalForm
      (by key_fresh)
      (by key_fresh) with
  | .left heavyHistory =>
      -- `[69]`: the compatibility lemma is a first-class ledger fact consumed
      -- by the heavy-centre dichotomy on this same decorated envelope.
      let compatibleHistory :=
        (sameCenterOpenPortCompatibilityRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          heavyHistory
            (by key_fresh)
      let localDichotomy :=
        (typeBFanLocalDichotomyRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          compatibleHistory (by key_fresh)
      let portRouted := Assembly.Internal.selectedTypeBPortRoutingPrefix localDichotomy
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
      -- `[70]`
      let capped :=
        (fanCertificateCapRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          portRouted (by key_fresh)
      exact selectedTypeBNearCubicCertificateAfterPortRouting capped
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (typeAExclusionFresh := by key_fresh)
        (typeBBridgeReductionFresh := by
          key_fresh)
        (piecesClassifiedFresh := by key_fresh)
        (sublinearLedgerFresh := by key_fresh)
        (sublinearResidualFresh := by key_fresh)
        (unifiedDeficitFresh := by key_fresh)
        (quotientFreeFresh := by key_fresh)
        (quotientResidualFresh := by key_fresh)
        (unifiedCensusFresh := by key_fresh)
        (extractedCensusFresh := by key_fresh)
        (unifiedTrueFresh := by key_fresh)
        (peelingFresh := by key_fresh)
        (stageFailedFresh := by key_fresh)
        (demandLedgerFresh := by key_fresh)
        (demandAbsorptionFresh := by key_fresh)
        (openBoundarySaturatedFresh := by key_fresh)
        (demandUnitCountFresh := by key_fresh)
        (windowBlockersFresh := by key_fresh)
        (windowShadowSignatureFresh := by key_fresh)
        (windowShadowTailFresh := by key_fresh)
        (windowShadowCycleFresh := by key_fresh)
        (windowShadowExcludedFresh := by key_fresh)
        (demandResidualFresh := by key_fresh)
        (unpaidExitFourFresh := by key_fresh)
        (unifiedVisibleFresh := by key_fresh)
        (unifiedVisibleOverloadFresh := by
          key_fresh)
        (jointBalanceFresh := by key_fresh)
        (unifiedTerminalFresh := by key_fresh)
        (globalLocalBridgeFresh := by
          key_fresh)
  | .right degreeFourHistory =>
      -- `[78]`--`[79]`
      let profile :=
        (typeBFanDegreeFourProfileRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          degreeFourHistory (by key_fresh)
      let triangularCore :=
        (triangularFanCoreRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          profile (by key_fresh)
      let completed :=
        (triangularShoulderCompletionRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          triangularCore (by key_fresh)
      let returned :=
        (triangularPortReturnRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          completed (by key_fresh)
      let firstLanded :=
        (triangularFirstLandingRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          returned (by key_fresh)
      let crossShouldered :=
        (triangularCrossShoulderRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          firstLanded (by key_fresh)
      let portRouted := Assembly.Internal.selectedTypeBPortRoutingPrefix crossShouldered
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
      let triangularRouted :=
        (triangularPortTypeBRoutingRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          portRouted (by key_fresh)
      -- `[70]`/`[80]`
      let capped :=
        (fanCertificateCapRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          triangularRouted (by key_fresh)
      exact selectedTypeBNearCubicCertificateAfterPortRouting capped
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (typeAExclusionFresh := by key_fresh)
        (typeBBridgeReductionFresh := by
          key_fresh)
        (piecesClassifiedFresh := by key_fresh)
        (sublinearLedgerFresh := by key_fresh)
        (sublinearResidualFresh := by key_fresh)
        (unifiedDeficitFresh := by key_fresh)
        (quotientFreeFresh := by key_fresh)
        (quotientResidualFresh := by key_fresh)
        (unifiedCensusFresh := by key_fresh)
        (extractedCensusFresh := by key_fresh)
        (unifiedTrueFresh := by key_fresh)
        (peelingFresh := by key_fresh)
        (stageFailedFresh := by key_fresh)
        (demandLedgerFresh := by key_fresh)
        (demandAbsorptionFresh := by key_fresh)
        (openBoundarySaturatedFresh := by key_fresh)
        (demandUnitCountFresh := by key_fresh)
        (windowBlockersFresh := by key_fresh)
        (windowShadowSignatureFresh := by key_fresh)
        (windowShadowTailFresh := by key_fresh)
        (windowShadowCycleFresh := by key_fresh)
        (windowShadowExcludedFresh := by key_fresh)
        (demandResidualFresh := by key_fresh)
        (unpaidExitFourFresh := by key_fresh)
        (unifiedVisibleFresh := by key_fresh)
        (unifiedVisibleOverloadFresh := by
          key_fresh)
        (jointBalanceFresh := by key_fresh)
        (unifiedTerminalFresh := by key_fresh)
        (globalLocalBridgeFresh := by
          key_fresh)

end HypostructureErdos64EG
