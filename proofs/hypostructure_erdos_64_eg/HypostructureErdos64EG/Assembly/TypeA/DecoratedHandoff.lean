import Hypostructure.Graph.Strategy.SpineRows.TypeBDecoratedAssignedSupport
import HypostructureErdos64EG.Assembly.TypeB.DecoratedContinuation

/-!
# Assembly: TypeA / DecoratedHandoff

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- **Node `[108]` → Type B `[65]` on the decorated envelope**: the exact
envelope committed at `[108]` (`K .typeAExitSevenHandoff`) enters the Type B
branch at `[65]`.  There `typeBDecoratedAssignedSupportRow` reads the inherited
selection, normalization, and uncompressibility facts, proves
`lem:decorated-fan-admissibility`, and commits the envelope's assigned support.
Then `[67]`--`[70]` run on that decorated envelope
(`selectedTypeBDecoratedContinuation`). -/
-- EG-NODE [65] Type B assigned support: high-degree fan centers and decorated handoff data
noncomputable def selectedTypeADecoratedHandoff
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .typeAExitSevenHandoff) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .negativeSupport) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .typeAReceiverRouting) known]
    [FactKeys.Has (K .bridgeless) known]
    (decoratedFresh : K .typeBDecoratedAssignedSupport ∉ known)
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
    (decoratedFanEntryFresh : K .typeBFanEntry ∉ known)
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
    (jointBalanceFresh : K .route8JointBalance ∉ known)
    (unifiedTerminalFresh : K .route8UnifiedTwoCarrierExit ∉ known)
    (decoratedExcludedFresh : K .typeBExcluded ∉ known)
    (decoratedExclusionResidualFresh : K .typeBExclusionResidual ∉ known)
    (decoratedExclusionMassFresh : K .typeBExclusionResidualMass ∉ known)
    (decoratedObstructionMassFresh : K .typeBOverlapObstructionMass ∉ known)
    (decoratedGlobalLocalBridgeFresh : K .typeBGlobalLocalBridge ∉ known)
    (fanClosedFresh : K .fanClosedPort ∉ known)
    (compatibleClosureFresh : K .compatiblePairFanClosure ∉ known)
    (fanClosedRoutingFresh : K .fanClosedPortTypeBRouting ∉ known)
    (compatibleRoutingFresh : K .compatiblePairTypeBRouting ∉ known)
    (shoulderCompletionFresh : K .triangularShoulderCompletion ∉ known)
    (portReturnFresh : K .triangularPortReturn ∉ known)
    (firstLandingFresh : K .triangularFirstLanding ∉ known)
    (crossShoulderFresh : K .triangularCrossShoulder ∉ known)
    (triangularRoutingFresh : K .triangularPortTypeBRouting ∉ known)
    (unpaidTwoFresh : K .route8UnpaidTwoCarrier ∉ known := by key_fresh)
    (witnessFreeFresh : K .route8UnpaidWitnessFree ∉ known := by key_fresh)
    (route8ClosureFresh : closed ∉ known := by key_fresh)
    :
    SelectedRouteEightBoundary selected := by
  let assigned :=
    (typeBDecoratedAssignedSupportRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by key_fresh)
  exact selectedTypeBDecoratedContinuation assigned
    (by key_fresh)
    (by key_fresh) (by key_fresh)
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
    (decoratedExcludedFresh := by key_fresh)
    (decoratedExclusionResidualFresh := by
      key_fresh)
    (decoratedExclusionMassFresh := by
      key_fresh)
    (decoratedObstructionMassFresh := by
      key_fresh)
    (decoratedGlobalLocalBridgeFresh := by
      key_fresh)
    (fanClosedFresh := by key_fresh)
    (compatibleClosureFresh := by key_fresh)
    (fanClosedRoutingFresh := by key_fresh)
    (compatibleRoutingFresh := by key_fresh)
    (shoulderCompletionFresh := by key_fresh)
    (portReturnFresh := by key_fresh)
    (firstLandingFresh := by key_fresh)
    (crossShoulderFresh := by key_fresh)
    (triangularRoutingFresh := by key_fresh)

end HypostructureErdos64EG
