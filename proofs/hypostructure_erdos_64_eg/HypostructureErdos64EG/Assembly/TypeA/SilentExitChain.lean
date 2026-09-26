import Hypostructure.Graph.Strategy.SpineRows.TypeASilentExitEntry
import HypostructureErdos64EG.Assembly.TypeA.ExitFourChainSilent

/-!
# Assembly: TypeA / SilentExitChain

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- **Node `[94]` → `[101]`, the silent lane**: the shared saturated exit entry
at the empty peeling set (`lem:typeA-unpeeled-silent-routing`), then the exit
segment `[101]`--`[109]`. -/
-- EG-NODE none (establishes no manuscript DAG node)
noncomputable def selectedTypeASilentExitChain
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .typeAReceiverRouting) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .typeAVisibleFirstExcess) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    (entryFresh : K .typeASaturatedExitEntry ∉ known)
    (descentFresh : K .typeAExitFourFiniteDescent ∉ known)
    (exitFourFresh : K .typeASaturatedHandoffExitFour ∉ known)
    (exitFourFreeFresh : K .typeASaturatedHandoffExitFourFree ∉ known)
    (peeledFresh : K .typeAExitFourPeeled ∉ known)
    (dischargedFresh : K .typeAExitFourReceiverDischarged ∉ known)
    (fiveFresh : K .typeAExitFive ∉ known)
    (fiveFreeFresh : K .typeAExitFiveFree ∉ known)
    (sixFresh : K .typeAExitSix ∉ known)
    (sixFreeFresh : K .typeAExitSixFree ∉ known)
    (sixProperFresh : K .typeAExitSixProper ∉ known)
    (sixGlobalFresh : K .typeAExitSixGlobal ∉ known)
    (sevenProducedFresh : K .typeAExitSevenProduced ∉ known)
    (sevenFreeFresh : K .typeAExitSevenFree ∉ known)
    (sevenHandoffFresh : K .typeAExitSevenHandoff ∉ known)
    (decoratedFresh : K .typeBDecoratedAssignedSupport ∉ known)
    (cubicBaselineFresh : FactKeys.Has (K .cubicBaseline) known := by infer_instance)
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
    (decoratedExcludedFresh : K .typeBExcluded ∉ known)
    (decoratedExclusionResidualFresh : K .typeBExclusionResidual ∉ known)
    (decoratedExclusionMassFresh : K .typeBExclusionResidualMass ∉ known)
    (decoratedObstructionMassFresh : K .typeBOverlapObstructionMass ∉ known)
    (profileFresh : K .route8ResidualProfile ∉ known)
    (squeezeFresh : K .route8GlobalSqueeze ∉ known)
    (burdenFresh : K .route8BasinBurden ∉ known)
    (deficitFresh : K .route8LargeBudgetDeficit ∉ known)
    (deficitFailsFresh : K .route8LargeBudgetDeficitFails ∉ known)
    (coreFresh : K .route8CarrierCore ∉ known)
    (trueResidualFresh : K .route8TrueResidual ∉ known)
    (cutParityFresh : K .route8CarrierCutParity ∉ known)
    (smallFresh : K .route8SmallCoreEntry ∉ known)
    (noSmallFresh : K .route8NoSmallCoreEntry ∉ known)
    (collapseFresh : K .route8SmallCoreCollapse ∉ known)
    (censusFresh : K .route8Census ∉ known)
    (twoFresh : K .route8TwoCarrierEntry ∉ known)
    (noTwoFresh : K .route8NoTwoCarrierEntry ∉ known)
    (trueEntryFresh : K .route8TrueTwoCarrierEntry ∉ known)
    (deletionWitnessesFresh : K .route8CarrierDeletionWitnesses ∉ known)
    (privateBudgetFresh : K .route8PrivateCarrierBudget ∉ known)
    (noTwoContradictionFresh : K .route8PrivateCarrierBudget ∉ known)
    (terminalNoGoFresh : K .route8TwoCarrierExit ∉ known)
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
    [FactKeys.Has (K .bridgeless) known]
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
    [FactKeys.Has (K .negativeSupport) known]
    (closureFresh : closed ∉ known)
    (silentFourFreeFresh : K .typeASilentExitFourFree ∉ known := by
      key_fresh)
    (silentFiveFreeFresh : K .typeASilentExitFiveFree ∉ known := by
      key_fresh)
    (silentSixFreeFresh : K .typeASilentExitSixFree ∉ known := by
      key_fresh)
    (silentSevenFreeFresh : K .typeASilentExitSevenFree ∉ known := by
      key_fresh)
    (unpaidTwoFresh : K .route8UnpaidTwoCarrier ∉ known := by key_fresh)
    (witnessFreeFresh : K .route8UnpaidWitnessFree ∉ known := by key_fresh)
   : SelectedRouteEightBoundary selected := by
  letI := cubicBaselineFresh
  let _cubicBaseline := (history.get (K .cubicBaseline)).down
  let entered :=
    (typeASilentExitEntryRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by key_fresh)
  exact selectedTypeAExitFourChainSilent entered
    (by key_fresh) (by key_fresh)
    (by key_fresh) (by key_fresh)
    (by key_fresh)
    (by key_fresh) (by key_fresh)
    (by key_fresh) (by key_fresh)
    (by key_fresh) (by key_fresh)
    (by key_fresh) (by key_fresh)
    (by key_fresh) (by key_fresh)
    (by infer_instance) (by key_fresh) (by key_fresh) (by key_fresh) (by key_fresh) (by key_fresh) (by key_fresh) (by key_fresh) (by key_fresh) (by key_fresh) (by key_fresh) (by key_fresh) (by key_fresh) (by key_fresh) (by key_fresh) (by key_fresh) (by key_fresh) (by key_fresh) (by key_fresh) (by key_fresh) (by key_fresh) (by key_fresh) (by key_fresh) (by key_fresh) (by key_fresh)
    (by key_fresh) (by key_fresh)
    (by key_fresh) (by key_fresh)
    (by key_fresh)
    (by key_fresh)
                (by key_fresh)
                (by key_fresh)
                (by key_fresh)
                (by key_fresh)
                (by key_fresh)
                (by key_fresh) (by key_fresh)
                (by key_fresh)
                (by key_fresh)
                (by key_fresh)
                (by key_fresh)
                (by key_fresh)
                (by key_fresh)
                (by key_fresh)
                (typeAExclusionFresh := by key_fresh)
                (typeBBridgeReductionFresh := by key_fresh)
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
    (decoratedGlobalLocalBridgeFresh := by key_fresh)
    (fanClosedFresh := by key_fresh)
    (compatibleClosureFresh := by key_fresh)
    (fanClosedRoutingFresh := by key_fresh)
    (compatibleRoutingFresh := by key_fresh)
    (shoulderCompletionFresh := by key_fresh)
    (portReturnFresh := by key_fresh)
    (firstLandingFresh := by key_fresh)
    (crossShoulderFresh := by key_fresh)
    (triangularRoutingFresh := by key_fresh)
    (closureFresh := by key_fresh)
    (silentFourFreeFresh := by key_fresh)
    (silentFiveFreeFresh := by key_fresh)
    (silentSixFreeFresh := by key_fresh)
    (silentSevenFreeFresh := by key_fresh)

end HypostructureErdos64EG
