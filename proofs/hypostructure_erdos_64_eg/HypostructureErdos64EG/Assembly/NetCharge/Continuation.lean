import Hypostructure.Graph.Strategy.SpineRows.AbsorbedConfigurationResidual
import Hypostructure.Graph.Strategy.SpineRows.Bridgeless
import Hypostructure.Graph.Strategy.SpineRows.ExactCollisionDichotomy
import Hypostructure.Graph.Strategy.SpineRows.NegativeSupport
import Hypostructure.Graph.Strategy.SpineRows.NetChargeDichotomy
import Hypostructure.Graph.Strategy.SpineRows.NetChargeLocalization
import Hypostructure.Graph.Strategy.SpineRows.TypeSplitDichotomy
import HypostructureErdos64EG.Assembly.Absorbed.Prerequisites
import HypostructureErdos64EG.Assembly.Absorbed.Residual
import HypostructureErdos64EG.Assembly.NetCharge.Boundary
import HypostructureErdos64EG.Assembly.TypeA.LowSurplusContinuation
import HypostructureErdos64EG.Assembly.TypeB.HighSurplusContinuation

/-!
# Assembly: NetCharge / Continuation

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- **Nodes `[57]`--`[64]`: the large-budget net-charge split**, on the `[56]`
residual of either spine arm.  `[57]` enters the asymptotic order regime and
reads the large-budget net cap; `[58]` localizes the charge; `[59]` splits on the
sign; the nonnegative arm is the `[60]` net-cap contradiction (cap gives
`N₀(R) < 0`, the sibling gives `N₀(R) ≥ 0`); the negative arm selects a connected
negative support `[61]` and `[62]` routes it to Type A `[63]` or Type B `[64]`.
The small-order complement `[57]`, and the Type A / Type B continuations, are the
next loud producers.  It is index-polymorphic over the arm's ledger, so both the
density-cap and route-8 arms use the same definition. -/
-- EG-NODE [57] large-budget net cap
-- EG-NODE [58] net charge \(\No\)
-- EG-NODE [59] \(\No(R)\ge0\)?
-- EG-NODE [60] net-cap contradiction
-- EG-NODE [61] choose connected \(\No(X)<0\)
-- EG-NODE [62] high-degree surplus?
-- EG-NODE [63] Type A continued in Part VIII
-- EG-NODE [64] Type B continued in Part VI
-- EG-NODE [173] exact collision test holds?
-- EG-NODE [174] absorbed-configuration residual: the exact collision fails and the selected cold corridors were charged to high-degree vertices
-- EG-NODE [86] Type A: $\sigma(X)=0$, hence $\defp(X)<|X|/4$
noncomputable def selectedNetChargeContinuation
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .netDeficiencyCap) known]
    [FactKeys.Has (K .stubSupply) known]
    [FactKeys.Has (K .boundaryDemand) known]
    [FactKeys.Has (K .maximalPacking) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .contractionCritical) known]
    (capFresh : K .netChargeCap ∉ known := by simp [K_eq_iff])
    -- `[173]`--`[177]`, the exact collision test and the absorbed-germ residual.
    (failsFresh : K .exactCollisionFails ∉ known := by simp [K_eq_iff])
    (absorbedResidualFresh : K .absorbedConfigurationResidual ∉ known := by simp [K_eq_iff])
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .slackIndependent) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    (absorbedSplitFresh : K .absorbedGermSplit ∉ known := by simp [K_eq_iff])
    (absorbedBridgelessFresh : K .bridgeless ∉ known := by simp [K_eq_iff])
    (absorbedReturnFresh : K .coldReturnCorridors ∉ known := by simp [K_eq_iff])
    (absorbedDeclaredFresh : K .coldDeclaredHandoffLedger ∉ known := by simp [K_eq_iff])
    (absorbedStateFresh : K .coldCorridorState ∉ known := by simp [K_eq_iff])
    (absorbedTerminalFresh : K .denseColdCorridorsTerminal ∉ known := by
      simp [K_eq_iff])
    (absorbedOccurrenceFresh : K .coldFirstFailureOccurrence ∉ known := by simp [K_eq_iff])
    (absorbedRoutingFresh : K .coldFailureRouting ∉ known := by simp [K_eq_iff])
    (absorbedFailureCycleFresh : K .coldFailureCycle ∉ known := by simp [K_eq_iff])
    (absorbedFailureDefectFresh : K .coldFailureDefect ∉ known := by simp [K_eq_iff])
    (absorbedFailureDefectRouteFresh : K .coldFailureDefectRoute ∉ known := by
      simp [K_eq_iff])
    (absorbedFailureCompressionFresh : K .coldFailureCompression ∉ known := by
      simp [K_eq_iff])
    (absorbedFailureHandoffFresh : K .coldFailureHandoff ∉ known := by simp [K_eq_iff])
    (absorbedHandoffTransferFresh : K .coldHandoffTransfer ∉ known := by
      simp [K_eq_iff])
    (absorbedExchangeFresh : K .coldExchangeBound ∉ known := by simp [K_eq_iff])
    (absorbedExtractionFresh : K .coldGermExtraction ∉ known := by simp [K_eq_iff])
    (absorbedCandidatesFresh : K .coldGermCandidates ∉ known := by simp [K_eq_iff])
    (absorbedPositiveFresh : K .coldPositiveGerm ∉ known := by simp [K_eq_iff])
    (absorbedFamilyPositiveFresh : K .coldGermFamilyPositive ∉ known := by
      simp [K_eq_iff])
    (absorbedFanFresh : K .absorbedGermFanData ∉ known := by simp [K_eq_iff])
    (absorbedFanEntryFresh : K .typeBFanEntry ∉ known := by simp [K_eq_iff])
    (absorbedRealizedFresh : K .coldGermRealized ∉ known := by simp [K_eq_iff])
    (absorbedDistinguishedFresh : K .coldGermDistinguished ∉ known := by simp [K_eq_iff])
    (absorbedSilentFresh : K .coldGermSilent ∉ known := by simp [K_eq_iff])
    (absorbedRoutedFresh : K .coldGermRouted ∉ known := by simp [K_eq_iff])
    (absorbedTableFresh : K .coldSameInterfaceTable ∉ known := by simp [K_eq_iff])
    (absorbedClosedFresh : K .coldBranchClosed ∉ known := by simp [K_eq_iff])
    (absorbedNeutralFresh : K .coldNeutralEqualLengthTerminal ∉ known := by
      simp [K_eq_iff])
    (absorbedCanonicalFresh : K .coldCanonicalNeutralConfiguration ∉ known := by
      simp [K_eq_iff])
    (absorbedGenuineFresh : K .coldGenuineSecondStrand ∉ known := by
      simp [K_eq_iff])
    (absorbedReplacementSwapFresh : K .coldCanonicalReplacementSwap ∉ known := by
      simp [K_eq_iff])
    (absorbedReplacementTrivialFresh : K .coldCanonicalReplacementTrivial ∉ known := by
      simp [K_eq_iff])
    (absorbedTwoStrandSurvivorFresh : K .coldTwoStrandSurvivor ∉ known := by
      simp [K_eq_iff])
    (absorbedWindowStubFresh : K .coldWindowStubStructure ∉ known := by
      simp [K_eq_iff])
    (absorbedPairExcludedFresh : K .coldSymmetricPairExcluded ∉ known := by
      simp [K_eq_iff])
    (locFresh : K .netChargeLocalization ∉ known := by simp [K_eq_iff])
    (nonNegFresh : K .netChargeNonNegative ∉ known := by simp [K_eq_iff])
    (negFresh : K .netChargeNegative ∉ known := by simp [K_eq_iff])
    (supportFresh : K .negativeSupport ∉ known := by simp [K_eq_iff])
    (typeAFresh : K .typeALowSurplus ∉ known := by simp [K_eq_iff])
    (typeBFresh : K .typeBHighSurplus ∉ known := by simp [K_eq_iff])
    -- Type A `[63]`, `[86]`--`[94]` freshness on the same ledger.
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .selection) known]
    (boundedFresh : K .typeABoundedSupport ∉ known := by simp [K_eq_iff])
    (routingFresh : K .typeAReceiverRouting ∉ known := by simp [K_eq_iff])
    (saturatedFresh : K .typeASaturatedReceiver ∉ known := by simp [K_eq_iff])
    (unsaturatedFresh : K .typeAUnsaturatedReceivers ∉ known := by simp [K_eq_iff])
    (dischargeFresh : K .typeAUnsaturatedDischarge ∉ known := by simp [K_eq_iff])
    (portFresh : K .typeAPortReturn ∉ known := by simp [K_eq_iff])
    (powerReturnFresh : K .portPowerReturn ∉ known := by simp [K_eq_iff])
    (visibleFresh : K .typeAVisibleEntry ∉ known := by simp [K_eq_iff])
    (excessFresh : K .typeAVisibleFirstExcess ∉ known := by simp [K_eq_iff])
    [FactKeys.Has (K .returnAvoidance) known]
    (returnFresh : K .typeAExitOneReturn ∉ known := by simp [K_eq_iff])
    (oneFreeFresh : K .typeAExitOneFree ∉ known := by simp [K_eq_iff])
    (thetaFresh : K .typeAExitTwoTheta ∉ known := by simp [K_eq_iff])
    (twoFreeFresh : K .typeAExitTwoFree ∉ known := by simp [K_eq_iff])
    (collisionFresh : K .typeAExitThreeCollision ∉ known := by simp [K_eq_iff])
    (threeFreeFresh : K .typeAExitThreeFree ∉ known := by simp [K_eq_iff])
    (closureFresh : closed ∉ known := by simp [K_eq_iff])
    -- Type A exits `(4)`--`(7)`, `[101]`--`[109]` (`selectedTypeAExitFourChain`).
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .replacementExclusion) known]
    (entryFresh : K .typeASaturatedExitEntry ∉ known := by simp [K_eq_iff])
    (descentFresh : K .typeAExitFourFiniteDescent ∉ known := by simp [K_eq_iff])
    (exitFourFresh : K .typeASaturatedHandoffExitFour ∉ known := by simp [K_eq_iff])
    (exitFourFreeFresh : K .typeASaturatedHandoffExitFourFree ∉ known := by simp [K_eq_iff])
    (peeledFresh : K .typeAExitFourPeeled ∉ known := by simp [K_eq_iff])
    (dischargedFresh : K .typeAExitFourReceiverDischarged ∉ known := by simp [K_eq_iff])
    (fiveFresh : K .typeAExitFive ∉ known := by simp [K_eq_iff])
    (fiveFreeFresh : K .typeAExitFiveFree ∉ known := by simp [K_eq_iff])
    (sixFresh : K .typeAExitSix ∉ known := by simp [K_eq_iff])
    (sixFreeFresh : K .typeAExitSixFree ∉ known := by simp [K_eq_iff])
    (sixProperFresh : K .typeAExitSixProper ∉ known := by simp [K_eq_iff])
    (sixGlobalFresh : K .typeAExitSixGlobal ∉ known := by simp [K_eq_iff])
    (sevenProducedFresh : K .typeAExitSevenProduced ∉ known := by simp [K_eq_iff])
    (sevenFreeFresh : K .typeAExitSevenFree ∉ known := by simp [K_eq_iff])
    (sevenHandoffFresh : K .typeAExitSevenHandoff ∉ known := by simp [K_eq_iff])
    -- Type B `[64]`+ keys (`selectedTypeBHighSurplusContinuation`).
    [FactKeys.Has (K .tightEndpoint) known]
    (typeBAssignedFresh : K .typeBAssignedSupport ∉ known := by simp [K_eq_iff])
    (typeBFanEntryFresh : K .typeBFanEntry ∉ known := by simp [K_eq_iff])
    (normalFormFresh : K .highCentreNormalForm ∉ known := by simp [K_eq_iff])
    (fanHeavyFresh : K .typeBFanHeavyCentre ∉ known := by simp [K_eq_iff])
    (fanDegreeFourFresh : K .typeBFanDegreeFourCentres ∉ known := by simp [K_eq_iff])
    (fanLocalFresh : K .typeBFanLocalDichotomy ∉ known := by simp [K_eq_iff])
    (fanCompatibilityFresh : K .sameCenterOpenPortCompatibility ∉ known := by
      simp [K_eq_iff])
    (fanCapFresh : K .fanCertificateCap ∉ known := by simp [K_eq_iff])
    (decoratedMarkedFresh : K .fanCertificateMarked ∉ known := by simp [K_eq_iff])
    (decoratedResidualFresh : K .fanCertificateResidual ∉ known := by simp [K_eq_iff])
    (decoratedCertificateMassFresh : K .fanCertificateResidualMass ∉ known := by simp [K_eq_iff])
    (decoratedCycleFresh : K .typeBDirectCycle ∉ known := by simp [K_eq_iff])
    (decoratedFreeFresh : K .typeBDirectCycleFree ∉ known := by simp [K_eq_iff])
    (decoratedFanEntryFresh : K .typeBFanEntry ∉ known := by simp [K_eq_iff])
    (decoratedB2ChoiceFresh : K .typeBB2Choice ∉ known := by simp [K_eq_iff])
    (decoratedB2ObstructionFresh : K .typeBOverlapObstruction ∉ known := by simp [K_eq_iff])
    (decoratedHybridFresh : K .typeBHybridEntry ∉ known := by simp [K_eq_iff])
    (decoratedLedgerFresh : K .typeBDisjointLedger ∉ known := by simp [K_eq_iff])
    (decoratedBridgeMassFresh : K .typeBBridgeMass ∉ known := by simp [K_eq_iff])
    (decoratedBridgeSublinearFresh : K .typeBBridgeSublinear ∉ known := by simp [K_eq_iff])
    (decoratedExcludedFresh : K .typeBExcluded ∉ known := by simp [K_eq_iff])
    (decoratedExclusionResidualFresh : K .typeBExclusionResidual ∉ known := by simp [K_eq_iff])
    (decoratedExclusionMassFresh : K .typeBExclusionResidualMass ∉ known := by simp [K_eq_iff])
    (decoratedObstructionMassFresh : K .typeBOverlapObstructionMass ∉ known := by simp [K_eq_iff])
    (decoratedClosureFresh : closed ∉ known := by simp [K_eq_iff])
    (fanMarkedFresh : K .fanCertificateMarked ∉ known := by simp [K_eq_iff])
    (fanResidualFresh : K .fanCertificateResidual ∉ known := by simp [K_eq_iff])
    -- Type B `[72]`--`[85]` keys on the same exact ledger.
    [FactKeys.Has (K .uncompressible) known]
    (cycleFresh : K .typeBDirectCycle ∉ known := by simp [K_eq_iff])
    (freeFresh : K .typeBDirectCycleFree ∉ known := by simp [K_eq_iff])
    (choiceFresh : K .typeBB2Choice ∉ known := by simp [K_eq_iff])
    (obstructionFresh : K .typeBOverlapObstruction ∉ known := by simp [K_eq_iff])
    (hybridFresh : K .typeBHybridEntry ∉ known := by simp [K_eq_iff])
    (ledgerFresh : K .typeBDisjointLedger ∉ known := by simp [K_eq_iff])
    (bridgeMassFresh : K .typeBBridgeMass ∉ known := by simp [K_eq_iff])
    (bridgeSublinearFresh : K .typeBBridgeSublinear ∉ known := by simp [K_eq_iff])
    (excludedFresh : K .typeBExcluded ∉ known := by simp [K_eq_iff])
    (exclusionResidualFresh : K .typeBExclusionResidual ∉ known := by simp [K_eq_iff])
    (exclusionMassFresh : K .typeBExclusionResidualMass ∉ known := by simp [K_eq_iff])
    (obstructionMassFresh : K .typeBOverlapObstructionMass ∉ known := by simp [K_eq_iff])
    (certificateMassFresh : K .fanCertificateResidualMass ∉ known := by simp [K_eq_iff])
    (degreeFourProfileFresh : K .typeBFanDegreeFourProfile ∉ known := by simp [K_eq_iff])
    (triangularCoreFresh : K .triangularFanCore ∉ known := by simp [K_eq_iff])
    -- `[108]` decorated handoff, `[110]`--`[116]` route 8, `[76]`/`[85]` → `[123]`.
    (decoratedFresh : K .typeBDecoratedAssignedSupport ∉ known := by simp [K_eq_iff])
    (cubicBaselineFresh : FactKeys.Has (K .cubicBaseline) known := by infer_instance)
    (decoratedHeavyFresh : K .typeBFanHeavyCentre ∉ known := by simp [K_eq_iff])
    (decoratedDegreeFourFresh : K .typeBFanDegreeFourCentres ∉ known := by simp [K_eq_iff])
    (decoratedLocalFresh : K .typeBFanLocalDichotomy ∉ known := by simp [K_eq_iff])
    (decoratedCompatibilityFresh :
      K .sameCenterOpenPortCompatibility ∉ known := by simp [K_eq_iff])
    (decoratedProfileFresh : K .typeBFanDegreeFourProfile ∉ known := by simp [K_eq_iff])
    (decoratedTriangularCoreFresh : K .triangularFanCore ∉ known := by simp [K_eq_iff])
    (profileFresh : K .route8ResidualProfile ∉ known := by simp [K_eq_iff])
    (squeezeFresh : K .route8GlobalSqueeze ∉ known := by simp [K_eq_iff])
    (burdenFresh : K .route8BasinBurden ∉ known := by simp [K_eq_iff])
    (deficitFresh : K .route8LargeBudgetDeficit ∉ known := by simp [K_eq_iff])
    (deficitFailsFresh : K .route8LargeBudgetDeficitFails ∉ known :=
      by simp [K_eq_iff])
    (coreFresh : K .route8CarrierCore ∉ known := by simp [K_eq_iff])
    (trueResidualFresh : K .route8TrueResidual ∉ known := by simp [K_eq_iff])
    (cutParityFresh : K .route8CarrierCutParity ∉ known := by simp [K_eq_iff])
    (smallFresh : K .route8SmallCoreEntry ∉ known := by simp [K_eq_iff])
    (noSmallFresh : K .route8NoSmallCoreEntry ∉ known := by simp [K_eq_iff])
    (collapseFresh : K .route8SmallCoreCollapse ∉ known := by simp [K_eq_iff])
    (censusFresh : K .route8Census ∉ known := by simp [K_eq_iff])
    (twoFresh : K .route8TwoCarrierEntry ∉ known := by simp [K_eq_iff])
    (noTwoFresh : K .route8NoTwoCarrierEntry ∉ known := by simp [K_eq_iff])
    (trueEntryFresh : K .route8TrueTwoCarrierEntry ∉ known := by simp [K_eq_iff])
    (deletionWitnessesFresh : K .route8CarrierDeletionWitnesses ∉ known :=
      by simp [K_eq_iff])
    (privateBudgetFresh : K .route8PrivateCarrierBudget ∉ known :=
      by simp [K_eq_iff])
    (noTwoContradictionFresh : K .route8NoTwoCarrierContradiction ∉ known :=
      by simp [K_eq_iff])
    (terminalNoGoFresh : K .route8TerminalNoGo ∉ known := by simp [K_eq_iff])
    (unifiedNegativeFresh : K .route8UnifiedNegative ∉ known := by simp [K_eq_iff])
    (typeAExclusionFresh : K .typeAExclusion ∉ known := by simp [K_eq_iff])
    (typeBBridgeReductionFresh : K .typeBBridgeReduction ∉ known := by
      simp [K_eq_iff])
    (piecesClassifiedFresh : K .route8PiecesClassified ∉ known := by simp [K_eq_iff])
    (sublinearLedgerFresh : K .typeBSublinearLedger ∉ known := by simp [K_eq_iff])
    (sublinearResidualFresh : K .typeBSublinearResidual ∉ known := by simp [K_eq_iff])
    (unifiedDeficitFresh : K .route8UnifiedDeficit ∉ known := by simp [K_eq_iff])
    (quotientFreeFresh : K .route8QuotientFree ∉ known := by simp [K_eq_iff])
    (quotientResidualFresh : K .route8QuotientResidual ∉ known := by simp [K_eq_iff])
    (unifiedCensusFresh : K .route8UnifiedEntryCensus ∉ known := by simp [K_eq_iff])
    (extractedEntryCensusFresh : K .route8ExtractedEntryCensus ∉ known := by
      simp [K_eq_iff])
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known := by simp [K_eq_iff])
    (peelingFresh : K .route8PeelingDescent ∉ known := by simp [K_eq_iff])
    (stageFailedFresh : K .route8StageRateFailed ∉ known := by simp [K_eq_iff])
    (demandLedgerFresh : K .route8DemandLedger ∉ known := by simp [K_eq_iff])
    (demandAbsorptionFresh : K .route8DemandAbsorption ∉ known := by simp [K_eq_iff])
    (openBoundarySaturatedFresh : K .route8OpenBoundarySaturated ∉ known := by simp [K_eq_iff])
    (demandUnitCountFresh : K .route8DemandUnitCount ∉ known := by simp [K_eq_iff])
    (windowBlockersFresh : K .route8WindowBlockers ∉ known := by simp [K_eq_iff])
    (windowShadowSignatureFresh : K .windowShadowSignature ∉ known := by simp [K_eq_iff])
    (windowShadowTailFresh : K .windowShadowSingletonTail ∉ known := by simp [K_eq_iff])
    (windowShadowCycleFresh : K .windowShadowHitCycle ∉ known := by simp [K_eq_iff])
    (windowShadowExcludedFresh : K .windowShadowHitExcluded ∉ known := by simp [K_eq_iff])
    (demandResidualFresh : K .route8PeeledDemandResidual ∉ known := by simp [K_eq_iff])
    (unpaidExitFourFresh : K .route8UnpaidExitFourResidual ∉ known := by
      simp [K_eq_iff])
    (unifiedVisibleFresh : K .route8UnifiedVisibleResidual ∉ known := by
      simp [K_eq_iff])
    (unifiedVisibleOverloadFresh : K .route8UnifiedVisibleOverload ∉ known := by
      simp [K_eq_iff])
    (jointBalanceFresh : K .route8JointBalance ∉ known := by
      simp [K_eq_iff])
    (unifiedTerminalFresh : K .route8TerminalNoGo ∉ known := by simp [K_eq_iff])
    (globalLocalBridgeFresh : K .typeBGlobalLocalBridge ∉ known := by simp [K_eq_iff])
    (fanClosedFresh : K .fanClosedPort ∉ known := by simp [K_eq_iff])
    (compatibleClosureFresh : K .compatiblePairFanClosure ∉ known := by simp [K_eq_iff])
    (fanClosedRoutingFresh : K .fanClosedPortTypeBRouting ∉ known := by simp [K_eq_iff])
    (compatibleRoutingFresh : K .compatiblePairTypeBRouting ∉ known := by simp [K_eq_iff])
    (triangularRoutingFresh : K .triangularPortTypeBRouting ∉ known := by simp [K_eq_iff])
    (shoulderCompletionFresh : K .triangularShoulderCompletion ∉ known := by simp [K_eq_iff])
    (triangularPortReturnFresh : K .triangularPortReturn ∉ known := by simp [K_eq_iff])
    (firstLandingFresh : K .triangularFirstLanding ∉ known := by simp [K_eq_iff])
    (crossShoulderFresh : K .triangularCrossShoulder ∉ known := by simp [K_eq_iff])
    (fanSafeFresh : K .typeBFanSafe ∉ known := by simp [K_eq_iff])
    (silentFourFreeFresh : K .typeASilentExitFourFree ∉ known := by
      simp [K_eq_iff])
    (silentFiveFreeFresh : K .typeASilentExitFiveFree ∉ known := by
      simp [K_eq_iff])
    (silentSixFreeFresh : K .typeASilentExitSixFree ∉ known := by
      simp [K_eq_iff])
    (silentSevenFreeFresh : K .typeASilentExitSevenFree ∉ known := by
      simp [K_eq_iff])
    :
    SelectedNetChargeBoundary selected := by
  letI := cubicBaselineFresh
  let _cubicBaseline := (history.get (K .cubicBaseline)).down
  -- `[57]` = `[173]`, `lem:exact-collision-test`: node `[56]`'s collision decided
  -- exactly on the current object (`K .netChargeCap`), with no condition on `n`.
  let bridgeless :=
    (bridgelessRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [K_eq_iff, absorbedBridgelessFresh])
  match exactCollisionDichotomy (data := spineData) bridgeless
      (by simp [K_eq_iff, capFresh]) (by simp [K_eq_iff, failsFresh]) with
  | .right failsHistory =>
      -- `[174]`, `lem:exact-collision-test`: the failed collision rearranges to
      -- the cold-window lower bound `n + s·σ_R ≤ A·(|𝒫_hot| + |𝒫_cold|) + s·σ_W`.
      let absorbed :=
        (absorbedConfigurationResidualRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          failsHistory (by simp [K_eq_iff, absorbedResidualFresh])
      let prepared := selectedAbsorbedGermPrerequisites absorbed
        (by simp [K_eq_iff, absorbedReturnFresh])
        (by simp [K_eq_iff, absorbedDeclaredFresh])
        (by simp [K_eq_iff, absorbedStateFresh])
        (by simp [K_eq_iff, absorbedTerminalFresh])
        (by simp [K_eq_iff, absorbedOccurrenceFresh])
        (by simp [K_eq_iff, absorbedRoutingFresh])
        (by simp [K_eq_iff, absorbedFailureCycleFresh])
        (by simp [K_eq_iff, absorbedFailureDefectFresh])
        (by simp [K_eq_iff, absorbedFailureDefectRouteFresh])
        (by simp [K_eq_iff, absorbedFailureCompressionFresh])
        (by simp [K_eq_iff, absorbedFailureHandoffFresh])
        (by simp [K_eq_iff, absorbedHandoffTransferFresh])
        (by simp [K_eq_iff, absorbedExchangeFresh])
        (by simp [K_eq_iff, absorbedExtractionFresh])
        (by simp [K_eq_iff, absorbedCandidatesFresh])
      -- `[175]`--`[177]`, `lem:absorbed-germ-fan-data`: the absorbed-germ
      -- residual (`selectedAbsorbedGermResidual`).
      exact Or.inr (selectedAbsorbedGermResidual prepared
        (by simp [K_eq_iff, absorbedSplitFresh])
        (absorbedPositiveFresh := by simp [K_eq_iff, absorbedPositiveFresh])
        (absorbedFamilyPositiveFresh := by
          simp [K_eq_iff, absorbedFamilyPositiveFresh])
        (by simp [K_eq_iff, absorbedFanFresh])
        (by simp [K_eq_iff, absorbedFanEntryFresh])
        (by simp [K_eq_iff, normalFormFresh])
        (by simp [K_eq_iff, fanHeavyFresh])
        (by simp [K_eq_iff, fanDegreeFourFresh])
        (by simp [K_eq_iff, fanCompatibilityFresh])
        (by simp [K_eq_iff, fanLocalFresh])
        (by simp [K_eq_iff, degreeFourProfileFresh])
        (by simp [K_eq_iff, triangularCoreFresh])
        (by simp [K_eq_iff, fanCapFresh])
        (by simp [K_eq_iff, fanMarkedFresh])
        (by simp [K_eq_iff, fanResidualFresh])
        (by simp [K_eq_iff, certificateMassFresh])
        (by simp [K_eq_iff, cycleFresh])
        (by simp [K_eq_iff, freeFresh])
        (by simp [K_eq_iff, choiceFresh])
        (by simp [K_eq_iff, obstructionFresh])
        (by simp [K_eq_iff, hybridFresh])
        (by simp [K_eq_iff, ledgerFresh])
        (by simp [K_eq_iff, excludedFresh])
        (by simp [K_eq_iff, exclusionResidualFresh])
        (by simp [K_eq_iff, exclusionMassFresh])
        (by simp [K_eq_iff, obstructionMassFresh])
        (by simp [K_eq_iff, absorbedRealizedFresh]) (by simp [K_eq_iff, absorbedDistinguishedFresh])
        (by simp [K_eq_iff, absorbedSilentFresh]) (by simp [K_eq_iff, absorbedRoutedFresh])
        (by simp [K_eq_iff, absorbedTableFresh]) (by simp [K_eq_iff, absorbedClosedFresh])
        (absorbedNeutralFresh := by simp [K_eq_iff, absorbedNeutralFresh])
        (absorbedCanonicalFresh := by simp [K_eq_iff, absorbedCanonicalFresh])
        (absorbedGenuineFresh := by simp [K_eq_iff, absorbedGenuineFresh])
        (absorbedReplacementSwapFresh := by
          simp [K_eq_iff, absorbedReplacementSwapFresh])
        (absorbedReplacementTrivialFresh := by
          simp [K_eq_iff, absorbedReplacementTrivialFresh])
        (absorbedTwoStrandSurvivorFresh := by
          simp [K_eq_iff, absorbedTwoStrandSurvivorFresh])
        (absorbedWindowStubFresh := by simp [K_eq_iff, absorbedWindowStubFresh])
        (absorbedPairExcludedFresh := by simp [K_eq_iff, absorbedPairExcludedFresh])
        (absorbedTerminalFresh := by simp [K_eq_iff, closureFresh])
        (by simp [K_eq_iff, bridgeMassFresh])
        (by simp [K_eq_iff, bridgeSublinearFresh])
        (by infer_instance)
        (by simp [K_eq_iff, extractedEntryCensusFresh])
        (absorbedGlobalLocalBridgeFresh := by simp [K_eq_iff, globalLocalBridgeFresh])
        (absorbedFanClosedFresh := by simp [K_eq_iff, fanClosedFresh])
        (absorbedCompatibleClosureFresh := by simp [K_eq_iff, compatibleClosureFresh])
        (absorbedFanClosedRoutingFresh := by simp [K_eq_iff, fanClosedRoutingFresh])
        (absorbedCompatibleRoutingFresh := by simp [K_eq_iff, compatibleRoutingFresh])
        (absorbedTriangularRoutingFresh := by simp [K_eq_iff, triangularRoutingFresh])
        (absorbedShoulderCompletionFresh := by simp [K_eq_iff, shoulderCompletionFresh])
        (absorbedPortReturnFresh := by simp [K_eq_iff, triangularPortReturnFresh])
        (absorbedFirstLandingFresh := by simp [K_eq_iff, firstLandingFresh])
        (absorbedCrossShoulderFresh := by simp [K_eq_iff, crossShoulderFresh])
        (absorbedFanSafeFresh := by simp [K_eq_iff, fanSafeFresh])
        (absorbedRoutingFresh := by simp [K_eq_iff, routingFresh])
        (absorbedUnifiedNegativeFresh := by simp [K_eq_iff, unifiedNegativeFresh])
        (absorbedTypeAExclusionFresh := by simp [K_eq_iff, typeAExclusionFresh])
        (absorbedTypeBBridgeReductionFresh := by
          simp [K_eq_iff, typeBBridgeReductionFresh])
        (absorbedPiecesClassifiedFresh := by simp [K_eq_iff, piecesClassifiedFresh])
        (absorbedSublinearLedgerFresh := by simp [K_eq_iff, sublinearLedgerFresh])
        (absorbedSublinearResidualFresh := by simp [K_eq_iff, sublinearResidualFresh])
        (absorbedUnifiedDeficitFresh := by simp [K_eq_iff, unifiedDeficitFresh])
        (absorbedQuotientFreeFresh := by simp [K_eq_iff, quotientFreeFresh])
        (absorbedQuotientResidualFresh := by simp [K_eq_iff, quotientResidualFresh])
        (absorbedUnifiedCensusFresh := by simp [K_eq_iff, unifiedCensusFresh])
        (absorbedUnifiedTrueFresh := by simp [K_eq_iff, unifiedTrueFresh])
        (absorbedPeelingFresh := by simp [K_eq_iff, peelingFresh])
        (absorbedStageFailedFresh := by simp [K_eq_iff, stageFailedFresh])
        (absorbedDemandLedgerFresh := by simp [K_eq_iff, demandLedgerFresh])
        (absorbedDemandAbsorptionFresh := by simp [K_eq_iff, demandAbsorptionFresh])
        (absorbedOpenBoundarySaturatedFresh := by simp [K_eq_iff, openBoundarySaturatedFresh])
        (absorbedDemandUnitCountFresh := by simp [K_eq_iff, demandUnitCountFresh])
        (absorbedWindowBlockersFresh := by simp [K_eq_iff, windowBlockersFresh])
        (absorbedWindowShadowSignatureFresh := by simp [K_eq_iff, windowShadowSignatureFresh])
        (absorbedWindowShadowTailFresh := by simp [K_eq_iff, windowShadowTailFresh])
        (absorbedWindowShadowCycleFresh := by simp [K_eq_iff, windowShadowCycleFresh])
        (absorbedWindowShadowExcludedFresh := by simp [K_eq_iff, windowShadowExcludedFresh])
        (absorbedDemandResidualFresh := by simp [K_eq_iff, demandResidualFresh])
        (absorbedUnpaidExitFourFresh := by simp [K_eq_iff, unpaidExitFourFresh])
        (absorbedUnifiedVisibleFresh := by simp [K_eq_iff, unifiedVisibleFresh])
        (absorbedUnifiedVisibleOverloadFresh := by
          simp [K_eq_iff, unifiedVisibleOverloadFresh])
        (absorbedJointBalanceFresh := by simp [K_eq_iff, jointBalanceFresh])
        (absorbedUnifiedTerminalFresh := by simp [K_eq_iff, unifiedTerminalFresh]))
  | .left capped =>
      -- `[58]`: `lem:netcharge-superadd` localizes negative charge to a piece.
      let localized :=
        (netChargeLocalizationRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) spineData).run
          capped (by simp [K_eq_iff, locFresh])
      -- `[59]`: `N₀(R) ≥ 0?`
      match netChargeDichotomy (data := spineData) localized
          (by simp [K_eq_iff, nonNegFresh]) (by simp [K_eq_iff, negFresh]) with
      | .left nonNegHistory =>
          -- `[60]`: the net-cap contradiction on the same canonical maximal
          -- packing.  The cap gives `N₀(R) < 0`; the sibling gives `N₀(R) ≥ 0`.
          have impossible : False := by
            obtain ⟨packing, _canonical, valid, cardinality, _maximal, nonnegative⟩ :=
              (nonNegHistory.get (K .netChargeNonNegative)).down
            have negative :=
              (nonNegHistory.get (K .netChargeCap)).down packing valid cardinality
            exact ((selected.object.not_negativeNetCharge_iff
              (selected.object.remainderSupport packing) spineData.threshold
              spineData.dischargeScale).mpr nonnegative) negative
          exact impossible.elim
      | .right negativeHistory =>
          -- `[61]`: select the connected negative support.
          let support :=
            (negativeSupportRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              negativeHistory (by simp [K_eq_iff, supportFresh])
          -- `[62]`: high-degree surplus? Type A `[63]` / Type B `[64]`.
          match typeSplitDichotomy (data := spineData) support
              (by simp [K_eq_iff, typeAFresh]) (by simp [K_eq_iff, typeBFresh]) with
          | .left typeAHistory =>
              exact Or.inl (selectedTypeALowSurplusContinuation typeAHistory
                (by simp [K_eq_iff, boundedFresh])
                (by simp [K_eq_iff, routingFresh]) (by simp [K_eq_iff, saturatedFresh])
                (by simp [K_eq_iff, unsaturatedFresh]) (by simp [K_eq_iff, dischargeFresh])
                (by simp [K_eq_iff, portFresh])
                (by simp [K_eq_iff, powerReturnFresh])
                (by simp [K_eq_iff, visibleFresh])
                (by simp [K_eq_iff, excessFresh])
                (by simp [K_eq_iff, returnFresh]) (by simp [K_eq_iff, oneFreeFresh])
                (by simp [K_eq_iff, thetaFresh]) (by simp [K_eq_iff, twoFreeFresh])
                (by simp [K_eq_iff, collisionFresh]) (by simp [K_eq_iff, threeFreeFresh])
                (by simp [K_eq_iff, entryFresh]) (by simp [K_eq_iff, descentFresh])
                (by simp [K_eq_iff, exitFourFresh]) (by simp [K_eq_iff, exitFourFreeFresh])
                (by simp [K_eq_iff, peeledFresh]) (by simp [K_eq_iff, dischargedFresh])
                (by simp [K_eq_iff, fiveFresh]) (by simp [K_eq_iff, fiveFreeFresh])
                (by simp [K_eq_iff, sixFresh]) (by simp [K_eq_iff, sixFreeFresh])
                (by simp [K_eq_iff, sixProperFresh]) (by simp [K_eq_iff, sixGlobalFresh])
                (by simp [K_eq_iff, sevenProducedFresh])
                (by simp [K_eq_iff, sevenFreeFresh]) (by simp [K_eq_iff, sevenHandoffFresh])
                (by simp [K_eq_iff, decoratedFresh])
                (by infer_instance) (by simp [K_eq_iff, normalFormFresh]) (by simp [K_eq_iff, decoratedHeavyFresh]) (by simp [K_eq_iff, decoratedDegreeFourFresh]) (by simp [K_eq_iff, decoratedLocalFresh]) (by simp [K_eq_iff, decoratedCompatibilityFresh]) (by simp [K_eq_iff, decoratedProfileFresh]) (by simp [K_eq_iff, decoratedTriangularCoreFresh]) (by simp [K_eq_iff, fanCapFresh]) (by simp [K_eq_iff, decoratedMarkedFresh]) (by simp [K_eq_iff, decoratedResidualFresh]) (by simp [K_eq_iff, decoratedCertificateMassFresh]) (by simp [K_eq_iff, decoratedCycleFresh]) (by simp [K_eq_iff, decoratedFreeFresh]) (by simp [K_eq_iff, decoratedFanEntryFresh]) (by simp [K_eq_iff, decoratedB2ChoiceFresh]) (by simp [K_eq_iff, decoratedB2ObstructionFresh]) (by simp [K_eq_iff, decoratedHybridFresh]) (by simp [K_eq_iff, decoratedLedgerFresh]) (by simp [K_eq_iff, decoratedBridgeMassFresh]) (by simp [K_eq_iff, decoratedBridgeSublinearFresh]) (by simp [K_eq_iff, decoratedExcludedFresh]) (by simp [K_eq_iff, decoratedExclusionResidualFresh]) (by simp [K_eq_iff, decoratedExclusionMassFresh]) (by simp [K_eq_iff, decoratedObstructionMassFresh])
                (by simp [K_eq_iff, profileFresh]) (by simp [K_eq_iff, squeezeFresh])
                (by simp [K_eq_iff, burdenFresh]) (by simp [K_eq_iff, deficitFresh])
                (by simp [K_eq_iff, deficitFailsFresh])
                (by simp [K_eq_iff, coreFresh])
                (by simp [K_eq_iff, trueResidualFresh])
                (by simp [K_eq_iff, cutParityFresh])
                (by simp [K_eq_iff, smallFresh])
                (by simp [K_eq_iff, noSmallFresh])
                (by simp [K_eq_iff, collapseFresh])
                (by simp [K_eq_iff, censusFresh]) (by simp [K_eq_iff, twoFresh])
                (by simp [K_eq_iff, noTwoFresh])
                (by simp [K_eq_iff, trueEntryFresh])
                (by simp [K_eq_iff, deletionWitnessesFresh])
                (by simp [K_eq_iff, privateBudgetFresh])
                (by simp [K_eq_iff, noTwoContradictionFresh])
                (by simp [K_eq_iff, terminalNoGoFresh])
                (by simp [K_eq_iff, unifiedNegativeFresh])
                (by simp [K_eq_iff, typeAExclusionFresh])
                (by simp [K_eq_iff, typeBBridgeReductionFresh])
                (by simp [K_eq_iff, piecesClassifiedFresh])
                (by simp [K_eq_iff, sublinearLedgerFresh])
                (by simp [K_eq_iff, sublinearResidualFresh])
                (by simp [K_eq_iff, unifiedDeficitFresh])
                (by simp [K_eq_iff, quotientFreeFresh])
                (by simp [K_eq_iff, quotientResidualFresh])
                (by simp [K_eq_iff, unifiedCensusFresh])
                (by simp [K_eq_iff, extractedEntryCensusFresh])
                (by simp [K_eq_iff, unifiedTrueFresh])
                (by simp [K_eq_iff, peelingFresh])
                (by simp [K_eq_iff, stageFailedFresh])
                (by simp [K_eq_iff, demandLedgerFresh])
                (by simp [K_eq_iff, demandAbsorptionFresh])
                (by simp [K_eq_iff, openBoundarySaturatedFresh])
                (by simp [K_eq_iff, demandUnitCountFresh])
                (by simp [K_eq_iff, windowBlockersFresh])
                (by simp [K_eq_iff, windowShadowSignatureFresh])
                (by simp [K_eq_iff, windowShadowTailFresh])
                (by simp [K_eq_iff, windowShadowCycleFresh])
                (by simp [K_eq_iff, windowShadowExcludedFresh])
                (by simp [K_eq_iff, demandResidualFresh])
                (unpaidExitFourFresh := by simp [K_eq_iff, unpaidExitFourFresh])
                (unifiedVisibleFresh := by simp [K_eq_iff, unifiedVisibleFresh])
                (unifiedVisibleOverloadFresh := by
                  simp [K_eq_iff, unifiedVisibleOverloadFresh])
                (jointBalanceFresh := by simp [K_eq_iff, jointBalanceFresh])
                (unifiedTerminalFresh := by simp [K_eq_iff, unifiedTerminalFresh])
                (decoratedGlobalLocalBridgeFresh := by simp [K_eq_iff, globalLocalBridgeFresh])
                (fanClosedFresh := by simp [K_eq_iff, fanClosedFresh])
                (compatibleClosureFresh := by simp [K_eq_iff, compatibleClosureFresh])
                (fanClosedRoutingFresh := by simp [K_eq_iff, fanClosedRoutingFresh])
                (compatibleRoutingFresh := by simp [K_eq_iff, compatibleRoutingFresh])
                (shoulderCompletionFresh := by simp [K_eq_iff, shoulderCompletionFresh])
                (portReturnFresh := by simp [K_eq_iff, triangularPortReturnFresh])
                (firstLandingFresh := by simp [K_eq_iff, firstLandingFresh])
                (crossShoulderFresh := by simp [K_eq_iff, crossShoulderFresh])
                (triangularRoutingFresh := by simp [K_eq_iff, triangularRoutingFresh])
                (closureFresh := by simp [K_eq_iff, closureFresh])
                (silentFourFreeFresh := by simp [K_eq_iff, silentFourFreeFresh])
                (silentFiveFreeFresh := by simp [K_eq_iff, silentFiveFreeFresh])
                (silentSixFreeFresh := by simp [K_eq_iff, silentSixFreeFresh])
                (silentSevenFreeFresh := by simp [K_eq_iff, silentSevenFreeFresh]))
          | .right typeBHistory =>
              exact Or.inl (selectedTypeBHighSurplusContinuation typeBHistory
                (by simp [K_eq_iff, routingFresh])
                (by infer_instance)
                (by simp [K_eq_iff, typeBAssignedFresh]) (by simp [K_eq_iff, typeBFanEntryFresh]) (by simp [K_eq_iff, normalFormFresh])
                (by simp [K_eq_iff, fanHeavyFresh]) (by simp [K_eq_iff, fanDegreeFourFresh])
                (by simp [K_eq_iff, fanLocalFresh])
                (by simp [K_eq_iff, fanCompatibilityFresh])
                (by simp [K_eq_iff, fanCapFresh])
                (by simp [K_eq_iff, fanMarkedFresh]) (by simp [K_eq_iff, fanResidualFresh])
                (by simp [K_eq_iff, cycleFresh]) (by simp [K_eq_iff, freeFresh])
                (by simp [K_eq_iff, choiceFresh]) (by simp [K_eq_iff, obstructionFresh])
                (by simp [K_eq_iff, hybridFresh]) (by simp [K_eq_iff, ledgerFresh])
                (by simp [K_eq_iff, bridgeMassFresh])
                (by simp [K_eq_iff, bridgeSublinearFresh])
                (by simp [K_eq_iff, unifiedNegativeFresh])
                (by simp [K_eq_iff, typeAExclusionFresh])
                (by simp [K_eq_iff, typeBBridgeReductionFresh])
                (by simp [K_eq_iff, piecesClassifiedFresh])
                (by simp [K_eq_iff, sublinearLedgerFresh])
                (by simp [K_eq_iff, sublinearResidualFresh])
                (by simp [K_eq_iff, unifiedDeficitFresh])
                (by simp [K_eq_iff, quotientFreeFresh])
                (by simp [K_eq_iff, quotientResidualFresh])
                (by simp [K_eq_iff, unifiedCensusFresh])
                (by simp [K_eq_iff, extractedEntryCensusFresh])
                (by simp [K_eq_iff, unifiedTrueFresh])
                (by simp [K_eq_iff, peelingFresh])
                (by simp [K_eq_iff, stageFailedFresh])
                (by simp [K_eq_iff, demandLedgerFresh])
                (by simp [K_eq_iff, demandAbsorptionFresh])
                (by simp [K_eq_iff, openBoundarySaturatedFresh])
                (by simp [K_eq_iff, demandUnitCountFresh])
                (by simp [K_eq_iff, windowBlockersFresh])
                (by simp [K_eq_iff, windowShadowSignatureFresh])
                (by simp [K_eq_iff, windowShadowTailFresh])
                (by simp [K_eq_iff, windowShadowCycleFresh])
                (by simp [K_eq_iff, windowShadowExcludedFresh])
                (by simp [K_eq_iff, demandResidualFresh])
                (unpaidExitFourFresh := by simp [K_eq_iff, unpaidExitFourFresh])
                (unifiedVisibleFresh := by simp [K_eq_iff, unifiedVisibleFresh])
                (unifiedVisibleOverloadFresh := by
                  simp [K_eq_iff, unifiedVisibleOverloadFresh])
                (jointBalanceFresh := by simp [K_eq_iff, jointBalanceFresh])
                (unifiedTerminalFresh := by simp [K_eq_iff, unifiedTerminalFresh])
                (by simp [K_eq_iff, excludedFresh]) (by simp [K_eq_iff, exclusionResidualFresh])
                (by simp [K_eq_iff, exclusionMassFresh]) (by simp [K_eq_iff, obstructionMassFresh])
                (by simp [K_eq_iff, certificateMassFresh])
                (by simp [K_eq_iff, degreeFourProfileFresh])
                (by simp [K_eq_iff, triangularCoreFresh])
                (fanClosedFresh := by simp [K_eq_iff, fanClosedFresh])
                (compatibleClosureFresh := by simp [K_eq_iff, compatibleClosureFresh])
                (fanClosedRoutingFresh := by simp [K_eq_iff, fanClosedRoutingFresh])
                (compatibleRoutingFresh := by simp [K_eq_iff, compatibleRoutingFresh])
                (shoulderCompletionFresh := by simp [K_eq_iff, shoulderCompletionFresh])
                (portReturnFresh := by simp [K_eq_iff, triangularPortReturnFresh])
                (firstLandingFresh := by simp [K_eq_iff, firstLandingFresh])
                (crossShoulderFresh := by simp [K_eq_iff, crossShoulderFresh])
                (triangularRoutingFresh := by simp [K_eq_iff, triangularRoutingFresh])
                (globalLocalBridgeFresh := by simp [K_eq_iff, globalLocalBridgeFresh]))

end HypostructureErdos64EG
