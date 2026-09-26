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
    (capFresh : K .netChargeCap ∉ known := by key_fresh)
    -- `[173]`--`[177]`, the exact collision test and the absorbed-germ residual.
    (failsFresh : K .exactCollisionFails ∉ known := by key_fresh)
    (absorbedResidualFresh : K .absorbedConfigurationResidual ∉ known := by key_fresh)
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .slackIndependent) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    (absorbedSplitFresh : K .absorbedGermSplit ∉ known := by key_fresh)
    (absorbedBridgelessFresh : K .bridgeless ∉ known := by key_fresh)
    (absorbedReturnFresh : K .coldReturnCorridors ∉ known := by key_fresh)
    (absorbedDeclaredFresh : K .coldDeclaredHandoffLedger ∉ known := by key_fresh)
    (absorbedStateFresh : K .coldCorridorState ∉ known := by key_fresh)
    (absorbedTerminalFresh : K .denseColdCorridorsTerminal ∉ known := by
      key_fresh)
    (absorbedOccurrenceFresh : K .coldFirstFailureOccurrence ∉ known := by key_fresh)
    (absorbedRoutingFresh : K .coldFailureRouting ∉ known := by key_fresh)
    (absorbedFailureCycleFresh : K .coldFailureCycle ∉ known := by key_fresh)
    (absorbedFailureDefectFresh : K .coldFailureDefect ∉ known := by key_fresh)
    (absorbedFailureDefectRouteFresh : K .coldFailureDefectRoute ∉ known := by
      key_fresh)
    (absorbedFailureCompressionFresh : K .coldFailureCompression ∉ known := by
      key_fresh)
    (absorbedFailureHandoffFresh : K .coldFailureHandoff ∉ known := by key_fresh)
    (absorbedHandoffTransferFresh : K .coldHandoffTransfer ∉ known := by
      key_fresh)
    (absorbedExchangeFresh : K .coldExchangeBound ∉ known := by key_fresh)
    (absorbedExtractionFresh : K .coldGermExtraction ∉ known := by key_fresh)
    (absorbedCandidatesFresh : K .coldGermCandidates ∉ known := by key_fresh)
    (absorbedPositiveFresh : K .coldPositiveGerm ∉ known := by key_fresh)
    (absorbedFamilyPositiveFresh : K .coldGermFamilyPositive ∉ known := by
      key_fresh)
    (absorbedFanFresh : K .absorbedGermFanData ∉ known := by key_fresh)
    (absorbedFanEntryFresh : K .typeBFanEntry ∉ known := by key_fresh)
    (absorbedRealizedFresh : K .coldGermRealized ∉ known := by key_fresh)
    (absorbedDistinguishedFresh : K .coldGermDistinguished ∉ known := by key_fresh)
    (absorbedSilentFresh : K .coldGermSilent ∉ known := by key_fresh)
    (absorbedRoutedFresh : K .coldGermRouted ∉ known := by key_fresh)
    (absorbedTableFresh : K .coldSameInterfaceTable ∉ known := by key_fresh)
    (absorbedClosedFresh : K .coldBranchClosed ∉ known := by key_fresh)
    (absorbedNeutralFresh : K .coldNeutralEqualLengthTerminal ∉ known := by
      key_fresh)
    (absorbedCanonicalFresh : K .coldCanonicalNeutralConfiguration ∉ known := by
      key_fresh)
    (absorbedGenuineFresh : K .coldGenuineSecondStrand ∉ known := by
      key_fresh)
    (absorbedReplacementSwapFresh : K .coldCanonicalReplacementSwap ∉ known := by
      key_fresh)
    (absorbedReplacementTrivialFresh : K .coldCanonicalReplacementTrivial ∉ known := by
      key_fresh)
    (absorbedTwoStrandSurvivorFresh : K .coldTwoStrandSurvivor ∉ known := by
      key_fresh)
    (absorbedWindowStubFresh : K .coldWindowStubStructure ∉ known := by
      key_fresh)
    (absorbedPairExcludedFresh : K .coldSymmetricPairExcluded ∉ known := by
      key_fresh)
    (locFresh : K .netChargeLocalization ∉ known := by key_fresh)
    (nonNegFresh : K .netChargeNonNegative ∉ known := by key_fresh)
    (negFresh : K .netChargeNegative ∉ known := by key_fresh)
    (supportFresh : K .negativeSupport ∉ known := by key_fresh)
    (typeAFresh : K .typeALowSurplus ∉ known := by key_fresh)
    (typeBFresh : K .typeBHighSurplus ∉ known := by key_fresh)
    -- Type A `[63]`, `[86]`--`[94]` freshness on the same ledger.
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .selection) known]
    (boundedFresh : K .typeABoundedSupport ∉ known := by key_fresh)
    (routingFresh : K .typeAReceiverRouting ∉ known := by key_fresh)
    (saturatedFresh : K .typeASaturatedReceiver ∉ known := by key_fresh)
    (unsaturatedFresh : K .typeAUnsaturatedReceivers ∉ known := by key_fresh)
    (dischargeFresh : K .typeAUnsaturatedDischarge ∉ known := by key_fresh)
    (portFresh : K .typeAPortReturn ∉ known := by key_fresh)
    (powerReturnFresh : K .portPowerReturn ∉ known := by key_fresh)
    (visibleFresh : K .typeAVisibleEntry ∉ known := by key_fresh)
    (excessFresh : K .typeAVisibleFirstExcess ∉ known := by key_fresh)
    [FactKeys.Has (K .returnAvoidance) known]
    (returnFresh : K .typeAExitOneReturn ∉ known := by key_fresh)
    (oneFreeFresh : K .typeAExitOneFree ∉ known := by key_fresh)
    (thetaFresh : K .typeAExitTwoTheta ∉ known := by key_fresh)
    (twoFreeFresh : K .typeAExitTwoFree ∉ known := by key_fresh)
    (collisionFresh : K .typeAExitThreeCollision ∉ known := by key_fresh)
    (threeFreeFresh : K .typeAExitThreeFree ∉ known := by key_fresh)
    (closureFresh : closed ∉ known := by key_fresh)
    -- Type A exits `(4)`--`(7)`, `[101]`--`[109]` (`selectedTypeAExitFourChain`).
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .replacementExclusion) known]
    (entryFresh : K .typeASaturatedExitEntry ∉ known := by key_fresh)
    (descentFresh : K .typeAExitFourFiniteDescent ∉ known := by key_fresh)
    (exitFourFresh : K .typeASaturatedHandoffExitFour ∉ known := by key_fresh)
    (exitFourFreeFresh : K .typeASaturatedHandoffExitFourFree ∉ known := by key_fresh)
    (peeledFresh : K .typeAExitFourPeeled ∉ known := by key_fresh)
    (dischargedFresh : K .typeAExitFourReceiverDischarged ∉ known := by key_fresh)
    (fiveFresh : K .typeAExitFive ∉ known := by key_fresh)
    (fiveFreeFresh : K .typeAExitFiveFree ∉ known := by key_fresh)
    (sixFresh : K .typeAExitSix ∉ known := by key_fresh)
    (sixFreeFresh : K .typeAExitSixFree ∉ known := by key_fresh)
    (sixProperFresh : K .typeAExitSixProper ∉ known := by key_fresh)
    (sixGlobalFresh : K .typeAExitSixGlobal ∉ known := by key_fresh)
    (sevenProducedFresh : K .typeAExitSevenProduced ∉ known := by key_fresh)
    (sevenFreeFresh : K .typeAExitSevenFree ∉ known := by key_fresh)
    (sevenHandoffFresh : K .typeAExitSevenHandoff ∉ known := by key_fresh)
    -- Type B `[64]`+ keys (`selectedTypeBHighSurplusContinuation`).
    [FactKeys.Has (K .tightEndpoint) known]
    (typeBAssignedFresh : K .typeBAssignedSupport ∉ known := by key_fresh)
    (typeBFanEntryFresh : K .typeBFanEntry ∉ known := by key_fresh)
    (normalFormFresh : K .highCentreNormalForm ∉ known := by key_fresh)
    (fanHeavyFresh : K .typeBFanHeavyCentre ∉ known := by key_fresh)
    (fanDegreeFourFresh : K .typeBFanDegreeFourCentres ∉ known := by key_fresh)
    (fanLocalFresh : K .typeBFanLocalDichotomy ∉ known := by key_fresh)
    (fanCompatibilityFresh : K .sameCenterOpenPortCompatibility ∉ known := by
      key_fresh)
    (fanCapFresh : K .fanCertificateCap ∉ known := by key_fresh)
    (decoratedMarkedFresh : K .fanCertificateMarked ∉ known := by key_fresh)
    (decoratedResidualFresh : K .fanCertificateResidual ∉ known := by key_fresh)
    (decoratedCertificateMassFresh : K .fanCertificateResidualMass ∉ known := by key_fresh)
    (decoratedCycleFresh : K .typeBDirectCycle ∉ known := by key_fresh)
    (decoratedFreeFresh : K .typeBDirectCycleFree ∉ known := by key_fresh)
    (decoratedFanEntryFresh : K .typeBFanEntry ∉ known := by key_fresh)
    (decoratedB2ChoiceFresh : K .typeBB2Choice ∉ known := by key_fresh)
    (decoratedB2ObstructionFresh : K .typeBOverlapObstruction ∉ known := by key_fresh)
    (decoratedHybridFresh : K .typeBHybridEntry ∉ known := by key_fresh)
    (decoratedLedgerFresh : K .typeBDisjointLedger ∉ known := by key_fresh)
    (decoratedBridgeMassFresh : K .typeBBridgeMass ∉ known := by key_fresh)
    (decoratedBridgeSublinearFresh : K .typeBBridgeSublinear ∉ known := by key_fresh)
    (decoratedExcludedFresh : K .typeBExcluded ∉ known := by key_fresh)
    (decoratedExclusionResidualFresh : K .typeBExclusionResidual ∉ known := by key_fresh)
    (decoratedExclusionMassFresh : K .typeBExclusionResidualMass ∉ known := by key_fresh)
    (decoratedObstructionMassFresh : K .typeBOverlapObstructionMass ∉ known := by key_fresh)
    (decoratedClosureFresh : closed ∉ known := by key_fresh)
    (fanMarkedFresh : K .fanCertificateMarked ∉ known := by key_fresh)
    (fanResidualFresh : K .fanCertificateResidual ∉ known := by key_fresh)
    -- Type B `[72]`--`[85]` keys on the same exact ledger.
    [FactKeys.Has (K .uncompressible) known]
    (cycleFresh : K .typeBDirectCycle ∉ known := by key_fresh)
    (freeFresh : K .typeBDirectCycleFree ∉ known := by key_fresh)
    (choiceFresh : K .typeBB2Choice ∉ known := by key_fresh)
    (obstructionFresh : K .typeBOverlapObstruction ∉ known := by key_fresh)
    (hybridFresh : K .typeBHybridEntry ∉ known := by key_fresh)
    (ledgerFresh : K .typeBDisjointLedger ∉ known := by key_fresh)
    (bridgeMassFresh : K .typeBBridgeMass ∉ known := by key_fresh)
    (bridgeSublinearFresh : K .typeBBridgeSublinear ∉ known := by key_fresh)
    (excludedFresh : K .typeBExcluded ∉ known := by key_fresh)
    (exclusionResidualFresh : K .typeBExclusionResidual ∉ known := by key_fresh)
    (exclusionMassFresh : K .typeBExclusionResidualMass ∉ known := by key_fresh)
    (obstructionMassFresh : K .typeBOverlapObstructionMass ∉ known := by key_fresh)
    (certificateMassFresh : K .fanCertificateResidualMass ∉ known := by key_fresh)
    (degreeFourProfileFresh : K .typeBFanDegreeFourProfile ∉ known := by key_fresh)
    (triangularCoreFresh : K .triangularFanCore ∉ known := by key_fresh)
    -- `[108]` decorated handoff, `[110]`--`[116]` route 8, `[76]`/`[85]` → `[123]`.
    (decoratedFresh : K .typeBDecoratedAssignedSupport ∉ known := by key_fresh)
    (cubicBaselineFresh : FactKeys.Has (K .cubicBaseline) known := by infer_instance)
    (decoratedHeavyFresh : K .typeBFanHeavyCentre ∉ known := by key_fresh)
    (decoratedDegreeFourFresh : K .typeBFanDegreeFourCentres ∉ known := by key_fresh)
    (decoratedLocalFresh : K .typeBFanLocalDichotomy ∉ known := by key_fresh)
    (decoratedCompatibilityFresh :
      K .sameCenterOpenPortCompatibility ∉ known := by key_fresh)
    (decoratedProfileFresh : K .typeBFanDegreeFourProfile ∉ known := by key_fresh)
    (decoratedTriangularCoreFresh : K .triangularFanCore ∉ known := by key_fresh)
    (profileFresh : K .route8ResidualProfile ∉ known := by key_fresh)
    (squeezeFresh : K .route8GlobalSqueeze ∉ known := by key_fresh)
    (burdenFresh : K .route8BasinBurden ∉ known := by key_fresh)
    (deficitFresh : K .route8LargeBudgetDeficit ∉ known := by key_fresh)
    (deficitFailsFresh : K .route8LargeBudgetDeficitFails ∉ known :=
      by key_fresh)
    (coreFresh : K .route8CarrierCore ∉ known := by key_fresh)
    (trueResidualFresh : K .route8TrueResidual ∉ known := by key_fresh)
    (cutParityFresh : K .route8CarrierCutParity ∉ known := by key_fresh)
    (smallFresh : K .route8SmallCoreEntry ∉ known := by key_fresh)
    (noSmallFresh : K .route8NoSmallCoreEntry ∉ known := by key_fresh)
    (collapseFresh : K .route8SmallCoreCollapse ∉ known := by key_fresh)
    (censusFresh : K .route8Census ∉ known := by key_fresh)
    (twoFresh : K .route8TwoCarrierEntry ∉ known := by key_fresh)
    (noTwoFresh : K .route8NoTwoCarrierEntry ∉ known := by key_fresh)
    (trueEntryFresh : K .route8TrueTwoCarrierEntry ∉ known := by key_fresh)
    (deletionWitnessesFresh : K .route8CarrierDeletionWitnesses ∉ known :=
      by key_fresh)
    (privateBudgetFresh : K .route8PrivateCarrierBudget ∉ known :=
      by key_fresh)
    (noTwoContradictionFresh : K .route8NoTwoCarrierContradiction ∉ known :=
      by key_fresh)
    (terminalNoGoFresh : K .route8TerminalNoGo ∉ known := by key_fresh)
    (unifiedNegativeFresh : K .route8UnifiedNegative ∉ known := by key_fresh)
    (typeAExclusionFresh : K .typeAExclusion ∉ known := by key_fresh)
    (typeBBridgeReductionFresh : K .typeBBridgeReduction ∉ known := by
      key_fresh)
    (piecesClassifiedFresh : K .route8PiecesClassified ∉ known := by key_fresh)
    (sublinearLedgerFresh : K .typeBSublinearLedger ∉ known := by key_fresh)
    (sublinearResidualFresh : K .typeBSublinearResidual ∉ known := by key_fresh)
    (unifiedDeficitFresh : K .route8UnifiedDeficit ∉ known := by key_fresh)
    (quotientFreeFresh : K .route8QuotientFree ∉ known := by key_fresh)
    (quotientResidualFresh : K .route8QuotientResidual ∉ known := by key_fresh)
    (unifiedCensusFresh : K .route8UnifiedEntryCensus ∉ known := by key_fresh)
    (extractedEntryCensusFresh : K .route8ExtractedEntryCensus ∉ known := by
      key_fresh)
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known := by key_fresh)
    (peelingFresh : K .route8PeelingDescent ∉ known := by key_fresh)
    (stageFailedFresh : K .route8StageRateFailed ∉ known := by key_fresh)
    (demandLedgerFresh : K .route8DemandLedger ∉ known := by key_fresh)
    (demandAbsorptionFresh : K .route8DemandAbsorption ∉ known := by key_fresh)
    (openBoundarySaturatedFresh : K .route8OpenBoundarySaturated ∉ known := by key_fresh)
    (demandUnitCountFresh : K .route8DemandUnitCount ∉ known := by key_fresh)
    (windowBlockersFresh : K .route8WindowBlockers ∉ known := by key_fresh)
    (windowShadowSignatureFresh : K .windowShadowSignature ∉ known := by key_fresh)
    (windowShadowTailFresh : K .windowShadowSingletonTail ∉ known := by key_fresh)
    (windowShadowCycleFresh : K .windowShadowHitCycle ∉ known := by key_fresh)
    (windowShadowExcludedFresh : K .windowShadowHitExcluded ∉ known := by key_fresh)
    (demandResidualFresh : K .route8PeeledDemandResidual ∉ known := by key_fresh)
    (unpaidExitFourFresh : K .route8UnpaidExitFourResidual ∉ known := by
      key_fresh)
    (unifiedVisibleFresh : K .route8UnifiedVisibleResidual ∉ known := by
      key_fresh)
    (unifiedVisibleOverloadFresh : K .route8UnifiedVisibleOverload ∉ known := by
      key_fresh)
    (jointBalanceFresh : K .route8JointBalance ∉ known := by
      key_fresh)
    (unifiedTerminalFresh : K .route8TerminalNoGo ∉ known := by key_fresh)
    (globalLocalBridgeFresh : K .typeBGlobalLocalBridge ∉ known := by key_fresh)
    (fanClosedFresh : K .fanClosedPort ∉ known := by key_fresh)
    (compatibleClosureFresh : K .compatiblePairFanClosure ∉ known := by key_fresh)
    (fanClosedRoutingFresh : K .fanClosedPortTypeBRouting ∉ known := by key_fresh)
    (compatibleRoutingFresh : K .compatiblePairTypeBRouting ∉ known := by key_fresh)
    (triangularRoutingFresh : K .triangularPortTypeBRouting ∉ known := by key_fresh)
    (shoulderCompletionFresh : K .triangularShoulderCompletion ∉ known := by key_fresh)
    (triangularPortReturnFresh : K .triangularPortReturn ∉ known := by key_fresh)
    (firstLandingFresh : K .triangularFirstLanding ∉ known := by key_fresh)
    (crossShoulderFresh : K .triangularCrossShoulder ∉ known := by key_fresh)
    (fanSafeFresh : K .typeBFanSafe ∉ known := by key_fresh)
    (silentFourFreeFresh : K .typeASilentExitFourFree ∉ known := by
      key_fresh)
    (silentFiveFreeFresh : K .typeASilentExitFiveFree ∉ known := by
      key_fresh)
    (silentSixFreeFresh : K .typeASilentExitSixFree ∉ known := by
      key_fresh)
    (silentSevenFreeFresh : K .typeASilentExitSevenFree ∉ known := by
      key_fresh)
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
      history (by key_fresh)
  match exactCollisionDichotomy (data := spineData) bridgeless
      (by key_fresh) (by key_fresh) with
  | .right failsHistory =>
      -- `[174]`, `lem:exact-collision-test`: the failed collision rearranges to
      -- the cold-window lower bound `n + s·σ_R ≤ A·(|𝒫_hot| + |𝒫_cold|) + s·σ_W`.
      let absorbed :=
        (absorbedConfigurationResidualRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          failsHistory (by key_fresh)
      let prepared := selectedAbsorbedGermPrerequisites absorbed
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
      -- `[175]`--`[177]`, `lem:absorbed-germ-fan-data`: the absorbed-germ
      -- residual (`selectedAbsorbedGermResidual`).
      exact Or.inr (selectedAbsorbedGermResidual prepared
        (by key_fresh)
        (absorbedPositiveFresh := by key_fresh)
        (absorbedFamilyPositiveFresh := by
          key_fresh)
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
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh) (by key_fresh)
        (by key_fresh) (by key_fresh)
        (by key_fresh) (by key_fresh)
        (absorbedNeutralFresh := by key_fresh)
        (absorbedCanonicalFresh := by key_fresh)
        (absorbedGenuineFresh := by key_fresh)
        (absorbedReplacementSwapFresh := by
          key_fresh)
        (absorbedReplacementTrivialFresh := by
          key_fresh)
        (absorbedTwoStrandSurvivorFresh := by
          key_fresh)
        (absorbedWindowStubFresh := by key_fresh)
        (absorbedPairExcludedFresh := by key_fresh)
        (absorbedTerminalFresh := by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by infer_instance)
        (by key_fresh)
        (absorbedGlobalLocalBridgeFresh := by key_fresh)
        (absorbedFanClosedFresh := by key_fresh)
        (absorbedCompatibleClosureFresh := by key_fresh)
        (absorbedFanClosedRoutingFresh := by key_fresh)
        (absorbedCompatibleRoutingFresh := by key_fresh)
        (absorbedTriangularRoutingFresh := by key_fresh)
        (absorbedShoulderCompletionFresh := by key_fresh)
        (absorbedPortReturnFresh := by key_fresh)
        (absorbedFirstLandingFresh := by key_fresh)
        (absorbedCrossShoulderFresh := by key_fresh)
        (absorbedFanSafeFresh := by key_fresh)
        (absorbedRoutingFresh := by key_fresh)
        (absorbedUnifiedNegativeFresh := by key_fresh)
        (absorbedTypeAExclusionFresh := by key_fresh)
        (absorbedTypeBBridgeReductionFresh := by
          key_fresh)
        (absorbedPiecesClassifiedFresh := by key_fresh)
        (absorbedSublinearLedgerFresh := by key_fresh)
        (absorbedSublinearResidualFresh := by key_fresh)
        (absorbedUnifiedDeficitFresh := by key_fresh)
        (absorbedQuotientFreeFresh := by key_fresh)
        (absorbedQuotientResidualFresh := by key_fresh)
        (absorbedUnifiedCensusFresh := by key_fresh)
        (absorbedUnifiedTrueFresh := by key_fresh)
        (absorbedPeelingFresh := by key_fresh)
        (absorbedStageFailedFresh := by key_fresh)
        (absorbedDemandLedgerFresh := by key_fresh)
        (absorbedDemandAbsorptionFresh := by key_fresh)
        (absorbedOpenBoundarySaturatedFresh := by key_fresh)
        (absorbedDemandUnitCountFresh := by key_fresh)
        (absorbedWindowBlockersFresh := by key_fresh)
        (absorbedWindowShadowSignatureFresh := by key_fresh)
        (absorbedWindowShadowTailFresh := by key_fresh)
        (absorbedWindowShadowCycleFresh := by key_fresh)
        (absorbedWindowShadowExcludedFresh := by key_fresh)
        (absorbedDemandResidualFresh := by key_fresh)
        (absorbedUnpaidExitFourFresh := by key_fresh)
        (absorbedUnifiedVisibleFresh := by key_fresh)
        (absorbedUnifiedVisibleOverloadFresh := by
          key_fresh)
        (absorbedJointBalanceFresh := by key_fresh)
        (absorbedUnifiedTerminalFresh := by key_fresh))
  | .left capped =>
      -- `[58]`: `lem:netcharge-superadd` localizes negative charge to a piece.
      let localized :=
        (netChargeLocalizationRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) spineData).run
          capped (by key_fresh)
      -- `[59]`: `N₀(R) ≥ 0?`
      match netChargeDichotomy (data := spineData) localized
          (by key_fresh) (by key_fresh) with
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
              negativeHistory (by key_fresh)
          -- `[62]`: high-degree surplus? Type A `[63]` / Type B `[64]`.
          match typeSplitDichotomy (data := spineData) support
              (by key_fresh) (by key_fresh) with
          | .left typeAHistory =>
              exact Or.inl (selectedTypeALowSurplusContinuation typeAHistory
                (by key_fresh)
                (by key_fresh) (by key_fresh)
                (by key_fresh) (by key_fresh)
                (by key_fresh)
                (by key_fresh)
                (by key_fresh)
                (by key_fresh)
                (by key_fresh) (by key_fresh)
                (by key_fresh) (by key_fresh)
                (by key_fresh) (by key_fresh)
                (by key_fresh) (by key_fresh)
                (by key_fresh) (by key_fresh)
                (by key_fresh) (by key_fresh)
                (by key_fresh) (by key_fresh)
                (by key_fresh) (by key_fresh)
                (by key_fresh) (by key_fresh)
                (by key_fresh)
                (by key_fresh) (by key_fresh)
                (by key_fresh)
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
                (by key_fresh)
                (by key_fresh)
                (by key_fresh)
                (by key_fresh)
                (by key_fresh)
                (by key_fresh)
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
                (silentSevenFreeFresh := by key_fresh))
          | .right typeBHistory =>
              exact Or.inl (selectedTypeBHighSurplusContinuation typeBHistory
                (by key_fresh)
                (by infer_instance)
                (by key_fresh) (by key_fresh) (by key_fresh)
                (by key_fresh) (by key_fresh)
                (by key_fresh)
                (by key_fresh)
                (by key_fresh)
                (by key_fresh) (by key_fresh)
                (by key_fresh) (by key_fresh)
                (by key_fresh) (by key_fresh)
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
                (by key_fresh)
                (by key_fresh)
                (by key_fresh)
                (by key_fresh)
                (by key_fresh)
                (by key_fresh)
                (by key_fresh)
                (by key_fresh)
                (by key_fresh)
                (unpaidExitFourFresh := by key_fresh)
                (unifiedVisibleFresh := by key_fresh)
                (unifiedVisibleOverloadFresh := by
                  key_fresh)
                (jointBalanceFresh := by key_fresh)
                (unifiedTerminalFresh := by key_fresh)
                (by key_fresh) (by key_fresh)
                (by key_fresh) (by key_fresh)
                (by key_fresh)
                (by key_fresh)
                (by key_fresh)
                (fanClosedFresh := by key_fresh)
                (compatibleClosureFresh := by key_fresh)
                (fanClosedRoutingFresh := by key_fresh)
                (compatibleRoutingFresh := by key_fresh)
                (shoulderCompletionFresh := by key_fresh)
                (portReturnFresh := by key_fresh)
                (firstLandingFresh := by key_fresh)
                (crossShoulderFresh := by key_fresh)
                (triangularRoutingFresh := by key_fresh)
                (globalLocalBridgeFresh := by key_fresh))

end HypostructureErdos64EG
