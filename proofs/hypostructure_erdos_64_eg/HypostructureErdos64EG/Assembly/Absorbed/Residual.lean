import Hypostructure.Graph.Strategy.ColdCorridorRows
import HypostructureErdos64EG.Assembly.Absorbed.Boundary
import HypostructureErdos64EG.Assembly.Absorbed.FanCharge

/-!
# Assembly: Absorbed / Residual

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

noncomputable def selectedAbsorbedGermResidual
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .slackIndependent) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .absorbedConfigurationResidual) known]
    [FactKeys.Has (K .coldGermCandidates) known]
    [FactKeys.Has (K .coldGermExtraction) known]
    [FactKeys.Has (K .coldHandoffTransfer) known]
    [FactKeys.Has (K .coldCorridorState) known]
    [FactKeys.Has (K .denseColdCorridorsTerminal) known]
    [FactKeys.Has (K .bridgeless) known]
    (absorbedSplitFresh : K .absorbedGermSplit ∉ known := by simp [K_eq_iff])
    (absorbedPositiveFresh : K .coldPositiveGerm ∉ known := by simp [K_eq_iff])
    (absorbedFamilyPositiveFresh : K .coldGermFamilyPositive ∉ known := by
      simp [K_eq_iff])
    (absorbedFanFresh : K .absorbedGermFanData ∉ known := by simp [K_eq_iff])
    (absorbedFanEntryFresh : K .typeBFanEntry ∉ known := by simp [K_eq_iff])
    (absorbedNormalFormFresh : K .highCentreNormalForm ∉ known := by simp [K_eq_iff])
    (absorbedHeavyFresh : K .typeBFanHeavyCentre ∉ known := by simp [K_eq_iff])
    (absorbedDegreeFourFresh : K .typeBFanDegreeFourCentres ∉ known := by simp [K_eq_iff])
    (absorbedCompatibilityFresh : K .sameCenterOpenPortCompatibility ∉ known := by
      simp [K_eq_iff])
    (absorbedLocalFresh : K .typeBFanLocalDichotomy ∉ known := by simp [K_eq_iff])
    (absorbedProfileFresh : K .typeBFanDegreeFourProfile ∉ known := by simp [K_eq_iff])
    (absorbedTriangularFresh : K .triangularFanCore ∉ known := by simp [K_eq_iff])
    (absorbedCapFresh : K .fanCertificateCap ∉ known := by simp [K_eq_iff])
    (absorbedMarkedFresh : K .fanCertificateMarked ∉ known := by simp [K_eq_iff])
    (absorbedResidualFresh : K .fanCertificateResidual ∉ known := by simp [K_eq_iff])
    (absorbedCertificateMassFresh : K .fanCertificateResidualMass ∉ known := by
      simp [K_eq_iff])
    (absorbedCycleFresh : K .typeBDirectCycle ∉ known := by simp [K_eq_iff])
    (absorbedFreeFresh : K .typeBDirectCycleFree ∉ known := by simp [K_eq_iff])
    (absorbedChoiceFresh : K .typeBB2Choice ∉ known := by simp [K_eq_iff])
    (absorbedObstructionFresh : K .typeBOverlapObstruction ∉ known := by
      simp [K_eq_iff])
    (absorbedHybridFresh : K .typeBHybridEntry ∉ known := by simp [K_eq_iff])
    (absorbedLedgerFresh : K .typeBDisjointLedger ∉ known := by simp [K_eq_iff])
    (absorbedExcludedFresh : K .typeBExcluded ∉ known := by simp [K_eq_iff])
    (absorbedExclusionResidualFresh : K .typeBExclusionResidual ∉ known := by
      simp [K_eq_iff])
    (absorbedExclusionMassFresh : K .typeBExclusionResidualMass ∉ known := by
      simp [K_eq_iff])
    (absorbedObstructionMassFresh : K .typeBOverlapObstructionMass ∉ known := by
      simp [K_eq_iff])
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
    (absorbedTerminalFresh : closed ∉ known := by simp [K_eq_iff])
    (absorbedBridgeMassFresh : K .typeBBridgeMass ∉ known := by simp [K_eq_iff])
    (absorbedBridgeSublinearFresh : K .typeBBridgeSublinear ∉ known := by
      simp [K_eq_iff])
    (absorbedCubicFresh : FactKeys.Has (K .cubicBaseline) known := by infer_instance)
    (absorbedExtractedFresh : K .route8ExtractedEntryCensus ∉ known := by
      simp [K_eq_iff])
    (absorbedGlobalLocalBridgeFresh : K .typeBGlobalLocalBridge ∉ known := by simp [K_eq_iff])
    (absorbedFanClosedFresh : K .fanClosedPort ∉ known := by simp [K_eq_iff])
    (absorbedCompatibleClosureFresh : K .compatiblePairFanClosure ∉ known := by simp [K_eq_iff])
    (absorbedFanClosedRoutingFresh : K .fanClosedPortTypeBRouting ∉ known := by simp [K_eq_iff])
    (absorbedCompatibleRoutingFresh : K .compatiblePairTypeBRouting ∉ known := by simp [K_eq_iff])
    (absorbedTriangularRoutingFresh : K .triangularPortTypeBRouting ∉ known := by simp [K_eq_iff])
    (absorbedShoulderCompletionFresh : K .triangularShoulderCompletion ∉ known := by simp [K_eq_iff])
    (absorbedPortReturnFresh : K .triangularPortReturn ∉ known := by simp [K_eq_iff])
    (absorbedFirstLandingFresh : K .triangularFirstLanding ∉ known := by simp [K_eq_iff])
    (absorbedCrossShoulderFresh : K .triangularCrossShoulder ∉ known := by simp [K_eq_iff])
    (absorbedFanSafeFresh : K .typeBFanSafe ∉ known := by simp [K_eq_iff])
    (absorbedRoutingFresh : K .typeAReceiverRouting ∉ known := by simp [K_eq_iff])
    (absorbedUnifiedNegativeFresh : K .route8UnifiedNegative ∉ known := by simp [K_eq_iff])
    (absorbedTypeAExclusionFresh : K .typeAExclusion ∉ known := by simp [K_eq_iff])
    (absorbedTypeBBridgeReductionFresh : K .typeBBridgeReduction ∉ known := by
      simp [K_eq_iff])
    (absorbedPiecesClassifiedFresh : K .route8PiecesClassified ∉ known := by
      simp [K_eq_iff])
    (absorbedSublinearLedgerFresh : K .typeBSublinearLedger ∉ known := by simp [K_eq_iff])
    (absorbedSublinearResidualFresh : K .typeBSublinearResidual ∉ known := by simp [K_eq_iff])
    (absorbedUnifiedDeficitFresh : K .route8UnifiedDeficit ∉ known := by simp [K_eq_iff])
    (absorbedQuotientFreeFresh : K .route8QuotientFree ∉ known := by simp [K_eq_iff])
    (absorbedQuotientResidualFresh : K .route8QuotientResidual ∉ known := by simp [K_eq_iff])
    (absorbedUnifiedCensusFresh : K .route8UnifiedEntryCensus ∉ known := by simp [K_eq_iff])
    (absorbedUnifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known := by
      simp [K_eq_iff])
    (absorbedPeelingFresh : K .route8PeelingDescent ∉ known := by simp [K_eq_iff])
    (absorbedStageFailedFresh : K .route8StageRateFailed ∉ known := by simp [K_eq_iff])
    (absorbedDemandLedgerFresh : K .route8DemandLedger ∉ known := by simp [K_eq_iff])
    (absorbedDemandAbsorptionFresh : K .route8DemandAbsorption ∉ known := by simp [K_eq_iff])
    (absorbedOpenBoundarySaturatedFresh : K .route8OpenBoundarySaturated ∉ known := by simp [K_eq_iff])
    (absorbedDemandUnitCountFresh : K .route8DemandUnitCount ∉ known := by simp [K_eq_iff])
    (absorbedWindowBlockersFresh : K .route8WindowBlockers ∉ known := by simp [K_eq_iff])
    (absorbedWindowShadowSignatureFresh : K .windowShadowSignature ∉ known := by simp [K_eq_iff])
    (absorbedWindowShadowTailFresh : K .windowShadowSingletonTail ∉ known := by simp [K_eq_iff])
    (absorbedWindowShadowCycleFresh : K .windowShadowHitCycle ∉ known := by simp [K_eq_iff])
    (absorbedWindowShadowExcludedFresh : K .windowShadowHitExcluded ∉ known := by simp [K_eq_iff])
    (absorbedDemandResidualFresh : K .route8PeeledDemandResidual ∉ known := by simp [K_eq_iff])
    (absorbedUnpaidExitFourFresh : K .route8UnpaidExitFourResidual ∉ known := by
      simp [K_eq_iff])
    (absorbedUnifiedVisibleFresh : K .route8UnifiedVisibleResidual ∉ known := by
      simp [K_eq_iff])
    (absorbedUnifiedVisibleOverloadFresh :
        K .route8UnifiedVisibleOverload ∉ known := by simp [K_eq_iff])
    (absorbedJointBalanceFresh : K .route8JointBalance ∉ known := by
      simp [K_eq_iff])
    (absorbedUnifiedTerminalFresh : K .route8TerminalNoGo ∉ known := by simp [K_eq_iff])
   :
    SelectedAbsorbedGermBoundary selected := by
  letI := absorbedCubicFresh
  let _cubicBaseline := (history.get (K .cubicBaseline)).down
  let _absorbed := (history.get (K .absorbedConfigurationResidual)).down
  let _candidates := (history.get (K .coldGermCandidates)).down
  -- `[175]`, `lem:absorbed-germ-fan-data`: the per-half-edge dichotomy — every
  -- selected corridor's first-failure support is subcubic (a charged candidate
  -- germ, `[176]`) or meets a heavy centre whose neighbours sit at the threshold
  -- by node `[10]` (`[177]`).
  let split :=
    (absorbedGermSplitRow (data := spineData)).run history
      (by simp [K_eq_iff, absorbedSplitFresh])
  -- The exhaustive object-level reading of `[175]`: is the subcubic occurrence
  -- class nonempty?  This decision records only that branch predicate.
  match absorbedGermDichotomy (data := spineData) split
      (by simp [K_eq_iff, absorbedPositiveFresh])
      (by simp [K_eq_iff, absorbedFanFresh]) with
  | .left positiveHistory =>
      -- `[176]`: a genuine (F5) germ family; routed exactly as `[154]`--`[157]`,
      -- then the neutral-germ symmetry split of `[163]`.  The candidate family
      -- is obtained by running its registered node-`[153]` owner on this exact
      -- ledger; `[175]` does not reconstruct its count or overlap proof.
      let positiveFamily :=
        (absorbedGermFamilyPositiveRow (data := spineData)).run positiveHistory
          (by simp [K_eq_iff, absorbedFamilyPositiveFresh])
      let neutralConfiguration :=
        (neutralEqualLengthTerminalRow (data := spineData)).run positiveFamily
          (by simp [K_eq_iff, absorbedNeutralFresh])
      let trichotomy :=
        (coldGermTrichotomyRow (data := spineData)).run neutralConfiguration
          (by simp [K_eq_iff, absorbedRealizedFresh, absorbedDistinguishedFresh,
            absorbedSilentFresh, absorbedRoutedFresh])
      let table :=
        (coldSameInterfaceTableRow (data := spineData)).run trichotomy
          (by simp [K_eq_iff, absorbedTableFresh])
      let closed :=
        (coldBranchClosedRow (data := spineData)).run table
          (by simp [K_eq_iff, absorbedClosedFresh])
      match neutralGermSymmetryDichotomy (data := spineData) closed
          (by simp [K_eq_iff, absorbedCanonicalFresh])
          (by simp [K_eq_iff, absorbedGenuineFresh]) with
      | .left canonicalHistory =>
          -- `[165]`--`[166]`: the non-realized representative is exchanged in
          -- the retained context, and refined minimality publishes `Q = E`.
          -- This is the local manuscript consumer only; the dense-only
          -- blocked-class continuation `[169]` is not entered here.
          let swapped :=
            (canonicalReplacementSwapRow (data := spineData)).run
              canonicalHistory
              (by simp [K_eq_iff, absorbedReplacementSwapFresh])
          let trivial :=
            (canonicalReplacementTrivialRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              swapped
              (by simp [K_eq_iff, absorbedReplacementTrivialFresh])
          -- `[176]` has now consumed every cited cold/symmetry fact.  Because
          -- `[175]` is per incidence, append `[177]`'s aggregate package and
          -- fan entry on this same ledger so a mixed family retains `Q = E`
          -- together with the Type-B charge of its complement.
          let fanData :=
            (absorbedGermFanDataRow (data := spineData)).run trivial
              (by simp [K_eq_iff, absorbedFanFresh])
          let fanEntry :=
            (absorbedGermFanEnvelopeRow (data := spineData)).run fanData
              (by simp [K_eq_iff, absorbedFanEntryFresh])
          exact Or.inl (Assembly.Internal.selectedAbsorbedFanChargeContinuation fanEntry
            (by simp [K_eq_iff, absorbedNormalFormFresh])
            (by simp [K_eq_iff, absorbedHeavyFresh])
            (by simp [K_eq_iff, absorbedDegreeFourFresh])
            (by simp [K_eq_iff, absorbedCompatibilityFresh])
            (by simp [K_eq_iff, absorbedLocalFresh])
            (by simp [K_eq_iff, absorbedProfileFresh])
            (by simp [K_eq_iff, absorbedTriangularFresh])
            (by simp [K_eq_iff, absorbedCapFresh])
            (by simp [K_eq_iff, absorbedMarkedFresh])
            (by simp [K_eq_iff, absorbedResidualFresh])
            (by simp [K_eq_iff, absorbedCertificateMassFresh])
            (by simp [K_eq_iff, absorbedCycleFresh])
            (by simp [K_eq_iff, absorbedFreeFresh])
            (by simp [K_eq_iff, absorbedChoiceFresh])
            (by simp [K_eq_iff, absorbedObstructionFresh])
            (by simp [K_eq_iff, absorbedGlobalLocalBridgeFresh])
            (by simp [K_eq_iff, absorbedHybridFresh])
            (by simp [K_eq_iff, absorbedLedgerFresh])
            (by simp [K_eq_iff, absorbedExcludedFresh])
            (by simp [K_eq_iff, absorbedExclusionResidualFresh])
            (by simp [K_eq_iff, absorbedExclusionMassFresh])
            (by simp [K_eq_iff, absorbedObstructionMassFresh])
            (by simp [K_eq_iff, absorbedFanClosedFresh])
            (by simp [K_eq_iff, absorbedCompatibleClosureFresh])
            (by simp [K_eq_iff, absorbedFanClosedRoutingFresh])
            (by simp [K_eq_iff, absorbedCompatibleRoutingFresh])
            (by simp [K_eq_iff, absorbedTriangularRoutingFresh])
            (by simp [K_eq_iff, absorbedShoulderCompletionFresh])
            (by simp [K_eq_iff, absorbedPortReturnFresh])
            (by simp [K_eq_iff, absorbedFirstLandingFresh])
            (by simp [K_eq_iff, absorbedCrossShoulderFresh])
            (by simp [K_eq_iff, absorbedFanSafeFresh])
            (by simp [K_eq_iff, absorbedBridgeMassFresh])
            (by simp [K_eq_iff, absorbedBridgeSublinearFresh])
            (by infer_instance)
            (by simp [K_eq_iff, absorbedExtractedFresh])
            (routingFresh := by simp [K_eq_iff, absorbedRoutingFresh])
            (unifiedNegativeFresh := by simp [K_eq_iff, absorbedUnifiedNegativeFresh])
            (typeAExclusionFresh := by simp [K_eq_iff, absorbedTypeAExclusionFresh])
            (typeBBridgeReductionFresh := by
              simp [K_eq_iff, absorbedTypeBBridgeReductionFresh])
            (piecesClassifiedFresh := by simp [K_eq_iff, absorbedPiecesClassifiedFresh])
            (sublinearLedgerFresh := by simp [K_eq_iff, absorbedSublinearLedgerFresh])
            (sublinearResidualFresh := by simp [K_eq_iff, absorbedSublinearResidualFresh])
            (unifiedDeficitFresh := by simp [K_eq_iff, absorbedUnifiedDeficitFresh])
            (quotientFreeFresh := by simp [K_eq_iff, absorbedQuotientFreeFresh])
            (quotientResidualFresh := by simp [K_eq_iff, absorbedQuotientResidualFresh])
            (unifiedCensusFresh := by simp [K_eq_iff, absorbedUnifiedCensusFresh])
            (unifiedTrueFresh := by simp [K_eq_iff, absorbedUnifiedTrueFresh])
            (peelingFresh := by simp [K_eq_iff, absorbedPeelingFresh])
            (stageFailedFresh := by simp [K_eq_iff, absorbedStageFailedFresh])
            (demandLedgerFresh := by simp [K_eq_iff, absorbedDemandLedgerFresh])
            (demandAbsorptionFresh := by simp [K_eq_iff, absorbedDemandAbsorptionFresh])
            (openBoundarySaturatedFresh := by simp [K_eq_iff, absorbedOpenBoundarySaturatedFresh])
            (demandUnitCountFresh := by simp [K_eq_iff, absorbedDemandUnitCountFresh])
            (windowBlockersFresh := by simp [K_eq_iff, absorbedWindowBlockersFresh])
            (windowShadowSignatureFresh := by simp [K_eq_iff, absorbedWindowShadowSignatureFresh])
            (windowShadowTailFresh := by simp [K_eq_iff, absorbedWindowShadowTailFresh])
            (windowShadowCycleFresh := by simp [K_eq_iff, absorbedWindowShadowCycleFresh])
            (windowShadowExcludedFresh := by simp [K_eq_iff, absorbedWindowShadowExcludedFresh])
            (demandResidualFresh := by simp [K_eq_iff, absorbedDemandResidualFresh])
            (unpaidExitFourFresh := by simp [K_eq_iff, absorbedUnpaidExitFourFresh])
            (unifiedVisibleFresh := by simp [K_eq_iff, absorbedUnifiedVisibleFresh])
            (unifiedVisibleOverloadFresh := by
              simp [K_eq_iff, absorbedUnifiedVisibleOverloadFresh])
            (jointBalanceFresh := by simp [K_eq_iff, absorbedJointBalanceFresh])
            (unifiedTerminalFresh := by simp [K_eq_iff, absorbedUnifiedTerminalFresh]))
      | .right genuineHistory =>
          -- `[167]`--`[168]`: the graph-realized second strand either gives
          -- one of the two prescribed dyadic cycles inside its owner or lands
          -- in the finite survivor list, where the retained interior stub is
          -- incompatible with the two endpoint attachments.
          let survivor :=
            (twoStrandSurvivorRow (data := spineData)).run genuineHistory
              (by simp [K_eq_iff, absorbedTwoStrandSurvivorFresh])
          let stubbed :=
            (coldWindowStubStructureRow (data := spineData)).run survivor
              (by simp [K_eq_iff, absorbedWindowStubFresh])
          let impossible :=
            (symmetricPairEndpointExclusionRow (data := spineData)).runAndCloseIncompatible
              stubbed (K .coldTwoStrandSurvivor) (K .coldSymmetricPairExcluded)
              (by simp [K_eq_iff, absorbedPairExcludedFresh])
              (by simp [K_eq_iff, absorbedTerminalFresh])
          exact (impossible.elimClosed (by infer_instance)).elim
  | .right absorbedHistory =>
      -- `[177]`, `lem:absorbed-germ-fan-data` (ii): at every heavy centre of a
      -- selected corridor, the corridor's two incidences and tails are decorated
      -- handoff fan data (`def:decorated-fan-envelope`,
      -- `lem:typeA-high-degree-handoff`), published on the literal residual.
      let fanEntry :=
        (absorbedGermFanEnvelopeRow (data := spineData)).run absorbedHistory
          (by simp [K_eq_iff, absorbedFanEntryFresh])
      -- This is exactly the drawn `[177] → [65]` edge, followed by the common
      -- registered charge tail.  On this no-candidate arm the complement is
      -- the whole selected family.
      exact Or.inl (Assembly.Internal.selectedAbsorbedFanChargeContinuation fanEntry
        (by simp [K_eq_iff, absorbedNormalFormFresh])
        (by simp [K_eq_iff, absorbedHeavyFresh])
        (by simp [K_eq_iff, absorbedDegreeFourFresh])
        (by simp [K_eq_iff, absorbedCompatibilityFresh])
        (by simp [K_eq_iff, absorbedLocalFresh])
        (by simp [K_eq_iff, absorbedProfileFresh])
        (by simp [K_eq_iff, absorbedTriangularFresh])
        (by simp [K_eq_iff, absorbedCapFresh])
        (by simp [K_eq_iff, absorbedMarkedFresh])
        (by simp [K_eq_iff, absorbedResidualFresh])
        (by simp [K_eq_iff, absorbedCertificateMassFresh])
        (by simp [K_eq_iff, absorbedCycleFresh])
        (by simp [K_eq_iff, absorbedFreeFresh])
        (by simp [K_eq_iff, absorbedChoiceFresh])
        (by simp [K_eq_iff, absorbedObstructionFresh])
        (by simp [K_eq_iff, absorbedGlobalLocalBridgeFresh])
        (by simp [K_eq_iff, absorbedHybridFresh])
        (by simp [K_eq_iff, absorbedLedgerFresh])
        (by simp [K_eq_iff, absorbedExcludedFresh])
        (by simp [K_eq_iff, absorbedExclusionResidualFresh])
        (by simp [K_eq_iff, absorbedExclusionMassFresh])
        (by simp [K_eq_iff, absorbedObstructionMassFresh])
        (by simp [K_eq_iff, absorbedFanClosedFresh])
        (by simp [K_eq_iff, absorbedCompatibleClosureFresh])
        (by simp [K_eq_iff, absorbedFanClosedRoutingFresh])
        (by simp [K_eq_iff, absorbedCompatibleRoutingFresh])
        (by simp [K_eq_iff, absorbedTriangularRoutingFresh])
        (by simp [K_eq_iff, absorbedShoulderCompletionFresh])
        (by simp [K_eq_iff, absorbedPortReturnFresh])
        (by simp [K_eq_iff, absorbedFirstLandingFresh])
        (by simp [K_eq_iff, absorbedCrossShoulderFresh])
        (by simp [K_eq_iff, absorbedFanSafeFresh])
        (by simp [K_eq_iff, absorbedBridgeMassFresh])
        (by simp [K_eq_iff, absorbedBridgeSublinearFresh])
        (by infer_instance)
        (by simp [K_eq_iff, absorbedExtractedFresh])
        (routingFresh := by simp [K_eq_iff, absorbedRoutingFresh])
        (unifiedNegativeFresh := by simp [K_eq_iff, absorbedUnifiedNegativeFresh])
        (typeAExclusionFresh := by simp [K_eq_iff, absorbedTypeAExclusionFresh])
        (typeBBridgeReductionFresh := by
          simp [K_eq_iff, absorbedTypeBBridgeReductionFresh])
        (piecesClassifiedFresh := by simp [K_eq_iff, absorbedPiecesClassifiedFresh])
        (sublinearLedgerFresh := by simp [K_eq_iff, absorbedSublinearLedgerFresh])
        (sublinearResidualFresh := by simp [K_eq_iff, absorbedSublinearResidualFresh])
        (unifiedDeficitFresh := by simp [K_eq_iff, absorbedUnifiedDeficitFresh])
        (quotientFreeFresh := by simp [K_eq_iff, absorbedQuotientFreeFresh])
        (quotientResidualFresh := by simp [K_eq_iff, absorbedQuotientResidualFresh])
        (unifiedCensusFresh := by simp [K_eq_iff, absorbedUnifiedCensusFresh])
        (unifiedTrueFresh := by simp [K_eq_iff, absorbedUnifiedTrueFresh])
        (peelingFresh := by simp [K_eq_iff, absorbedPeelingFresh])
        (stageFailedFresh := by simp [K_eq_iff, absorbedStageFailedFresh])
        (demandLedgerFresh := by simp [K_eq_iff, absorbedDemandLedgerFresh])
        (demandAbsorptionFresh := by simp [K_eq_iff, absorbedDemandAbsorptionFresh])
        (openBoundarySaturatedFresh := by simp [K_eq_iff, absorbedOpenBoundarySaturatedFresh])
        (demandUnitCountFresh := by simp [K_eq_iff, absorbedDemandUnitCountFresh])
        (windowBlockersFresh := by simp [K_eq_iff, absorbedWindowBlockersFresh])
        (windowShadowSignatureFresh := by simp [K_eq_iff, absorbedWindowShadowSignatureFresh])
        (windowShadowTailFresh := by simp [K_eq_iff, absorbedWindowShadowTailFresh])
        (windowShadowCycleFresh := by simp [K_eq_iff, absorbedWindowShadowCycleFresh])
        (windowShadowExcludedFresh := by simp [K_eq_iff, absorbedWindowShadowExcludedFresh])
        (demandResidualFresh := by simp [K_eq_iff, absorbedDemandResidualFresh])
        (unpaidExitFourFresh := by simp [K_eq_iff, absorbedUnpaidExitFourFresh])
        (unifiedVisibleFresh := by simp [K_eq_iff, absorbedUnifiedVisibleFresh])
        (unifiedVisibleOverloadFresh := by
          simp [K_eq_iff, absorbedUnifiedVisibleOverloadFresh])
        (jointBalanceFresh := by simp [K_eq_iff, absorbedJointBalanceFresh])
        (unifiedTerminalFresh := by simp [K_eq_iff, absorbedUnifiedTerminalFresh]))

end HypostructureErdos64EG
