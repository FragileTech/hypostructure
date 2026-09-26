import Hypostructure.Graph.Strategy.ColdCorridorRows.AbsorbedGerm
import Hypostructure.Graph.Strategy.ColdCorridorRows.AbsorbedGermFanEnvelope
import Hypostructure.Graph.Strategy.ColdCorridorRows.CanonicalReplacement
import Hypostructure.Graph.Strategy.ColdCorridorRows.ColdFamilyClosure
import Hypostructure.Graph.Strategy.ColdCorridorRows.GermTrichotomy
import Hypostructure.Graph.Strategy.ColdCorridorRows.NeutralTerminal
import Hypostructure.Graph.Strategy.ColdCorridorRows.TwoStrand
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
    (absorbedSplitFresh : K .absorbedGermSplit ∉ known := by key_fresh)
    (absorbedPositiveFresh : K .coldPositiveGerm ∉ known := by key_fresh)
    (absorbedFamilyPositiveFresh : K .coldGermFamilyPositive ∉ known := by
      key_fresh)
    (absorbedFanFresh : K .absorbedGermFanData ∉ known := by key_fresh)
    (absorbedFanEntryFresh : K .typeBFanEntry ∉ known := by key_fresh)
    (absorbedNormalFormFresh : K .highCentreNormalForm ∉ known := by key_fresh)
    (absorbedHeavyFresh : K .typeBFanHeavyCentre ∉ known := by key_fresh)
    (absorbedDegreeFourFresh : K .typeBFanDegreeFourCentres ∉ known := by key_fresh)
    (absorbedCompatibilityFresh : K .sameCenterOpenPortCompatibility ∉ known := by
      key_fresh)
    (absorbedLocalFresh : K .typeBFanLocalDichotomy ∉ known := by key_fresh)
    (absorbedProfileFresh : K .typeBFanDegreeFourProfile ∉ known := by key_fresh)
    (absorbedTriangularFresh : K .triangularFanCore ∉ known := by key_fresh)
    (absorbedCapFresh : K .fanCertificateCap ∉ known := by key_fresh)
    (absorbedMarkedFresh : K .fanCertificateMarked ∉ known := by key_fresh)
    (absorbedResidualFresh : K .fanCertificateResidual ∉ known := by key_fresh)
    (absorbedCertificateMassFresh : K .fanCertificateResidualMass ∉ known := by
      key_fresh)
    (absorbedCycleFresh : K .typeBDirectCycle ∉ known := by key_fresh)
    (absorbedFreeFresh : K .typeBDirectCycleFree ∉ known := by key_fresh)
    (absorbedChoiceFresh : K .typeBB2Choice ∉ known := by key_fresh)
    (absorbedObstructionFresh : K .typeBOverlapObstruction ∉ known := by
      key_fresh)
    (absorbedHybridFresh : K .typeBHybridEntry ∉ known := by key_fresh)
    (absorbedLedgerFresh : K .typeBDisjointLedger ∉ known := by key_fresh)
    (absorbedExcludedFresh : K .typeBExcluded ∉ known := by key_fresh)
    (absorbedExclusionResidualFresh : K .typeBExclusionResidual ∉ known := by
      key_fresh)
    (absorbedExclusionMassFresh : K .typeBExclusionResidualMass ∉ known := by
      key_fresh)
    (absorbedObstructionMassFresh : K .typeBOverlapObstructionMass ∉ known := by
      key_fresh)
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
    (absorbedTerminalFresh : closed ∉ known := by key_fresh)
    (absorbedBridgeMassFresh : K .typeBBridgeMass ∉ known := by key_fresh)
    (absorbedBridgeSublinearFresh : K .typeBBridgeSublinear ∉ known := by
      key_fresh)
    (absorbedCubicFresh : FactKeys.Has (K .cubicBaseline) known := by infer_instance)
    (absorbedExtractedFresh : K .route8ExtractedEntryCensus ∉ known := by
      key_fresh)
    (absorbedGlobalLocalBridgeFresh : K .typeBGlobalLocalBridge ∉ known := by key_fresh)
    (absorbedFanClosedFresh : K .fanClosedPort ∉ known := by key_fresh)
    (absorbedCompatibleClosureFresh : K .compatiblePairFanClosure ∉ known := by key_fresh)
    (absorbedFanClosedRoutingFresh : K .fanClosedPortTypeBRouting ∉ known := by key_fresh)
    (absorbedCompatibleRoutingFresh : K .compatiblePairTypeBRouting ∉ known := by key_fresh)
    (absorbedTriangularRoutingFresh : K .triangularPortTypeBRouting ∉ known := by key_fresh)
    (absorbedShoulderCompletionFresh : K .triangularShoulderCompletion ∉ known := by key_fresh)
    (absorbedPortReturnFresh : K .triangularPortReturn ∉ known := by key_fresh)
    (absorbedFirstLandingFresh : K .triangularFirstLanding ∉ known := by key_fresh)
    (absorbedCrossShoulderFresh : K .triangularCrossShoulder ∉ known := by key_fresh)
    (absorbedFanSafeFresh : K .typeBFanSafe ∉ known := by key_fresh)
    (absorbedRoutingFresh : K .typeAReceiverRouting ∉ known := by key_fresh)
    (absorbedUnifiedNegativeFresh : K .route8UnifiedNegative ∉ known := by key_fresh)
    (absorbedTypeAExclusionFresh : K .typeAExclusion ∉ known := by key_fresh)
    (absorbedTypeBBridgeReductionFresh : K .typeBBridgeReduction ∉ known := by
      key_fresh)
    (absorbedPiecesClassifiedFresh : K .route8PiecesClassified ∉ known := by
      key_fresh)
    (absorbedSublinearLedgerFresh : K .typeBSublinearLedger ∉ known := by key_fresh)
    (absorbedSublinearResidualFresh : K .typeBSublinearResidual ∉ known := by key_fresh)
    (absorbedUnifiedDeficitFresh : K .route8UnifiedDeficit ∉ known := by key_fresh)
    (absorbedQuotientFreeFresh : K .route8QuotientFree ∉ known := by key_fresh)
    (absorbedQuotientResidualFresh : K .route8QuotientResidual ∉ known := by key_fresh)
    (absorbedUnifiedCensusFresh : K .route8UnifiedEntryCensus ∉ known := by key_fresh)
    (absorbedUnifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known := by
      key_fresh)
    (absorbedPeelingFresh : K .route8PeelingDescent ∉ known := by key_fresh)
    (absorbedStageFailedFresh : K .route8StageRateFailed ∉ known := by key_fresh)
    (absorbedDemandLedgerFresh : K .route8DemandLedger ∉ known := by key_fresh)
    (absorbedDemandAbsorptionFresh : K .route8DemandAbsorption ∉ known := by key_fresh)
    (absorbedOpenBoundarySaturatedFresh : K .route8OpenBoundarySaturated ∉ known := by key_fresh)
    (absorbedDemandUnitCountFresh : K .route8DemandUnitCount ∉ known := by key_fresh)
    (absorbedWindowBlockersFresh : K .route8WindowBlockers ∉ known := by key_fresh)
    (absorbedWindowShadowSignatureFresh : K .windowShadowSignature ∉ known := by key_fresh)
    (absorbedWindowShadowTailFresh : K .windowShadowSingletonTail ∉ known := by key_fresh)
    (absorbedWindowShadowCycleFresh : K .windowShadowHitCycle ∉ known := by key_fresh)
    (absorbedWindowShadowExcludedFresh : K .windowShadowHitExcluded ∉ known := by key_fresh)
    (absorbedDemandResidualFresh : K .route8PeeledDemandResidual ∉ known := by key_fresh)
    (absorbedUnpaidExitFourFresh : K .route8UnpaidExitFourResidual ∉ known := by
      key_fresh)
    (absorbedUnifiedVisibleFresh : K .route8UnifiedVisibleResidual ∉ known := by
      key_fresh)
    (absorbedUnifiedVisibleOverloadFresh :
        K .route8UnifiedVisibleOverload ∉ known := by key_fresh)
    (absorbedJointBalanceFresh : K .route8JointBalance ∉ known := by
      key_fresh)
    (absorbedUnifiedTerminalFresh : K .route8TerminalNoGo ∉ known := by key_fresh)
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
      (by key_fresh)
  -- The exhaustive object-level reading of `[175]`: is the subcubic occurrence
  -- class nonempty?  This decision records only that branch predicate.
  match absorbedGermDichotomy (data := spineData) split
      (by key_fresh)
      (by key_fresh) with
  | .left positiveHistory =>
      -- `[176]`: a genuine (F5) germ family; routed exactly as `[154]`--`[157]`,
      -- then the neutral-germ symmetry split of `[163]`.  The candidate family
      -- is obtained by running its registered node-`[153]` owner on this exact
      -- ledger; `[175]` does not reconstruct its count or overlap proof.
      let positiveFamily :=
        (absorbedGermFamilyPositiveRow (data := spineData)).run positiveHistory
          (by key_fresh)
      let neutralConfiguration :=
        (neutralEqualLengthTerminalRow (data := spineData)).run positiveFamily
          (by key_fresh)
      let trichotomy :=
        (coldGermTrichotomyRow (data := spineData)).run neutralConfiguration
          (by key_fresh)
      let table :=
        (coldSameInterfaceTableRow (data := spineData)).run trichotomy
          (by key_fresh)
      let closed :=
        (coldBranchClosedRow (data := spineData)).run table
          (by key_fresh)
      match neutralGermSymmetryDichotomy (data := spineData) closed
          (by key_fresh)
          (by key_fresh) with
      | .left canonicalHistory =>
          -- `[165]`--`[166]`: the non-realized representative is exchanged in
          -- the retained context, and refined minimality publishes `Q = E`.
          -- This is the local manuscript consumer only; the dense-only
          -- blocked-class continuation `[169]` is not entered here.
          let swapped :=
            (canonicalReplacementSwapRow (data := spineData)).run
              canonicalHistory
              (by key_fresh)
          let trivial :=
            (canonicalReplacementTrivialRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              swapped
              (by key_fresh)
          -- `[176]` has now consumed every cited cold/symmetry fact.  Because
          -- `[175]` is per incidence, append `[177]`'s aggregate package and
          -- fan entry on this same ledger so a mixed family retains `Q = E`
          -- together with the Type-B charge of its complement.
          let fanData :=
            (absorbedGermFanDataRow (data := spineData)).run trivial
              (by key_fresh)
          let fanEntry :=
            (absorbedGermFanEnvelopeRow (data := spineData)).run fanData
              (by key_fresh)
          exact Or.inl (Assembly.Internal.selectedAbsorbedFanChargeContinuation fanEntry
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
            (by key_fresh)
            (by key_fresh)
            (by key_fresh)
            (by key_fresh)
            (by infer_instance)
            (by key_fresh)
            (routingFresh := by key_fresh)
            (unifiedNegativeFresh := by key_fresh)
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
            (unifiedTerminalFresh := by key_fresh))
      | .right genuineHistory =>
          -- `[167]`--`[168]`: the graph-realized second strand either gives
          -- one of the two prescribed dyadic cycles inside its owner or lands
          -- in the finite survivor list, where the retained interior stub is
          -- incompatible with the two endpoint attachments.
          let survivor :=
            (twoStrandSurvivorRow (data := spineData)).run genuineHistory
              (by key_fresh)
          let stubbed :=
            (coldWindowStubStructureRow (data := spineData)).run survivor
              (by key_fresh)
          let impossible :=
            (symmetricPairEndpointExclusionRow (data := spineData)).runAndCloseIncompatible
              stubbed (K .coldTwoStrandSurvivor) (K .coldSymmetricPairExcluded)
              (by key_fresh)
              (by key_fresh)
          exact (impossible.elimClosed (by infer_instance)).elim
  | .right absorbedHistory =>
      -- `[177]`, `lem:absorbed-germ-fan-data` (ii): at every heavy centre of a
      -- selected corridor, the corridor's two incidences and tails are decorated
      -- handoff fan data (`def:decorated-fan-envelope`,
      -- `lem:typeA-high-degree-handoff`), published on the literal residual.
      let fanEntry :=
        (absorbedGermFanEnvelopeRow (data := spineData)).run absorbedHistory
          (by key_fresh)
      -- This is exactly the drawn `[177] → [65]` edge, followed by the common
      -- registered charge tail.  On this no-candidate arm the complement is
      -- the whole selected family.
      exact Or.inl (Assembly.Internal.selectedAbsorbedFanChargeContinuation fanEntry
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
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by infer_instance)
        (by key_fresh)
        (routingFresh := by key_fresh)
        (unifiedNegativeFresh := by key_fresh)
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
        (unifiedTerminalFresh := by key_fresh))

end HypostructureErdos64EG
