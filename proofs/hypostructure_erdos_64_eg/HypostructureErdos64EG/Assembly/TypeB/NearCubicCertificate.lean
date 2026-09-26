import HypostructureErdos64EG.Assembly.RouteEight.TypeBContinuation
import HypostructureErdos64EG.Assembly.TypeB.Internal.Certificate

/-!
# Assembly: TypeB / NearCubicCertificate

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- The quantitative tail of `[76]`/`[85]` on the near-cubic inputs for which
the paper supplies the ordinary route-8 census facts.  This wrapper is
deliberately separate from the strict-surplus `[144]` handoff, which does not
carry the sublinear-surplus input of `[76]`. -/
noncomputable def selectedTypeBNearCubicCertificateAfterPortRouting
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeBFanEntry) known]
    [FactKeys.Has (K .fanCertificateCap) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .highCentreNormalForm) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .negativeSupport) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .typeAReceiverRouting) known]
    [FactKeys.Has (K .fanClosedPort) known]
    [FactKeys.Has (K .compatiblePairFanClosure) known]
    [FactKeys.Has (K .fanClosedPortTypeBRouting) known]
    [FactKeys.Has (K .compatiblePairTypeBRouting) known]
    (markedFresh : K .fanCertificateMarked ∉ known)
    (residualFresh : K .fanCertificateResidual ∉ known)
    (certificateMassFresh : K .fanCertificateResidualMass ∉ known)
    (cycleFresh : K .typeBDirectCycle ∉ known)
    (freeFresh : K .typeBDirectCycleFree ∉ known)
    (choiceFresh : K .typeBB2Choice ∉ known)
    (obstructionFresh : K .typeBOverlapObstruction ∉ known)
    (hybridFresh : K .typeBHybridEntry ∉ known)
    (ledgerFresh : K .typeBDisjointLedger ∉ known)
    (excludedFresh : K .typeBExcluded ∉ known)
    (exclusionResidualFresh : K .typeBExclusionResidual ∉ known)
    (exclusionMassFresh : K .typeBExclusionResidualMass ∉ known)
    (obstructionMassFresh : K .typeBOverlapObstructionMass ∉ known)
    (bridgeMassFresh : K .typeBBridgeMass ∉ known)
    (bridgeSublinearFresh : K .typeBBridgeSublinear ∉ known)
    (unifiedNegativeFresh : K .route8UnifiedNegative ∉ known)
    (typeAExclusionFresh : K .typeAExclusion ∉ known := by key_fresh)
    (typeBBridgeReductionFresh : K .typeBBridgeReduction ∉ known := by
      key_fresh)
    (piecesClassifiedFresh : K .route8PiecesClassified ∉ known := by
      key_fresh)
    (sublinearLedgerFresh : K .typeBSublinearLedger ∉ known := by
      key_fresh)
    (sublinearResidualFresh : K .typeBSublinearResidual ∉ known := by
      key_fresh)
    (unifiedDeficitFresh : K .route8UnifiedDeficit ∉ known := by
      key_fresh)
    (quotientFreeFresh : K .route8QuotientFree ∉ known := by key_fresh)
    (quotientResidualFresh : K .route8QuotientResidual ∉ known := by
      key_fresh)
    (unifiedCensusFresh : K .route8UnifiedEntryCensus ∉ known := by
      key_fresh)
    (extractedCensusFresh : K .route8ExtractedEntryCensus ∉ known := by
      key_fresh)
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known)
    (peelingFresh : K .route8PeelingDescent ∉ known)
    (stageFailedFresh : K .route8StageRateFailed ∉ known := by key_fresh)
    (demandLedgerFresh : K .route8DemandLedger ∉ known := by key_fresh)
    (demandAbsorptionFresh : K .route8DemandAbsorption ∉ known := by
      key_fresh)
    (openBoundarySaturatedFresh : K .route8OpenBoundarySaturated ∉ known := by
      key_fresh)
    (demandUnitCountFresh : K .route8DemandUnitCount ∉ known := by
      key_fresh)
    (windowBlockersFresh : K .route8WindowBlockers ∉ known := by key_fresh)
    (windowShadowSignatureFresh : K .windowShadowSignature ∉ known := by key_fresh)
    (windowShadowTailFresh : K .windowShadowSingletonTail ∉ known := by key_fresh)
    (windowShadowCycleFresh : K .windowShadowHitCycle ∉ known := by key_fresh)
    (windowShadowExcludedFresh : K .windowShadowHitExcluded ∉ known := by key_fresh)
    (demandResidualFresh : K .route8PeeledDemandResidual ∉ known := by
      key_fresh)
    (unpaidExitFourFresh : K .route8UnpaidExitFourResidual ∉ known := by
      key_fresh)
    (unifiedVisibleFresh : K .route8UnifiedVisibleResidual ∉ known := by
      key_fresh)
    (unifiedVisibleOverloadFresh : K .route8UnifiedVisibleOverload ∉ known := by
      key_fresh)
    (jointBalanceFresh : K .route8JointBalance ∉ known := by
      key_fresh)
    (unifiedTerminalFresh : K .route8TerminalNoGo ∉ known)
    (globalLocalBridgeFresh : K .typeBGlobalLocalBridge ∉ known := by
      key_fresh)
   :
    SelectedRouteEightBoundary selected := by
  match Assembly.Internal.selectedTypeBCertificateBoundaryAfterPortRouting history markedFresh residualFresh
      certificateMassFresh cycleFresh freeFresh choiceFresh obstructionFresh
      hybridFresh ledgerFresh excludedFresh exclusionResidualFresh
      exclusionMassFresh obstructionMassFresh
      (globalLocalBridgeFresh := globalLocalBridgeFresh) with
  | .inl mass =>
      exact selectedTypeBRoute8Continuation mass
        (bridgeMassFresh := by key_fresh)
        (bridgeSublinearFresh := by key_fresh)
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
  | .inr (.inl paid) =>
      rcases (paid.get (K .typeBExcluded)).down with canonical | _handoff
      · obtain ⟨_packing, _valid, _maximal, canonicalPiece,
          _centres, assigned, nonnegative⟩ := canonical
        have negative : selected.object.NegativeNetCharge
            canonicalPiece.vertices spineData.threshold
            spineData.dischargeScale := by
          rcases assigned with ⟨negative, _, _⟩ | ⟨negative, _, _⟩ <;>
            exact negative
        exact ((selected.object.not_negativeNetCharge_iff
          canonicalPiece.vertices spineData.threshold
            spineData.dischargeScale).mpr nonnegative negative).elim
      · exact selectedTypeBRoute8Continuation paid
          (bridgeMassFresh := by key_fresh)
          (bridgeSublinearFresh := by key_fresh)
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
  | .inr (.inr (.inl mass)) =>
      exact selectedTypeBRoute8Continuation mass
        (bridgeMassFresh := by key_fresh)
        (bridgeSublinearFresh := by key_fresh)
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
  | .inr (.inr (.inr mass)) =>
      exact selectedTypeBRoute8Continuation mass
        (bridgeMassFresh := by key_fresh)
        (bridgeSublinearFresh := by key_fresh)
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

/-- Compatibility name for callers that already carry the common `[72]`
port-routing ledger.  New branch assembly uses the explicit
`AfterPortRouting` name so duplicate publication is impossible. -/
noncomputable abbrev selectedTypeBNearCubicCertificate :=
  @selectedTypeBNearCubicCertificateAfterPortRouting

end HypostructureErdos64EG
