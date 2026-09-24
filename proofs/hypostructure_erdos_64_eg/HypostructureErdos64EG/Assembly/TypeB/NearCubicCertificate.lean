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
    (typeAExclusionFresh : K .typeAExclusion ∉ known := by simp [K_eq_iff])
    (typeBBridgeReductionFresh : K .typeBBridgeReduction ∉ known := by
      simp [K_eq_iff])
    (piecesClassifiedFresh : K .route8PiecesClassified ∉ known := by
      simp [K_eq_iff])
    (sublinearLedgerFresh : K .typeBSublinearLedger ∉ known := by
      simp [K_eq_iff])
    (sublinearResidualFresh : K .typeBSublinearResidual ∉ known := by
      simp [K_eq_iff])
    (unifiedDeficitFresh : K .route8UnifiedDeficit ∉ known := by
      simp [K_eq_iff])
    (quotientFreeFresh : K .route8QuotientFree ∉ known := by simp [K_eq_iff])
    (quotientResidualFresh : K .route8QuotientResidual ∉ known := by
      simp [K_eq_iff])
    (unifiedCensusFresh : K .route8UnifiedEntryCensus ∉ known := by
      simp [K_eq_iff])
    (extractedCensusFresh : K .route8ExtractedEntryCensus ∉ known := by
      simp [K_eq_iff])
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known)
    (peelingFresh : K .route8PeelingDescent ∉ known)
    (stageFailedFresh : K .route8StageRateFailed ∉ known := by simp [K_eq_iff])
    (demandLedgerFresh : K .route8DemandLedger ∉ known := by simp [K_eq_iff])
    (demandAbsorptionFresh : K .route8DemandAbsorption ∉ known := by
      simp [K_eq_iff])
    (openBoundarySaturatedFresh : K .route8OpenBoundarySaturated ∉ known := by
      simp [K_eq_iff])
    (demandUnitCountFresh : K .route8DemandUnitCount ∉ known := by
      simp [K_eq_iff])
    (windowBlockersFresh : K .route8WindowBlockers ∉ known := by simp [K_eq_iff])
    (windowShadowSignatureFresh : K .windowShadowSignature ∉ known := by simp [K_eq_iff])
    (windowShadowTailFresh : K .windowShadowSingletonTail ∉ known := by simp [K_eq_iff])
    (windowShadowCycleFresh : K .windowShadowHitCycle ∉ known := by simp [K_eq_iff])
    (windowShadowExcludedFresh : K .windowShadowHitExcluded ∉ known := by simp [K_eq_iff])
    (demandResidualFresh : K .route8PeeledDemandResidual ∉ known := by
      simp [K_eq_iff])
    (unpaidExitFourFresh : K .route8UnpaidExitFourResidual ∉ known := by
      simp [K_eq_iff])
    (unifiedVisibleFresh : K .route8UnifiedVisibleResidual ∉ known := by
      simp [K_eq_iff])
    (unifiedVisibleOverloadFresh : K .route8UnifiedVisibleOverload ∉ known := by
      simp [K_eq_iff])
    (jointBalanceFresh : K .route8JointBalance ∉ known := by
      simp [K_eq_iff])
    (unifiedTerminalFresh : K .route8TerminalNoGo ∉ known)
    (globalLocalBridgeFresh : K .typeBGlobalLocalBridge ∉ known := by
      simp [K_eq_iff])
   :
    SelectedRouteEightBoundary selected := by
  match Assembly.Internal.selectedTypeBCertificateBoundaryAfterPortRouting history markedFresh residualFresh
      certificateMassFresh cycleFresh freeFresh choiceFresh obstructionFresh
      hybridFresh ledgerFresh excludedFresh exclusionResidualFresh
      exclusionMassFresh obstructionMassFresh
      (globalLocalBridgeFresh := globalLocalBridgeFresh) with
  | .inl mass =>
      exact selectedTypeBRoute8Continuation mass
        (bridgeMassFresh := by simp [K_eq_iff, bridgeMassFresh])
        (bridgeSublinearFresh := by simp [K_eq_iff, bridgeSublinearFresh])
        (unifiedNegativeFresh := by simp [K_eq_iff, unifiedNegativeFresh])
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
          (bridgeMassFresh := by simp [K_eq_iff, bridgeMassFresh])
          (bridgeSublinearFresh := by simp [K_eq_iff, bridgeSublinearFresh])
          (unifiedNegativeFresh := by simp [K_eq_iff, unifiedNegativeFresh])
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
  | .inr (.inr (.inl mass)) =>
      exact selectedTypeBRoute8Continuation mass
        (bridgeMassFresh := by simp [K_eq_iff, bridgeMassFresh])
        (bridgeSublinearFresh := by simp [K_eq_iff, bridgeSublinearFresh])
        (unifiedNegativeFresh := by simp [K_eq_iff, unifiedNegativeFresh])
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
  | .inr (.inr (.inr mass)) =>
      exact selectedTypeBRoute8Continuation mass
        (bridgeMassFresh := by simp [K_eq_iff, bridgeMassFresh])
        (bridgeSublinearFresh := by simp [K_eq_iff, bridgeSublinearFresh])
        (unifiedNegativeFresh := by simp [K_eq_iff, unifiedNegativeFresh])
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

/-- Compatibility name for callers that already carry the common `[72]`
port-routing ledger.  New branch assembly uses the explicit
`AfterPortRouting` name so duplicate publication is impossible. -/
noncomputable abbrev selectedTypeBNearCubicCertificate :=
  @selectedTypeBNearCubicCertificateAfterPortRouting

end HypostructureErdos64EG
