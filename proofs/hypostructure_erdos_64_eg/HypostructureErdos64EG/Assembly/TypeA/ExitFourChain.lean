import Hypostructure.Graph.Strategy.SpineRows.TypeAExitFourDichotomy
import Hypostructure.Graph.Strategy.SpineRows.TypeAExitFourFiniteDescent
import Hypostructure.Graph.Strategy.SpineRows.TypeAExitFourPeelingStep
import Hypostructure.Graph.Strategy.SpineRows.TypeAExitFourRetestDichotomy
import HypostructureErdos64EG.Assembly.TypeA.ExitFiveToSeven
import HypostructureErdos64EG.Assembly.TypeA.ExitFourDischargedRetest

/-!
# Assembly: TypeA / ExitFourChain

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- **Nodes `[101]`--`[102]` and their loop back to `[89]`**, on the shared
saturated exit entry (index-polymorphic).  `lem:typeA-exit4-finite-descent` is
put on the ledger for `[123]`; then `[101]` tests exit `(4)` at the entry state.
Yes: `[102]` peels the witness's load (`lem:typeA-exit4-discharge`) and the
"recompute `L₄`" loop is the finite descent `typeAExitFourRetestDichotomy`,
which ends either at a saturated state with no further exit-`(4)` witness — the
hypothesis of exits `(5)`--`(8)` — or at an unsaturated peeled state whose
receiver charge is nonnegative (`lem:typeA-exit4-peeling-charge`) and whose
peeled loads are target-defect entries: the retest at `[89]` with the
target-defect ledger (Part IX `[123]`), the next producer.  No: exits
`(5)`--`(8)` at the entry state. -/
-- EG-NODE [101] exit 4? target-defective quotient
-- EG-NODE [102] target-defect peels one load
noncomputable def selectedTypeAExitFourChain
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .typeASaturatedExitEntry) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .typeAReceiverRouting) known]
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
    (deletionWitnessesFresh : K .route8CarrierDeletionWitnesses ∉ known)
    (privateBudgetFresh : K .route8PrivateCarrierBudget ∉ known)
    (noTwoContradictionFresh : K .route8NoTwoCarrierContradiction ∉ known)
    (terminalNoGoFresh : K .route8TerminalNoGo ∉ known)
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
    (censusFresh : K .route8Census ∉ known)
    (twoFresh : K .route8TwoCarrierEntry ∉ known)
    (noTwoFresh : K .route8NoTwoCarrierEntry ∉ known)
    (trueEntryFresh : K .route8TrueTwoCarrierEntry ∉ known)
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
    (jointBalanceFresh : K .route8JointBalance ∉ known)
    (unifiedTerminalFresh : K .route8TerminalNoGo ∉ known)
    (decoratedExcludedFresh : K .typeBExcluded ∉ known)
    (decoratedExclusionResidualFresh : K .typeBExclusionResidual ∉ known)
    (decoratedExclusionMassFresh : K .typeBExclusionResidualMass ∉ known)
    (decoratedObstructionMassFresh : K .typeBOverlapObstructionMass ∉ known)
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
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .negativeSupport) known]
    (closureFresh : closed ∉ known)
   : SelectedRouteEightBoundary selected := by
  letI := cubicBaselineFresh
  let _cubicBaseline := (history.get (K .cubicBaseline)).down
  let cubic := history
  -- `lem:typeA-exit4-finite-descent` on the ledger (read again at `[123]`).
  let descended :=
    (typeAExitFourFiniteDescentRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      cubic (by simp [K_eq_iff, descentFresh])
  -- `[101]`
  match typeAExitFourDichotomy (data := spineData) descended
      (by simp [K_eq_iff, exitFourFresh]) (by simp [K_eq_iff, exitFourFreeFresh]) with
  | .left exitFourHistory =>
      -- `[102]`
      let peeled :=
        (typeAExitFourPeelingStepRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          exitFourHistory (by simp [K_eq_iff, peeledFresh])
      -- `[102]` → `[89]`: recompute `L₄` — the finite exit-`(4)` descent.
      match typeAExitFourRetestDichotomy (data := spineData) peeled
          (by simp [K_eq_iff, exitFourFreeFresh]) (by simp [K_eq_iff, dischargedFresh]) with
      | .left terminalHistory =>
          exact selectedTypeAExitFiveToSeven terminalHistory
            (by simp [K_eq_iff, profileFresh]) (by simp [K_eq_iff, squeezeFresh])
            (by simp [K_eq_iff, burdenFresh]) (by simp [K_eq_iff, deficitFresh])
            (by simp [K_eq_iff, deficitFailsFresh]) (by simp [K_eq_iff, coreFresh])
            (by simp [K_eq_iff, trueResidualFresh])
            (by simp [K_eq_iff, cutParityFresh]) (by simp [K_eq_iff, smallFresh])
            (by simp [K_eq_iff, noSmallFresh]) (by simp [K_eq_iff, collapseFresh])
            (by simp [K_eq_iff, deletionWitnessesFresh])
            (by simp [K_eq_iff, privateBudgetFresh])
            (by simp [K_eq_iff, noTwoContradictionFresh])
            (by simp [K_eq_iff, terminalNoGoFresh])
            (by simp [K_eq_iff, fiveFresh]) (by simp [K_eq_iff, fiveFreeFresh])
            (by simp [K_eq_iff, sixFresh]) (by simp [K_eq_iff, sixFreeFresh])
            (by simp [K_eq_iff, sixProperFresh]) (by simp [K_eq_iff, sixGlobalFresh])
            (by simp [K_eq_iff, sevenProducedFresh]) (by simp [K_eq_iff, sevenFreeFresh])
            (by simp [K_eq_iff, sevenHandoffFresh])
            (by simp [K_eq_iff, decoratedFresh])
            (by simp [K_eq_iff, normalFormFresh]) (by simp [K_eq_iff, decoratedHeavyFresh]) (by simp [K_eq_iff, decoratedDegreeFourFresh]) (by simp [K_eq_iff, decoratedLocalFresh]) (by simp [K_eq_iff, decoratedCompatibilityFresh]) (by simp [K_eq_iff, decoratedProfileFresh]) (by simp [K_eq_iff, decoratedTriangularCoreFresh]) (by simp [K_eq_iff, fanCapFresh]) (by simp [K_eq_iff, decoratedMarkedFresh]) (by simp [K_eq_iff, decoratedResidualFresh]) (by simp [K_eq_iff, decoratedCertificateMassFresh]) (by simp [K_eq_iff, decoratedCycleFresh]) (by simp [K_eq_iff, decoratedFreeFresh]) (by simp [K_eq_iff, decoratedFanEntryFresh]) (by simp [K_eq_iff, decoratedB2ChoiceFresh]) (by simp [K_eq_iff, decoratedB2ObstructionFresh]) (by simp [K_eq_iff, decoratedHybridFresh]) (by simp [K_eq_iff, decoratedLedgerFresh]) (by simp [K_eq_iff, decoratedBridgeMassFresh]) (by simp [K_eq_iff, decoratedBridgeSublinearFresh])
            (by simp [K_eq_iff, censusFresh]) (by simp [K_eq_iff, twoFresh])
            (by simp [K_eq_iff, noTwoFresh]) (by simp [K_eq_iff, trueEntryFresh])
            (by simp [K_eq_iff, unifiedNegativeFresh])
            (typeAExclusionFresh := by simp [K_eq_iff, typeAExclusionFresh])
            (typeBBridgeReductionFresh := by simp [K_eq_iff, typeBBridgeReductionFresh])
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
            (decoratedExcludedFresh := by simp [K_eq_iff, decoratedExcludedFresh])
            (decoratedExclusionResidualFresh := by simp [K_eq_iff, decoratedExclusionResidualFresh])
            (decoratedExclusionMassFresh := by simp [K_eq_iff, decoratedExclusionMassFresh])
            (decoratedObstructionMassFresh := by simp [K_eq_iff, decoratedObstructionMassFresh])
            (decoratedGlobalLocalBridgeFresh := by simp [K_eq_iff, decoratedGlobalLocalBridgeFresh])
            (fanClosedFresh := by simp [K_eq_iff, fanClosedFresh])
            (compatibleClosureFresh := by simp [K_eq_iff, compatibleClosureFresh])
            (fanClosedRoutingFresh := by simp [K_eq_iff, fanClosedRoutingFresh])
            (compatibleRoutingFresh := by simp [K_eq_iff, compatibleRoutingFresh])
            (shoulderCompletionFresh := by simp [K_eq_iff, shoulderCompletionFresh])
            (portReturnFresh := by simp [K_eq_iff, portReturnFresh])
            (firstLandingFresh := by simp [K_eq_iff, firstLandingFresh])
            (crossShoulderFresh := by simp [K_eq_iff, crossShoulderFresh])
            (triangularRoutingFresh := by simp [K_eq_iff, triangularRoutingFresh])
            (by simp [K_eq_iff, closureFresh])
      | .right dischargedHistory =>
          -- `[89]` retest of the discharged receiver with its peeled
          -- target-defect loads (Part IX pressure ledger `[123]`) — the next
          -- producer.
          exact selectedTypeAExitFourDischargedRetest dischargedHistory
            (by simp [K_eq_iff, unifiedNegativeFresh])
            (by simp [K_eq_iff, typeAExclusionFresh])
            (by simp [K_eq_iff, typeBBridgeReductionFresh])
            (by simp [K_eq_iff, piecesClassifiedFresh])
            (by simp [K_eq_iff, decoratedBridgeMassFresh])
            (by simp [K_eq_iff, decoratedBridgeSublinearFresh])
            (by simp [K_eq_iff, sublinearLedgerFresh])
            (by simp [K_eq_iff, sublinearResidualFresh])
            (by simp [K_eq_iff, unifiedDeficitFresh])
            (by simp [K_eq_iff, quotientFreeFresh])
            (by simp [K_eq_iff, quotientResidualFresh])
            (by simp [K_eq_iff, unifiedCensusFresh])
            (by simp [K_eq_iff, extractedCensusFresh])
            (by simp [K_eq_iff, peelingFresh])
            (by simp [K_eq_iff, unifiedTrueFresh])
            (by simp [K_eq_iff, stageFailedFresh])
            (by simp [K_eq_iff, unifiedTerminalFresh])
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
  | .right freeHistory =>
      exact selectedTypeAExitFiveToSeven freeHistory
        (by simp [K_eq_iff, profileFresh]) (by simp [K_eq_iff, squeezeFresh])
        (by simp [K_eq_iff, burdenFresh]) (by simp [K_eq_iff, deficitFresh])
        (by simp [K_eq_iff, deficitFailsFresh]) (by simp [K_eq_iff, coreFresh])
        (by simp [K_eq_iff, trueResidualFresh])
        (by simp [K_eq_iff, cutParityFresh]) (by simp [K_eq_iff, smallFresh])
        (by simp [K_eq_iff, noSmallFresh]) (by simp [K_eq_iff, collapseFresh])
        (by simp [K_eq_iff, deletionWitnessesFresh])
        (by simp [K_eq_iff, privateBudgetFresh])
        (by simp [K_eq_iff, noTwoContradictionFresh])
        (by simp [K_eq_iff, terminalNoGoFresh])
        (by simp [K_eq_iff, fiveFresh]) (by simp [K_eq_iff, fiveFreeFresh])
        (by simp [K_eq_iff, sixFresh]) (by simp [K_eq_iff, sixFreeFresh])
        (by simp [K_eq_iff, sixProperFresh]) (by simp [K_eq_iff, sixGlobalFresh])
        (by simp [K_eq_iff, sevenProducedFresh]) (by simp [K_eq_iff, sevenFreeFresh])
        (by simp [K_eq_iff, sevenHandoffFresh])
        (by simp [K_eq_iff, decoratedFresh])
        (by simp [K_eq_iff, normalFormFresh]) (by simp [K_eq_iff, decoratedHeavyFresh]) (by simp [K_eq_iff, decoratedDegreeFourFresh]) (by simp [K_eq_iff, decoratedLocalFresh]) (by simp [K_eq_iff, decoratedCompatibilityFresh]) (by simp [K_eq_iff, decoratedProfileFresh]) (by simp [K_eq_iff, decoratedTriangularCoreFresh]) (by simp [K_eq_iff, fanCapFresh]) (by simp [K_eq_iff, decoratedMarkedFresh]) (by simp [K_eq_iff, decoratedResidualFresh]) (by simp [K_eq_iff, decoratedCertificateMassFresh]) (by simp [K_eq_iff, decoratedCycleFresh]) (by simp [K_eq_iff, decoratedFreeFresh]) (by simp [K_eq_iff, decoratedFanEntryFresh]) (by simp [K_eq_iff, decoratedB2ChoiceFresh]) (by simp [K_eq_iff, decoratedB2ObstructionFresh]) (by simp [K_eq_iff, decoratedHybridFresh]) (by simp [K_eq_iff, decoratedLedgerFresh]) (by simp [K_eq_iff, decoratedBridgeMassFresh]) (by simp [K_eq_iff, decoratedBridgeSublinearFresh])
        (by simp [K_eq_iff, censusFresh]) (by simp [K_eq_iff, twoFresh])
        (by simp [K_eq_iff, noTwoFresh]) (by simp [K_eq_iff, trueEntryFresh])
        (by simp [K_eq_iff, unifiedNegativeFresh])
        (typeAExclusionFresh := by simp [K_eq_iff, typeAExclusionFresh])
        (typeBBridgeReductionFresh := by simp [K_eq_iff, typeBBridgeReductionFresh])
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
        (decoratedExcludedFresh := by simp [K_eq_iff, decoratedExcludedFresh])
        (decoratedExclusionResidualFresh := by simp [K_eq_iff, decoratedExclusionResidualFresh])
        (decoratedExclusionMassFresh := by simp [K_eq_iff, decoratedExclusionMassFresh])
        (decoratedObstructionMassFresh := by simp [K_eq_iff, decoratedObstructionMassFresh])
        (decoratedGlobalLocalBridgeFresh := by simp [K_eq_iff, decoratedGlobalLocalBridgeFresh])
        (fanClosedFresh := by simp [K_eq_iff, fanClosedFresh])
        (compatibleClosureFresh := by simp [K_eq_iff, compatibleClosureFresh])
        (fanClosedRoutingFresh := by simp [K_eq_iff, fanClosedRoutingFresh])
        (compatibleRoutingFresh := by simp [K_eq_iff, compatibleRoutingFresh])
        (shoulderCompletionFresh := by simp [K_eq_iff, shoulderCompletionFresh])
        (portReturnFresh := by simp [K_eq_iff, portReturnFresh])
        (firstLandingFresh := by simp [K_eq_iff, firstLandingFresh])
        (crossShoulderFresh := by simp [K_eq_iff, crossShoulderFresh])
        (triangularRoutingFresh := by simp [K_eq_iff, triangularRoutingFresh])
        (by simp [K_eq_iff, closureFresh])

end HypostructureErdos64EG
