import Hypostructure.Graph.Strategy.SpineRows.HighCentreNormalForm
import Hypostructure.Graph.Strategy.SpineRows.TypeAExitFiveDichotomy
import Hypostructure.Graph.Strategy.SpineRows.TypeAExitSevenDichotomy
import Hypostructure.Graph.Strategy.SpineRows.TypeAExitSevenHandoff
import Hypostructure.Graph.Strategy.SpineRows.TypeAExitSixDichotomy
import Hypostructure.Graph.Strategy.SpineRows.TypeAExitSixScopeDichotomy
import HypostructureErdos64EG.Assembly.RouteEight.Residual
import HypostructureErdos64EG.Assembly.TypeA.DecoratedHandoff

/-!
# Assembly: TypeA / ExitFiveToSeven

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- **Nodes `[103]`--`[109]`: exits `(5)`--`(7)` and the route-8 residual**, on the
saturated-handoff state after exit `(4)` is absent (index-polymorphic).
`[103]` exit `(5)`: a target-complete proper-support compression closes at
`[104]` against `cor:uncompressible`.  `[105]` exit `(6)`: a delocalizing
response equality is localized at `[106]` — proper scope closes against
`lem:replacement` (`K .replacementExclusion`), global scope against the
selection's minimality.  `[107]` exit `(7)`: the decorated handoff fan envelope
is committed as the Type B handoff at `[108]`; its admissibility is proved at
`[65]`, the next producer on that lane.  Its absence is `[109]`, the route-8
residual continued in Part IX (`[110]`, the next producer). -/
-- EG-NODE [103] exit 5? target-complete response compression
-- EG-NODE [104] uncompressibility contradiction
-- EG-NODE [105] exit 6? proper/whole-graph support dependence
-- EG-NODE [106] support-dependence branch closes
-- EG-NODE [107] exit 7? decorated handoff fan
-- EG-NODE [108] returns to Type B handoff
-- EG-NODE [66] Type A exit 7 input from the Part VIII handoff
noncomputable def selectedTypeAExitFiveToSeven
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .typeASaturatedHandoffExitFourFree) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .negativeSupport) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
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
    (fiveFresh : K .typeAExitFive ∉ known)
    (fiveFreeFresh : K .typeAExitFiveFree ∉ known)
    (sixFresh : K .typeAExitSix ∉ known)
    (sixFreeFresh : K .typeAExitSixFree ∉ known)
    (sixProperFresh : K .typeAExitSixProper ∉ known)
    (sixGlobalFresh : K .typeAExitSixGlobal ∉ known)
    (sevenProducedFresh : K .typeAExitSevenProduced ∉ known)
    (sevenFreeFresh : K .typeAExitSevenFree ∉ known)
    (sevenHandoffFresh : K .typeAExitSevenHandoff ∉ known)
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
    (closureFresh : closed ∉ known)
   : SelectedRouteEightBoundary selected := by
  -- `[103]`
  match typeAExitFiveDichotomy (data := spineData) history fiveFresh fiveFreeFresh with
  | .left fiveHistory =>
      -- `[104]`
      exact ((closeIncompatible fiveHistory (K .uncompressible) (K .typeAExitFive)
        (by simp [K_eq_iff, closureFresh])).elimClosed (by infer_instance)).elim
  | .right fiveFree =>
      -- `[105]`
      match typeAExitSixDichotomy (data := spineData) fiveFree
          (by simp [K_eq_iff, sixFresh]) (by simp [K_eq_iff, sixFreeFresh]) with
      | .left sixHistory =>
          -- `[106]`
          match typeAExitSixScopeDichotomy (data := spineData) sixHistory
              (by simp [K_eq_iff, sixProperFresh]) (by simp [K_eq_iff, sixGlobalFresh]) with
          | .left properHistory =>
              exact ((closeIncompatible properHistory (K .replacementExclusion)
                (K .typeAExitSixProper) (by simp [K_eq_iff, closureFresh])).elimClosed
                (by infer_instance)).elim
          | .right globalHistory =>
              exact ((closeIncompatible globalHistory (K .selection)
                (K .typeAExitSixGlobal) (by simp [K_eq_iff, closureFresh])).elimClosed
                (by infer_instance)).elim
      | .right sixFree =>
          -- `[107]`
          match typeAExitSevenDichotomy (data := spineData) sixFree
              (by simp [K_eq_iff, sevenProducedFresh])
              (by simp [K_eq_iff, sevenFreeFresh]) with
          | .left producedHistory =>
              -- `[108]`: record the produced Type B handoff envelope; `[65]`
              -- proves its admissibility — the next producer.
              let handoff :=
                (typeAExitSevenHandoffRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  producedHistory (by simp [K_eq_iff, sevenHandoffFresh])
              exact selectedTypeADecoratedHandoff handoff
                (by simp [K_eq_iff, decoratedFresh])
                (by simp [K_eq_iff, normalFormFresh]) (by simp [K_eq_iff, decoratedHeavyFresh]) (by simp [K_eq_iff, decoratedDegreeFourFresh]) (by simp [K_eq_iff, decoratedLocalFresh]) (by simp [K_eq_iff, decoratedCompatibilityFresh]) (by simp [K_eq_iff, decoratedProfileFresh]) (by simp [K_eq_iff, decoratedTriangularCoreFresh]) (by simp [K_eq_iff, fanCapFresh]) (by simp [K_eq_iff, decoratedMarkedFresh]) (by simp [K_eq_iff, decoratedResidualFresh]) (by simp [K_eq_iff, decoratedCertificateMassFresh]) (by simp [K_eq_iff, decoratedCycleFresh]) (by simp [K_eq_iff, decoratedFreeFresh]) (by simp [K_eq_iff, decoratedFanEntryFresh]) (by simp [K_eq_iff, decoratedB2ChoiceFresh]) (by simp [K_eq_iff, decoratedB2ObstructionFresh]) (by simp [K_eq_iff, decoratedHybridFresh]) (by simp [K_eq_iff, decoratedLedgerFresh]) (by simp [K_eq_iff, decoratedBridgeMassFresh]) (by simp [K_eq_iff, decoratedBridgeSublinearFresh])
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
          | .right route8History =>
              -- `[109]` is the shared no-exit-`(7)` residual drawn in Part
              -- VIII.  After any finite exit-`(4)` peeling the residual may be
              -- on the silent side of `lem:typeA-exit4-residual-routing`, so
              -- the paper sends this exact ledger to `[110]`; it has no
              -- visible-lane impossibility terminal.
              let normal :=
                (highCentreNormalFormRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run route8History
                    (by simp [K_eq_iff, normalFormFresh])
              exact selectedRouteEightResidual normal
                (by simp [K_eq_iff, profileFresh])
                (by simp [K_eq_iff, squeezeFresh])
                (by simp [K_eq_iff, burdenFresh])
                (by simp [K_eq_iff, deficitFresh])
                (by simp [K_eq_iff, deficitFailsFresh])
                (by simp [K_eq_iff, coreFresh])
                (by simp [K_eq_iff, trueResidualFresh])
                (by simp [K_eq_iff, cutParityFresh])
                (by simp [K_eq_iff, smallFresh])
                (by simp [K_eq_iff, noSmallFresh])
                (by simp [K_eq_iff, collapseFresh])
                (by simp [K_eq_iff, decoratedBridgeMassFresh])
                (by simp [K_eq_iff, decoratedBridgeSublinearFresh])
                (by simp [K_eq_iff, censusFresh])
                (by simp [K_eq_iff, twoFresh])
                (by simp [K_eq_iff, noTwoFresh])
                (by simp [K_eq_iff, trueEntryFresh])
                (by simp [K_eq_iff, deletionWitnessesFresh])
                (by simp [K_eq_iff, privateBudgetFresh])
                (by simp [K_eq_iff, noTwoContradictionFresh])
                (by simp [K_eq_iff, terminalNoGoFresh])
                (by simp [K_eq_iff, unifiedNegativeFresh])
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

end HypostructureErdos64EG
