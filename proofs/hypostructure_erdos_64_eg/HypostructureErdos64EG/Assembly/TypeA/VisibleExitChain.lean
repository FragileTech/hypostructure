import Hypostructure.Graph.Strategy.SpineRows.TypeAExitOneDichotomy
import Hypostructure.Graph.Strategy.SpineRows.TypeAExitThreeDichotomy
import Hypostructure.Graph.Strategy.SpineRows.TypeAExitTwoDichotomy
import HypostructureErdos64EG.Assembly.TypeA.VisibleExitFour

/-!
# Assembly: TypeA / VisibleExitChain

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- **Nodes `[95]`--`[100]`: the saturated exit chain, exits `(1)`--`(3)`**, on
the `[93]` visible-entry residual (index-polymorphic).  `def:typeA-saturated-exits`
and `lem:typeA-exits-discharged`: exit `(1)` — an anchored return through the
saturated receiver's completion port of Mersenne length — is a power-of-two
cycle by `lem:return-equivalence`, closed at `[96]` against the return-avoidance
invariant `[5]`--`[7]`; exit `(2)` — two internally disjoint receiver-entry
returns through one port with accepted total length — is a cycle
(`lem:typeA-common-port-return-cycle`), closed at `[98]` against the selection;
exit `(3)` — a `P₁₃` label collision — closes at `[100]` against the selection.
The exit-`(3)`-free residual enters exit `(4)`, `[101]`, the next producer. -/
-- EG-NODE [95] exit 1? Mersenne return
-- EG-NODE [96] target cycle
-- EG-NODE [97] exit 2? power-of-two theta
-- EG-NODE [98] target cycle
-- EG-NODE [99] exit 3? $P_{13}$ label collision
-- EG-NODE [100] label/target collision
noncomputable def selectedTypeAVisibleExitChain
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .typeAVisibleEntry) known]
    [FactKeys.Has (K .returnAvoidance) known]
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
    (noTwoContradictionFresh : K .route8PrivateCarrierBudget ∉ known)
    (terminalNoGoFresh : K .route8TwoCarrierExit ∉ known)
    (returnFresh : K .typeAExitOneReturn ∉ known)
    (oneFreeFresh : K .typeAExitOneFree ∉ known)
    (thetaFresh : K .typeAExitTwoTheta ∉ known)
    (twoFreeFresh : K .typeAExitTwoFree ∉ known)
    (collisionFresh : K .typeAExitThreeCollision ∉ known)
    (threeFreeFresh : K .typeAExitThreeFree ∉ known)
    -- Type A exits `(4)`--`(7)`, `[101]`--`[109]` (`selectedTypeAExitFourChain`).
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .replacementExclusion) known]
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
    (unpaidTwoFresh : K .route8UnpaidTwoCarrier ∉ known := by key_fresh)
    (witnessFreeFresh : K .route8UnpaidWitnessFree ∉ known := by key_fresh)
   : SelectedRouteEightBoundary selected := by
  letI := cubicBaselineFresh
  let _cubicBaseline := (history.get (K .cubicBaseline)).down
  -- `[95]`
  match typeAExitOneDichotomy (data := spineData) history returnFresh oneFreeFresh with
  | .left returnHistory =>
      -- `[96]`
      exact ((closeIncompatible returnHistory (K .returnAvoidance) (K .typeAExitOneReturn)
        (by key_fresh)).elimClosed (by infer_instance)).elim
  | .right oneFree =>
      -- `[97]`
      match typeAExitTwoDichotomy (data := spineData) oneFree
          (by key_fresh) (by key_fresh) with
      | .left thetaHistory =>
          -- `[98]`
          exact ((closeIncompatible thetaHistory (K .selection) (K .typeAExitTwoTheta)
            (by key_fresh)).elimClosed (by infer_instance)).elim
      | .right twoFree =>
          -- `[99]`
          match typeAExitThreeDichotomy (data := spineData) twoFree
              (by key_fresh) (by key_fresh) with
          | .left collisionHistory =>
              -- `[100]`
              exact ((closeIncompatible collisionHistory (K .selection)
                (K .typeAExitThreeCollision)
                (by key_fresh)).elimClosed (by infer_instance)).elim
          | .right threeFree =>
              -- `[101]`--`[109]`: exit `(4)` and the rest of the exit segment on
              -- the visible lane.
              exact selectedTypeAVisibleExitFour threeFree
                (by key_fresh) (by key_fresh)
                (by key_fresh) (by key_fresh)
                (by key_fresh) (by key_fresh)
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
                (by key_fresh)
                (by key_fresh) (by key_fresh)
                (by key_fresh)
                (by infer_instance) (by key_fresh) (by key_fresh) (by key_fresh) (by key_fresh) (by key_fresh) (by key_fresh) (by key_fresh) (by key_fresh) (by key_fresh) (by key_fresh) (by key_fresh) (by key_fresh) (by key_fresh) (by key_fresh) (by key_fresh) (by key_fresh) (by key_fresh) (by key_fresh) (by key_fresh) (by key_fresh)
                (by key_fresh) (by key_fresh)
                (by key_fresh) (by key_fresh)
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
                (decoratedExcludedFresh := by key_fresh)
                (decoratedExclusionResidualFresh := by key_fresh)
                (decoratedExclusionMassFresh := by key_fresh)
                (decoratedObstructionMassFresh := by key_fresh)
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

end HypostructureErdos64EG
