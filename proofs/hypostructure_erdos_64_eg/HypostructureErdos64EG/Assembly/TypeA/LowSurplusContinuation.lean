import Hypostructure.Graph.Strategy.SpineRows.PortPowerReturn
import Hypostructure.Graph.Strategy.SpineRows.TypeABoundedSupport
import Hypostructure.Graph.Strategy.SpineRows.TypeAPortReturn
import Hypostructure.Graph.Strategy.SpineRows.TypeAReceiverRouting
import Hypostructure.Graph.Strategy.SpineRows.TypeASaturationDichotomy
import Hypostructure.Graph.Strategy.SpineRows.TypeAUnsaturatedDischarge
import Hypostructure.Graph.Strategy.SpineRows.TypeAVisibleEntryDichotomy
import HypostructureErdos64EG.Assembly.TypeA.SilentExitChain
import HypostructureErdos64EG.Assembly.TypeA.VisibleExitChain

/-!
# Assembly: TypeA / LowSurplusContinuation

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- **Nodes `[63]`, `[86]`--`[94]`: the Type A entry**, on the `[62]` Type A
residual of either spine arm (index-polymorphic, as `selectedNetChargeContinuation`).

`[86]` is `def:typeA-support`, namely `def:admissible` with `σ(X) = 0`.
At `[87]`, node `[27]` makes that selected piece `P13`-free; shortest internal
paths give `diam(X) ≤ 11`, and the subcubic breadth-first count gives
`|X| ≤ 6142`.  At `[88]`, the receiver routing `lem:typeA-receiver-loads`
and the threshold algebra
`lem:typeA-threshold-algebra` (`H₀ ≤ 4, H₁ ≤ 8, H₂ ≤ 12` at the registered
values) are `typeAReceiverRoutingRow`.  `[89]` asks whether some receiver is
saturated (`L(w) ≥ s·q(w)`).  No: `[90]` `L(w) ≤ s·q(w) − 1`, `[91]`
`lem:typeA-unsaturated-discharge` gives `|X| ≤ s·def⁺(X)`, and `[92]` closes
against the support's negative net charge `s·def⁺(X) < |X| + s·σ(X)` with
`σ(X) = 0`.  Yes: `lem:typeA-port-return` (every completion port has an
anchored return, from `lem:bridgeless`) and `[93]`: does a port of the
saturated receiver see `s` visible receiver-entry returns?  Yes → the exit
chain `[95]`--`[107]`; no → `[94]` `S_sil^exc(X) ≥ s·D_A(X)` → exits
`[101]`--`[107]`.  Both exit lanes are the next loud producers. -/
-- EG-NODE [88] raw thresholds $H_0\le4$, $H_1\le8$, $H_2\le12$
-- EG-NODE [89] some receiver has $L(w)\ge4q(w)$?
-- EG-NODE [90] no: unsaturated $L(w)\le4q(w)-1$
-- EG-NODE [91] $3/7/11$ charge bound
-- EG-NODE [92] unsaturated Type A charge closes
-- EG-NODE [93] some port has four visible receiver-entry returns?
-- EG-NODE [94] visible-first excess: $S_{\rm sil}^{\rm exc}(X)\ge4D_A(X)$
-- EG-NODE [86] Type A: $\sigma(X)=0$, hence $\defp(X)<|X|/4$
-- EG-NODE [87] $P_{13}$-free; subcubic case has $\diam(X)\le11$ and $|X|\le6142$
noncomputable def selectedTypeALowSurplusContinuation
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .typeALowSurplus) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .contractionCritical) known]
    [FactKeys.Has (K .slackIndependent) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    [FactKeys.Has (K .returnAvoidance) known]
    [FactKeys.Has (K .tightEndpoint) known]
    (boundedFresh : K .typeABoundedSupport ∉ known := by key_fresh)
    (routingFresh : K .typeAReceiverRouting ∉ known := by key_fresh)
    (saturatedFresh : K .typeASaturatedReceiver ∉ known := by key_fresh)
    (unsaturatedFresh : K .typeAUnsaturatedReceivers ∉ known := by key_fresh)
    (dischargeFresh : K .typeAUnsaturatedDischarge ∉ known := by key_fresh)
    (portFresh : K .typeAPortReturn ∉ known := by key_fresh)
    (powerReturnFresh : K .portPowerReturn ∉ known := by key_fresh)
    (visibleFresh : K .typeAVisibleEntry ∉ known := by key_fresh)
    (excessFresh : K .typeAVisibleFirstExcess ∉ known := by key_fresh)
    -- exits `(1)`--`(3)`, `[95]`--`[100]`
    [FactKeys.Has (K .returnAvoidance) known]
    (returnFresh : K .typeAExitOneReturn ∉ known := by key_fresh)
    (oneFreeFresh : K .typeAExitOneFree ∉ known := by key_fresh)
    (thetaFresh : K .typeAExitTwoTheta ∉ known := by key_fresh)
    (twoFreeFresh : K .typeAExitTwoFree ∉ known := by key_fresh)
    (collisionFresh : K .typeAExitThreeCollision ∉ known := by key_fresh)
    (threeFreeFresh : K .typeAExitThreeFree ∉ known := by key_fresh)
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
    -- `[108]` → Type B `[65]` (decorated) and `[109]` → Part IX `[110]`--`[116]`.
    [FactKeys.Has (K .largeBudgetResidual) known]
    (decoratedFresh : K .typeBDecoratedAssignedSupport ∉ known := by key_fresh)
    (cubicBaselineFresh : FactKeys.Has (K .cubicBaseline) known := by infer_instance)
    (normalFormFresh : K .highCentreNormalForm ∉ known := by key_fresh)
    (decoratedHeavyFresh : K .typeBFanHeavyCentre ∉ known := by key_fresh)
    (decoratedDegreeFourFresh : K .typeBFanDegreeFourCentres ∉ known := by key_fresh)
    (decoratedLocalFresh : K .typeBFanLocalDichotomy ∉ known := by key_fresh)
    (decoratedCompatibilityFresh :
      K .sameCenterOpenPortCompatibility ∉ known := by key_fresh)
    (decoratedProfileFresh : K .typeBFanDegreeFourProfile ∉ known := by key_fresh)
    (decoratedTriangularCoreFresh : K .triangularFanCore ∉ known := by key_fresh)
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
    (noTwoContradictionFresh : K .route8PrivateCarrierBudget ∉ known :=
      by key_fresh)
    (terminalNoGoFresh : K .route8TwoCarrierExit ∉ known := by key_fresh)
    (unifiedNegativeFresh : K .route8UnifiedNegative ∉ known := by key_fresh)
    (typeAExclusionFresh : K .typeAExclusion ∉ known := by key_fresh)
    (typeBBridgeReductionFresh : K .typeBBridgeReduction ∉ known := by
      key_fresh)
    (piecesClassifiedFresh : K .route8PiecesClassified ∉ known := by
      key_fresh)
    (sublinearLedgerFresh : K .typeBSublinearLedger ∉ known := by key_fresh)
    (sublinearResidualFresh : K .typeBSublinearResidual ∉ known := by key_fresh)
    (unifiedDeficitFresh : K .route8UnifiedDeficit ∉ known := by key_fresh)
    (quotientFreeFresh : K .route8QuotientFree ∉ known := by key_fresh)
    (quotientResidualFresh : K .route8QuotientResidual ∉ known := by key_fresh)
    (unifiedCensusFresh : K .route8UnifiedEntryCensus ∉ known := by key_fresh)
    (extractedCensusFresh : K .route8ExtractedEntryCensus ∉ known := by
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
    (demandResidualFresh : K .route8StageRate ∉ known := by key_fresh)
    (unpaidExitFourFresh : K .route8UnpaidExitFourResidual ∉ known := by
      key_fresh)
    (unifiedVisibleFresh : K .route8UnifiedVisibleResidual ∉ known := by
      key_fresh)
    (unifiedVisibleOverloadFresh : K .route8UnifiedVisibleOverload ∉ known := by
      key_fresh)
    (jointBalanceFresh : K .route8JointBalance ∉ known := by
      key_fresh)
    (unifiedTerminalFresh : K .route8UnifiedTwoCarrierExit ∉ known := by key_fresh)
    (unpaidTwoFresh : K .route8UnpaidTwoCarrier ∉ known := by key_fresh)
    (witnessFreeFresh : K .route8UnpaidWitnessFree ∉ known := by key_fresh)
    (decoratedGlobalLocalBridgeFresh : K .typeBGlobalLocalBridge ∉ known := by key_fresh)
    (fanClosedFresh : K .fanClosedPort ∉ known := by key_fresh)
    (compatibleClosureFresh : K .compatiblePairFanClosure ∉ known := by key_fresh)
    (fanClosedRoutingFresh : K .fanClosedPortTypeBRouting ∉ known := by key_fresh)
    (compatibleRoutingFresh : K .compatiblePairTypeBRouting ∉ known := by key_fresh)
    (shoulderCompletionFresh : K .triangularShoulderCompletion ∉ known := by key_fresh)
    (portReturnFresh : K .triangularPortReturn ∉ known := by key_fresh)
    (firstLandingFresh : K .triangularFirstLanding ∉ known := by key_fresh)
    (crossShoulderFresh : K .triangularCrossShoulder ∉ known := by key_fresh)
    (triangularRoutingFresh : K .triangularPortTypeBRouting ∉ known := by key_fresh)
    [FactKeys.Has (K .negativeSupport) known]
    (closureFresh : closed ∉ known := by key_fresh)
    (silentFourFreeFresh : K .typeASilentExitFourFree ∉ known := by
      key_fresh)
    (silentFiveFreeFresh : K .typeASilentExitFiveFree ∉ known := by
      key_fresh)
    (silentSixFreeFresh : K .typeASilentExitSixFree ∉ known := by
      key_fresh)
    (silentSevenFreeFresh : K .typeASilentExitSevenFree ∉ known := by
      key_fresh) :
    SelectedRouteEightBoundary selected := by
  letI := cubicBaselineFresh
  let _cubicBaseline := (history.get (K .cubicBaseline)).down
  -- `[87]`: the selected incoming Type A piece is P13-free, has diameter at
  -- most 11, and has at most 6142 vertices.
  let bounded :=
    (typeABoundedSupportRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by key_fresh)
  -- `[88]`
  let routed :=
    (typeAReceiverRoutingRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) spineData).run
      bounded (by key_fresh)
  -- `[89]`
  match typeASaturationDichotomy (data := spineData) routed
      (by key_fresh) (by key_fresh) with
  | .right unsaturatedHistory =>
      -- `[90]`--`[91]`
      let discharged :=
        (typeAUnsaturatedDischargeRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          unsaturatedHistory (by key_fresh)
      -- `[92]`: `|X| ≤ s·def⁺(X)` against `s·def⁺(X) < |X| + s·σ(X)`, `σ(X) = 0`.
      obtain ⟨packing, _valid, _maximal, component, _present, negative, zero, bound⟩ :=
        (discharged.get (K .typeAUnsaturatedDischarge)).down
      have negative' := negative
      unfold Graph.FiniteObject.NegativeNetCharge at negative'
      rw [zero] at negative'
      omega
  | .left saturatedHistory =>
      -- `lem:typeA-port-return`
      let ports :=
        (typeAPortReturnRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          saturatedHistory (by key_fresh)
      -- Power-of-two port returns (no manuscript label), on the same saturated
      -- support and before `[93]`.
      let powerReturns :=
        (portPowerReturnRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          ports (by key_fresh)
      -- `[93]`
      match typeAVisibleEntryDichotomy (data := spineData) powerReturns
          (by key_fresh) (by key_fresh) with
      | .left visibleHistory =>
          -- `[95]`--`[107]`: the saturated exit chain on the visible arm.
          exact selectedTypeAVisibleExitChain visibleHistory
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
            (by key_fresh) (by key_fresh)
            (by key_fresh) (by key_fresh)
            (by key_fresh) (by key_fresh)
            (by key_fresh) (by key_fresh)
            (by key_fresh) (by key_fresh)
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
      | .right excessHistory =>
          -- `[94]` → `[101]`--`[107]`: the exit chain from exit `(4)` on the
          -- silent-excess arm.
          exact selectedTypeASilentExitChain excessHistory
            (by key_fresh) (by key_fresh)
            (by key_fresh) (by key_fresh)
            (by key_fresh) (by key_fresh)
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
