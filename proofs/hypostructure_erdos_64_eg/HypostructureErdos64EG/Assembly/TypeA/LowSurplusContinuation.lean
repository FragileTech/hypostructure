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
    (boundedFresh : K .typeABoundedSupport ∉ known := by simp [K_eq_iff])
    (routingFresh : K .typeAReceiverRouting ∉ known := by simp [K_eq_iff])
    (saturatedFresh : K .typeASaturatedReceiver ∉ known := by simp [K_eq_iff])
    (unsaturatedFresh : K .typeAUnsaturatedReceivers ∉ known := by simp [K_eq_iff])
    (dischargeFresh : K .typeAUnsaturatedDischarge ∉ known := by simp [K_eq_iff])
    (portFresh : K .typeAPortReturn ∉ known := by simp [K_eq_iff])
    (powerReturnFresh : K .portPowerReturn ∉ known := by simp [K_eq_iff])
    (visibleFresh : K .typeAVisibleEntry ∉ known := by simp [K_eq_iff])
    (excessFresh : K .typeAVisibleFirstExcess ∉ known := by simp [K_eq_iff])
    -- exits `(1)`--`(3)`, `[95]`--`[100]`
    [FactKeys.Has (K .returnAvoidance) known]
    (returnFresh : K .typeAExitOneReturn ∉ known := by simp [K_eq_iff])
    (oneFreeFresh : K .typeAExitOneFree ∉ known := by simp [K_eq_iff])
    (thetaFresh : K .typeAExitTwoTheta ∉ known := by simp [K_eq_iff])
    (twoFreeFresh : K .typeAExitTwoFree ∉ known := by simp [K_eq_iff])
    (collisionFresh : K .typeAExitThreeCollision ∉ known := by simp [K_eq_iff])
    (threeFreeFresh : K .typeAExitThreeFree ∉ known := by simp [K_eq_iff])
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
    -- `[108]` → Type B `[65]` (decorated) and `[109]` → Part IX `[110]`--`[116]`.
    [FactKeys.Has (K .largeBudgetResidual) known]
    (decoratedFresh : K .typeBDecoratedAssignedSupport ∉ known := by simp [K_eq_iff])
    (cubicBaselineFresh : FactKeys.Has (K .cubicBaseline) known := by infer_instance)
    (normalFormFresh : K .highCentreNormalForm ∉ known := by simp [K_eq_iff])
    (decoratedHeavyFresh : K .typeBFanHeavyCentre ∉ known := by simp [K_eq_iff])
    (decoratedDegreeFourFresh : K .typeBFanDegreeFourCentres ∉ known := by simp [K_eq_iff])
    (decoratedLocalFresh : K .typeBFanLocalDichotomy ∉ known := by simp [K_eq_iff])
    (decoratedCompatibilityFresh :
      K .sameCenterOpenPortCompatibility ∉ known := by simp [K_eq_iff])
    (decoratedProfileFresh : K .typeBFanDegreeFourProfile ∉ known := by simp [K_eq_iff])
    (decoratedTriangularCoreFresh : K .triangularFanCore ∉ known := by simp [K_eq_iff])
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
    (piecesClassifiedFresh : K .route8PiecesClassified ∉ known := by
      simp [K_eq_iff])
    (sublinearLedgerFresh : K .typeBSublinearLedger ∉ known := by simp [K_eq_iff])
    (sublinearResidualFresh : K .typeBSublinearResidual ∉ known := by simp [K_eq_iff])
    (unifiedDeficitFresh : K .route8UnifiedDeficit ∉ known := by simp [K_eq_iff])
    (quotientFreeFresh : K .route8QuotientFree ∉ known := by simp [K_eq_iff])
    (quotientResidualFresh : K .route8QuotientResidual ∉ known := by simp [K_eq_iff])
    (unifiedCensusFresh : K .route8UnifiedEntryCensus ∉ known := by simp [K_eq_iff])
    (extractedCensusFresh : K .route8ExtractedEntryCensus ∉ known := by
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
    (decoratedGlobalLocalBridgeFresh : K .typeBGlobalLocalBridge ∉ known := by simp [K_eq_iff])
    (fanClosedFresh : K .fanClosedPort ∉ known := by simp [K_eq_iff])
    (compatibleClosureFresh : K .compatiblePairFanClosure ∉ known := by simp [K_eq_iff])
    (fanClosedRoutingFresh : K .fanClosedPortTypeBRouting ∉ known := by simp [K_eq_iff])
    (compatibleRoutingFresh : K .compatiblePairTypeBRouting ∉ known := by simp [K_eq_iff])
    (shoulderCompletionFresh : K .triangularShoulderCompletion ∉ known := by simp [K_eq_iff])
    (portReturnFresh : K .triangularPortReturn ∉ known := by simp [K_eq_iff])
    (firstLandingFresh : K .triangularFirstLanding ∉ known := by simp [K_eq_iff])
    (crossShoulderFresh : K .triangularCrossShoulder ∉ known := by simp [K_eq_iff])
    (triangularRoutingFresh : K .triangularPortTypeBRouting ∉ known := by simp [K_eq_iff])
    [FactKeys.Has (K .negativeSupport) known]
    (closureFresh : closed ∉ known := by simp [K_eq_iff])
    (silentFourFreeFresh : K .typeASilentExitFourFree ∉ known := by
      simp [K_eq_iff])
    (silentFiveFreeFresh : K .typeASilentExitFiveFree ∉ known := by
      simp [K_eq_iff])
    (silentSixFreeFresh : K .typeASilentExitSixFree ∉ known := by
      simp [K_eq_iff])
    (silentSevenFreeFresh : K .typeASilentExitSevenFree ∉ known := by
      simp [K_eq_iff]) :
    SelectedRouteEightBoundary selected := by
  letI := cubicBaselineFresh
  let _cubicBaseline := (history.get (K .cubicBaseline)).down
  -- `[87]`: the selected incoming Type A piece is P13-free, has diameter at
  -- most 11, and has at most 6142 vertices.
  let bounded :=
    (typeABoundedSupportRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [K_eq_iff, boundedFresh])
  -- `[88]`
  let routed :=
    (typeAReceiverRoutingRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) spineData).run
      bounded (by simp [K_eq_iff, routingFresh])
  -- `[89]`
  match typeASaturationDichotomy (data := spineData) routed
      (by simp [K_eq_iff, saturatedFresh]) (by simp [K_eq_iff, unsaturatedFresh]) with
  | .right unsaturatedHistory =>
      -- `[90]`--`[91]`
      let discharged :=
        (typeAUnsaturatedDischargeRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          unsaturatedHistory (by simp [K_eq_iff, dischargeFresh])
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
          saturatedHistory (by simp [K_eq_iff, portFresh])
      -- Power-of-two port returns (no manuscript label), on the same saturated
      -- support and before `[93]`.
      let powerReturns :=
        (portPowerReturnRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          ports (by simp [K_eq_iff, powerReturnFresh])
      -- `[93]`
      match typeAVisibleEntryDichotomy (data := spineData) powerReturns
          (by simp [K_eq_iff, visibleFresh]) (by simp [K_eq_iff, excessFresh]) with
      | .left visibleHistory =>
          -- `[95]`--`[107]`: the saturated exit chain on the visible arm.
          exact selectedTypeAVisibleExitChain visibleHistory
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
            (by simp [K_eq_iff, returnFresh]) (by simp [K_eq_iff, oneFreeFresh])
            (by simp [K_eq_iff, thetaFresh]) (by simp [K_eq_iff, twoFreeFresh])
            (by simp [K_eq_iff, collisionFresh]) (by simp [K_eq_iff, threeFreeFresh])
            (by simp [K_eq_iff, entryFresh]) (by simp [K_eq_iff, descentFresh])
            (by simp [K_eq_iff, exitFourFresh]) (by simp [K_eq_iff, exitFourFreeFresh])
            (by simp [K_eq_iff, peeledFresh]) (by simp [K_eq_iff, dischargedFresh])
            (by simp [K_eq_iff, fiveFresh]) (by simp [K_eq_iff, fiveFreeFresh])
            (by simp [K_eq_iff, sixFresh]) (by simp [K_eq_iff, sixFreeFresh])
            (by simp [K_eq_iff, sixProperFresh]) (by simp [K_eq_iff, sixGlobalFresh])
            (by simp [K_eq_iff, sevenProducedFresh]) (by simp [K_eq_iff, sevenFreeFresh])
            (by simp [K_eq_iff, sevenHandoffFresh]) (by simp [K_eq_iff, decoratedFresh])
            (by infer_instance) (by simp [K_eq_iff, normalFormFresh]) (by simp [K_eq_iff, decoratedHeavyFresh]) (by simp [K_eq_iff, decoratedDegreeFourFresh]) (by simp [K_eq_iff, decoratedLocalFresh]) (by simp [K_eq_iff, decoratedCompatibilityFresh]) (by simp [K_eq_iff, decoratedProfileFresh]) (by simp [K_eq_iff, decoratedTriangularCoreFresh]) (by simp [K_eq_iff, fanCapFresh]) (by simp [K_eq_iff, decoratedMarkedFresh]) (by simp [K_eq_iff, decoratedResidualFresh]) (by simp [K_eq_iff, decoratedCertificateMassFresh]) (by simp [K_eq_iff, decoratedCycleFresh]) (by simp [K_eq_iff, decoratedFreeFresh]) (by simp [K_eq_iff, decoratedFanEntryFresh]) (by simp [K_eq_iff, decoratedB2ChoiceFresh]) (by simp [K_eq_iff, decoratedB2ObstructionFresh]) (by simp [K_eq_iff, decoratedHybridFresh]) (by simp [K_eq_iff, decoratedLedgerFresh]) (by simp [K_eq_iff, decoratedBridgeMassFresh]) (by simp [K_eq_iff, decoratedBridgeSublinearFresh])
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
            (closureFresh := by simp [K_eq_iff, closureFresh])
      | .right excessHistory =>
          -- `[94]` → `[101]`--`[107]`: the exit chain from exit `(4)` on the
          -- silent-excess arm.
          exact selectedTypeASilentExitChain excessHistory
            (by simp [K_eq_iff, entryFresh]) (by simp [K_eq_iff, descentFresh])
            (by simp [K_eq_iff, exitFourFresh]) (by simp [K_eq_iff, exitFourFreeFresh])
            (by simp [K_eq_iff, peeledFresh]) (by simp [K_eq_iff, dischargedFresh])
            (by simp [K_eq_iff, fiveFresh]) (by simp [K_eq_iff, fiveFreeFresh])
            (by simp [K_eq_iff, sixFresh]) (by simp [K_eq_iff, sixFreeFresh])
            (by simp [K_eq_iff, sixProperFresh]) (by simp [K_eq_iff, sixGlobalFresh])
            (by simp [K_eq_iff, sevenProducedFresh]) (by simp [K_eq_iff, sevenFreeFresh])
            (by simp [K_eq_iff, sevenHandoffFresh]) (by simp [K_eq_iff, decoratedFresh])
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
            (closureFresh := by simp [K_eq_iff, closureFresh])
            (silentFourFreeFresh := by simp [K_eq_iff, silentFourFreeFresh])
            (silentFiveFreeFresh := by simp [K_eq_iff, silentFiveFreeFresh])
            (silentSixFreeFresh := by simp [K_eq_iff, silentSixFreeFresh])
            (silentSevenFreeFresh := by simp [K_eq_iff, silentSevenFreeFresh])

end HypostructureErdos64EG
