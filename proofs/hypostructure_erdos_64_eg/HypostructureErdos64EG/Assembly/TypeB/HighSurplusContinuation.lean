import Hypostructure.Graph.Strategy.SpineRows.FanCertificateCap
import Hypostructure.Graph.Strategy.SpineRows.HighCentreNormalForm
import Hypostructure.Graph.Strategy.SpineRows.SameCenterOpenPortCompatibility
import Hypostructure.Graph.Strategy.SpineRows.TriangularCrossShoulder
import Hypostructure.Graph.Strategy.SpineRows.TriangularFanCore
import Hypostructure.Graph.Strategy.SpineRows.TriangularFirstLanding
import Hypostructure.Graph.Strategy.SpineRows.TriangularPortReturn
import Hypostructure.Graph.Strategy.SpineRows.TriangularPortTypeBRouting
import Hypostructure.Graph.Strategy.SpineRows.TriangularShoulderCompletion
import Hypostructure.Graph.Strategy.SpineRows.TypeAReceiverRouting
import Hypostructure.Graph.Strategy.SpineRows.TypeBAssignedSupport
import Hypostructure.Graph.Strategy.SpineRows.TypeBFanDegreeDichotomy
import Hypostructure.Graph.Strategy.SpineRows.TypeBFanDegreeFourProfile
import Hypostructure.Graph.Strategy.SpineRows.TypeBFanLocalDichotomy
import HypostructureErdos64EG.Assembly.TypeB.NearCubicCertificate

/-!
# Assembly: TypeB / HighSurplusContinuation

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- **Node `[64]`: the ordinary Type B entry**, on the `[62]` yes-residual of any
arm.  `[65]` (`typeBAssignedSupportRow`: the support's assigned fan centres are
its high centres, `def:canonical-decomp`), `[67]`
(`highCentreNormalFormRow`, `lem:heavy-neighbourhood-normal-form`), the `[68]`
heavy-centre split (`typeBFanDegreeDichotomy`); on the heavy arm `[69]`
(`typeBFanLocalDichotomyRow`, `cor:heavy-center-local-dichotomy`), `[70]`
(`fanCertificateCapRow`, `lem:fan-certificate`) and the `[71]` certificate split
(`fanCertificateDichotomy`, `def:marked-typeB-fan`).  Next producers: `[72]`
(the local fan-window ledger / B2 question) on the marked arm, `[75]` (bridge
fan-mass) on the residual arm, and `[78]` (the degree-four Part VII branch) on the
`[68]` no arm.  Index-polymorphic over the arm's ledger. -/
-- EG-NODE [65] Type B assigned support: high-degree fan centers and decorated handoff data
-- EG-NODE [67] high-degree centers independent; fan neighbours cubic
-- EG-NODE [68] some center has \(d_G(h)>4\)?
-- EG-NODE [69] degree \(>4\) local dichotomy: fan-compatible open pair or \(k-2\) triangular ports gives fan-closed ports
-- EG-NODE [70] fan-safe graph, \(P_{13}\) certificate graph, and certificate-marked cap \(d_G(h)\le8\)
-- EG-NODE [71] certificate labelling present?
-- EG-NODE [75] bridge fan-mass: fan-certificate centers and B2 failures charged to assigned surplus
-- EG-NODE [78] degree-\(4\) branch: \(d_G(h)=4\)
-- EG-NODE [79] degree-\(4\) fan profile: center surplus \(1\), \(0\le c\le4\), \(D_B=c-\frac74\)
-- EG-NODE [80] certificate labelling present?
-- EG-NODE [84] fan-mass route: certificate failures and B2 failures charged to assigned surplus
noncomputable def selectedTypeBHighSurplusContinuation
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeBHighSurplus) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .bridgeless) known]
    (routingFresh : K .typeAReceiverRouting ∉ known := by simp [K_eq_iff])
    (cubicFresh : FactKeys.Has (K .cubicBaseline) known := by infer_instance)
    (assignedFresh : K .typeBAssignedSupport ∉ known := by simp [K_eq_iff])
    (fanEntryFresh : K .typeBFanEntry ∉ known := by simp [K_eq_iff])
    (normalFormFresh : K .highCentreNormalForm ∉ known := by simp [K_eq_iff])
    (heavyFresh : K .typeBFanHeavyCentre ∉ known := by simp [K_eq_iff])
    (degreeFourFresh : K .typeBFanDegreeFourCentres ∉ known := by simp [K_eq_iff])
    (localFresh : K .typeBFanLocalDichotomy ∉ known := by simp [K_eq_iff])
    (compatibilityFresh : K .sameCenterOpenPortCompatibility ∉ known := by
      simp [K_eq_iff])
    (capFresh : K .fanCertificateCap ∉ known := by simp [K_eq_iff])
    (markedFresh : K .fanCertificateMarked ∉ known := by simp [K_eq_iff])
    (residualFresh : K .fanCertificateResidual ∉ known := by simp [K_eq_iff])
    -- `[72]`--`[85]` continue on this same exact ledger.
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .negativeSupport) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    (cycleFresh : K .typeBDirectCycle ∉ known := by simp [K_eq_iff])
    (freeFresh : K .typeBDirectCycleFree ∉ known := by simp [K_eq_iff])
    (choiceFresh : K .typeBB2Choice ∉ known := by simp [K_eq_iff])
    (obstructionFresh : K .typeBOverlapObstruction ∉ known := by simp [K_eq_iff])
    (hybridFresh : K .typeBHybridEntry ∉ known := by simp [K_eq_iff])
    (ledgerFresh : K .typeBDisjointLedger ∉ known := by simp [K_eq_iff])
    (bridgeMassFresh : K .typeBBridgeMass ∉ known := by simp [K_eq_iff])
    (bridgeSublinearFresh : K .typeBBridgeSublinear ∉ known := by simp [K_eq_iff])
    (unifiedNegativeFresh : K .route8UnifiedNegative ∉ known := by simp [K_eq_iff])
    (typeAExclusionFresh : K .typeAExclusion ∉ known := by simp [K_eq_iff])
    (typeBBridgeReductionFresh : K .typeBBridgeReduction ∉ known := by
      simp [K_eq_iff])
    (piecesClassifiedFresh : K .route8PiecesClassified ∉ known := by simp [K_eq_iff])
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
    (excludedFresh : K .typeBExcluded ∉ known := by simp [K_eq_iff])
    (exclusionResidualFresh : K .typeBExclusionResidual ∉ known := by simp [K_eq_iff])
    (exclusionMassFresh : K .typeBExclusionResidualMass ∉ known := by simp [K_eq_iff])
    (obstructionMassFresh : K .typeBOverlapObstructionMass ∉ known := by simp [K_eq_iff])
    (certificateMassFresh : K .fanCertificateResidualMass ∉ known := by simp [K_eq_iff])
    (degreeFourProfileFresh : K .typeBFanDegreeFourProfile ∉ known := by simp [K_eq_iff])
    (triangularCoreFresh : K .triangularFanCore ∉ known := by simp [K_eq_iff])
    (fanClosedFresh : K .fanClosedPort ∉ known := by simp [K_eq_iff])
    (compatibleClosureFresh : K .compatiblePairFanClosure ∉ known := by simp [K_eq_iff])
    (fanClosedRoutingFresh : K .fanClosedPortTypeBRouting ∉ known := by simp [K_eq_iff])
    (compatibleRoutingFresh : K .compatiblePairTypeBRouting ∉ known := by simp [K_eq_iff])
    (shoulderCompletionFresh : K .triangularShoulderCompletion ∉ known := by simp [K_eq_iff])
    (portReturnFresh : K .triangularPortReturn ∉ known := by simp [K_eq_iff])
    (firstLandingFresh : K .triangularFirstLanding ∉ known := by simp [K_eq_iff])
    (crossShoulderFresh : K .triangularCrossShoulder ∉ known := by simp [K_eq_iff])
    (triangularRoutingFresh : K .triangularPortTypeBRouting ∉ known := by simp [K_eq_iff])
    (globalLocalBridgeFresh : K .typeBGlobalLocalBridge ∉ known := by simp [K_eq_iff])
   :
    SelectedRouteEightBoundary selected := by
  letI := cubicFresh
  let _cubicBaseline := (history.get (K .cubicBaseline)).down
  -- The common Part IX census reads the object-wide receiver routing of
  -- `[88]`.  Publish that paper fact on this literal Type B residual before
  -- adding the branch-specific fan support; no handoff carrier is needed.
  let routed :=
    (typeAReceiverRoutingRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) spineData).run
      history (by simp [K_eq_iff, routingFresh])
  let cubic := routed
  -- `[65]`: the ordinary Type B assigned support.
  let assigned :=
    (typeBAssignedSupportRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      cubic (by simp [K_eq_iff, assignedFresh, fanEntryFresh])
  -- `[67]`: `lem:heavy-neighbourhood-normal-form` at every high centre.
  let normal :=
    (highCentreNormalFormRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      assigned (by simp [K_eq_iff, normalFormFresh])
  -- `[68]`: some assigned fan centre heavy?
  match typeBFanDegreeDichotomy (data := spineData) normal
      (by simp [K_eq_iff, heavyFresh]) (by simp [K_eq_iff, degreeFourFresh]) with
  | .left heavyHistory =>
      -- `[69]`: publish `lem:same-center-open-port-compatibility`, then derive
      -- `cor:heavy-center-local-dichotomy` from that registered fact.
      let compatibleHistory :=
        (sameCenterOpenPortCompatibilityRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          heavyHistory (by simp [K_eq_iff, compatibilityFresh])
      let localDichotomy :=
        (typeBFanLocalDichotomyRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          compatibleHistory (by simp [K_eq_iff, localFresh])
      let portRouted := Assembly.Internal.selectedTypeBPortRoutingPrefix localDichotomy
        (by simp [K_eq_iff, fanClosedFresh])
        (by simp [K_eq_iff, compatibleClosureFresh])
        (by simp [K_eq_iff, fanClosedRoutingFresh])
        (by simp [K_eq_iff, compatibleRoutingFresh])
      -- `[70]`: `lem:fan-certificate`, the certificate-marked degree cap.
      let capped :=
        (fanCertificateCapRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          portRouted (by simp [K_eq_iff, capFresh])
      exact selectedTypeBNearCubicCertificateAfterPortRouting capped
        (by simp [K_eq_iff, markedFresh])
        (by simp [K_eq_iff, residualFresh])
        (by simp [K_eq_iff, certificateMassFresh])
        (by simp [K_eq_iff, cycleFresh])
        (by simp [K_eq_iff, freeFresh])
        (by simp [K_eq_iff, choiceFresh])
        (by simp [K_eq_iff, obstructionFresh])
        (by simp [K_eq_iff, hybridFresh])
        (by simp [K_eq_iff, ledgerFresh])
        (by simp [K_eq_iff, excludedFresh])
        (by simp [K_eq_iff, exclusionResidualFresh])
        (by simp [K_eq_iff, exclusionMassFresh])
        (by simp [K_eq_iff, obstructionMassFresh])
        (by simp [K_eq_iff, bridgeMassFresh])
        (by simp [K_eq_iff, bridgeSublinearFresh])
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
        (globalLocalBridgeFresh := by simp [K_eq_iff, globalLocalBridgeFresh])
  | .right degreeFourHistory =>
      -- `[78]`--`[79]`: every assigned fan centre has degree `δ + 1`; the
      -- degree-four fan profile (`cor:degree-four-local-activation`).
      let profile :=
        (typeBFanDegreeFourProfileRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          degreeFourHistory (by simp [K_eq_iff, degreeFourProfileFresh])
      let triangularCore :=
        (triangularFanCoreRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          profile (by simp [K_eq_iff, triangularCoreFresh])
      let completed :=
        (triangularShoulderCompletionRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          triangularCore (by simp [K_eq_iff, shoulderCompletionFresh])
      let returned :=
        (triangularPortReturnRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          completed (by simp [K_eq_iff, portReturnFresh])
      let firstLanded :=
        (triangularFirstLandingRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          returned (by simp [K_eq_iff, firstLandingFresh])
      let crossShouldered :=
        (triangularCrossShoulderRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          firstLanded (by simp [K_eq_iff, crossShoulderFresh])
      let portRouted := Assembly.Internal.selectedTypeBPortRoutingPrefix crossShouldered
        (by simp [K_eq_iff, fanClosedFresh])
        (by simp [K_eq_iff, compatibleClosureFresh])
        (by simp [K_eq_iff, fanClosedRoutingFresh])
        (by simp [K_eq_iff, compatibleRoutingFresh])
      let triangularRouted :=
        (triangularPortTypeBRoutingRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          portRouted (by simp [K_eq_iff, triangularRoutingFresh])
      -- `lem:fan-certificate` (the `[70]` cap, a fact of the object: every
      -- certificate-marked centre is capped by the label packing number), which
      -- `[82]`'s certificate-closed entries and the B1 budget read.
      let capped :=
        (fanCertificateCapRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          triangularRouted (by simp [K_eq_iff, capFresh])
      exact selectedTypeBNearCubicCertificateAfterPortRouting capped
        (by simp [K_eq_iff, markedFresh])
        (by simp [K_eq_iff, residualFresh])
        (by simp [K_eq_iff, certificateMassFresh])
        (by simp [K_eq_iff, cycleFresh])
        (by simp [K_eq_iff, freeFresh])
        (by simp [K_eq_iff, choiceFresh])
        (by simp [K_eq_iff, obstructionFresh])
        (by simp [K_eq_iff, hybridFresh])
        (by simp [K_eq_iff, ledgerFresh])
        (by simp [K_eq_iff, excludedFresh])
        (by simp [K_eq_iff, exclusionResidualFresh])
        (by simp [K_eq_iff, exclusionMassFresh])
        (by simp [K_eq_iff, obstructionMassFresh])
        (by simp [K_eq_iff, bridgeMassFresh])
        (by simp [K_eq_iff, bridgeSublinearFresh])
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
        (globalLocalBridgeFresh := by simp [K_eq_iff, globalLocalBridgeFresh])

end HypostructureErdos64EG
