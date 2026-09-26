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
    (routingFresh : K .typeAReceiverRouting ∉ known := by key_fresh)
    (cubicFresh : FactKeys.Has (K .cubicBaseline) known := by infer_instance)
    (assignedFresh : K .typeBAssignedSupport ∉ known := by key_fresh)
    (fanEntryFresh : K .typeBFanEntry ∉ known := by key_fresh)
    (normalFormFresh : K .highCentreNormalForm ∉ known := by key_fresh)
    (heavyFresh : K .typeBFanHeavyCentre ∉ known := by key_fresh)
    (degreeFourFresh : K .typeBFanDegreeFourCentres ∉ known := by key_fresh)
    (localFresh : K .typeBFanLocalDichotomy ∉ known := by key_fresh)
    (compatibilityFresh : K .sameCenterOpenPortCompatibility ∉ known := by
      key_fresh)
    (capFresh : K .fanCertificateCap ∉ known := by key_fresh)
    (markedFresh : K .fanCertificateMarked ∉ known := by key_fresh)
    (residualFresh : K .fanCertificateResidual ∉ known := by key_fresh)
    -- `[72]`--`[85]` continue on this same exact ledger.
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .negativeSupport) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    (cycleFresh : K .typeBDirectCycle ∉ known := by key_fresh)
    (freeFresh : K .typeBDirectCycleFree ∉ known := by key_fresh)
    (choiceFresh : K .typeBB2Choice ∉ known := by key_fresh)
    (obstructionFresh : K .typeBOverlapObstruction ∉ known := by key_fresh)
    (hybridFresh : K .typeBHybridEntry ∉ known := by key_fresh)
    (ledgerFresh : K .typeBDisjointLedger ∉ known := by key_fresh)
    (bridgeMassFresh : K .typeBBridgeMass ∉ known := by key_fresh)
    (bridgeSublinearFresh : K .typeBBridgeSublinear ∉ known := by key_fresh)
    (unifiedNegativeFresh : K .route8UnifiedNegative ∉ known := by key_fresh)
    (typeAExclusionFresh : K .typeAExclusion ∉ known := by key_fresh)
    (typeBBridgeReductionFresh : K .typeBBridgeReduction ∉ known := by
      key_fresh)
    (piecesClassifiedFresh : K .route8PiecesClassified ∉ known := by key_fresh)
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
    (excludedFresh : K .typeBExcluded ∉ known := by key_fresh)
    (exclusionResidualFresh : K .typeBExclusionResidual ∉ known := by key_fresh)
    (exclusionMassFresh : K .typeBExclusionResidualMass ∉ known := by key_fresh)
    (obstructionMassFresh : K .typeBOverlapObstructionMass ∉ known := by key_fresh)
    (certificateMassFresh : K .fanCertificateResidualMass ∉ known := by key_fresh)
    (degreeFourProfileFresh : K .typeBFanDegreeFourProfile ∉ known := by key_fresh)
    (triangularCoreFresh : K .triangularFanCore ∉ known := by key_fresh)
    (fanClosedFresh : K .fanClosedPort ∉ known := by key_fresh)
    (compatibleClosureFresh : K .compatiblePairFanClosure ∉ known := by key_fresh)
    (fanClosedRoutingFresh : K .fanClosedPortTypeBRouting ∉ known := by key_fresh)
    (compatibleRoutingFresh : K .compatiblePairTypeBRouting ∉ known := by key_fresh)
    (shoulderCompletionFresh : K .triangularShoulderCompletion ∉ known := by key_fresh)
    (portReturnFresh : K .triangularPortReturn ∉ known := by key_fresh)
    (firstLandingFresh : K .triangularFirstLanding ∉ known := by key_fresh)
    (crossShoulderFresh : K .triangularCrossShoulder ∉ known := by key_fresh)
    (triangularRoutingFresh : K .triangularPortTypeBRouting ∉ known := by key_fresh)
    (globalLocalBridgeFresh : K .typeBGlobalLocalBridge ∉ known := by key_fresh)
    (unpaidTwoFresh : K .route8UnpaidTwoCarrier ∉ known := by key_fresh)
    (witnessFreeFresh : K .route8UnpaidWitnessFree ∉ known := by key_fresh)
    (route8ClosureFresh : closed ∉ known := by key_fresh)
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
      history (by key_fresh)
  let cubic := routed
  -- `[65]`: the ordinary Type B assigned support.
  let assigned :=
    (typeBAssignedSupportRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      cubic (by key_fresh)
  -- `[67]`: `lem:heavy-neighbourhood-normal-form` at every high centre.
  let normal :=
    (highCentreNormalFormRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      assigned (by key_fresh)
  -- `[68]`: some assigned fan centre heavy?
  match typeBFanDegreeDichotomy (data := spineData) normal
      (by key_fresh) (by key_fresh) with
  | .left heavyHistory =>
      -- `[69]`: publish `lem:same-center-open-port-compatibility`, then derive
      -- `cor:heavy-center-local-dichotomy` from that registered fact.
      let compatibleHistory :=
        (sameCenterOpenPortCompatibilityRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          heavyHistory (by key_fresh)
      let localDichotomy :=
        (typeBFanLocalDichotomyRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          compatibleHistory (by key_fresh)
      let portRouted := Assembly.Internal.selectedTypeBPortRoutingPrefix localDichotomy
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
      -- `[70]`: `lem:fan-certificate`, the certificate-marked degree cap.
      let capped :=
        (fanCertificateCapRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          portRouted (by key_fresh)
      exact selectedTypeBNearCubicCertificateAfterPortRouting capped
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
        (globalLocalBridgeFresh := by key_fresh)
  | .right degreeFourHistory =>
      -- `[78]`--`[79]`: every assigned fan centre has degree `δ + 1`; the
      -- degree-four fan profile (`cor:degree-four-local-activation`).
      let profile :=
        (typeBFanDegreeFourProfileRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          degreeFourHistory (by key_fresh)
      let triangularCore :=
        (triangularFanCoreRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          profile (by key_fresh)
      let completed :=
        (triangularShoulderCompletionRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          triangularCore (by key_fresh)
      let returned :=
        (triangularPortReturnRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          completed (by key_fresh)
      let firstLanded :=
        (triangularFirstLandingRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          returned (by key_fresh)
      let crossShouldered :=
        (triangularCrossShoulderRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          firstLanded (by key_fresh)
      let portRouted := Assembly.Internal.selectedTypeBPortRoutingPrefix crossShouldered
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
      let triangularRouted :=
        (triangularPortTypeBRoutingRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          portRouted (by key_fresh)
      -- `lem:fan-certificate` (the `[70]` cap, a fact of the object: every
      -- certificate-marked centre is capped by the label packing number), which
      -- `[82]`'s certificate-closed entries and the B1 budget read.
      let capped :=
        (fanCertificateCapRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          triangularRouted (by key_fresh)
      exact selectedTypeBNearCubicCertificateAfterPortRouting capped
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
        (globalLocalBridgeFresh := by key_fresh)

end HypostructureErdos64EG
