import Hypostructure.Graph.Strategy.SpineRows.CompatiblePairFanClosure
import Hypostructure.Graph.Strategy.SpineRows.CompatiblePairTypeBRouting
import Hypostructure.Graph.Strategy.SpineRows.FanCertificateCap
import Hypostructure.Graph.Strategy.SpineRows.FanClosedPortTypeBRouting
import Hypostructure.Graph.Strategy.SpineRows.HighCentreNormalForm
import Hypostructure.Graph.Strategy.SpineRows.SameCenterOpenPortCompatibility
import Hypostructure.Graph.Strategy.SpineRows.TriangularCrossShoulder
import Hypostructure.Graph.Strategy.SpineRows.TriangularFanCore
import Hypostructure.Graph.Strategy.SpineRows.TriangularFirstLanding
import Hypostructure.Graph.Strategy.SpineRows.TriangularPortReturn
import Hypostructure.Graph.Strategy.SpineRows.TriangularPortTypeBRouting
import Hypostructure.Graph.Strategy.SpineRows.TriangularShoulderCompletion
import Hypostructure.Graph.Strategy.SpineRows.TypeBFanDegreeDichotomy
import Hypostructure.Graph.Strategy.SpineRows.TypeBFanDegreeFourProfile
import Hypostructure.Graph.Strategy.SpineRows.TypeBFanLocalDichotomy
import HypostructureErdos64EG.Assembly.TypeB.Internal.Certificate

/-!
# Assembly: TypeB / Continuation

The one composition of Parts VI--VII, generic over the incoming ledger.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

set_option maxHeartbeats 8000000 in
/-- **The common Type B continuation `[67]`--`[85]`.**

It is run after node `[65]` on every entry: the ordinary support `[64]`, the
decorated handoff `[66]`/`[108]`, and the absorbed-germ fan data `[177]`.  It
reads only facts of the literal incoming ledger.  `[67]` is the normal form;
`[68]` reads the node-`[65]` entry and decides whether some assigned centre of
its Type B support is heavy.  The heavy arm is `[69]`: the same-centre
compatibility lemma, the triangular fan core and its landing lemmas (stated at a
heavy centre), the fan-closed port routing, and the routed local dichotomy
(fan-compatible pair or `k - 2` triangular ports, each giving fan-closed ports).
The degree-four arm is `[78]`--`[79]`: the degree-four profile and the
fan-closed port routing of `cor:degree-four-local-activation`.  Both arms enter
`[70]`. -/
-- EG-NODE [67] high-degree centers independent; fan neighbours cubic
-- EG-NODE [68] some center has \(d_G(h)>4\)?
-- EG-NODE [69] degree \(>4\) local dichotomy: fan-compatible open pair or \(k-2\) triangular ports gives fan-closed ports
-- EG-NODE [78] degree-\(4\) branch: \(d_G(h)=4\)
-- EG-NODE [70] fan-safe graph, \(P_{13}\) certificate graph, and certificate-marked cap \(d_G(h)\le8\)
-- EG-NODE [79] degree-\(4\) fan profile: center surplus \(1\), \(0\le c\le4\), \(D_B=c-\frac74\)
noncomputable def Assembly.Internal.selectedTypeBFanContinuation
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeBFanEntry) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .cubicBaseline) known]
    (closureFresh : closed ∉ known := by key_fresh)
    (normalFormFresh : K .highCentreNormalForm ∉ known := by key_fresh)
    (heavyFresh : K .typeBFanHeavyCentre ∉ known := by key_fresh)
    (degreeFourFresh : K .typeBFanDegreeFourCentres ∉ known := by key_fresh)
    (compatibilityFresh : K .sameCenterOpenPortCompatibility ∉ known := by
      key_fresh)
    (route8EntryFresh : K .typeBRoute8Entry ∉ known := by key_fresh)
    (compatibleClosureFresh : K .compatiblePairFanClosure ∉ known := by
      key_fresh)
    (fanClosedRoutingFresh : K .fanClosedPortTypeBRouting ∉ known := by
      key_fresh)
    (compatibleRoutingFresh : K .compatiblePairTypeBRouting ∉ known := by
      key_fresh)
    (triangularRoutingFresh : K .triangularPortTypeBRouting ∉ known := by
      key_fresh)
    (localFresh : K .typeBFanLocalDichotomy ∉ known := by key_fresh)
    (profileFresh : K .typeBFanDegreeFourProfile ∉ known := by key_fresh)
    (triangularCoreFresh : K .triangularFanCore ∉ known := by key_fresh)
    (shoulderCompletionFresh : K .triangularShoulderCompletion ∉ known := by
      key_fresh)
    (portReturnFresh : K .triangularPortReturn ∉ known := by key_fresh)
    (firstLandingFresh : K .triangularFirstLanding ∉ known := by key_fresh)
    (crossShoulderFresh : K .triangularCrossShoulder ∉ known := by key_fresh)
    (capFresh : K .fanCertificateCap ∉ known := by key_fresh)
    (markedFresh : K .fanCertificateMarked ∉ known := by key_fresh)
    (residualFresh : K .fanCertificateResidual ∉ known := by key_fresh)
    (certificateMassFresh : K .fanCertificateResidualMass ∉ known := by
      key_fresh)
    (freeFresh : K .typeBDirectCycleFree ∉ known := by key_fresh)
    (hybridFresh : K .typeBHybridEntry ∉ known := by key_fresh)
    (choiceFresh : K .typeBB2Choice ∉ known := by key_fresh)
    (obstructionFresh : K .typeBOverlapObstruction ∉ known := by key_fresh)
    (ledgerFresh : K .typeBDisjointLedger ∉ known := by key_fresh)
    (excludedFresh : K .typeBExcluded ∉ known := by key_fresh)
    (exclusionResidualFresh : K .typeBExclusionResidual ∉ known := by key_fresh)
    (degreeFourLedgerFresh : K .typeBDegreeFourLedger ∉ known := by key_fresh)
    (degreeFourOverlapFresh : K .typeBDegreeFourOverlap ∉ known := by key_fresh)
    (degreeFourClosedFresh : K .typeBDegreeFourClosed ∉ known := by key_fresh)
    (globalLocalBridgeFresh : K .typeBGlobalLocalBridge ∉ known := by
      key_fresh)
    (obstructionMassFresh : K .typeBOverlapObstructionMass ∉ known := by
      key_fresh)
    (bridgeMassFresh : K .typeBBridgeMass ∉ known := by key_fresh)
    (bridgeSublinearFresh : K .typeBBridgeSublinear ∉ known := by key_fresh)
    (unifiedNegativeFresh : K .route8UnifiedNegative ∉ known := by key_fresh)
    (typeAExclusionFresh : K .typeAExclusion ∉ known := by key_fresh)
    (typeBBridgeReductionFresh : K .typeBBridgeReduction ∉ known := by
      key_fresh)
    (piecesClassifiedFresh : K .route8PiecesClassified ∉ known := by
      key_fresh)
    (sublinearLedgerFresh : K .typeBSublinearLedger ∉ known := by key_fresh)
    (sublinearResidualFresh : K .typeBSublinearResidual ∉ known := by
      key_fresh)
    (unifiedDeficitFresh : K .route8UnifiedDeficit ∉ known := by key_fresh)
    (quotientFreeFresh : K .route8QuotientFree ∉ known := by key_fresh)
    (quotientResidualFresh : K .route8QuotientResidual ∉ known := by
      key_fresh)
    (unifiedCensusFresh : K .route8UnifiedEntryCensus ∉ known := by
      key_fresh)
    (extractedCensusFresh : K .route8ExtractedEntryCensus ∉ known := by
      key_fresh)
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known := by
      key_fresh)
    (peelingFresh : K .route8PeelingDescent ∉ known := by key_fresh)
    (stageFailedFresh : K .route8StageRateFailed ∉ known := by key_fresh)
    (demandLedgerFresh : K .route8DemandLedger ∉ known := by key_fresh)
    (demandAbsorptionFresh : K .route8DemandAbsorption ∉ known := by
      key_fresh)
    (openBoundarySaturatedFresh : K .route8OpenBoundarySaturated ∉ known := by
      key_fresh)
    (demandUnitCountFresh : K .route8DemandUnitCount ∉ known := by key_fresh)
    (windowBlockersFresh : K .route8WindowBlockers ∉ known := by key_fresh)
    (windowShadowCycleFresh : K .windowShadowHitCycle ∉ known := by
      key_fresh)
    (windowShadowExcludedFresh : K .windowShadowHitExcluded ∉ known := by
      key_fresh)
    (demandResidualFresh : K .route8StageRate ∉ known := by
      key_fresh)
    (unpaidExitFourFresh : K .route8UnpaidExitFourResidual ∉ known := by
      key_fresh)
    (unifiedVisibleFresh : K .route8UnifiedVisibleResidual ∉ known := by
      key_fresh)
    (unifiedVisibleOverloadFresh : K .route8UnifiedVisibleOverload ∉ known := by
      key_fresh)
    (jointBalanceFresh : K .route8JointBalance ∉ known := by key_fresh)
    (unifiedTerminalFresh : K .route8UnifiedTwoCarrierExit ∉ known := by key_fresh)
    (unpaidTwoFresh : K .route8UnpaidTwoCarrier ∉ known := by key_fresh)
    (witnessFreeFresh : K .route8UnpaidWitnessFree ∉ known := by key_fresh)
    (burdenFresh : K .route8BasinBurden ∉ known := by key_fresh)
    (carrierCoreFresh : K .route8CarrierCore ∉ known := by key_fresh)
    [FactKeys.Has (K .barrierCap) known]
    [FactKeys.Has (K .barrierEnumeration) known]
    [FactKeys.Has (K .boundaryDemand) known]
    [FactKeys.Has (K .coldAmbientCubic) known]
    [FactKeys.Has (K .coldAmbientCubicStubExcess) known]
    [FactKeys.Has (K .coldCorridorState) known]
    [FactKeys.Has (K .coldFailureCompression) known]
    [FactKeys.Has (K .coldFailureCycle) known]
    [FactKeys.Has (K .coldFirstFailureOccurrence) known]
    [FactKeys.Has (K .coldHandoffTransfer) known]
    [FactKeys.Has (K .coldHotEntropyCap) known]
    [FactKeys.Has (K .coldMass) known]
    [FactKeys.Has (K .coldReturnCorridors) known]
    [FactKeys.Has (K .coldSelectedBranchExcess) known]
    [FactKeys.Has (K .coldStubExcess) known]
    [FactKeys.Has (K .curvatureFullRank) known]
    [FactKeys.Has (K .curvatureTargetRank) known]
    [FactKeys.Has (K .cycleRankConstraint) known]
    [FactKeys.Has (K .degreeProfileFibres) known]
    [FactKeys.Has (K .exactResponseProfile) known]
    [FactKeys.Has (K .forcedCurvatureCost) known]
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .localAlgebra) known]
    [FactKeys.Has (K .maximalPacking) known]
    [FactKeys.Has (K .netChargeLocalization) known]
    [FactKeys.Has (K .netDeficiencyCap) known]
    [FactKeys.Has (K .noProperBaseline) known]
    [FactKeys.Has (K .returnAvoidance) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .skeletonDominates) known]
    [FactKeys.Has (K .slackIndependent) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    [FactKeys.Has (K .stubSupply) known]
    [FactKeys.Has (K .targetCompleteContextUniversality) known]
    [FactKeys.Has (K .targetRankCircuit) known]
    [FactKeys.Has (K .typeBAbsorbedCharge) known]
    [FactKeys.Has (K .wedgeSupply) known]
    [FactKeys.Has (K .windowPackageSeparated) known]
    [FactKeys.Has (K .windowPresent) known] :
    SelectedRouteEightBoundary selected := by
  -- `[67]`: `lem:heavy-neighbourhood-normal-form`.
  let normal := (highCentreNormalFormRow (data := spineData)).run history
    (by key_fresh)
  -- `[68]`: some assigned centre heavy?
  match typeBFanDegreeDichotomy (data := spineData) normal
      (by key_fresh) (by key_fresh) with
  | .left heavyHistory =>
      -- `[69]`: `lem:same-center-open-port-compatibility`; the triangular fan
      -- core and its landing lemmas (`def:triangular-fan-core`,
      -- `lem:triangular-shoulder-completion`, `lem:triangular-port-return`,
      -- `lem:triangular-first-landing`, `lem:triangular-cross-shoulder`, all
      -- stated at a heavy centre, tex 2378--2521); the fan-closed port routing;
      -- and the routed heavy-centre local dichotomy.
      let compatible := (sameCenterOpenPortCompatibilityRow (data := spineData)).run
        heavyHistory (by key_fresh)
      let core := (triangularFanCoreRow (data := spineData)).run compatible
        (by key_fresh)
      let completed := (triangularShoulderCompletionRow (data := spineData)).run
        core (by key_fresh)
      let returned := (triangularPortReturnRow (data := spineData)).run completed
        (by key_fresh)
      let landed := (triangularFirstLandingRow (data := spineData)).run returned
        (by key_fresh)
      let crossed := (triangularCrossShoulderRow (data := spineData)).run landed
        (by key_fresh)
      let pairClosure := (compatiblePairFanClosureRow (data := spineData)).run
        crossed (by key_fresh)
      let fanClosedRouting := (fanClosedPortTypeBRoutingRow (data := spineData)).run
        pairClosure (by key_fresh)
      let pairRouting := (compatiblePairTypeBRoutingRow (data := spineData)).run
        fanClosedRouting (by key_fresh)
      let triangularRouting :=
        (triangularPortTypeBRoutingRow (data := spineData)).run pairRouting
          (by key_fresh)
      let localDichotomy := (typeBFanLocalDichotomyRow (data := spineData)).run
        triangularRouting (by key_fresh)
      -- `[70]`: the fan-safe graph and the certificate-marked cap at the Type B
      -- support of the `[69]` fact.
      let capped := (fanCertificateCapRow (data := spineData)).run
        localDichotomy (by key_fresh)
      exact Assembly.Internal.selectedTypeBCertificateContinuation capped
        none
  | .right degreeFourHistory =>
      -- `[78]`--`[79]`: the degree-four fan profile and the fan-closed port
      -- routing of `cor:degree-four-local-activation` (tex 2336): alternative
      -- (i) routes by `cor:compatible-pair-typeB-routing`, alternative (ii) by
      -- `prop:fan-closed-port-typeB-routing` with `r = 2`.
      let profileOnly := (typeBFanDegreeFourProfileRow (data := spineData)).run
        degreeFourHistory (by key_fresh)
      -- The same-centre compatibility and the triangular landing lemmas of
      -- `[69]` are facts of G on this arm too.
      let compatible := (sameCenterOpenPortCompatibilityRow (data := spineData)).run
        profileOnly (by key_fresh)
      let completed := (triangularShoulderCompletionRow (data := spineData)).run
        compatible (by key_fresh)
      let profile := (triangularPortReturnRow (data := spineData)).run completed
        (by key_fresh)
      let pairClosure := (compatiblePairFanClosureRow (data := spineData)).run
        profile (by key_fresh)
      let fanClosedRouting := (fanClosedPortTypeBRoutingRow (data := spineData)).run
        pairClosure (by key_fresh)
      let pairRouting := (compatiblePairTypeBRoutingRow (data := spineData)).run
        fanClosedRouting (by key_fresh)
      -- `[70]`: the fan-safe graph and the certificate-marked cap at the Type B
      -- support of the `[79]` fact.
      let capped := (degreeFourFanCertificateCapRow (data := spineData)).run
        pairRouting (by key_fresh)
      exact Assembly.Internal.selectedTypeBCertificateContinuation capped
        (some inferInstance)

end HypostructureErdos64EG
