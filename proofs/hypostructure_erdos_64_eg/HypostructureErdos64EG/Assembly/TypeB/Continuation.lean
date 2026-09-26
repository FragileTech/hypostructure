import Hypostructure.Graph.Strategy.SpineRows.CompatiblePairFanClosure
import Hypostructure.Graph.Strategy.SpineRows.CompatiblePairTypeBRouting
import Hypostructure.Graph.Strategy.SpineRows.FanClosedPort
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

/-- **The common Type B continuation `[67]`--`[85]`.**

It is run after node `[65]` on every entry: the ordinary support `[64]`, the
decorated handoff `[66]`/`[108]`, and the absorbed-germ fan data `[177]`.  It
reads only facts of the literal incoming ledger.  `[67]` is the normal form;
`[68]` decides whether some assigned centre is heavy.  The heavy arm is `[69]`:
the same-centre compatibility lemma, the fan-closed port routing, and the routed
local dichotomy (fan-compatible pair or `k - 2` triangular ports, each giving
fan-closed ports).  The degree-four arm is `[78]`--`[79]`: the degree-four
profile, the triangular fan core and its landing lemmas, and the fan-closed port
routing of `cor:degree-four-local-activation`.  Both arms enter `[70]`. -/
-- EG-NODE [67] high-degree centers independent; fan neighbours cubic
-- EG-NODE [68] some center has \(d_G(h)>4\)?
-- EG-NODE [69] degree \(>4\) local dichotomy: fan-compatible open pair or \(k-2\) triangular ports gives fan-closed ports
-- EG-NODE [78] degree-\(4\) branch: \(d_G(h)=4\)
-- EG-NODE [79] degree-\(4\) fan profile: center surplus \(1\), \(0\le c\le4\), \(D_B=c-\frac74\)
noncomputable def Assembly.Internal.selectedTypeBFanContinuation
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .typeAReceiverRouting) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .cubicBaseline) known]
    (closureFresh : closed ∉ known := by key_fresh)
    (normalFormFresh : K .highCentreNormalForm ∉ known := by key_fresh)
    (heavyFresh : K .typeBFanHeavyCentre ∉ known := by key_fresh)
    (degreeFourFresh : K .typeBFanDegreeFourCentres ∉ known := by key_fresh)
    (compatibilityFresh : K .sameCenterOpenPortCompatibility ∉ known := by
      key_fresh)
    (fanClosedFresh : K .fanClosedPort ∉ known := by key_fresh)
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
    (cycleFresh : K .typeBDirectCycle ∉ known := by key_fresh)
    (freeFresh : K .typeBDirectCycleFree ∉ known := by key_fresh)
    (hybridFresh : K .typeBHybridEntry ∉ known := by key_fresh)
    (choiceFresh : K .typeBB2Choice ∉ known := by key_fresh)
    (obstructionFresh : K .typeBOverlapObstruction ∉ known := by key_fresh)
    (ledgerFresh : K .typeBDisjointLedger ∉ known := by key_fresh)
    (excludedFresh : K .typeBExcluded ∉ known := by key_fresh)
    (exclusionResidualFresh : K .typeBExclusionResidual ∉ known := by key_fresh)
    (exclusionMassFresh : K .typeBExclusionResidualMass ∉ known := by key_fresh)
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
    (windowShadowSignatureFresh : K .windowShadowSignature ∉ known := by
      key_fresh)
    (windowShadowTailFresh : K .windowShadowSingletonTail ∉ known := by
      key_fresh)
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
    (witnessFreeFresh : K .route8UnpaidWitnessFree ∉ known := by key_fresh) :
    SelectedRouteEightBoundary selected := by
  -- `[67]`: `lem:heavy-neighbourhood-normal-form`.
  let normal := (highCentreNormalFormRow (data := spineData)).run history
    (by key_fresh)
  -- `[68]`: some assigned centre heavy?
  match typeBFanDegreeDichotomy (data := spineData) normal
      (by key_fresh) (by key_fresh) with
  | .left heavyHistory =>
      -- `[69]`: `lem:same-center-open-port-compatibility`, the fan-closed port
      -- routing, and the routed heavy-centre local dichotomy.
      let compatible := (sameCenterOpenPortCompatibilityRow (data := spineData)).run
        heavyHistory (by key_fresh)
      let fanClosed := (fanClosedPortRow (data := spineData)).run compatible
        (by key_fresh)
      let pairClosure := (compatiblePairFanClosureRow (data := spineData)).run
        fanClosed (by key_fresh)
      let fanClosedRouting := (fanClosedPortTypeBRoutingRow (data := spineData)).run
        pairClosure (by key_fresh)
      let pairRouting := (compatiblePairTypeBRoutingRow (data := spineData)).run
        fanClosedRouting (by key_fresh)
      let triangularRouting :=
        (triangularPortTypeBRoutingRow (data := spineData)).run pairRouting
          (by key_fresh)
      let localDichotomy := (typeBFanLocalDichotomyRow (data := spineData)).run
        triangularRouting (by key_fresh)
      exact Assembly.Internal.selectedTypeBCertificateContinuation localDichotomy
  | .right degreeFourHistory =>
      -- `[78]`--`[79]`: the degree-four fan profile, the triangular fan core and
      -- its landing lemmas, and the fan-closed port routing of
      -- `cor:degree-four-local-activation`.
      let profile := (typeBFanDegreeFourProfileRow (data := spineData)).run
        degreeFourHistory (by key_fresh)
      let core := (triangularFanCoreRow (data := spineData)).run profile
        (by key_fresh)
      let completed := (triangularShoulderCompletionRow (data := spineData)).run
        core (by key_fresh)
      let returned := (triangularPortReturnRow (data := spineData)).run completed
        (by key_fresh)
      let landed := (triangularFirstLandingRow (data := spineData)).run returned
        (by key_fresh)
      let crossed := (triangularCrossShoulderRow (data := spineData)).run landed
        (by key_fresh)
      let fanClosed := (fanClosedPortRow (data := spineData)).run crossed
        (by key_fresh)
      let pairClosure := (compatiblePairFanClosureRow (data := spineData)).run
        fanClosed (by key_fresh)
      let fanClosedRouting := (fanClosedPortTypeBRoutingRow (data := spineData)).run
        pairClosure (by key_fresh)
      let pairRouting := (compatiblePairTypeBRoutingRow (data := spineData)).run
        fanClosedRouting (by key_fresh)
      exact Assembly.Internal.selectedTypeBCertificateContinuation pairRouting

end HypostructureErdos64EG
