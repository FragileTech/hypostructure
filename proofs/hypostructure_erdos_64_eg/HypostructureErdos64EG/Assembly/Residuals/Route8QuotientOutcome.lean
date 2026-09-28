import HypostructureErdos64EG.Assembly.Residuals
import HypostructureErdos64EG.Assembly.Residuals.Route8Blocks

/-!
# Assembly: Residuals / Route8QuotientOutcome

Node `[187] ([348], route-8 quotient failure)` as a PRODUCT OF ARM BLOCKS.

The 1240 paths from `selectedLedgerBoundary` to the one return site
(`route8QuotientReturn` in `selectedRouteEightUnifiedResidual`,
`Assembly/RouteEight/Local.lean`) carry 1240 distinct fact sets.  Each is
exactly the 64 common keys of `Route8QuotientOutcome` together with one block
per factor of

  `5 prefix × 4 entropy × 62 continuation`,  `62 = 2·22 + 12 + 6`,

and every combination occurs (checked against the elaborated ledger of every
path).  The blocks live in `Residuals/Route8Blocks.lean`.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u

/-- **Node `[187] ([348])` as a product of arm blocks**: the generic
residual (64 common facts), one near-cubic prefix block, one entropy block,
and one net-charge continuation (Type A lane, absorbed lane, or Type B
high-surplus lane, each a nested product of its own blocks).  Totals run from
84 to 121 facts. -/
abbrev Route8QuotientOutcome_product (selected : EGInput.{u}) : Prop :=
  Route8QuotientOutcome selected ∧ Route8LanePrefix selected ∧
    EntropyArm selected ∧ NetChargeContinuation selected

theorem Route8QuotientOutcome_product.toGeneric {selected : EGInput.{u}}
    (h : Route8QuotientOutcome_product selected) :
    Route8QuotientOutcome selected :=
  h.1

/-- The return of `Route8QuotientOutcome_product`, parameterised by the arm
choices: the 64 common facts are read from the ledger by
`route8QuotientReturn`, and each factor is the arm block the path took, built
by that block's `.ret` from the same ledger (one `get` per key). -/
theorem route8QuotientProductReturn
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .returnAvoidance) known]
    [FactKeys.Has (K .noProperBaseline) known]
    [FactKeys.Has (K .slackIndependent) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .cycleRankConstraint) known]
    [FactKeys.Has (K .degreeProfileFibres) known]
    [FactKeys.Has (K .targetCompleteContextUniversality) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .windowPresent) known]
    [FactKeys.Has (K .maximalPacking) known]
    [FactKeys.Has (K .localAlgebra) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    [FactKeys.Has (K .barrierEnumeration) known]
    [FactKeys.Has (K .windowPackageSeparated) known]
    [FactKeys.Has (K .skeletonDominates) known]
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .barrierCap) known]
    [FactKeys.Has (K .coldHotEntropyCap) known]
    [FactKeys.Has (K .coldMass) known]
    [FactKeys.Has (K .coldAmbientCubic) known]
    [FactKeys.Has (K .coldStubExcess) known]
    [FactKeys.Has (K .coldAmbientCubicStubExcess) known]
    [FactKeys.Has (K .coldSelectedBranchExcess) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .boundaryDemand) known]
    [FactKeys.Has (K .stubSupply) known]
    [FactKeys.Has (K .wedgeSupply) known]
    [FactKeys.Has (K .curvatureTargetRank) known]
    [FactKeys.Has (K .exactResponseProfile) known]
    [FactKeys.Has (K .targetRankCircuit) known]
    [FactKeys.Has (K .curvatureFullRank) known]
    [FactKeys.Has (K .forcedCurvatureCost) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .netDeficiencyCap) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .coldReturnCorridors) known]
    [FactKeys.Has (K .coldCorridorState) known]
    [FactKeys.Has (K .coldFirstFailureOccurrence) known]
    [FactKeys.Has (K .coldFailureCycle) known]
    [FactKeys.Has (K .coldFailureCompression) known]
    [FactKeys.Has (K .coldHandoffTransfer) known]
    [FactKeys.Has (K .netChargeLocalization) known]
    [FactKeys.Has (K .typeBAbsorbedCharge) known]
    [FactKeys.Has (K .highCentreNormalForm) known]
    [FactKeys.Has (K .sameCenterOpenPortCompatibility) known]
    [FactKeys.Has (K .triangularShoulderCompletion) known]
    [FactKeys.Has (K .triangularPortReturn) known]
    [FactKeys.Has (K .route8BasinBurden) known]
    [FactKeys.Has (K .route8CarrierCore) known]
    [FactKeys.Has (K .typeBBridgeMass) known]
    [FactKeys.Has (K .typeBBridgeSublinear) known]
    [FactKeys.Has (K .route8UnifiedNegative) known]
    [FactKeys.Has (K .typeAExclusion) known]
    [FactKeys.Has (K .typeBBridgeReduction) known]
    [FactKeys.Has (K .route8PiecesClassified) known]
    [FactKeys.Has (K .route8ExtractedEntryCensus) known]
    [FactKeys.Has (K .typeBSublinearLedger) known]
    [FactKeys.Has (K .route8UnifiedDeficit) known]
    [FactKeys.Has (K .route8QuotientResidual) known]
    (lanePrefix : Route8LanePrefix selected)
    (entropy : EntropyArm selected)
    (continuation : NetChargeContinuation selected) :
    Route8QuotientOutcome_product selected :=
  ⟨route8QuotientReturn history, lanePrefix, entropy, continuation⟩

end HypostructureErdos64EG
