import HypostructureErdos64EG.Assembly.Residuals
import HypostructureErdos64EG.Assembly.Residuals.Route8Blocks

/-!
# Assembly: Residuals / Route8JointBalanceOutcome

Node `[186]` as a PRODUCT OF ARM BLOCKS.

The 750 paths from `selectedLedgerBoundary` to the one return site
(`route8JointBalanceReturn` in `selectedRouteEightUnifiedResidual`,
`Assembly/RouteEight/Local.lean`) carry 750 distinct fact sets.  Each is
exactly the 80 common keys of `Route8JointBalanceOutcome` together with one
block per factor of

  `15 lane entries × 50 continuation`,  `50 = 2·22 + 6`,

where the lane entry (`Route8LaneEntry`) is `3 prefix × 4 entropy` or the
`[161]` prefix with one of the 3 low-entropy arms: the near-cubic route
"unrealized, `τ(θ) ≥ 1/4`, `θ < 1/78`" is closed at `[146]`, and the `[161]`
route with high entropy is closed at `[53]`,

and every combination occurs (checked against the elaborated ledger of every
path).  These are the same factors as `Route8QuotientOutcome`: both residuals
are returned from the same composition on the same incoming ledger, [186] on
the quotient-free arm after `[123]`, `[181]` and `[183]`--`[185]`.  The blocks
live in `Residuals/Route8Blocks.lean`.
The absorbed lane `[174]`--`[177]` contributes no path: `[173]`'s no-arm is
closed at the node against the private-carrier rate `K .route8Rate`
(`instIncompatibleExactCollisionFailsRoute8Rate`).
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u

/-- **Node `[186]` as a product of arm blocks**: the generic residual (80
common facts), one lane entry (a near-cubic prefix block with an entropy
block), and one net-charge continuation (Type A lane or Type B high-surplus
lane, each a nested product of its own blocks).  Totals run from 100 to 137
facts. -/
abbrev Route8JointBalanceOutcome_product (selected : EGInput.{u}) : Prop :=
  Route8JointBalanceOutcome selected ∧ Route8LaneEntry selected ∧
    NetChargeContinuation selected

theorem Route8JointBalanceOutcome_product.toGeneric {selected : EGInput.{u}}
    (h : Route8JointBalanceOutcome_product selected) :
    Route8JointBalanceOutcome selected :=
  h.1

/-- The return of `Route8JointBalanceOutcome_product`, parameterised by the
arm choices: the 80 common facts are read from the ledger by
`route8JointBalanceReturn`, and each factor is the arm block the path took,
built by that block's `.ret` from the same ledger (one `get` per key). -/
theorem route8JointBalanceProductReturn
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .minDegreeBaseline) known]
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
    [FactKeys.Has (K .route8QuotientFree) known]
    [FactKeys.Has (K .route8UnifiedEntryCensus) known]
    [FactKeys.Has (K .route8PeelingDescent) known]
    [FactKeys.Has (K .route8StageRateFailed) known]
    [FactKeys.Has (K .route8DemandLedger) known]
    [FactKeys.Has (K .route8DemandAbsorption) known]
    [FactKeys.Has (K .route8DemandUnitCount) known]
    [FactKeys.Has (K .route8OpenBoundarySaturated) known]
    [FactKeys.Has (K .route8WindowBlockers) known]
    [FactKeys.Has (K .windowShadowHitCycle) known]
    [FactKeys.Has (K .windowShadowHitExcluded) known]
    [FactKeys.Has (K .route8UnpaidTwoCarrier) known]
    [FactKeys.Has (K .route8UnpaidExitFourResidual) known]
    [FactKeys.Has (K .route8UnifiedVisibleResidual) known]
    [FactKeys.Has (K .route8UnifiedVisibleOverload) known]
    [FactKeys.Has (K .route8JointBalance) known]
    (entry : Route8LaneEntry selected)
    (continuation : NetChargeContinuation selected) :
    Route8JointBalanceOutcome_product selected :=
  ⟨route8JointBalanceReturn history, entry, continuation⟩

end HypostructureErdos64EG
