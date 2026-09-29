import HypostructureErdos64EG.Assembly.Residuals
import HypostructureErdos64EG.Assembly.Residuals.Route8Blocks

/-!
# Assembly: `TypeBSublinearOutcome` as a product of arm blocks

`TypeBSublinearOutcome` (node `[187]`, Type B sublinear failure) is returned
at one Lean site, the negative arm of `typeBSublinearDichotomy` in
`selectedRouteEightUnifiedResidual` (`Assembly/RouteEight/Local.lean`), and
is reached there by 750 selected-root paths whose ledgers hold 750 distinct
fact sets.  Those fact sets are exactly the 80 common keys of the generic
residual `TypeBSublinearOutcome` together with one choice in each factor of the
nested arm-block product of `Assembly/Residuals/Route8Blocks.lean`; the
product is full (all 15 × 50 combinations of lane entry and continuation
occur, each on one path; the lane entry `Route8LaneEntry` is 3 prefixes × 4
entropy arms plus the `[161]` prefix × 3 low-entropy arms, the two closed
combinations being "unrealized, `τ(θ) ≥ 1/4`, `θ < 1/78`" (closed at `[146]`)
and "`[161]`, high entropy" (closed at `[53]`)).
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

/-- **Node `[187]` (Type B sublinear failure), as a product of arm blocks**:
the 102 common facts of the generic residual, one of the 15 lane entries
(prefix block with entropy block) and one of the 50 continuation
combinations. -/
abbrev TypeBSublinearOutcome_product (selected : EGInput.{u}) : Prop :=
  TypeBSublinearOutcome selected ∧
  Route8LaneEntry selected ∧
  NetChargeContinuation selected

/-- The product residual forgets to the generic residual. -/
theorem TypeBSublinearOutcome_product.toGeneric {selected : EGInput.{u}}
    (h : TypeBSublinearOutcome_product selected) :
    TypeBSublinearOutcome selected :=
  h.1

/-- The return of `TypeBSublinearOutcome_product`, parameterised by the arm
choices: the generic facts are read with one `get` each
(`typeBSublinearReturn`), and each factor is the chosen arm block, itself built
by its `.ret` theorem with one `get` per key on the same ledger. -/
theorem typeBSublinearProductReturn
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
    [FactKeys.Has (K .everyWitnessSpectrumSplit) known]
    [FactKeys.Has (K .packingOrderBound) known]
    [FactKeys.Has (K .noSuppressionChordViolation) known]
    [FactKeys.Has (K .twoSwitchForcedPath) known]
    [FactKeys.Has (K .crossSwitchFamily) known]
    [FactKeys.Has (K .highCentreSplitForced) known]
    [FactKeys.Has (K .sameVertexSwitchForcedPath) known]
    [FactKeys.Has (K .specWitnessStructure) known]
    [FactKeys.Has (K .remainderDeficiencyBelowCut) known]
    [FactKeys.Has (K .windowCutCapacity) known]
    [FactKeys.Has (K .primitiveCarrierCount) known]
    [FactKeys.Has (K .singleBoundaryShape) known]
    [FactKeys.Has (K .neighbourhoodPairCount) known]
    [FactKeys.Has (K .starCycleConstraint) known]
    [FactKeys.Has (K .meetingCycleConstraint) known]
    [FactKeys.Has (K .highDegreePairSum) known]
    [FactKeys.Has (K .vertexDeletionComponents) known]
    [FactKeys.Has (K .cyclesThroughVertex) known]
    [FactKeys.Has (K .cutVertexBlockPaths) known]
    [FactKeys.Has (K .cycleDoubleCount) known]
    [FactKeys.Has (K .threeRouteFan) known]
    [FactKeys.Has (K .threeRouteChain) known]
    [FactKeys.Has (K .windowPositionStubs) known]
    [FactKeys.Has (K .windowAttachmentGap) known]
    [FactKeys.Has (K .portEndDegree) known]
    [FactKeys.Has (K .hubLinkStructure) known]
    [FactKeys.Has (K .hubClassCounts) known]
    [FactKeys.Has (K .slotRelation) known]
    [FactKeys.Has (K .closedClasses) known]
    [FactKeys.Has (K .hubTwoHopLinks) known]
    [FactKeys.Has (K .slotLinear) known]
    [FactKeys.Has (K .remainderPathBounds) known]
    [FactKeys.Has (K .windowFreeGeometry) known]
    [FactKeys.Has (K .inducedPathAttachment) known]
    [FactKeys.Has (K .densityExcess) known]
    [FactKeys.Has (K .remainderSlack) known]
    [FactKeys.Has (K .hubWindowBudget) known]
    [FactKeys.Has (K .windowHubBounds) known]
    [FactKeys.Has (K .cubicNeighbourSupply) known]
    [FactKeys.Has (K .hubCountBound) known]
    [FactKeys.Has (K .lowEdgeParity) known]
    [FactKeys.Has (K .bigHubBound) known]
    [FactKeys.Has (K .bigHubVShapes) known]
    [FactKeys.Has (K .highSurplusBound) known]
    [FactKeys.Has (K .hubLengthThreePairs) known]
    [FactKeys.Has (K .surplusDartIdentity) known]
    [FactKeys.Has (K .highDegreeCountBound) known]
    [FactKeys.Has (K .admissibleQuotientsLabelInjective) known]
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
    [FactKeys.Has (K .typeBSublinearResidual) known]
    [FactKeys.Has (K .typeBSublinearCanonicalForm) known]
    [FactKeys.Has (K .groupedAbsorbedCoreSubset) known]
    [FactKeys.Has (K .typeBSublinearFailureArms) known]
    [FactKeys.Has (K .groupedCentresHigh) known]
    [FactKeys.Has (K .handoffDegreeClauseEmpty) known]
    [FactKeys.Has (K .pieceRoutingTotal) known]
    [FactKeys.Has (K .coverPayment) known]
    [FactKeys.Has (K .loadFailureSaturated) known]
    [FactKeys.Has (K .unpaidAbsorbedWindowPort) known]
    [FactKeys.Has (K .receiverPortsAreWindowStubs) known]
    [FactKeys.Has (K .saturatedReceiverBasin) known]
    [FactKeys.Has (K .loadFlowValue) known]
    [FactKeys.Has (K .coverFlowValue) known]
    [FactKeys.Has (K .pieceSizeProfile) known]
    [FactKeys.Has (K .bridgePieceMassDichotomy) known]
    [FactKeys.Has (K .traceIntoCentreStructure) known]
    [FactKeys.Has (K .traceIntoAbsorbedStructure) known]
    (entryArm : Route8LaneEntry selected)
    (continuationArm : NetChargeContinuation selected) :
    TypeBSublinearOutcome_product selected :=
  ⟨typeBSublinearReturn history, entryArm, continuationArm⟩

end HypostructureErdos64EG
