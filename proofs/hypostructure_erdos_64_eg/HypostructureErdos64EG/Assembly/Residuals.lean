import HypostructureErdos64EG.Assembly.Basic

/-!
# Assembly: Residuals

The returned residuals of the selected-root reduction, each stated as the
explicit conjunction of EVERY fact on its maximal ledger: the facts common to
every path that reaches the residual, after each path has been brought, by the
rows whose requirements it carries, to the same fact set.  One return theorem
per residual (per arm of the residual's own decision) reads each fact with one
`ExactLedger.get`.  A fact present on some paths but not derivable on the
others (its prerequisite is an arm of a decision that path did not take) is
listed in `audits/erdos-64-red-team/lean-vs-paper-discrepancies.md`.

Every residual carries the 21 entry-prefix facts of
`SpineRows/JointHubs.lean` (after `K .windowAttachmentGap`), and every strict-surplus
residual the 16 strict-arm facts (after `K .highSurplusConfiguration`).  The fact counts
quoted below are the numbers of `Holds` conjuncts of each abbrev, equal to
the numbers of `get`s in its return theorem, and include these facts.

The named sparse exits of `[125]` are the two cycle conclusions in G (an
accepted cycle, and a suppression-chord certificate whose lifted length is
accepted), refuted by `[4]`'s selection.  `[125]`'s survivor fact is a theorem
about G (`sparseSurplusSurvivorRow`), so no residual carries a sparse exit.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- **Node `[144a]`** (thm:main (ii), tex 355-364): the same-token Type B
handoff of [144] on the strict-surplus survivor, or (the paper error at
[144]) the unresolved same-label pattern pair.  The generic residual: the
explicit conjunction of the 135 facts common to every path.  Its six distinct
fact sets (the class arm of [139]/[141] times the arm of [144]'s handoff
decision) are its subtypes in `Assembly/Residuals/Node144aOutcome.lean`. -/
abbrev Node144aOutcome (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .selection selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cubicBaseline selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .minDegreeBaseline selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .returnAvoidance selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .noProperBaseline selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .slackIndependent selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .tightEndpoint selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cycleRankConstraint selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .degreeProfileFibres selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .targetCompleteContextUniversality selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .replacementExclusion selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .uncompressible selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPresent selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .maximalPacking selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .localAlgebra selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .packingOrderBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .noSuppressionChordViolation selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .twoSwitchForcedPath selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .crossSwitchFamily selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highCentreSplitForced selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sameVertexSwitchForcedPath selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .declaredPairSupportStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderDeficiencyBelowCut selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowCutCapacity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .primitiveCarrierCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .singleBoundaryShape selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .neighbourhoodPairCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .starCycleConstraint selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .meetingCycleConstraint selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highDegreePairSum selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .vertexDeletionComponents selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cyclesThroughVertex selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cutVertexBlockPaths selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cycleDoubleCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .threeRouteFan selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .threeRouteChain selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPositionStubs selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowAttachmentGap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .portEndDegree selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubLinkStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubClassCounts selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .slotRelation selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .closedClasses selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubTwoHopLinks selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .slotLinear selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderPathBounds selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowFreeGeometry selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .inducedPathAttachment selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .densityExcess selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderSlack selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubWindowBudget selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowHubBounds selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cubicNeighbourSupply selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubCountBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .lowEdgeParity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .bigHubBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .bigHubVShapes selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highSurplusBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubLengthThreePairs selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .surplusDartIdentity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highDegreeCountBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .admissibleQuotientsLabelInjective selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .surplusAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highSurplusConfiguration selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairArmAPattern selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairArmARoleAlphabet selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairArmB selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .extFreeEmpty selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .extLoadSum selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .extOverload selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .extOverloadedToken selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .newLoadBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .freeSideHubs selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .separatedPairs selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .scalePressure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .freeSideStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .freeSideCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highSurplusOrder selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowChargeKinds selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .responseObstructionTargetDefect selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highEndpointSwitch selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .edgeSurplusIdentity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .ceilSqrtAboveScale selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .orderAboveScaleSquare selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sixVertexExtremalEnvelope selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highDegreePositive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highDegreeSurplusCapacity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .canonicalCapacityExplicit selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .canonicalTokenCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .canonicalBlockedFreePartition selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .canonicalLedgerDeficit selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairCountDeficit selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .canonicalCertificationCriterion selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .canonicalOverloadOfFits selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .canonicalFreeExcessOfCapped selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .paperBudgetBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .paperBudgetCertifies selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairCodeConfiguration selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sparseSurplusSurvivor selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .openPortSuppression selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .openPortSuppressionSafe selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .singleOpenPortSuppressionWitness selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .suppressedFamilyCriticalCycle selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sparseSlackSurplus selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .activeSurplusFamily selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sparsePortActivation selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .activeSurplusDemands selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .baselineSpineDemand selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .freePairCountFails selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .dependentPairFamily selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairDegreeProfileFibres selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairNoProfileObstruction selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairNoResponseObstruction selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .blockedPairNoExit selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .canonicalBlockerRoute selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .canonicalPairLedger selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sparseUpperEnvelope selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .capacityTokenLedger selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .blockedPairEntropySetup selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .blockedPairEntropySandwich selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .roleFibrePartition selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .fibrePressure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sparsePressureOverload selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .bridgeless selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highCentreNormalForm selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .homogeneousBottleneckPattern selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .homogeneousCapsFail selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .bottleneckRouting selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sameTokenPatternSupports selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sameTokenPatternSwap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sameTokenWalkWindows selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sameTokenWalkExchange selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sameTokenW0Escape selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sameTokenCrossingCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sameTokenHubCount selected.object

/-- The return of the generic `Node144aOutcome`: one `get` per common fact.
The subtypes' return theorems extend it with one `get` per extra fact. -/
theorem node144aReturn
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
    [FactKeys.Has (K .packingOrderBound) known]
    [FactKeys.Has (K .noSuppressionChordViolation) known]
    [FactKeys.Has (K .twoSwitchForcedPath) known]
    [FactKeys.Has (K .crossSwitchFamily) known]
    [FactKeys.Has (K .highCentreSplitForced) known]
    [FactKeys.Has (K .sameVertexSwitchForcedPath) known]
    [FactKeys.Has (K .declaredPairSupportStructure) known]
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
    [FactKeys.Has (K .surplusAbove) known]
    [FactKeys.Has (K .highSurplusConfiguration) known]
    [FactKeys.Has (K .pairArmAPattern) known]
    [FactKeys.Has (K .pairArmARoleAlphabet) known]
    [FactKeys.Has (K .pairArmB) known]
    [FactKeys.Has (K .extFreeEmpty) known]
    [FactKeys.Has (K .extLoadSum) known]
    [FactKeys.Has (K .extOverload) known]
    [FactKeys.Has (K .extOverloadedToken) known]
    [FactKeys.Has (K .newLoadBound) known]
    [FactKeys.Has (K .freeSideHubs) known]
    [FactKeys.Has (K .separatedPairs) known]
    [FactKeys.Has (K .scalePressure) known]
    [FactKeys.Has (K .freeSideStructure) known]
    [FactKeys.Has (K .freeSideCount) known]
    [FactKeys.Has (K .highSurplusOrder) known]
    [FactKeys.Has (K .windowChargeKinds) known]
    [FactKeys.Has (K .responseObstructionTargetDefect) known]
    [FactKeys.Has (K .highEndpointSwitch) known]
    [FactKeys.Has (K .edgeSurplusIdentity) known]
    [FactKeys.Has (K .ceilSqrtAboveScale) known]
    [FactKeys.Has (K .orderAboveScaleSquare) known]
    [FactKeys.Has (K .sixVertexExtremalEnvelope) known]
    [FactKeys.Has (K .highDegreePositive) known]
    [FactKeys.Has (K .highDegreeSurplusCapacity) known]
    [FactKeys.Has (K .canonicalCapacityExplicit) known]
    [FactKeys.Has (K .canonicalTokenCount) known]
    [FactKeys.Has (K .canonicalBlockedFreePartition) known]
    [FactKeys.Has (K .canonicalLedgerDeficit) known]
    [FactKeys.Has (K .pairCountDeficit) known]
    [FactKeys.Has (K .canonicalCertificationCriterion) known]
    [FactKeys.Has (K .canonicalOverloadOfFits) known]
    [FactKeys.Has (K .canonicalFreeExcessOfCapped) known]
    [FactKeys.Has (K .paperBudgetBound) known]
    [FactKeys.Has (K .paperBudgetCertifies) known]
    [FactKeys.Has (K .pairCodeConfiguration) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    [FactKeys.Has (K .openPortSuppression) known]
    [FactKeys.Has (K .openPortSuppressionSafe) known]
    [FactKeys.Has (K .singleOpenPortSuppressionWitness) known]
    [FactKeys.Has (K .suppressedFamilyCriticalCycle) known]
    [FactKeys.Has (K .sparseSlackSurplus) known]
    [FactKeys.Has (K .activeSurplusFamily) known]
    [FactKeys.Has (K .sparsePortActivation) known]
    [FactKeys.Has (K .activeSurplusDemands) known]
    [FactKeys.Has (K .baselineSpineDemand) known]
    [FactKeys.Has (K .freePairCountFails) known]
    [FactKeys.Has (K .dependentPairFamily) known]
    [FactKeys.Has (K .pairDegreeProfileFibres) known]
    [FactKeys.Has (K .pairNoProfileObstruction) known]
    [FactKeys.Has (K .pairNoResponseObstruction) known]
    [FactKeys.Has (K .blockedPairNoExit) known]
    [FactKeys.Has (K .canonicalBlockerRoute) known]
    [FactKeys.Has (K .canonicalPairLedger) known]
    [FactKeys.Has (K .sparseUpperEnvelope) known]
    [FactKeys.Has (K .capacityTokenLedger) known]
    [FactKeys.Has (K .blockedPairEntropySetup) known]
    [FactKeys.Has (K .blockedPairEntropySandwich) known]
    [FactKeys.Has (K .roleFibrePartition) known]
    [FactKeys.Has (K .fibrePressure) known]
    [FactKeys.Has (K .sparsePressureOverload) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .highCentreNormalForm) known]
    [FactKeys.Has (K .homogeneousBottleneckPattern) known]
    [FactKeys.Has (K .homogeneousCapsFail) known]
    [FactKeys.Has (K .bottleneckRouting) known]
    [FactKeys.Has (K .sameTokenPatternSupports) known]
    [FactKeys.Has (K .sameTokenPatternSwap) known]
    [FactKeys.Has (K .sameTokenWalkWindows) known]
    [FactKeys.Has (K .sameTokenWalkExchange) known]
    [FactKeys.Has (K .sameTokenW0Escape) known]
    [FactKeys.Has (K .sameTokenCrossingCount) known]
    [FactKeys.Has (K .sameTokenHubCount) known] :
    Node144aOutcome selected :=
  ⟨(history.get (K .selection)).down,
    (history.get (K .cubicBaseline)).down,
    (history.get (K .minDegreeBaseline)).down,
    (history.get (K .returnAvoidance)).down,
    (history.get (K .noProperBaseline)).down,
    (history.get (K .slackIndependent)).down,
    (history.get (K .tightEndpoint)).down,
    (history.get (K .cycleRankConstraint)).down,
    (history.get (K .degreeProfileFibres)).down,
    (history.get (K .targetCompleteContextUniversality)).down,
    (history.get (K .replacementExclusion)).down,
    (history.get (K .uncompressible)).down,
    (history.get (K .windowPresent)).down,
    (history.get (K .maximalPacking)).down,
    (history.get (K .localAlgebra)).down,
    (history.get (K .packingOrderBound)).down,
    (history.get (K .noSuppressionChordViolation)).down,
    (history.get (K .twoSwitchForcedPath)).down,
    (history.get (K .crossSwitchFamily)).down,
    (history.get (K .highCentreSplitForced)).down,
    (history.get (K .sameVertexSwitchForcedPath)).down,
    (history.get (K .declaredPairSupportStructure)).down,
    (history.get (K .remainderDeficiencyBelowCut)).down,
    (history.get (K .windowCutCapacity)).down,
    (history.get (K .primitiveCarrierCount)).down,
    (history.get (K .singleBoundaryShape)).down,
    (history.get (K .neighbourhoodPairCount)).down,
    (history.get (K .starCycleConstraint)).down,
    (history.get (K .meetingCycleConstraint)).down,
    (history.get (K .highDegreePairSum)).down,
    (history.get (K .vertexDeletionComponents)).down,
    (history.get (K .cyclesThroughVertex)).down,
    (history.get (K .cutVertexBlockPaths)).down,
    (history.get (K .cycleDoubleCount)).down,
    (history.get (K .threeRouteFan)).down,
    (history.get (K .threeRouteChain)).down,
    (history.get (K .windowPositionStubs)).down,
    (history.get (K .windowAttachmentGap)).down,
    (history.get (K .portEndDegree)).down,
    (history.get (K .hubLinkStructure)).down,
    (history.get (K .hubClassCounts)).down,
    (history.get (K .slotRelation)).down,
    (history.get (K .closedClasses)).down,
    (history.get (K .hubTwoHopLinks)).down,
    (history.get (K .slotLinear)).down,
    (history.get (K .remainderPathBounds)).down,
    (history.get (K .windowFreeGeometry)).down,
    (history.get (K .inducedPathAttachment)).down,
    (history.get (K .densityExcess)).down,
    (history.get (K .remainderSlack)).down,
    (history.get (K .hubWindowBudget)).down,
    (history.get (K .windowHubBounds)).down,
    (history.get (K .cubicNeighbourSupply)).down,
    (history.get (K .hubCountBound)).down,
    (history.get (K .lowEdgeParity)).down,
    (history.get (K .bigHubBound)).down,
    (history.get (K .bigHubVShapes)).down,
    (history.get (K .highSurplusBound)).down,
    (history.get (K .hubLengthThreePairs)).down,
    (history.get (K .surplusDartIdentity)).down,
    (history.get (K .highDegreeCountBound)).down,
    (history.get (K .admissibleQuotientsLabelInjective)).down,
    (history.get (K .surplusAbove)).down,
    (history.get (K .highSurplusConfiguration)).down,
    (history.get (K .pairArmAPattern)).down,
    (history.get (K .pairArmARoleAlphabet)).down,
    (history.get (K .pairArmB)).down,
    (history.get (K .extFreeEmpty)).down,
    (history.get (K .extLoadSum)).down,
    (history.get (K .extOverload)).down,
    (history.get (K .extOverloadedToken)).down,
    (history.get (K .newLoadBound)).down,
    (history.get (K .freeSideHubs)).down,
    (history.get (K .separatedPairs)).down,
    (history.get (K .scalePressure)).down,
    (history.get (K .freeSideStructure)).down,
    (history.get (K .freeSideCount)).down,
    (history.get (K .highSurplusOrder)).down,
    (history.get (K .windowChargeKinds)).down,
    (history.get (K .responseObstructionTargetDefect)).down,
    (history.get (K .highEndpointSwitch)).down,
    (history.get (K .edgeSurplusIdentity)).down,
    (history.get (K .ceilSqrtAboveScale)).down,
    (history.get (K .orderAboveScaleSquare)).down,
    (history.get (K .sixVertexExtremalEnvelope)).down,
    (history.get (K .highDegreePositive)).down,
    (history.get (K .highDegreeSurplusCapacity)).down,
    (history.get (K .canonicalCapacityExplicit)).down,
    (history.get (K .canonicalTokenCount)).down,
    (history.get (K .canonicalBlockedFreePartition)).down,
    (history.get (K .canonicalLedgerDeficit)).down,
    (history.get (K .pairCountDeficit)).down,
    (history.get (K .canonicalCertificationCriterion)).down,
    (history.get (K .canonicalOverloadOfFits)).down,
    (history.get (K .canonicalFreeExcessOfCapped)).down,
    (history.get (K .paperBudgetBound)).down,
    (history.get (K .paperBudgetCertifies)).down,
    (history.get (K .pairCodeConfiguration)).down,
    (history.get (K .sparseSurplusSurvivor)).down,
    (history.get (K .openPortSuppression)).down,
    (history.get (K .openPortSuppressionSafe)).down,
    (history.get (K .singleOpenPortSuppressionWitness)).down,
    (history.get (K .suppressedFamilyCriticalCycle)).down,
    (history.get (K .sparseSlackSurplus)).down,
    (history.get (K .activeSurplusFamily)).down,
    (history.get (K .sparsePortActivation)).down,
    (history.get (K .activeSurplusDemands)).down,
    (history.get (K .baselineSpineDemand)).down,
    (history.get (K .freePairCountFails)).down,
    (history.get (K .dependentPairFamily)).down,
    (history.get (K .pairDegreeProfileFibres)).down,
    (history.get (K .pairNoProfileObstruction)).down,
    (history.get (K .pairNoResponseObstruction)).down,
    (history.get (K .blockedPairNoExit)).down,
    (history.get (K .canonicalBlockerRoute)).down,
    (history.get (K .canonicalPairLedger)).down,
    (history.get (K .sparseUpperEnvelope)).down,
    (history.get (K .capacityTokenLedger)).down,
    (history.get (K .blockedPairEntropySetup)).down,
    (history.get (K .blockedPairEntropySandwich)).down,
    (history.get (K .roleFibrePartition)).down,
    (history.get (K .fibrePressure)).down,
    (history.get (K .sparsePressureOverload)).down,
    (history.get (K .bridgeless)).down,
    (history.get (K .highCentreNormalForm)).down,
    (history.get (K .homogeneousBottleneckPattern)).down,
    (history.get (K .homogeneousCapsFail)).down,
    (history.get (K .bottleneckRouting)).down,
    (history.get (K .sameTokenPatternSupports)).down,
    (history.get (K .sameTokenPatternSwap)).down,
    (history.get (K .sameTokenWalkWindows)).down,
    (history.get (K .sameTokenWalkExchange)).down,
    (history.get (K .sameTokenW0Escape)).down,
    (history.get (K .sameTokenCrossingCount)).down,
    (history.get (K .sameTokenHubCount)).down⟩

/-- **Node `[172a]`** (thm:main (iii), tex 365-372): the first failed
conditional graph-count inequality of lem:scale-additivity on the dense-
packing branch, with its minimal same-scale barrier overlap.  The explicit
conjunction of every fact on its maximal ledger (124 common facts). -/
abbrev BlockedBarrierOverlapOutcome (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .selection selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cubicBaseline selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .minDegreeBaseline selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .returnAvoidance selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .noProperBaseline selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .slackIndependent selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .tightEndpoint selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cycleRankConstraint selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .degreeProfileFibres selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .targetCompleteContextUniversality selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .replacementExclusion selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .uncompressible selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPresent selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .maximalPacking selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .localAlgebra selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .packingOrderBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .noSuppressionChordViolation selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .twoSwitchForcedPath selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .crossSwitchFamily selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highCentreSplitForced selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sameVertexSwitchForcedPath selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .declaredPairSupportStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderDeficiencyBelowCut selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowCutCapacity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .primitiveCarrierCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .singleBoundaryShape selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .neighbourhoodPairCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .starCycleConstraint selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .meetingCycleConstraint selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highDegreePairSum selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .vertexDeletionComponents selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cyclesThroughVertex selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cutVertexBlockPaths selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cycleDoubleCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .threeRouteFan selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .threeRouteChain selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPositionStubs selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowAttachmentGap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .portEndDegree selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubLinkStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubClassCounts selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .slotRelation selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .closedClasses selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubTwoHopLinks selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .slotLinear selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderPathBounds selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowFreeGeometry selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .inducedPathAttachment selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .densityExcess selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderSlack selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubWindowBudget selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowHubBounds selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cubicNeighbourSupply selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubCountBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .lowEdgeParity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .bigHubBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .bigHubVShapes selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highSurplusBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubLengthThreePairs selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .surplusDartIdentity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highDegreeCountBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .admissibleQuotientsLabelInjective selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .surplusAtOrBelow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sparseSurplusSurvivor selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .barrierEnumeration selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageSeparated selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .skeletonDominates selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hotColdPartition selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .barrierCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8AtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldHotEntropyCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMass selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldAmbientCubic selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldStubExcess selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldAmbientCubicStubExcess selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldSelectedBranchExcess selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMassLinear selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderNormalized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .boundaryDemand selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .stubSupply selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .wedgeSupply selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .curvatureTargetRank selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .exactResponseProfile selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .targetRankCircuit selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .curvatureFullRank selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .forcedCurvatureCost selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .netChargeLocalization selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .bridgeless selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldReturnCorridors selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldCorridorState selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldFirstFailureOccurrence selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldCutStatesDistinct selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldHeavyEntryTerminal selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseColdCorridorsTerminal selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldFailureCycle selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldFailureDefectRoute selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldFailureCompression selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldHandoffTransfer selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldFailureRouting selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldExchangeBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermCandidates selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermFamilyPositive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .absorbedGermSplit selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .absorbedGermFanData selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermNoneRealizing selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermNoneDistinguishing selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldNeutralEqualLengthTerminal selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermRouted selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermSilent selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermDistinguished selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermRealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldSameInterfaceTable selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldBranchClosed selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldCanonicalNeutralConfiguration selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldCanonicalReplacementSwap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldCanonicalReplacementTrivial selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .blockedClassMember selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .blockedBarrierOverlap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .blockedOwnRecord selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .blockedFailureSlack selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .blockedPrefixCompression selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .blockedFailingSetCarries selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .blockedOverlapSupport selected.object

/-- The return of `BlockedBarrierOverlapOutcome`: one `get` per fact of
its maximal ledger. -/
theorem blockedBarrierOverlapReturn
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
    [FactKeys.Has (K .packingOrderBound) known]
    [FactKeys.Has (K .noSuppressionChordViolation) known]
    [FactKeys.Has (K .twoSwitchForcedPath) known]
    [FactKeys.Has (K .crossSwitchFamily) known]
    [FactKeys.Has (K .highCentreSplitForced) known]
    [FactKeys.Has (K .sameVertexSwitchForcedPath) known]
    [FactKeys.Has (K .declaredPairSupportStructure) known]
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
    [FactKeys.Has (K .windowPackageUnrealized) known]
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .barrierCap) known]
    [FactKeys.Has (K .coldRoute8AtOrAbove) known]
    [FactKeys.Has (K .coldHotEntropyCap) known]
    [FactKeys.Has (K .coldMass) known]
    [FactKeys.Has (K .coldAmbientCubic) known]
    [FactKeys.Has (K .coldStubExcess) known]
    [FactKeys.Has (K .coldAmbientCubicStubExcess) known]
    [FactKeys.Has (K .coldSelectedBranchExcess) known]
    [FactKeys.Has (K .coldMassLinear) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .boundaryDemand) known]
    [FactKeys.Has (K .stubSupply) known]
    [FactKeys.Has (K .wedgeSupply) known]
    [FactKeys.Has (K .curvatureTargetRank) known]
    [FactKeys.Has (K .exactResponseProfile) known]
    [FactKeys.Has (K .targetRankCircuit) known]
    [FactKeys.Has (K .curvatureFullRank) known]
    [FactKeys.Has (K .forcedCurvatureCost) known]
    [FactKeys.Has (K .netChargeLocalization) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .coldReturnCorridors) known]
    [FactKeys.Has (K .coldCorridorState) known]
    [FactKeys.Has (K .coldFirstFailureOccurrence) known]
    [FactKeys.Has (K .coldCutStatesDistinct) known]
    [FactKeys.Has (K .coldHeavyEntryTerminal) known]
    [FactKeys.Has (K .denseColdCorridorsTerminal) known]
    [FactKeys.Has (K .coldFailureCycle) known]
    [FactKeys.Has (K .coldFailureDefectRoute) known]
    [FactKeys.Has (K .coldFailureCompression) known]
    [FactKeys.Has (K .coldHandoffTransfer) known]
    [FactKeys.Has (K .coldFailureRouting) known]
    [FactKeys.Has (K .coldExchangeBound) known]
    [FactKeys.Has (K .coldGermCandidates) known]
    [FactKeys.Has (K .coldGermFamilyPositive) known]
    [FactKeys.Has (K .absorbedGermSplit) known]
    [FactKeys.Has (K .absorbedGermFanData) known]
    [FactKeys.Has (K .coldGermNoneRealizing) known]
    [FactKeys.Has (K .coldGermNoneDistinguishing) known]
    [FactKeys.Has (K .coldNeutralEqualLengthTerminal) known]
    [FactKeys.Has (K .coldGermRouted) known]
    [FactKeys.Has (K .coldGermSilent) known]
    [FactKeys.Has (K .coldGermDistinguished) known]
    [FactKeys.Has (K .coldGermRealized) known]
    [FactKeys.Has (K .coldSameInterfaceTable) known]
    [FactKeys.Has (K .coldBranchClosed) known]
    [FactKeys.Has (K .coldCanonicalNeutralConfiguration) known]
    [FactKeys.Has (K .coldCanonicalReplacementSwap) known]
    [FactKeys.Has (K .coldCanonicalReplacementTrivial) known]
    [FactKeys.Has (K .blockedClassMember) known]
    [FactKeys.Has (K .blockedBarrierOverlap) known]
    [FactKeys.Has (K .blockedOwnRecord) known]
    [FactKeys.Has (K .blockedFailureSlack) known]
    [FactKeys.Has (K .blockedPrefixCompression) known]
    [FactKeys.Has (K .blockedFailingSetCarries) known]
    [FactKeys.Has (K .blockedOverlapSupport) known] :
    BlockedBarrierOverlapOutcome selected :=
  ⟨(history.get (K .selection)).down,
    (history.get (K .cubicBaseline)).down,
    (history.get (K .minDegreeBaseline)).down,
    (history.get (K .returnAvoidance)).down,
    (history.get (K .noProperBaseline)).down,
    (history.get (K .slackIndependent)).down,
    (history.get (K .tightEndpoint)).down,
    (history.get (K .cycleRankConstraint)).down,
    (history.get (K .degreeProfileFibres)).down,
    (history.get (K .targetCompleteContextUniversality)).down,
    (history.get (K .replacementExclusion)).down,
    (history.get (K .uncompressible)).down,
    (history.get (K .windowPresent)).down,
    (history.get (K .maximalPacking)).down,
    (history.get (K .localAlgebra)).down,
    (history.get (K .packingOrderBound)).down,
    (history.get (K .noSuppressionChordViolation)).down,
    (history.get (K .twoSwitchForcedPath)).down,
    (history.get (K .crossSwitchFamily)).down,
    (history.get (K .highCentreSplitForced)).down,
    (history.get (K .sameVertexSwitchForcedPath)).down,
    (history.get (K .declaredPairSupportStructure)).down,
    (history.get (K .remainderDeficiencyBelowCut)).down,
    (history.get (K .windowCutCapacity)).down,
    (history.get (K .primitiveCarrierCount)).down,
    (history.get (K .singleBoundaryShape)).down,
    (history.get (K .neighbourhoodPairCount)).down,
    (history.get (K .starCycleConstraint)).down,
    (history.get (K .meetingCycleConstraint)).down,
    (history.get (K .highDegreePairSum)).down,
    (history.get (K .vertexDeletionComponents)).down,
    (history.get (K .cyclesThroughVertex)).down,
    (history.get (K .cutVertexBlockPaths)).down,
    (history.get (K .cycleDoubleCount)).down,
    (history.get (K .threeRouteFan)).down,
    (history.get (K .threeRouteChain)).down,
    (history.get (K .windowPositionStubs)).down,
    (history.get (K .windowAttachmentGap)).down,
    (history.get (K .portEndDegree)).down,
    (history.get (K .hubLinkStructure)).down,
    (history.get (K .hubClassCounts)).down,
    (history.get (K .slotRelation)).down,
    (history.get (K .closedClasses)).down,
    (history.get (K .hubTwoHopLinks)).down,
    (history.get (K .slotLinear)).down,
    (history.get (K .remainderPathBounds)).down,
    (history.get (K .windowFreeGeometry)).down,
    (history.get (K .inducedPathAttachment)).down,
    (history.get (K .densityExcess)).down,
    (history.get (K .remainderSlack)).down,
    (history.get (K .hubWindowBudget)).down,
    (history.get (K .windowHubBounds)).down,
    (history.get (K .cubicNeighbourSupply)).down,
    (history.get (K .hubCountBound)).down,
    (history.get (K .lowEdgeParity)).down,
    (history.get (K .bigHubBound)).down,
    (history.get (K .bigHubVShapes)).down,
    (history.get (K .highSurplusBound)).down,
    (history.get (K .hubLengthThreePairs)).down,
    (history.get (K .surplusDartIdentity)).down,
    (history.get (K .highDegreeCountBound)).down,
    (history.get (K .admissibleQuotientsLabelInjective)).down,
    (history.get (K .surplusAtOrBelow)).down,
    (history.get (K .sparseSurplusSurvivor)).down,
    (history.get (K .barrierEnumeration)).down,
    (history.get (K .windowPackageSeparated)).down,
    (history.get (K .skeletonDominates)).down,
    (history.get (K .windowPackageUnrealized)).down,
    (history.get (K .hotColdPartition)).down,
    (history.get (K .barrierCap)).down,
    (history.get (K .coldRoute8AtOrAbove)).down,
    (history.get (K .coldHotEntropyCap)).down,
    (history.get (K .coldMass)).down,
    (history.get (K .coldAmbientCubic)).down,
    (history.get (K .coldStubExcess)).down,
    (history.get (K .coldAmbientCubicStubExcess)).down,
    (history.get (K .coldSelectedBranchExcess)).down,
    (history.get (K .coldMassLinear)).down,
    (history.get (K .remainderNormalized)).down,
    (history.get (K .boundaryDemand)).down,
    (history.get (K .stubSupply)).down,
    (history.get (K .wedgeSupply)).down,
    (history.get (K .curvatureTargetRank)).down,
    (history.get (K .exactResponseProfile)).down,
    (history.get (K .targetRankCircuit)).down,
    (history.get (K .curvatureFullRank)).down,
    (history.get (K .forcedCurvatureCost)).down,
    (history.get (K .netChargeLocalization)).down,
    (history.get (K .bridgeless)).down,
    (history.get (K .coldReturnCorridors)).down,
    (history.get (K .coldCorridorState)).down,
    (history.get (K .coldFirstFailureOccurrence)).down,
    (history.get (K .coldCutStatesDistinct)).down,
    (history.get (K .coldHeavyEntryTerminal)).down,
    (history.get (K .denseColdCorridorsTerminal)).down,
    (history.get (K .coldFailureCycle)).down,
    (history.get (K .coldFailureDefectRoute)).down,
    (history.get (K .coldFailureCompression)).down,
    (history.get (K .coldHandoffTransfer)).down,
    (history.get (K .coldFailureRouting)).down,
    (history.get (K .coldExchangeBound)).down,
    (history.get (K .coldGermCandidates)).down,
    (history.get (K .coldGermFamilyPositive)).down,
    (history.get (K .absorbedGermSplit)).down,
    (history.get (K .absorbedGermFanData)).down,
    (history.get (K .coldGermNoneRealizing)).down,
    (history.get (K .coldGermNoneDistinguishing)).down,
    (history.get (K .coldNeutralEqualLengthTerminal)).down,
    (history.get (K .coldGermRouted)).down,
    (history.get (K .coldGermSilent)).down,
    (history.get (K .coldGermDistinguished)).down,
    (history.get (K .coldGermRealized)).down,
    (history.get (K .coldSameInterfaceTable)).down,
    (history.get (K .coldBranchClosed)).down,
    (history.get (K .coldCanonicalNeutralConfiguration)).down,
    (history.get (K .coldCanonicalReplacementSwap)).down,
    (history.get (K .coldCanonicalReplacementTrivial)).down,
    (history.get (K .blockedClassMember)).down,
    (history.get (K .blockedBarrierOverlap)).down,
    (history.get (K .blockedOwnRecord)).down,
    (history.get (K .blockedFailureSlack)).down,
    (history.get (K .blockedPrefixCompression)).down,
    (history.get (K .blockedFailingSetCarries)).down,
    (history.get (K .blockedOverlapSupport)).down⟩

/-- **Node `[182]`** (thm:main (iv), tex 373-377): the first failed coverage
implication of [178], [179] or [180] on the strict-surplus pair-code chain.
The explicit conjunction of every fact on its maximal ledger (120 common
facts). -/
abbrev PairConditionalFactorizationOutcome (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .selection selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cubicBaseline selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .minDegreeBaseline selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .returnAvoidance selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .noProperBaseline selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .slackIndependent selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .tightEndpoint selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cycleRankConstraint selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .degreeProfileFibres selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .targetCompleteContextUniversality selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .replacementExclusion selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .uncompressible selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPresent selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .maximalPacking selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .localAlgebra selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .packingOrderBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .noSuppressionChordViolation selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .twoSwitchForcedPath selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .crossSwitchFamily selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highCentreSplitForced selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sameVertexSwitchForcedPath selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .declaredPairSupportStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .bridgeless selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderDeficiencyBelowCut selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowCutCapacity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .primitiveCarrierCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .singleBoundaryShape selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .neighbourhoodPairCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .starCycleConstraint selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .meetingCycleConstraint selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highDegreePairSum selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .vertexDeletionComponents selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cyclesThroughVertex selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cutVertexBlockPaths selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cycleDoubleCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .threeRouteFan selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .threeRouteChain selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPositionStubs selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowAttachmentGap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .portEndDegree selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubLinkStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubClassCounts selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .slotRelation selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .closedClasses selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubTwoHopLinks selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .slotLinear selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderPathBounds selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowFreeGeometry selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .inducedPathAttachment selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .densityExcess selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderSlack selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubWindowBudget selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowHubBounds selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cubicNeighbourSupply selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubCountBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .lowEdgeParity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .bigHubBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .bigHubVShapes selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highSurplusBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubLengthThreePairs selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .surplusDartIdentity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highDegreeCountBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .admissibleQuotientsLabelInjective selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .surplusAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highSurplusConfiguration selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairArmAPattern selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairArmARoleAlphabet selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairArmB selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .extFreeEmpty selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .extLoadSum selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .extOverload selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .extOverloadedToken selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .newLoadBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .freeSideHubs selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .separatedPairs selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .scalePressure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .freeSideStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .freeSideCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highSurplusOrder selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowChargeKinds selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .responseObstructionTargetDefect selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highEndpointSwitch selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .edgeSurplusIdentity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .ceilSqrtAboveScale selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .orderAboveScaleSquare selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sixVertexExtremalEnvelope selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highDegreePositive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highDegreeSurplusCapacity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .canonicalCapacityExplicit selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .canonicalTokenCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .canonicalBlockedFreePartition selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .canonicalLedgerDeficit selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairCountDeficit selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .canonicalCertificationCriterion selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .canonicalOverloadOfFits selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .canonicalFreeExcessOfCapped selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .paperBudgetBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .paperBudgetCertifies selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairCodeConfiguration selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sparseSurplusSurvivor selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .openPortSuppression selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .openPortSuppressionSafe selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .singleOpenPortSuppressionWitness selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .suppressedFamilyCriticalCycle selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sparseSlackSurplus selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .activeSurplusFamily selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sparsePortActivation selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .activeSurplusDemands selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .baselineSpineDemand selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .freePairCountFails selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sparseUpperEnvelope selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairOverlapFirstFailure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .mixedSparseSpineDependence selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .exactCubicBaselineBudget selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .incrementalSkeletonRoom selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .skeletonDominates selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairOverlapSystem selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairConditionalFactorizationResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairCorrelation selected.object

/-- The return of `PairConditionalFactorizationOutcome`: one `get` per fact of
its maximal ledger. -/
theorem pairConditionalFactorizationReturn
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
    [FactKeys.Has (K .packingOrderBound) known]
    [FactKeys.Has (K .noSuppressionChordViolation) known]
    [FactKeys.Has (K .twoSwitchForcedPath) known]
    [FactKeys.Has (K .crossSwitchFamily) known]
    [FactKeys.Has (K .highCentreSplitForced) known]
    [FactKeys.Has (K .sameVertexSwitchForcedPath) known]
    [FactKeys.Has (K .declaredPairSupportStructure) known]
    [FactKeys.Has (K .bridgeless) known]
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
    [FactKeys.Has (K .surplusAbove) known]
    [FactKeys.Has (K .highSurplusConfiguration) known]
    [FactKeys.Has (K .pairArmAPattern) known]
    [FactKeys.Has (K .pairArmARoleAlphabet) known]
    [FactKeys.Has (K .pairArmB) known]
    [FactKeys.Has (K .extFreeEmpty) known]
    [FactKeys.Has (K .extLoadSum) known]
    [FactKeys.Has (K .extOverload) known]
    [FactKeys.Has (K .extOverloadedToken) known]
    [FactKeys.Has (K .newLoadBound) known]
    [FactKeys.Has (K .freeSideHubs) known]
    [FactKeys.Has (K .separatedPairs) known]
    [FactKeys.Has (K .scalePressure) known]
    [FactKeys.Has (K .freeSideStructure) known]
    [FactKeys.Has (K .freeSideCount) known]
    [FactKeys.Has (K .highSurplusOrder) known]
    [FactKeys.Has (K .windowChargeKinds) known]
    [FactKeys.Has (K .responseObstructionTargetDefect) known]
    [FactKeys.Has (K .highEndpointSwitch) known]
    [FactKeys.Has (K .edgeSurplusIdentity) known]
    [FactKeys.Has (K .ceilSqrtAboveScale) known]
    [FactKeys.Has (K .orderAboveScaleSquare) known]
    [FactKeys.Has (K .sixVertexExtremalEnvelope) known]
    [FactKeys.Has (K .highDegreePositive) known]
    [FactKeys.Has (K .highDegreeSurplusCapacity) known]
    [FactKeys.Has (K .canonicalCapacityExplicit) known]
    [FactKeys.Has (K .canonicalTokenCount) known]
    [FactKeys.Has (K .canonicalBlockedFreePartition) known]
    [FactKeys.Has (K .canonicalLedgerDeficit) known]
    [FactKeys.Has (K .pairCountDeficit) known]
    [FactKeys.Has (K .canonicalCertificationCriterion) known]
    [FactKeys.Has (K .canonicalOverloadOfFits) known]
    [FactKeys.Has (K .canonicalFreeExcessOfCapped) known]
    [FactKeys.Has (K .paperBudgetBound) known]
    [FactKeys.Has (K .paperBudgetCertifies) known]
    [FactKeys.Has (K .pairCodeConfiguration) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    [FactKeys.Has (K .openPortSuppression) known]
    [FactKeys.Has (K .openPortSuppressionSafe) known]
    [FactKeys.Has (K .singleOpenPortSuppressionWitness) known]
    [FactKeys.Has (K .suppressedFamilyCriticalCycle) known]
    [FactKeys.Has (K .sparseSlackSurplus) known]
    [FactKeys.Has (K .activeSurplusFamily) known]
    [FactKeys.Has (K .sparsePortActivation) known]
    [FactKeys.Has (K .activeSurplusDemands) known]
    [FactKeys.Has (K .baselineSpineDemand) known]
    [FactKeys.Has (K .freePairCountFails) known]
    [FactKeys.Has (K .sparseUpperEnvelope) known]
    [FactKeys.Has (K .pairOverlapFirstFailure) known]
    [FactKeys.Has (K .mixedSparseSpineDependence) known]
    [FactKeys.Has (K .exactCubicBaselineBudget) known]
    [FactKeys.Has (K .incrementalSkeletonRoom) known]
    [FactKeys.Has (K .skeletonDominates) known]
    [FactKeys.Has (K .pairOverlapSystem) known]
    [FactKeys.Has (K .pairConditionalFactorizationResidual) known]
    [FactKeys.Has (K .pairCorrelation) known] :
    PairConditionalFactorizationOutcome selected :=
  ⟨(history.get (K .selection)).down,
    (history.get (K .cubicBaseline)).down,
    (history.get (K .minDegreeBaseline)).down,
    (history.get (K .returnAvoidance)).down,
    (history.get (K .noProperBaseline)).down,
    (history.get (K .slackIndependent)).down,
    (history.get (K .tightEndpoint)).down,
    (history.get (K .cycleRankConstraint)).down,
    (history.get (K .degreeProfileFibres)).down,
    (history.get (K .targetCompleteContextUniversality)).down,
    (history.get (K .replacementExclusion)).down,
    (history.get (K .uncompressible)).down,
    (history.get (K .windowPresent)).down,
    (history.get (K .maximalPacking)).down,
    (history.get (K .localAlgebra)).down,
    (history.get (K .packingOrderBound)).down,
    (history.get (K .noSuppressionChordViolation)).down,
    (history.get (K .twoSwitchForcedPath)).down,
    (history.get (K .crossSwitchFamily)).down,
    (history.get (K .highCentreSplitForced)).down,
    (history.get (K .sameVertexSwitchForcedPath)).down,
    (history.get (K .declaredPairSupportStructure)).down,
    (history.get (K .bridgeless)).down,
    (history.get (K .remainderDeficiencyBelowCut)).down,
    (history.get (K .windowCutCapacity)).down,
    (history.get (K .primitiveCarrierCount)).down,
    (history.get (K .singleBoundaryShape)).down,
    (history.get (K .neighbourhoodPairCount)).down,
    (history.get (K .starCycleConstraint)).down,
    (history.get (K .meetingCycleConstraint)).down,
    (history.get (K .highDegreePairSum)).down,
    (history.get (K .vertexDeletionComponents)).down,
    (history.get (K .cyclesThroughVertex)).down,
    (history.get (K .cutVertexBlockPaths)).down,
    (history.get (K .cycleDoubleCount)).down,
    (history.get (K .threeRouteFan)).down,
    (history.get (K .threeRouteChain)).down,
    (history.get (K .windowPositionStubs)).down,
    (history.get (K .windowAttachmentGap)).down,
    (history.get (K .portEndDegree)).down,
    (history.get (K .hubLinkStructure)).down,
    (history.get (K .hubClassCounts)).down,
    (history.get (K .slotRelation)).down,
    (history.get (K .closedClasses)).down,
    (history.get (K .hubTwoHopLinks)).down,
    (history.get (K .slotLinear)).down,
    (history.get (K .remainderPathBounds)).down,
    (history.get (K .windowFreeGeometry)).down,
    (history.get (K .inducedPathAttachment)).down,
    (history.get (K .densityExcess)).down,
    (history.get (K .remainderSlack)).down,
    (history.get (K .hubWindowBudget)).down,
    (history.get (K .windowHubBounds)).down,
    (history.get (K .cubicNeighbourSupply)).down,
    (history.get (K .hubCountBound)).down,
    (history.get (K .lowEdgeParity)).down,
    (history.get (K .bigHubBound)).down,
    (history.get (K .bigHubVShapes)).down,
    (history.get (K .highSurplusBound)).down,
    (history.get (K .hubLengthThreePairs)).down,
    (history.get (K .surplusDartIdentity)).down,
    (history.get (K .highDegreeCountBound)).down,
    (history.get (K .admissibleQuotientsLabelInjective)).down,
    (history.get (K .surplusAbove)).down,
    (history.get (K .highSurplusConfiguration)).down,
    (history.get (K .pairArmAPattern)).down,
    (history.get (K .pairArmARoleAlphabet)).down,
    (history.get (K .pairArmB)).down,
    (history.get (K .extFreeEmpty)).down,
    (history.get (K .extLoadSum)).down,
    (history.get (K .extOverload)).down,
    (history.get (K .extOverloadedToken)).down,
    (history.get (K .newLoadBound)).down,
    (history.get (K .freeSideHubs)).down,
    (history.get (K .separatedPairs)).down,
    (history.get (K .scalePressure)).down,
    (history.get (K .freeSideStructure)).down,
    (history.get (K .freeSideCount)).down,
    (history.get (K .highSurplusOrder)).down,
    (history.get (K .windowChargeKinds)).down,
    (history.get (K .responseObstructionTargetDefect)).down,
    (history.get (K .highEndpointSwitch)).down,
    (history.get (K .edgeSurplusIdentity)).down,
    (history.get (K .ceilSqrtAboveScale)).down,
    (history.get (K .orderAboveScaleSquare)).down,
    (history.get (K .sixVertexExtremalEnvelope)).down,
    (history.get (K .highDegreePositive)).down,
    (history.get (K .highDegreeSurplusCapacity)).down,
    (history.get (K .canonicalCapacityExplicit)).down,
    (history.get (K .canonicalTokenCount)).down,
    (history.get (K .canonicalBlockedFreePartition)).down,
    (history.get (K .canonicalLedgerDeficit)).down,
    (history.get (K .pairCountDeficit)).down,
    (history.get (K .canonicalCertificationCriterion)).down,
    (history.get (K .canonicalOverloadOfFits)).down,
    (history.get (K .canonicalFreeExcessOfCapped)).down,
    (history.get (K .paperBudgetBound)).down,
    (history.get (K .paperBudgetCertifies)).down,
    (history.get (K .pairCodeConfiguration)).down,
    (history.get (K .sparseSurplusSurvivor)).down,
    (history.get (K .openPortSuppression)).down,
    (history.get (K .openPortSuppressionSafe)).down,
    (history.get (K .singleOpenPortSuppressionWitness)).down,
    (history.get (K .suppressedFamilyCriticalCycle)).down,
    (history.get (K .sparseSlackSurplus)).down,
    (history.get (K .activeSurplusFamily)).down,
    (history.get (K .sparsePortActivation)).down,
    (history.get (K .activeSurplusDemands)).down,
    (history.get (K .baselineSpineDemand)).down,
    (history.get (K .freePairCountFails)).down,
    (history.get (K .sparseUpperEnvelope)).down,
    (history.get (K .pairOverlapFirstFailure)).down,
    (history.get (K .mixedSparseSpineDependence)).down,
    (history.get (K .exactCubicBaselineBudget)).down,
    (history.get (K .incrementalSkeletonRoom)).down,
    (history.get (K .skeletonDominates)).down,
    (history.get (K .pairOverlapSystem)).down,
    (history.get (K .pairConditionalFactorizationResidual)).down,
    (history.get (K .pairCorrelation)).down⟩

/-- **Node `[186]`** (thm:main (v), tex 378-385): the visible-entry route-8
residual after [181], [183]-[185], with the joint balances of lem:typeA-
unified-joint-balance.  The explicit conjunction of every fact on its
maximal ledger (154 common facts).  The last twenty-six, in order: the
blob-structure keys 9900--9902 (the pieces of `R` against the windows of `P₀`
and the rate `K .route8Rate` over the pieces); the six CT3 facts
`pieceDominanceIrreducible`, `twoExitNewLength`, `canonicalPieceDominance`,
`canonicalTwoExitNewLength`, `twoExitSizeMonotone`, `canonicalTwoExitSizeMonotone`
(keys 9975--9980); then the packing-exchange keys 9800--9802, the hub-piece mass
9803, the arm-cap keys 9804--9807, the density keys 9700--9704, the small arm
9706 of the net-cap size split, `¬ (F ≤ 14 ∧ SufficientlyLargeForNetCap)`, and the
window-exchange keys 9810--9812 (legal double landings of `X15` on one window of `P₀`,
the two-arm trigger on one window, and the rung bound for a copy of `X15` with exits on
two windows). -/
abbrev Route8JointBalanceOutcome (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .selection selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cubicBaseline selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .minDegreeBaseline selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .returnAvoidance selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .noProperBaseline selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .slackIndependent selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .tightEndpoint selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cycleRankConstraint selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .degreeProfileFibres selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .targetCompleteContextUniversality selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .replacementExclusion selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .uncompressible selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPresent selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .maximalPacking selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .localAlgebra selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .packingOrderBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .noSuppressionChordViolation selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .twoSwitchForcedPath selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .crossSwitchFamily selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highCentreSplitForced selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sameVertexSwitchForcedPath selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .declaredPairSupportStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderDeficiencyBelowCut selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowCutCapacity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .primitiveCarrierCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .singleBoundaryShape selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .neighbourhoodPairCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .starCycleConstraint selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .meetingCycleConstraint selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highDegreePairSum selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .vertexDeletionComponents selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cyclesThroughVertex selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cutVertexBlockPaths selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cycleDoubleCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .threeRouteFan selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .threeRouteChain selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPositionStubs selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowAttachmentGap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .portEndDegree selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubLinkStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubClassCounts selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .slotRelation selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .closedClasses selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubTwoHopLinks selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .slotLinear selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderPathBounds selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowFreeGeometry selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .inducedPathAttachment selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .densityExcess selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderSlack selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubWindowBudget selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowHubBounds selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cubicNeighbourSupply selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubCountBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .lowEdgeParity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .bigHubBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .bigHubVShapes selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highSurplusBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubLengthThreePairs selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .surplusDartIdentity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highDegreeCountBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .admissibleQuotientsLabelInjective selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .surplusAtOrBelow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sparseSurplusSurvivor selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .barrierEnumeration selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageSeparated selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .skeletonDominates selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hotColdPartition selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .barrierCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldHotEntropyCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMass selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldAmbientCubic selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldStubExcess selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldAmbientCubicStubExcess selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldSelectedBranchExcess selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderNormalized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .boundaryDemand selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .stubSupply selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .wedgeSupply selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .curvatureTargetRank selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .exactResponseProfile selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .targetRankCircuit selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .curvatureFullRank selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .forcedCurvatureCost selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .largeBudgetResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .netDeficiencyCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8Rate selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .bridgeless selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldReturnCorridors selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldCorridorState selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldFirstFailureOccurrence selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldFailureCycle selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldFailureCompression selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldHandoffTransfer selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .netChargeLocalization selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBAbsorbedCharge selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highCentreNormalForm selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sameCenterOpenPortCompatibility selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .triangularShoulderCompletion selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .triangularPortReturn selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8BasinBurden selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8CarrierCore selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBBridgeMass selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBBridgeSublinear selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8UnifiedNegative selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeAExclusion selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBBridgeReduction selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8PiecesClassified selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8ExtractedEntryCensus selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBSublinearLedger selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8UnifiedDeficit selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8FoldPeels selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8QuotientFree selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8UnifiedEntryCensus selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8PeelingDescent selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8StageRateFailed selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8DemandLedger selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8DemandAbsorption selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8DemandUnitCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8OpenBoundarySaturated selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8WindowBlockers selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowShadowHitCycle selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowShadowHitExcluded selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8UnpaidTwoCarrier selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8UnpaidExitFourResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8UnifiedVisibleResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8UnifiedVisibleOverload selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8JointBalance selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8PieceWindowAttachment selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8PieceChainCycle selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8PiecewiseRate selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pieceDominanceIrreducible selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .twoExitNewLength selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .canonicalPieceDominance selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .canonicalTwoExitNewLength selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .twoExitSizeMonotone selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .canonicalTwoExitSizeMonotone selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8PackingExchange selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8ArmExchange selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8FullArmLandingCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8HubPieceMass selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8NetCapExcess selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8CleanLandingRules selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8CleanLandingCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8ArmClosureResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8HubFreeDensity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8X15LongLandings selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8HubFreePi selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8HubPieceExcess selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8ArmClosure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8NetCapSmall selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8X15DoubleLanding selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8ArmPairTrigger selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8X15HeavyPair selected.object

/-- The return of `Route8JointBalanceOutcome`: one `get` per fact of
its maximal ledger. -/
theorem route8JointBalanceReturn
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
    [FactKeys.Has (K .packingOrderBound) known]
    [FactKeys.Has (K .noSuppressionChordViolation) known]
    [FactKeys.Has (K .twoSwitchForcedPath) known]
    [FactKeys.Has (K .crossSwitchFamily) known]
    [FactKeys.Has (K .highCentreSplitForced) known]
    [FactKeys.Has (K .sameVertexSwitchForcedPath) known]
    [FactKeys.Has (K .declaredPairSupportStructure) known]
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
    [FactKeys.Has (K .typeBSublinearLedger) known]
    [FactKeys.Has (K .route8UnifiedDeficit) known]
    [FactKeys.Has (K .route8FoldPeels) known]
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
    [FactKeys.Has (K .route8PieceWindowAttachment) known]
    [FactKeys.Has (K .route8PieceChainCycle) known]
    [FactKeys.Has (K .route8PiecewiseRate) known]
    [FactKeys.Has (K .pieceDominanceIrreducible) known]
    [FactKeys.Has (K .twoExitNewLength) known]
    [FactKeys.Has (K .canonicalPieceDominance) known]
    [FactKeys.Has (K .canonicalTwoExitNewLength) known]
    [FactKeys.Has (K .twoExitSizeMonotone) known]
    [FactKeys.Has (K .canonicalTwoExitSizeMonotone) known]
    [FactKeys.Has (K .route8PackingExchange) known]
    [FactKeys.Has (K .route8ArmExchange) known]
    [FactKeys.Has (K .route8FullArmLandingCap) known]
    [FactKeys.Has (K .route8HubPieceMass) known]
    [FactKeys.Has (K .route8NetCapExcess) known]
    [FactKeys.Has (K .route8CleanLandingRules) known]
    [FactKeys.Has (K .route8CleanLandingCap) known]
    [FactKeys.Has (K .route8ArmClosureResidual) known]
    [FactKeys.Has (K .route8HubFreeDensity) known]
    [FactKeys.Has (K .route8X15LongLandings) known]
    [FactKeys.Has (K .route8HubFreePi) known]
    [FactKeys.Has (K .route8HubPieceExcess) known]
    [FactKeys.Has (K .route8ArmClosure) known]
    [FactKeys.Has (K .route8NetCapSmall) known]
    [FactKeys.Has (K .route8X15DoubleLanding) known]
    [FactKeys.Has (K .route8ArmPairTrigger) known]
    [FactKeys.Has (K .route8X15HeavyPair) known] :
    Route8JointBalanceOutcome selected :=
  ⟨(history.get (K .selection)).down,
    (history.get (K .cubicBaseline)).down,
    (history.get (K .minDegreeBaseline)).down,
    (history.get (K .returnAvoidance)).down,
    (history.get (K .noProperBaseline)).down,
    (history.get (K .slackIndependent)).down,
    (history.get (K .tightEndpoint)).down,
    (history.get (K .cycleRankConstraint)).down,
    (history.get (K .degreeProfileFibres)).down,
    (history.get (K .targetCompleteContextUniversality)).down,
    (history.get (K .replacementExclusion)).down,
    (history.get (K .uncompressible)).down,
    (history.get (K .windowPresent)).down,
    (history.get (K .maximalPacking)).down,
    (history.get (K .localAlgebra)).down,
    (history.get (K .packingOrderBound)).down,
    (history.get (K .noSuppressionChordViolation)).down,
    (history.get (K .twoSwitchForcedPath)).down,
    (history.get (K .crossSwitchFamily)).down,
    (history.get (K .highCentreSplitForced)).down,
    (history.get (K .sameVertexSwitchForcedPath)).down,
    (history.get (K .declaredPairSupportStructure)).down,
    (history.get (K .remainderDeficiencyBelowCut)).down,
    (history.get (K .windowCutCapacity)).down,
    (history.get (K .primitiveCarrierCount)).down,
    (history.get (K .singleBoundaryShape)).down,
    (history.get (K .neighbourhoodPairCount)).down,
    (history.get (K .starCycleConstraint)).down,
    (history.get (K .meetingCycleConstraint)).down,
    (history.get (K .highDegreePairSum)).down,
    (history.get (K .vertexDeletionComponents)).down,
    (history.get (K .cyclesThroughVertex)).down,
    (history.get (K .cutVertexBlockPaths)).down,
    (history.get (K .cycleDoubleCount)).down,
    (history.get (K .threeRouteFan)).down,
    (history.get (K .threeRouteChain)).down,
    (history.get (K .windowPositionStubs)).down,
    (history.get (K .windowAttachmentGap)).down,
    (history.get (K .portEndDegree)).down,
    (history.get (K .hubLinkStructure)).down,
    (history.get (K .hubClassCounts)).down,
    (history.get (K .slotRelation)).down,
    (history.get (K .closedClasses)).down,
    (history.get (K .hubTwoHopLinks)).down,
    (history.get (K .slotLinear)).down,
    (history.get (K .remainderPathBounds)).down,
    (history.get (K .windowFreeGeometry)).down,
    (history.get (K .inducedPathAttachment)).down,
    (history.get (K .densityExcess)).down,
    (history.get (K .remainderSlack)).down,
    (history.get (K .hubWindowBudget)).down,
    (history.get (K .windowHubBounds)).down,
    (history.get (K .cubicNeighbourSupply)).down,
    (history.get (K .hubCountBound)).down,
    (history.get (K .lowEdgeParity)).down,
    (history.get (K .bigHubBound)).down,
    (history.get (K .bigHubVShapes)).down,
    (history.get (K .highSurplusBound)).down,
    (history.get (K .hubLengthThreePairs)).down,
    (history.get (K .surplusDartIdentity)).down,
    (history.get (K .highDegreeCountBound)).down,
    (history.get (K .admissibleQuotientsLabelInjective)).down,
    (history.get (K .surplusAtOrBelow)).down,
    (history.get (K .sparseSurplusSurvivor)).down,
    (history.get (K .barrierEnumeration)).down,
    (history.get (K .windowPackageSeparated)).down,
    (history.get (K .skeletonDominates)).down,
    (history.get (K .hotColdPartition)).down,
    (history.get (K .barrierCap)).down,
    (history.get (K .coldHotEntropyCap)).down,
    (history.get (K .coldMass)).down,
    (history.get (K .coldAmbientCubic)).down,
    (history.get (K .coldStubExcess)).down,
    (history.get (K .coldAmbientCubicStubExcess)).down,
    (history.get (K .coldSelectedBranchExcess)).down,
    (history.get (K .remainderNormalized)).down,
    (history.get (K .boundaryDemand)).down,
    (history.get (K .stubSupply)).down,
    (history.get (K .wedgeSupply)).down,
    (history.get (K .curvatureTargetRank)).down,
    (history.get (K .exactResponseProfile)).down,
    (history.get (K .targetRankCircuit)).down,
    (history.get (K .curvatureFullRank)).down,
    (history.get (K .forcedCurvatureCost)).down,
    (history.get (K .largeBudgetResidual)).down,
    (history.get (K .netDeficiencyCap)).down,
    (history.get (K .route8Rate)).down,
    (history.get (K .bridgeless)).down,
    (history.get (K .coldReturnCorridors)).down,
    (history.get (K .coldCorridorState)).down,
    (history.get (K .coldFirstFailureOccurrence)).down,
    (history.get (K .coldFailureCycle)).down,
    (history.get (K .coldFailureCompression)).down,
    (history.get (K .coldHandoffTransfer)).down,
    (history.get (K .netChargeLocalization)).down,
    (history.get (K .typeBAbsorbedCharge)).down,
    (history.get (K .highCentreNormalForm)).down,
    (history.get (K .sameCenterOpenPortCompatibility)).down,
    (history.get (K .triangularShoulderCompletion)).down,
    (history.get (K .triangularPortReturn)).down,
    (history.get (K .route8BasinBurden)).down,
    (history.get (K .route8CarrierCore)).down,
    (history.get (K .typeBBridgeMass)).down,
    (history.get (K .typeBBridgeSublinear)).down,
    (history.get (K .route8UnifiedNegative)).down,
    (history.get (K .typeAExclusion)).down,
    (history.get (K .typeBBridgeReduction)).down,
    (history.get (K .route8PiecesClassified)).down,
    (history.get (K .route8ExtractedEntryCensus)).down,
    (history.get (K .typeBSublinearLedger)).down,
    (history.get (K .route8UnifiedDeficit)).down,
    (history.get (K .route8FoldPeels)).down,
    (history.get (K .route8QuotientFree)).down,
    (history.get (K .route8UnifiedEntryCensus)).down,
    (history.get (K .route8PeelingDescent)).down,
    (history.get (K .route8StageRateFailed)).down,
    (history.get (K .route8DemandLedger)).down,
    (history.get (K .route8DemandAbsorption)).down,
    (history.get (K .route8DemandUnitCount)).down,
    (history.get (K .route8OpenBoundarySaturated)).down,
    (history.get (K .route8WindowBlockers)).down,
    (history.get (K .windowShadowHitCycle)).down,
    (history.get (K .windowShadowHitExcluded)).down,
    (history.get (K .route8UnpaidTwoCarrier)).down,
    (history.get (K .route8UnpaidExitFourResidual)).down,
    (history.get (K .route8UnifiedVisibleResidual)).down,
    (history.get (K .route8UnifiedVisibleOverload)).down,
    (history.get (K .route8JointBalance)).down,
    (history.get (K .route8PieceWindowAttachment)).down,
    (history.get (K .route8PieceChainCycle)).down,
    (history.get (K .route8PiecewiseRate)).down,
    (history.get (K .pieceDominanceIrreducible)).down,
    (history.get (K .twoExitNewLength)).down,
    (history.get (K .canonicalPieceDominance)).down,
    (history.get (K .canonicalTwoExitNewLength)).down,
    (history.get (K .twoExitSizeMonotone)).down,
    (history.get (K .canonicalTwoExitSizeMonotone)).down,
    (history.get (K .route8PackingExchange)).down,
    (history.get (K .route8ArmExchange)).down,
    (history.get (K .route8FullArmLandingCap)).down,
    (history.get (K .route8HubPieceMass)).down,
    (history.get (K .route8NetCapExcess)).down,
    (history.get (K .route8CleanLandingRules)).down,
    (history.get (K .route8CleanLandingCap)).down,
    (history.get (K .route8ArmClosureResidual)).down,
    (history.get (K .route8HubFreeDensity)).down,
    (history.get (K .route8X15LongLandings)).down,
    (history.get (K .route8HubFreePi)).down,
    (history.get (K .route8HubPieceExcess)).down,
    (history.get (K .route8ArmClosure)).down,
    (history.get (K .route8NetCapSmall)).down,
    (history.get (K .route8X15DoubleLanding)).down,
    (history.get (K .route8ArmPairTrigger)).down,
    (history.get (K .route8X15HeavyPair)).down⟩

/-- **Node `[187] ([179]/[180] Type B entry)`** (thm:main (vi), tex 386-403): a
Type B entry produced by the [179] or [180] pair-system outcome, with its
strict-surplus and sparse-survivor ancestry.  The explicit conjunction of
every fact on its maximal ledger (132 common facts, the last the `[179]` early outcome).
(G audit, `[187]`: the `[180]` increment arm is empty at G and closed -- `[180]`'s periodic
alternatives are alternatives of `[179]`'s early outcome at the same returns, so
`K .pairIncrementEarlyOutcome` is incompatible with `K .pairSystemNoEarlyOutcome`; this
residual carries no increment-arm keys.) -/
abbrev PairTypeBOutcome (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .selection selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cubicBaseline selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .minDegreeBaseline selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .returnAvoidance selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .noProperBaseline selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .slackIndependent selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .tightEndpoint selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cycleRankConstraint selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .degreeProfileFibres selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .targetCompleteContextUniversality selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .replacementExclusion selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .uncompressible selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPresent selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .maximalPacking selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .localAlgebra selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .packingOrderBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .noSuppressionChordViolation selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .twoSwitchForcedPath selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .crossSwitchFamily selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highCentreSplitForced selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sameVertexSwitchForcedPath selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .declaredPairSupportStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .bridgeless selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderDeficiencyBelowCut selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowCutCapacity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .primitiveCarrierCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .singleBoundaryShape selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .neighbourhoodPairCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .starCycleConstraint selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .meetingCycleConstraint selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highDegreePairSum selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .vertexDeletionComponents selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cyclesThroughVertex selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cutVertexBlockPaths selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cycleDoubleCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .threeRouteFan selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .threeRouteChain selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPositionStubs selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowAttachmentGap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .portEndDegree selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubLinkStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubClassCounts selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .slotRelation selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .closedClasses selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubTwoHopLinks selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .slotLinear selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderPathBounds selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowFreeGeometry selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .inducedPathAttachment selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .densityExcess selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderSlack selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubWindowBudget selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowHubBounds selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cubicNeighbourSupply selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubCountBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .lowEdgeParity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .bigHubBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .bigHubVShapes selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highSurplusBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubLengthThreePairs selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .surplusDartIdentity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highDegreeCountBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .admissibleQuotientsLabelInjective selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .surplusAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highSurplusConfiguration selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairArmB selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .extFreeEmpty selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .extLoadSum selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .extOverload selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .extOverloadedToken selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .newLoadBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .freeSideHubs selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .separatedPairs selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .scalePressure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .freeSideStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .freeSideCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highSurplusOrder selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowChargeKinds selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .responseObstructionTargetDefect selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highEndpointSwitch selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .edgeSurplusIdentity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .ceilSqrtAboveScale selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .orderAboveScaleSquare selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sixVertexExtremalEnvelope selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highDegreePositive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highDegreeSurplusCapacity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .canonicalCapacityExplicit selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .canonicalTokenCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .canonicalBlockedFreePartition selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .canonicalLedgerDeficit selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairCountDeficit selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .canonicalCertificationCriterion selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .canonicalOverloadOfFits selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .canonicalFreeExcessOfCapped selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .paperBudgetBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .paperBudgetCertifies selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairCodeConfiguration selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sparseSurplusSurvivor selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .openPortSuppression selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .openPortSuppressionSafe selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .singleOpenPortSuppressionWitness selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .suppressedFamilyCriticalCycle selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sparseSlackSurplus selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .activeSurplusFamily selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sparsePortActivation selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .activeSurplusDemands selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .baselineSpineDemand selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .freePairCountFails selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sparseUpperEnvelope selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairOverlapFirstFailure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .mixedSparseSpineDependence selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .exactCubicBaselineBudget selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .incrementalSkeletonRoom selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .skeletonDominates selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairOverlapSystem selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairConditionalFactorization selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairFailureOverlap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairDemandReturns selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairSystemRealizability selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBFanEntry selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairHandoffSupport selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairHandoffCharge selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairHandoffNetCharge selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairHandoffHubCharge selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairHandoffBoundaryType selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairHandoffCriticalCoordinate selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairObstructionDescent selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairHandoffHubForces selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairHandoffDemandEnds selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairHandoffHubBalance selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairHandoffFibreAtG selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairSystemEarlyOutcome selected.object

/-- The return of `PairTypeBOutcome` (arm `system`): one `get` per fact of
its maximal ledger. -/
theorem pairTypeBSystemReturn
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
    [FactKeys.Has (K .packingOrderBound) known]
    [FactKeys.Has (K .noSuppressionChordViolation) known]
    [FactKeys.Has (K .twoSwitchForcedPath) known]
    [FactKeys.Has (K .crossSwitchFamily) known]
    [FactKeys.Has (K .highCentreSplitForced) known]
    [FactKeys.Has (K .sameVertexSwitchForcedPath) known]
    [FactKeys.Has (K .declaredPairSupportStructure) known]
    [FactKeys.Has (K .bridgeless) known]
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
    [FactKeys.Has (K .surplusAbove) known]
    [FactKeys.Has (K .highSurplusConfiguration) known]
    [FactKeys.Has (K .pairArmB) known]
    [FactKeys.Has (K .extFreeEmpty) known]
    [FactKeys.Has (K .extLoadSum) known]
    [FactKeys.Has (K .extOverload) known]
    [FactKeys.Has (K .extOverloadedToken) known]
    [FactKeys.Has (K .newLoadBound) known]
    [FactKeys.Has (K .freeSideHubs) known]
    [FactKeys.Has (K .separatedPairs) known]
    [FactKeys.Has (K .scalePressure) known]
    [FactKeys.Has (K .freeSideStructure) known]
    [FactKeys.Has (K .freeSideCount) known]
    [FactKeys.Has (K .highSurplusOrder) known]
    [FactKeys.Has (K .windowChargeKinds) known]
    [FactKeys.Has (K .responseObstructionTargetDefect) known]
    [FactKeys.Has (K .highEndpointSwitch) known]
    [FactKeys.Has (K .edgeSurplusIdentity) known]
    [FactKeys.Has (K .ceilSqrtAboveScale) known]
    [FactKeys.Has (K .orderAboveScaleSquare) known]
    [FactKeys.Has (K .sixVertexExtremalEnvelope) known]
    [FactKeys.Has (K .highDegreePositive) known]
    [FactKeys.Has (K .highDegreeSurplusCapacity) known]
    [FactKeys.Has (K .canonicalCapacityExplicit) known]
    [FactKeys.Has (K .canonicalTokenCount) known]
    [FactKeys.Has (K .canonicalBlockedFreePartition) known]
    [FactKeys.Has (K .canonicalLedgerDeficit) known]
    [FactKeys.Has (K .pairCountDeficit) known]
    [FactKeys.Has (K .canonicalCertificationCriterion) known]
    [FactKeys.Has (K .canonicalOverloadOfFits) known]
    [FactKeys.Has (K .canonicalFreeExcessOfCapped) known]
    [FactKeys.Has (K .paperBudgetBound) known]
    [FactKeys.Has (K .paperBudgetCertifies) known]
    [FactKeys.Has (K .pairCodeConfiguration) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    [FactKeys.Has (K .openPortSuppression) known]
    [FactKeys.Has (K .openPortSuppressionSafe) known]
    [FactKeys.Has (K .singleOpenPortSuppressionWitness) known]
    [FactKeys.Has (K .suppressedFamilyCriticalCycle) known]
    [FactKeys.Has (K .sparseSlackSurplus) known]
    [FactKeys.Has (K .activeSurplusFamily) known]
    [FactKeys.Has (K .sparsePortActivation) known]
    [FactKeys.Has (K .activeSurplusDemands) known]
    [FactKeys.Has (K .baselineSpineDemand) known]
    [FactKeys.Has (K .freePairCountFails) known]
    [FactKeys.Has (K .sparseUpperEnvelope) known]
    [FactKeys.Has (K .pairOverlapFirstFailure) known]
    [FactKeys.Has (K .mixedSparseSpineDependence) known]
    [FactKeys.Has (K .exactCubicBaselineBudget) known]
    [FactKeys.Has (K .incrementalSkeletonRoom) known]
    [FactKeys.Has (K .skeletonDominates) known]
    [FactKeys.Has (K .pairOverlapSystem) known]
    [FactKeys.Has (K .pairConditionalFactorization) known]
    [FactKeys.Has (K .pairFailureOverlap) known]
    [FactKeys.Has (K .pairDemandReturns) known]
    [FactKeys.Has (K .pairSystemRealizability) known]
    [FactKeys.Has (K .typeBFanEntry) known]
    [FactKeys.Has (K .pairHandoffSupport) known]
    [FactKeys.Has (K .pairHandoffCharge) known]
    [FactKeys.Has (K .pairHandoffNetCharge) known]
    [FactKeys.Has (K .pairHandoffHubCharge) known]
    [FactKeys.Has (K .pairHandoffBoundaryType) known]
    [FactKeys.Has (K .pairHandoffCriticalCoordinate) known]
    [FactKeys.Has (K .pairObstructionDescent) known]
    [FactKeys.Has (K .pairHandoffHubForces) known]
    [FactKeys.Has (K .pairHandoffDemandEnds) known]
    [FactKeys.Has (K .pairHandoffHubBalance) known]
    [FactKeys.Has (K .pairHandoffFibreAtG) known]
    [FactKeys.Has (K .pairSystemEarlyOutcome) known] :
    PairTypeBOutcome selected :=
  ⟨(history.get (K .selection)).down,
    (history.get (K .cubicBaseline)).down,
    (history.get (K .minDegreeBaseline)).down,
    (history.get (K .returnAvoidance)).down,
    (history.get (K .noProperBaseline)).down,
    (history.get (K .slackIndependent)).down,
    (history.get (K .tightEndpoint)).down,
    (history.get (K .cycleRankConstraint)).down,
    (history.get (K .degreeProfileFibres)).down,
    (history.get (K .targetCompleteContextUniversality)).down,
    (history.get (K .replacementExclusion)).down,
    (history.get (K .uncompressible)).down,
    (history.get (K .windowPresent)).down,
    (history.get (K .maximalPacking)).down,
    (history.get (K .localAlgebra)).down,
    (history.get (K .packingOrderBound)).down,
    (history.get (K .noSuppressionChordViolation)).down,
    (history.get (K .twoSwitchForcedPath)).down,
    (history.get (K .crossSwitchFamily)).down,
    (history.get (K .highCentreSplitForced)).down,
    (history.get (K .sameVertexSwitchForcedPath)).down,
    (history.get (K .declaredPairSupportStructure)).down,
    (history.get (K .bridgeless)).down,
    (history.get (K .remainderDeficiencyBelowCut)).down,
    (history.get (K .windowCutCapacity)).down,
    (history.get (K .primitiveCarrierCount)).down,
    (history.get (K .singleBoundaryShape)).down,
    (history.get (K .neighbourhoodPairCount)).down,
    (history.get (K .starCycleConstraint)).down,
    (history.get (K .meetingCycleConstraint)).down,
    (history.get (K .highDegreePairSum)).down,
    (history.get (K .vertexDeletionComponents)).down,
    (history.get (K .cyclesThroughVertex)).down,
    (history.get (K .cutVertexBlockPaths)).down,
    (history.get (K .cycleDoubleCount)).down,
    (history.get (K .threeRouteFan)).down,
    (history.get (K .threeRouteChain)).down,
    (history.get (K .windowPositionStubs)).down,
    (history.get (K .windowAttachmentGap)).down,
    (history.get (K .portEndDegree)).down,
    (history.get (K .hubLinkStructure)).down,
    (history.get (K .hubClassCounts)).down,
    (history.get (K .slotRelation)).down,
    (history.get (K .closedClasses)).down,
    (history.get (K .hubTwoHopLinks)).down,
    (history.get (K .slotLinear)).down,
    (history.get (K .remainderPathBounds)).down,
    (history.get (K .windowFreeGeometry)).down,
    (history.get (K .inducedPathAttachment)).down,
    (history.get (K .densityExcess)).down,
    (history.get (K .remainderSlack)).down,
    (history.get (K .hubWindowBudget)).down,
    (history.get (K .windowHubBounds)).down,
    (history.get (K .cubicNeighbourSupply)).down,
    (history.get (K .hubCountBound)).down,
    (history.get (K .lowEdgeParity)).down,
    (history.get (K .bigHubBound)).down,
    (history.get (K .bigHubVShapes)).down,
    (history.get (K .highSurplusBound)).down,
    (history.get (K .hubLengthThreePairs)).down,
    (history.get (K .surplusDartIdentity)).down,
    (history.get (K .highDegreeCountBound)).down,
    (history.get (K .admissibleQuotientsLabelInjective)).down,
    (history.get (K .surplusAbove)).down,
    (history.get (K .highSurplusConfiguration)).down,
    (history.get (K .pairArmB)).down,
    (history.get (K .extFreeEmpty)).down,
    (history.get (K .extLoadSum)).down,
    (history.get (K .extOverload)).down,
    (history.get (K .extOverloadedToken)).down,
    (history.get (K .newLoadBound)).down,
    (history.get (K .freeSideHubs)).down,
    (history.get (K .separatedPairs)).down,
    (history.get (K .scalePressure)).down,
    (history.get (K .freeSideStructure)).down,
    (history.get (K .freeSideCount)).down,
    (history.get (K .highSurplusOrder)).down,
    (history.get (K .windowChargeKinds)).down,
    (history.get (K .responseObstructionTargetDefect)).down,
    (history.get (K .highEndpointSwitch)).down,
    (history.get (K .edgeSurplusIdentity)).down,
    (history.get (K .ceilSqrtAboveScale)).down,
    (history.get (K .orderAboveScaleSquare)).down,
    (history.get (K .sixVertexExtremalEnvelope)).down,
    (history.get (K .highDegreePositive)).down,
    (history.get (K .highDegreeSurplusCapacity)).down,
    (history.get (K .canonicalCapacityExplicit)).down,
    (history.get (K .canonicalTokenCount)).down,
    (history.get (K .canonicalBlockedFreePartition)).down,
    (history.get (K .canonicalLedgerDeficit)).down,
    (history.get (K .pairCountDeficit)).down,
    (history.get (K .canonicalCertificationCriterion)).down,
    (history.get (K .canonicalOverloadOfFits)).down,
    (history.get (K .canonicalFreeExcessOfCapped)).down,
    (history.get (K .paperBudgetBound)).down,
    (history.get (K .paperBudgetCertifies)).down,
    (history.get (K .pairCodeConfiguration)).down,
    (history.get (K .sparseSurplusSurvivor)).down,
    (history.get (K .openPortSuppression)).down,
    (history.get (K .openPortSuppressionSafe)).down,
    (history.get (K .singleOpenPortSuppressionWitness)).down,
    (history.get (K .suppressedFamilyCriticalCycle)).down,
    (history.get (K .sparseSlackSurplus)).down,
    (history.get (K .activeSurplusFamily)).down,
    (history.get (K .sparsePortActivation)).down,
    (history.get (K .activeSurplusDemands)).down,
    (history.get (K .baselineSpineDemand)).down,
    (history.get (K .freePairCountFails)).down,
    (history.get (K .sparseUpperEnvelope)).down,
    (history.get (K .pairOverlapFirstFailure)).down,
    (history.get (K .mixedSparseSpineDependence)).down,
    (history.get (K .exactCubicBaselineBudget)).down,
    (history.get (K .incrementalSkeletonRoom)).down,
    (history.get (K .skeletonDominates)).down,
    (history.get (K .pairOverlapSystem)).down,
    (history.get (K .pairConditionalFactorization)).down,
    (history.get (K .pairFailureOverlap)).down,
    (history.get (K .pairDemandReturns)).down,
    (history.get (K .pairSystemRealizability)).down,
    (history.get (K .typeBFanEntry)).down,
    (history.get (K .pairHandoffSupport)).down,
    (history.get (K .pairHandoffCharge)).down,
    (history.get (K .pairHandoffNetCharge)).down,
    (history.get (K .pairHandoffHubCharge)).down,
    (history.get (K .pairHandoffBoundaryType)).down,
    (history.get (K .pairHandoffCriticalCoordinate)).down,
    (history.get (K .pairObstructionDescent)).down,
    (history.get (K .pairHandoffHubForces)).down,
    (history.get (K .pairHandoffDemandEnds)).down,
    (history.get (K .pairHandoffHubBalance)).down,
    (history.get (K .pairHandoffFibreAtG)).down,
    (history.get (K .pairSystemEarlyOutcome)).down⟩

/-- **Node `[187] (Type B sublinear failure)`** (thm:main (vi), tex 386-403):
failure of the Type B sublinear hypothesis package on the unified route-8
ledger.  The explicit conjunction of every fact on its maximal ledger (128
common facts). -/
abbrev TypeBSublinearOutcome (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .selection selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cubicBaseline selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .minDegreeBaseline selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .returnAvoidance selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .noProperBaseline selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .slackIndependent selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .tightEndpoint selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cycleRankConstraint selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .degreeProfileFibres selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .targetCompleteContextUniversality selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .replacementExclusion selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .uncompressible selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPresent selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .maximalPacking selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .localAlgebra selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .packingOrderBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .noSuppressionChordViolation selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .twoSwitchForcedPath selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .crossSwitchFamily selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highCentreSplitForced selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sameVertexSwitchForcedPath selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .declaredPairSupportStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderDeficiencyBelowCut selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowCutCapacity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .primitiveCarrierCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .singleBoundaryShape selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .neighbourhoodPairCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .starCycleConstraint selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .meetingCycleConstraint selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highDegreePairSum selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .vertexDeletionComponents selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cyclesThroughVertex selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cutVertexBlockPaths selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cycleDoubleCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .threeRouteFan selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .threeRouteChain selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPositionStubs selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowAttachmentGap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .portEndDegree selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubLinkStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubClassCounts selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .slotRelation selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .closedClasses selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubTwoHopLinks selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .slotLinear selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderPathBounds selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowFreeGeometry selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .inducedPathAttachment selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .densityExcess selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderSlack selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubWindowBudget selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowHubBounds selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cubicNeighbourSupply selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubCountBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .lowEdgeParity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .bigHubBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .bigHubVShapes selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highSurplusBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubLengthThreePairs selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .surplusDartIdentity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highDegreeCountBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .admissibleQuotientsLabelInjective selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .surplusAtOrBelow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sparseSurplusSurvivor selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .barrierEnumeration selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageSeparated selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .skeletonDominates selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hotColdPartition selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .barrierCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldHotEntropyCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMass selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldAmbientCubic selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldStubExcess selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldAmbientCubicStubExcess selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldSelectedBranchExcess selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderNormalized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .boundaryDemand selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .stubSupply selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .wedgeSupply selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .curvatureTargetRank selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .exactResponseProfile selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .targetRankCircuit selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .curvatureFullRank selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .forcedCurvatureCost selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .largeBudgetResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .netDeficiencyCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8Rate selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .bridgeless selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldReturnCorridors selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldCorridorState selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldFirstFailureOccurrence selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldFailureCycle selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldFailureCompression selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldHandoffTransfer selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .netChargeLocalization selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBAbsorbedCharge selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highCentreNormalForm selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sameCenterOpenPortCompatibility selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .triangularShoulderCompletion selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .triangularPortReturn selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8BasinBurden selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8CarrierCore selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBBridgeMass selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBBridgeSublinear selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8UnifiedNegative selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeAExclusion selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBBridgeReduction selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8PiecesClassified selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8ExtractedEntryCensus selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBSublinearResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBSublinearCanonicalForm selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .groupedAbsorbedCoreSubset selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBSublinearFailureArms selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .groupedCentresHigh selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .handoffDegreeClauseEmpty selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pieceRoutingTotal selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coverPayment selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .loadFailureSaturated selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .unpaidAbsorbedWindowPort selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .receiverPortsAreWindowStubs selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .saturatedReceiverBasin selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .loadFlowValue selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coverFlowValue selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pieceSizeProfile selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .bridgePieceMassDichotomy selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .traceIntoCentreStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .traceIntoAbsorbedStructure selected.object

/-- The return of `TypeBSublinearOutcome`: one `get` per fact of
its maximal ledger. -/
theorem typeBSublinearReturn
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
    [FactKeys.Has (K .packingOrderBound) known]
    [FactKeys.Has (K .noSuppressionChordViolation) known]
    [FactKeys.Has (K .twoSwitchForcedPath) known]
    [FactKeys.Has (K .crossSwitchFamily) known]
    [FactKeys.Has (K .highCentreSplitForced) known]
    [FactKeys.Has (K .sameVertexSwitchForcedPath) known]
    [FactKeys.Has (K .declaredPairSupportStructure) known]
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
    [FactKeys.Has (K .traceIntoAbsorbedStructure) known] :
    TypeBSublinearOutcome selected :=
  ⟨(history.get (K .selection)).down,
    (history.get (K .cubicBaseline)).down,
    (history.get (K .minDegreeBaseline)).down,
    (history.get (K .returnAvoidance)).down,
    (history.get (K .noProperBaseline)).down,
    (history.get (K .slackIndependent)).down,
    (history.get (K .tightEndpoint)).down,
    (history.get (K .cycleRankConstraint)).down,
    (history.get (K .degreeProfileFibres)).down,
    (history.get (K .targetCompleteContextUniversality)).down,
    (history.get (K .replacementExclusion)).down,
    (history.get (K .uncompressible)).down,
    (history.get (K .windowPresent)).down,
    (history.get (K .maximalPacking)).down,
    (history.get (K .localAlgebra)).down,
    (history.get (K .packingOrderBound)).down,
    (history.get (K .noSuppressionChordViolation)).down,
    (history.get (K .twoSwitchForcedPath)).down,
    (history.get (K .crossSwitchFamily)).down,
    (history.get (K .highCentreSplitForced)).down,
    (history.get (K .sameVertexSwitchForcedPath)).down,
    (history.get (K .declaredPairSupportStructure)).down,
    (history.get (K .remainderDeficiencyBelowCut)).down,
    (history.get (K .windowCutCapacity)).down,
    (history.get (K .primitiveCarrierCount)).down,
    (history.get (K .singleBoundaryShape)).down,
    (history.get (K .neighbourhoodPairCount)).down,
    (history.get (K .starCycleConstraint)).down,
    (history.get (K .meetingCycleConstraint)).down,
    (history.get (K .highDegreePairSum)).down,
    (history.get (K .vertexDeletionComponents)).down,
    (history.get (K .cyclesThroughVertex)).down,
    (history.get (K .cutVertexBlockPaths)).down,
    (history.get (K .cycleDoubleCount)).down,
    (history.get (K .threeRouteFan)).down,
    (history.get (K .threeRouteChain)).down,
    (history.get (K .windowPositionStubs)).down,
    (history.get (K .windowAttachmentGap)).down,
    (history.get (K .portEndDegree)).down,
    (history.get (K .hubLinkStructure)).down,
    (history.get (K .hubClassCounts)).down,
    (history.get (K .slotRelation)).down,
    (history.get (K .closedClasses)).down,
    (history.get (K .hubTwoHopLinks)).down,
    (history.get (K .slotLinear)).down,
    (history.get (K .remainderPathBounds)).down,
    (history.get (K .windowFreeGeometry)).down,
    (history.get (K .inducedPathAttachment)).down,
    (history.get (K .densityExcess)).down,
    (history.get (K .remainderSlack)).down,
    (history.get (K .hubWindowBudget)).down,
    (history.get (K .windowHubBounds)).down,
    (history.get (K .cubicNeighbourSupply)).down,
    (history.get (K .hubCountBound)).down,
    (history.get (K .lowEdgeParity)).down,
    (history.get (K .bigHubBound)).down,
    (history.get (K .bigHubVShapes)).down,
    (history.get (K .highSurplusBound)).down,
    (history.get (K .hubLengthThreePairs)).down,
    (history.get (K .surplusDartIdentity)).down,
    (history.get (K .highDegreeCountBound)).down,
    (history.get (K .admissibleQuotientsLabelInjective)).down,
    (history.get (K .surplusAtOrBelow)).down,
    (history.get (K .sparseSurplusSurvivor)).down,
    (history.get (K .barrierEnumeration)).down,
    (history.get (K .windowPackageSeparated)).down,
    (history.get (K .skeletonDominates)).down,
    (history.get (K .hotColdPartition)).down,
    (history.get (K .barrierCap)).down,
    (history.get (K .coldHotEntropyCap)).down,
    (history.get (K .coldMass)).down,
    (history.get (K .coldAmbientCubic)).down,
    (history.get (K .coldStubExcess)).down,
    (history.get (K .coldAmbientCubicStubExcess)).down,
    (history.get (K .coldSelectedBranchExcess)).down,
    (history.get (K .remainderNormalized)).down,
    (history.get (K .boundaryDemand)).down,
    (history.get (K .stubSupply)).down,
    (history.get (K .wedgeSupply)).down,
    (history.get (K .curvatureTargetRank)).down,
    (history.get (K .exactResponseProfile)).down,
    (history.get (K .targetRankCircuit)).down,
    (history.get (K .curvatureFullRank)).down,
    (history.get (K .forcedCurvatureCost)).down,
    (history.get (K .largeBudgetResidual)).down,
    (history.get (K .netDeficiencyCap)).down,
    (history.get (K .route8Rate)).down,
    (history.get (K .bridgeless)).down,
    (history.get (K .coldReturnCorridors)).down,
    (history.get (K .coldCorridorState)).down,
    (history.get (K .coldFirstFailureOccurrence)).down,
    (history.get (K .coldFailureCycle)).down,
    (history.get (K .coldFailureCompression)).down,
    (history.get (K .coldHandoffTransfer)).down,
    (history.get (K .netChargeLocalization)).down,
    (history.get (K .typeBAbsorbedCharge)).down,
    (history.get (K .highCentreNormalForm)).down,
    (history.get (K .sameCenterOpenPortCompatibility)).down,
    (history.get (K .triangularShoulderCompletion)).down,
    (history.get (K .triangularPortReturn)).down,
    (history.get (K .route8BasinBurden)).down,
    (history.get (K .route8CarrierCore)).down,
    (history.get (K .typeBBridgeMass)).down,
    (history.get (K .typeBBridgeSublinear)).down,
    (history.get (K .route8UnifiedNegative)).down,
    (history.get (K .typeAExclusion)).down,
    (history.get (K .typeBBridgeReduction)).down,
    (history.get (K .route8PiecesClassified)).down,
    (history.get (K .route8ExtractedEntryCensus)).down,
    (history.get (K .typeBSublinearResidual)).down,
    (history.get (K .typeBSublinearCanonicalForm)).down,
    (history.get (K .groupedAbsorbedCoreSubset)).down,
    (history.get (K .typeBSublinearFailureArms)).down,
    (history.get (K .groupedCentresHigh)).down,
    (history.get (K .handoffDegreeClauseEmpty)).down,
    (history.get (K .pieceRoutingTotal)).down,
    (history.get (K .coverPayment)).down,
    (history.get (K .loadFailureSaturated)).down,
    (history.get (K .unpaidAbsorbedWindowPort)).down,
    (history.get (K .receiverPortsAreWindowStubs)).down,
    (history.get (K .saturatedReceiverBasin)).down,
    (history.get (K .loadFlowValue)).down,
    (history.get (K .coverFlowValue)).down,
    (history.get (K .pieceSizeProfile)).down,
    (history.get (K .bridgePieceMassDichotomy)).down,
    (history.get (K .traceIntoCentreStructure)).down,
    (history.get (K .traceIntoAbsorbedStructure)).down⟩

/-- **Node `[187] ([348], route-8 quotient failure)`** (thm:main (vi), tex
386-403): failure of route-8 quotient freeness of the unified
census.  The explicit conjunction of every fact on its maximal ledger (142
common facts); the fact
`K .route8QuotientEntriesAtG` decides the quotient test at G (the failure
is the non-emptiness of the unified entry family, with the aggregate bound
`|∂R| < δ·|\tilde\Xi|`) and the one before it, `K .route8PeelingDescent`, is the
stage accounting that fact consumes.
The conjunction closes with the blob-structure keys 9900--9902 (the pieces of `R`
against the windows of `P₀`, and the rate `K .route8Rate` over the pieces), then the
six CT3 facts (dominance irreducibility of G's pieces, keys 9975--9980), then the
packing-exchange keys 9800--9802, the hub-piece mass 9803 and the arm-cap keys
9804--9807, then the density keys 9700--9704 and the small arm 9706 of the net-cap size
split (`¬ (F ≤ 14 ∧ SufficientlyLargeForNetCap)`), then the window-exchange keys
9810--9812 (legal double landings of `X15` on one window of `P₀`, the two-arm trigger on
one window, and the rung bound for a copy of `X15` with exits on two windows). -/
abbrev Route8QuotientOutcome (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .selection selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cubicBaseline selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .minDegreeBaseline selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .returnAvoidance selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .noProperBaseline selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .slackIndependent selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .tightEndpoint selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cycleRankConstraint selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .degreeProfileFibres selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .targetCompleteContextUniversality selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .replacementExclusion selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .uncompressible selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPresent selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .maximalPacking selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .localAlgebra selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .packingOrderBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .noSuppressionChordViolation selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .twoSwitchForcedPath selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .crossSwitchFamily selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highCentreSplitForced selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sameVertexSwitchForcedPath selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .declaredPairSupportStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderDeficiencyBelowCut selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowCutCapacity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .primitiveCarrierCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .singleBoundaryShape selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .neighbourhoodPairCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .starCycleConstraint selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .meetingCycleConstraint selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highDegreePairSum selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .vertexDeletionComponents selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cyclesThroughVertex selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cutVertexBlockPaths selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cycleDoubleCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .threeRouteFan selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .threeRouteChain selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPositionStubs selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowAttachmentGap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .portEndDegree selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubLinkStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubClassCounts selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .slotRelation selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .closedClasses selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubTwoHopLinks selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .slotLinear selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderPathBounds selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowFreeGeometry selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .inducedPathAttachment selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .densityExcess selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderSlack selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubWindowBudget selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowHubBounds selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cubicNeighbourSupply selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubCountBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .lowEdgeParity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .bigHubBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .bigHubVShapes selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highSurplusBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubLengthThreePairs selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .surplusDartIdentity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highDegreeCountBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .admissibleQuotientsLabelInjective selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .surplusAtOrBelow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sparseSurplusSurvivor selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .barrierEnumeration selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageSeparated selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .skeletonDominates selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hotColdPartition selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .barrierCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldHotEntropyCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMass selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldAmbientCubic selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldStubExcess selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldAmbientCubicStubExcess selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldSelectedBranchExcess selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderNormalized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .boundaryDemand selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .stubSupply selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .wedgeSupply selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .curvatureTargetRank selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .exactResponseProfile selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .targetRankCircuit selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .curvatureFullRank selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .forcedCurvatureCost selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .largeBudgetResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .netDeficiencyCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8Rate selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .bridgeless selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldReturnCorridors selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldCorridorState selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldFirstFailureOccurrence selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldFailureCycle selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldFailureCompression selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldHandoffTransfer selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .netChargeLocalization selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBAbsorbedCharge selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highCentreNormalForm selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sameCenterOpenPortCompatibility selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .triangularShoulderCompletion selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .triangularPortReturn selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8BasinBurden selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8CarrierCore selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBBridgeMass selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBBridgeSublinear selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8UnifiedNegative selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeAExclusion selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBBridgeReduction selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8PiecesClassified selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8ExtractedEntryCensus selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBSublinearLedger selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8UnifiedDeficit selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8FoldPeels selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8QuotientResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8PeelingDescent selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8QuotientEntriesAtG selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8PieceWindowAttachment selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8PieceChainCycle selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8PiecewiseRate selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pieceDominanceIrreducible selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .twoExitNewLength selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .canonicalPieceDominance selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .canonicalTwoExitNewLength selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .twoExitSizeMonotone selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .canonicalTwoExitSizeMonotone selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8PackingExchange selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8ArmExchange selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8FullArmLandingCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8HubPieceMass selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8NetCapExcess selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8CleanLandingRules selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8CleanLandingCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8ArmClosureResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8HubFreeDensity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8X15LongLandings selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8HubFreePi selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8HubPieceExcess selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8ArmClosure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8NetCapSmall selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8X15DoubleLanding selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8ArmPairTrigger selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8X15HeavyPair selected.object

/-- The return of `Route8QuotientOutcome`: one `get` per fact of
its maximal ledger. -/
theorem route8QuotientReturn
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
    [FactKeys.Has (K .packingOrderBound) known]
    [FactKeys.Has (K .noSuppressionChordViolation) known]
    [FactKeys.Has (K .twoSwitchForcedPath) known]
    [FactKeys.Has (K .crossSwitchFamily) known]
    [FactKeys.Has (K .highCentreSplitForced) known]
    [FactKeys.Has (K .sameVertexSwitchForcedPath) known]
    [FactKeys.Has (K .declaredPairSupportStructure) known]
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
    [FactKeys.Has (K .typeBSublinearLedger) known]
    [FactKeys.Has (K .route8UnifiedDeficit) known]
    [FactKeys.Has (K .route8FoldPeels) known]
    [FactKeys.Has (K .route8QuotientResidual) known]
    [FactKeys.Has (K .route8PeelingDescent) known]
    [FactKeys.Has (K .route8QuotientEntriesAtG) known]
    [FactKeys.Has (K .route8PieceWindowAttachment) known]
    [FactKeys.Has (K .route8PieceChainCycle) known]
    [FactKeys.Has (K .route8PiecewiseRate) known]
    [FactKeys.Has (K .pieceDominanceIrreducible) known]
    [FactKeys.Has (K .twoExitNewLength) known]
    [FactKeys.Has (K .canonicalPieceDominance) known]
    [FactKeys.Has (K .canonicalTwoExitNewLength) known]
    [FactKeys.Has (K .twoExitSizeMonotone) known]
    [FactKeys.Has (K .canonicalTwoExitSizeMonotone) known]
    [FactKeys.Has (K .route8PackingExchange) known]
    [FactKeys.Has (K .route8ArmExchange) known]
    [FactKeys.Has (K .route8FullArmLandingCap) known]
    [FactKeys.Has (K .route8HubPieceMass) known]
    [FactKeys.Has (K .route8NetCapExcess) known]
    [FactKeys.Has (K .route8CleanLandingRules) known]
    [FactKeys.Has (K .route8CleanLandingCap) known]
    [FactKeys.Has (K .route8ArmClosureResidual) known]
    [FactKeys.Has (K .route8HubFreeDensity) known]
    [FactKeys.Has (K .route8X15LongLandings) known]
    [FactKeys.Has (K .route8HubFreePi) known]
    [FactKeys.Has (K .route8HubPieceExcess) known]
    [FactKeys.Has (K .route8ArmClosure) known]
    [FactKeys.Has (K .route8NetCapSmall) known]
    [FactKeys.Has (K .route8X15DoubleLanding) known]
    [FactKeys.Has (K .route8ArmPairTrigger) known]
    [FactKeys.Has (K .route8X15HeavyPair) known] :
    Route8QuotientOutcome selected :=
  ⟨(history.get (K .selection)).down,
    (history.get (K .cubicBaseline)).down,
    (history.get (K .minDegreeBaseline)).down,
    (history.get (K .returnAvoidance)).down,
    (history.get (K .noProperBaseline)).down,
    (history.get (K .slackIndependent)).down,
    (history.get (K .tightEndpoint)).down,
    (history.get (K .cycleRankConstraint)).down,
    (history.get (K .degreeProfileFibres)).down,
    (history.get (K .targetCompleteContextUniversality)).down,
    (history.get (K .replacementExclusion)).down,
    (history.get (K .uncompressible)).down,
    (history.get (K .windowPresent)).down,
    (history.get (K .maximalPacking)).down,
    (history.get (K .localAlgebra)).down,
    (history.get (K .packingOrderBound)).down,
    (history.get (K .noSuppressionChordViolation)).down,
    (history.get (K .twoSwitchForcedPath)).down,
    (history.get (K .crossSwitchFamily)).down,
    (history.get (K .highCentreSplitForced)).down,
    (history.get (K .sameVertexSwitchForcedPath)).down,
    (history.get (K .declaredPairSupportStructure)).down,
    (history.get (K .remainderDeficiencyBelowCut)).down,
    (history.get (K .windowCutCapacity)).down,
    (history.get (K .primitiveCarrierCount)).down,
    (history.get (K .singleBoundaryShape)).down,
    (history.get (K .neighbourhoodPairCount)).down,
    (history.get (K .starCycleConstraint)).down,
    (history.get (K .meetingCycleConstraint)).down,
    (history.get (K .highDegreePairSum)).down,
    (history.get (K .vertexDeletionComponents)).down,
    (history.get (K .cyclesThroughVertex)).down,
    (history.get (K .cutVertexBlockPaths)).down,
    (history.get (K .cycleDoubleCount)).down,
    (history.get (K .threeRouteFan)).down,
    (history.get (K .threeRouteChain)).down,
    (history.get (K .windowPositionStubs)).down,
    (history.get (K .windowAttachmentGap)).down,
    (history.get (K .portEndDegree)).down,
    (history.get (K .hubLinkStructure)).down,
    (history.get (K .hubClassCounts)).down,
    (history.get (K .slotRelation)).down,
    (history.get (K .closedClasses)).down,
    (history.get (K .hubTwoHopLinks)).down,
    (history.get (K .slotLinear)).down,
    (history.get (K .remainderPathBounds)).down,
    (history.get (K .windowFreeGeometry)).down,
    (history.get (K .inducedPathAttachment)).down,
    (history.get (K .densityExcess)).down,
    (history.get (K .remainderSlack)).down,
    (history.get (K .hubWindowBudget)).down,
    (history.get (K .windowHubBounds)).down,
    (history.get (K .cubicNeighbourSupply)).down,
    (history.get (K .hubCountBound)).down,
    (history.get (K .lowEdgeParity)).down,
    (history.get (K .bigHubBound)).down,
    (history.get (K .bigHubVShapes)).down,
    (history.get (K .highSurplusBound)).down,
    (history.get (K .hubLengthThreePairs)).down,
    (history.get (K .surplusDartIdentity)).down,
    (history.get (K .highDegreeCountBound)).down,
    (history.get (K .admissibleQuotientsLabelInjective)).down,
    (history.get (K .surplusAtOrBelow)).down,
    (history.get (K .sparseSurplusSurvivor)).down,
    (history.get (K .barrierEnumeration)).down,
    (history.get (K .windowPackageSeparated)).down,
    (history.get (K .skeletonDominates)).down,
    (history.get (K .hotColdPartition)).down,
    (history.get (K .barrierCap)).down,
    (history.get (K .coldHotEntropyCap)).down,
    (history.get (K .coldMass)).down,
    (history.get (K .coldAmbientCubic)).down,
    (history.get (K .coldStubExcess)).down,
    (history.get (K .coldAmbientCubicStubExcess)).down,
    (history.get (K .coldSelectedBranchExcess)).down,
    (history.get (K .remainderNormalized)).down,
    (history.get (K .boundaryDemand)).down,
    (history.get (K .stubSupply)).down,
    (history.get (K .wedgeSupply)).down,
    (history.get (K .curvatureTargetRank)).down,
    (history.get (K .exactResponseProfile)).down,
    (history.get (K .targetRankCircuit)).down,
    (history.get (K .curvatureFullRank)).down,
    (history.get (K .forcedCurvatureCost)).down,
    (history.get (K .largeBudgetResidual)).down,
    (history.get (K .netDeficiencyCap)).down,
    (history.get (K .route8Rate)).down,
    (history.get (K .bridgeless)).down,
    (history.get (K .coldReturnCorridors)).down,
    (history.get (K .coldCorridorState)).down,
    (history.get (K .coldFirstFailureOccurrence)).down,
    (history.get (K .coldFailureCycle)).down,
    (history.get (K .coldFailureCompression)).down,
    (history.get (K .coldHandoffTransfer)).down,
    (history.get (K .netChargeLocalization)).down,
    (history.get (K .typeBAbsorbedCharge)).down,
    (history.get (K .highCentreNormalForm)).down,
    (history.get (K .sameCenterOpenPortCompatibility)).down,
    (history.get (K .triangularShoulderCompletion)).down,
    (history.get (K .triangularPortReturn)).down,
    (history.get (K .route8BasinBurden)).down,
    (history.get (K .route8CarrierCore)).down,
    (history.get (K .typeBBridgeMass)).down,
    (history.get (K .typeBBridgeSublinear)).down,
    (history.get (K .route8UnifiedNegative)).down,
    (history.get (K .typeAExclusion)).down,
    (history.get (K .typeBBridgeReduction)).down,
    (history.get (K .route8PiecesClassified)).down,
    (history.get (K .route8ExtractedEntryCensus)).down,
    (history.get (K .typeBSublinearLedger)).down,
    (history.get (K .route8UnifiedDeficit)).down,
    (history.get (K .route8FoldPeels)).down,
    (history.get (K .route8QuotientResidual)).down,
    (history.get (K .route8PeelingDescent)).down,
    (history.get (K .route8QuotientEntriesAtG)).down,
    (history.get (K .route8PieceWindowAttachment)).down,
    (history.get (K .route8PieceChainCycle)).down,
    (history.get (K .route8PiecewiseRate)).down,
    (history.get (K .pieceDominanceIrreducible)).down,
    (history.get (K .twoExitNewLength)).down,
    (history.get (K .canonicalPieceDominance)).down,
    (history.get (K .canonicalTwoExitNewLength)).down,
    (history.get (K .twoExitSizeMonotone)).down,
    (history.get (K .canonicalTwoExitSizeMonotone)).down,
    (history.get (K .route8PackingExchange)).down,
    (history.get (K .route8ArmExchange)).down,
    (history.get (K .route8FullArmLandingCap)).down,
    (history.get (K .route8HubPieceMass)).down,
    (history.get (K .route8NetCapExcess)).down,
    (history.get (K .route8CleanLandingRules)).down,
    (history.get (K .route8CleanLandingCap)).down,
    (history.get (K .route8ArmClosureResidual)).down,
    (history.get (K .route8HubFreeDensity)).down,
    (history.get (K .route8X15LongLandings)).down,
    (history.get (K .route8HubFreePi)).down,
    (history.get (K .route8HubPieceExcess)).down,
    (history.get (K .route8ArmClosure)).down,
    (history.get (K .route8NetCapSmall)).down,
    (history.get (K .route8X15DoubleLanding)).down,
    (history.get (K .route8ArmPairTrigger)).down,
    (history.get (K .route8X15HeavyPair)).down⟩

/-- **Node `[187] (private-carrier rate failure)`** (thm:main (vi), tex
386-403): failure of the exact private-carrier rate at the entry of the
route-8 continuation.  The explicit conjunction of every fact on its maximal
ledger (112 common facts: the first 91 facts and the G-audit facts
`route8RateFailsJoin`, `route8RateFailsPiece`, `route8RateFailsCrossBound`,
`route8RateFailsFlow`, `route8CarrierInjection`, `route8RateExactSlack`,
`route8BasinBurden`, `route8StubDeficit`, `route8DeficitVsStubs`, `route8EntryLowerBound`, `route8CoreEmpty`,
`route8StrongRate`, `route8ThinIsolation`, `route8WindowStub`, `route8ThinSmall`,
`route8WindowRPathGap`, `route8HubStubs`,
`route8WindowSelfRPathGap`, `route8PieceBoundary`,
`route8WindowPieceRank`, `route8AchievableLengths`).  `K .route8RateFails` is the
failed manuscript rate `δ|R| ≤ (δs+1)|∂R| + δ·F·s·T(n)`. -/
abbrev Route8RateFailsOutcome (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .selection selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cubicBaseline selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .minDegreeBaseline selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .returnAvoidance selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .noProperBaseline selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .slackIndependent selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .tightEndpoint selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cycleRankConstraint selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .degreeProfileFibres selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .targetCompleteContextUniversality selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .replacementExclusion selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .uncompressible selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPresent selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .maximalPacking selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .localAlgebra selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .packingOrderBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .noSuppressionChordViolation selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .twoSwitchForcedPath selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .crossSwitchFamily selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highCentreSplitForced selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sameVertexSwitchForcedPath selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .declaredPairSupportStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .bridgeless selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderDeficiencyBelowCut selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowCutCapacity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .primitiveCarrierCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .singleBoundaryShape selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .neighbourhoodPairCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .starCycleConstraint selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .meetingCycleConstraint selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highDegreePairSum selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .vertexDeletionComponents selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cyclesThroughVertex selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cutVertexBlockPaths selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cycleDoubleCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .threeRouteFan selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .threeRouteChain selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPositionStubs selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowAttachmentGap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .portEndDegree selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubLinkStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubClassCounts selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .slotRelation selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .closedClasses selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubTwoHopLinks selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .slotLinear selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderPathBounds selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowFreeGeometry selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .inducedPathAttachment selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .densityExcess selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderSlack selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubWindowBudget selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowHubBounds selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cubicNeighbourSupply selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubCountBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .lowEdgeParity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .bigHubBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .bigHubVShapes selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highSurplusBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubLengthThreePairs selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .surplusDartIdentity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highDegreeCountBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .admissibleQuotientsLabelInjective selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .surplusAtOrBelow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sparseSurplusSurvivor selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .barrierEnumeration selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageSeparated selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .skeletonDominates selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hotColdPartition selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .barrierCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8AtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldHotEntropyCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMass selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldAmbientCubic selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldStubExcess selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldAmbientCubicStubExcess selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldSelectedBranchExcess selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMassBounded selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .densityCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderNormalized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .boundaryDemand selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .stubSupply selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .wedgeSupply selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .curvatureTargetRank selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .exactResponseProfile selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .targetRankCircuit selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .curvatureFullRank selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .forcedCurvatureCost selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .largeBudgetResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .netDeficiencyCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8RateFails selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8RateFailsJoin selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8RateFailsPiece selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8RateFailsCrossBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8RateFailsFlow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8CarrierInjection selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8RateExactSlack selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8BasinBurden selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8StubDeficit selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8DeficitVsStubs selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8EntryLowerBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8CoreEmpty selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8StrongRate selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8ThinIsolation selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8WindowStub selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8ThinSmall selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8WindowRPathGap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8HubStubs selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8WindowSelfRPathGap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8PieceBoundary selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8WindowPieceRank selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8AchievableLengths selected.object

/-- The return of `Route8RateFailsOutcome`: one `get` per fact of
its maximal ledger. -/
theorem route8RateFailsReturn
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
    [FactKeys.Has (K .packingOrderBound) known]
    [FactKeys.Has (K .noSuppressionChordViolation) known]
    [FactKeys.Has (K .twoSwitchForcedPath) known]
    [FactKeys.Has (K .crossSwitchFamily) known]
    [FactKeys.Has (K .highCentreSplitForced) known]
    [FactKeys.Has (K .sameVertexSwitchForcedPath) known]
    [FactKeys.Has (K .declaredPairSupportStructure) known]
    [FactKeys.Has (K .bridgeless) known]
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
    [FactKeys.Has (K .coldRoute8AtOrAbove) known]
    [FactKeys.Has (K .coldHotEntropyCap) known]
    [FactKeys.Has (K .coldMass) known]
    [FactKeys.Has (K .coldAmbientCubic) known]
    [FactKeys.Has (K .coldStubExcess) known]
    [FactKeys.Has (K .coldAmbientCubicStubExcess) known]
    [FactKeys.Has (K .coldSelectedBranchExcess) known]
    [FactKeys.Has (K .coldMassBounded) known]
    [FactKeys.Has (K .densityCap) known]
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
    [FactKeys.Has (K .route8RateFails) known]
    [FactKeys.Has (K .route8RateFailsJoin) known]
    [FactKeys.Has (K .route8RateFailsPiece) known]
    [FactKeys.Has (K .route8RateFailsCrossBound) known]
    [FactKeys.Has (K .route8RateFailsFlow) known]
    [FactKeys.Has (K .route8CarrierInjection) known]
    [FactKeys.Has (K .route8RateExactSlack) known]
    [FactKeys.Has (K .route8BasinBurden) known]
    [FactKeys.Has (K .route8StubDeficit) known]
    [FactKeys.Has (K .route8DeficitVsStubs) known]
    [FactKeys.Has (K .route8EntryLowerBound) known]
    [FactKeys.Has (K .route8CoreEmpty) known]
    [FactKeys.Has (K .route8StrongRate) known]
    [FactKeys.Has (K .route8ThinIsolation) known]
    [FactKeys.Has (K .route8WindowStub) known]
    [FactKeys.Has (K .route8ThinSmall) known]
    [FactKeys.Has (K .route8WindowRPathGap) known]
    [FactKeys.Has (K .route8HubStubs) known]
    [FactKeys.Has (K .route8WindowSelfRPathGap) known]
    [FactKeys.Has (K .route8PieceBoundary) known]
    [FactKeys.Has (K .route8WindowPieceRank) known]
    [FactKeys.Has (K .route8AchievableLengths) known] :
    Route8RateFailsOutcome selected :=
  ⟨(history.get (K .selection)).down,
    (history.get (K .cubicBaseline)).down,
    (history.get (K .minDegreeBaseline)).down,
    (history.get (K .returnAvoidance)).down,
    (history.get (K .noProperBaseline)).down,
    (history.get (K .slackIndependent)).down,
    (history.get (K .tightEndpoint)).down,
    (history.get (K .cycleRankConstraint)).down,
    (history.get (K .degreeProfileFibres)).down,
    (history.get (K .targetCompleteContextUniversality)).down,
    (history.get (K .replacementExclusion)).down,
    (history.get (K .uncompressible)).down,
    (history.get (K .windowPresent)).down,
    (history.get (K .maximalPacking)).down,
    (history.get (K .localAlgebra)).down,
    (history.get (K .packingOrderBound)).down,
    (history.get (K .noSuppressionChordViolation)).down,
    (history.get (K .twoSwitchForcedPath)).down,
    (history.get (K .crossSwitchFamily)).down,
    (history.get (K .highCentreSplitForced)).down,
    (history.get (K .sameVertexSwitchForcedPath)).down,
    (history.get (K .declaredPairSupportStructure)).down,
    (history.get (K .bridgeless)).down,
    (history.get (K .remainderDeficiencyBelowCut)).down,
    (history.get (K .windowCutCapacity)).down,
    (history.get (K .primitiveCarrierCount)).down,
    (history.get (K .singleBoundaryShape)).down,
    (history.get (K .neighbourhoodPairCount)).down,
    (history.get (K .starCycleConstraint)).down,
    (history.get (K .meetingCycleConstraint)).down,
    (history.get (K .highDegreePairSum)).down,
    (history.get (K .vertexDeletionComponents)).down,
    (history.get (K .cyclesThroughVertex)).down,
    (history.get (K .cutVertexBlockPaths)).down,
    (history.get (K .cycleDoubleCount)).down,
    (history.get (K .threeRouteFan)).down,
    (history.get (K .threeRouteChain)).down,
    (history.get (K .windowPositionStubs)).down,
    (history.get (K .windowAttachmentGap)).down,
    (history.get (K .portEndDegree)).down,
    (history.get (K .hubLinkStructure)).down,
    (history.get (K .hubClassCounts)).down,
    (history.get (K .slotRelation)).down,
    (history.get (K .closedClasses)).down,
    (history.get (K .hubTwoHopLinks)).down,
    (history.get (K .slotLinear)).down,
    (history.get (K .remainderPathBounds)).down,
    (history.get (K .windowFreeGeometry)).down,
    (history.get (K .inducedPathAttachment)).down,
    (history.get (K .densityExcess)).down,
    (history.get (K .remainderSlack)).down,
    (history.get (K .hubWindowBudget)).down,
    (history.get (K .windowHubBounds)).down,
    (history.get (K .cubicNeighbourSupply)).down,
    (history.get (K .hubCountBound)).down,
    (history.get (K .lowEdgeParity)).down,
    (history.get (K .bigHubBound)).down,
    (history.get (K .bigHubVShapes)).down,
    (history.get (K .highSurplusBound)).down,
    (history.get (K .hubLengthThreePairs)).down,
    (history.get (K .surplusDartIdentity)).down,
    (history.get (K .highDegreeCountBound)).down,
    (history.get (K .admissibleQuotientsLabelInjective)).down,
    (history.get (K .surplusAtOrBelow)).down,
    (history.get (K .sparseSurplusSurvivor)).down,
    (history.get (K .barrierEnumeration)).down,
    (history.get (K .windowPackageSeparated)).down,
    (history.get (K .skeletonDominates)).down,
    (history.get (K .hotColdPartition)).down,
    (history.get (K .barrierCap)).down,
    (history.get (K .coldRoute8AtOrAbove)).down,
    (history.get (K .coldHotEntropyCap)).down,
    (history.get (K .coldMass)).down,
    (history.get (K .coldAmbientCubic)).down,
    (history.get (K .coldStubExcess)).down,
    (history.get (K .coldAmbientCubicStubExcess)).down,
    (history.get (K .coldSelectedBranchExcess)).down,
    (history.get (K .coldMassBounded)).down,
    (history.get (K .densityCap)).down,
    (history.get (K .remainderNormalized)).down,
    (history.get (K .boundaryDemand)).down,
    (history.get (K .stubSupply)).down,
    (history.get (K .wedgeSupply)).down,
    (history.get (K .curvatureTargetRank)).down,
    (history.get (K .exactResponseProfile)).down,
    (history.get (K .targetRankCircuit)).down,
    (history.get (K .curvatureFullRank)).down,
    (history.get (K .forcedCurvatureCost)).down,
    (history.get (K .largeBudgetResidual)).down,
    (history.get (K .netDeficiencyCap)).down,
    (history.get (K .route8RateFails)).down,
    (history.get (K .route8RateFailsJoin)).down,
    (history.get (K .route8RateFailsPiece)).down,
    (history.get (K .route8RateFailsCrossBound)).down,
    (history.get (K .route8RateFailsFlow)).down,
    (history.get (K .route8CarrierInjection)).down,
    (history.get (K .route8RateExactSlack)).down,
    (history.get (K .route8BasinBurden)).down,
    (history.get (K .route8StubDeficit)).down,
    (history.get (K .route8DeficitVsStubs)).down,
    (history.get (K .route8EntryLowerBound)).down,
    (history.get (K .route8CoreEmpty)).down,
    (history.get (K .route8StrongRate)).down,
    (history.get (K .route8ThinIsolation)).down,
    (history.get (K .route8WindowStub)).down,
    (history.get (K .route8ThinSmall)).down,
    (history.get (K .route8WindowRPathGap)).down,
    (history.get (K .route8HubStubs)).down,
    (history.get (K .route8WindowSelfRPathGap)).down,
    (history.get (K .route8PieceBoundary)).down,
    (history.get (K .route8WindowPieceRank)).down,
    (history.get (K .route8AchievableLengths)).down⟩

/-- **Node `[187] (local cold-terminal exclusion)`** (thm:main (vi), tex
386-403): the local cold-terminal exclusion of thm:cold-branch-quantitative-
closure without a global terminal contradiction.  The explicit conjunction
of every fact on its maximal ledger (104 common facts). -/
abbrev ColdBranchClosedOutcome (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .selection selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cubicBaseline selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .minDegreeBaseline selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .returnAvoidance selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .noProperBaseline selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .slackIndependent selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .tightEndpoint selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cycleRankConstraint selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .degreeProfileFibres selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .targetCompleteContextUniversality selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .replacementExclusion selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .uncompressible selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPresent selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .maximalPacking selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .localAlgebra selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .packingOrderBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .noSuppressionChordViolation selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .twoSwitchForcedPath selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .crossSwitchFamily selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highCentreSplitForced selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sameVertexSwitchForcedPath selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .declaredPairSupportStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderDeficiencyBelowCut selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowCutCapacity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .primitiveCarrierCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .singleBoundaryShape selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .neighbourhoodPairCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .starCycleConstraint selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .meetingCycleConstraint selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highDegreePairSum selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .vertexDeletionComponents selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cyclesThroughVertex selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cutVertexBlockPaths selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cycleDoubleCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .threeRouteFan selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .threeRouteChain selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPositionStubs selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowAttachmentGap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .portEndDegree selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubLinkStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubClassCounts selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .slotRelation selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .closedClasses selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubTwoHopLinks selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .slotLinear selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderPathBounds selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowFreeGeometry selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .inducedPathAttachment selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .densityExcess selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderSlack selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubWindowBudget selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowHubBounds selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cubicNeighbourSupply selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubCountBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .lowEdgeParity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .bigHubBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .bigHubVShapes selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highSurplusBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubLengthThreePairs selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .surplusDartIdentity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highDegreeCountBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .admissibleQuotientsLabelInjective selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .surplusAtOrBelow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sparseSurplusSurvivor selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .barrierEnumeration selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageSeparated selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .skeletonDominates selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hotColdPartition selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .barrierCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldHotEntropyCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMass selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldAmbientCubic selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldStubExcess selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldAmbientCubicStubExcess selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldSelectedBranchExcess selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderNormalized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .boundaryDemand selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .stubSupply selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .wedgeSupply selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .curvatureTargetRank selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .exactResponseProfile selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .targetRankCircuit selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .curvatureFullRank selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .forcedCurvatureCost selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .bridgeless selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .netChargeLocalization selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldReturnCorridors selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldCorridorState selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldFirstFailureOccurrence selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldFailureCycle selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldFailureDefectRoute selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldFailureCompression selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldHandoffTransfer selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldFailureRouting selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldExchangeBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermCandidates selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .absorbedGermSplit selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermRouted selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermSilent selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermDistinguished selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermRealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldSameInterfaceTable selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldBranchClosed selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .absorbedGermFanData selected.object

/-- The return of `ColdBranchClosedOutcome`: one `get` per fact of
its maximal ledger. -/
theorem coldBranchClosedReturn
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
    [FactKeys.Has (K .packingOrderBound) known]
    [FactKeys.Has (K .noSuppressionChordViolation) known]
    [FactKeys.Has (K .twoSwitchForcedPath) known]
    [FactKeys.Has (K .crossSwitchFamily) known]
    [FactKeys.Has (K .highCentreSplitForced) known]
    [FactKeys.Has (K .sameVertexSwitchForcedPath) known]
    [FactKeys.Has (K .declaredPairSupportStructure) known]
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
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .netChargeLocalization) known]
    [FactKeys.Has (K .coldReturnCorridors) known]
    [FactKeys.Has (K .coldCorridorState) known]
    [FactKeys.Has (K .coldFirstFailureOccurrence) known]
    [FactKeys.Has (K .coldFailureCycle) known]
    [FactKeys.Has (K .coldFailureDefectRoute) known]
    [FactKeys.Has (K .coldFailureCompression) known]
    [FactKeys.Has (K .coldHandoffTransfer) known]
    [FactKeys.Has (K .coldFailureRouting) known]
    [FactKeys.Has (K .coldExchangeBound) known]
    [FactKeys.Has (K .coldGermCandidates) known]
    [FactKeys.Has (K .absorbedGermSplit) known]
    [FactKeys.Has (K .coldGermRouted) known]
    [FactKeys.Has (K .coldGermSilent) known]
    [FactKeys.Has (K .coldGermDistinguished) known]
    [FactKeys.Has (K .coldGermRealized) known]
    [FactKeys.Has (K .coldSameInterfaceTable) known]
    [FactKeys.Has (K .coldBranchClosed) known]
    [FactKeys.Has (K .absorbedGermFanData) known] :
    ColdBranchClosedOutcome selected :=
  ⟨(history.get (K .selection)).down,
    (history.get (K .cubicBaseline)).down,
    (history.get (K .minDegreeBaseline)).down,
    (history.get (K .returnAvoidance)).down,
    (history.get (K .noProperBaseline)).down,
    (history.get (K .slackIndependent)).down,
    (history.get (K .tightEndpoint)).down,
    (history.get (K .cycleRankConstraint)).down,
    (history.get (K .degreeProfileFibres)).down,
    (history.get (K .targetCompleteContextUniversality)).down,
    (history.get (K .replacementExclusion)).down,
    (history.get (K .uncompressible)).down,
    (history.get (K .windowPresent)).down,
    (history.get (K .maximalPacking)).down,
    (history.get (K .localAlgebra)).down,
    (history.get (K .packingOrderBound)).down,
    (history.get (K .noSuppressionChordViolation)).down,
    (history.get (K .twoSwitchForcedPath)).down,
    (history.get (K .crossSwitchFamily)).down,
    (history.get (K .highCentreSplitForced)).down,
    (history.get (K .sameVertexSwitchForcedPath)).down,
    (history.get (K .declaredPairSupportStructure)).down,
    (history.get (K .remainderDeficiencyBelowCut)).down,
    (history.get (K .windowCutCapacity)).down,
    (history.get (K .primitiveCarrierCount)).down,
    (history.get (K .singleBoundaryShape)).down,
    (history.get (K .neighbourhoodPairCount)).down,
    (history.get (K .starCycleConstraint)).down,
    (history.get (K .meetingCycleConstraint)).down,
    (history.get (K .highDegreePairSum)).down,
    (history.get (K .vertexDeletionComponents)).down,
    (history.get (K .cyclesThroughVertex)).down,
    (history.get (K .cutVertexBlockPaths)).down,
    (history.get (K .cycleDoubleCount)).down,
    (history.get (K .threeRouteFan)).down,
    (history.get (K .threeRouteChain)).down,
    (history.get (K .windowPositionStubs)).down,
    (history.get (K .windowAttachmentGap)).down,
    (history.get (K .portEndDegree)).down,
    (history.get (K .hubLinkStructure)).down,
    (history.get (K .hubClassCounts)).down,
    (history.get (K .slotRelation)).down,
    (history.get (K .closedClasses)).down,
    (history.get (K .hubTwoHopLinks)).down,
    (history.get (K .slotLinear)).down,
    (history.get (K .remainderPathBounds)).down,
    (history.get (K .windowFreeGeometry)).down,
    (history.get (K .inducedPathAttachment)).down,
    (history.get (K .densityExcess)).down,
    (history.get (K .remainderSlack)).down,
    (history.get (K .hubWindowBudget)).down,
    (history.get (K .windowHubBounds)).down,
    (history.get (K .cubicNeighbourSupply)).down,
    (history.get (K .hubCountBound)).down,
    (history.get (K .lowEdgeParity)).down,
    (history.get (K .bigHubBound)).down,
    (history.get (K .bigHubVShapes)).down,
    (history.get (K .highSurplusBound)).down,
    (history.get (K .hubLengthThreePairs)).down,
    (history.get (K .surplusDartIdentity)).down,
    (history.get (K .highDegreeCountBound)).down,
    (history.get (K .admissibleQuotientsLabelInjective)).down,
    (history.get (K .surplusAtOrBelow)).down,
    (history.get (K .sparseSurplusSurvivor)).down,
    (history.get (K .barrierEnumeration)).down,
    (history.get (K .windowPackageSeparated)).down,
    (history.get (K .skeletonDominates)).down,
    (history.get (K .hotColdPartition)).down,
    (history.get (K .barrierCap)).down,
    (history.get (K .coldHotEntropyCap)).down,
    (history.get (K .coldMass)).down,
    (history.get (K .coldAmbientCubic)).down,
    (history.get (K .coldStubExcess)).down,
    (history.get (K .coldAmbientCubicStubExcess)).down,
    (history.get (K .coldSelectedBranchExcess)).down,
    (history.get (K .remainderNormalized)).down,
    (history.get (K .boundaryDemand)).down,
    (history.get (K .stubSupply)).down,
    (history.get (K .wedgeSupply)).down,
    (history.get (K .curvatureTargetRank)).down,
    (history.get (K .exactResponseProfile)).down,
    (history.get (K .targetRankCircuit)).down,
    (history.get (K .curvatureFullRank)).down,
    (history.get (K .forcedCurvatureCost)).down,
    (history.get (K .bridgeless)).down,
    (history.get (K .netChargeLocalization)).down,
    (history.get (K .coldReturnCorridors)).down,
    (history.get (K .coldCorridorState)).down,
    (history.get (K .coldFirstFailureOccurrence)).down,
    (history.get (K .coldFailureCycle)).down,
    (history.get (K .coldFailureDefectRoute)).down,
    (history.get (K .coldFailureCompression)).down,
    (history.get (K .coldHandoffTransfer)).down,
    (history.get (K .coldFailureRouting)).down,
    (history.get (K .coldExchangeBound)).down,
    (history.get (K .coldGermCandidates)).down,
    (history.get (K .absorbedGermSplit)).down,
    (history.get (K .coldGermRouted)).down,
    (history.get (K .coldGermSilent)).down,
    (history.get (K .coldGermDistinguished)).down,
    (history.get (K .coldGermRealized)).down,
    (history.get (K .coldSameInterfaceTable)).down,
    (history.get (K .coldBranchClosed)).down,
    (history.get (K .absorbedGermFanData)).down⟩

/-- **Node `[54]`** (thm:main (vii), tex 404-443; prop:entropy-high-theta, tex 10368): the configuration at G
where the joint realization inequality RS(R0)*2^(rate*s*p13)*2^F <= B fails.
The explicit conjunction of every fact on its maximal ledger (92 common
facts). -/
abbrev Node54ResidualOutcome (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .selection selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cubicBaseline selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .minDegreeBaseline selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .returnAvoidance selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .noProperBaseline selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .slackIndependent selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .tightEndpoint selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cycleRankConstraint selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .degreeProfileFibres selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .targetCompleteContextUniversality selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .replacementExclusion selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .uncompressible selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPresent selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .maximalPacking selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .localAlgebra selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .packingOrderBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .noSuppressionChordViolation selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .twoSwitchForcedPath selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .crossSwitchFamily selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highCentreSplitForced selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sameVertexSwitchForcedPath selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .declaredPairSupportStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .bridgeless selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderDeficiencyBelowCut selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowCutCapacity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .primitiveCarrierCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .singleBoundaryShape selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .neighbourhoodPairCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .starCycleConstraint selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .meetingCycleConstraint selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highDegreePairSum selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .vertexDeletionComponents selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cyclesThroughVertex selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cutVertexBlockPaths selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cycleDoubleCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .threeRouteFan selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .threeRouteChain selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPositionStubs selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowAttachmentGap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .portEndDegree selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubLinkStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubClassCounts selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .slotRelation selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .closedClasses selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubTwoHopLinks selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .slotLinear selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderPathBounds selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowFreeGeometry selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .inducedPathAttachment selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .densityExcess selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderSlack selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubWindowBudget selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowHubBounds selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cubicNeighbourSupply selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubCountBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .lowEdgeParity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .bigHubBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .bigHubVShapes selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highSurplusBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hubLengthThreePairs selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .surplusDartIdentity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highDegreeCountBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .admissibleQuotientsLabelInjective selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .surplusAtOrBelow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sparseSurplusSurvivor selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .barrierEnumeration selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageSeparated selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .skeletonDominates selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .hotColdPartition selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .barrierCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldHotEntropyCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMass selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldAmbientCubic selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldStubExcess selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldAmbientCubicStubExcess selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldSelectedBranchExcess selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderNormalized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .boundaryDemand selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .stubSupply selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .wedgeSupply selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .curvatureTargetRank selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .exactResponseProfile selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .targetRankCircuit selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .curvatureFullRank selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .forcedCurvatureCost selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderEntropyHigh selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .entropyPackageDemand selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .entropyCapActive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .allColdEntropyResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .stubDeficitIdentity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderCycleSpectrum selected.object

/-- The return of `Node54ResidualOutcome`: one `get` per fact of
its maximal ledger. -/
theorem node54Return
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
    [FactKeys.Has (K .packingOrderBound) known]
    [FactKeys.Has (K .noSuppressionChordViolation) known]
    [FactKeys.Has (K .twoSwitchForcedPath) known]
    [FactKeys.Has (K .crossSwitchFamily) known]
    [FactKeys.Has (K .highCentreSplitForced) known]
    [FactKeys.Has (K .sameVertexSwitchForcedPath) known]
    [FactKeys.Has (K .declaredPairSupportStructure) known]
    [FactKeys.Has (K .bridgeless) known]
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
    [FactKeys.Has (K .remainderEntropyHigh) known]
    [FactKeys.Has (K .entropyPackageDemand) known]
    [FactKeys.Has (K .entropyCapActive) known]
    [FactKeys.Has (K .allColdEntropyResidual) known]
    [FactKeys.Has (K .stubDeficitIdentity) known]
    [FactKeys.Has (K .remainderCycleSpectrum) known] :
    Node54ResidualOutcome selected :=
  ⟨(history.get (K .selection)).down,
    (history.get (K .cubicBaseline)).down,
    (history.get (K .minDegreeBaseline)).down,
    (history.get (K .returnAvoidance)).down,
    (history.get (K .noProperBaseline)).down,
    (history.get (K .slackIndependent)).down,
    (history.get (K .tightEndpoint)).down,
    (history.get (K .cycleRankConstraint)).down,
    (history.get (K .degreeProfileFibres)).down,
    (history.get (K .targetCompleteContextUniversality)).down,
    (history.get (K .replacementExclusion)).down,
    (history.get (K .uncompressible)).down,
    (history.get (K .windowPresent)).down,
    (history.get (K .maximalPacking)).down,
    (history.get (K .localAlgebra)).down,
    (history.get (K .packingOrderBound)).down,
    (history.get (K .noSuppressionChordViolation)).down,
    (history.get (K .twoSwitchForcedPath)).down,
    (history.get (K .crossSwitchFamily)).down,
    (history.get (K .highCentreSplitForced)).down,
    (history.get (K .sameVertexSwitchForcedPath)).down,
    (history.get (K .declaredPairSupportStructure)).down,
    (history.get (K .bridgeless)).down,
    (history.get (K .remainderDeficiencyBelowCut)).down,
    (history.get (K .windowCutCapacity)).down,
    (history.get (K .primitiveCarrierCount)).down,
    (history.get (K .singleBoundaryShape)).down,
    (history.get (K .neighbourhoodPairCount)).down,
    (history.get (K .starCycleConstraint)).down,
    (history.get (K .meetingCycleConstraint)).down,
    (history.get (K .highDegreePairSum)).down,
    (history.get (K .vertexDeletionComponents)).down,
    (history.get (K .cyclesThroughVertex)).down,
    (history.get (K .cutVertexBlockPaths)).down,
    (history.get (K .cycleDoubleCount)).down,
    (history.get (K .threeRouteFan)).down,
    (history.get (K .threeRouteChain)).down,
    (history.get (K .windowPositionStubs)).down,
    (history.get (K .windowAttachmentGap)).down,
    (history.get (K .portEndDegree)).down,
    (history.get (K .hubLinkStructure)).down,
    (history.get (K .hubClassCounts)).down,
    (history.get (K .slotRelation)).down,
    (history.get (K .closedClasses)).down,
    (history.get (K .hubTwoHopLinks)).down,
    (history.get (K .slotLinear)).down,
    (history.get (K .remainderPathBounds)).down,
    (history.get (K .windowFreeGeometry)).down,
    (history.get (K .inducedPathAttachment)).down,
    (history.get (K .densityExcess)).down,
    (history.get (K .remainderSlack)).down,
    (history.get (K .hubWindowBudget)).down,
    (history.get (K .windowHubBounds)).down,
    (history.get (K .cubicNeighbourSupply)).down,
    (history.get (K .hubCountBound)).down,
    (history.get (K .lowEdgeParity)).down,
    (history.get (K .bigHubBound)).down,
    (history.get (K .bigHubVShapes)).down,
    (history.get (K .highSurplusBound)).down,
    (history.get (K .hubLengthThreePairs)).down,
    (history.get (K .surplusDartIdentity)).down,
    (history.get (K .highDegreeCountBound)).down,
    (history.get (K .admissibleQuotientsLabelInjective)).down,
    (history.get (K .surplusAtOrBelow)).down,
    (history.get (K .sparseSurplusSurvivor)).down,
    (history.get (K .barrierEnumeration)).down,
    (history.get (K .windowPackageSeparated)).down,
    (history.get (K .skeletonDominates)).down,
    (history.get (K .hotColdPartition)).down,
    (history.get (K .barrierCap)).down,
    (history.get (K .coldHotEntropyCap)).down,
    (history.get (K .coldMass)).down,
    (history.get (K .coldAmbientCubic)).down,
    (history.get (K .coldStubExcess)).down,
    (history.get (K .coldAmbientCubicStubExcess)).down,
    (history.get (K .coldSelectedBranchExcess)).down,
    (history.get (K .remainderNormalized)).down,
    (history.get (K .boundaryDemand)).down,
    (history.get (K .stubSupply)).down,
    (history.get (K .wedgeSupply)).down,
    (history.get (K .curvatureTargetRank)).down,
    (history.get (K .exactResponseProfile)).down,
    (history.get (K .targetRankCircuit)).down,
    (history.get (K .curvatureFullRank)).down,
    (history.get (K .forcedCurvatureCost)).down,
    (history.get (K .remainderEntropyHigh)).down,
    (history.get (K .entropyPackageDemand)).down,
    (history.get (K .entropyCapActive)).down,
    (history.get (K .allColdEntropyResidual)).down,
    (history.get (K .stubDeficitIdentity)).down,
    (history.get (K .remainderCycleSpectrum)).down⟩

end HypostructureErdos64EG
