import HypostructureErdos64EG.Assembly.Residuals

/-!
# Assembly: Residuals / PairTypeBOutcome

Node `[187]` ([179]/[180] Type B entry), split by distinct fact set.  The
generic residual `PairTypeBOutcome` (`Assembly/Residuals.lean`) lists the 37
facts common to every path, then its own `[179]`/`[180]` arm as a disjunction.
It is reached along four paths with four distinct literal ledgers: the entry
into the pair-code chain `[178]` is either the free side of `[131]` (node
`[130]`'s independent arm) or the free side of `[137]` (node `[130]`'s
dependent arm), and the chain returns on the `[179]` early arm (`system`) or
on the `[180]` early arm (`increment`).  Each distinct fact set is its own open
node, a subtype of the generic residual: the generic residual, then every
extra key of its ledger as an explicit `Holds` conjunct (the entry keys, then
the arm keys).  Each return theorem reads each key of its ledger with exactly
one `ExactLedger.get`.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u

/-- **Node `[187]` ([179]/[180] Type B entry), `independentSystem`** (thm:main
(vi), tex 369-378): the generic residual `PairTypeBOutcome` on the ledger
reached by [130] independent arm (canonical pair split), [131] free-pair count
fails; then [179] early outcome.  Every fact of its ledger: the 84 common facts
and 3 explicit extra facts (87 facts). -/
abbrev PairTypeBOutcome_independentSystem (selected : EGInput.{u}) : Prop :=
  PairTypeBOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .independentPairFamily selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .freePairCodeUnrealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairSystemEarlyOutcome selected.object

theorem PairTypeBOutcome_independentSystem.toGeneric {selected : EGInput.{u}}
    (h : PairTypeBOutcome_independentSystem selected) : PairTypeBOutcome selected :=
  h.1

/-- The return of `PairTypeBOutcome_independentSystem`: one `get` per fact of
its ledger. -/
theorem pairTypeBIndependentSystemReturn
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
    [FactKeys.Has (K .independentPairFamily) known]
    [FactKeys.Has (K .freePairCountFails) known]
    [FactKeys.Has (K .freePairCodeUnrealized) known]
    [FactKeys.Has (K .pairSystemEarlyOutcome) known] :
    PairTypeBOutcome_independentSystem selected :=
  have pairSystemEarlyOutcome := (history.get (K .pairSystemEarlyOutcome)).down
  ⟨⟨(history.get (K .selection)).down,
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
      (history.get (K .everyWitnessSpectrumSplit)).down,
      (history.get (K .packingOrderBound)).down,
      (history.get (K .noSuppressionChordViolation)).down,
      (history.get (K .twoSwitchForcedPath)).down,
      (history.get (K .crossSwitchFamily)).down,
      (history.get (K .highCentreSplitForced)).down,
      (history.get (K .sameVertexSwitchForcedPath)).down,
      (history.get (K .specWitnessStructure)).down,
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
      (history.get (K .pairConditionalFactorization)).down,
      (history.get (K .pairFailureOverlap)).down,
      (history.get (K .pairDemandReturns)).down,
      (history.get (K .pairSystemRealizability)).down,
      (history.get (K .typeBFanEntry)).down,
      Or.inl pairSystemEarlyOutcome⟩,
    (history.get (K .independentPairFamily)).down,
    (history.get (K .freePairCodeUnrealized)).down,
    pairSystemEarlyOutcome⟩

/-- **Node `[187]` ([179]/[180] Type B entry), `independentIncrement`**
(thm:main (vi), tex 369-378): the generic residual `PairTypeBOutcome` on the
ledger reached by [130] independent arm (canonical pair split), [131] free-pair
count fails; then [179] serial arm, [180] covered increment, [180] early
outcome.  Every fact of its ledger: the 84 common facts and 6 explicit extra
facts (90 facts). -/
abbrev PairTypeBOutcome_independentIncrement (selected : EGInput.{u}) : Prop :=
  PairTypeBOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .independentPairFamily selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .freePairCodeUnrealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairSystemNoEarlyOutcome selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairSerialDemandSystem selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairIncrementCovered selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairIncrementEarlyOutcome selected.object

theorem PairTypeBOutcome_independentIncrement.toGeneric {selected : EGInput.{u}}
    (h : PairTypeBOutcome_independentIncrement selected) : PairTypeBOutcome selected :=
  h.1

/-- The return of `PairTypeBOutcome_independentIncrement`: one `get` per fact of
its ledger. -/
theorem pairTypeBIndependentIncrementReturn
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
    [FactKeys.Has (K .independentPairFamily) known]
    [FactKeys.Has (K .freePairCountFails) known]
    [FactKeys.Has (K .freePairCodeUnrealized) known]
    [FactKeys.Has (K .pairSystemNoEarlyOutcome) known]
    [FactKeys.Has (K .pairSerialDemandSystem) known]
    [FactKeys.Has (K .pairIncrementCovered) known]
    [FactKeys.Has (K .pairIncrementEarlyOutcome) known] :
    PairTypeBOutcome_independentIncrement selected :=
  have pairSystemNoEarlyOutcome := (history.get (K .pairSystemNoEarlyOutcome)).down
  have pairSerialDemandSystem := (history.get (K .pairSerialDemandSystem)).down
  have pairIncrementCovered := (history.get (K .pairIncrementCovered)).down
  have pairIncrementEarlyOutcome := (history.get (K .pairIncrementEarlyOutcome)).down
  ⟨⟨(history.get (K .selection)).down,
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
      (history.get (K .everyWitnessSpectrumSplit)).down,
      (history.get (K .packingOrderBound)).down,
      (history.get (K .noSuppressionChordViolation)).down,
      (history.get (K .twoSwitchForcedPath)).down,
      (history.get (K .crossSwitchFamily)).down,
      (history.get (K .highCentreSplitForced)).down,
      (history.get (K .sameVertexSwitchForcedPath)).down,
      (history.get (K .specWitnessStructure)).down,
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
      (history.get (K .pairConditionalFactorization)).down,
      (history.get (K .pairFailureOverlap)).down,
      (history.get (K .pairDemandReturns)).down,
      (history.get (K .pairSystemRealizability)).down,
      (history.get (K .typeBFanEntry)).down,
      Or.inr ⟨pairSystemNoEarlyOutcome, pairSerialDemandSystem,
        pairIncrementCovered, pairIncrementEarlyOutcome⟩⟩,
    (history.get (K .independentPairFamily)).down,
    (history.get (K .freePairCodeUnrealized)).down,
    pairSystemNoEarlyOutcome,
    pairSerialDemandSystem,
    pairIncrementCovered,
    pairIncrementEarlyOutcome⟩

/-- **Node `[187]` ([179]/[180] Type B entry), `dependentSystem`** (thm:main
(vi), tex 369-378): the generic residual `PairTypeBOutcome` on the ledger
reached by [130] dependent arm (canonical pair split: fibres, no blocker (d), no
blocker (e)), [132] blocker arm, [137] blocked-side count fails; then [179]
early outcome.  Every fact of its ledger: the 84 common facts and 12 explicit
extra facts (96 facts). -/
abbrev PairTypeBOutcome_dependentSystem (selected : EGInput.{u}) : Prop :=
  PairTypeBOutcome selected ∧
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
      erdosReceiverLoadProfile spineData .capacityTokenLedger selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .blockedPairEntropySetup selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .blockedPairCountFails selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .blockedPairCodeUnrealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairSystemEarlyOutcome selected.object

theorem PairTypeBOutcome_dependentSystem.toGeneric {selected : EGInput.{u}}
    (h : PairTypeBOutcome_dependentSystem selected) : PairTypeBOutcome selected :=
  h.1

/-- The return of `PairTypeBOutcome_dependentSystem`: one `get` per fact of its
ledger. -/
theorem pairTypeBDependentSystemReturn
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
    [FactKeys.Has (K .pairConditionalFactorization) known]
    [FactKeys.Has (K .pairFailureOverlap) known]
    [FactKeys.Has (K .pairDemandReturns) known]
    [FactKeys.Has (K .pairSystemRealizability) known]
    [FactKeys.Has (K .typeBFanEntry) known]
    [FactKeys.Has (K .dependentPairFamily) known]
    [FactKeys.Has (K .pairDegreeProfileFibres) known]
    [FactKeys.Has (K .pairNoProfileObstruction) known]
    [FactKeys.Has (K .pairNoResponseObstruction) known]
    [FactKeys.Has (K .blockedPairNoExit) known]
    [FactKeys.Has (K .canonicalBlockerRoute) known]
    [FactKeys.Has (K .canonicalPairLedger) known]
    [FactKeys.Has (K .capacityTokenLedger) known]
    [FactKeys.Has (K .blockedPairEntropySetup) known]
    [FactKeys.Has (K .blockedPairCountFails) known]
    [FactKeys.Has (K .blockedPairCodeUnrealized) known]
    [FactKeys.Has (K .pairSystemEarlyOutcome) known] :
    PairTypeBOutcome_dependentSystem selected :=
  have pairSystemEarlyOutcome := (history.get (K .pairSystemEarlyOutcome)).down
  ⟨⟨(history.get (K .selection)).down,
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
      (history.get (K .everyWitnessSpectrumSplit)).down,
      (history.get (K .packingOrderBound)).down,
      (history.get (K .noSuppressionChordViolation)).down,
      (history.get (K .twoSwitchForcedPath)).down,
      (history.get (K .crossSwitchFamily)).down,
      (history.get (K .highCentreSplitForced)).down,
      (history.get (K .sameVertexSwitchForcedPath)).down,
      (history.get (K .specWitnessStructure)).down,
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
      (history.get (K .pairConditionalFactorization)).down,
      (history.get (K .pairFailureOverlap)).down,
      (history.get (K .pairDemandReturns)).down,
      (history.get (K .pairSystemRealizability)).down,
      (history.get (K .typeBFanEntry)).down,
      Or.inl pairSystemEarlyOutcome⟩,
    (history.get (K .dependentPairFamily)).down,
    (history.get (K .pairDegreeProfileFibres)).down,
    (history.get (K .pairNoProfileObstruction)).down,
    (history.get (K .pairNoResponseObstruction)).down,
    (history.get (K .blockedPairNoExit)).down,
    (history.get (K .canonicalBlockerRoute)).down,
    (history.get (K .canonicalPairLedger)).down,
    (history.get (K .capacityTokenLedger)).down,
    (history.get (K .blockedPairEntropySetup)).down,
    (history.get (K .blockedPairCountFails)).down,
    (history.get (K .blockedPairCodeUnrealized)).down,
    pairSystemEarlyOutcome⟩

/-- **Node `[187]` ([179]/[180] Type B entry), `dependentIncrement`** (thm:main
(vi), tex 369-378): the generic residual `PairTypeBOutcome` on the ledger
reached by [130] dependent arm (canonical pair split: fibres, no blocker (d), no
blocker (e)), [132] blocker arm, [137] blocked-side count fails; then [179]
serial arm, [180] covered increment, [180] early outcome.  Every fact of its
ledger: the 84 common facts and 15 explicit extra facts (99 facts). -/
abbrev PairTypeBOutcome_dependentIncrement (selected : EGInput.{u}) : Prop :=
  PairTypeBOutcome selected ∧
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
      erdosReceiverLoadProfile spineData .capacityTokenLedger selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .blockedPairEntropySetup selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .blockedPairCountFails selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .blockedPairCodeUnrealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairSystemNoEarlyOutcome selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairSerialDemandSystem selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairIncrementCovered selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairIncrementEarlyOutcome selected.object

theorem PairTypeBOutcome_dependentIncrement.toGeneric {selected : EGInput.{u}}
    (h : PairTypeBOutcome_dependentIncrement selected) : PairTypeBOutcome selected :=
  h.1

/-- The return of `PairTypeBOutcome_dependentIncrement`: one `get` per fact of
its ledger. -/
theorem pairTypeBDependentIncrementReturn
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
    [FactKeys.Has (K .pairConditionalFactorization) known]
    [FactKeys.Has (K .pairFailureOverlap) known]
    [FactKeys.Has (K .pairDemandReturns) known]
    [FactKeys.Has (K .pairSystemRealizability) known]
    [FactKeys.Has (K .typeBFanEntry) known]
    [FactKeys.Has (K .dependentPairFamily) known]
    [FactKeys.Has (K .pairDegreeProfileFibres) known]
    [FactKeys.Has (K .pairNoProfileObstruction) known]
    [FactKeys.Has (K .pairNoResponseObstruction) known]
    [FactKeys.Has (K .blockedPairNoExit) known]
    [FactKeys.Has (K .canonicalBlockerRoute) known]
    [FactKeys.Has (K .canonicalPairLedger) known]
    [FactKeys.Has (K .capacityTokenLedger) known]
    [FactKeys.Has (K .blockedPairEntropySetup) known]
    [FactKeys.Has (K .blockedPairCountFails) known]
    [FactKeys.Has (K .blockedPairCodeUnrealized) known]
    [FactKeys.Has (K .pairSystemNoEarlyOutcome) known]
    [FactKeys.Has (K .pairSerialDemandSystem) known]
    [FactKeys.Has (K .pairIncrementCovered) known]
    [FactKeys.Has (K .pairIncrementEarlyOutcome) known] :
    PairTypeBOutcome_dependentIncrement selected :=
  have pairSystemNoEarlyOutcome := (history.get (K .pairSystemNoEarlyOutcome)).down
  have pairSerialDemandSystem := (history.get (K .pairSerialDemandSystem)).down
  have pairIncrementCovered := (history.get (K .pairIncrementCovered)).down
  have pairIncrementEarlyOutcome := (history.get (K .pairIncrementEarlyOutcome)).down
  ⟨⟨(history.get (K .selection)).down,
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
      (history.get (K .everyWitnessSpectrumSplit)).down,
      (history.get (K .packingOrderBound)).down,
      (history.get (K .noSuppressionChordViolation)).down,
      (history.get (K .twoSwitchForcedPath)).down,
      (history.get (K .crossSwitchFamily)).down,
      (history.get (K .highCentreSplitForced)).down,
      (history.get (K .sameVertexSwitchForcedPath)).down,
      (history.get (K .specWitnessStructure)).down,
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
      (history.get (K .pairConditionalFactorization)).down,
      (history.get (K .pairFailureOverlap)).down,
      (history.get (K .pairDemandReturns)).down,
      (history.get (K .pairSystemRealizability)).down,
      (history.get (K .typeBFanEntry)).down,
      Or.inr ⟨pairSystemNoEarlyOutcome, pairSerialDemandSystem,
        pairIncrementCovered, pairIncrementEarlyOutcome⟩⟩,
    (history.get (K .dependentPairFamily)).down,
    (history.get (K .pairDegreeProfileFibres)).down,
    (history.get (K .pairNoProfileObstruction)).down,
    (history.get (K .pairNoResponseObstruction)).down,
    (history.get (K .blockedPairNoExit)).down,
    (history.get (K .canonicalBlockerRoute)).down,
    (history.get (K .canonicalPairLedger)).down,
    (history.get (K .capacityTokenLedger)).down,
    (history.get (K .blockedPairEntropySetup)).down,
    (history.get (K .blockedPairCountFails)).down,
    (history.get (K .blockedPairCodeUnrealized)).down,
    pairSystemNoEarlyOutcome,
    pairSerialDemandSystem,
    pairIncrementCovered,
    pairIncrementEarlyOutcome⟩

end HypostructureErdos64EG
