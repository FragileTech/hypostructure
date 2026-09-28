import HypostructureErdos64EG.Assembly.Residuals

/-!
# Assembly: Residuals / PairConditionalFactorizationOutcome

Node `[182]` is reached along six ledger histories with six distinct fact sets:
the pair-code chain `[178]`--`[180]` is entered from the free side of `[131]`
or from the blocked side of `[137]`, and returns `[182]` at the failure of
`[178]`'s conditional factorization, of `[179]`'s realizability, or of `[180]`'s
increment coverage.  Each fact set is its own open node, stated as a subtype of
the generic residual `PairConditionalFactorizationOutcome` (the 62 facts common
to all six): the generic residual conjoined with every extra fact of its set,
each read with one `ExactLedger.get`.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- **Node `[182]`, free side, factorizationFails**: `[130]` blocker-free arm, `[131]` free-pair count fails; `[178]` conditional factorization fails.
The generic residual and the 4 extra facts of this ledger (66 facts). -/
abbrev PairConditionalFactorizationOutcome_freeFactorizationFails (selected : EGInput.{u}) : Prop :=
  PairConditionalFactorizationOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .independentPairFamily selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .freePairCountFails selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .freePairCodeUnrealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairFactorizationFails selected.object

theorem PairConditionalFactorizationOutcome_freeFactorizationFails.toGeneric {selected : EGInput.{u}}
    (outcome : PairConditionalFactorizationOutcome_freeFactorizationFails selected) :
    PairConditionalFactorizationOutcome selected :=
  outcome.1

/-- The return of `PairConditionalFactorizationOutcome_freeFactorizationFails`: one `get` per fact of its ledger. -/
theorem pairConditionalFactorizationReturn_freeFactorizationFails
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
    [FactKeys.Has (K .surplusDartIdentity) known]
    [FactKeys.Has (K .highDegreeCountBound) known]
    [FactKeys.Has (K .admissibleQuotientsLabelInjective) known]
    [FactKeys.Has (K .surplusAbove) known]
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
    [FactKeys.Has (K .pairConditionalFactorizationResidual) known]
    [FactKeys.Has (K .independentPairFamily) known]
    [FactKeys.Has (K .freePairCountFails) known]
    [FactKeys.Has (K .freePairCodeUnrealized) known]
    [FactKeys.Has (K .pairFactorizationFails) known]
    : PairConditionalFactorizationOutcome_freeFactorizationFails selected :=
  ⟨pairConditionalFactorizationReturn history,
    (history.get (K .independentPairFamily)).down,
    (history.get (K .freePairCountFails)).down,
    (history.get (K .freePairCodeUnrealized)).down,
    (history.get (K .pairFactorizationFails)).down⟩

/-- **Node `[182]`, free side, realizabilityFails**: `[130]` blocker-free arm, `[131]` free-pair count fails; `[178]` factorization holds, `[179]` realizability fails.
The generic residual and the 7 extra facts of this ledger (69 facts). -/
abbrev PairConditionalFactorizationOutcome_freeRealizabilityFails (selected : EGInput.{u}) : Prop :=
  PairConditionalFactorizationOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .independentPairFamily selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .freePairCountFails selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .freePairCodeUnrealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairConditionalFactorization selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairFailureOverlap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairDemandReturns selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairRealizabilityFails selected.object

theorem PairConditionalFactorizationOutcome_freeRealizabilityFails.toGeneric {selected : EGInput.{u}}
    (outcome : PairConditionalFactorizationOutcome_freeRealizabilityFails selected) :
    PairConditionalFactorizationOutcome selected :=
  outcome.1

/-- The return of `PairConditionalFactorizationOutcome_freeRealizabilityFails`: one `get` per fact of its ledger. -/
theorem pairConditionalFactorizationReturn_freeRealizabilityFails
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
    [FactKeys.Has (K .surplusDartIdentity) known]
    [FactKeys.Has (K .highDegreeCountBound) known]
    [FactKeys.Has (K .admissibleQuotientsLabelInjective) known]
    [FactKeys.Has (K .surplusAbove) known]
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
    [FactKeys.Has (K .pairConditionalFactorizationResidual) known]
    [FactKeys.Has (K .independentPairFamily) known]
    [FactKeys.Has (K .freePairCountFails) known]
    [FactKeys.Has (K .freePairCodeUnrealized) known]
    [FactKeys.Has (K .pairConditionalFactorization) known]
    [FactKeys.Has (K .pairFailureOverlap) known]
    [FactKeys.Has (K .pairDemandReturns) known]
    [FactKeys.Has (K .pairRealizabilityFails) known]
    : PairConditionalFactorizationOutcome_freeRealizabilityFails selected :=
  ⟨pairConditionalFactorizationReturn history,
    (history.get (K .independentPairFamily)).down,
    (history.get (K .freePairCountFails)).down,
    (history.get (K .freePairCodeUnrealized)).down,
    (history.get (K .pairConditionalFactorization)).down,
    (history.get (K .pairFailureOverlap)).down,
    (history.get (K .pairDemandReturns)).down,
    (history.get (K .pairRealizabilityFails)).down⟩

/-- **Node `[182]`, free side, incrementFails**: `[130]` blocker-free arm, `[131]` free-pair count fails; `[179]` realizability holds with no early outcome, `[180]` increment coverage fails.
The generic residual and the 10 extra facts of this ledger (72 facts). -/
abbrev PairConditionalFactorizationOutcome_freeIncrementFails (selected : EGInput.{u}) : Prop :=
  PairConditionalFactorizationOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .independentPairFamily selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .freePairCountFails selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .freePairCodeUnrealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairConditionalFactorization selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairFailureOverlap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairDemandReturns selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairSystemRealizability selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairSystemNoEarlyOutcome selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairSerialDemandSystem selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairIncrementFails selected.object

theorem PairConditionalFactorizationOutcome_freeIncrementFails.toGeneric {selected : EGInput.{u}}
    (outcome : PairConditionalFactorizationOutcome_freeIncrementFails selected) :
    PairConditionalFactorizationOutcome selected :=
  outcome.1

/-- The return of `PairConditionalFactorizationOutcome_freeIncrementFails`: one `get` per fact of its ledger. -/
theorem pairConditionalFactorizationReturn_freeIncrementFails
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
    [FactKeys.Has (K .surplusDartIdentity) known]
    [FactKeys.Has (K .highDegreeCountBound) known]
    [FactKeys.Has (K .admissibleQuotientsLabelInjective) known]
    [FactKeys.Has (K .surplusAbove) known]
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
    [FactKeys.Has (K .pairConditionalFactorizationResidual) known]
    [FactKeys.Has (K .independentPairFamily) known]
    [FactKeys.Has (K .freePairCountFails) known]
    [FactKeys.Has (K .freePairCodeUnrealized) known]
    [FactKeys.Has (K .pairConditionalFactorization) known]
    [FactKeys.Has (K .pairFailureOverlap) known]
    [FactKeys.Has (K .pairDemandReturns) known]
    [FactKeys.Has (K .pairSystemRealizability) known]
    [FactKeys.Has (K .pairSystemNoEarlyOutcome) known]
    [FactKeys.Has (K .pairSerialDemandSystem) known]
    [FactKeys.Has (K .pairIncrementFails) known]
    : PairConditionalFactorizationOutcome_freeIncrementFails selected :=
  ⟨pairConditionalFactorizationReturn history,
    (history.get (K .independentPairFamily)).down,
    (history.get (K .freePairCountFails)).down,
    (history.get (K .freePairCodeUnrealized)).down,
    (history.get (K .pairConditionalFactorization)).down,
    (history.get (K .pairFailureOverlap)).down,
    (history.get (K .pairDemandReturns)).down,
    (history.get (K .pairSystemRealizability)).down,
    (history.get (K .pairSystemNoEarlyOutcome)).down,
    (history.get (K .pairSerialDemandSystem)).down,
    (history.get (K .pairIncrementFails)).down⟩

/-- **Node `[182]`, blocked side, factorizationFails**: `[130]` blocked arm (no (d)/(e) blocker), `[132]` no sparse exit, `[134]`--`[137]` token ledger, `[137]` blocked-side count fails; `[178]` conditional factorization fails.
The generic residual and the 12 extra facts of this ledger (74 facts). -/
abbrev PairConditionalFactorizationOutcome_blockedFactorizationFails (selected : EGInput.{u}) : Prop :=
  PairConditionalFactorizationOutcome selected ∧
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
      erdosReceiverLoadProfile spineData .pairFactorizationFails selected.object

theorem PairConditionalFactorizationOutcome_blockedFactorizationFails.toGeneric {selected : EGInput.{u}}
    (outcome : PairConditionalFactorizationOutcome_blockedFactorizationFails selected) :
    PairConditionalFactorizationOutcome selected :=
  outcome.1

/-- The return of `PairConditionalFactorizationOutcome_blockedFactorizationFails`: one `get` per fact of its ledger. -/
theorem pairConditionalFactorizationReturn_blockedFactorizationFails
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
    [FactKeys.Has (K .surplusDartIdentity) known]
    [FactKeys.Has (K .highDegreeCountBound) known]
    [FactKeys.Has (K .admissibleQuotientsLabelInjective) known]
    [FactKeys.Has (K .surplusAbove) known]
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
    [FactKeys.Has (K .pairConditionalFactorizationResidual) known]
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
    [FactKeys.Has (K .pairFactorizationFails) known]
    : PairConditionalFactorizationOutcome_blockedFactorizationFails selected :=
  ⟨pairConditionalFactorizationReturn history,
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
    (history.get (K .pairFactorizationFails)).down⟩

/-- **Node `[182]`, blocked side, realizabilityFails**: `[130]` blocked arm (no (d)/(e) blocker), `[132]` no sparse exit, `[134]`--`[137]` token ledger, `[137]` blocked-side count fails; `[178]` factorization holds, `[179]` realizability fails.
The generic residual and the 15 extra facts of this ledger (77 facts). -/
abbrev PairConditionalFactorizationOutcome_blockedRealizabilityFails (selected : EGInput.{u}) : Prop :=
  PairConditionalFactorizationOutcome selected ∧
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
      erdosReceiverLoadProfile spineData .pairConditionalFactorization selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairFailureOverlap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairDemandReturns selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairRealizabilityFails selected.object

theorem PairConditionalFactorizationOutcome_blockedRealizabilityFails.toGeneric {selected : EGInput.{u}}
    (outcome : PairConditionalFactorizationOutcome_blockedRealizabilityFails selected) :
    PairConditionalFactorizationOutcome selected :=
  outcome.1

/-- The return of `PairConditionalFactorizationOutcome_blockedRealizabilityFails`: one `get` per fact of its ledger. -/
theorem pairConditionalFactorizationReturn_blockedRealizabilityFails
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
    [FactKeys.Has (K .surplusDartIdentity) known]
    [FactKeys.Has (K .highDegreeCountBound) known]
    [FactKeys.Has (K .admissibleQuotientsLabelInjective) known]
    [FactKeys.Has (K .surplusAbove) known]
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
    [FactKeys.Has (K .pairConditionalFactorizationResidual) known]
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
    [FactKeys.Has (K .pairConditionalFactorization) known]
    [FactKeys.Has (K .pairFailureOverlap) known]
    [FactKeys.Has (K .pairDemandReturns) known]
    [FactKeys.Has (K .pairRealizabilityFails) known]
    : PairConditionalFactorizationOutcome_blockedRealizabilityFails selected :=
  ⟨pairConditionalFactorizationReturn history,
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
    (history.get (K .pairConditionalFactorization)).down,
    (history.get (K .pairFailureOverlap)).down,
    (history.get (K .pairDemandReturns)).down,
    (history.get (K .pairRealizabilityFails)).down⟩

/-- **Node `[182]`, blocked side, incrementFails**: `[130]` blocked arm (no (d)/(e) blocker), `[132]` no sparse exit, `[134]`--`[137]` token ledger, `[137]` blocked-side count fails; `[179]` realizability holds with no early outcome, `[180]` increment coverage fails.
The generic residual and the 18 extra facts of this ledger (80 facts). -/
abbrev PairConditionalFactorizationOutcome_blockedIncrementFails (selected : EGInput.{u}) : Prop :=
  PairConditionalFactorizationOutcome selected ∧
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
      erdosReceiverLoadProfile spineData .pairConditionalFactorization selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairFailureOverlap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairDemandReturns selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairSystemRealizability selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairSystemNoEarlyOutcome selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairSerialDemandSystem selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairIncrementFails selected.object

theorem PairConditionalFactorizationOutcome_blockedIncrementFails.toGeneric {selected : EGInput.{u}}
    (outcome : PairConditionalFactorizationOutcome_blockedIncrementFails selected) :
    PairConditionalFactorizationOutcome selected :=
  outcome.1

/-- The return of `PairConditionalFactorizationOutcome_blockedIncrementFails`: one `get` per fact of its ledger. -/
theorem pairConditionalFactorizationReturn_blockedIncrementFails
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
    [FactKeys.Has (K .surplusDartIdentity) known]
    [FactKeys.Has (K .highDegreeCountBound) known]
    [FactKeys.Has (K .admissibleQuotientsLabelInjective) known]
    [FactKeys.Has (K .surplusAbove) known]
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
    [FactKeys.Has (K .pairConditionalFactorizationResidual) known]
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
    [FactKeys.Has (K .pairConditionalFactorization) known]
    [FactKeys.Has (K .pairFailureOverlap) known]
    [FactKeys.Has (K .pairDemandReturns) known]
    [FactKeys.Has (K .pairSystemRealizability) known]
    [FactKeys.Has (K .pairSystemNoEarlyOutcome) known]
    [FactKeys.Has (K .pairSerialDemandSystem) known]
    [FactKeys.Has (K .pairIncrementFails) known]
    : PairConditionalFactorizationOutcome_blockedIncrementFails selected :=
  ⟨pairConditionalFactorizationReturn history,
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
    (history.get (K .pairConditionalFactorization)).down,
    (history.get (K .pairFailureOverlap)).down,
    (history.get (K .pairDemandReturns)).down,
    (history.get (K .pairSystemRealizability)).down,
    (history.get (K .pairSystemNoEarlyOutcome)).down,
    (history.get (K .pairSerialDemandSystem)).down,
    (history.get (K .pairIncrementFails)).down⟩

end HypostructureErdos64EG
