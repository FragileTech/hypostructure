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
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- **Node `[20a]`** (thm:main (i), tex 339-346): the strict-surplus named
sparse exit of [20]: the attempted-quotient target defect and its registered
structure, on the strict arm of [19].  The explicit conjunction of every
fact on its maximal ledger, 95 facts: the 19 facts of the path, the 76 facts
first published for `[20a]` (`SpineRows/SparseExitResidual.lean`, with
`K .bridgeless`, `K .sparseUpperEnvelope`, `K .baselineSpineDemand` and
`K .freePairCountFails`).  Each is now published at the earliest point where
its inputs are on the ledger: 11 in the entry prefix (carried by every
residual), 19 at the top of the strict arm of `[19]` (carried by every
strict-surplus residual), and the 46 that read `[20a]`'s own facts (or, for
`K .freePairCountFails`, would collide with `[131]`'s decision key) on the
`[20a]` arm. -/
abbrev Node20aOutcome (selected : EGInput.{u}) : Prop :=
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
      erdosReceiverLoadProfile spineData .surplusAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sparsePairExit selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sparseTargetDefectResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sparseTargetDefectStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .bridgeless selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sparseUpperEnvelope selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .baselineSpineDemand selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .freePairCountFails selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .witnessReadingsNotTargetComplete selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .witnessActualOutsideNegative selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .witnessReadingsCycleFree selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .witnessSupportOrderBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .witnessReadingGluesNotSmallerBaseline selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .noSuppressionChordViolation selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .edgeSurplusIdentity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .surplusDartIdentity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highDegreeCountBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .packingOrderBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .ceilSqrtAboveScale selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .orderAboveScaleSquare selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sixVertexExtremalEnvelope selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderDeficiencyBelowCut selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowCutCapacity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .witnessOutsideNotRealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .realizedContextsNegative selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .negativeSubGluingNotSmallerBaseline selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cycleSubContextSeparates selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pathSpectrumSplit selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .admissibleQuotientsLabelInjective selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .singleBoundaryShape selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .positiveSupportBoundaryTwo selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .supportCutEdgesTwo selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .boundaryLowInsideVertex selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .outsideLowVertex selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .twoBoundaryLowOutsideSide selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .twoBoundarySupportClosure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .twoBoundaryOutsideClosure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .twoBoundaryNoTargetSum selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .outsideOrBoundaryLarge selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .droppedEdgeTightDeficit selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .notBothReadingsWhole selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .firstWholeOrientation selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .firstWholeDeficitNonempty selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .firstWholeDeficitStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .firstWholeDeficitSum selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .secondWholeOrientation selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .secondWholeDeficitNonempty selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .secondWholeDeficitStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .secondWholeDeficitSum selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .deletedSupportReduction selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .deletedSupportDeficientVertex selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .deletedSupportDeficitSums selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .deletedSupportEdgeRestoration selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .deletedSupportEdgeSetRestoration selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .firstKeepsAllNotWhole selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .secondKeepsAllNotWhole selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highDegreePositive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highDegreeSurplusCapacity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairArmExcluded selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .twoBoundaryForcesArmOne selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .armOneForcedPath selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .twoBoundaryForcedPathCross selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .supportSteinerMinimal selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .steinerVerticesCut selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .wholeSupportEqual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .wholeDeficitBoundaryCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .wholeCutEdgeSurplusBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .canonicalCapacityExplicit selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .primitiveCarrierCount selected.object ∧
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
      erdosReceiverLoadProfile spineData .specWitnessStructure selected.object

/-- The return of `Node20aOutcome`: one `get` per fact of
its maximal ledger. -/
theorem node20aReturn
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
    [FactKeys.Has (K .surplusAbove) known]
    [FactKeys.Has (K .sparsePairExit) known]
    [FactKeys.Has (K .sparseTargetDefectResidual) known]
    [FactKeys.Has (K .sparseTargetDefectStructure) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .sparseUpperEnvelope) known]
    [FactKeys.Has (K .baselineSpineDemand) known]
    [FactKeys.Has (K .freePairCountFails) known]
    [FactKeys.Has (K .witnessReadingsNotTargetComplete) known]
    [FactKeys.Has (K .witnessActualOutsideNegative) known]
    [FactKeys.Has (K .witnessReadingsCycleFree) known]
    [FactKeys.Has (K .witnessSupportOrderBound) known]
    [FactKeys.Has (K .witnessReadingGluesNotSmallerBaseline) known]
    [FactKeys.Has (K .noSuppressionChordViolation) known]
    [FactKeys.Has (K .edgeSurplusIdentity) known]
    [FactKeys.Has (K .surplusDartIdentity) known]
    [FactKeys.Has (K .highDegreeCountBound) known]
    [FactKeys.Has (K .packingOrderBound) known]
    [FactKeys.Has (K .ceilSqrtAboveScale) known]
    [FactKeys.Has (K .orderAboveScaleSquare) known]
    [FactKeys.Has (K .sixVertexExtremalEnvelope) known]
    [FactKeys.Has (K .remainderDeficiencyBelowCut) known]
    [FactKeys.Has (K .windowCutCapacity) known]
    [FactKeys.Has (K .witnessOutsideNotRealized) known]
    [FactKeys.Has (K .realizedContextsNegative) known]
    [FactKeys.Has (K .negativeSubGluingNotSmallerBaseline) known]
    [FactKeys.Has (K .cycleSubContextSeparates) known]
    [FactKeys.Has (K .pathSpectrumSplit) known]
    [FactKeys.Has (K .admissibleQuotientsLabelInjective) known]
    [FactKeys.Has (K .singleBoundaryShape) known]
    [FactKeys.Has (K .positiveSupportBoundaryTwo) known]
    [FactKeys.Has (K .supportCutEdgesTwo) known]
    [FactKeys.Has (K .boundaryLowInsideVertex) known]
    [FactKeys.Has (K .outsideLowVertex) known]
    [FactKeys.Has (K .twoBoundaryLowOutsideSide) known]
    [FactKeys.Has (K .twoBoundarySupportClosure) known]
    [FactKeys.Has (K .twoBoundaryOutsideClosure) known]
    [FactKeys.Has (K .twoBoundaryNoTargetSum) known]
    [FactKeys.Has (K .outsideOrBoundaryLarge) known]
    [FactKeys.Has (K .droppedEdgeTightDeficit) known]
    [FactKeys.Has (K .notBothReadingsWhole) known]
    [FactKeys.Has (K .firstWholeOrientation) known]
    [FactKeys.Has (K .firstWholeDeficitNonempty) known]
    [FactKeys.Has (K .firstWholeDeficitStructure) known]
    [FactKeys.Has (K .firstWholeDeficitSum) known]
    [FactKeys.Has (K .secondWholeOrientation) known]
    [FactKeys.Has (K .secondWholeDeficitNonempty) known]
    [FactKeys.Has (K .secondWholeDeficitStructure) known]
    [FactKeys.Has (K .secondWholeDeficitSum) known]
    [FactKeys.Has (K .deletedSupportReduction) known]
    [FactKeys.Has (K .deletedSupportDeficientVertex) known]
    [FactKeys.Has (K .deletedSupportDeficitSums) known]
    [FactKeys.Has (K .deletedSupportEdgeRestoration) known]
    [FactKeys.Has (K .deletedSupportEdgeSetRestoration) known]
    [FactKeys.Has (K .firstKeepsAllNotWhole) known]
    [FactKeys.Has (K .secondKeepsAllNotWhole) known]
    [FactKeys.Has (K .highDegreePositive) known]
    [FactKeys.Has (K .highDegreeSurplusCapacity) known]
    [FactKeys.Has (K .pairArmExcluded) known]
    [FactKeys.Has (K .twoBoundaryForcesArmOne) known]
    [FactKeys.Has (K .armOneForcedPath) known]
    [FactKeys.Has (K .twoBoundaryForcedPathCross) known]
    [FactKeys.Has (K .supportSteinerMinimal) known]
    [FactKeys.Has (K .steinerVerticesCut) known]
    [FactKeys.Has (K .wholeSupportEqual) known]
    [FactKeys.Has (K .wholeDeficitBoundaryCount) known]
    [FactKeys.Has (K .wholeCutEdgeSurplusBound) known]
    [FactKeys.Has (K .canonicalCapacityExplicit) known]
    [FactKeys.Has (K .primitiveCarrierCount) known]
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
    [FactKeys.Has (K .specWitnessStructure) known] :
    Node20aOutcome selected :=
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
    (history.get (K .surplusAbove)).down,
    (history.get (K .sparsePairExit)).down,
    (history.get (K .sparseTargetDefectResidual)).down,
    (history.get (K .sparseTargetDefectStructure)).down,
    (history.get (K .bridgeless)).down,
    (history.get (K .sparseUpperEnvelope)).down,
    (history.get (K .baselineSpineDemand)).down,
    (history.get (K .freePairCountFails)).down,
    (history.get (K .witnessReadingsNotTargetComplete)).down,
    (history.get (K .witnessActualOutsideNegative)).down,
    (history.get (K .witnessReadingsCycleFree)).down,
    (history.get (K .witnessSupportOrderBound)).down,
    (history.get (K .witnessReadingGluesNotSmallerBaseline)).down,
    (history.get (K .noSuppressionChordViolation)).down,
    (history.get (K .edgeSurplusIdentity)).down,
    (history.get (K .surplusDartIdentity)).down,
    (history.get (K .highDegreeCountBound)).down,
    (history.get (K .packingOrderBound)).down,
    (history.get (K .ceilSqrtAboveScale)).down,
    (history.get (K .orderAboveScaleSquare)).down,
    (history.get (K .sixVertexExtremalEnvelope)).down,
    (history.get (K .remainderDeficiencyBelowCut)).down,
    (history.get (K .windowCutCapacity)).down,
    (history.get (K .witnessOutsideNotRealized)).down,
    (history.get (K .realizedContextsNegative)).down,
    (history.get (K .negativeSubGluingNotSmallerBaseline)).down,
    (history.get (K .cycleSubContextSeparates)).down,
    (history.get (K .pathSpectrumSplit)).down,
    (history.get (K .admissibleQuotientsLabelInjective)).down,
    (history.get (K .singleBoundaryShape)).down,
    (history.get (K .positiveSupportBoundaryTwo)).down,
    (history.get (K .supportCutEdgesTwo)).down,
    (history.get (K .boundaryLowInsideVertex)).down,
    (history.get (K .outsideLowVertex)).down,
    (history.get (K .twoBoundaryLowOutsideSide)).down,
    (history.get (K .twoBoundarySupportClosure)).down,
    (history.get (K .twoBoundaryOutsideClosure)).down,
    (history.get (K .twoBoundaryNoTargetSum)).down,
    (history.get (K .outsideOrBoundaryLarge)).down,
    (history.get (K .droppedEdgeTightDeficit)).down,
    (history.get (K .notBothReadingsWhole)).down,
    (history.get (K .firstWholeOrientation)).down,
    (history.get (K .firstWholeDeficitNonempty)).down,
    (history.get (K .firstWholeDeficitStructure)).down,
    (history.get (K .firstWholeDeficitSum)).down,
    (history.get (K .secondWholeOrientation)).down,
    (history.get (K .secondWholeDeficitNonempty)).down,
    (history.get (K .secondWholeDeficitStructure)).down,
    (history.get (K .secondWholeDeficitSum)).down,
    (history.get (K .deletedSupportReduction)).down,
    (history.get (K .deletedSupportDeficientVertex)).down,
    (history.get (K .deletedSupportDeficitSums)).down,
    (history.get (K .deletedSupportEdgeRestoration)).down,
    (history.get (K .deletedSupportEdgeSetRestoration)).down,
    (history.get (K .firstKeepsAllNotWhole)).down,
    (history.get (K .secondKeepsAllNotWhole)).down,
    (history.get (K .highDegreePositive)).down,
    (history.get (K .highDegreeSurplusCapacity)).down,
    (history.get (K .pairArmExcluded)).down,
    (history.get (K .twoBoundaryForcesArmOne)).down,
    (history.get (K .armOneForcedPath)).down,
    (history.get (K .twoBoundaryForcedPathCross)).down,
    (history.get (K .supportSteinerMinimal)).down,
    (history.get (K .steinerVerticesCut)).down,
    (history.get (K .wholeSupportEqual)).down,
    (history.get (K .wholeDeficitBoundaryCount)).down,
    (history.get (K .wholeCutEdgeSurplusBound)).down,
    (history.get (K .canonicalCapacityExplicit)).down,
    (history.get (K .primitiveCarrierCount)).down,
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
    (history.get (K .specWitnessStructure)).down⟩

/-- **Node `[187] (near-cubic target defect)`** (thm:main (vi), tex 369-378):
the sparse target-defect exit of [20] on the at-or-below-surplus arm of
[19].  The explicit conjunction of every fact on its maximal ledger (75
facts): the 30 facts of the path, then the 45 witness-level facts first
published on `[20a]` (`SpineRows/SparseExitResidual.lean`), re-invoked here by
the same six rows: this ledger carries the same `K .sparseTargetDefectResidual`,
so they are the same keys at the same canonical witness
`sparseTargetDefectWitness` (each contract is `atWitness_of_spec` of its
`<key>_of_spec`, stated for every `Spec` witness). -/
abbrev NearCubicTargetDefectOutcome (selected : EGInput.{u}) : Prop :=
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
      erdosReceiverLoadProfile spineData .specWitnessStructure selected.object ∧
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
      erdosReceiverLoadProfile spineData .surplusDartIdentity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highDegreeCountBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .admissibleQuotientsLabelInjective selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .surplusAtOrBelow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sparsePairExit selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sparseTargetDefectResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sparseTargetDefectStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .witnessReadingsNotTargetComplete selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .witnessActualOutsideNegative selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .witnessReadingsCycleFree selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .witnessSupportOrderBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .witnessReadingGluesNotSmallerBaseline selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .witnessOutsideNotRealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .realizedContextsNegative selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .negativeSubGluingNotSmallerBaseline selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cycleSubContextSeparates selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pathSpectrumSplit selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .positiveSupportBoundaryTwo selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .supportCutEdgesTwo selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .boundaryLowInsideVertex selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .outsideLowVertex selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .twoBoundaryLowOutsideSide selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .twoBoundarySupportClosure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .twoBoundaryOutsideClosure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .twoBoundaryNoTargetSum selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .outsideOrBoundaryLarge selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .droppedEdgeTightDeficit selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .notBothReadingsWhole selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .firstWholeOrientation selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .firstWholeDeficitNonempty selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .firstWholeDeficitStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .firstWholeDeficitSum selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .secondWholeOrientation selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .secondWholeDeficitNonempty selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .secondWholeDeficitStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .secondWholeDeficitSum selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .deletedSupportReduction selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .deletedSupportDeficientVertex selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .deletedSupportDeficitSums selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .deletedSupportEdgeRestoration selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .deletedSupportEdgeSetRestoration selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .firstKeepsAllNotWhole selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .secondKeepsAllNotWhole selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairArmExcluded selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .twoBoundaryForcesArmOne selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .armOneForcedPath selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .twoBoundaryForcedPathCross selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .supportSteinerMinimal selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .steinerVerticesCut selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .wholeSupportEqual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .wholeDeficitBoundaryCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .wholeCutEdgeSurplusBound selected.object

/-- The return of `NearCubicTargetDefectOutcome`: one `get` per fact of
its maximal ledger. -/
theorem nearCubicTargetDefectReturn
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
    [FactKeys.Has (K .surplusDartIdentity) known]
    [FactKeys.Has (K .highDegreeCountBound) known]
    [FactKeys.Has (K .admissibleQuotientsLabelInjective) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .sparsePairExit) known]
    [FactKeys.Has (K .sparseTargetDefectResidual) known]
    [FactKeys.Has (K .sparseTargetDefectStructure) known]
    [FactKeys.Has (K .witnessReadingsNotTargetComplete) known]
    [FactKeys.Has (K .witnessActualOutsideNegative) known]
    [FactKeys.Has (K .witnessReadingsCycleFree) known]
    [FactKeys.Has (K .witnessSupportOrderBound) known]
    [FactKeys.Has (K .witnessReadingGluesNotSmallerBaseline) known]
    [FactKeys.Has (K .witnessOutsideNotRealized) known]
    [FactKeys.Has (K .realizedContextsNegative) known]
    [FactKeys.Has (K .negativeSubGluingNotSmallerBaseline) known]
    [FactKeys.Has (K .cycleSubContextSeparates) known]
    [FactKeys.Has (K .pathSpectrumSplit) known]
    [FactKeys.Has (K .positiveSupportBoundaryTwo) known]
    [FactKeys.Has (K .supportCutEdgesTwo) known]
    [FactKeys.Has (K .boundaryLowInsideVertex) known]
    [FactKeys.Has (K .outsideLowVertex) known]
    [FactKeys.Has (K .twoBoundaryLowOutsideSide) known]
    [FactKeys.Has (K .twoBoundarySupportClosure) known]
    [FactKeys.Has (K .twoBoundaryOutsideClosure) known]
    [FactKeys.Has (K .twoBoundaryNoTargetSum) known]
    [FactKeys.Has (K .outsideOrBoundaryLarge) known]
    [FactKeys.Has (K .droppedEdgeTightDeficit) known]
    [FactKeys.Has (K .notBothReadingsWhole) known]
    [FactKeys.Has (K .firstWholeOrientation) known]
    [FactKeys.Has (K .firstWholeDeficitNonempty) known]
    [FactKeys.Has (K .firstWholeDeficitStructure) known]
    [FactKeys.Has (K .firstWholeDeficitSum) known]
    [FactKeys.Has (K .secondWholeOrientation) known]
    [FactKeys.Has (K .secondWholeDeficitNonempty) known]
    [FactKeys.Has (K .secondWholeDeficitStructure) known]
    [FactKeys.Has (K .secondWholeDeficitSum) known]
    [FactKeys.Has (K .deletedSupportReduction) known]
    [FactKeys.Has (K .deletedSupportDeficientVertex) known]
    [FactKeys.Has (K .deletedSupportDeficitSums) known]
    [FactKeys.Has (K .deletedSupportEdgeRestoration) known]
    [FactKeys.Has (K .deletedSupportEdgeSetRestoration) known]
    [FactKeys.Has (K .firstKeepsAllNotWhole) known]
    [FactKeys.Has (K .secondKeepsAllNotWhole) known]
    [FactKeys.Has (K .pairArmExcluded) known]
    [FactKeys.Has (K .twoBoundaryForcesArmOne) known]
    [FactKeys.Has (K .armOneForcedPath) known]
    [FactKeys.Has (K .twoBoundaryForcedPathCross) known]
    [FactKeys.Has (K .supportSteinerMinimal) known]
    [FactKeys.Has (K .steinerVerticesCut) known]
    [FactKeys.Has (K .wholeSupportEqual) known]
    [FactKeys.Has (K .wholeDeficitBoundaryCount) known]
    [FactKeys.Has (K .wholeCutEdgeSurplusBound) known] :
    NearCubicTargetDefectOutcome selected :=
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
    (history.get (K .specWitnessStructure)).down,
    (history.get (K .bridgeless)).down,
    (history.get (K .remainderDeficiencyBelowCut)).down,
    (history.get (K .windowCutCapacity)).down,
    (history.get (K .primitiveCarrierCount)).down,
    (history.get (K .singleBoundaryShape)).down,
    (history.get (K .surplusDartIdentity)).down,
    (history.get (K .highDegreeCountBound)).down,
    (history.get (K .admissibleQuotientsLabelInjective)).down,
    (history.get (K .surplusAtOrBelow)).down,
    (history.get (K .sparsePairExit)).down,
    (history.get (K .sparseTargetDefectResidual)).down,
    (history.get (K .sparseTargetDefectStructure)).down,
    (history.get (K .witnessReadingsNotTargetComplete)).down,
    (history.get (K .witnessActualOutsideNegative)).down,
    (history.get (K .witnessReadingsCycleFree)).down,
    (history.get (K .witnessSupportOrderBound)).down,
    (history.get (K .witnessReadingGluesNotSmallerBaseline)).down,
    (history.get (K .witnessOutsideNotRealized)).down,
    (history.get (K .realizedContextsNegative)).down,
    (history.get (K .negativeSubGluingNotSmallerBaseline)).down,
    (history.get (K .cycleSubContextSeparates)).down,
    (history.get (K .pathSpectrumSplit)).down,
    (history.get (K .positiveSupportBoundaryTwo)).down,
    (history.get (K .supportCutEdgesTwo)).down,
    (history.get (K .boundaryLowInsideVertex)).down,
    (history.get (K .outsideLowVertex)).down,
    (history.get (K .twoBoundaryLowOutsideSide)).down,
    (history.get (K .twoBoundarySupportClosure)).down,
    (history.get (K .twoBoundaryOutsideClosure)).down,
    (history.get (K .twoBoundaryNoTargetSum)).down,
    (history.get (K .outsideOrBoundaryLarge)).down,
    (history.get (K .droppedEdgeTightDeficit)).down,
    (history.get (K .notBothReadingsWhole)).down,
    (history.get (K .firstWholeOrientation)).down,
    (history.get (K .firstWholeDeficitNonempty)).down,
    (history.get (K .firstWholeDeficitStructure)).down,
    (history.get (K .firstWholeDeficitSum)).down,
    (history.get (K .secondWholeOrientation)).down,
    (history.get (K .secondWholeDeficitNonempty)).down,
    (history.get (K .secondWholeDeficitStructure)).down,
    (history.get (K .secondWholeDeficitSum)).down,
    (history.get (K .deletedSupportReduction)).down,
    (history.get (K .deletedSupportDeficientVertex)).down,
    (history.get (K .deletedSupportDeficitSums)).down,
    (history.get (K .deletedSupportEdgeRestoration)).down,
    (history.get (K .deletedSupportEdgeSetRestoration)).down,
    (history.get (K .firstKeepsAllNotWhole)).down,
    (history.get (K .secondKeepsAllNotWhole)).down,
    (history.get (K .pairArmExcluded)).down,
    (history.get (K .twoBoundaryForcesArmOne)).down,
    (history.get (K .armOneForcedPath)).down,
    (history.get (K .twoBoundaryForcedPathCross)).down,
    (history.get (K .supportSteinerMinimal)).down,
    (history.get (K .steinerVerticesCut)).down,
    (history.get (K .wholeSupportEqual)).down,
    (history.get (K .wholeDeficitBoundaryCount)).down,
    (history.get (K .wholeCutEdgeSurplusBound)).down⟩

/-- **Node `[144a]`** (thm:main (ii), tex 347-353): the same-token Type B
handoff of [144] on the strict-surplus survivor, or (the paper error at
[144]) the unresolved same-label pattern pair.  The generic residual: the
explicit conjunction of the 72 facts common to every path.  Its six distinct
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
      erdosReceiverLoadProfile spineData .specWitnessStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderDeficiencyBelowCut selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowCutCapacity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .primitiveCarrierCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .singleBoundaryShape selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .surplusDartIdentity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highDegreeCountBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .admissibleQuotientsLabelInjective selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .surplusAbove selected.object ∧
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
      erdosReceiverLoadProfile spineData .bottleneckRouting selected.object

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
    [FactKeys.Has (K .specWitnessStructure) known]
    [FactKeys.Has (K .remainderDeficiencyBelowCut) known]
    [FactKeys.Has (K .windowCutCapacity) known]
    [FactKeys.Has (K .primitiveCarrierCount) known]
    [FactKeys.Has (K .singleBoundaryShape) known]
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
    [FactKeys.Has (K .bottleneckRouting) known] :
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
    (history.get (K .specWitnessStructure)).down,
    (history.get (K .remainderDeficiencyBelowCut)).down,
    (history.get (K .windowCutCapacity)).down,
    (history.get (K .primitiveCarrierCount)).down,
    (history.get (K .singleBoundaryShape)).down,
    (history.get (K .surplusDartIdentity)).down,
    (history.get (K .highDegreeCountBound)).down,
    (history.get (K .admissibleQuotientsLabelInjective)).down,
    (history.get (K .surplusAbove)).down,
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
    (history.get (K .bottleneckRouting)).down⟩

/-- **Node `[172a]`** (thm:main (iii), tex 354-358): the first failed
conditional graph-count inequality of lem:scale-additivity on the dense-
packing branch, with its minimal same-scale barrier overlap.  The explicit
conjunction of every fact on its maximal ledger (82 common facts). -/
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
      erdosReceiverLoadProfile spineData .specWitnessStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderDeficiencyBelowCut selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowCutCapacity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .primitiveCarrierCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .singleBoundaryShape selected.object ∧
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
      erdosReceiverLoadProfile spineData .blockedBarrierOverlap selected.object

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
    [FactKeys.Has (K .specWitnessStructure) known]
    [FactKeys.Has (K .remainderDeficiencyBelowCut) known]
    [FactKeys.Has (K .windowCutCapacity) known]
    [FactKeys.Has (K .primitiveCarrierCount) known]
    [FactKeys.Has (K .singleBoundaryShape) known]
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
    [FactKeys.Has (K .blockedBarrierOverlap) known] :
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
    (history.get (K .specWitnessStructure)).down,
    (history.get (K .remainderDeficiencyBelowCut)).down,
    (history.get (K .windowCutCapacity)).down,
    (history.get (K .primitiveCarrierCount)).down,
    (history.get (K .singleBoundaryShape)).down,
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
    (history.get (K .blockedBarrierOverlap)).down⟩

/-- **Node `[182]`** (thm:main (iv), tex 359-363): the first failed coverage
implication of [178], [179] or [180] on the strict-surplus pair-code chain.
The explicit conjunction of every fact on its maximal ledger (62 common
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
      erdosReceiverLoadProfile spineData .specWitnessStructure selected.object ∧
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
      erdosReceiverLoadProfile spineData .surplusDartIdentity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highDegreeCountBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .admissibleQuotientsLabelInjective selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .surplusAbove selected.object ∧
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
      erdosReceiverLoadProfile spineData .pairConditionalFactorizationResidual selected.object

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
    [FactKeys.Has (K .specWitnessStructure) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .remainderDeficiencyBelowCut) known]
    [FactKeys.Has (K .windowCutCapacity) known]
    [FactKeys.Has (K .primitiveCarrierCount) known]
    [FactKeys.Has (K .singleBoundaryShape) known]
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
    [FactKeys.Has (K .freePairCountFails) known]
    [FactKeys.Has (K .sparseUpperEnvelope) known]
    [FactKeys.Has (K .pairOverlapFirstFailure) known]
    [FactKeys.Has (K .mixedSparseSpineDependence) known]
    [FactKeys.Has (K .exactCubicBaselineBudget) known]
    [FactKeys.Has (K .incrementalSkeletonRoom) known]
    [FactKeys.Has (K .skeletonDominates) known]
    [FactKeys.Has (K .pairOverlapSystem) known]
    [FactKeys.Has (K .pairConditionalFactorizationResidual) known] :
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
    (history.get (K .specWitnessStructure)).down,
    (history.get (K .bridgeless)).down,
    (history.get (K .remainderDeficiencyBelowCut)).down,
    (history.get (K .windowCutCapacity)).down,
    (history.get (K .primitiveCarrierCount)).down,
    (history.get (K .singleBoundaryShape)).down,
    (history.get (K .surplusDartIdentity)).down,
    (history.get (K .highDegreeCountBound)).down,
    (history.get (K .admissibleQuotientsLabelInjective)).down,
    (history.get (K .surplusAbove)).down,
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
    (history.get (K .pairConditionalFactorizationResidual)).down⟩

/-- **Node `[186]`** (thm:main (v), tex 364-368): the visible-entry route-8
residual after [181], [183]-[185], with the joint balances of lem:typeA-
unified-joint-balance.  The explicit conjunction of every fact on its
maximal ledger (90 common facts). -/
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
      erdosReceiverLoadProfile spineData .specWitnessStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderDeficiencyBelowCut selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowCutCapacity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .primitiveCarrierCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .singleBoundaryShape selected.object ∧
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
      erdosReceiverLoadProfile spineData .route8JointBalance selected.object

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
    [FactKeys.Has (K .specWitnessStructure) known]
    [FactKeys.Has (K .remainderDeficiencyBelowCut) known]
    [FactKeys.Has (K .windowCutCapacity) known]
    [FactKeys.Has (K .primitiveCarrierCount) known]
    [FactKeys.Has (K .singleBoundaryShape) known]
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
    [FactKeys.Has (K .route8JointBalance) known] :
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
    (history.get (K .specWitnessStructure)).down,
    (history.get (K .remainderDeficiencyBelowCut)).down,
    (history.get (K .windowCutCapacity)).down,
    (history.get (K .primitiveCarrierCount)).down,
    (history.get (K .singleBoundaryShape)).down,
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
    (history.get (K .route8JointBalance)).down⟩

/-- **Node `[187] ([179]/[180] Type B entry)`** (thm:main (vi), tex 369-378): a
Type B entry produced by the [179] or [180] pair-system outcome, with its
strict-surplus and sparse-survivor ancestry.  The explicit conjunction of
every fact on its maximal ledger (71 common facts, then the arms of the
residual's own decision: system 1; increment 4). -/
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
      erdosReceiverLoadProfile spineData .specWitnessStructure selected.object ∧
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
      erdosReceiverLoadProfile spineData .surplusDartIdentity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highDegreeCountBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .admissibleQuotientsLabelInjective selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .surplusAbove selected.object ∧
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
  (Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairSystemEarlyOutcome selected.object ∨
    (Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairSystemNoEarlyOutcome selected.object ∧
    Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairSerialDemandSystem selected.object ∧
    Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairIncrementCovered selected.object ∧
    Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .pairIncrementEarlyOutcome selected.object))

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
    [FactKeys.Has (K .specWitnessStructure) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .remainderDeficiencyBelowCut) known]
    [FactKeys.Has (K .windowCutCapacity) known]
    [FactKeys.Has (K .primitiveCarrierCount) known]
    [FactKeys.Has (K .singleBoundaryShape) known]
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
    (history.get (K .specWitnessStructure)).down,
    (history.get (K .bridgeless)).down,
    (history.get (K .remainderDeficiencyBelowCut)).down,
    (history.get (K .windowCutCapacity)).down,
    (history.get (K .primitiveCarrierCount)).down,
    (history.get (K .singleBoundaryShape)).down,
    (history.get (K .surplusDartIdentity)).down,
    (history.get (K .highDegreeCountBound)).down,
    (history.get (K .admissibleQuotientsLabelInjective)).down,
    (history.get (K .surplusAbove)).down,
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
    Or.inl ((history.get (K .pairSystemEarlyOutcome)).down)⟩

/-- The return of `PairTypeBOutcome` (arm `increment`): one `get` per fact of
its maximal ledger. -/
theorem pairTypeBIncrementReturn
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
    [FactKeys.Has (K .pairSystemNoEarlyOutcome) known]
    [FactKeys.Has (K .pairSerialDemandSystem) known]
    [FactKeys.Has (K .pairIncrementCovered) known]
    [FactKeys.Has (K .pairIncrementEarlyOutcome) known] :
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
    (history.get (K .specWitnessStructure)).down,
    (history.get (K .bridgeless)).down,
    (history.get (K .remainderDeficiencyBelowCut)).down,
    (history.get (K .windowCutCapacity)).down,
    (history.get (K .primitiveCarrierCount)).down,
    (history.get (K .singleBoundaryShape)).down,
    (history.get (K .surplusDartIdentity)).down,
    (history.get (K .highDegreeCountBound)).down,
    (history.get (K .admissibleQuotientsLabelInjective)).down,
    (history.get (K .surplusAbove)).down,
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
    Or.inr ⟨(history.get (K .pairSystemNoEarlyOutcome)).down,
    (history.get (K .pairSerialDemandSystem)).down,
    (history.get (K .pairIncrementCovered)).down,
    (history.get (K .pairIncrementEarlyOutcome)).down⟩⟩

/-- **Node `[187] (Type B sublinear failure)`** (thm:main (vi), tex 369-378):
failure of the Type B sublinear hypothesis package on the unified route-8
ledger.  The explicit conjunction of every fact on its maximal ledger (72
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
      erdosReceiverLoadProfile spineData .specWitnessStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderDeficiencyBelowCut selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowCutCapacity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .primitiveCarrierCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .singleBoundaryShape selected.object ∧
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
      erdosReceiverLoadProfile spineData .typeBSublinearResidual selected.object

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
    [FactKeys.Has (K .specWitnessStructure) known]
    [FactKeys.Has (K .remainderDeficiencyBelowCut) known]
    [FactKeys.Has (K .windowCutCapacity) known]
    [FactKeys.Has (K .primitiveCarrierCount) known]
    [FactKeys.Has (K .singleBoundaryShape) known]
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
    [FactKeys.Has (K .typeBSublinearResidual) known] :
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
    (history.get (K .specWitnessStructure)).down,
    (history.get (K .remainderDeficiencyBelowCut)).down,
    (history.get (K .windowCutCapacity)).down,
    (history.get (K .primitiveCarrierCount)).down,
    (history.get (K .singleBoundaryShape)).down,
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
    (history.get (K .typeBSublinearResidual)).down⟩

/-- **Node `[187] ([348], route-8 quotient failure)`** (thm:main (vi), tex
369-378, 388-390): failure of route-8 quotient freeness of the unified
census.  The explicit conjunction of every fact on its maximal ledger (74
common facts). -/
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
      erdosReceiverLoadProfile spineData .specWitnessStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderDeficiencyBelowCut selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowCutCapacity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .primitiveCarrierCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .singleBoundaryShape selected.object ∧
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
      erdosReceiverLoadProfile spineData .route8QuotientResidual selected.object

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
    [FactKeys.Has (K .specWitnessStructure) known]
    [FactKeys.Has (K .remainderDeficiencyBelowCut) known]
    [FactKeys.Has (K .windowCutCapacity) known]
    [FactKeys.Has (K .primitiveCarrierCount) known]
    [FactKeys.Has (K .singleBoundaryShape) known]
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
    [FactKeys.Has (K .route8QuotientResidual) known] :
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
    (history.get (K .specWitnessStructure)).down,
    (history.get (K .remainderDeficiencyBelowCut)).down,
    (history.get (K .windowCutCapacity)).down,
    (history.get (K .primitiveCarrierCount)).down,
    (history.get (K .singleBoundaryShape)).down,
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
    (history.get (K .route8QuotientResidual)).down⟩

/-- **Node `[187] (private-carrier rate failure)`** (thm:main (vi), tex
369-378): failure of the exact private-carrier rate at the entry of the
route-8 continuation.  The explicit conjunction of every fact on its maximal
ledger (54 common facts). -/
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
      erdosReceiverLoadProfile spineData .specWitnessStructure selected.object ∧
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
      erdosReceiverLoadProfile spineData .route8RateFails selected.object

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
    [FactKeys.Has (K .specWitnessStructure) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .remainderDeficiencyBelowCut) known]
    [FactKeys.Has (K .windowCutCapacity) known]
    [FactKeys.Has (K .primitiveCarrierCount) known]
    [FactKeys.Has (K .singleBoundaryShape) known]
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
    [FactKeys.Has (K .route8RateFails) known] :
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
    (history.get (K .specWitnessStructure)).down,
    (history.get (K .bridgeless)).down,
    (history.get (K .remainderDeficiencyBelowCut)).down,
    (history.get (K .windowCutCapacity)).down,
    (history.get (K .primitiveCarrierCount)).down,
    (history.get (K .singleBoundaryShape)).down,
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
    (history.get (K .route8RateFails)).down⟩

/-- **Node `[187] (local cold-terminal exclusion)`** (thm:main (vi), tex
369-378): the local cold-terminal exclusion of thm:cold-branch-quantitative-
closure without a global terminal contradiction.  The explicit conjunction
of every fact on its maximal ledger (68 common facts). -/
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
      erdosReceiverLoadProfile spineData .specWitnessStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderDeficiencyBelowCut selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowCutCapacity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .primitiveCarrierCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .singleBoundaryShape selected.object ∧
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
      erdosReceiverLoadProfile spineData .coldCutStatesDistinct selected.object ∧
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
    [FactKeys.Has (K .specWitnessStructure) known]
    [FactKeys.Has (K .remainderDeficiencyBelowCut) known]
    [FactKeys.Has (K .windowCutCapacity) known]
    [FactKeys.Has (K .primitiveCarrierCount) known]
    [FactKeys.Has (K .singleBoundaryShape) known]
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
    [FactKeys.Has (K .coldCutStatesDistinct) known]
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
    (history.get (K .specWitnessStructure)).down,
    (history.get (K .remainderDeficiencyBelowCut)).down,
    (history.get (K .windowCutCapacity)).down,
    (history.get (K .primitiveCarrierCount)).down,
    (history.get (K .singleBoundaryShape)).down,
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
    (history.get (K .coldCutStatesDistinct)).down,
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

/-- **Node `[153]`** (lem:cold-corridor-first-failure (ii), tex 7265-7270): G's
first equal-state pair on a retained cold corridor, with its separating path
context and profile separation.  The explicit conjunction of every fact on
its maximal ledger (53 common facts). -/
abbrev Node153ResidualOutcome (selected : EGInput.{u}) : Prop :=
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
      erdosReceiverLoadProfile spineData .specWitnessStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderDeficiencyBelowCut selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowCutCapacity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .primitiveCarrierCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .singleBoundaryShape selected.object ∧
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
      erdosReceiverLoadProfile spineData .coldRepeatedStateResidual selected.object

/-- The return of `Node153ResidualOutcome`: one `get` per fact of
its maximal ledger. -/
theorem node153Return
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
    [FactKeys.Has (K .remainderDeficiencyBelowCut) known]
    [FactKeys.Has (K .windowCutCapacity) known]
    [FactKeys.Has (K .primitiveCarrierCount) known]
    [FactKeys.Has (K .singleBoundaryShape) known]
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
    [FactKeys.Has (K .coldRepeatedStateResidual) known] :
    Node153ResidualOutcome selected :=
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
    (history.get (K .specWitnessStructure)).down,
    (history.get (K .remainderDeficiencyBelowCut)).down,
    (history.get (K .windowCutCapacity)).down,
    (history.get (K .primitiveCarrierCount)).down,
    (history.get (K .singleBoundaryShape)).down,
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
    (history.get (K .coldRepeatedStateResidual)).down⟩

/-- **Node `[162]`** (lem:dense-cold-pass, tex 7692-7694): a retained cold
corridor of G whose first failure is a heavy centre strictly before its
terminal segment and which reads more than Q_cold states.  The explicit
conjunction of every fact on its maximal ledger (57 common facts). -/
abbrev Node162ResidualOutcome (selected : EGInput.{u}) : Prop :=
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
      erdosReceiverLoadProfile spineData .specWitnessStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderDeficiencyBelowCut selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowCutCapacity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .primitiveCarrierCount selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .singleBoundaryShape selected.object ∧
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
      erdosReceiverLoadProfile spineData .coldDenseHeavyEntryResidual selected.object

/-- The return of `Node162ResidualOutcome`: one `get` per fact of
its maximal ledger. -/
theorem node162Return
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
    [FactKeys.Has (K .remainderDeficiencyBelowCut) known]
    [FactKeys.Has (K .windowCutCapacity) known]
    [FactKeys.Has (K .primitiveCarrierCount) known]
    [FactKeys.Has (K .singleBoundaryShape) known]
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
    [FactKeys.Has (K .coldDenseHeavyEntryResidual) known] :
    Node162ResidualOutcome selected :=
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
    (history.get (K .specWitnessStructure)).down,
    (history.get (K .remainderDeficiencyBelowCut)).down,
    (history.get (K .windowCutCapacity)).down,
    (history.get (K .primitiveCarrierCount)).down,
    (history.get (K .singleBoundaryShape)).down,
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
    (history.get (K .coldDenseHeavyEntryResidual)).down⟩

/-- **Node `[54]`** (prop:entropy-high-theta, tex 9921): the configuration at G
where the joint realization inequality RS(R0)*2^(rate*s*p13)*2^F <= B fails.
The explicit conjunction of every fact on its maximal ledger (52 common
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
      erdosReceiverLoadProfile spineData .specWitnessStructure selected.object ∧
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
      erdosReceiverLoadProfile spineData .allColdEntropyResidual selected.object

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
    [FactKeys.Has (K .specWitnessStructure) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .remainderDeficiencyBelowCut) known]
    [FactKeys.Has (K .windowCutCapacity) known]
    [FactKeys.Has (K .primitiveCarrierCount) known]
    [FactKeys.Has (K .singleBoundaryShape) known]
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
    [FactKeys.Has (K .allColdEntropyResidual) known] :
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
    (history.get (K .specWitnessStructure)).down,
    (history.get (K .bridgeless)).down,
    (history.get (K .remainderDeficiencyBelowCut)).down,
    (history.get (K .windowCutCapacity)).down,
    (history.get (K .primitiveCarrierCount)).down,
    (history.get (K .singleBoundaryShape)).down,
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
    (history.get (K .allColdEntropyResidual)).down⟩

end HypostructureErdos64EG
