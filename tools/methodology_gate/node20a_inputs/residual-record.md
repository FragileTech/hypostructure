# Node [20a]: the exact incoming residual `Node20aOutcome selected`

Pinned source revision: `g-repair-base` @ `7d3186b` (Merge port-20a). All paths are repository-relative. This file quotes the Lean source verbatim; it adds no mathematics.

* Residual definition: `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/Residuals.lean` lines 25-292 (`abbrev Node20aOutcome`).
* Return theorem: `node20aReturn` (same file): one `ExactLedger.get` per fact; the ledger `history : ExactLedger EGInput selected known` carries all 128 keys.
* Direct consumer: `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/Final.lean` line 351, `exact Or.inl (node20aReturn privateSwitchHistory)` — the first disjunct of the root result (`Node20aOutcome selected ∨ …`, Final.lean line 161).
* `Holds BranchState Presentation presentation data k object` is defined by cases on the key `k` in `hypostructure/Hypostructure/Graph/Strategy/SpineVocabulary.lean` (`def Holds`, line 1971); the clause for each key is quoted below. At G: `BranchState`, `Presentation := Graph.ReceiverLoad.LoadCapacityProfile`, `presentation := erdosReceiverLoadProfile`, `data := spineData`, `object := selected.object` (G).
* Target of this run: derive `False` from `Node20aOutcome selected`, or a significant exact reduction of it (an exact surviving residual carrying every one of the 128 facts plus the new ones).

## The residual definition (verbatim)

```lean
/-- **Node `[20a]`** (thm:main (i), tex 339-346): the strict-surplus named
sparse exit of [20]: the attempted-quotient target defect and its registered
structure, on the strict arm of [19].  The explicit conjunction of every
fact on its maximal ledger, 128 facts: the facts of the path and of the
entry prefix and strict arm of `[19]` (every lane's hoisted facts), the facts
first published for `[20a]` (`SpineRows/SparseExitResidual.lean`), and the 14
witness-level readings facts of `SpineRows/SparseExitReadings.lean` (whose
entry key `K .everyWitnessSpectrumSplit` and strict-arm keys
`K .highSurplusConfiguration`, `K .highEndpointSwitch` are carried by every
residual, resp. every strict-surplus residual).  Each is published at the
earliest point where its inputs are on the ledger. -/
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
      erdosReceiverLoadProfile spineData .everyWitnessSpectrumSplit selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .surplusAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highSurplusConfiguration selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highEndpointSwitch selected.object ∧
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
      erdosReceiverLoadProfile spineData .twoSwitchForcedPath selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .crossSwitchFamily selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .highCentreSplitForced selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sameVertexSwitchForcedPath selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .specWitnessStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .witnessReadingCounts selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .witnessActiveLabels selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .boundaryPartition selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .positiveCyclePrivateEdge selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .wholeCycleMeetsDeficit selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .wholePrivateEdges selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .spectrumArmOneRefined selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .separatingEdgeContextWitness selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .twoBoundaryAllActive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .privateEdgeSwap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .cubicLabelOutsidePath selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .separatingEdgeContextSpectrum selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .privateEdgeSwitch selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .twoBoundaryOutsideBoth selected.object
```

## The 128 facts: key, `Holds` clause, statement declaration

| # | fact id | key | `Holds` clause | declaration location |
|---|---|---|---|---|
| 1 | `f001_selection` | `K .selection` | `SelectionStatement BranchState Presentation presentation data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/Spine.lean:2518-2527` |
| 2 | `f002_cubicBaseline` | `K .cubicBaseline` | `PresentationLawsStatement data.toParameters data.windowBarrierLabel object` | `hypostructure/Hypostructure/Graph/Strategy/SpineVocabulary.lean:1941-1961` |
| 3 | `f003_minDegreeBaseline` | `K .minDegreeBaseline` | `MinDegreeBaselineStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/Spine.lean:2529-2536` |
| 4 | `f004_returnAvoidance` | `K .returnAvoidance` | `ReturnAvoidanceStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/Spine.lean:2634-2643` |
| 5 | `f005_noProperBaseline` | `K .noProperBaseline` | `NoProperBaselineStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/Spine.lean:2656-2663` |
| 6 | `f006_slackIndependent` | `K .slackIndependent` | `SlackIndependentStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/Spine.lean:2675-2684` |
| 7 | `f007_tightEndpoint` | `K .tightEndpoint` | `TightEndpointStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/Spine.lean:2665-2673` |
| 8 | `f008_cycleRankConstraint` | `K .cycleRankConstraint` | `CycleRankConstraintStatement object` | `hypostructure/Hypostructure/Graph/Statements/Spine.lean:2686-2691` |
| 9 | `f009_degreeProfileFibres` | `K .degreeProfileFibres` | `DegreeProfileFibresStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/Spine.lean:2709-2727` |
| 10 | `f010_targetCompleteContextUniversality` | `K .targetCompleteContextUniversality` | `TargetCompleteContextUniversalityStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/Spine.lean:2729-2769` |
| 11 | `f011_replacementExclusion` | `K .replacementExclusion` | `ReplacementExclusionStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/Spine.lean:2771-2781` |
| 12 | `f012_uncompressible` | `K .uncompressible` | `UncompressibleStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/Spine.lean:2783-2797` |
| 13 | `f013_windowPresent` | `K .windowPresent` | `Graph.HasInducedPath object data.windowOrder` | `hypostructure/Hypostructure/Graph/InducedPath.lean:15-17` |
| 14 | `f014_maximalPacking` | `K .maximalPacking` | `MaximalPackingStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/Spine.lean:2799-2812` |
| 15 | `f015_localAlgebra` | `K .localAlgebra` | `LocalAlgebraStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/Spine.lean:2841-2852` |
| 16 | `f016_everyWitnessSpectrumSplit` | `K .everyWitnessSpectrumSplit` | `EveryWitnessSpectrumSplitStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean:68-101` |
| 17 | `f017_surplusAbove` | `K .surplusAbove` | `SurplusAboveStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/Spine.lean:2854-2861` |
| 18 | `f018_highSurplusConfiguration` | `K .highSurplusConfiguration` | `HighSurplusConfigurationStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean:40-46` |
| 19 | `f019_highEndpointSwitch` | `K .highEndpointSwitch` | `HighEndpointSwitchStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean:48-64` |
| 20 | `f020_sparsePairExit` | `K .sparsePairExit` | `SparsePairExitStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SurplusPair.lean:1093-1101` |
| 21 | `f021_sparseTargetDefectResidual` | `K .sparseTargetDefectResidual` | `SparseTargetDefectResidualStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SurplusPair.lean:1200-1212` |
| 22 | `f022_sparseTargetDefectStructure` | `K .sparseTargetDefectStructure` | `SparseTargetDefectStructureStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SurplusPair.lean:1214-1228` |
| 23 | `f023_bridgeless` | `K .bridgeless` | `BridgelessStatement object` | `hypostructure/Hypostructure/Graph/Statements/Spine.lean:3348-3354` |
| 24 | `f024_sparseUpperEnvelope` | `K .sparseUpperEnvelope` | `SparseUpperEnvelopeStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SurplusPair.lean:1482-1497` |
| 25 | `f025_baselineSpineDemand` | `K .baselineSpineDemand` | `BaselineSpineDemandStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SurplusPair.lean:1044-1062` |
| 26 | `f026_freePairCountFails` | `K .freePairCountFails` | `FreePairCountFailsStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SurplusPairCode.lean:37-42` |
| 27 | `f027_witnessReadingsNotTargetComplete` | `K .witnessReadingsNotTargetComplete` | `WitnessReadingsNotTargetCompleteStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:143-146` |
| 28 | `f028_witnessActualOutsideNegative` | `K .witnessActualOutsideNegative` | `WitnessActualOutsideNegativeStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:158-161` |
| 29 | `f029_witnessReadingsCycleFree` | `K .witnessReadingsCycleFree` | `WitnessReadingsCycleFreeStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:171-174` |
| 30 | `f030_witnessSupportOrderBound` | `K .witnessSupportOrderBound` | `WitnessSupportOrderBoundStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:183-186` |
| 31 | `f031_witnessReadingGluesNotSmallerBaseline` | `K .witnessReadingGluesNotSmallerBaseline` | `WitnessReadingGluesNotSmallerBaselineStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:200-204` |
| 32 | `f032_noSuppressionChordViolation` | `K .noSuppressionChordViolation` | `NoSuppressionChordViolationStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:206-212` |
| 33 | `f033_edgeSurplusIdentity` | `K .edgeSurplusIdentity` | `EdgeSurplusIdentityStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:77-81` |
| 34 | `f034_surplusDartIdentity` | `K .surplusDartIdentity` | `SurplusDartIdentityStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:83-89` |
| 35 | `f035_highDegreeCountBound` | `K .highDegreeCountBound` | `HighDegreeCountBoundStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:91-94` |
| 36 | `f036_packingOrderBound` | `K .packingOrderBound` | `PackingOrderBoundStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:108-111` |
| 37 | `f037_ceilSqrtAboveScale` | `K .ceilSqrtAboveScale` | `CeilSqrtAboveScaleStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:113-116` |
| 38 | `f038_orderAboveScaleSquare` | `K .orderAboveScaleSquare` | `OrderAboveScaleSquareStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:118-121` |
| 39 | `f039_sixVertexExtremalEnvelope` | `K .sixVertexExtremalEnvelope` | `SixVertexExtremalEnvelopeStatement object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:127-129` |
| 40 | `f040_remainderDeficiencyBelowCut` | `K .remainderDeficiencyBelowCut` | `RemainderDeficiencyBelowCutStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:1071-1077` |
| 41 | `f041_windowCutCapacity` | `K .windowCutCapacity` | `WindowCutCapacityStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:1079-1087` |
| 42 | `f042_witnessOutsideNotRealized` | `K .witnessOutsideNotRealized` | `WitnessOutsideNotRealizedStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:223-226` |
| 43 | `f043_realizedContextsNegative` | `K .realizedContextsNegative` | `RealizedContextsNegativeStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:238-241` |
| 44 | `f044_negativeSubGluingNotSmallerBaseline` | `K .negativeSubGluingNotSmallerBaseline` | `NegativeSubGluingNotSmallerBaselineStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:258-262` |
| 45 | `f045_cycleSubContextSeparates` | `K .cycleSubContextSeparates` | `CycleSubContextSeparatesStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:282-287` |
| 46 | `f046_pathSpectrumSplit` | `K .pathSpectrumSplit` | `PathSpectrumSplitStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:338-346` |
| 47 | `f047_admissibleQuotientsLabelInjective` | `K .admissibleQuotientsLabelInjective` | `AdmissibleQuotientsLabelInjectiveStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:353-360` |
| 48 | `f048_singleBoundaryShape` | `K .singleBoundaryShape` | `SingleBoundaryShapeStatement object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:369-379` |
| 49 | `f049_neighbourhoodPairCount` | `K .neighbourhoodPairCount` | `NeighbourhoodPairCountStatement object` | `hypostructure/Hypostructure/Graph/Statements/CycleCounting.lean:30-35` |
| 50 | `f050_starCycleConstraint` | `K .starCycleConstraint` | `StarCycleConstraintStatement object` | `hypostructure/Hypostructure/Graph/Statements/CycleCounting.lean:37-42` |
| 51 | `f051_meetingCycleConstraint` | `K .meetingCycleConstraint` | `MeetingCycleConstraintStatement object` | `hypostructure/Hypostructure/Graph/Statements/CycleCounting.lean:44-49` |
| 52 | `f052_highDegreePairSum` | `K .highDegreePairSum` | `HighDegreePairSumStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/CycleCounting.lean:51-57` |
| 53 | `f053_vertexDeletionComponents` | `K .vertexDeletionComponents` | `VertexDeletionComponentsStatement object` | `hypostructure/Hypostructure/Graph/Statements/CycleCounting.lean:59-64` |
| 54 | `f054_cyclesThroughVertex` | `K .cyclesThroughVertex` | `CyclesThroughVertexStatement object` | `hypostructure/Hypostructure/Graph/Statements/CycleCounting.lean:66-69` |
| 55 | `f055_cutVertexBlockPaths` | `K .cutVertexBlockPaths` | `CutVertexBlockPathsStatement object` | `hypostructure/Hypostructure/Graph/Statements/CycleCounting.lean:71-78` |
| 56 | `f056_cycleDoubleCount` | `K .cycleDoubleCount` | `CycleDoubleCountStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/CycleCounting.lean:80-85` |
| 57 | `f057_threeRouteFan` | `K .threeRouteFan` | `ThreeRouteFanStatement object` | `hypostructure/Hypostructure/Graph/Statements/LocalRigidity.lean:27-32` |
| 58 | `f058_threeRouteChain` | `K .threeRouteChain` | `ThreeRouteChainStatement object` | `hypostructure/Hypostructure/Graph/Statements/LocalRigidity.lean:34-38` |
| 59 | `f059_windowPositionStubs` | `K .windowPositionStubs` | `WindowPositionStubsStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/LocalRigidity.lean:52-58` |
| 60 | `f060_windowAttachmentGap` | `K .windowAttachmentGap` | `WindowAttachmentGapStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/LocalRigidity.lean:40-50` |
| 61 | `f061_positiveSupportBoundaryTwo` | `K .positiveSupportBoundaryTwo` | `PositiveSupportBoundaryTwoStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:391-394` |
| 62 | `f062_supportCutEdgesTwo` | `K .supportCutEdgesTwo` | `SupportCutEdgesTwoStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:410-413` |
| 63 | `f063_boundaryLowInsideVertex` | `K .boundaryLowInsideVertex` | `BoundaryLowInsideVertexStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:422-425` |
| 64 | `f064_outsideLowVertex` | `K .outsideLowVertex` | `OutsideLowVertexStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:437-441` |
| 65 | `f065_twoBoundaryLowOutsideSide` | `K .twoBoundaryLowOutsideSide` | `TwoBoundaryLowOutsideSideStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:453-457` |
| 66 | `f066_twoBoundarySupportClosure` | `K .twoBoundarySupportClosure` | `TwoBoundarySupportClosureStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:470-475` |
| 67 | `f067_twoBoundaryOutsideClosure` | `K .twoBoundaryOutsideClosure` | `TwoBoundaryOutsideClosureStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:491-494` |
| 68 | `f068_twoBoundaryNoTargetSum` | `K .twoBoundaryNoTargetSum` | `TwoBoundaryNoTargetSumStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:507-512` |
| 69 | `f069_outsideOrBoundaryLarge` | `K .outsideOrBoundaryLarge` | `OutsideOrBoundaryLargeStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:528-531` |
| 70 | `f070_droppedEdgeTightDeficit` | `K .droppedEdgeTightDeficit` | `DroppedEdgeTightDeficitStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:552-556` |
| 71 | `f071_notBothReadingsWhole` | `K .notBothReadingsWhole` | `NotBothReadingsWholeStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:566-569` |
| 72 | `f072_firstWholeOrientation` | `K .firstWholeOrientation` | `FirstWholeOrientationStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:639-642` |
| 73 | `f073_firstWholeDeficitNonempty` | `K .firstWholeDeficitNonempty` | `FirstWholeDeficitNonemptyStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:651-654` |
| 74 | `f074_firstWholeDeficitStructure` | `K .firstWholeDeficitStructure` | `FirstWholeDeficitStructureStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:663-667` |
| 75 | `f075_firstWholeDeficitSum` | `K .firstWholeDeficitSum` | `FirstWholeDeficitSumStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:676-680` |
| 76 | `f076_secondWholeOrientation` | `K .secondWholeOrientation` | `SecondWholeOrientationStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:689-692` |
| 77 | `f077_secondWholeDeficitNonempty` | `K .secondWholeDeficitNonempty` | `SecondWholeDeficitNonemptyStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:701-704` |
| 78 | `f078_secondWholeDeficitStructure` | `K .secondWholeDeficitStructure` | `SecondWholeDeficitStructureStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:713-717` |
| 79 | `f079_secondWholeDeficitSum` | `K .secondWholeDeficitSum` | `SecondWholeDeficitSumStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:726-730` |
| 80 | `f080_deletedSupportReduction` | `K .deletedSupportReduction` | `DeletedSupportReductionStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:762-764` |
| 81 | `f081_deletedSupportDeficientVertex` | `K .deletedSupportDeficientVertex` | `DeletedSupportDeficientVertexStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:784-786` |
| 82 | `f082_deletedSupportDeficitSums` | `K .deletedSupportDeficitSums` | `DeletedSupportDeficitSumsStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:812-814` |
| 83 | `f083_deletedSupportEdgeRestoration` | `K .deletedSupportEdgeRestoration` | `DeletedSupportEdgeRestorationStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:835-837` |
| 84 | `f084_deletedSupportEdgeSetRestoration` | `K .deletedSupportEdgeSetRestoration` | `DeletedSupportEdgeSetRestorationStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:858-860` |
| 85 | `f085_firstKeepsAllNotWhole` | `K .firstKeepsAllNotWhole` | `FirstKeepsAllNotWholeStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:875-879` |
| 86 | `f086_secondKeepsAllNotWhole` | `K .secondKeepsAllNotWhole` | `SecondKeepsAllNotWholeStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:894-898` |
| 87 | `f087_highDegreePositive` | `K .highDegreePositive` | `HighDegreePositiveStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:96-99` |
| 88 | `f088_highDegreeSurplusCapacity` | `K .highDegreeSurplusCapacity` | `HighDegreeSurplusCapacityStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:101-106` |
| 89 | `f089_pairArmExcluded` | `K .pairArmExcluded` | `PairArmExcludedStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:907-912` |
| 90 | `f090_twoBoundaryForcesArmOne` | `K .twoBoundaryForcesArmOne` | `TwoBoundaryForcesArmOneStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:929-934` |
| 91 | `f091_armOneForcedPath` | `K .armOneForcedPath` | `ArmOneForcedPathStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:949-954` |
| 92 | `f092_twoBoundaryForcedPathCross` | `K .twoBoundaryForcedPathCross` | `TwoBoundaryForcedPathCrossStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:974-981` |
| 93 | `f093_supportSteinerMinimal` | `K .supportSteinerMinimal` | `SupportSteinerMinimalStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:993-996` |
| 94 | `f094_steinerVerticesCut` | `K .steinerVerticesCut` | `SteinerVerticesCutStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:1007-1010` |
| 95 | `f095_wholeSupportEqual` | `K .wholeSupportEqual` | `WholeSupportEqualStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:1024-1027` |
| 96 | `f096_wholeDeficitBoundaryCount` | `K .wholeDeficitBoundaryCount` | `WholeDeficitBoundaryCountStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:1042-1045` |
| 97 | `f097_wholeCutEdgeSurplusBound` | `K .wholeCutEdgeSurplusBound` | `WholeCutEdgeSurplusBoundStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:1062-1065` |
| 98 | `f098_canonicalCapacityExplicit` | `K .canonicalCapacityExplicit` | `CanonicalCapacityExplicitStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:1114-1123` |
| 99 | `f099_primitiveCarrierCount` | `K .primitiveCarrierCount` | `PrimitiveCarrierCountStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:1125-1129` |
| 100 | `f100_canonicalTokenCount` | `K .canonicalTokenCount` | `CanonicalTokenCountStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:1131-1139` |
| 101 | `f101_canonicalBlockedFreePartition` | `K .canonicalBlockedFreePartition` | `CanonicalBlockedFreePartitionStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:1141-1146` |
| 102 | `f102_canonicalLedgerDeficit` | `K .canonicalLedgerDeficit` | `CanonicalLedgerDeficitStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:1148-1159` |
| 103 | `f103_pairCountDeficit` | `K .pairCountDeficit` | `PairCountDeficitStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:1161-1167` |
| 104 | `f104_canonicalCertificationCriterion` | `K .canonicalCertificationCriterion` | `CanonicalCertificationCriterionStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:1169-1175` |
| 105 | `f105_canonicalOverloadOfFits` | `K .canonicalOverloadOfFits` | `CanonicalOverloadOfFitsStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:1200-1221` |
| 106 | `f106_canonicalFreeExcessOfCapped` | `K .canonicalFreeExcessOfCapped` | `CanonicalFreeExcessOfCappedStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:1223-1233` |
| 107 | `f107_paperBudgetBound` | `K .paperBudgetBound` | `PaperBudgetBoundStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:1184-1189` |
| 108 | `f108_paperBudgetCertifies` | `K .paperBudgetCertifies` | `PaperBudgetCertifiesStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:1191-1198` |
| 109 | `f109_pairCodeConfiguration` | `K .pairCodeConfiguration` | `PairCodeConfigurationStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:1235-1255` |
| 110 | `f110_twoSwitchForcedPath` | `K .twoSwitchForcedPath` | `TwoSwitchForcedPathStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SwitchForcedPaths.lean:34-45` |
| 111 | `f111_crossSwitchFamily` | `K .crossSwitchFamily` | `CrossSwitchFamilyStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SwitchForcedPaths.lean:78-95` |
| 112 | `f112_highCentreSplitForced` | `K .highCentreSplitForced` | `HighCentreSplitForcedStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SwitchForcedPaths.lean:65-76` |
| 113 | `f113_sameVertexSwitchForcedPath` | `K .sameVertexSwitchForcedPath` | `SameVertexSwitchForcedPathStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SwitchForcedPaths.lean:47-63` |
| 114 | `f114_specWitnessStructure` | `K .specWitnessStructure` | `SpecWitnessStructureStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean:1260-1286` |
| 115 | `f115_witnessReadingCounts` | `K .witnessReadingCounts` | `WitnessReadingCountsStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean:203-208` |
| 116 | `f116_witnessActiveLabels` | `K .witnessActiveLabels` | `WitnessActiveLabelsStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean:225-231` |
| 117 | `f117_boundaryPartition` | `K .boundaryPartition` | `BoundaryPartitionStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean:264-270` |
| 118 | `f118_positiveCyclePrivateEdge` | `K .positiveCyclePrivateEdge` | `PositiveCyclePrivateEdgeStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean:280-287` |
| 119 | `f119_wholeCycleMeetsDeficit` | `K .wholeCycleMeetsDeficit` | `WholeCycleMeetsDeficitStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean:294-298` |
| 120 | `f120_wholePrivateEdges` | `K .wholePrivateEdges` | `WholePrivateEdgesStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean:305-309` |
| 121 | `f121_spectrumArmOneRefined` | `K .spectrumArmOneRefined` | `SpectrumArmOneRefinedStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean:320-329` |
| 122 | `f122_separatingEdgeContextWitness` | `K .separatingEdgeContextWitness` | `SeparatingEdgeContextWitnessStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean:353-359` |
| 123 | `f123_twoBoundaryAllActive` | `K .twoBoundaryAllActive` | `TwoBoundaryAllActiveStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean:241-244` |
| 124 | `f124_privateEdgeSwap` | `K .privateEdgeSwap` | `PrivateEdgeSwapStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean:414-420` |
| 125 | `f125_cubicLabelOutsidePath` | `K .cubicLabelOutsidePath` | `CubicLabelOutsidePathStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean:463-468` |
| 126 | `f126_separatingEdgeContextSpectrum` | `K .separatingEdgeContextSpectrum` | `SeparatingEdgeContextSpectrumStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean:391-399` |
| 127 | `f127_privateEdgeSwitch` | `K .privateEdgeSwitch` | `PrivateEdgeSwitchStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean:445-453` |
| 128 | `f128_twoBoundaryOutsideBoth` | `K .twoBoundaryOutsideBoth` | `TwoBoundaryOutsideBothStatement data.toParameters object` | `hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean:481-486` |

## Exact statements (verbatim Lean, in residual order)

### 1. `K .selection` (fact `f001_selection`)

`Holds … .selection object = SelectionStatement BranchState Presentation presentation data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/Spine.lean` lines 2518-2527:

```lean
/-- Nodes `[1]`--`[4]`: the selected object avoids the target and every
strictly smaller baseline object does not. -/
noncomputable abbrev SelectionStatement
    (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation)
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  (¬ Graph.HasCycleWithLength data.LengthOK object ∧
    SelectionMinimality BranchState Presentation presentation data object)
```

### 2. `K .cubicBaseline` (fact `f002_cubicBaseline`)

`Holds … .cubicBaseline object = PresentationLawsStatement data.toParameters data.windowBarrierLabel object`; source `hypostructure/Hypostructure/Graph/Strategy/SpineVocabulary.lean` lines 1941-1961:

```lean
/-- **The presentation laws of G's registered presentation, published once at
the entry** under the one key `K .cubicBaseline`.  The four components are
disjoint: no law appears in two of them, and no other key publishes any of
them.

1. `CubicBaselineStatement`: `δ = 3`, `s = 4`, `2` is not an accepted length,
   and the window rate is the barrier table's rate;
2. `TypeBPresentationStatement`: the quadrilateral is accepted, the accepted
   lengths are exactly the dyadic ones (the one copy of the target law), and
   the Type B fan, deficit and bridge-mass slacks;
3. `SurplusPresentationStatement`: the sparse-surplus presentation identities;
4. `SpinePresentationLawsStatement`: the HSS closure law at `G` and at `G`'s
   induced subgraphs, the scale family, the net-cap slack and the barrier
   table's label semantics, stated at `G`. -/
noncomputable abbrev PresentationLawsStatement (data : Parameters)
    (label : Fin data.windowBarrier.size →
      Graph.WindowCurvature.Label data.windowOrder)
    (object : Graph.FiniteObject.{u}) : Prop :=
  CubicBaselineStatement data ∧ TypeBPresentationStatement data ∧
    SurplusPresentationStatement data ∧
    SpinePresentationLawsStatement data label object
```

### 3. `K .minDegreeBaseline` (fact `f003_minDegreeBaseline`)

`Holds … .minDegreeBaseline object = MinDegreeBaselineStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/Spine.lean` lines 2529-2536:

```lean
/-- **G meets the registered baseline** (`def:counterexample`, nodes
`[1]`--`[3]`, tex 714, 1370: `δ(G) ≥ 3`): every vertex of G has degree at least
the registered threshold (`δ = 3` by `CubicBaselineStatement`).  Published once
at the entry (key `minDegreeBaseline`) from the selected object's own baseline
proof, so the fact is on G's ledger rather than only in the input. -/
noncomputable abbrev MinDegreeBaselineStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.MinimumDegreeAtLeast data.threshold object
```

### 4. `K .returnAvoidance` (fact `f004_returnAvoidance`)

`Holds … .returnAvoidance object = ReturnAvoidanceStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/Spine.lean` lines 2634-2643:

```lean
/-- Nodes `[5]`--`[7]`: the return-length set is disjoint from the shifted
accepted set at every oriented edge.  This is the return-set form of target
avoidance, the standing invariant the rest of the spine consumes. -/
noncomputable abbrev ReturnAvoidanceStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  (∀ dart : object.graph.Dart,
    Disjoint (Graph.returnLengthSet object dart)
      (Graph.shiftedAcceptedSet data.LengthOK))
```

### 5. `K .noProperBaseline` (fact `f005_noProperBaseline`)

`Holds … .noProperBaseline object = NoProperBaselineStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/Spine.lean` lines 2656-2663:

```lean
/-- Node `[8]`: no proper subgraph satisfies the baseline. -/
noncomputable abbrev NoProperBaselineStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  (∀ subgraph : Graph.ProperSubgraph object,
    ¬ Graph.MinimumDegreeAtLeast data.threshold subgraph.value) ∧
  object.graph.Connected
```

### 6. `K .slackIndependent` (fact `f006_slackIndependent`)

`Holds … .slackIndependent object = SlackIndependentStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/Spine.lean` lines 2675-2684:

```lean
/-- Node `[10]`: vertices strictly above the threshold are pairwise
nonadjacent. -/
noncomputable abbrev SlackIndependentStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  (∀ left right : object.Vertex,
    data.threshold < object.degree left →
    data.threshold < object.degree right →
    ¬ object.graph.Adj left right)
```

### 7. `K .tightEndpoint` (fact `f007_tightEndpoint`)

`Holds … .tightEndpoint object = TightEndpointStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/Spine.lean` lines 2665-2673:

```lean
/-- Node `[9]`: every oriented edge has an endpoint exactly at the
threshold. -/
noncomputable abbrev TightEndpointStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  (∀ dart : object.graph.Dart,
    object.degree dart.fst = data.threshold ∨
      object.degree dart.snd = data.threshold)
```

### 8. `K .cycleRankConstraint` (fact `f008_cycleRankConstraint`)

`Holds … .cycleRankConstraint object = CycleRankConstraintStatement object`; source `hypostructure/Hypostructure/Graph/Statements/Spine.lean` lines 2686-2691:

```lean
/-- `lem:cycle-rank`: for the selected graph,
`β(G) = m - n + 1` satisfies `2β(G) ≥ n + 2`.  This is the manuscript's
division-free form of `β(G) ≥ n/2 + 1`. -/
noncomputable abbrev CycleRankConstraintStatement (object : Graph.FiniteObject.{u}) : Prop :=
  object.vertexCount + 2 ≤
    2 * (object.edgeCount + 1 - object.vertexCount)
```

### 9. `K .degreeProfileFibres` (fact `f009_degreeProfileFibres`)

`Holds … .degreeProfileFibres object = DegreeProfileFibresStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/Spine.lean` lines 2709-2727:

```lean
/-- Node `[11]`, `lem:degree-profile-fibres` (tex 6088), at G's own boundaried
pieces: "if `𝐝_∂(X₁) ≠ 𝐝_∂(X₂)`, then no target-complete quotient identifies
`X₁` and `X₂`".  For every region `X ⊆ V(G)`, every admissible rank quotient of
`X`'s declared coordinates on G, and every two `T`-boundaried realizations of
its support `Z ⊆ G` (`T = ∂Z` in G): realizations in different boundary-degree
fibres are not identified. -/
noncomputable abbrev DegreeProfileFibresStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ∀ (region : Finset object.Vertex)
    (quotient : Graph.CurvatureQuotient
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object region)
    (left right : Graph.BoundaryPiece
      (Graph.Strategy.InterfaceReplacement.SupportAtom.boundary object
        quotient.support)),
    left.boundaryDegreeProfile ≠ right.boundaryDegreeProfile →
      ¬ QuotientIdentifies quotient left right
```

### 10. `K .targetCompleteContextUniversality` (fact `f010_targetCompleteContextUniversality`)

`Holds … .targetCompleteContextUniversality object = TargetCompleteContextUniversalityStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/Spine.lean` lines 2729-2769:

```lean
/-- Node `[12]`, `lem:context-universality` (tex 6106), at G's own boundaried
pieces.

* "Suppose that two coordinates are identified in a target-complete quotient of
  `X`.  Then [they] have the same target response against every `T`-boundaried
  context `Y`": for every region `X ⊆ V(G)` and every admissible rank quotient of
  its declared coordinates on G, two realizations of the quotient's support
  `Z ⊆ G` that it identifies are target-completely identified -- one
  boundary-degree fibre (node `[11]`) and the same power-of-two-cycle response
  after gluing to every `∂Z`-boundaried context.
* "Consequently any identification valid only for the actual outside context
  `G − X`, but not for all `T`-boundaried contexts, is target-defective": two
  realizations of a support `X ⊆ V(G)` with the same response at G's own outside
  context `G − X` that some `∂X`-boundaried context separates carry a concrete
  distinguishing context and are not target-completely identified. -/
noncomputable abbrev TargetCompleteContextUniversalityStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  (∀ (region : Finset object.Vertex)
    (quotient : Graph.CurvatureQuotient
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object region)
    (left right : Graph.BoundaryPiece
      (Graph.Strategy.InterfaceReplacement.SupportAtom.boundary object
        quotient.support)),
    QuotientIdentifies quotient left right →
      Graph.Response.TargetComplete Graph.BoundaryPiece.boundaryDegreeProfile
        (Graph.HasCycleWithLength data.LengthOK) left right) ∧
  (∀ (support : Finset object.Vertex)
    (left right : Graph.BoundaryPiece
      (Graph.Strategy.InterfaceReplacement.SupportAtom.boundary object support)),
    (Graph.HasCycleWithLength data.LengthOK (Graph.glue left
        (Graph.Strategy.InterfaceReplacement.SupportAtom.outside object support)) ↔
      Graph.HasCycleWithLength data.LengthOK (Graph.glue right
        (Graph.Strategy.InterfaceReplacement.SupportAtom.outside object support))) →
    ¬ Graph.Response.ContextEquivalent (Graph.HasCycleWithLength data.LengthOK)
      left right →
    Graph.Response.TargetDefect (Graph.HasCycleWithLength data.LengthOK) left right ∧
      ¬ Graph.Response.TargetComplete Graph.BoundaryPiece.boundaryDegreeProfile
        (Graph.HasCycleWithLength data.LengthOK) left right)
```

### 11. `K .replacementExclusion` (fact `f011_replacementExclusion`)

`Holds … .replacementExclusion object = ReplacementExclusionStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/Spine.lean` lines 2771-2781:

```lean
/-- Node `[13]`, `lem:replacement`: no proper atom admits a strictly smaller
boundary-signature-preserving replacement with one-way obstruction
inclusion. -/
noncomputable abbrev ReplacementExclusionStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  (∀ support : Finset object.Vertex,
    ¬ Graph.Strategy.InterfaceReplacement.ReplacementSupport
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object support)
```

### 12. `K .uncompressible` (fact `f012_uncompressible`)

`Holds … .uncompressible object = UncompressibleStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/Spine.lean` lines 2783-2797:

```lean
/-- Node `[14]`: no proper boundaried piece admits a nontrivial target-complete
compression (`cor:uncompressible`, tex 6142): no proper support of G has a
strictly smaller boundaried representative with the same boundary-degree
profile and the same target response against every context
(`CompressibleSupport`).  It is derived from node `[13]`'s one-way
`ReplacementSupport` exclusion by `replacementSupportOfCompressibleSupport`;
the two facts are distinct statements of the paper. -/
noncomputable abbrev UncompressibleStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  (∀ support : Finset object.Vertex,
    ¬ Graph.Strategy.InterfaceReplacement.CompressibleSupport
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object support)
```

### 13. `K .windowPresent` (fact `f013_windowPresent`)

`Holds … .windowPresent object = Graph.HasInducedPath object data.windowOrder`; source `hypostructure/Hypostructure/Graph/InducedPath.lean` lines 15-17:

```lean
/-- A literal induced copy of the path on `order` vertices. -/
def HasInducedPath (object : FiniteObject.{uVertex}) (order : Nat) : Prop :=
  HasInducedObstruction (SimpleGraph.pathGraph order) object
```

### 14. `K .maximalPacking` (fact `f014_maximalPacking`)

`Holds … .maximalPacking object = MaximalPackingStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/Spine.lean` lines 2799-2812:

```lean
/-- Nodes `[15]`--`[17]`: the fixed packing `P₀` is a maximum, maximal
vertex-disjoint family of induced windows, and it is nonempty
(`thm:p13free` tex 6573, "fix a maximal packing" tex 6581). -/
noncomputable abbrev MaximalPackingStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  (0 < object.windowPackingNumber data.windowOrder ∧
    let packing := canonicalWindowPacking data object;
      object.IsWindowPacking data.windowOrder packing ∧
        packing.card = object.windowPackingNumber data.windowOrder ∧
        ∀ support : Finset object.Vertex,
          object.InducesWindow data.windowOrder support →
          ∃ member ∈ packing, ¬ Disjoint support member)
```

### 15. `K .localAlgebra` (fact `f015_localAlgebra`)

`Holds … .localAlgebra object = LocalAlgebraStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/Spine.lean` lines 2841-2852:

```lean
/-- Node `[18]`: `lem:labels`'s exact legal-label census at the registered
window order (tex 6661).  The census is a statement about the window label
alphabet, not about any support of `G`, so it carries no guard over `G`'s
windows.  The adjacent `C_s` and `Ω₂` displays are definitions supplied by
`WindowCurvature.Safe` and `WindowCurvature.curvatureTwo`. -/
noncomputable abbrev LocalAlgebraStatement
    (data : Parameters)
    (_object : Graph.FiniteObject.{u}) :
    Prop :=
  (Graph.WindowCurvature.Labels data.windowOrder).card = 399 ∧
    (Graph.WindowCurvature.sizeDistribution data.windowOrder).take 7 =
      [13, 60, 122, 122, 63, 17, 2]
```

### 16. `K .everyWitnessSpectrumSplit` (fact `f016_everyWitnessSpectrumSplit`)

`Holds … .everyWitnessSpectrumSplit object = EveryWitnessSpectrumSplitStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean` lines 68-101:

```lean
/-- **The path-spectrum split at every clause-(b) witness of G** (not only the
canonical one): for every `w'` with `w'.Spec`, a positive reading `P` and a
negative reading `N` at `w'.outside`, and either (i) labels `a ≠ b`, a path
`π : a → b` of `ret_P` and an outside path `σ : b → a` meeting no other label
with `|π| + |σ|` accepted and `≥ 3`, every `ret_N` path `π'` between the same
labels having `|π'| ≠ |π|` and (unless both `π'` and `σ` are single edges)
`|π'| + |σ|` not accepted; or (ii) every accepted cycle of the positive gluing
meets three labels. -/
noncomputable def EveryWitnessSpectrumSplitStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ w' : SparseTargetDefectWitness data object, w'.Spec →
    ∃ P ∈ w'.pairSupports, ∃ N ∈ w'.pairSupports,
      Graph.HasCycleWithLength data.LengthOK
        (Graph.glue (SupportAtom.retainedPiece object w'.support P) w'.outside) ∧
      ¬ Graph.HasCycleWithLength data.LengthOK
        (Graph.glue (SupportAtom.retainedPiece object w'.support N) w'.outside) ∧
      ((∃ a b : (SupportAtom.boundary object w'.support).Vertex, a ≠ b ∧
          ∃ π : (SupportAtom.retainedPiece object w'.support P).graph.Walk
              (.inl a) (.inl b), π.IsPath ∧
          ∃ σ : w'.outside.graph.Walk (.inl b) (.inl a), σ.IsPath ∧
            (∀ d, (Sum.inl d : _ ⊕ w'.outside.Internal) ∈ σ.support → d = a ∨ d = b) ∧
            data.LengthOK (π.length + σ.length) ∧ 3 ≤ π.length + σ.length ∧
            ∀ π' : (SupportAtom.retainedPiece object w'.support N).graph.Walk
                (.inl a) (.inl b), π'.IsPath →
              π'.length ≠ π.length ∧
              ((1 < π'.length ∨ 1 < σ.length) → ¬ data.LengthOK (π'.length + σ.length))) ∨
        (∀ c : Graph.CycleCertificate
            (Graph.glue (SupportAtom.retainedPiece object w'.support P) w'.outside)
            data.LengthOK,
          ∃ a b d : (SupportAtom.boundary object w'.support).Vertex,
            a ≠ b ∧ a ≠ d ∧ b ≠ d ∧
            (Sum.inl a : Graph.GluedVertex _ w'.outside) ∈ c.walk.support ∧
            (Sum.inl b : Graph.GluedVertex _ w'.outside) ∈ c.walk.support ∧
            (Sum.inl d : Graph.GluedVertex _ w'.outside) ∈ c.walk.support))
```

### 17. `K .surplusAbove` (fact `f017_surplusAbove`)

`Holds … .surplusAbove object = SurplusAboveStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/Spine.lean` lines 2854-2861:

```lean
/-- Node `[19]`, above arm: the degree surplus exceeds the registered scale
threshold. -/
noncomputable abbrev SurplusAboveStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  (data.surplusThreshold object.vertexCount <
    object.degreeSurplus data.threshold)
```

### 18. `K .highSurplusConfiguration` (fact `f018_highSurplusConfiguration`)

`Holds … .highSurplusConfiguration object = HighSurplusConfigurationStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean` lines 40-46:

```lean
/-- **Where the surplus of G sits**: G has a vertex of degree `≥ δ + 2`, or two
distinct vertices of degree exactly `δ + 1`. -/
def HighSurplusConfigurationStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  (∃ h, data.threshold + 2 ≤ object.degree h) ∨
    ∃ h₁ h₂, h₁ ≠ h₂ ∧ object.degree h₁ = data.threshold + 1 ∧
      object.degree h₂ = data.threshold + 1
```

### 19. `K .highEndpointSwitch` (fact `f019_highEndpointSwitch`)

`Holds … .highEndpointSwitch object = HighEndpointSwitchStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean` lines 48-64:

```lean
/-- **The switch at every high/baseline edge `hc`**: a forced path from `c`,
by the same-vertex switch at `h` when `deg h ≥ δ + 2` (to a neighbour `u` of
`h` with `u ≠ c`, `u ≁ c`, in `G − {hc, hu}`), else by the two-edge switch with
a second high vertex `h₂ ≠ h` and its neighbour `u₂ ≠ c`, `u₂ ≁ c` (in
`G − {ch, u₂h₂}`). -/
def HighEndpointSwitchStatement (data : Parameters) (object : Graph.FiniteObject.{u}) :
    Prop :=
  ∀ h c : object.Vertex, data.threshold + 1 ≤ object.degree h →
    object.degree c = data.threshold → object.graph.Adj h c →
    (data.threshold + 2 ≤ object.degree h ∧ ∃ u, object.graph.Adj h u ∧ u ≠ c ∧
        ¬ object.graph.Adj c u ∧
        ∃ p : (object.graph.deleteEdges {s(h, c), s(h, u)}).Walk c u,
          p.IsPath ∧ data.LengthOK (p.length + 1)) ∨
      ∃ h₂ u₂, h₂ ≠ h ∧ data.threshold + 1 ≤ object.degree h₂ ∧
        object.graph.Adj u₂ h₂ ∧ u₂ ≠ c ∧ ¬ object.graph.Adj c u₂ ∧
        ∃ p : (object.graph.deleteEdges {s(c, h), s(u₂, h₂)}).Walk c u₂,
          p.IsPath ∧ data.LengthOK (p.length + 1)
```

### 20. `K .sparsePairExit` (fact `f020_sparsePairExit`)

`Holds … .sparsePairExit object = SparsePairExitStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SurplusPair.lean` lines 1093-1101:

```lean
/-- Node `[132]`, exit arm of `lem:sparse-pair-dependence-exit`: the
dependence of a blocked pair's response coordinates is settled by a sparse
surplus exit of `def:named-surplus-exits` rather than by a canonical blocker.
It closes the branch against node `[125]`'s survivor entry at `[133]`. -/
noncomputable abbrev SparsePairExitStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  DeclaredSparseSurplusExit data object
```

### 21. `K .sparseTargetDefectResidual` (fact `f021_sparseTargetDefectResidual`)

`Holds … .sparseTargetDefectResidual object = SparseTargetDefectResidualStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SurplusPair.lean` lines 1200-1212:

```lean
/-- Node `[125]`, the sole nonterminal named-exit payload: clause (b) of
`def:named-surplus-exits` at G's declared sparse family
(`lem:context-universality`, tex 6106-6112), at G's canonical witness
`sparseTargetDefectWitness` -- two distinct declared coordinates of G, read on
G's own piece at their canonical connected support `Z`, agree in G's actual
outside context and are separated by the witness's `∂Z`-boundaried context
`O`. -/
noncomputable abbrev SparseTargetDefectResidualStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ∃ witness, sparseTargetDefectWitness data object = some witness ∧
    witness.Spec
```

### 22. `K .sparseTargetDefectStructure` (fact `f022_sparseTargetDefectStructure`)

`Holds … .sparseTargetDefectStructure object = SparseTargetDefectStructureStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SurplusPair.lean` lines 1214-1228:

```lean
/-- Node `[20]`: the bound target-defect geometry of the two readings of
`[125]`'s identified pair on G's piece at `[125]`'s support `Z`, at `[125]`'s
separating context `O` -- all three read from the one canonical witness
`sparseTargetDefectWitness`, the witness `[125]` publishes. -/
noncomputable abbrev SparseTargetDefectStructureStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ∃ witness, sparseTargetDefectWitness data object = some witness ∧
    Graph.BoundTargetDefectGeometryAt object witness.support data.LengthOK
      (Graph.Strategy.InterfaceReplacement.SupportAtom.retainedPiece object
        witness.support (sparseDeclaredSupport data object witness.first))
      (Graph.Strategy.InterfaceReplacement.SupportAtom.retainedPiece object
        witness.support (sparseDeclaredSupport data object witness.second))
      witness.outside
```

### 23. `K .bridgeless` (fact `f023_bridgeless`)

`Holds … .bridgeless object = BridgelessStatement object`; source `hypostructure/Hypostructure/Graph/Statements/Spine.lean` lines 3348-3354:

```lean
/-- `lem:bridgeless`: the selected minimal counterexample has no bridge —
every oriented edge has a simple return after its deletion, `R_e(G) ≠ ∅`. -/
noncomputable abbrev BridgelessStatement (object : Graph.FiniteObject.{u}) : Prop :=
  -- `lem:bridgeless`: "every edge of `G` lies on a cycle; equivalently
  -- `R_e(G) ≠ ∅` for every oriented edge".  `HasReturn` is a simple path
  -- from the tail back to the head after the edge is deleted.
  (∀ contraction : Graph.EdgeContraction object, contraction.HasReturn)
```

### 24. `K .sparseUpperEnvelope` (fact `f024_sparseUpperEnvelope`)

`Holds … .sparseUpperEnvelope object = SparseUpperEnvelopeStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SurplusPair.lean` lines 1482-1497:

```lean
/-- `lem:sparse-upper-envelope`: `m + 2 ≤ (δ − 1)·n`, the manuscript's
`m ≤ 2n − 2` at its own `δ = 3`.  It is `lem:no-proper-core`'s degeneracy --
every proper subgraph misses the baseline, so the object less a vertex sitting
exactly at the baseline is `(δ − 1)`-degenerate -- spent against
`lem:deletion-critical`'s tight endpoint. -/
noncomputable abbrev SparseUpperEnvelopeStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  (object.edgeCount + 2 ≤ (data.threshold - 1) * object.vertexCount) ∧
    let packing := canonicalWindowPacking data object
    (object.windowRemainderIncidences packing).card +
        (2 * (data.windowOrder - 1) * packing.card +
          (object.crossWindowIncidences packing).card) =
      data.threshold * (data.windowOrder * packing.card) +
        object.ambientSurplus (object.windowSupport packing) data.threshold
```

### 25. `K .baselineSpineDemand` (fact `f025_baselineSpineDemand`)

`Holds … .baselineSpineDemand object = BaselineSpineDemandStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SurplusPair.lean` lines 1044-1062:

```lean
/-- Node `[129]`, `def:baseline-spine-demand` with
`lem:exact-cubic-baseline-budget`, `lem:incremental-skeleton-room` and
`def:spine-lower-bound-deficits`: the common cubic baseline `B₀(n)` the later
surplus accounting is measured against, evaluated in both directions; the room
an edge count above the cubic one buys over it; the definition itself, at
every declared target coordinate family the branch may present, with the
deficit `E_spine(n)` as this node's own output; and the ordering of the three
lower-bound packages that supply it.  Every display is committed with the
logarithms cleared. -/
noncomputable abbrev BaselineSpineDemandStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  -- Node `[129]`, exactly `def:baseline-spine-demand`, at G's canonical
  -- spine family: the `Classical.choose` of this node's own `∃`-body, so
  -- every later key speaks about the family this node exhibits.
  ∃ spine, canonicalBaselineSpineFamily data object = some spine ∧
    BaselineSpineFamilySpec data object spine.Coordinate spine.family
      spine.coordinateSupport
```

### 26. `K .freePairCountFails` (fact `f026_freePairCountFails`)

`Holds … .freePairCountFails object = FreePairCountFailsStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SurplusPairCode.lean` lines 37-42:

```lean
/-- Node `[131]`, count fails: the negation of the free-pair entropy count. -/
noncomputable abbrev FreePairCountFailsStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ¬ FreePairEntropySandwichStatement data object
```

### 27. `K .witnessReadingsNotTargetComplete` (fact `f027_witnessReadingsNotTargetComplete`)

`Holds … .witnessReadingsNotTargetComplete object = WitnessReadingsNotTargetCompleteStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 143-146:

```lean
/-- **The readings are not target-complete.** -/
noncomputable def WitnessReadingsNotTargetCompleteStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object WitnessReadingsNotTargetCompleteAtWitness
```

### 28. `K .witnessActualOutsideNegative` (fact `f028_witnessActualOutsideNegative`)

`Holds … .witnessActualOutsideNegative object = WitnessActualOutsideNegativeStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 158-161:

```lean
/-- **Neither reading has an accepted cycle at `G − Z`.** -/
noncomputable def WitnessActualOutsideNegativeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object WitnessActualOutsideNegativeAtWitness
```

### 29. `K .witnessReadingsCycleFree` (fact `f029_witnessReadingsCycleFree`)

`Holds … .witnessReadingsCycleFree object = WitnessReadingsCycleFreeStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 171-174:

```lean
/-- **Both reading pieces are cycle-free** (each embeds in G). -/
noncomputable def WitnessReadingsCycleFreeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object WitnessReadingsCycleFreeAtWitness
```

### 30. `K .witnessSupportOrderBound` (fact `f030_witnessSupportOrderBound`)

`Holds … .witnessSupportOrderBound object = WitnessSupportOrderBoundStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 183-186:

```lean
/-- **`|Z| + 1 ≤ n`.** -/
noncomputable def WitnessSupportOrderBoundStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object WitnessSupportOrderBoundAtWitness
```

### 31. `K .witnessReadingGluesNotSmallerBaseline` (fact `f031_witnessReadingGluesNotSmallerBaseline`)

`Holds … .witnessReadingGluesNotSmallerBaseline object = WitnessReadingGluesNotSmallerBaselineStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 200-204:

```lean
/-- **No reading's gluing with `G − Z` is a lexicographically smaller
baseline object** (¬K3). -/
noncomputable def WitnessReadingGluesNotSmallerBaselineStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object WitnessReadingGluesNotSmallerBaselineAtWitness
```

### 32. `K .noSuppressionChordViolation` (fact `f032_noSuppressionChordViolation`)

`Holds … .noSuppressionChordViolation object = NoSuppressionChordViolationStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 206-212:

```lean
/-- **Exit (e) is excluded at G**: no open-port suppression cycle has an
accepted lifted length `|walk| + |chords|`. -/
def NoSuppressionChordViolationStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ (tvs : Graph.TightVertexSuppression.CompatibleFamily object)
    (certificate : Graph.CycleCertificate tvs.suppressed data.LengthOK),
    ¬ data.LengthOK (certificate.walk.length + (tvs.usedChords certificate.walk).card)
```

### 33. `K .edgeSurplusIdentity` (fact `f033_edgeSurplusIdentity`)

`Holds … .edgeSurplusIdentity object = EdgeSurplusIdentityStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 77-81:

```lean
/-- **Edge–surplus identity**: `2m = δ·n + σ`. -/
def EdgeSurplusIdentityStatement (data : Parameters) (object : Graph.FiniteObject.{u}) :
    Prop :=
  2 * object.edgeCount = data.threshold * object.vertexCount +
    object.degreeSurplus data.threshold
```

### 34. `K .surplusDartIdentity` (fact `f034_surplusDartIdentity`)

`Holds … .surplusDartIdentity object = SurplusDartIdentityStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 83-89:

```lean
/-- **The dart identity**: `σ + 2δ·|H| + lowDarts = δ·n` (at `δ = 3`:
`σ + 6|H| + lowDarts = 3n`). -/
def SurplusDartIdentityStatement (data : Parameters) (object : Graph.FiniteObject.{u}) :
    Prop :=
  object.degreeSurplus data.threshold + 2 * data.threshold * sparseHighDegreeCount data object +
      sparseLowDartCount data object =
    data.threshold * object.vertexCount
```

### 35. `K .highDegreeCountBound` (fact `f035_highDegreeCountBound`)

`Holds … .highDegreeCountBound object = HighDegreeCountBoundStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 91-94:

```lean
/-- **High-degree count**: `|H| ≤ σ`. -/
def HighDegreeCountBoundStatement (data : Parameters) (object : Graph.FiniteObject.{u}) :
    Prop :=
  sparseHighDegreeCount data object ≤ object.degreeSurplus data.threshold
```

### 36. `K .packingOrderBound` (fact `f036_packingOrderBound`)

`Holds … .packingOrderBound object = PackingOrderBoundStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 108-111:

```lean
/-- **Packing ratio**: `order·ν ≤ n` (at order `13`: `13ν ≤ n`). -/
noncomputable def PackingOrderBoundStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  data.windowOrder * (canonicalWindowPacking data object).card ≤ object.vertexCount
```

### 37. `K .ceilSqrtAboveScale` (fact `f037_ceilSqrtAboveScale`)

`Holds … .ceilSqrtAboveScale object = CeilSqrtAboveScaleStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 113-116:

```lean
/-- **`C + 1 ≤ ⌈√n⌉`.** -/
def CeilSqrtAboveScaleStatement (data : Parameters) (object : Graph.FiniteObject.{u}) :
    Prop :=
  data.spineScale + 1 ≤ Core.ceilSqrt object.vertexCount
```

### 38. `K .orderAboveScaleSquare` (fact `f038_orderAboveScaleSquare`)

`Holds … .orderAboveScaleSquare object = OrderAboveScaleSquareStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 118-121:

```lean
/-- **`C(C+1) + 9 ≤ n`** (¬K4, sharpened by `σ + 8 ≤ n`). -/
def OrderAboveScaleSquareStatement (data : Parameters) (object : Graph.FiniteObject.{u}) :
    Prop :=
  data.spineScale * (data.spineScale + 1) + 9 ≤ object.vertexCount
```

### 39. `K .sixVertexExtremalEnvelope` (fact `f039_sixVertexExtremalEnvelope`)

`Holds … .sixVertexExtremalEnvelope object = SixVertexExtremalEnvelopeStatement object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 127-129:

```lean
/-- **Envelope from `ex(6, C₄) = 7`**: `m + 4 ≤ 2n`. -/
def SixVertexExtremalEnvelopeStatement (object : Graph.FiniteObject.{u}) : Prop :=
  object.edgeCount + 4 ≤ 2 * object.vertexCount
```

### 40. `K .remainderDeficiencyBelowCut` (fact `f040_remainderDeficiencyBelowCut`)

`Holds … .remainderDeficiencyBelowCut object = RemainderDeficiencyBelowCutStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 1071-1077:

```lean
/-- **`def⁺(R) ≤ e(R, W)`** at the canonical packing `P₀` (`R` its
remainder). -/
noncomputable def RemainderDeficiencyBelowCutStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  object.positiveDeficiency (object.remainderSupport (canonicalWindowPacking data object))
      data.threshold ≤
    object.boundaryIncidence (object.remainderSupport (canonicalWindowPacking data object))
```

### 41. `K .windowCutCapacity` (fact `f041_windowCutCapacity`)

`Holds … .windowCutCapacity object = WindowCutCapacityStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 1079-1087:

```lean
/-- **The window cut capacity** at `P₀`:
`e(R, W) + 2(order − 1)·p ≤ δ·order·p + σ_W`. -/
noncomputable def WindowCutCapacityStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  object.boundaryIncidence (object.remainderSupport (canonicalWindowPacking data object)) +
      2 * (data.windowOrder - 1) * (canonicalWindowPacking data object).card ≤
    data.threshold * (data.windowOrder * (canonicalWindowPacking data object).card) +
      object.ambientSurplus (object.windowSupport (canonicalWindowPacking data object))
        data.threshold
```

### 42. `K .witnessOutsideNotRealized` (fact `f042_witnessOutsideNotRealized`)

`Holds … .witnessOutsideNotRealized object = WitnessOutsideNotRealizedStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 223-226:

```lean
/-- **`O` is not realized in `G − Z`.** -/
noncomputable def WitnessOutsideNotRealizedStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object WitnessOutsideNotRealizedAtWitness
```

### 43. `K .realizedContextsNegative` (fact `f043_realizedContextsNegative`)

`Holds … .realizedContextsNegative object = RealizedContextsNegativeStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 238-241:

```lean
/-- **Both readings are negative in every context realized in `G − Z`.** -/
noncomputable def RealizedContextsNegativeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object RealizedContextsNegativeAtWitness
```

### 44. `K .negativeSubGluingNotSmallerBaseline` (fact `f044_negativeSubGluingNotSmallerBaseline`)

`Holds … .negativeSubGluingNotSmallerBaseline object = NegativeSubGluingNotSmallerBaselineStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 258-262:

```lean
/-- **No negative sub-gluing is a lexicographically smaller baseline object**:
the negative reading `N` at `O`, against every sub-context `O' ≤ O`. -/
noncomputable def NegativeSubGluingNotSmallerBaselineStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object NegativeSubGluingNotSmallerBaselineAtWitness
```

### 45. `K .cycleSubContextSeparates` (fact `f045_cycleSubContextSeparates`)

`Holds … .cycleSubContextSeparates object = CycleSubContextSeparatesStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 282-287:

```lean
/-- **The O-part of one positive cycle still separates**: a sub-context
`O' ≤ O` with `P` positive and `N` negative, every `O'`-internal vertex of
`O'`-degree at most `2`, and `glue N O'` not a baseline object. -/
noncomputable def CycleSubContextSeparatesStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object CycleSubContextSeparatesAtWitness
```

### 46. `K .pathSpectrumSplit` (fact `f046_pathSpectrumSplit`)

`Holds … .pathSpectrumSplit object = PathSpectrumSplitStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 338-346:

```lean
/-- **The path-length spectrum split** at the witness: for the positive
reading `P` and the negative reading `N` at `O`, either (i) labels `a ≠ b` of
`∂Z`, a path `π : a → b` of `ret_P` and an `O`-path `σ : b → a` meeting no
other label with `|π| + |σ| = 2^k` (`k ≥ 2`), such that every `a → b` path
`π'` of `ret_N` has `|π'| ≠ |π|` and `|π'| + |σ| ≠ 2^j` for every `j ≥ 2`; or
(ii) every accepted cycle of `glue ret_P O` meets three distinct labels. -/
noncomputable def PathSpectrumSplitStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object PathSpectrumSplitAtWitness
```

### 47. `K .admissibleQuotientsLabelInjective` (fact `f047_admissibleQuotientsLabelInjective`)

`Holds … .admissibleQuotientsLabelInjective object = AdmissibleQuotientsLabelInjectiveStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 353-360:

```lean
/-- **Every admissible quotient of G is label-injective** on its family. -/
def AdmissibleQuotientsLabelInjectiveStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ {Coordinate : Type u} (family : Finset Coordinate)
    (cs : Coordinate → Finset object.Vertex)
    (q : Graph.DeclaredQuotient (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object family cs),
    Set.InjOn q.label ↑family
```

### 48. `K .singleBoundaryShape` (fact `f048_singleBoundaryShape`)

`Holds … .singleBoundaryShape object = SingleBoundaryShapeStatement object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 369-379:

```lean
/-- **The one-boundary shape**: every support `S` with a single boundary vertex
`b`, a second vertex and a vertex outside has `b` with exactly two neighbours
in `S` and two outside (`deg b = 4`, a 2+2 cut vertex). -/
def SingleBoundaryShapeStatement (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ (S : Finset object.Vertex) (b : object.Vertex),
    SupportAtom.cutBoundary object S = {b} →
    ∀ z ∈ S, z ≠ b → (∃ x, x ∉ S) →
      (by classical exact (object.vertexFinset.filter fun y =>
          object.graph.Adj b y ∧ y ∈ S).card) = 2 ∧
      (by classical exact (object.vertexFinset.filter fun y =>
          object.graph.Adj b y ∧ y ∉ S).card) = 2
```

### 49. `K .neighbourhoodPairCount` (fact `f049_neighbourhoodPairCount`)

`Holds … .neighbourhoodPairCount object = NeighbourhoodPairCountStatement object`; source `hypostructure/Hypostructure/Graph/Statements/CycleCounting.lean` lines 30-35:

```lean
/-- **Neighbourhood pairs of G**: for every vertex `h`, `G[N(h)]` is a
matching, `N(h)` has at least `C(d_h, 2) − ⌊d_h/2⌋` nonadjacent pairs, and
every `x ∈ N(h)` has at least `d_h − 2` nonadjacent partners in `N(h)`. -/
noncomputable abbrev NeighbourhoodPairCountStatement (object : Graph.FiniteObject.{u}) :
    Prop :=
  Graph.CycleCounting.NeighbourhoodPairs object
```

### 50. `K .starCycleConstraint` (fact `f050_starCycleConstraint`)

`Holds … .starCycleConstraint object = StarCycleConstraintStatement object`; source `hypostructure/Hypostructure/Graph/Statements/CycleCounting.lean` lines 37-42:

```lean
/-- **Star constraint at G**: for every vertex `h`, distinct neighbours `y, z`
and paths `P : x → y`, `Q : x → z` of `G − h` meeting only at `x`,
`|P| + |Q| + 2 ≠ 2^k` (`k ≥ 2`); in particular two such paths never both have
length `2^j − 1`. -/
abbrev StarCycleConstraintStatement (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.CycleCounting.StarConstraint object
```

### 51. `K .meetingCycleConstraint` (fact `f051_meetingCycleConstraint`)

`Holds … .meetingCycleConstraint object = MeetingCycleConstraintStatement object`; source `hypostructure/Hypostructure/Graph/Statements/CycleCounting.lean` lines 44-49:

```lean
/-- **Meeting constraint at G**: for every vertex `h`, distinct neighbours
`y, z` and paths `P : x → y`, `Q : x → z` of `G − h`, the paths meet at a
vertex `t` reached along them by `P₁`, `Q₁` with
`|P| + |Q| + 2 ≠ 2^k + |P₁| + |Q₁|` for every `k ≥ 2`. -/
abbrev MeetingCycleConstraintStatement (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.CycleCounting.MeetingConstraint object
```

### 52. `K .highDegreePairSum` (fact `f052_highDegreePairSum`)

`Holds … .highDegreePairSum object = HighDegreePairSumStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/CycleCounting.lean` lines 51-57:

```lean
/-- **Pair sums at the high vertices of G** `H = {d ≠ δ}`:
`σ = Σ_H (d_h − 3)`, `5σ ≤ Σ_H C(d_h, 2)`,
`σ² + 5σ|H| + 6|H|² ≤ 2|H| Σ_H C(d_h, 2)`, `2 Σ_H C(d_h, 2) ≤ 16σ²`, and
`σ = 0` or some `h ∈ H` has `σ ≤ |H|(d_h − 3)`. -/
noncomputable abbrev HighDegreePairSumStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.CycleCounting.HighPairSum object data.threshold
```

### 53. `K .vertexDeletionComponents` (fact `f053_vertexDeletionComponents`)

`Holds … .vertexDeletionComponents object = VertexDeletionComponentsStatement object`; source `hypostructure/Hypostructure/Graph/Statements/CycleCounting.lean` lines 59-64:

```lean
/-- **Vertex deletions of G**: for every vertex `h`, `G − h` is connected, or
`d_h` is even, `d_h = 2·#blocks(h)`, and every component of `G − h` meeting
`N(h)` holds exactly two neighbours of `h`. -/
noncomputable abbrev VertexDeletionComponentsStatement (object : Graph.FiniteObject.{u}) :
    Prop :=
  Graph.CycleCounting.VertexDeletionShape object
```

### 54. `K .cyclesThroughVertex` (fact `f054_cyclesThroughVertex`)

`Holds … .cyclesThroughVertex object = CyclesThroughVertexStatement object`; source `hypostructure/Hypostructure/Graph/Statements/CycleCounting.lean` lines 66-69:

```lean
/-- **Cycles through every vertex of G**: `C(d_h, 2) ≤ #cycles(h)` when
`G − h` is connected; otherwise `2·#pairs(h) = d_h` and `d_h/2 ≤ #cycles(h)`. -/
noncomputable abbrev CyclesThroughVertexStatement (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.CycleCounting.CyclesThroughVertex object
```

### 55. `K .cutVertexBlockPaths` (fact `f055_cutVertexBlockPaths`)

`Holds … .cutVertexBlockPaths object = CutVertexBlockPathsStatement object`; source `hypostructure/Hypostructure/Graph/Statements/CycleCounting.lean` lines 71-78:

```lean
/-- **Block paths at the cut vertices of G**: for every vertex `h` with
`G − h` disconnected and every neighbour `a`, the block `{a, b}` of `a`; the
`a → b` paths of `G − h` have `|r| + 2 ≠ 2^k`; every return of `ha` ends by
`bh`; an `a → b` path avoiding `ha`, `hb` avoids `h` (residue `3 mod 4` at
length `2^j − 1`); a path to another block splits at `h` (residue `1 mod 4`,
opposite parities, at length `2^j − 1`). -/
noncomputable abbrev CutVertexBlockPathsStatement (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.CycleCounting.BlockPaths object
```

### 56. `K .cycleDoubleCount` (fact `f056_cycleDoubleCount`)

`Holds … .cycleDoubleCount object = CycleDoubleCountStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/CycleCounting.lean` lines 80-85:

```lean
/-- **Double count of the cycles of G at its high vertices** `H = {d ≠ δ}`:
`2 Σ_H #cycles(h) ≤ n · #cycles(G)`, `2 Σ_H L_h ≤ n · #cycles(G)` with
`L_h = C(d_h, 2)` (`G − h` connected) or `d_h / 2`, and `#cycles(G) ≤ 2^m`. -/
noncomputable abbrev CycleDoubleCountStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.CycleCounting.CycleDoubleCount object data.threshold
```

### 57. `K .threeRouteFan` (fact `f057_threeRouteFan`)

`Holds … .threeRouteFan object = ThreeRouteFanStatement object`; source `hypostructure/Hypostructure/Graph/Statements/LocalRigidity.lean` lines 27-32:

```lean
/-- **The length-3 fan at G**: at every vertex `h`, two paths `a p₁ p₂ b`,
`a q₁ q₂ c` of length `3` of `G − h` from a neighbour `a` of `h` to distinct
neighbours `b ≠ c` of `h` have `p₁ = q₁`, `p₂ ≠ q₂`, `p₂ ≠ c`, `q₂ ≠ b`; two
such paths with distinct first steps would close the 8-cycle `h b p₂ p₁ a q₁ q₂ c`. -/
abbrev ThreeRouteFanStatement (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.LocalRigidity.ThreeRouteFan object
```

### 58. `K .threeRouteChain` (fact `f058_threeRouteChain`)

`Holds … .threeRouteChain object = ThreeRouteChainStatement object`; source `hypostructure/Hypostructure/Graph/Statements/LocalRigidity.lean` lines 34-38:

```lean
/-- **The chain `3, 3, 3` at G**: at every vertex `h`, paths `a p₁ p₂ b`,
`b r₁ r₂ c`, `c q₁ q₂ d` of length `3` of `G − h` between neighbours of `h`
(`a ≠ c`, `b ≠ d`) have `r₁ = p₂` and `r₂ = q₁`. -/
abbrev ThreeRouteChainStatement (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.LocalRigidity.ThreeRouteChain object
```

### 59. `K .windowPositionStubs` (fact `f059_windowPositionStubs`)

`Holds … .windowPositionStubs object = WindowPositionStubsStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/LocalRigidity.lean` lines 52-58:

```lean
/-- **Window positions of `P₀`**: every window of `P₀` has a placement; at
every placement an interior vertex carries `d − 2` external neighbours (exactly
one when cubic) and an end vertex `d − 1`. -/
noncomputable abbrev WindowPositionStubsStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.LocalRigidity.WindowPositionStubs object data.windowOrder
    (canonicalWindowPacking data object)
```

### 60. `K .windowAttachmentGap` (fact `f060_windowAttachmentGap`)

`Holds … .windowAttachmentGap object = WindowAttachmentGapStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/LocalRigidity.lean` lines 40-50:

```lean
/-- **The cross-edge gap at G and at the windows of `P₀`**: two
vertex-disjoint placed paths of G joined at `(i, j)` and `(i', j')` have
`|i − i'| + 2 + |j − j'|` not accepted; at every placed window of `P₀`, every
outside vertex carries a legal label (in `Labels 13`), two adjacent outside
vertices carry `C₁`-safe labels, two distinct windows obey the same gap rule,
and no two windows form a ladder. -/
noncomputable abbrev WindowAttachmentGapStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.LocalRigidity.CrossGap object ∧
    Graph.LocalRigidity.WindowAttachmentRules object data.windowOrder
      (canonicalWindowPacking data object)
```

### 61. `K .positiveSupportBoundaryTwo` (fact `f061_positiveSupportBoundaryTwo`)

`Holds … .positiveSupportBoundaryTwo object = PositiveSupportBoundaryTwoStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 391-394:

```lean
/-- **`2 ≤ |∂Z ∩ X⁺|`** for one declared support `X⁺ ∈ {A, B}`. -/
noncomputable def PositiveSupportBoundaryTwoStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object PositiveSupportBoundaryTwoAtWitness
```

### 62. `K .supportCutEdgesTwo` (fact `f062_supportCutEdgesTwo`)

`Holds … .supportCutEdgesTwo object = SupportCutEdgesTwoStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 410-413:

```lean
/-- **`2 ≤ e(∂Z, V ∖ Z)`.** -/
noncomputable def SupportCutEdgesTwoStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object SupportCutEdgesTwoAtWitness
```

### 63. `K .boundaryLowInsideVertex` (fact `f063_boundaryLowInsideVertex`)

`Holds … .boundaryLowInsideVertex object = BoundaryLowInsideVertexStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 422-425:

```lean
/-- **A boundary vertex with at most two neighbours in `Z`.** -/
noncomputable def BoundaryLowInsideVertexStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object BoundaryLowInsideVertexAtWitness
```

### 64. `K .outsideLowVertex` (fact `f064_outsideLowVertex`)

`Holds … .outsideLowVertex object = OutsideLowVertexStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 437-441:

```lean
/-- **An outside vertex with at most two outside neighbours and a neighbour in
`Z`.** -/
noncomputable def OutsideLowVertexStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object OutsideLowVertexAtWitness
```

### 65. `K .twoBoundaryLowOutsideSide` (fact `f065_twoBoundaryLowOutsideSide`)

`Holds … .twoBoundaryLowOutsideSide object = TwoBoundaryLowOutsideSideStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 453-457:

```lean
/-- **`∂Z = {a, b}` with an interior vertex: one terminal has at most two
neighbours in `T' = (V ∖ Z) ∪ {a, b}`.** -/
noncomputable def TwoBoundaryLowOutsideSideStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object TwoBoundaryLowOutsideSideAtWitness
```

### 66. `K .twoBoundarySupportClosure` (fact `f066_twoBoundarySupportClosure`)

`Holds … .twoBoundarySupportClosure object = TwoBoundarySupportClosureStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 470-475:

```lean
/-- **2-sum closure on the `Z` side**: if `a ≁ b` and both have two
neighbours in `Z`, then `G[Z]` has an `a`–`b` path `P` with `|P| + 1`
accepted. -/
noncomputable def TwoBoundarySupportClosureStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object TwoBoundarySupportClosureAtWitness
```

### 67. `K .twoBoundaryOutsideClosure` (fact `f067_twoBoundaryOutsideClosure`)

`Holds … .twoBoundaryOutsideClosure object = TwoBoundaryOutsideClosureStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 491-494:

```lean
/-- **2-sum closure on the outside side** (interior arm). -/
noncomputable def TwoBoundaryOutsideClosureStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object TwoBoundaryOutsideClosureAtWitness
```

### 68. `K .twoBoundaryNoTargetSum` (fact `f068_twoBoundaryNoTargetSum`)

`Holds … .twoBoundaryNoTargetSum object = TwoBoundaryNoTargetSumStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 507-512:

```lean
/-- **The length-set constraint at `∂Z = {a, b}`**: an `a`–`b` path in `Z`
and a `b`–`a` path in `T'` (not both single edges) never sum to an accepted
length. -/
noncomputable def TwoBoundaryNoTargetSumStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object TwoBoundaryNoTargetSumAtWitness
```

### 69. `K .outsideOrBoundaryLarge` (fact `f069_outsideOrBoundaryLarge`)

`Holds … .outsideOrBoundaryLarge object = OutsideOrBoundaryLargeStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 528-531:

```lean
/-- **`2 ≤ |W|` or `3 ≤ |∂Z|`.** -/
noncomputable def OutsideOrBoundaryLargeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object OutsideOrBoundaryLargeAtWitness
```

### 70. `K .droppedEdgeTightDeficit` (fact `f070_droppedEdgeTightDeficit`)

`Holds … .droppedEdgeTightDeficit object = DroppedEdgeTightDeficitStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 552-556:

```lean
/-- **Every G-edge a reading drops at `G − Z` has an endpoint below the
baseline there.** -/
noncomputable def DroppedEdgeTightDeficitStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object DroppedEdgeTightDeficitAtWitness
```

### 71. `K .notBothReadingsWhole` (fact `f071_notBothReadingsWhole`)

`Holds … .notBothReadingsWhole object = NotBothReadingsWholeStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 566-569:

```lean
/-- **At most one reading is whole**: `¬ (Z ⊆ A ∧ Z ⊆ B)`. -/
noncomputable def NotBothReadingsWholeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object NotBothReadingsWholeAtWitness
```

### 72. `K .firstWholeOrientation` (fact `f072_firstWholeOrientation`)

`Holds … .firstWholeOrientation object = FirstWholeOrientationStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 639-642:

```lean
/-- **Whole case `Z ⊆ A`: `A` positive and `B` negative at `O`.** -/
noncomputable def FirstWholeOrientationStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object FirstWholeOrientationAtWitness
```

### 73. `K .firstWholeDeficitNonempty` (fact `f073_firstWholeDeficitNonempty`)

`Holds … .firstWholeDeficitNonempty object = FirstWholeDeficitNonemptyStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 651-654:

```lean
/-- **Whole case `Z ⊆ A`: `1 ≤ |Z ∖ B|`.** -/
noncomputable def FirstWholeDeficitNonemptyStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object FirstWholeDeficitNonemptyAtWitness
```

### 74. `K .firstWholeDeficitStructure` (fact `f074_firstWholeDeficitStructure`)

`Holds … .firstWholeDeficitStructure object = FirstWholeDeficitStructureStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 663-667:

```lean
/-- **Whole case `Z ⊆ A`: the deficit set `Z ∖ B` is internal, has no
`∂Z`-neighbour, and is isolated in every gluing of `ret_B`.** -/
noncomputable def FirstWholeDeficitStructureStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object FirstWholeDeficitStructureAtWitness
```

### 75. `K .firstWholeDeficitSum` (fact `f075_firstWholeDeficitSum`)

`Holds … .firstWholeDeficitSum object = FirstWholeDeficitSumStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 676-680:

```lean
/-- **Whole case `Z ⊆ A`: `δ·|Z ∖ B| ≤ Σ (δ − deg)` in every gluing of
`ret_B`.** -/
noncomputable def FirstWholeDeficitSumStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object FirstWholeDeficitSumAtWitness
```

### 76. `K .secondWholeOrientation` (fact `f076_secondWholeOrientation`)

`Holds … .secondWholeOrientation object = SecondWholeOrientationStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 689-692:

```lean
/-- **Whole case `Z ⊆ B`: `B` positive and `A` negative at `O`.** -/
noncomputable def SecondWholeOrientationStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object SecondWholeOrientationAtWitness
```

### 77. `K .secondWholeDeficitNonempty` (fact `f077_secondWholeDeficitNonempty`)

`Holds … .secondWholeDeficitNonempty object = SecondWholeDeficitNonemptyStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 701-704:

```lean
/-- **Whole case `Z ⊆ B`: `1 ≤ |Z ∖ A|`.** -/
noncomputable def SecondWholeDeficitNonemptyStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object SecondWholeDeficitNonemptyAtWitness
```

### 78. `K .secondWholeDeficitStructure` (fact `f078_secondWholeDeficitStructure`)

`Holds … .secondWholeDeficitStructure object = SecondWholeDeficitStructureStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 713-717:

```lean
/-- **Whole case `Z ⊆ B`: the deficit set `Z ∖ A` is internal, has no
`∂Z`-neighbour, and is isolated in every gluing of `ret_A`.** -/
noncomputable def SecondWholeDeficitStructureStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object SecondWholeDeficitStructureAtWitness
```

### 79. `K .secondWholeDeficitSum` (fact `f079_secondWholeDeficitSum`)

`Holds … .secondWholeDeficitSum object = SecondWholeDeficitSumStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 726-730:

```lean
/-- **Whole case `Z ⊆ B`: `δ·|Z ∖ A| ≤ Σ (δ − deg)` in every gluing of
`ret_A`.** -/
noncomputable def SecondWholeDeficitSumStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object SecondWholeDeficitSumAtWitness
```

### 80. `K .deletedSupportReduction` (fact `f080_deletedSupportReduction`)

`Holds … .deletedSupportReduction object = DeletedSupportReductionStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 762-764:

```lean
noncomputable def DeletedSupportReductionStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object DeletedSupportReductionAtWitness
```

### 81. `K .deletedSupportDeficientVertex` (fact `f081_deletedSupportDeficientVertex`)

`Holds … .deletedSupportDeficientVertex object = DeletedSupportDeficientVertexStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 784-786:

```lean
noncomputable def DeletedSupportDeficientVertexStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object DeletedSupportDeficientVertexAtWitness
```

### 82. `K .deletedSupportDeficitSums` (fact `f082_deletedSupportDeficitSums`)

`Holds … .deletedSupportDeficitSums object = DeletedSupportDeficitSumsStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 812-814:

```lean
noncomputable def DeletedSupportDeficitSumsStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object DeletedSupportDeficitSumsAtWitness
```

### 83. `K .deletedSupportEdgeRestoration` (fact `f083_deletedSupportEdgeRestoration`)

`Holds … .deletedSupportEdgeRestoration object = DeletedSupportEdgeRestorationStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 835-837:

```lean
noncomputable def DeletedSupportEdgeRestorationStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object DeletedSupportEdgeRestorationAtWitness
```

### 84. `K .deletedSupportEdgeSetRestoration` (fact `f084_deletedSupportEdgeSetRestoration`)

`Holds … .deletedSupportEdgeSetRestoration object = DeletedSupportEdgeSetRestorationStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 858-860:

```lean
noncomputable def DeletedSupportEdgeSetRestorationStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object DeletedSupportEdgeSetRestorationAtWitness
```

### 85. `K .firstKeepsAllNotWhole` (fact `f085_firstKeepsAllNotWhole`)

`Holds … .firstKeepsAllNotWhole object = FirstKeepsAllNotWholeStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 875-879:

```lean
/-- **Keeps-all for `A` with `Z ⊄ A`**: `Z ⊄ B`, and both readings' profiles
differ from the whole piece's. -/
noncomputable def FirstKeepsAllNotWholeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object FirstKeepsAllNotWholeAtWitness
```

### 86. `K .secondKeepsAllNotWhole` (fact `f086_secondKeepsAllNotWhole`)

`Holds … .secondKeepsAllNotWhole object = SecondKeepsAllNotWholeStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 894-898:

```lean
/-- **Keeps-all for `B` with `Z ⊄ B`**: `Z ⊄ A`, and both readings' profiles
differ from the whole piece's. -/
noncomputable def SecondKeepsAllNotWholeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object SecondKeepsAllNotWholeAtWitness
```

### 87. `K .highDegreePositive` (fact `f087_highDegreePositive`)

`Holds … .highDegreePositive object = HighDegreePositiveStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 96-99:

```lean
/-- **At least one high-degree vertex**: `1 ≤ |H|`. -/
def HighDegreePositiveStatement (data : Parameters) (object : Graph.FiniteObject.{u}) :
    Prop :=
  1 ≤ sparseHighDegreeCount data object
```

### 88. `K .highDegreeSurplusCapacity` (fact `f088_highDegreeSurplusCapacity`)

`Holds … .highDegreeSurplusCapacity object = HighDegreeSurplusCapacityStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 101-106:

```lean
/-- **The surplus fits on the high vertices**: `σ ≤ |H|·(n − |H| − δ)` (every
high vertex has all its neighbours among the `n − |H|` baseline vertices). -/
def HighDegreeSurplusCapacityStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  object.degreeSurplus data.threshold ≤ sparseHighDegreeCount data object *
    (object.vertexCount - sparseHighDegreeCount data object - data.threshold)
```

### 89. `K .pairArmExcluded` (fact `f089_pairArmExcluded`)

`Holds … .pairArmExcluded object = PairArmExcludedStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 907-912:

```lean
/-- **The pair arm does not occur**: `¬ (∂Z = Z = {a, b})` (equal profiles
on a two-vertex all-boundary support force equal readings, against the
separation at `O`). -/
noncomputable def PairArmExcludedStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object PairArmExcludedAtWitness
```

### 90. `K .twoBoundaryForcesArmOne` (fact `f090_twoBoundaryForcesArmOne`)

`Holds … .twoBoundaryForcesArmOne object = TwoBoundaryForcesArmOneStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 929-934:

```lean
/-- **`|∂Z| = 2` forces arm (i) of the spectrum split**, `∂Z = {a, b}` inside
one declared support, an interior vertex of `Z`, and `{a, b}` separating the
interior from `V ∖ Z`. -/
noncomputable def TwoBoundaryForcesArmOneStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object TwoBoundaryForcesArmOneAtWitness
```

### 91. `K .armOneForcedPath` (fact `f091_armOneForcedPath`)

`Holds … .armOneForcedPath object = ArmOneForcedPathStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 949-954:

```lean
/-- **Arm (i) gives a forced path in `G[Z]`**: a simple `a–b` path `p` of
`G[Z]` between two boundary vertices with `|p| + 1 ≤ |Z|` and `|p| + s = 2^k`
(`k ≥ 2`, `s ≥ 1`, `(|p| + s) % 4 = 0`). -/
noncomputable def ArmOneForcedPathStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object ArmOneForcedPathAtWitness
```

### 92. `K .twoBoundaryForcedPathCross` (fact `f092_twoBoundaryForcedPathCross`)

`Holds … .twoBoundaryForcedPathCross object = TwoBoundaryForcedPathCrossStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 974-981:

```lean
/-- **`|∂Z| = 2`, the K1 × K2 cross constraint**: `∂Z = {a, b}` carries the
forced path `p ⊆ G[Z]` (`|p| + s = 2^k`); no simple `b → a` path `q` in
`T' = (V ∖ Z) ∪ {a, b}` (not both single edges) has `|p| + |q|` accepted; and
if `a ≁ b` with both terminals of `T'`-degree `≥ 2`, the outside closure `q`
exists with `|q| + 1` accepted and `|p| + |q|` not accepted. -/
noncomputable def TwoBoundaryForcedPathCrossStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object TwoBoundaryForcedPathCrossAtWitness
```

### 93. `K .supportSteinerMinimal` (fact `f093_supportSteinerMinimal`)

`Holds … .supportSteinerMinimal object = SupportSteinerMinimalStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 993-996:

```lean
/-- **`Z` is a minimum connected set containing `A ∪ B`.** -/
noncomputable def SupportSteinerMinimalStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object SupportSteinerMinimalAtWitness
```

### 94. `K .steinerVerticesCut` (fact `f094_steinerVerticesCut`)

`Holds … .steinerVerticesCut object = SteinerVerticesCutStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 1007-1010:

```lean
/-- **Every vertex of `Z ∖ (A ∪ B)` is a cut vertex of `G[Z]`.** -/
noncomputable def SteinerVerticesCutStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object SteinerVerticesCutAtWitness
```

### 95. `K .wholeSupportEqual` (fact `f095_wholeSupportEqual`)

`Holds … .wholeSupportEqual object = WholeSupportEqualStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 1024-1027:

```lean
/-- **The whole case pins `Z`**: `Z ⊆ A ⇒ Z = A ∧ B ⊆ A`, and `Z ⊆ B ⇒ Z = B ∧ A ⊆ B`. -/
noncomputable def WholeSupportEqualStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object WholeSupportEqualAtWitness
```

### 96. `K .wholeDeficitBoundaryCount` (fact `f096_wholeDeficitBoundaryCount`)

`Holds … .wholeDeficitBoundaryCount object = WholeDeficitBoundaryCountStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 1042-1045:

```lean
/-- **Whole case: `|S| + |∂Z| ≤ |Z|`** (`S = Z ∖ B` resp. `Z ∖ A`). -/
noncomputable def WholeDeficitBoundaryCountStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object WholeDeficitBoundaryCountAtWitness
```

### 97. `K .wholeCutEdgeSurplusBound` (fact `f097_wholeCutEdgeSurplusBound`)

`Holds … .wholeCutEdgeSurplusBound object = WholeCutEdgeSurplusBoundStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 1062-1065:

```lean
/-- **Whole case: `e(S, T) ≤ D_T + σ`**, with `D_T = Σ_T (3 − deg_{G−S})`. -/
noncomputable def WholeCutEdgeSurplusBoundStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object WholeCutEdgeSurplusBoundAtWitness
```

### 98. `K .canonicalCapacityExplicit` (fact `f098_canonicalCapacityExplicit`)

`Holds … .canonicalCapacityExplicit object = CanonicalCapacityExplicitStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 1114-1123:

```lean
/-- **G's canonical capacity presentation is the explicit one**: the recorded
blocker activation of G's active family on the node-`[19]` packing. -/
noncomputable def CanonicalCapacityExplicitStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ (active : Graph.ActiveSurplusDemands
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object data.threshold)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (connected : object.graph.Connected),
    canonicalCapacity data object = some (explicitCapacity active avoids connected)
```

### 99. `K .primitiveCarrierCount` (fact `f099_primitiveCarrierCount`)

`Holds … .primitiveCarrierCount object = PrimitiveCarrierCountStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 1125-1129:

```lean
/-- **`|𝔘_sp(G)| = 4n + 2σ`.** -/
def PrimitiveCarrierCountStatement (data : Parameters) (object : Graph.FiniteObject.{u}) :
    Prop :=
  (object.primitiveCarrier data.threshold).card =
    4 * object.vertexCount + 2 * object.degreeSurplus data.threshold
```

### 100. `K .canonicalTokenCount` (fact `f100_canonicalTokenCount`)

`Holds … .canonicalTokenCount object = CanonicalTokenCountStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 1131-1139:

```lean
/-- **The exact token count at the canonical presentation**:
`|𝔗_cap| + 2(order − 1)·ν = 4n + 3σ + 3·order·ν` (at order `13`:
`|𝔗_cap| = 4n + 3σ + 15ν`). -/
noncomputable def CanonicalTokenCountStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtCanonicalCapacityCounts data object fun c _ =>
    c.tokens.card + 2 * (data.windowOrder - 1) * (canonicalWindowPacking data object).card =
      4 * object.vertexCount + 3 * object.degreeSurplus data.threshold +
        3 * (data.windowOrder * (canonicalWindowPacking data object).card)
```

### 101. `K .canonicalBlockedFreePartition` (fact `f101_canonicalBlockedFreePartition`)

`Holds … .canonicalBlockedFreePartition object = CanonicalBlockedFreePartitionStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 1141-1146:

```lean
/-- **`|Π_blk| + |Π_free| = C(σ, 2)`** at the canonical ledger. -/
noncomputable def CanonicalBlockedFreePartitionStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtCanonicalCapacityCounts data object fun c L =>
    L.presented.blocked.card + freeCount data object c =
      (object.degreeSurplus data.threshold).choose 2
```

### 102. `K .canonicalLedgerDeficit` (fact `f102_canonicalLedgerDeficit`)

`Holds … .canonicalLedgerDeficit object = CanonicalLedgerDeficitStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 1148-1159:

```lean
/-- **The deficit at the canonical ledger** (G2): with `c = ⌈√n⌉`,
`c²K + 2M₀(8n + σ − |𝔗|) ≤ 2(|Π_free| − B) + 2(|Π_blk| − M₀|𝔗|)`. -/
noncomputable def CanonicalLedgerDeficitStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtCanonicalCapacityCounts data object fun c L =>
    (Core.ceilSqrt object.vertexCount : ℤ) ^ 2 * pairDeficitCoefficient data +
        2 * (homogeneousTokenCap data.routingLabelBound : ℤ) *
          ((8 * object.vertexCount + object.degreeSurplus data.threshold : ℕ) -
            (c.tokens.card : ℤ)) ≤
      2 * ((freeCount data object c : ℤ) - (certificationBudget data object : ℤ)) +
        2 * ((L.presented.blocked.card : ℤ) -
          (homogeneousTokenCap data.routingLabelBound : ℤ) * c.tokens.card)
```

### 103. `K .pairCountDeficit` (fact `f103_pairCountDeficit`)

`Holds … .pairCountDeficit object = PairCountDeficitStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 1161-1167:

```lean
/-- **The pair-count deficit** (G3): `c²K + 2M₀(8n + σ) ≤ 2(C(σ, 2) − B)`. -/
def PairCountDeficitStatement (data : Parameters) (object : Graph.FiniteObject.{u}) : Prop :=
  (Core.ceilSqrt object.vertexCount : ℤ) ^ 2 * pairDeficitCoefficient data +
      2 * (homogeneousTokenCap data.routingLabelBound : ℤ) *
        ((8 * object.vertexCount + object.degreeSurplus data.threshold : ℕ) : ℤ) ≤
    2 * (((object.degreeSurplus data.threshold).choose 2 : ℕ) -
      (certificationBudget data object : ℤ))
```

### 104. `K .canonicalCertificationCriterion` (fact `f104_canonicalCertificationCriterion`)

`Holds … .canonicalCertificationCriterion object = CanonicalCertificationCriterionStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 1169-1175:

```lean
/-- **The certification criterion at the canonical presentation**: its
canonical certified ledger exists iff `|Π_free| ≤ B`. -/
noncomputable def CanonicalCertificationCriterionStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtCanonicalCapacityCounts data object fun c _ =>
    ((canonicalCertifiedCapacityDataAt data object c).isSome ↔
      freeCount data object c ≤ certificationBudget data object)
```

### 105. `K .canonicalOverloadOfFits` (fact `f105_canonicalOverloadOfFits`)

`Holds … .canonicalOverloadOfFits object = CanonicalOverloadOfFitsStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 1200-1221:

```lean
/-- **If the free side fits `B`, the blocked side is overloaded**:
`c²K + 2M₀(8n + σ − |𝔗|) ≤ 2(|Π_blk| − M₀|𝔗|)`, and some token has load
`> M₀` and carries an `L_geom` role-homogeneous matching or star. -/
noncomputable def CanonicalOverloadOfFitsStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtCanonicalCapacityCounts data object fun c L =>
    freeCount data object c ≤ certificationBudget data object →
      (Core.ceilSqrt object.vertexCount : ℤ) ^ 2 * pairDeficitCoefficient data +
          2 * (homogeneousTokenCap data.routingLabelBound : ℤ) *
            ((8 * object.vertexCount + object.degreeSurplus data.threshold : ℕ) -
              (c.tokens.card : ℤ)) ≤
        2 * ((L.presented.blocked.card : ℤ) -
          (homogeneousTokenCap data.routingLabelBound : ℤ) * c.tokens.card) ∧
      ∃ token ∈ L.presented.tokens,
        homogeneousTokenCap data.routingLabelBound < L.presented.load token ∧
        ∃ role : Role,
          (∃ pattern ⊆ L.presented.roleFibre token role,
              PatternFamily.IsMatching pattern ∧
                geometricPatternBound data.routingLabelBound ≤ pattern.card) ∨
          (∃ centre, ∃ pattern ⊆ L.presented.roleFibre token role,
              PatternFamily.IsStar pattern centre ∧
                geometricPatternBound data.routingLabelBound ≤ pattern.card)
```

### 106. `K .canonicalFreeExcessOfCapped` (fact `f106_canonicalFreeExcessOfCapped`)

`Holds … .canonicalFreeExcessOfCapped object = CanonicalFreeExcessOfCappedStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 1223-1233:

```lean
/-- **If every token carries load `≤ M₀`, the free side exceeds `B`**:
`c²K + 2M₀(8n + σ − |𝔗|) ≤ 2(|Π_free| − B)`. -/
noncomputable def CanonicalFreeExcessOfCappedStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtCanonicalCapacityCounts data object fun c L =>
    (∀ t ∈ L.presented.tokens, L.presented.load t ≤ homogeneousTokenCap data.routingLabelBound) →
      (Core.ceilSqrt object.vertexCount : ℤ) ^ 2 * pairDeficitCoefficient data +
          2 * (homogeneousTokenCap data.routingLabelBound : ℤ) *
            ((8 * object.vertexCount + object.degreeSurplus data.threshold : ℕ) -
              (c.tokens.card : ℤ)) ≤
        2 * ((freeCount data object c : ℤ) - (certificationBudget data object : ℤ))
```

### 107. `K .paperBudgetBound` (fact `f107_paperBudgetBound`)

`Holds … .paperBudgetBound object = PaperBudgetBoundStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 1184-1189:

```lean
/-- **The paper's budget at the canonical spine family fits the certification
budget**: `E_paper ≤ B`. -/
noncomputable def PaperBudgetBoundStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ spine, canonicalBaselineSpineFamily data object = some spine ∧
    paperBudget data object spine.family.card ≤ certificationBudget data object
```

### 108. `K .paperBudgetCertifies` (fact `f108_paperBudgetCertifies`)

`Holds … .paperBudgetCertifies object = PaperBudgetCertifiesStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 1191-1198:

```lean
/-- **`|Π_free| ≤ E_paper` certifies**: at the canonical spine family and
presentation, `|Π_free| ≤ E_paper` makes the canonical certified ledger exist. -/
noncomputable def PaperBudgetCertifiesStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ spine c, canonicalBaselineSpineFamily data object = some spine ∧
    canonicalCapacity data object = some c ∧
    (freeCount data object c ≤ paperBudget data object spine.family.card →
      (canonicalCertifiedCapacityDataAt data object c).isSome)
```

### 109. `K .pairCodeConfiguration` (fact `f109_pairCodeConfiguration`)

`Holds … .pairCodeConfiguration object = PairCodeConfigurationStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 1235-1255:

```lean
/-- **Where G sits in the pair-code chain**: either the `[137]`→`[143]`
configuration holds at the canonical objects (blocked pair, `[137]` count,
canonical pattern, overload, caps fail), or G's canonical first failure exists
and yields the `[182]` residual, or the target defect of the canonical return
system's obstruction coordinates, or that obstruction's handoff together with
the Type B fan entry `[65]`. -/
noncomputable def PairCodeConfigurationStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  (DependentPairFamilyStatement data object ∧
      BlockedPairEntropySandwichStatement data object ∧
      HomogeneousBottleneckPatternSchema data object ∧
      SparsePressureOverloadSchema data object ∧
      ¬ HomogeneousCapsHoldStatement data object) ∨
    (PairOverlapFirstFailureStatement data object ∧
      (PairConditionalFactorizationResidualStatement data object ∨
        (∃ returns, canonicalPairDemandReturns data object = some returns ∧
          Graph.ResidualTargetDefect (Graph.HasCycleWithLength data.LengthOK) object
            returns.obstructionCoordinates pairCoordinateSupport) ∨
        ((∃ returns, canonicalPairDemandReturns data object = some returns ∧
            PairObstructionHandoff data object returns) ∧
          TypeBFanEntryStatement data object)))
```

### 110. `K .twoSwitchForcedPath` (fact `f110_twoSwitchForcedPath`)

`Holds … .twoSwitchForcedPath object = TwoSwitchForcedPathStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SwitchForcedPaths.lean` lines 34-45:

```lean
/-- **The two-edge switch of G forces a path.**  For edges `u₁v₁`, `u₂v₂` of G
with `u₁, v₁, u₂, v₂` distinct, `u₁ ≁ u₂` and `deg v₁, deg v₂ ≥ δ + 1`, the
graph `G − {u₁v₁, u₂v₂}` has a simple `u₁`–`u₂` path `p` with `|p| + 1`
accepted. -/
def TwoSwitchForcedPathStatement (data : Parameters) (object : Graph.FiniteObject.{u}) :
    Prop :=
  ∀ ⦃u₁ v₁ u₂ v₂ : object.Vertex⦄,
    object.graph.Adj u₁ v₁ → object.graph.Adj u₂ v₂ →
    u₁ ≠ u₂ → u₁ ≠ v₂ → v₁ ≠ u₂ → v₁ ≠ v₂ → ¬ object.graph.Adj u₁ u₂ →
    data.threshold + 1 ≤ object.degree v₁ → data.threshold + 1 ≤ object.degree v₂ →
    ∃ p : (object.graph.deleteEdges {s(u₁, v₁), s(u₂, v₂)}).Walk u₁ u₂,
      p.IsPath ∧ data.LengthOK (p.length + 1)
```

### 111. `K .crossSwitchFamily` (fact `f111_crossSwitchFamily`)

`Holds … .crossSwitchFamily object = CrossSwitchFamilyStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SwitchForcedPaths.lean` lines 78-95:

```lean
/-- **The cross-vertex switch family of G.**  Fix an edge `u₁v` of G and a
vertex `h' ≠ v`, both `v` and `h'` of degree at least `δ + 1`.  Every
neighbour `u` of `h'` with `u ≁ u₁` (four distinct endpoints) has a forced
simple path `u₁ → u` in `G − {u₁v, uh'}` with accepted closing length; and two
simple paths of G from `u₁` into two distinct neighbours of `h'`, both of
length `2^j − 1` (`j ≥ 1`), are never simultaneously `h'`-free and internally
disjoint. -/
def CrossSwitchFamilyStatement (data : Parameters) (object : Graph.FiniteObject.{u}) :
    Prop :=
  ∀ ⦃u₁ v h' : object.Vertex⦄, object.graph.Adj u₁ v → v ≠ h' →
    data.threshold + 1 ≤ object.degree v → data.threshold + 1 ≤ object.degree h' →
    (∀ u, object.graph.Adj u h' → u ≠ u₁ → u ≠ v → u₁ ≠ h' → ¬ object.graph.Adj u₁ u →
      ∃ p : (object.graph.deleteEdges {s(u₁, v), s(u, h')}).Walk u₁ u,
        p.IsPath ∧ data.LengthOK (p.length + 1)) ∧
    (∀ u u' j (P : object.graph.Walk u₁ u) (Q : object.graph.Walk u₁ u'),
      object.graph.Adj u h' → object.graph.Adj u' h' → u ≠ u' → 1 ≤ j →
      P.IsPath → Q.IsPath → P.length + 1 = 2 ^ j → Q.length + 1 = 2 ^ j →
      ¬ (h' ∉ P.support ∧ h' ∉ Q.support ∧ ∀ w ∈ P.support, w ∈ Q.support → w = u₁))
```

### 112. `K .highCentreSplitForced` (fact `f112_highCentreSplitForced`)

`Holds … .highCentreSplitForced object = HighCentreSplitForcedStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SwitchForcedPaths.lean` lines 65-76:

```lean
/-- **The vertex split of G at every high centre forces a cycle.**  At every
vertex `h` of G of degree above `δ`, the graph `G ⊔ M_h` (`M_h` the
non-adjacent pairs of `N(h)`) has an accepted cycle that avoids `h` and uses
an edge of `M_h` absent from G. -/
def HighCentreSplitForcedStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ h : object.Vertex, data.threshold < object.degree h →
    ∃ (v : object.Vertex)
      (c : (object.graph ⊔ Graph.SwitchForcedPaths.antiPairs object h).Walk v v),
      c.IsCycle ∧ data.LengthOK c.length ∧ h ∉ c.support ∧
        ∃ e ∈ c.edges, e ∈ (Graph.SwitchForcedPaths.antiPairs object h).edgeSet ∧
          e ∉ object.graph.edgeSet
```

### 113. `K .sameVertexSwitchForcedPath` (fact `f113_sameVertexSwitchForcedPath`)

`Holds … .sameVertexSwitchForcedPath object = SameVertexSwitchForcedPathStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SwitchForcedPaths.lean` lines 47-63:

```lean
/-- **The same-vertex switch of G forces a path, and splits it exactly.**  For
non-adjacent neighbours `u₁ ≠ u₂` of a vertex `h` of G with
`deg h ≥ δ + 2`, the graph `G − {hu₁, hu₂}` has a simple `u₁`–`u₂` path `p`
with `|p| + 1` accepted; and either `p` avoids `h` and the closing cycle
`p + u₂h + hu₁` of length `|p| + 2` is not accepted, or `p` passes through `h`
and splits into two returns of `hu₁`, `hu₂` of lengths `ℓ₁ + ℓ₂ = |p|` with
neither `ℓᵢ + 1` accepted. -/
def SameVertexSwitchForcedPathStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ ⦃h u₁ u₂ : object.Vertex⦄,
    object.graph.Adj h u₁ → object.graph.Adj h u₂ → u₁ ≠ u₂ →
    ¬ object.graph.Adj u₁ u₂ → data.threshold + 2 ≤ object.degree h →
    ∃ p : (object.graph.deleteEdges {s(h, u₁), s(h, u₂)}).Walk u₁ u₂,
      p.IsPath ∧ data.LengthOK (p.length + 1) ∧
        ((h ∉ p.support ∧ ¬ data.LengthOK (p.length + 2)) ∨
          ∃ ℓ₁ ℓ₂, ℓ₁ + ℓ₂ = p.length ∧ ¬ data.LengthOK (ℓ₁ + 1) ∧
            ¬ data.LengthOK (ℓ₂ + 1))
```

### 114. `K .specWitnessStructure` (fact `f114_specWitnessStructure`)

`Holds … .specWitnessStructure object = SpecWitnessStructureStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitResidual.lean` lines 1260-1286:

```lean
/-- **Every target-defect witness of G has the `[20a]` structure** (not only the
canonical one): for every `w` with `w.Spec`, `O` is not realized in `G − Z`;
the bound target-defect geometry; `2 ≤ |∂Z|` and `Z ⊊ V(G)`;
`2 ≤ |∂Z ∩ X|` for a declared support `X`; the pair arm is excluded; the
whole case `Z ⊆ A` orients the readings and leaves `Z ∖ B ≠ ∅`; and `Z` is a
minimum connected set containing `A ∪ B`. -/
noncomputable def SpecWitnessStructureStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ w : SparseTargetDefectWitness data object, w.Spec →
    IsEmpty (Graph.GluedReadings.RealizedIn w.outside) ∧
    Graph.BoundTargetDefectGeometryAt object w.support data.LengthOK
      (w.reading w.first) (w.reading w.second) w.outside ∧
    2 ≤ (SupportAtom.cutBoundary object w.support).card ∧
    (∃ vertex, vertex ∉ w.support) ∧
    (2 ≤ (by classical exact (SupportAtom.cutBoundary object w.support ∩
        sparseDeclaredSupport data object w.first).card) ∨
      2 ≤ (by classical exact (SupportAtom.cutBoundary object w.support ∩
        sparseDeclaredSupport data object w.second).card)) ∧
    (¬ ∃ a b, SupportAtom.cutBoundary object w.support = {a, b} ∧ w.support = {a, b}) ∧
    (w.support ⊆ sparseDeclaredSupport data object w.first →
      (Graph.HasCycleWithLength data.LengthOK (Graph.glue (w.reading w.first) w.outside) ∧
        ¬ Graph.HasCycleWithLength data.LengthOK (Graph.glue (w.reading w.second) w.outside)) ∧
      (∃ s ∈ w.support, s ∉ sparseDeclaredSupport data object w.second)) ∧
    (∀ Y : Finset object.Vertex,
      (by classical exact sparseDeclaredSupport data object w.first ∪
        sparseDeclaredSupport data object w.second) ⊆ Y →
      Graph.SupportComponents.Connected.ConnectedOn object Y → w.support.card ≤ Y.card)
```

### 115. `K .witnessReadingCounts` (fact `f115_witnessReadingCounts`)

`Holds … .witnessReadingCounts object = WitnessReadingCountsStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean` lines 203-208:

```lean
/-- **Reading counts and transfer at the canonical witness**: `c_A(b) = c_B(b)`
at every `b ∈ ∂Z`; a boundary vertex of `A` with an `A`-neighbour lies in `B`,
and conversely. -/
noncomputable def WitnessReadingCountsStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object WitnessReadingCountsAtWitness
```

### 116. `K .witnessActiveLabels` (fact `f116_witnessActiveLabels`)

`Holds … .witnessActiveLabels object = WitnessActiveLabelsStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean` lines 225-231:

```lean
/-- **At least two active labels at the canonical witness**: the set of labels
`l ∈ ∂Z` with `c_A(l) > 0` has at least two elements; two distinct ones have
`1 ≤ c_A(l) = c_B(l) ≤ deg(l) − 1` and lie in `A ∩ B`; in particular both `A`
and `B` meet `∂Z` (no reading is boundary-free). -/
noncomputable def WitnessActiveLabelsStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object WitnessActiveLabelsAtWitness
```

### 117. `K .boundaryPartition` (fact `f117_boundaryPartition`)

`Holds … .boundaryPartition object = BoundaryPartitionStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean` lines 264-270:

```lean
/-- **The exact partition of `∂Z`** at the canonical witness: every boundary
vertex is (i) active (`c_A = c_B ≥ 1`, in `A ∩ B`), or (ii) a zero-count vertex
of `A ∪ B`, isolated in `G[A]` resp. `G[B]`, or (iii) a Steiner vertex
(`∉ A ∪ B`), a cut vertex of `G[Z]`. -/
noncomputable def BoundaryPartitionStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object BoundaryPartitionAtWitness
```

### 118. `K .positiveCyclePrivateEdge` (fact `f118_positiveCyclePrivateEdge`)

`Holds … .positiveCyclePrivateEdge object = PositiveCyclePrivateEdgeStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean` lines 280-287:

```lean
/-- **Every positive cycle uses a private edge, so `ret_P ⊄ ret_N`**: at the
canonical witness, with `P` the positive and `N` the negative reading at `O`,
every accepted cycle of `glue ret_P O` traverses a private edge `xy` of `P`
(`x, y ∈ P`, `y ∉ N`, `y` internal to `Z`), and `ret_P` has an edge that is not
an edge of `ret_N`. -/
noncomputable def PositiveCyclePrivateEdgeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object PositiveCyclePrivateEdgeAtWitness
```

### 119. `K .wholeCycleMeetsDeficit` (fact `f119_wholeCycleMeetsDeficit`)

`Holds … .wholeCycleMeetsDeficit object = WholeCycleMeetsDeficitStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean` lines 294-298:

```lean
/-- **Whole case: every positive cycle passes through `Z ∖ Y`**, at both
orientations (`Z ⊆ A` and `Z ⊆ B`). -/
noncomputable def WholeCycleMeetsDeficitStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object WholeCycleMeetsDeficitAtWitness
```

### 120. `K .wholePrivateEdges` (fact `f120_wholePrivateEdges`)

`Holds … .wholePrivateEdges object = WholePrivateEdgesStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean` lines 305-309:

```lean
/-- **Whole case: the private edges of `X` are exactly the edges at `Z ∖ Y`**,
at both orientations. -/
noncomputable def WholePrivateEdgesStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object WholePrivateEdgesAtWitness
```

### 121. `K .spectrumArmOneRefined` (fact `f121_spectrumArmOneRefined`)

`Holds … .spectrumArmOneRefined object = SpectrumArmOneRefinedStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean` lines 320-329:

```lean
/-- **Arm (i) of the spectrum split, refined, at the canonical witness**: with
`P` positive and `N` negative at `O`, either the refined arm (i)
(`ArmOneRefined`: active labels in `A ∩ B`, a private edge on `π`, `|π| ≥ 2`;
at `a ~ b`: `|σ| ≥ 2`, `|π| + 1`, `|σ| + 1` not accepted, the four residue
classes and the outside closures; no outside `b → a` path completes `π`; and
`|σ| = 1` makes the single-edge context `a — b` separating), or arm (ii); and
`|∂Z| = 2` forces the refined arm (i). -/
noncomputable def SpectrumArmOneRefinedStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object SpectrumArmOneRefinedAtWitness
```

### 122. `K .separatingEdgeContextWitness` (fact `f122_separatingEdgeContextWitness`)

`Holds … .separatingEdgeContextWitness object = SeparatingEdgeContextWitnessStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean` lines 353-359:

```lean
/-- **A separating single-edge context is never at an adjacent pair, and is a
clause-(b) witness**: at the canonical witness, if the single-edge context
`a — b` (`a ≠ b` in `∂Z`) separates the readings, then `a ≁ b` in G and
`w_ab = (A, B, Z, a — b)` satisfies the clause-(b) specification. -/
noncomputable def SeparatingEdgeContextWitnessStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object SeparatingEdgeContextWitnessAtWitness
```

### 123. `K .twoBoundaryAllActive` (fact `f123_twoBoundaryAllActive`)

`Holds … .twoBoundaryAllActive object = TwoBoundaryAllActiveStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean` lines 241-244:

```lean
/-- **`|∂Z| = 2`: the whole boundary is active and lies in `A ∩ B`.** -/
noncomputable def TwoBoundaryAllActiveStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object TwoBoundaryAllActiveAtWitness
```

### 124. `K .privateEdgeSwap` (fact `f124_privateEdgeSwap`)

`Holds … .privateEdgeSwap object = PrivateEdgeSwapStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean` lines 414-420:

```lean
/-- **The swap object of the canonical witness**: the positive reading `P` has
a private edge `xy` (`x, y ∈ P ⊆ Z`, `y ∉ N`, `y` internal to `Z`), and
`G − Priv(P)` (the edges of `G[P]` not in `G[N]` removed) fails the baseline at
a tight endpoint of a private edge. -/
noncomputable def PrivateEdgeSwapStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object PrivateEdgeSwapAtWitness
```

### 125. `K .cubicLabelOutsidePath` (fact `f125_cubicLabelOutsidePath`)

`Holds … .cubicLabelOutsidePath object = CubicLabelOutsidePathStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean` lines 463-468:

```lean
/-- **Every baseline label has an outside return**: at the canonical witness,
every `a ∈ ∂Z` of degree `δ` is joined to another `b' ∈ ∂Z` by a path `τ` of
length `≥ 2` with interior in `V ∖ Z`. -/
noncomputable def CubicLabelOutsidePathStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object CubicLabelOutsidePathAtWitness
```

### 126. `K .separatingEdgeContextSpectrum` (fact `f126_separatingEdgeContextSpectrum`)

`Holds … .separatingEdgeContextSpectrum object = SeparatingEdgeContextSpectrumStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean` lines 391-399:

```lean
/-- **The spectrum split at a separating single-edge context**: at the
canonical witness, if `a — b` separates the readings, then `a ≁ b`, one reading
`P` is positive and the other `N` negative at `a — b`, and either a reading path
`π : a' → b'` has `|π| + 1` accepted while every `ret_N` path `π'` between the
same labels has `|π'| ≠ |π|` and (if `|π'| ≥ 2`) `|π'| + 1` not accepted, or
every accepted cycle of the positive gluing meets three labels. -/
noncomputable def SeparatingEdgeContextSpectrumStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object SeparatingEdgeContextSpectrumAtWitness
```

### 127. `K .privateEdgeSwitch` (fact `f127_privateEdgeSwitch`)

`Holds … .privateEdgeSwitch object = PrivateEdgeSwitchStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean` lines 445-453:

```lean
/-- **The private edge of the positive reading and its switch**: at the
canonical witness there is a private edge `xy` of `P` (`x, y ∈ P ⊆ Z`, `y ∉ N`,
`y` internal) with either both ends at the baseline, both losing the edge in
the swap object (`deg ≤ δ − 1` at `x` and at `y`), or a high end `h`
(`deg ≥ δ + 1`) and a baseline end `c`, with the forced path from `c` of the
switch at `hc`. -/
noncomputable def PrivateEdgeSwitchStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object PrivateEdgeSwitchAtWitness
```

### 128. `K .twoBoundaryOutsideBoth` (fact `f128_twoBoundaryOutsideBoth`)

`Holds … .twoBoundaryOutsideBoth object = TwoBoundaryOutsideBothStatement data.toParameters object`; source `hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean` lines 481-486:

```lean
/-- **`|∂Z| = 2` with a baseline label: outside paths in both orientations**:
if `∂Z = {x, y}` and one of `x, y` has degree `δ`, then G has paths `x → y`
and `y → x` of length `≥ 2` with interior in `V ∖ Z`. -/
noncomputable def TwoBoundaryOutsideBothStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  AtSparseTargetDefectWitness data object TwoBoundaryOutsideBothAtWitness
```

