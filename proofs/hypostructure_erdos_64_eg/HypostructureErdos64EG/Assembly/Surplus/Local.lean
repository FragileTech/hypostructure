import Hypostructure.Graph.Strategy.SpineRows.OpenPortSuppression
import Hypostructure.Graph.Strategy.SpineRows.OpenPortSuppressionSafe
import Hypostructure.Graph.Strategy.SpineRows.SingleOpenPortSuppressionWitness
import Hypostructure.Graph.Strategy.SpineRows.SuppressedFamilyCriticalCycle
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.SameTokenBottleneckRouting
import Hypostructure.Graph.Strategy.SpineRows.SameTokenPair
import Hypostructure.Graph.Strategy.SpineRows.SameTokenSwap
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.SameTokenTypeBFanEntry
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.HomogeneousCapsClose
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.FibrePressure
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.PairFailureOverlap
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.PairOverlapSystem
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.PairCorrelation
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.PairPowerOfTwoCycle
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.PairSystemOutcome
import Hypostructure.Graph.Strategy.SurplusRows
import HypostructureErdos64EG.Assembly.Surplus.Boundary

/-!
# Assembly: Surplus / Local

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 2048 in
/-- Nodes `[126]`--`[128]`, sparse-surplus activation on node `[125]`'s
unchanged literal survivor residual. -/
-- EG-NODE [126] sparse envelope: \(m\le2n-2\), \(\sigma=n-6-2\lambda\)
-- EG-NODE [127] excess-port extraction: \(\mathcal A=\mathcal P_{\rm exc}\), \(|\mathcal A|=\sigma(G)\)
-- EG-NODE [128] canonical activation: returns \(R_p\); open \(Q_p\); triangular response
noncomputable def selectedSparseSurplusActivation
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .sparseSurplusSurvivor,
        K .paperBudgetBound, K .paperBudgetCertifies, K .pairCodeConfiguration,
        K .extFreeEmpty, K .extLoadSum, K .extOverload, K .extOverloadedToken, K .newLoadBound, K .freeSideHubs, K .freeSideCount, K .canonicalTokenCount,
        K .canonicalBlockedFreePartition, K .canonicalLedgerDeficit,
        K .pairCountDeficit, K .canonicalCertificationCriterion,
        K .canonicalOverloadOfFits, K .canonicalFreeExcessOfCapped,
        K .pairArmAPattern, K .pairArmARoleAlphabet, K .freeSideStructure, K .separatedPairs, K .windowChargeKinds, K .responseObstructionTargetDefect, K .canonicalCapacityExplicit, K .highDegreePositive,
        K .highDegreeSurplusCapacity, K .orderAboveScaleSquare,
        K .sixVertexExtremalEnvelope, K .pairArmB, K .highEndpointSwitch, K .highSurplusConfiguration, K .scalePressure, K .highSurplusOrder, K .edgeSurplusIdentity,
        K .ceilSqrtAboveScale, K .baselineSpineDemand, K .sparseUpperEnvelope,
        K .surplusAbove, K .localAlgebra, K .maximalPacking, K .windowPresent, K .uncompressible,
        K .admissibleQuotientsLabelInjective, K .replacementExclusion,
        K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint,
        K .cycleDoubleCount, K .surplusDartIdentity, K .highDegreeCountBound, K .highCentreSplitForced, K .portEndDegree, K .hubLinkStructure, K .hubClassCounts, K .slotRelation, K .closedClasses, K .hubTwoHopLinks, K .slotLinear, K .hubWindowBudget, K .windowHubBounds, K .cubicNeighbourSupply, K .hubCountBound, K .lowEdgeParity, K .bigHubBound, K .bigHubVShapes, K .highSurplusBound, K .hubLengthThreePairs, K .tightEndpoint, K .slackIndependent,
        K .vertexDeletionComponents, K .cyclesThroughVertex,
        K .cutVertexBlockPaths, K .singleBoundaryShape, K .densityExcess, K .remainderSlack, K .noProperBaseline, K .sameVertexSwitchForcedPath, K .returnAvoidance,
        K .primitiveCarrierCount, K .remainderPathBounds, K .windowFreeGeometry, K .inducedPathAttachment, K .windowPositionStubs, K .windowAttachmentGap, K .remainderDeficiencyBelowCut, K .windowCutCapacity,
        K .highDegreePairSum, K .twoSwitchForcedPath, K .crossSwitchFamily, K .minDegreeBaseline, K .bridgeless, K .threeRouteFan, K .threeRouteChain, K .neighbourhoodPairCount, K .starCycleConstraint,
        K .meetingCycleConstraint, K .cubicBaseline, K .everyWitnessSpectrumSplit, K .packingOrderBound,
        K .noSuppressionChordViolation, K .specWitnessStructure, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .suppressedFamilyCriticalCycle,
        K .singleOpenPortSuppressionWitness, K .openPortSuppressionSafe,
        K .openPortSuppression, K .sparseSurplusSurvivor,
        K .paperBudgetBound, K .paperBudgetCertifies, K .pairCodeConfiguration,
        K .extFreeEmpty, K .extLoadSum, K .extOverload, K .extOverloadedToken, K .newLoadBound, K .freeSideHubs, K .freeSideCount, K .canonicalTokenCount,
        K .canonicalBlockedFreePartition, K .canonicalLedgerDeficit,
        K .pairCountDeficit, K .canonicalCertificationCriterion,
        K .canonicalOverloadOfFits, K .canonicalFreeExcessOfCapped,
        K .pairArmAPattern, K .pairArmARoleAlphabet, K .freeSideStructure, K .separatedPairs, K .windowChargeKinds, K .responseObstructionTargetDefect, K .canonicalCapacityExplicit, K .highDegreePositive,
        K .highDegreeSurplusCapacity, K .orderAboveScaleSquare,
        K .sixVertexExtremalEnvelope, K .pairArmB, K .highEndpointSwitch, K .highSurplusConfiguration, K .scalePressure, K .highSurplusOrder, K .edgeSurplusIdentity,
        K .ceilSqrtAboveScale, K .baselineSpineDemand, K .sparseUpperEnvelope,
        K .surplusAbove, K .localAlgebra, K .maximalPacking, K .windowPresent, K .uncompressible,
          K .admissibleQuotientsLabelInjective, K .replacementExclusion,
          K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint,
          K .cycleDoubleCount, K .surplusDartIdentity, K .highDegreeCountBound, K .highCentreSplitForced, K .portEndDegree, K .hubLinkStructure, K .hubClassCounts, K .slotRelation, K .closedClasses, K .hubTwoHopLinks, K .slotLinear, K .hubWindowBudget, K .windowHubBounds, K .cubicNeighbourSupply, K .hubCountBound, K .lowEdgeParity, K .bigHubBound, K .bigHubVShapes, K .highSurplusBound, K .hubLengthThreePairs, K .tightEndpoint,
        K .slackIndependent, K .vertexDeletionComponents, K .cyclesThroughVertex,
        K .cutVertexBlockPaths, K .singleBoundaryShape, K .densityExcess, K .remainderSlack, K .noProperBaseline, K .sameVertexSwitchForcedPath, K .returnAvoidance,
          K .primitiveCarrierCount, K .remainderPathBounds, K .windowFreeGeometry, K .inducedPathAttachment, K .windowPositionStubs, K .windowAttachmentGap, K .remainderDeficiencyBelowCut, K .windowCutCapacity,
          K .highDegreePairSum, K .twoSwitchForcedPath, K .crossSwitchFamily, K .minDegreeBaseline, K .bridgeless, K .threeRouteFan, K .threeRouteChain, K .neighbourhoodPairCount, K .starCycleConstraint,
        K .meetingCycleConstraint, K .cubicBaseline, K .everyWitnessSpectrumSplit, K .packingOrderBound,
          K .noSuppressionChordViolation, K .specWitnessStructure, K .selection] := by
  -- The presentation identities the surplus rows spend are read from the one
  -- presentation-law fact `K .cubicBaseline`, published at the entry.
  let suppressionDefined :=
    (openPortSuppressionRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by key_fresh)
  let suppressionSafe :=
    (openPortSuppressionSafeRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      suppressionDefined (by
        key_fresh)
  let singleSuppressionWitnessed :=
    (singleOpenPortSuppressionWitnessRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      suppressionSafe (by
        key_fresh)
  let familyCritical :=
    (suppressedFamilyCriticalCycleRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      singleSuppressionWitnessed (by
        key_fresh)
  let h2 :=
    (sparseSlackSurplusRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      familyCritical (by
        key_fresh)
  let h3 :=
    (activeSurplusFamilyRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run h2 (by
        key_fresh)
  let h4 :=
    (sparsePortActivationRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run h3 (by
        key_fresh)
  exact
    (activeSurplusDemandsRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run h4 (by
        key_fresh)

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 2048 in
/-- Nodes `[178]`--`[180]`, the pair-code chain entered from the free side of `[131]` (node `[130]`'s independent arm): on
any ledger that carries the node-`[178]` first failure
`K .pairOverlapFirstFailure` and every key of that entry arm.  Each paper test is a `Decision`; each
uncovered implication is retained at the open node `[182]`, each covered Type B
alternative returns with its own `[179]`/`[180]` source key, and the
full-modulus arithmetic arm closes against node `[1]` through the framework. -/
-- EG-NODE [178] pair-code unrealized residual: conditional factorization gives a minimal connected pair overlap obstruction
-- EG-NODE [179] covered uncrossing: target/sparse-exit/Type B, or a graph-realized serial demand system
-- EG-NODE [180] covered increment split: periodic sparse-exit/Type B, or full-modulus arithmetic gives an actual power-of-two cycle
-- EG-NODE [182] OPEN: the exact [178], [179], or [180] implication not supplied by the manuscript
noncomputable def selectedPairCodeChainIndependent
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .pairOverlapFirstFailure) known]
    [FactKeys.Has (K .noProperBaseline) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
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
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .minDegreeBaseline) known]
    (systemFresh : K .pairOverlapSystem ∉ known := by key_fresh)
    (correlationFresh : K .pairCorrelation ∉ known := by key_fresh)
    (coverageFresh : K .pairCoverage ∉ known := by key_fresh)
    (fullModulusFresh : K .pairFullModulus ∉ known := by key_fresh)
    (uncrossingFresh : K .pairUncrossing ∉ known := by key_fresh)
    (factorizationFresh : K .pairConditionalFactorization ∉ known := by key_fresh)
    (factorizationFailsFresh : K .pairFactorizationFails ∉ known := by key_fresh)
    (residualFresh : K .pairConditionalFactorizationResidual ∉ known := by key_fresh)
    (overlapFresh : K .pairFailureOverlap ∉ known := by key_fresh)
    (returnsFresh : K .pairDemandReturns ∉ known := by key_fresh)
    (realizabilityFresh : K .pairSystemRealizability ∉ known := by key_fresh)
    (realizabilityFailsFresh : K .pairRealizabilityFails ∉ known := by key_fresh)
    (systemEarlyFresh : K .pairSystemEarlyOutcome ∉ known := by key_fresh)
    (systemNoEarlyFresh : K .pairSystemNoEarlyOutcome ∉ known := by key_fresh)
    (serialFresh : K .pairSerialDemandSystem ∉ known := by key_fresh)
    (fanEntryFresh : K .typeBFanEntry ∉ known := by key_fresh)
    (handoffSupportFresh : K .pairHandoffSupport ∉ known := by key_fresh)
    (handoffChargeFresh : K .pairHandoffCharge ∉ known := by key_fresh)
    (handoffNetChargeFresh : K .pairHandoffNetCharge ∉ known := by key_fresh)
    (pairHandoffHubChargeFresh : K .pairHandoffHubCharge ∉ known := by key_fresh)
    (pairHandoffBoundaryTypeFresh : K .pairHandoffBoundaryType ∉ known := by key_fresh)
    (pairHandoffCriticalCoordinateFresh : K .pairHandoffCriticalCoordinate ∉ known := by key_fresh)
    (pairObstructionDescentFresh : K .pairObstructionDescent ∉ known := by key_fresh)
    (pairHandoffHubForcesFresh : K .pairHandoffHubForces ∉ known := by key_fresh)
    (pairHandoffDemandEndsFresh : K .pairHandoffDemandEnds ∉ known := by key_fresh)
    (pairHandoffHubBalanceFresh : K .pairHandoffHubBalance ∉ known := by key_fresh)
    (pairHandoffFibreAtGFresh : K .pairHandoffFibreAtG ∉ known := by key_fresh)
    (incrementFresh : K .pairIncrementCovered ∉ known := by key_fresh)
    (incrementFailsFresh : K .pairIncrementFails ∉ known := by key_fresh)
    (incrementEarlyFresh : K .pairIncrementEarlyOutcome ∉ known := by key_fresh)
    (incrementNoEarlyFresh : K .pairIncrementNoEarlyOutcome ∉ known := by key_fresh)
    (arithmeticFresh : K .pairSerialArithmetic ∉ known := by key_fresh)
    (cycleFresh : K .pairPowerOfTwoCycle ∉ known := by key_fresh)
    (closedFresh : closed ∉ known := by key_fresh)
    [FactKeys.Has (K .activeSurplusDemands) known]
    [FactKeys.Has (K .activeSurplusFamily) known]
    [FactKeys.Has (K .baselineSpineDemand) known]
    [FactKeys.Has (K .cycleRankConstraint) known]
    [FactKeys.Has (K .degreeProfileFibres) known]
    [FactKeys.Has (K .exactCubicBaselineBudget) known]
    [FactKeys.Has (K .incrementalSkeletonRoom) known]
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
    [FactKeys.Has (K .maximalPacking) known]
    [FactKeys.Has (K .mixedSparseSpineDependence) known]
    [FactKeys.Has (K .openPortSuppression) known]
    [FactKeys.Has (K .openPortSuppressionSafe) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .returnAvoidance) known]
    [FactKeys.Has (K .singleOpenPortSuppressionWitness) known]
    [FactKeys.Has (K .skeletonDominates) known]
    [FactKeys.Has (K .slackIndependent) known]
    [FactKeys.Has (K .sparsePortActivation) known]
    [FactKeys.Has (K .sparseSlackSurplus) known]
    [FactKeys.Has (K .sparseUpperEnvelope) known]
    [FactKeys.Has (K .suppressedFamilyCriticalCycle) known]
    [FactKeys.Has (K .targetCompleteContextUniversality) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .windowPresent) known]
    [FactKeys.Has (K .independentPairFamily) known]
    [FactKeys.Has (K .freePairCountFails) known]
    [FactKeys.Has (K .freePairCodeUnrealized) known] :
    StrictSurplusBoundaryResult selected := by
  let overlapSystem :=
    (pairOverlapSystemRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by key_fresh)
  let correlated :=
    (pairCorrelationRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      overlapSystem (by key_fresh)
  match pairConditionalFactorizationDichotomy (data := spineData)
      correlated (by key_fresh) (by key_fresh) with
  | .right failsHistory =>
      let residualHistory :=
        (pairFactorizationResidualRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run failsHistory (by key_fresh)
      exact Or.inr (Or.inr
        (Or.inl (pairConditionalFactorizationReturn_freeFactorizationFails residualHistory)))
  | .left factorizationHistory =>
      let overlapFailure :=
        (pairFailureOverlapRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run factorizationHistory (by key_fresh)
      let demandReturns :=
        (pairDemandReturnsRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run overlapFailure (by key_fresh)
      let coverage :=
        (pairCoverageRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          demandReturns (by key_fresh)
      let uncrossing :=
        (pairUncrossingRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          coverage (by key_fresh)
      match pairSystemRealizabilityDichotomy (data := spineData)
          uncrossing (by key_fresh) (by key_fresh) with
      | .right failsHistory =>
          let residualHistory :=
            (pairRealizabilityResidualRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run failsHistory (by key_fresh)
          exact Or.inr (Or.inr
            (Or.inr (Or.inl
              (pairConditionalFactorizationReturn_freeRealizabilityFails residualHistory))))
      | .left coveredHistory =>
          match pairSystemOutcomeDichotomy (data := spineData)
              coveredHistory (by key_fresh) (by key_fresh) with
          | .left earlyHistory =>
              let typeBHistory :=
                (pairSystemEarlyTypeBEntryRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run earlyHistory (by key_fresh)
              let factsHistory :=
                (pairHandoffFactsRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run typeBHistory (by key_fresh)
              exact Or.inr (Or.inl (Or.inl
                (pairTypeBIndependentSystemReturn
                  ((pairHandoffBalanceRow (BranchState := BranchState)
                    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                    (presentation := erdosReceiverLoadProfile)
                    (data := spineData)).run factsHistory (by key_fresh)))))
          | .right noEarlyHistory =>
              let serialHistory :=
                (pairSerialDemandSystemRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run noEarlyHistory (by key_fresh)
              let fullModulus :=
                (pairFullModulusRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  serialHistory (by key_fresh)
              match pairIncrementCoveredDichotomy (data := spineData)
                  fullModulus (by key_fresh) (by key_fresh) with
              | .right failsHistory =>
                  let residualHistory :=
                    (pairIncrementResidualRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile)
                      (data := spineData)).run failsHistory (by key_fresh)
                  exact Or.inr (Or.inr
                    (Or.inr (Or.inr (Or.inl
                      (pairConditionalFactorizationReturn_freeIncrementFails residualHistory)))))
              | .left incrementHistory =>
                  match pairIncrementOutcomeDichotomy (data := spineData)
                      incrementHistory (by key_fresh) (by key_fresh) with
                  | .left earlyHistory =>
                      -- Lean improvement: `[180]`'s periodic alternatives are `[179]`'s
                      -- early alternatives at the same returns; empty after `[179]` no-early.
                      exact (closeIncompatible earlyHistory (K .pairSystemNoEarlyOutcome)
                        (K .pairIncrementEarlyOutcome) (by key_fresh)).elimClosed
                        (by infer_instance) |>.elim
                  | .right noEarlyHistory =>
                      let arithmeticHistory :=
                        (pairSerialArithmeticRow (BranchState := BranchState)
                          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                          (presentation := erdosReceiverLoadProfile)
                          (data := spineData)).run noEarlyHistory (by key_fresh)
                      let closedHistory :=
                        (pairPowerOfTwoCycleRow (BranchState := BranchState)
                          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                          (presentation := erdosReceiverLoadProfile)
                          (data := spineData)).runAndCloseIncompatible
                            arithmeticHistory (K .selection)
                            (K .pairPowerOfTwoCycle) (by key_fresh)
                            (by key_fresh)
                      exact (closedHistory.elimClosed (by infer_instance)).elim

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 2048 in
/-- Nodes `[178]`--`[180]`, the pair-code chain entered from the free side of `[137]` (node `[130]`'s dependent arm): on
any ledger that carries the node-`[178]` first failure
`K .pairOverlapFirstFailure` and every key of that entry arm.  Each paper test is a `Decision`; each
uncovered implication is retained at the open node `[182]`, each covered Type B
alternative returns with its own `[179]`/`[180]` source key, and the
full-modulus arithmetic arm closes against node `[1]` through the framework. -/
-- EG-NODE [178] pair-code unrealized residual: conditional factorization gives a minimal connected pair overlap obstruction
-- EG-NODE [179] covered uncrossing: target/sparse-exit/Type B, or a graph-realized serial demand system
-- EG-NODE [180] covered increment split: periodic sparse-exit/Type B, or full-modulus arithmetic gives an actual power-of-two cycle
-- EG-NODE [182] OPEN: the exact [178], [179], or [180] implication not supplied by the manuscript
noncomputable def selectedPairCodeChainDependent
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .pairOverlapFirstFailure) known]
    [FactKeys.Has (K .noProperBaseline) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
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
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .minDegreeBaseline) known]
    (systemFresh : K .pairOverlapSystem ∉ known := by key_fresh)
    (correlationFresh : K .pairCorrelation ∉ known := by key_fresh)
    (coverageFresh : K .pairCoverage ∉ known := by key_fresh)
    (fullModulusFresh : K .pairFullModulus ∉ known := by key_fresh)
    (uncrossingFresh : K .pairUncrossing ∉ known := by key_fresh)
    (factorizationFresh : K .pairConditionalFactorization ∉ known := by key_fresh)
    (factorizationFailsFresh : K .pairFactorizationFails ∉ known := by key_fresh)
    (residualFresh : K .pairConditionalFactorizationResidual ∉ known := by key_fresh)
    (overlapFresh : K .pairFailureOverlap ∉ known := by key_fresh)
    (returnsFresh : K .pairDemandReturns ∉ known := by key_fresh)
    (realizabilityFresh : K .pairSystemRealizability ∉ known := by key_fresh)
    (realizabilityFailsFresh : K .pairRealizabilityFails ∉ known := by key_fresh)
    (systemEarlyFresh : K .pairSystemEarlyOutcome ∉ known := by key_fresh)
    (systemNoEarlyFresh : K .pairSystemNoEarlyOutcome ∉ known := by key_fresh)
    (serialFresh : K .pairSerialDemandSystem ∉ known := by key_fresh)
    (fanEntryFresh : K .typeBFanEntry ∉ known := by key_fresh)
    (handoffSupportFresh : K .pairHandoffSupport ∉ known := by key_fresh)
    (handoffChargeFresh : K .pairHandoffCharge ∉ known := by key_fresh)
    (handoffNetChargeFresh : K .pairHandoffNetCharge ∉ known := by key_fresh)
    (pairHandoffHubChargeFresh : K .pairHandoffHubCharge ∉ known := by key_fresh)
    (pairHandoffBoundaryTypeFresh : K .pairHandoffBoundaryType ∉ known := by key_fresh)
    (pairHandoffCriticalCoordinateFresh : K .pairHandoffCriticalCoordinate ∉ known := by key_fresh)
    (pairObstructionDescentFresh : K .pairObstructionDescent ∉ known := by key_fresh)
    (pairHandoffHubForcesFresh : K .pairHandoffHubForces ∉ known := by key_fresh)
    (pairHandoffDemandEndsFresh : K .pairHandoffDemandEnds ∉ known := by key_fresh)
    (pairHandoffHubBalanceFresh : K .pairHandoffHubBalance ∉ known := by key_fresh)
    (pairHandoffFibreAtGFresh : K .pairHandoffFibreAtG ∉ known := by key_fresh)
    (incrementFresh : K .pairIncrementCovered ∉ known := by key_fresh)
    (incrementFailsFresh : K .pairIncrementFails ∉ known := by key_fresh)
    (incrementEarlyFresh : K .pairIncrementEarlyOutcome ∉ known := by key_fresh)
    (incrementNoEarlyFresh : K .pairIncrementNoEarlyOutcome ∉ known := by key_fresh)
    (arithmeticFresh : K .pairSerialArithmetic ∉ known := by key_fresh)
    (cycleFresh : K .pairPowerOfTwoCycle ∉ known := by key_fresh)
    (closedFresh : closed ∉ known := by key_fresh)
    [FactKeys.Has (K .activeSurplusDemands) known]
    [FactKeys.Has (K .activeSurplusFamily) known]
    [FactKeys.Has (K .baselineSpineDemand) known]
    [FactKeys.Has (K .freePairCountFails) known]
    [FactKeys.Has (K .cycleRankConstraint) known]
    [FactKeys.Has (K .degreeProfileFibres) known]
    [FactKeys.Has (K .exactCubicBaselineBudget) known]
    [FactKeys.Has (K .incrementalSkeletonRoom) known]
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
    [FactKeys.Has (K .maximalPacking) known]
    [FactKeys.Has (K .mixedSparseSpineDependence) known]
    [FactKeys.Has (K .openPortSuppression) known]
    [FactKeys.Has (K .openPortSuppressionSafe) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .returnAvoidance) known]
    [FactKeys.Has (K .singleOpenPortSuppressionWitness) known]
    [FactKeys.Has (K .skeletonDominates) known]
    [FactKeys.Has (K .slackIndependent) known]
    [FactKeys.Has (K .sparsePortActivation) known]
    [FactKeys.Has (K .sparseSlackSurplus) known]
    [FactKeys.Has (K .sparseUpperEnvelope) known]
    [FactKeys.Has (K .suppressedFamilyCriticalCycle) known]
    [FactKeys.Has (K .targetCompleteContextUniversality) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .windowPresent) known]
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
    [FactKeys.Has (K .blockedPairCodeUnrealized) known] :
    StrictSurplusBoundaryResult selected := by
  let overlapSystem :=
    (pairOverlapSystemRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by key_fresh)
  let correlated :=
    (pairCorrelationRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      overlapSystem (by key_fresh)
  match pairConditionalFactorizationDichotomy (data := spineData)
      correlated (by key_fresh) (by key_fresh) with
  | .right failsHistory =>
      let residualHistory :=
        (pairFactorizationResidualRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run failsHistory (by key_fresh)
      exact Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inl
          (pairConditionalFactorizationReturn_blockedFactorizationFails residualHistory))))))
  | .left factorizationHistory =>
      let overlapFailure :=
        (pairFailureOverlapRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run factorizationHistory (by key_fresh)
      let demandReturns :=
        (pairDemandReturnsRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run overlapFailure (by key_fresh)
      let coverage :=
        (pairCoverageRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          demandReturns (by key_fresh)
      let uncrossing :=
        (pairUncrossingRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          coverage (by key_fresh)
      match pairSystemRealizabilityDichotomy (data := spineData)
          uncrossing (by key_fresh) (by key_fresh) with
      | .right failsHistory =>
          let residualHistory :=
            (pairRealizabilityResidualRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run failsHistory (by key_fresh)
          exact Or.inr (Or.inr
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              (pairConditionalFactorizationReturn_blockedRealizabilityFails residualHistory)))))))
      | .left coveredHistory =>
          match pairSystemOutcomeDichotomy (data := spineData)
              coveredHistory (by key_fresh) (by key_fresh) with
          | .left earlyHistory =>
              let typeBHistory :=
                (pairSystemEarlyTypeBEntryRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run earlyHistory (by key_fresh)
              let factsHistory :=
                (pairHandoffFactsRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run typeBHistory (by key_fresh)
              exact Or.inr (Or.inl (Or.inr
                (pairTypeBDependentSystemReturn
                  ((pairHandoffBalanceRow (BranchState := BranchState)
                    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                    (presentation := erdosReceiverLoadProfile)
                    (data := spineData)).run factsHistory (by key_fresh)))))
          | .right noEarlyHistory =>
              let serialHistory :=
                (pairSerialDemandSystemRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run noEarlyHistory (by key_fresh)
              let fullModulus :=
                (pairFullModulusRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  serialHistory (by key_fresh)
              match pairIncrementCoveredDichotomy (data := spineData)
                  fullModulus (by key_fresh) (by key_fresh) with
              | .right failsHistory =>
                  let residualHistory :=
                    (pairIncrementResidualRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile)
                      (data := spineData)).run failsHistory (by key_fresh)
                  exact Or.inr (Or.inr
                    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                      (pairConditionalFactorizationReturn_blockedIncrementFails residualHistory)))))))
              | .left incrementHistory =>
                  match pairIncrementOutcomeDichotomy (data := spineData)
                      incrementHistory (by key_fresh) (by key_fresh) with
                  | .left earlyHistory =>
                      -- Lean improvement: `[180]`'s periodic alternatives are `[179]`'s
                      -- early alternatives at the same returns; empty after `[179]` no-early.
                      exact (closeIncompatible earlyHistory (K .pairSystemNoEarlyOutcome)
                        (K .pairIncrementEarlyOutcome) (by key_fresh)).elimClosed
                        (by infer_instance) |>.elim
                  | .right noEarlyHistory =>
                      let arithmeticHistory :=
                        (pairSerialArithmeticRow (BranchState := BranchState)
                          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                          (presentation := erdosReceiverLoadProfile)
                          (data := spineData)).run noEarlyHistory (by key_fresh)
                      let closedHistory :=
                        (pairPowerOfTwoCycleRow (BranchState := BranchState)
                          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                          (presentation := erdosReceiverLoadProfile)
                          (data := spineData)).runAndCloseIncompatible
                            arithmeticHistory (K .selection)
                            (K .pairPowerOfTwoCycle) (by key_fresh)
                            (by key_fresh)
                      exact (closedHistory.elimClosed (by infer_instance)).elim

set_option maxHeartbeats 8000000 in
/-- Node `[144]` on any ledger carrying the homogeneous bottleneck pattern
published by the geometric audit `[140]`/`[142]`/`[143]`: decide the fixed caps.
On the failing arm `lem:same-token-bottleneck-routing` routes the pattern to the
decorated same-token Type B handoff and node `[65]` appends the common Type B
entry, reaching `[144a]`.  The caps arm is dead at G: it is closed at the node
with `closeIncompatible` against the audited pattern
`K .homogeneousBottleneckPattern` on the same ledger, which refutes the caps at
G's canonical certified ledger.  The two `[144a]` ledgers (handoff; handoff
fails) are handed back to the caller, whose class arm of `[139]`/`[141]` fixes
which subtype of `Node144aOutcome` each one returns. -/
-- EG-NODE [144] same-token bottleneck: Type B handoff or capped route?
-- EG-NODE [138] no coupled overload: explicit quadratic bound on \(\sigma\); near-cubic spine
noncomputable def selectedBottleneckDischarge
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .homogeneousBottleneckPattern) known]
    [FactKeys.Has (K .sparsePressureOverload) known]
    [FactKeys.Has (K .capacityTokenLedger) known]
    [FactKeys.Has (K .activeSurplusDemands) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .minDegreeBaseline) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .highCentreNormalForm) known]
    [FactKeys.Has (K .sparseSlackSurplus) known]
    [FactKeys.Has (K .fibrePressure) known]
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
    [FactKeys.Has (K .selection) known]
    (failFresh : K .homogeneousCapsFail ∉ known := by key_fresh)
    (capsFresh : K .homogeneousCapsHold ∉ known := by key_fresh)
    (routingFresh : K .bottleneckRouting ∉ known := by key_fresh)
    (handoffFresh : K .typeBHandoff ∉ known := by key_fresh)
    (handoffFailsFresh : K .typeBHandoffFails ∉ known := by key_fresh)
    (unresolvedFresh : K .sameTokenPatternUnresolved ∉ known := by key_fresh)
    (readingsFresh : K .sameTokenReadingsNotReplacement ∉ known := by key_fresh)
    (fanEntryFresh : K .typeBFanEntry ∉ known := by key_fresh)
    (supportsFresh : K .sameTokenPatternSupports ∉ known := by key_fresh)
    (swapFresh : K .sameTokenPatternSwap ∉ known := by key_fresh)
    (partitionFresh : K .sameTokenPairPartition ∉ known := by key_fresh)
    (transplantSizeFresh : K .sameTokenTransplantSize ∉ known := by key_fresh)
    (transplantDeficitFresh : K .sameTokenTransplantDeficit ∉ known := by key_fresh)
    (decidedFresh : K .sameTokenUnresolvedDecided ∉ known := by key_fresh)
    (readingsExactFresh : K .sameTokenReadingsExact ∉ known := by key_fresh)
    (swapFreshKey : K .sameTokenSwap ∉ known := by key_fresh)
    (swapExactFresh : K .sameTokenSwapExact ∉ known := by key_fresh)
    (wholeFresh : K .sameTokenU2FreeWhole ∉ known := by key_fresh)
    (seedCoverFresh : K .sameTokenSeedCover ∉ known := by key_fresh)
    (pathInteractionsFresh : K .sameTokenPathInteractions ∉ known := by key_fresh)
    (closedFresh : closed ∉ known := by key_fresh)
    [FactKeys.Has (K .activeSurplusFamily) known]
    [FactKeys.Has (K .baselineSpineDemand) known]
    [FactKeys.Has (K .freePairCountFails) known]
    [FactKeys.Has (K .blockedPairEntropySandwich) known]
    [FactKeys.Has (K .blockedPairEntropySetup) known]
    [FactKeys.Has (K .blockedPairNoExit) known]
    [FactKeys.Has (K .canonicalBlockerRoute) known]
    [FactKeys.Has (K .canonicalPairLedger) known]
    [FactKeys.Has (K .cycleRankConstraint) known]
    [FactKeys.Has (K .degreeProfileFibres) known]
    [FactKeys.Has (K .dependentPairFamily) known]
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
    [FactKeys.Has (K .maximalPacking) known]
    [FactKeys.Has (K .noProperBaseline) known]
    [FactKeys.Has (K .openPortSuppression) known]
    [FactKeys.Has (K .openPortSuppressionSafe) known]
    [FactKeys.Has (K .pairDegreeProfileFibres) known]
    [FactKeys.Has (K .pairNoProfileObstruction) known]
    [FactKeys.Has (K .pairNoResponseObstruction) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .returnAvoidance) known]
    [FactKeys.Has (K .roleFibrePartition) known]
    [FactKeys.Has (K .singleOpenPortSuppressionWitness) known]
    [FactKeys.Has (K .slackIndependent) known]
    [FactKeys.Has (K .sparsePortActivation) known]
    [FactKeys.Has (K .sparseUpperEnvelope) known]
    [FactKeys.Has (K .suppressedFamilyCriticalCycle) known]
    [FactKeys.Has (K .targetCompleteContextUniversality) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .windowPresent) known] :
    ExactLedger EGInput.{u} selected
        (K .typeBFanEntry :: K .typeBHandoff :: K .sameTokenPatternSupports ::
          K .sameTokenPatternSwap :: K .bottleneckRouting ::
          K .homogeneousCapsFail :: known) ⊕
      ExactLedger EGInput.{u} selected
        (K .sameTokenUnresolvedDecided :: K .sameTokenReadingsExact :: K .sameTokenSwap ::
          K .sameTokenSwapExact :: K .sameTokenU2FreeWhole :: K .sameTokenSeedCover ::
          K .sameTokenPathInteractions ::
          K .sameTokenTransplantSize :: K .sameTokenTransplantDeficit ::
          K .sameTokenPairPartition :: K .sameTokenReadingsNotReplacement ::
          K .sameTokenPatternUnresolved :: K .typeBHandoffFails ::
          K .sameTokenPatternSupports :: K .sameTokenPatternSwap :: K .bottleneckRouting ::
          K .homogeneousCapsFail :: known) := by
  match homogeneousBottleneckDichotomy (data := spineData) history
      (by key_fresh) (by key_fresh) with
  | .left patternHistory =>
      let routed :=
        (sameTokenBottleneckRoutingRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run patternHistory (by key_fresh)
      -- The pattern supports of G's canonical routing and the exact swaps of
      -- its two readings, above the handoff decision; no decision.
      let supported :=
        (sameTokenPatternSupportsRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run routed (by key_fresh)
      match sameTokenHandoffDichotomy (data := spineData) supported
          (by key_fresh) (by key_fresh) with
      | .left handoffHistory =>
          let entered :=
            (sameTokenTypeBFanEntryRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run handoffHistory (by key_fresh)
          exact .inl entered
      | .right failsHistory =>
          let unresolvedOnly :=
            (sameTokenPatternUnresolvedRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run failsHistory (by key_fresh)
          -- `[144a]`: the explicit replacement candidates of tex 5594 at G,
          -- checked against the survivor and published.
          let unresolved :=
            (sameTokenReadingsNotReplacementRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run unresolvedOnly (by key_fresh)
          -- `[144a]`: the exact partition of the unresolved pair at G's
          -- canonical objects; the one-sided region is empty.  No decision.
          let partitioned :=
            (sameTokenPairPartitionRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run unresolved (by key_fresh)
          -- `[144a]` (G repair R5, Lean improvement): the transplants of the
          -- two pattern supports into `Z`, their conditions (i)--(iv), the size
          -- equality minimality gives, and their exact failure.  No decision:
          -- the arm "both transplants valid" does not close at G.
          let transplanted :=
            (sameTokenTransplantRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run partitioned (by key_fresh)
          -- `[144a]` (G audit S144a, Lean improvement): the entry test decided at
          -- G, the exact readings, the rerouted swaps of the two supports in both
          -- directions with their exact failure, and the boundary-free
          -- configuration.  No decision: no arm closes at G.
          let tested :=
            (sameTokenSwapRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run transplanted (by key_fresh)
          exact .inr tested
  | .right capsHistory =>
      -- The caps arm, closed at G: the audited pattern at G's overloading
      -- token refutes the caps at the same ledger.
      exact (closeIncompatible capsHistory (K .homogeneousBottleneckPattern)
        (K .homogeneousCapsHold) (by key_fresh)).elimClosed
        (by infer_instance) |>.elim

end HypostructureErdos64EG
