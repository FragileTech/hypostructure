import HypostructureErdos64EG.Assembly.Residuals.ArmBlocks

/-!
# Assembly: the `ColdBranchClosedOutcome` residual, split by fact set

`ColdBranchClosedOutcome` ([187], local cold-terminal exclusion) is reached
at G along one root path, the [153] linear cold-mass arm of the realized
package with a silent germ family: the singleton `linearRealizedSilent`.
The 100 paths through the absorbed-germ residual `[174]`--`[177]` (formerly
the product `ColdBranchClosedOutcome_product`) are not entered: `[173]`'s
no-arm is closed at the node against the private-carrier rate `K .route8Rate`
(`instIncompatibleExactCollisionFailsRoute8Rate`).

The singleton lists every key of its arm as an explicit `Holds` conjunct, and
its return theorem reads each fact with one `ExactLedger.get`.

G repair (R4): the three former singletons `linearDenseAtOrAbove`,
`linearDenseRateFailed` and `linearRealizedDistinguished` carried the `[154]`
G2 yes-arm `K .coldGermSomeDistinguishing`.  Read at G that arm is empty (the
two representatives of every germ have the same target response in `G − Z`),
and it is closed at `[154]` against the selection
(`instIncompatibleColdGermSomeDistinguishingSelection`).  They are unreachable
at G and are removed, together with their place in the root result type.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u

/-- **`[187]` (local cold-terminal exclusion), singleton `linearRealizedSilent`**
(88 facts): [153] linear cold mass in `nearCubicRealized`: [158] realized, [146] theta at or above, [154] none realizing / none distinguishing. -/
abbrev ColdBranchClosedOutcome_linearRealizedSilent (selected : EGInput.{u}) : Prop :=
  ColdBranchClosedOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermFamilyPositive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermNoneDistinguishing selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermNoneRealizing selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMassLinear selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8AtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageRealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .realizedDensityOrder selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .realizedOrderSmall selected.object

theorem ColdBranchClosedOutcome_linearRealizedSilent.toGeneric {selected : EGInput.{u}}
    (h : ColdBranchClosedOutcome_linearRealizedSilent selected) :
    ColdBranchClosedOutcome selected :=
  h.1

/-- The return of `ColdBranchClosedOutcome_linearRealizedSilent`: one `get` per fact. -/
theorem coldBranchClosed_linearRealizedSilentReturn
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .absorbedGermFanData) known]
    [FactKeys.Has (K .absorbedGermSplit) known]
    [FactKeys.Has (K .barrierCap) known]
    [FactKeys.Has (K .barrierEnumeration) known]
    [FactKeys.Has (K .boundaryDemand) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .coldAmbientCubic) known]
    [FactKeys.Has (K .coldAmbientCubicStubExcess) known]
    [FactKeys.Has (K .coldBranchClosed) known]
    [FactKeys.Has (K .coldCorridorState) known]
    [FactKeys.Has (K .coldCutStatesDistinct) known]
    [FactKeys.Has (K .coldExchangeBound) known]
    [FactKeys.Has (K .coldFailureCompression) known]
    [FactKeys.Has (K .coldFailureCycle) known]
    [FactKeys.Has (K .coldFailureDefectRoute) known]
    [FactKeys.Has (K .coldFailureRouting) known]
    [FactKeys.Has (K .coldFirstFailureOccurrence) known]
    [FactKeys.Has (K .coldGermCandidates) known]
    [FactKeys.Has (K .coldGermDistinguished) known]
    [FactKeys.Has (K .coldGermRealized) known]
    [FactKeys.Has (K .coldGermRouted) known]
    [FactKeys.Has (K .coldGermSilent) known]
    [FactKeys.Has (K .coldHandoffTransfer) known]
    [FactKeys.Has (K .coldHotEntropyCap) known]
    [FactKeys.Has (K .coldMass) known]
    [FactKeys.Has (K .coldReturnCorridors) known]
    [FactKeys.Has (K .coldSameInterfaceTable) known]
    [FactKeys.Has (K .coldSelectedBranchExcess) known]
    [FactKeys.Has (K .coldStubExcess) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .minDegreeBaseline) known]
    [FactKeys.Has (K .curvatureFullRank) known]
    [FactKeys.Has (K .curvatureTargetRank) known]
    [FactKeys.Has (K .cycleRankConstraint) known]
    [FactKeys.Has (K .degreeProfileFibres) known]
    [FactKeys.Has (K .exactResponseProfile) known]
    [FactKeys.Has (K .forcedCurvatureCost) known]
    [FactKeys.Has (K .hotColdPartition) known]
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
    [FactKeys.Has (K .netChargeLocalization) known]
    [FactKeys.Has (K .noProperBaseline) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .returnAvoidance) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .skeletonDominates) known]
    [FactKeys.Has (K .slackIndependent) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    [FactKeys.Has (K .stubSupply) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .targetCompleteContextUniversality) known]
    [FactKeys.Has (K .targetRankCircuit) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .wedgeSupply) known]
    [FactKeys.Has (K .windowPackageSeparated) known]
    [FactKeys.Has (K .windowPresent) known]
    [FactKeys.Has (K .coldGermFamilyPositive) known]
    [FactKeys.Has (K .coldGermNoneDistinguishing) known]
    [FactKeys.Has (K .coldGermNoneRealizing) known]
    [FactKeys.Has (K .coldMassLinear) known]
    [FactKeys.Has (K .coldRoute8AtOrAbove) known]
    [FactKeys.Has (K .windowPackageRealized) known]
    [FactKeys.Has (K .realizedDensityOrder) known]
    [FactKeys.Has (K .realizedOrderSmall) known]
    : ColdBranchClosedOutcome_linearRealizedSilent selected :=
  ⟨coldBranchClosedReturn history,
    (history.get (K .coldGermFamilyPositive)).down,
    (history.get (K .coldGermNoneDistinguishing)).down,
    (history.get (K .coldGermNoneRealizing)).down,
    (history.get (K .coldMassLinear)).down,
    (history.get (K .coldRoute8AtOrAbove)).down,
    (history.get (K .windowPackageRealized)).down,
    (history.get (K .realizedDensityOrder)).down,
    (history.get (K .realizedOrderSmall)).down⟩

end HypostructureErdos64EG
