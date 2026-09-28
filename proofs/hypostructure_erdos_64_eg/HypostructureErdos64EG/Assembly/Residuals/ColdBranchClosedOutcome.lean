import HypostructureErdos64EG.Assembly.Residuals.ArmBlocks

/-!
# Assembly: the `ColdBranchClosedOutcome` residual, split by fact set

`ColdBranchClosedOutcome` ([187], local cold-terminal exclusion) is reached
along 4 root paths, on the [153] linear cold-mass arm, each its own subtype.
The 100 paths through the absorbed-germ residual `[174]`--`[177]` (formerly
the product `ColdBranchClosedOutcome_product`) are not entered: `[173]`'s
no-arm is closed at the node against the private-carrier rate `K .route8Rate`
(`instIncompatibleExactCollisionFailsRoute8Rate`).

Every block lists every key of its arm as an explicit `Holds` conjunct, and
every return theorem reads each fact with one `ExactLedger.get`.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u
/-- **`[187]` (local cold-terminal exclusion), singleton `linearDenseAtOrAbove`**
(80 facts): [153] linear cold mass through `nearCubicDenseLinear` after `nearCubicDensePassAtOrAbove`: [158] unrealized, [160] tau at or above 1/4, [146] theta at or above, [162] heavy entry, [154] none realizing / some distinguishing. -/
abbrev ColdBranchClosedOutcome_linearDenseAtOrAbove (selected : EGInput.{u}) : Prop :=
  ColdBranchClosedOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermFamilyPositive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermNoneRealizing selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermSomeDistinguishing selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldHeavyEntryTerminal selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMassLinear selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8AtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseColdCorridorsTerminal selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyAtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object

theorem ColdBranchClosedOutcome_linearDenseAtOrAbove.toGeneric {selected : EGInput.{u}}
    (h : ColdBranchClosedOutcome_linearDenseAtOrAbove selected) :
    ColdBranchClosedOutcome selected :=
  h.1

/-- The return of `ColdBranchClosedOutcome_linearDenseAtOrAbove`: one `get` per
fact. The facts of the upstream arm are read from its block
(`DenseTauBlock_atOrAbove`), built by the block's `.ret` with one `get` per key
on the same ledger. -/
theorem coldBranchClosed_linearDenseAtOrAboveReturn
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
    [FactKeys.Has (K .twoHighForcedPath) known]
    [FactKeys.Has (K .sameHighForcedPath) known]
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
    [FactKeys.Has (K .coldGermNoneRealizing) known]
    [FactKeys.Has (K .coldGermSomeDistinguishing) known]
    [FactKeys.Has (K .coldHeavyEntryTerminal) known]
    [FactKeys.Has (K .coldMassLinear) known]
    [FactKeys.Has (K .coldRoute8AtOrAbove) known]
    [FactKeys.Has (K .denseColdCorridorsTerminal) known]
    [FactKeys.Has (K .windowPackageUnrealized) known]
    (tau : DenseTauBlock_atOrAbove selected)
    : ColdBranchClosedOutcome_linearDenseAtOrAbove selected :=
  ⟨coldBranchClosedReturn history,
    (history.get (K .coldGermFamilyPositive)).down,
    (history.get (K .coldGermNoneRealizing)).down,
    (history.get (K .coldGermSomeDistinguishing)).down,
    (history.get (K .coldHeavyEntryTerminal)).down,
    (history.get (K .coldMassLinear)).down,
    (history.get (K .coldRoute8AtOrAbove)).down,
    (history.get (K .denseColdCorridorsTerminal)).down,
    tau,
    (history.get (K .windowPackageUnrealized)).down⟩

/-- **`[187]` (local cold-terminal exclusion), singleton `linearDenseRateFailed`**
(81 facts): [153] linear cold mass through `nearCubicDenseLinear` after `nearCubicDensePassRateFailed`: [158] unrealized, [160] tau below 1/4 and route-8 rate failing, [146] theta at or above, [162] heavy entry, [154] none realizing / some distinguishing. -/
abbrev ColdBranchClosedOutcome_linearDenseRateFailed (selected : EGInput.{u}) : Prop :=
  ColdBranchClosedOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermFamilyPositive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermNoneRealizing selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermSomeDistinguishing selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldHeavyEntryTerminal selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMassLinear selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8AtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseColdCorridorsTerminal selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyBelow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8RateFails selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object

theorem ColdBranchClosedOutcome_linearDenseRateFailed.toGeneric {selected : EGInput.{u}}
    (h : ColdBranchClosedOutcome_linearDenseRateFailed selected) :
    ColdBranchClosedOutcome selected :=
  h.1

/-- The return of `ColdBranchClosedOutcome_linearDenseRateFailed`: one `get` per
fact. The facts of the upstream arm are read from its block
(`DenseTauBlock_belowRateFails`), built by the block's `.ret` with one `get` per
key on the same ledger. -/
theorem coldBranchClosed_linearDenseRateFailedReturn
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
    [FactKeys.Has (K .twoHighForcedPath) known]
    [FactKeys.Has (K .sameHighForcedPath) known]
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
    [FactKeys.Has (K .coldGermNoneRealizing) known]
    [FactKeys.Has (K .coldGermSomeDistinguishing) known]
    [FactKeys.Has (K .coldHeavyEntryTerminal) known]
    [FactKeys.Has (K .coldMassLinear) known]
    [FactKeys.Has (K .coldRoute8AtOrAbove) known]
    [FactKeys.Has (K .denseColdCorridorsTerminal) known]
    [FactKeys.Has (K .windowPackageUnrealized) known]
    (tau : DenseTauBlock_belowRateFails selected)
    : ColdBranchClosedOutcome_linearDenseRateFailed selected :=
  ⟨coldBranchClosedReturn history,
    (history.get (K .coldGermFamilyPositive)).down,
    (history.get (K .coldGermNoneRealizing)).down,
    (history.get (K .coldGermSomeDistinguishing)).down,
    (history.get (K .coldHeavyEntryTerminal)).down,
    (history.get (K .coldMassLinear)).down,
    (history.get (K .coldRoute8AtOrAbove)).down,
    (history.get (K .denseColdCorridorsTerminal)).down,
    tau.1,
    tau.2,
    (history.get (K .windowPackageUnrealized)).down⟩

/-- **`[187]` (local cold-terminal exclusion), singleton `linearRealizedDistinguished`**
(79 facts): [153] linear cold mass in `nearCubicRealized`: [158] realized, [146] theta at or above, [154] none realizing / some distinguishing. -/
abbrev ColdBranchClosedOutcome_linearRealizedDistinguished (selected : EGInput.{u}) : Prop :=
  ColdBranchClosedOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermFamilyPositive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermNoneRealizing selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermSomeDistinguishing selected.object ∧
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

theorem ColdBranchClosedOutcome_linearRealizedDistinguished.toGeneric {selected : EGInput.{u}}
    (h : ColdBranchClosedOutcome_linearRealizedDistinguished selected) :
    ColdBranchClosedOutcome selected :=
  h.1

/-- The return of `ColdBranchClosedOutcome_linearRealizedDistinguished`: one `get` per fact. -/
theorem coldBranchClosed_linearRealizedDistinguishedReturn
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
    [FactKeys.Has (K .twoHighForcedPath) known]
    [FactKeys.Has (K .sameHighForcedPath) known]
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
    [FactKeys.Has (K .coldGermNoneRealizing) known]
    [FactKeys.Has (K .coldGermSomeDistinguishing) known]
    [FactKeys.Has (K .coldMassLinear) known]
    [FactKeys.Has (K .coldRoute8AtOrAbove) known]
    [FactKeys.Has (K .windowPackageRealized) known]
    [FactKeys.Has (K .realizedDensityOrder) known]
    [FactKeys.Has (K .realizedOrderSmall) known]
    : ColdBranchClosedOutcome_linearRealizedDistinguished selected :=
  ⟨coldBranchClosedReturn history,
    (history.get (K .coldGermFamilyPositive)).down,
    (history.get (K .coldGermNoneRealizing)).down,
    (history.get (K .coldGermSomeDistinguishing)).down,
    (history.get (K .coldMassLinear)).down,
    (history.get (K .coldRoute8AtOrAbove)).down,
    (history.get (K .windowPackageRealized)).down,
    (history.get (K .realizedDensityOrder)).down,
    (history.get (K .realizedOrderSmall)).down⟩

/-- **`[187]` (local cold-terminal exclusion), singleton `linearRealizedSilent`**
(79 facts): [153] linear cold mass in `nearCubicRealized`: [158] realized, [146] theta at or above, [154] none realizing / none distinguishing. -/
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
    [FactKeys.Has (K .twoHighForcedPath) known]
    [FactKeys.Has (K .sameHighForcedPath) known]
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

/-- The four linear-arm singletons of the residual `[187]` (local
cold-terminal exclusion), returned on the `[153]` linear arm of the near-cubic
survivor. -/
abbrev ColdBranchClosedLinearSubtypes (selected : EGInput.{u}) : Prop :=
  ColdBranchClosedOutcome_linearDenseAtOrAbove selected ∨
  ColdBranchClosedOutcome_linearDenseRateFailed selected ∨
  ColdBranchClosedOutcome_linearRealizedDistinguished selected ∨
  ColdBranchClosedOutcome_linearRealizedSilent selected

/-- The return of the local cold-terminal exclusion on the `[153]` linear arm of the dense pass (`nearCubicDenseLinear`), on the `[160]` arm named by `tau`, through that singleton's return theorem. -/
theorem coldBranchClosedLinearDenseReturn
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
    [FactKeys.Has (K .twoHighForcedPath) known]
    [FactKeys.Has (K .sameHighForcedPath) known]
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
    [FactKeys.Has (K .coldGermNoneRealizing) known]
    [FactKeys.Has (K .coldGermSomeDistinguishing) known]
    [FactKeys.Has (K .coldHeavyEntryTerminal) known]
    [FactKeys.Has (K .coldMassLinear) known]
    [FactKeys.Has (K .coldRoute8AtOrAbove) known]
    [FactKeys.Has (K .denseColdCorridorsTerminal) known]
    [FactKeys.Has (K .windowPackageUnrealized) known]
    (tau : DenseTauArm selected) :
    ColdBranchClosedLinearSubtypes selected := by
  rcases tau with t | t
  · exact Or.inl (coldBranchClosed_linearDenseAtOrAboveReturn history t)
  · exact Or.inr (Or.inl (coldBranchClosed_linearDenseRateFailedReturn history t))

end HypostructureErdos64EG
