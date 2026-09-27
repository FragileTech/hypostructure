import HypostructureErdos64EG.Assembly.Residuals

/-!
# Assembly: Residuals / Route8RateFailsOutcome

Node `[187]` (private-carrier rate failure), split by the distinct fact set of
the single ledger at its return.  The generic `Route8RateFailsOutcome`
(`Assembly/Residuals.lean`) carries the 42 facts common to every path; the
twelve paths reach it through `[158]`/`[160]` (three upstream arms) times the
four surviving arms of `[50]`--`[55]`, and each path's ledger holds a distinct
set of extra facts.  Each subtype is the generic residual together with every
extra fact of its path, one `Holds` conjunct per key.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- **Node `[187]` (private-carrier rate failure)**:
`[158]` yes (realized package);
`[50]` high, `[53]` bound (Residual C).
The generic residual and the 4 extra facts of this path
(46 facts). -/
abbrev Route8RateFailsOutcome_realized_highEntropy (selected : EGInput.{u}) : Prop :=
  Route8RateFailsOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageRealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderEntropyHigh selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .entropyPackageDemand selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .entropyCapBound selected.object

theorem Route8RateFailsOutcome_realized_highEntropy.toGeneric
    {selected : EGInput.{u}}
    (outcome : Route8RateFailsOutcome_realized_highEntropy selected) :
    Route8RateFailsOutcome selected :=
  outcome.1

/-- The return of `Route8RateFailsOutcome_realized_highEntropy`:
one `get` per fact of its ledger. -/
theorem route8RateFailsReturn_realized_highEntropy
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .cubicBaseline) known]
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
    [FactKeys.Has (K .windowPackageRealized) known]
    [FactKeys.Has (K .remainderEntropyHigh) known]
    [FactKeys.Has (K .entropyPackageDemand) known]
    [FactKeys.Has (K .entropyCapBound) known] :
    Route8RateFailsOutcome_realized_highEntropy selected :=
  ⟨route8RateFailsReturn history,
    (history.get (K .windowPackageRealized)).down,
    (history.get (K .remainderEntropyHigh)).down,
    (history.get (K .entropyPackageDemand)).down,
    (history.get (K .entropyCapBound)).down⟩

/-- **Node `[187]` (private-carrier rate failure)**:
`[158]` yes (realized package);
`[50]` low, local-type coordinate nonrepetitive.
The generic residual and the 3 extra facts of this path
(45 facts). -/
abbrev Route8RateFailsOutcome_realized_lowNonrepetitive (selected : EGInput.{u}) : Prop :=
  Route8RateFailsOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageRealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderEntropyLow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .localTypeCoordinateNonrepetitive selected.object

theorem Route8RateFailsOutcome_realized_lowNonrepetitive.toGeneric
    {selected : EGInput.{u}}
    (outcome : Route8RateFailsOutcome_realized_lowNonrepetitive selected) :
    Route8RateFailsOutcome selected :=
  outcome.1

/-- The return of `Route8RateFailsOutcome_realized_lowNonrepetitive`:
one `get` per fact of its ledger. -/
theorem route8RateFailsReturn_realized_lowNonrepetitive
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .cubicBaseline) known]
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
    [FactKeys.Has (K .windowPackageRealized) known]
    [FactKeys.Has (K .remainderEntropyLow) known]
    [FactKeys.Has (K .localTypeCoordinateNonrepetitive) known] :
    Route8RateFailsOutcome_realized_lowNonrepetitive selected :=
  ⟨route8RateFailsReturn history,
    (history.get (K .windowPackageRealized)).down,
    (history.get (K .remainderEntropyLow)).down,
    (history.get (K .localTypeCoordinateNonrepetitive)).down⟩

/-- **Node `[187]` (private-carrier rate failure)**:
`[158]` yes (realized package);
`[50]` low, local-type coordinate repetitive, dominant rooted type wedge-free.
The generic residual and the 5 extra facts of this path
(47 facts). -/
abbrev Route8RateFailsOutcome_realized_lowWedgeFree (selected : EGInput.{u}) : Prop :=
  Route8RateFailsOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageRealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderEntropyLow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .localTypeCoordinateRepetitive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .dominantRootedType selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .dominantRootedTypeWedgeFree selected.object

theorem Route8RateFailsOutcome_realized_lowWedgeFree.toGeneric
    {selected : EGInput.{u}}
    (outcome : Route8RateFailsOutcome_realized_lowWedgeFree selected) :
    Route8RateFailsOutcome selected :=
  outcome.1

/-- The return of `Route8RateFailsOutcome_realized_lowWedgeFree`:
one `get` per fact of its ledger. -/
theorem route8RateFailsReturn_realized_lowWedgeFree
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .cubicBaseline) known]
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
    [FactKeys.Has (K .windowPackageRealized) known]
    [FactKeys.Has (K .remainderEntropyLow) known]
    [FactKeys.Has (K .localTypeCoordinateRepetitive) known]
    [FactKeys.Has (K .dominantRootedType) known]
    [FactKeys.Has (K .dominantRootedTypeWedgeFree) known] :
    Route8RateFailsOutcome_realized_lowWedgeFree selected :=
  ⟨route8RateFailsReturn history,
    (history.get (K .windowPackageRealized)).down,
    (history.get (K .remainderEntropyLow)).down,
    (history.get (K .localTypeCoordinateRepetitive)).down,
    (history.get (K .dominantRootedType)).down,
    (history.get (K .dominantRootedTypeWedgeFree)).down⟩

/-- **Node `[187]` (private-carrier rate failure)**:
`[158]` yes (realized package);
`[50]` low, local-type coordinate repetitive, dominant rooted wedge type.
The generic residual and the 6 extra facts of this path
(48 facts). -/
abbrev Route8RateFailsOutcome_realized_lowWedge (selected : EGInput.{u}) : Prop :=
  Route8RateFailsOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageRealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderEntropyLow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .localTypeCoordinateRepetitive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .dominantRootedType selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .dominantRootedWedgeType selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .independentObstructionTranslates selected.object

theorem Route8RateFailsOutcome_realized_lowWedge.toGeneric
    {selected : EGInput.{u}}
    (outcome : Route8RateFailsOutcome_realized_lowWedge selected) :
    Route8RateFailsOutcome selected :=
  outcome.1

/-- The return of `Route8RateFailsOutcome_realized_lowWedge`:
one `get` per fact of its ledger. -/
theorem route8RateFailsReturn_realized_lowWedge
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .cubicBaseline) known]
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
    [FactKeys.Has (K .windowPackageRealized) known]
    [FactKeys.Has (K .remainderEntropyLow) known]
    [FactKeys.Has (K .localTypeCoordinateRepetitive) known]
    [FactKeys.Has (K .dominantRootedType) known]
    [FactKeys.Has (K .dominantRootedWedgeType) known]
    [FactKeys.Has (K .independentObstructionTranslates) known] :
    Route8RateFailsOutcome_realized_lowWedge selected :=
  ⟨route8RateFailsReturn history,
    (history.get (K .windowPackageRealized)).down,
    (history.get (K .remainderEntropyLow)).down,
    (history.get (K .localTypeCoordinateRepetitive)).down,
    (history.get (K .dominantRootedType)).down,
    (history.get (K .dominantRootedWedgeType)).down,
    (history.get (K .independentObstructionTranslates)).down⟩

/-- **Node `[187]` (private-carrier rate failure)**:
`[158]` no (unrealized package), `[160]` first test no (`τ(θ) ≥ 1/4`);
`[50]` high, `[53]` bound (Residual C).
The generic residual and the 5 extra facts of this path
(47 facts). -/
abbrev Route8RateFailsOutcome_denseAtOrAbove_highEntropy (selected : EGInput.{u}) : Prop :=
  Route8RateFailsOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyAtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderEntropyHigh selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .entropyPackageDemand selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .entropyCapBound selected.object

theorem Route8RateFailsOutcome_denseAtOrAbove_highEntropy.toGeneric
    {selected : EGInput.{u}}
    (outcome : Route8RateFailsOutcome_denseAtOrAbove_highEntropy selected) :
    Route8RateFailsOutcome selected :=
  outcome.1

/-- The return of `Route8RateFailsOutcome_denseAtOrAbove_highEntropy`:
one `get` per fact of its ledger. -/
theorem route8RateFailsReturn_denseAtOrAbove_highEntropy
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .cubicBaseline) known]
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
    [FactKeys.Has (K .windowPackageUnrealized) known]
    [FactKeys.Has (K .denseDeficiencyAtOrAbove) known]
    [FactKeys.Has (K .remainderEntropyHigh) known]
    [FactKeys.Has (K .entropyPackageDemand) known]
    [FactKeys.Has (K .entropyCapBound) known] :
    Route8RateFailsOutcome_denseAtOrAbove_highEntropy selected :=
  ⟨route8RateFailsReturn history,
    (history.get (K .windowPackageUnrealized)).down,
    (history.get (K .denseDeficiencyAtOrAbove)).down,
    (history.get (K .remainderEntropyHigh)).down,
    (history.get (K .entropyPackageDemand)).down,
    (history.get (K .entropyCapBound)).down⟩

/-- **Node `[187]` (private-carrier rate failure)**:
`[158]` no (unrealized package), `[160]` first test no (`τ(θ) ≥ 1/4`);
`[50]` low, local-type coordinate nonrepetitive.
The generic residual and the 4 extra facts of this path
(46 facts). -/
abbrev Route8RateFailsOutcome_denseAtOrAbove_lowNonrepetitive (selected : EGInput.{u}) : Prop :=
  Route8RateFailsOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyAtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderEntropyLow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .localTypeCoordinateNonrepetitive selected.object

theorem Route8RateFailsOutcome_denseAtOrAbove_lowNonrepetitive.toGeneric
    {selected : EGInput.{u}}
    (outcome : Route8RateFailsOutcome_denseAtOrAbove_lowNonrepetitive selected) :
    Route8RateFailsOutcome selected :=
  outcome.1

/-- The return of `Route8RateFailsOutcome_denseAtOrAbove_lowNonrepetitive`:
one `get` per fact of its ledger. -/
theorem route8RateFailsReturn_denseAtOrAbove_lowNonrepetitive
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .cubicBaseline) known]
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
    [FactKeys.Has (K .windowPackageUnrealized) known]
    [FactKeys.Has (K .denseDeficiencyAtOrAbove) known]
    [FactKeys.Has (K .remainderEntropyLow) known]
    [FactKeys.Has (K .localTypeCoordinateNonrepetitive) known] :
    Route8RateFailsOutcome_denseAtOrAbove_lowNonrepetitive selected :=
  ⟨route8RateFailsReturn history,
    (history.get (K .windowPackageUnrealized)).down,
    (history.get (K .denseDeficiencyAtOrAbove)).down,
    (history.get (K .remainderEntropyLow)).down,
    (history.get (K .localTypeCoordinateNonrepetitive)).down⟩

/-- **Node `[187]` (private-carrier rate failure)**:
`[158]` no (unrealized package), `[160]` first test no (`τ(θ) ≥ 1/4`);
`[50]` low, local-type coordinate repetitive, dominant rooted type wedge-free.
The generic residual and the 6 extra facts of this path
(48 facts). -/
abbrev Route8RateFailsOutcome_denseAtOrAbove_lowWedgeFree (selected : EGInput.{u}) : Prop :=
  Route8RateFailsOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyAtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderEntropyLow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .localTypeCoordinateRepetitive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .dominantRootedType selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .dominantRootedTypeWedgeFree selected.object

theorem Route8RateFailsOutcome_denseAtOrAbove_lowWedgeFree.toGeneric
    {selected : EGInput.{u}}
    (outcome : Route8RateFailsOutcome_denseAtOrAbove_lowWedgeFree selected) :
    Route8RateFailsOutcome selected :=
  outcome.1

/-- The return of `Route8RateFailsOutcome_denseAtOrAbove_lowWedgeFree`:
one `get` per fact of its ledger. -/
theorem route8RateFailsReturn_denseAtOrAbove_lowWedgeFree
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .cubicBaseline) known]
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
    [FactKeys.Has (K .windowPackageUnrealized) known]
    [FactKeys.Has (K .denseDeficiencyAtOrAbove) known]
    [FactKeys.Has (K .remainderEntropyLow) known]
    [FactKeys.Has (K .localTypeCoordinateRepetitive) known]
    [FactKeys.Has (K .dominantRootedType) known]
    [FactKeys.Has (K .dominantRootedTypeWedgeFree) known] :
    Route8RateFailsOutcome_denseAtOrAbove_lowWedgeFree selected :=
  ⟨route8RateFailsReturn history,
    (history.get (K .windowPackageUnrealized)).down,
    (history.get (K .denseDeficiencyAtOrAbove)).down,
    (history.get (K .remainderEntropyLow)).down,
    (history.get (K .localTypeCoordinateRepetitive)).down,
    (history.get (K .dominantRootedType)).down,
    (history.get (K .dominantRootedTypeWedgeFree)).down⟩

/-- **Node `[187]` (private-carrier rate failure)**:
`[158]` no (unrealized package), `[160]` first test no (`τ(θ) ≥ 1/4`);
`[50]` low, local-type coordinate repetitive, dominant rooted wedge type.
The generic residual and the 7 extra facts of this path
(49 facts). -/
abbrev Route8RateFailsOutcome_denseAtOrAbove_lowWedge (selected : EGInput.{u}) : Prop :=
  Route8RateFailsOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyAtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderEntropyLow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .localTypeCoordinateRepetitive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .dominantRootedType selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .dominantRootedWedgeType selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .independentObstructionTranslates selected.object

theorem Route8RateFailsOutcome_denseAtOrAbove_lowWedge.toGeneric
    {selected : EGInput.{u}}
    (outcome : Route8RateFailsOutcome_denseAtOrAbove_lowWedge selected) :
    Route8RateFailsOutcome selected :=
  outcome.1

/-- The return of `Route8RateFailsOutcome_denseAtOrAbove_lowWedge`:
one `get` per fact of its ledger. -/
theorem route8RateFailsReturn_denseAtOrAbove_lowWedge
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .cubicBaseline) known]
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
    [FactKeys.Has (K .windowPackageUnrealized) known]
    [FactKeys.Has (K .denseDeficiencyAtOrAbove) known]
    [FactKeys.Has (K .remainderEntropyLow) known]
    [FactKeys.Has (K .localTypeCoordinateRepetitive) known]
    [FactKeys.Has (K .dominantRootedType) known]
    [FactKeys.Has (K .dominantRootedWedgeType) known]
    [FactKeys.Has (K .independentObstructionTranslates) known] :
    Route8RateFailsOutcome_denseAtOrAbove_lowWedge selected :=
  ⟨route8RateFailsReturn history,
    (history.get (K .windowPackageUnrealized)).down,
    (history.get (K .denseDeficiencyAtOrAbove)).down,
    (history.get (K .remainderEntropyLow)).down,
    (history.get (K .localTypeCoordinateRepetitive)).down,
    (history.get (K .dominantRootedType)).down,
    (history.get (K .dominantRootedWedgeType)).down,
    (history.get (K .independentObstructionTranslates)).down⟩

/-- **Node `[187]` (private-carrier rate failure)**:
`[158]` no (unrealized package), `[160]` first test yes (`τ(θ) < 1/4`), private-carrier rate failed;
`[50]` high, `[53]` bound (Residual C).
The generic residual and the 5 extra facts of this path
(47 facts). -/
abbrev Route8RateFailsOutcome_denseBelow_highEntropy (selected : EGInput.{u}) : Prop :=
  Route8RateFailsOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyBelow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderEntropyHigh selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .entropyPackageDemand selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .entropyCapBound selected.object

theorem Route8RateFailsOutcome_denseBelow_highEntropy.toGeneric
    {selected : EGInput.{u}}
    (outcome : Route8RateFailsOutcome_denseBelow_highEntropy selected) :
    Route8RateFailsOutcome selected :=
  outcome.1

/-- The return of `Route8RateFailsOutcome_denseBelow_highEntropy`:
one `get` per fact of its ledger. -/
theorem route8RateFailsReturn_denseBelow_highEntropy
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .cubicBaseline) known]
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
    [FactKeys.Has (K .windowPackageUnrealized) known]
    [FactKeys.Has (K .denseDeficiencyBelow) known]
    [FactKeys.Has (K .remainderEntropyHigh) known]
    [FactKeys.Has (K .entropyPackageDemand) known]
    [FactKeys.Has (K .entropyCapBound) known] :
    Route8RateFailsOutcome_denseBelow_highEntropy selected :=
  ⟨route8RateFailsReturn history,
    (history.get (K .windowPackageUnrealized)).down,
    (history.get (K .denseDeficiencyBelow)).down,
    (history.get (K .remainderEntropyHigh)).down,
    (history.get (K .entropyPackageDemand)).down,
    (history.get (K .entropyCapBound)).down⟩

/-- **Node `[187]` (private-carrier rate failure)**:
`[158]` no (unrealized package), `[160]` first test yes (`τ(θ) < 1/4`), private-carrier rate failed;
`[50]` low, local-type coordinate nonrepetitive.
The generic residual and the 4 extra facts of this path
(46 facts). -/
abbrev Route8RateFailsOutcome_denseBelow_lowNonrepetitive (selected : EGInput.{u}) : Prop :=
  Route8RateFailsOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyBelow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderEntropyLow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .localTypeCoordinateNonrepetitive selected.object

theorem Route8RateFailsOutcome_denseBelow_lowNonrepetitive.toGeneric
    {selected : EGInput.{u}}
    (outcome : Route8RateFailsOutcome_denseBelow_lowNonrepetitive selected) :
    Route8RateFailsOutcome selected :=
  outcome.1

/-- The return of `Route8RateFailsOutcome_denseBelow_lowNonrepetitive`:
one `get` per fact of its ledger. -/
theorem route8RateFailsReturn_denseBelow_lowNonrepetitive
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .cubicBaseline) known]
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
    [FactKeys.Has (K .windowPackageUnrealized) known]
    [FactKeys.Has (K .denseDeficiencyBelow) known]
    [FactKeys.Has (K .remainderEntropyLow) known]
    [FactKeys.Has (K .localTypeCoordinateNonrepetitive) known] :
    Route8RateFailsOutcome_denseBelow_lowNonrepetitive selected :=
  ⟨route8RateFailsReturn history,
    (history.get (K .windowPackageUnrealized)).down,
    (history.get (K .denseDeficiencyBelow)).down,
    (history.get (K .remainderEntropyLow)).down,
    (history.get (K .localTypeCoordinateNonrepetitive)).down⟩

/-- **Node `[187]` (private-carrier rate failure)**:
`[158]` no (unrealized package), `[160]` first test yes (`τ(θ) < 1/4`), private-carrier rate failed;
`[50]` low, local-type coordinate repetitive, dominant rooted type wedge-free.
The generic residual and the 6 extra facts of this path
(48 facts). -/
abbrev Route8RateFailsOutcome_denseBelow_lowWedgeFree (selected : EGInput.{u}) : Prop :=
  Route8RateFailsOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyBelow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderEntropyLow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .localTypeCoordinateRepetitive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .dominantRootedType selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .dominantRootedTypeWedgeFree selected.object

theorem Route8RateFailsOutcome_denseBelow_lowWedgeFree.toGeneric
    {selected : EGInput.{u}}
    (outcome : Route8RateFailsOutcome_denseBelow_lowWedgeFree selected) :
    Route8RateFailsOutcome selected :=
  outcome.1

/-- The return of `Route8RateFailsOutcome_denseBelow_lowWedgeFree`:
one `get` per fact of its ledger. -/
theorem route8RateFailsReturn_denseBelow_lowWedgeFree
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .cubicBaseline) known]
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
    [FactKeys.Has (K .windowPackageUnrealized) known]
    [FactKeys.Has (K .denseDeficiencyBelow) known]
    [FactKeys.Has (K .remainderEntropyLow) known]
    [FactKeys.Has (K .localTypeCoordinateRepetitive) known]
    [FactKeys.Has (K .dominantRootedType) known]
    [FactKeys.Has (K .dominantRootedTypeWedgeFree) known] :
    Route8RateFailsOutcome_denseBelow_lowWedgeFree selected :=
  ⟨route8RateFailsReturn history,
    (history.get (K .windowPackageUnrealized)).down,
    (history.get (K .denseDeficiencyBelow)).down,
    (history.get (K .remainderEntropyLow)).down,
    (history.get (K .localTypeCoordinateRepetitive)).down,
    (history.get (K .dominantRootedType)).down,
    (history.get (K .dominantRootedTypeWedgeFree)).down⟩

/-- **Node `[187]` (private-carrier rate failure)**:
`[158]` no (unrealized package), `[160]` first test yes (`τ(θ) < 1/4`), private-carrier rate failed;
`[50]` low, local-type coordinate repetitive, dominant rooted wedge type.
The generic residual and the 7 extra facts of this path
(49 facts). -/
abbrev Route8RateFailsOutcome_denseBelow_lowWedge (selected : EGInput.{u}) : Prop :=
  Route8RateFailsOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyBelow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderEntropyLow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .localTypeCoordinateRepetitive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .dominantRootedType selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .dominantRootedWedgeType selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .independentObstructionTranslates selected.object

theorem Route8RateFailsOutcome_denseBelow_lowWedge.toGeneric
    {selected : EGInput.{u}}
    (outcome : Route8RateFailsOutcome_denseBelow_lowWedge selected) :
    Route8RateFailsOutcome selected :=
  outcome.1

/-- The return of `Route8RateFailsOutcome_denseBelow_lowWedge`:
one `get` per fact of its ledger. -/
theorem route8RateFailsReturn_denseBelow_lowWedge
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .cubicBaseline) known]
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
    [FactKeys.Has (K .windowPackageUnrealized) known]
    [FactKeys.Has (K .denseDeficiencyBelow) known]
    [FactKeys.Has (K .remainderEntropyLow) known]
    [FactKeys.Has (K .localTypeCoordinateRepetitive) known]
    [FactKeys.Has (K .dominantRootedType) known]
    [FactKeys.Has (K .dominantRootedWedgeType) known]
    [FactKeys.Has (K .independentObstructionTranslates) known] :
    Route8RateFailsOutcome_denseBelow_lowWedge selected :=
  ⟨route8RateFailsReturn history,
    (history.get (K .windowPackageUnrealized)).down,
    (history.get (K .denseDeficiencyBelow)).down,
    (history.get (K .remainderEntropyLow)).down,
    (history.get (K .localTypeCoordinateRepetitive)).down,
    (history.get (K .dominantRootedType)).down,
    (history.get (K .dominantRootedWedgeType)).down,
    (history.get (K .independentObstructionTranslates)).down⟩

end HypostructureErdos64EG
