import HypostructureErdos64EG.Assembly.Residuals

/-!
# Assembly: Residuals / Node153ResidualOutcome

Node `[153]`'s returned residual (`Node153ResidualOutcome`, G's first
equal-state pair on a retained cold corridor) is reached along 23 root paths,
and the single ExactLedger holds a different fact set on each of them.  Each
distinct fact set is its own open node, stated here as a subtype of the generic
residual: the generic conjunction (the 42 facts common to every path) together
with every extra fact of that path's ledger, one `Holds` conjunct per key, in
ledger order.  Each subtype has one return theorem reading every fact with one
`ExactLedger.get`, and projects to the generic residual.

Labels name the distinguishing decision arms: the `[158]`/`[160]` root arm
(`realized`, `denseAtOrAbove`, `denseRateFails`, `denseRate`), the
`[146]`/`[153]` cold arm (`coldBelow`, `linear`, `bounded`), the `[173]` exact
collision failure (`absorbed`), and the `[50]` entropy arm (`high`,
`lowNonrep`, `lowWedgeFree`, `lowWedge`).
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- **Node `[153]` residual, arms: `[158]` no, `[160]` first test no (`τ(θ) ≥ 1/4`); `[146]` yes (`θ < 1/78`, `[147]`); `[57]`/`[173]` exact collision fails (`[174]`); `[50]` high entropy, `[53]` entropy cap bound.**  Path: `selectedLedgerBoundary → selectedNearCubicBranch → selectedNearCubicSurvivorBranch → nearCubicUnrealized → nearCubicDensePassAtOrAbove → nearCubicLargeBudgetColdRate → selectedNetChargeContinuation → selectedAbsorbedGermPrerequisites`.
The generic residual and the 11 extra facts of this path's ledger
(53 facts). -/
abbrev Node153ResidualOutcome_denseAtOrAbove_coldBelow_absorbed_high (selected : EGInput.{u}) : Prop :=
  Node153ResidualOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyAtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8Below selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8Rate selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderEntropyHigh selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .entropyPackageDemand selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .entropyCapBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .largeBudgetResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .netDeficiencyCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .exactCollisionFails selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .absorbedConfigurationResidual selected.object

/-- `Node153ResidualOutcome_denseAtOrAbove_coldBelow_absorbed_high` is a subtype of the generic `[153]` residual. -/
theorem Node153ResidualOutcome_denseAtOrAbove_coldBelow_absorbed_high.toGeneric {selected : EGInput.{u}}
    (outcome : Node153ResidualOutcome_denseAtOrAbove_coldBelow_absorbed_high selected) : Node153ResidualOutcome selected :=
  outcome.1

/-- The return of `Node153ResidualOutcome_denseAtOrAbove_coldBelow_absorbed_high`: one `get` per fact of its ledger. -/
theorem node153Return_denseAtOrAbove_coldBelow_absorbed_high
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
    [FactKeys.Has (K .coldRepeatedStateResidual) known]
    [FactKeys.Has (K .windowPackageUnrealized) known]
    [FactKeys.Has (K .denseDeficiencyAtOrAbove) known]
    [FactKeys.Has (K .coldRoute8Below) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .remainderEntropyHigh) known]
    [FactKeys.Has (K .entropyPackageDemand) known]
    [FactKeys.Has (K .entropyCapBound) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .netDeficiencyCap) known]
    [FactKeys.Has (K .exactCollisionFails) known]
    [FactKeys.Has (K .absorbedConfigurationResidual) known] :
    Node153ResidualOutcome_denseAtOrAbove_coldBelow_absorbed_high selected :=
  ⟨node153Return history,
    (history.get (K .windowPackageUnrealized)).down,
    (history.get (K .denseDeficiencyAtOrAbove)).down,
    (history.get (K .coldRoute8Below)).down,
    (history.get (K .route8Rate)).down,
    (history.get (K .remainderEntropyHigh)).down,
    (history.get (K .entropyPackageDemand)).down,
    (history.get (K .entropyCapBound)).down,
    (history.get (K .largeBudgetResidual)).down,
    (history.get (K .netDeficiencyCap)).down,
    (history.get (K .exactCollisionFails)).down,
    (history.get (K .absorbedConfigurationResidual)).down⟩

/-- **Node `[153]` residual, arms: `[158]` no, `[160]` first test no (`τ(θ) ≥ 1/4`); `[146]` yes (`θ < 1/78`, `[147]`); `[57]`/`[173]` exact collision fails (`[174]`); `[50]` low entropy, local-type coordinate non-repetitive.**  Path: `selectedLedgerBoundary → selectedNearCubicBranch → selectedNearCubicSurvivorBranch → nearCubicUnrealized → nearCubicDensePassAtOrAbove → nearCubicLargeBudgetColdRate → selectedNetChargeContinuation → selectedAbsorbedGermPrerequisites`.
The generic residual and the 10 extra facts of this path's ledger
(52 facts). -/
abbrev Node153ResidualOutcome_denseAtOrAbove_coldBelow_absorbed_lowNonrep (selected : EGInput.{u}) : Prop :=
  Node153ResidualOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyAtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8Below selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8Rate selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderEntropyLow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .localTypeCoordinateNonrepetitive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .largeBudgetResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .netDeficiencyCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .exactCollisionFails selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .absorbedConfigurationResidual selected.object

/-- `Node153ResidualOutcome_denseAtOrAbove_coldBelow_absorbed_lowNonrep` is a subtype of the generic `[153]` residual. -/
theorem Node153ResidualOutcome_denseAtOrAbove_coldBelow_absorbed_lowNonrep.toGeneric {selected : EGInput.{u}}
    (outcome : Node153ResidualOutcome_denseAtOrAbove_coldBelow_absorbed_lowNonrep selected) : Node153ResidualOutcome selected :=
  outcome.1

/-- The return of `Node153ResidualOutcome_denseAtOrAbove_coldBelow_absorbed_lowNonrep`: one `get` per fact of its ledger. -/
theorem node153Return_denseAtOrAbove_coldBelow_absorbed_lowNonrep
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
    [FactKeys.Has (K .coldRepeatedStateResidual) known]
    [FactKeys.Has (K .windowPackageUnrealized) known]
    [FactKeys.Has (K .denseDeficiencyAtOrAbove) known]
    [FactKeys.Has (K .coldRoute8Below) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .remainderEntropyLow) known]
    [FactKeys.Has (K .localTypeCoordinateNonrepetitive) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .netDeficiencyCap) known]
    [FactKeys.Has (K .exactCollisionFails) known]
    [FactKeys.Has (K .absorbedConfigurationResidual) known] :
    Node153ResidualOutcome_denseAtOrAbove_coldBelow_absorbed_lowNonrep selected :=
  ⟨node153Return history,
    (history.get (K .windowPackageUnrealized)).down,
    (history.get (K .denseDeficiencyAtOrAbove)).down,
    (history.get (K .coldRoute8Below)).down,
    (history.get (K .route8Rate)).down,
    (history.get (K .remainderEntropyLow)).down,
    (history.get (K .localTypeCoordinateNonrepetitive)).down,
    (history.get (K .largeBudgetResidual)).down,
    (history.get (K .netDeficiencyCap)).down,
    (history.get (K .exactCollisionFails)).down,
    (history.get (K .absorbedConfigurationResidual)).down⟩

/-- **Node `[153]` residual, arms: `[158]` no, `[160]` first test no (`τ(θ) ≥ 1/4`); `[146]` yes (`θ < 1/78`, `[147]`); `[57]`/`[173]` exact collision fails (`[174]`); `[50]` low entropy, repetitive, dominant rooted type wedge-free.**  Path: `selectedLedgerBoundary → selectedNearCubicBranch → selectedNearCubicSurvivorBranch → nearCubicUnrealized → nearCubicDensePassAtOrAbove → nearCubicLargeBudgetColdRate → selectedNetChargeContinuation → selectedAbsorbedGermPrerequisites`.
The generic residual and the 12 extra facts of this path's ledger
(54 facts). -/
abbrev Node153ResidualOutcome_denseAtOrAbove_coldBelow_absorbed_lowWedgeFree (selected : EGInput.{u}) : Prop :=
  Node153ResidualOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyAtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8Below selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8Rate selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderEntropyLow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .localTypeCoordinateRepetitive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .dominantRootedType selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .dominantRootedTypeWedgeFree selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .largeBudgetResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .netDeficiencyCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .exactCollisionFails selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .absorbedConfigurationResidual selected.object

/-- `Node153ResidualOutcome_denseAtOrAbove_coldBelow_absorbed_lowWedgeFree` is a subtype of the generic `[153]` residual. -/
theorem Node153ResidualOutcome_denseAtOrAbove_coldBelow_absorbed_lowWedgeFree.toGeneric {selected : EGInput.{u}}
    (outcome : Node153ResidualOutcome_denseAtOrAbove_coldBelow_absorbed_lowWedgeFree selected) : Node153ResidualOutcome selected :=
  outcome.1

/-- The return of `Node153ResidualOutcome_denseAtOrAbove_coldBelow_absorbed_lowWedgeFree`: one `get` per fact of its ledger. -/
theorem node153Return_denseAtOrAbove_coldBelow_absorbed_lowWedgeFree
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
    [FactKeys.Has (K .coldRepeatedStateResidual) known]
    [FactKeys.Has (K .windowPackageUnrealized) known]
    [FactKeys.Has (K .denseDeficiencyAtOrAbove) known]
    [FactKeys.Has (K .coldRoute8Below) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .remainderEntropyLow) known]
    [FactKeys.Has (K .localTypeCoordinateRepetitive) known]
    [FactKeys.Has (K .dominantRootedType) known]
    [FactKeys.Has (K .dominantRootedTypeWedgeFree) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .netDeficiencyCap) known]
    [FactKeys.Has (K .exactCollisionFails) known]
    [FactKeys.Has (K .absorbedConfigurationResidual) known] :
    Node153ResidualOutcome_denseAtOrAbove_coldBelow_absorbed_lowWedgeFree selected :=
  ⟨node153Return history,
    (history.get (K .windowPackageUnrealized)).down,
    (history.get (K .denseDeficiencyAtOrAbove)).down,
    (history.get (K .coldRoute8Below)).down,
    (history.get (K .route8Rate)).down,
    (history.get (K .remainderEntropyLow)).down,
    (history.get (K .localTypeCoordinateRepetitive)).down,
    (history.get (K .dominantRootedType)).down,
    (history.get (K .dominantRootedTypeWedgeFree)).down,
    (history.get (K .largeBudgetResidual)).down,
    (history.get (K .netDeficiencyCap)).down,
    (history.get (K .exactCollisionFails)).down,
    (history.get (K .absorbedConfigurationResidual)).down⟩

/-- **Node `[153]` residual, arms: `[158]` no, `[160]` first test no (`τ(θ) ≥ 1/4`); `[146]` yes (`θ < 1/78`, `[147]`); `[57]`/`[173]` exact collision fails (`[174]`); `[50]` low entropy, repetitive, dominant rooted wedge type.**  Path: `selectedLedgerBoundary → selectedNearCubicBranch → selectedNearCubicSurvivorBranch → nearCubicUnrealized → nearCubicDensePassAtOrAbove → nearCubicLargeBudgetColdRate → selectedNetChargeContinuation → selectedAbsorbedGermPrerequisites`.
The generic residual and the 13 extra facts of this path's ledger
(55 facts). -/
abbrev Node153ResidualOutcome_denseAtOrAbove_coldBelow_absorbed_lowWedge (selected : EGInput.{u}) : Prop :=
  Node153ResidualOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyAtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8Below selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8Rate selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderEntropyLow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .localTypeCoordinateRepetitive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .dominantRootedType selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .dominantRootedWedgeType selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .independentObstructionTranslates selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .largeBudgetResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .netDeficiencyCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .exactCollisionFails selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .absorbedConfigurationResidual selected.object

/-- `Node153ResidualOutcome_denseAtOrAbove_coldBelow_absorbed_lowWedge` is a subtype of the generic `[153]` residual. -/
theorem Node153ResidualOutcome_denseAtOrAbove_coldBelow_absorbed_lowWedge.toGeneric {selected : EGInput.{u}}
    (outcome : Node153ResidualOutcome_denseAtOrAbove_coldBelow_absorbed_lowWedge selected) : Node153ResidualOutcome selected :=
  outcome.1

/-- The return of `Node153ResidualOutcome_denseAtOrAbove_coldBelow_absorbed_lowWedge`: one `get` per fact of its ledger. -/
theorem node153Return_denseAtOrAbove_coldBelow_absorbed_lowWedge
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
    [FactKeys.Has (K .coldRepeatedStateResidual) known]
    [FactKeys.Has (K .windowPackageUnrealized) known]
    [FactKeys.Has (K .denseDeficiencyAtOrAbove) known]
    [FactKeys.Has (K .coldRoute8Below) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .remainderEntropyLow) known]
    [FactKeys.Has (K .localTypeCoordinateRepetitive) known]
    [FactKeys.Has (K .dominantRootedType) known]
    [FactKeys.Has (K .dominantRootedWedgeType) known]
    [FactKeys.Has (K .independentObstructionTranslates) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .netDeficiencyCap) known]
    [FactKeys.Has (K .exactCollisionFails) known]
    [FactKeys.Has (K .absorbedConfigurationResidual) known] :
    Node153ResidualOutcome_denseAtOrAbove_coldBelow_absorbed_lowWedge selected :=
  ⟨node153Return history,
    (history.get (K .windowPackageUnrealized)).down,
    (history.get (K .denseDeficiencyAtOrAbove)).down,
    (history.get (K .coldRoute8Below)).down,
    (history.get (K .route8Rate)).down,
    (history.get (K .remainderEntropyLow)).down,
    (history.get (K .localTypeCoordinateRepetitive)).down,
    (history.get (K .dominantRootedType)).down,
    (history.get (K .dominantRootedWedgeType)).down,
    (history.get (K .independentObstructionTranslates)).down,
    (history.get (K .largeBudgetResidual)).down,
    (history.get (K .netDeficiencyCap)).down,
    (history.get (K .exactCollisionFails)).down,
    (history.get (K .absorbedConfigurationResidual)).down⟩

/-- **Node `[153]` residual, arms: `[158]` no, `[160]` first test no (`τ(θ) ≥ 1/4`); `[146]` no, `[153]` linear cold mass.**  Path: `selectedLedgerBoundary → selectedNearCubicBranch → selectedNearCubicSurvivorBranch → nearCubicUnrealized → nearCubicDensePassAtOrAbove → nearCubicDenseLinear`.
The generic residual and the 4 extra facts of this path's ledger
(46 facts). -/
abbrev Node153ResidualOutcome_denseAtOrAbove_linear (selected : EGInput.{u}) : Prop :=
  Node153ResidualOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyAtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8AtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMassLinear selected.object

/-- `Node153ResidualOutcome_denseAtOrAbove_linear` is a subtype of the generic `[153]` residual. -/
theorem Node153ResidualOutcome_denseAtOrAbove_linear.toGeneric {selected : EGInput.{u}}
    (outcome : Node153ResidualOutcome_denseAtOrAbove_linear selected) : Node153ResidualOutcome selected :=
  outcome.1

/-- The return of `Node153ResidualOutcome_denseAtOrAbove_linear`: one `get` per fact of its ledger. -/
theorem node153Return_denseAtOrAbove_linear
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
    [FactKeys.Has (K .coldRepeatedStateResidual) known]
    [FactKeys.Has (K .windowPackageUnrealized) known]
    [FactKeys.Has (K .denseDeficiencyAtOrAbove) known]
    [FactKeys.Has (K .coldRoute8AtOrAbove) known]
    [FactKeys.Has (K .coldMassLinear) known] :
    Node153ResidualOutcome_denseAtOrAbove_linear selected :=
  ⟨node153Return history,
    (history.get (K .windowPackageUnrealized)).down,
    (history.get (K .denseDeficiencyAtOrAbove)).down,
    (history.get (K .coldRoute8AtOrAbove)).down,
    (history.get (K .coldMassLinear)).down⟩

/-- **Node `[153]` residual, arms: `[158]` no, `[160]` first test no (`τ(θ) ≥ 1/4`); `[146]` no, `[153]` bounded cold mass (`[24]`), route-8 entry rate holds; `[57]`/`[173]` exact collision fails (`[174]`); `[50]` high entropy, `[53]` entropy cap bound.**  Path: `selectedLedgerBoundary → selectedNearCubicBranch → selectedNearCubicSurvivorBranch → nearCubicUnrealized → nearCubicDensePassAtOrAbove → nearCubicLargeBudgetDensityCap → nearCubicRouteEightEntry → selectedNetChargeContinuation → selectedAbsorbedGermPrerequisites`.
The generic residual and the 13 extra facts of this path's ledger
(55 facts). -/
abbrev Node153ResidualOutcome_denseAtOrAbove_bounded_absorbed_high (selected : EGInput.{u}) : Prop :=
  Node153ResidualOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyAtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8AtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMassBounded selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .densityCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderEntropyHigh selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .entropyPackageDemand selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .entropyCapBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .largeBudgetResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .netDeficiencyCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8Rate selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .exactCollisionFails selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .absorbedConfigurationResidual selected.object

/-- `Node153ResidualOutcome_denseAtOrAbove_bounded_absorbed_high` is a subtype of the generic `[153]` residual. -/
theorem Node153ResidualOutcome_denseAtOrAbove_bounded_absorbed_high.toGeneric {selected : EGInput.{u}}
    (outcome : Node153ResidualOutcome_denseAtOrAbove_bounded_absorbed_high selected) : Node153ResidualOutcome selected :=
  outcome.1

/-- The return of `Node153ResidualOutcome_denseAtOrAbove_bounded_absorbed_high`: one `get` per fact of its ledger. -/
theorem node153Return_denseAtOrAbove_bounded_absorbed_high
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
    [FactKeys.Has (K .coldRepeatedStateResidual) known]
    [FactKeys.Has (K .windowPackageUnrealized) known]
    [FactKeys.Has (K .denseDeficiencyAtOrAbove) known]
    [FactKeys.Has (K .coldRoute8AtOrAbove) known]
    [FactKeys.Has (K .coldMassBounded) known]
    [FactKeys.Has (K .densityCap) known]
    [FactKeys.Has (K .remainderEntropyHigh) known]
    [FactKeys.Has (K .entropyPackageDemand) known]
    [FactKeys.Has (K .entropyCapBound) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .netDeficiencyCap) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .exactCollisionFails) known]
    [FactKeys.Has (K .absorbedConfigurationResidual) known] :
    Node153ResidualOutcome_denseAtOrAbove_bounded_absorbed_high selected :=
  ⟨node153Return history,
    (history.get (K .windowPackageUnrealized)).down,
    (history.get (K .denseDeficiencyAtOrAbove)).down,
    (history.get (K .coldRoute8AtOrAbove)).down,
    (history.get (K .coldMassBounded)).down,
    (history.get (K .densityCap)).down,
    (history.get (K .remainderEntropyHigh)).down,
    (history.get (K .entropyPackageDemand)).down,
    (history.get (K .entropyCapBound)).down,
    (history.get (K .largeBudgetResidual)).down,
    (history.get (K .netDeficiencyCap)).down,
    (history.get (K .route8Rate)).down,
    (history.get (K .exactCollisionFails)).down,
    (history.get (K .absorbedConfigurationResidual)).down⟩

/-- **Node `[153]` residual, arms: `[158]` no, `[160]` first test no (`τ(θ) ≥ 1/4`); `[146]` no, `[153]` bounded cold mass (`[24]`), route-8 entry rate holds; `[57]`/`[173]` exact collision fails (`[174]`); `[50]` low entropy, local-type coordinate non-repetitive.**  Path: `selectedLedgerBoundary → selectedNearCubicBranch → selectedNearCubicSurvivorBranch → nearCubicUnrealized → nearCubicDensePassAtOrAbove → nearCubicLargeBudgetDensityCap → nearCubicRouteEightEntry → selectedNetChargeContinuation → selectedAbsorbedGermPrerequisites`.
The generic residual and the 12 extra facts of this path's ledger
(54 facts). -/
abbrev Node153ResidualOutcome_denseAtOrAbove_bounded_absorbed_lowNonrep (selected : EGInput.{u}) : Prop :=
  Node153ResidualOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyAtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8AtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMassBounded selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .densityCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderEntropyLow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .localTypeCoordinateNonrepetitive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .largeBudgetResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .netDeficiencyCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8Rate selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .exactCollisionFails selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .absorbedConfigurationResidual selected.object

/-- `Node153ResidualOutcome_denseAtOrAbove_bounded_absorbed_lowNonrep` is a subtype of the generic `[153]` residual. -/
theorem Node153ResidualOutcome_denseAtOrAbove_bounded_absorbed_lowNonrep.toGeneric {selected : EGInput.{u}}
    (outcome : Node153ResidualOutcome_denseAtOrAbove_bounded_absorbed_lowNonrep selected) : Node153ResidualOutcome selected :=
  outcome.1

/-- The return of `Node153ResidualOutcome_denseAtOrAbove_bounded_absorbed_lowNonrep`: one `get` per fact of its ledger. -/
theorem node153Return_denseAtOrAbove_bounded_absorbed_lowNonrep
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
    [FactKeys.Has (K .coldRepeatedStateResidual) known]
    [FactKeys.Has (K .windowPackageUnrealized) known]
    [FactKeys.Has (K .denseDeficiencyAtOrAbove) known]
    [FactKeys.Has (K .coldRoute8AtOrAbove) known]
    [FactKeys.Has (K .coldMassBounded) known]
    [FactKeys.Has (K .densityCap) known]
    [FactKeys.Has (K .remainderEntropyLow) known]
    [FactKeys.Has (K .localTypeCoordinateNonrepetitive) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .netDeficiencyCap) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .exactCollisionFails) known]
    [FactKeys.Has (K .absorbedConfigurationResidual) known] :
    Node153ResidualOutcome_denseAtOrAbove_bounded_absorbed_lowNonrep selected :=
  ⟨node153Return history,
    (history.get (K .windowPackageUnrealized)).down,
    (history.get (K .denseDeficiencyAtOrAbove)).down,
    (history.get (K .coldRoute8AtOrAbove)).down,
    (history.get (K .coldMassBounded)).down,
    (history.get (K .densityCap)).down,
    (history.get (K .remainderEntropyLow)).down,
    (history.get (K .localTypeCoordinateNonrepetitive)).down,
    (history.get (K .largeBudgetResidual)).down,
    (history.get (K .netDeficiencyCap)).down,
    (history.get (K .route8Rate)).down,
    (history.get (K .exactCollisionFails)).down,
    (history.get (K .absorbedConfigurationResidual)).down⟩

/-- **Node `[153]` residual, arms: `[158]` no, `[160]` first test no (`τ(θ) ≥ 1/4`); `[146]` no, `[153]` bounded cold mass (`[24]`), route-8 entry rate holds; `[57]`/`[173]` exact collision fails (`[174]`); `[50]` low entropy, repetitive, dominant rooted type wedge-free.**  Path: `selectedLedgerBoundary → selectedNearCubicBranch → selectedNearCubicSurvivorBranch → nearCubicUnrealized → nearCubicDensePassAtOrAbove → nearCubicLargeBudgetDensityCap → nearCubicRouteEightEntry → selectedNetChargeContinuation → selectedAbsorbedGermPrerequisites`.
The generic residual and the 14 extra facts of this path's ledger
(56 facts). -/
abbrev Node153ResidualOutcome_denseAtOrAbove_bounded_absorbed_lowWedgeFree (selected : EGInput.{u}) : Prop :=
  Node153ResidualOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyAtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8AtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMassBounded selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .densityCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderEntropyLow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .localTypeCoordinateRepetitive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .dominantRootedType selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .dominantRootedTypeWedgeFree selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .largeBudgetResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .netDeficiencyCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8Rate selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .exactCollisionFails selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .absorbedConfigurationResidual selected.object

/-- `Node153ResidualOutcome_denseAtOrAbove_bounded_absorbed_lowWedgeFree` is a subtype of the generic `[153]` residual. -/
theorem Node153ResidualOutcome_denseAtOrAbove_bounded_absorbed_lowWedgeFree.toGeneric {selected : EGInput.{u}}
    (outcome : Node153ResidualOutcome_denseAtOrAbove_bounded_absorbed_lowWedgeFree selected) : Node153ResidualOutcome selected :=
  outcome.1

/-- The return of `Node153ResidualOutcome_denseAtOrAbove_bounded_absorbed_lowWedgeFree`: one `get` per fact of its ledger. -/
theorem node153Return_denseAtOrAbove_bounded_absorbed_lowWedgeFree
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
    [FactKeys.Has (K .coldRepeatedStateResidual) known]
    [FactKeys.Has (K .windowPackageUnrealized) known]
    [FactKeys.Has (K .denseDeficiencyAtOrAbove) known]
    [FactKeys.Has (K .coldRoute8AtOrAbove) known]
    [FactKeys.Has (K .coldMassBounded) known]
    [FactKeys.Has (K .densityCap) known]
    [FactKeys.Has (K .remainderEntropyLow) known]
    [FactKeys.Has (K .localTypeCoordinateRepetitive) known]
    [FactKeys.Has (K .dominantRootedType) known]
    [FactKeys.Has (K .dominantRootedTypeWedgeFree) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .netDeficiencyCap) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .exactCollisionFails) known]
    [FactKeys.Has (K .absorbedConfigurationResidual) known] :
    Node153ResidualOutcome_denseAtOrAbove_bounded_absorbed_lowWedgeFree selected :=
  ⟨node153Return history,
    (history.get (K .windowPackageUnrealized)).down,
    (history.get (K .denseDeficiencyAtOrAbove)).down,
    (history.get (K .coldRoute8AtOrAbove)).down,
    (history.get (K .coldMassBounded)).down,
    (history.get (K .densityCap)).down,
    (history.get (K .remainderEntropyLow)).down,
    (history.get (K .localTypeCoordinateRepetitive)).down,
    (history.get (K .dominantRootedType)).down,
    (history.get (K .dominantRootedTypeWedgeFree)).down,
    (history.get (K .largeBudgetResidual)).down,
    (history.get (K .netDeficiencyCap)).down,
    (history.get (K .route8Rate)).down,
    (history.get (K .exactCollisionFails)).down,
    (history.get (K .absorbedConfigurationResidual)).down⟩

/-- **Node `[153]` residual, arms: `[158]` no, `[160]` first test no (`τ(θ) ≥ 1/4`); `[146]` no, `[153]` bounded cold mass (`[24]`), route-8 entry rate holds; `[57]`/`[173]` exact collision fails (`[174]`); `[50]` low entropy, repetitive, dominant rooted wedge type.**  Path: `selectedLedgerBoundary → selectedNearCubicBranch → selectedNearCubicSurvivorBranch → nearCubicUnrealized → nearCubicDensePassAtOrAbove → nearCubicLargeBudgetDensityCap → nearCubicRouteEightEntry → selectedNetChargeContinuation → selectedAbsorbedGermPrerequisites`.
The generic residual and the 15 extra facts of this path's ledger
(57 facts). -/
abbrev Node153ResidualOutcome_denseAtOrAbove_bounded_absorbed_lowWedge (selected : EGInput.{u}) : Prop :=
  Node153ResidualOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyAtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8AtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMassBounded selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .densityCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderEntropyLow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .localTypeCoordinateRepetitive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .dominantRootedType selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .dominantRootedWedgeType selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .independentObstructionTranslates selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .largeBudgetResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .netDeficiencyCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8Rate selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .exactCollisionFails selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .absorbedConfigurationResidual selected.object

/-- `Node153ResidualOutcome_denseAtOrAbove_bounded_absorbed_lowWedge` is a subtype of the generic `[153]` residual. -/
theorem Node153ResidualOutcome_denseAtOrAbove_bounded_absorbed_lowWedge.toGeneric {selected : EGInput.{u}}
    (outcome : Node153ResidualOutcome_denseAtOrAbove_bounded_absorbed_lowWedge selected) : Node153ResidualOutcome selected :=
  outcome.1

/-- The return of `Node153ResidualOutcome_denseAtOrAbove_bounded_absorbed_lowWedge`: one `get` per fact of its ledger. -/
theorem node153Return_denseAtOrAbove_bounded_absorbed_lowWedge
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
    [FactKeys.Has (K .coldRepeatedStateResidual) known]
    [FactKeys.Has (K .windowPackageUnrealized) known]
    [FactKeys.Has (K .denseDeficiencyAtOrAbove) known]
    [FactKeys.Has (K .coldRoute8AtOrAbove) known]
    [FactKeys.Has (K .coldMassBounded) known]
    [FactKeys.Has (K .densityCap) known]
    [FactKeys.Has (K .remainderEntropyLow) known]
    [FactKeys.Has (K .localTypeCoordinateRepetitive) known]
    [FactKeys.Has (K .dominantRootedType) known]
    [FactKeys.Has (K .dominantRootedWedgeType) known]
    [FactKeys.Has (K .independentObstructionTranslates) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .netDeficiencyCap) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .exactCollisionFails) known]
    [FactKeys.Has (K .absorbedConfigurationResidual) known] :
    Node153ResidualOutcome_denseAtOrAbove_bounded_absorbed_lowWedge selected :=
  ⟨node153Return history,
    (history.get (K .windowPackageUnrealized)).down,
    (history.get (K .denseDeficiencyAtOrAbove)).down,
    (history.get (K .coldRoute8AtOrAbove)).down,
    (history.get (K .coldMassBounded)).down,
    (history.get (K .densityCap)).down,
    (history.get (K .remainderEntropyLow)).down,
    (history.get (K .localTypeCoordinateRepetitive)).down,
    (history.get (K .dominantRootedType)).down,
    (history.get (K .dominantRootedWedgeType)).down,
    (history.get (K .independentObstructionTranslates)).down,
    (history.get (K .largeBudgetResidual)).down,
    (history.get (K .netDeficiencyCap)).down,
    (history.get (K .route8Rate)).down,
    (history.get (K .exactCollisionFails)).down,
    (history.get (K .absorbedConfigurationResidual)).down⟩

/-- **Node `[153]` residual, arms: `[158]` no, `[160]` first test yes, second test no (private-carrier rate fails); `[146]` no, `[153]` linear cold mass.**  Path: `selectedLedgerBoundary → selectedNearCubicBranch → selectedNearCubicSurvivorBranch → nearCubicUnrealized → nearCubicDensePassRateFailed → nearCubicDenseLinear`.
The generic residual and the 5 extra facts of this path's ledger
(47 facts). -/
abbrev Node153ResidualOutcome_denseRateFails_linear (selected : EGInput.{u}) : Prop :=
  Node153ResidualOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyBelow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8RateFails selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8AtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMassLinear selected.object

/-- `Node153ResidualOutcome_denseRateFails_linear` is a subtype of the generic `[153]` residual. -/
theorem Node153ResidualOutcome_denseRateFails_linear.toGeneric {selected : EGInput.{u}}
    (outcome : Node153ResidualOutcome_denseRateFails_linear selected) : Node153ResidualOutcome selected :=
  outcome.1

/-- The return of `Node153ResidualOutcome_denseRateFails_linear`: one `get` per fact of its ledger. -/
theorem node153Return_denseRateFails_linear
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
    [FactKeys.Has (K .coldRepeatedStateResidual) known]
    [FactKeys.Has (K .windowPackageUnrealized) known]
    [FactKeys.Has (K .denseDeficiencyBelow) known]
    [FactKeys.Has (K .route8RateFails) known]
    [FactKeys.Has (K .coldRoute8AtOrAbove) known]
    [FactKeys.Has (K .coldMassLinear) known] :
    Node153ResidualOutcome_denseRateFails_linear selected :=
  ⟨node153Return history,
    (history.get (K .windowPackageUnrealized)).down,
    (history.get (K .denseDeficiencyBelow)).down,
    (history.get (K .route8RateFails)).down,
    (history.get (K .coldRoute8AtOrAbove)).down,
    (history.get (K .coldMassLinear)).down⟩

/-- **Node `[153]` residual, arms: `[158]` no, `[160]` both tests yes (`[161]`); `[57]`/`[173]` exact collision fails (`[174]`); `[50]` high entropy, `[53]` entropy cap bound.**  Path: `selectedLedgerBoundary → selectedNearCubicBranch → selectedNearCubicSurvivorBranch → nearCubicUnrealized → nearCubicLargeBudgetDenseRate → selectedNetChargeContinuation → selectedAbsorbedGermPrerequisites`.
The generic residual and the 10 extra facts of this path's ledger
(52 facts). -/
abbrev Node153ResidualOutcome_denseRate_absorbed_high (selected : EGInput.{u}) : Prop :=
  Node153ResidualOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyBelow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8Rate selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderEntropyHigh selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .entropyPackageDemand selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .entropyCapBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .largeBudgetResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .netDeficiencyCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .exactCollisionFails selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .absorbedConfigurationResidual selected.object

/-- `Node153ResidualOutcome_denseRate_absorbed_high` is a subtype of the generic `[153]` residual. -/
theorem Node153ResidualOutcome_denseRate_absorbed_high.toGeneric {selected : EGInput.{u}}
    (outcome : Node153ResidualOutcome_denseRate_absorbed_high selected) : Node153ResidualOutcome selected :=
  outcome.1

/-- The return of `Node153ResidualOutcome_denseRate_absorbed_high`: one `get` per fact of its ledger. -/
theorem node153Return_denseRate_absorbed_high
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
    [FactKeys.Has (K .coldRepeatedStateResidual) known]
    [FactKeys.Has (K .windowPackageUnrealized) known]
    [FactKeys.Has (K .denseDeficiencyBelow) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .remainderEntropyHigh) known]
    [FactKeys.Has (K .entropyPackageDemand) known]
    [FactKeys.Has (K .entropyCapBound) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .netDeficiencyCap) known]
    [FactKeys.Has (K .exactCollisionFails) known]
    [FactKeys.Has (K .absorbedConfigurationResidual) known] :
    Node153ResidualOutcome_denseRate_absorbed_high selected :=
  ⟨node153Return history,
    (history.get (K .windowPackageUnrealized)).down,
    (history.get (K .denseDeficiencyBelow)).down,
    (history.get (K .route8Rate)).down,
    (history.get (K .remainderEntropyHigh)).down,
    (history.get (K .entropyPackageDemand)).down,
    (history.get (K .entropyCapBound)).down,
    (history.get (K .largeBudgetResidual)).down,
    (history.get (K .netDeficiencyCap)).down,
    (history.get (K .exactCollisionFails)).down,
    (history.get (K .absorbedConfigurationResidual)).down⟩

/-- **Node `[153]` residual, arms: `[158]` no, `[160]` both tests yes (`[161]`); `[57]`/`[173]` exact collision fails (`[174]`); `[50]` low entropy, local-type coordinate non-repetitive.**  Path: `selectedLedgerBoundary → selectedNearCubicBranch → selectedNearCubicSurvivorBranch → nearCubicUnrealized → nearCubicLargeBudgetDenseRate → selectedNetChargeContinuation → selectedAbsorbedGermPrerequisites`.
The generic residual and the 9 extra facts of this path's ledger
(51 facts). -/
abbrev Node153ResidualOutcome_denseRate_absorbed_lowNonrep (selected : EGInput.{u}) : Prop :=
  Node153ResidualOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyBelow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8Rate selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderEntropyLow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .localTypeCoordinateNonrepetitive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .largeBudgetResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .netDeficiencyCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .exactCollisionFails selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .absorbedConfigurationResidual selected.object

/-- `Node153ResidualOutcome_denseRate_absorbed_lowNonrep` is a subtype of the generic `[153]` residual. -/
theorem Node153ResidualOutcome_denseRate_absorbed_lowNonrep.toGeneric {selected : EGInput.{u}}
    (outcome : Node153ResidualOutcome_denseRate_absorbed_lowNonrep selected) : Node153ResidualOutcome selected :=
  outcome.1

/-- The return of `Node153ResidualOutcome_denseRate_absorbed_lowNonrep`: one `get` per fact of its ledger. -/
theorem node153Return_denseRate_absorbed_lowNonrep
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
    [FactKeys.Has (K .coldRepeatedStateResidual) known]
    [FactKeys.Has (K .windowPackageUnrealized) known]
    [FactKeys.Has (K .denseDeficiencyBelow) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .remainderEntropyLow) known]
    [FactKeys.Has (K .localTypeCoordinateNonrepetitive) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .netDeficiencyCap) known]
    [FactKeys.Has (K .exactCollisionFails) known]
    [FactKeys.Has (K .absorbedConfigurationResidual) known] :
    Node153ResidualOutcome_denseRate_absorbed_lowNonrep selected :=
  ⟨node153Return history,
    (history.get (K .windowPackageUnrealized)).down,
    (history.get (K .denseDeficiencyBelow)).down,
    (history.get (K .route8Rate)).down,
    (history.get (K .remainderEntropyLow)).down,
    (history.get (K .localTypeCoordinateNonrepetitive)).down,
    (history.get (K .largeBudgetResidual)).down,
    (history.get (K .netDeficiencyCap)).down,
    (history.get (K .exactCollisionFails)).down,
    (history.get (K .absorbedConfigurationResidual)).down⟩

/-- **Node `[153]` residual, arms: `[158]` no, `[160]` both tests yes (`[161]`); `[57]`/`[173]` exact collision fails (`[174]`); `[50]` low entropy, repetitive, dominant rooted type wedge-free.**  Path: `selectedLedgerBoundary → selectedNearCubicBranch → selectedNearCubicSurvivorBranch → nearCubicUnrealized → nearCubicLargeBudgetDenseRate → selectedNetChargeContinuation → selectedAbsorbedGermPrerequisites`.
The generic residual and the 11 extra facts of this path's ledger
(53 facts). -/
abbrev Node153ResidualOutcome_denseRate_absorbed_lowWedgeFree (selected : EGInput.{u}) : Prop :=
  Node153ResidualOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyBelow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8Rate selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderEntropyLow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .localTypeCoordinateRepetitive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .dominantRootedType selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .dominantRootedTypeWedgeFree selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .largeBudgetResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .netDeficiencyCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .exactCollisionFails selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .absorbedConfigurationResidual selected.object

/-- `Node153ResidualOutcome_denseRate_absorbed_lowWedgeFree` is a subtype of the generic `[153]` residual. -/
theorem Node153ResidualOutcome_denseRate_absorbed_lowWedgeFree.toGeneric {selected : EGInput.{u}}
    (outcome : Node153ResidualOutcome_denseRate_absorbed_lowWedgeFree selected) : Node153ResidualOutcome selected :=
  outcome.1

/-- The return of `Node153ResidualOutcome_denseRate_absorbed_lowWedgeFree`: one `get` per fact of its ledger. -/
theorem node153Return_denseRate_absorbed_lowWedgeFree
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
    [FactKeys.Has (K .coldRepeatedStateResidual) known]
    [FactKeys.Has (K .windowPackageUnrealized) known]
    [FactKeys.Has (K .denseDeficiencyBelow) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .remainderEntropyLow) known]
    [FactKeys.Has (K .localTypeCoordinateRepetitive) known]
    [FactKeys.Has (K .dominantRootedType) known]
    [FactKeys.Has (K .dominantRootedTypeWedgeFree) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .netDeficiencyCap) known]
    [FactKeys.Has (K .exactCollisionFails) known]
    [FactKeys.Has (K .absorbedConfigurationResidual) known] :
    Node153ResidualOutcome_denseRate_absorbed_lowWedgeFree selected :=
  ⟨node153Return history,
    (history.get (K .windowPackageUnrealized)).down,
    (history.get (K .denseDeficiencyBelow)).down,
    (history.get (K .route8Rate)).down,
    (history.get (K .remainderEntropyLow)).down,
    (history.get (K .localTypeCoordinateRepetitive)).down,
    (history.get (K .dominantRootedType)).down,
    (history.get (K .dominantRootedTypeWedgeFree)).down,
    (history.get (K .largeBudgetResidual)).down,
    (history.get (K .netDeficiencyCap)).down,
    (history.get (K .exactCollisionFails)).down,
    (history.get (K .absorbedConfigurationResidual)).down⟩

/-- **Node `[153]` residual, arms: `[158]` no, `[160]` both tests yes (`[161]`); `[57]`/`[173]` exact collision fails (`[174]`); `[50]` low entropy, repetitive, dominant rooted wedge type.**  Path: `selectedLedgerBoundary → selectedNearCubicBranch → selectedNearCubicSurvivorBranch → nearCubicUnrealized → nearCubicLargeBudgetDenseRate → selectedNetChargeContinuation → selectedAbsorbedGermPrerequisites`.
The generic residual and the 12 extra facts of this path's ledger
(54 facts). -/
abbrev Node153ResidualOutcome_denseRate_absorbed_lowWedge (selected : EGInput.{u}) : Prop :=
  Node153ResidualOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyBelow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8Rate selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderEntropyLow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .localTypeCoordinateRepetitive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .dominantRootedType selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .dominantRootedWedgeType selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .independentObstructionTranslates selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .largeBudgetResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .netDeficiencyCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .exactCollisionFails selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .absorbedConfigurationResidual selected.object

/-- `Node153ResidualOutcome_denseRate_absorbed_lowWedge` is a subtype of the generic `[153]` residual. -/
theorem Node153ResidualOutcome_denseRate_absorbed_lowWedge.toGeneric {selected : EGInput.{u}}
    (outcome : Node153ResidualOutcome_denseRate_absorbed_lowWedge selected) : Node153ResidualOutcome selected :=
  outcome.1

/-- The return of `Node153ResidualOutcome_denseRate_absorbed_lowWedge`: one `get` per fact of its ledger. -/
theorem node153Return_denseRate_absorbed_lowWedge
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
    [FactKeys.Has (K .coldRepeatedStateResidual) known]
    [FactKeys.Has (K .windowPackageUnrealized) known]
    [FactKeys.Has (K .denseDeficiencyBelow) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .remainderEntropyLow) known]
    [FactKeys.Has (K .localTypeCoordinateRepetitive) known]
    [FactKeys.Has (K .dominantRootedType) known]
    [FactKeys.Has (K .dominantRootedWedgeType) known]
    [FactKeys.Has (K .independentObstructionTranslates) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .netDeficiencyCap) known]
    [FactKeys.Has (K .exactCollisionFails) known]
    [FactKeys.Has (K .absorbedConfigurationResidual) known] :
    Node153ResidualOutcome_denseRate_absorbed_lowWedge selected :=
  ⟨node153Return history,
    (history.get (K .windowPackageUnrealized)).down,
    (history.get (K .denseDeficiencyBelow)).down,
    (history.get (K .route8Rate)).down,
    (history.get (K .remainderEntropyLow)).down,
    (history.get (K .localTypeCoordinateRepetitive)).down,
    (history.get (K .dominantRootedType)).down,
    (history.get (K .dominantRootedWedgeType)).down,
    (history.get (K .independentObstructionTranslates)).down,
    (history.get (K .largeBudgetResidual)).down,
    (history.get (K .netDeficiencyCap)).down,
    (history.get (K .exactCollisionFails)).down,
    (history.get (K .absorbedConfigurationResidual)).down⟩

/-- **Node `[153]` residual, arms: `[158]` yes (window package realized); `[146]` yes (`θ < 1/78`, `[147]`); `[57]`/`[173]` exact collision fails (`[174]`); `[50]` high entropy, `[53]` entropy cap bound.**  Path: `selectedLedgerBoundary → selectedNearCubicBranch → selectedNearCubicSurvivorBranch → nearCubicRealized → nearCubicLargeBudgetColdRate → selectedNetChargeContinuation → selectedAbsorbedGermPrerequisites`.
The generic residual and the 10 extra facts of this path's ledger
(52 facts). -/
abbrev Node153ResidualOutcome_realized_coldBelow_absorbed_high (selected : EGInput.{u}) : Prop :=
  Node153ResidualOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageRealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8Below selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8Rate selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderEntropyHigh selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .entropyPackageDemand selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .entropyCapBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .largeBudgetResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .netDeficiencyCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .exactCollisionFails selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .absorbedConfigurationResidual selected.object

/-- `Node153ResidualOutcome_realized_coldBelow_absorbed_high` is a subtype of the generic `[153]` residual. -/
theorem Node153ResidualOutcome_realized_coldBelow_absorbed_high.toGeneric {selected : EGInput.{u}}
    (outcome : Node153ResidualOutcome_realized_coldBelow_absorbed_high selected) : Node153ResidualOutcome selected :=
  outcome.1

/-- The return of `Node153ResidualOutcome_realized_coldBelow_absorbed_high`: one `get` per fact of its ledger. -/
theorem node153Return_realized_coldBelow_absorbed_high
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
    [FactKeys.Has (K .coldRepeatedStateResidual) known]
    [FactKeys.Has (K .windowPackageRealized) known]
    [FactKeys.Has (K .coldRoute8Below) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .remainderEntropyHigh) known]
    [FactKeys.Has (K .entropyPackageDemand) known]
    [FactKeys.Has (K .entropyCapBound) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .netDeficiencyCap) known]
    [FactKeys.Has (K .exactCollisionFails) known]
    [FactKeys.Has (K .absorbedConfigurationResidual) known] :
    Node153ResidualOutcome_realized_coldBelow_absorbed_high selected :=
  ⟨node153Return history,
    (history.get (K .windowPackageRealized)).down,
    (history.get (K .coldRoute8Below)).down,
    (history.get (K .route8Rate)).down,
    (history.get (K .remainderEntropyHigh)).down,
    (history.get (K .entropyPackageDemand)).down,
    (history.get (K .entropyCapBound)).down,
    (history.get (K .largeBudgetResidual)).down,
    (history.get (K .netDeficiencyCap)).down,
    (history.get (K .exactCollisionFails)).down,
    (history.get (K .absorbedConfigurationResidual)).down⟩

/-- **Node `[153]` residual, arms: `[158]` yes (window package realized); `[146]` yes (`θ < 1/78`, `[147]`); `[57]`/`[173]` exact collision fails (`[174]`); `[50]` low entropy, local-type coordinate non-repetitive.**  Path: `selectedLedgerBoundary → selectedNearCubicBranch → selectedNearCubicSurvivorBranch → nearCubicRealized → nearCubicLargeBudgetColdRate → selectedNetChargeContinuation → selectedAbsorbedGermPrerequisites`.
The generic residual and the 9 extra facts of this path's ledger
(51 facts). -/
abbrev Node153ResidualOutcome_realized_coldBelow_absorbed_lowNonrep (selected : EGInput.{u}) : Prop :=
  Node153ResidualOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageRealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8Below selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8Rate selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderEntropyLow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .localTypeCoordinateNonrepetitive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .largeBudgetResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .netDeficiencyCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .exactCollisionFails selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .absorbedConfigurationResidual selected.object

/-- `Node153ResidualOutcome_realized_coldBelow_absorbed_lowNonrep` is a subtype of the generic `[153]` residual. -/
theorem Node153ResidualOutcome_realized_coldBelow_absorbed_lowNonrep.toGeneric {selected : EGInput.{u}}
    (outcome : Node153ResidualOutcome_realized_coldBelow_absorbed_lowNonrep selected) : Node153ResidualOutcome selected :=
  outcome.1

/-- The return of `Node153ResidualOutcome_realized_coldBelow_absorbed_lowNonrep`: one `get` per fact of its ledger. -/
theorem node153Return_realized_coldBelow_absorbed_lowNonrep
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
    [FactKeys.Has (K .coldRepeatedStateResidual) known]
    [FactKeys.Has (K .windowPackageRealized) known]
    [FactKeys.Has (K .coldRoute8Below) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .remainderEntropyLow) known]
    [FactKeys.Has (K .localTypeCoordinateNonrepetitive) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .netDeficiencyCap) known]
    [FactKeys.Has (K .exactCollisionFails) known]
    [FactKeys.Has (K .absorbedConfigurationResidual) known] :
    Node153ResidualOutcome_realized_coldBelow_absorbed_lowNonrep selected :=
  ⟨node153Return history,
    (history.get (K .windowPackageRealized)).down,
    (history.get (K .coldRoute8Below)).down,
    (history.get (K .route8Rate)).down,
    (history.get (K .remainderEntropyLow)).down,
    (history.get (K .localTypeCoordinateNonrepetitive)).down,
    (history.get (K .largeBudgetResidual)).down,
    (history.get (K .netDeficiencyCap)).down,
    (history.get (K .exactCollisionFails)).down,
    (history.get (K .absorbedConfigurationResidual)).down⟩

/-- **Node `[153]` residual, arms: `[158]` yes (window package realized); `[146]` yes (`θ < 1/78`, `[147]`); `[57]`/`[173]` exact collision fails (`[174]`); `[50]` low entropy, repetitive, dominant rooted type wedge-free.**  Path: `selectedLedgerBoundary → selectedNearCubicBranch → selectedNearCubicSurvivorBranch → nearCubicRealized → nearCubicLargeBudgetColdRate → selectedNetChargeContinuation → selectedAbsorbedGermPrerequisites`.
The generic residual and the 11 extra facts of this path's ledger
(53 facts). -/
abbrev Node153ResidualOutcome_realized_coldBelow_absorbed_lowWedgeFree (selected : EGInput.{u}) : Prop :=
  Node153ResidualOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageRealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8Below selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8Rate selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderEntropyLow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .localTypeCoordinateRepetitive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .dominantRootedType selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .dominantRootedTypeWedgeFree selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .largeBudgetResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .netDeficiencyCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .exactCollisionFails selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .absorbedConfigurationResidual selected.object

/-- `Node153ResidualOutcome_realized_coldBelow_absorbed_lowWedgeFree` is a subtype of the generic `[153]` residual. -/
theorem Node153ResidualOutcome_realized_coldBelow_absorbed_lowWedgeFree.toGeneric {selected : EGInput.{u}}
    (outcome : Node153ResidualOutcome_realized_coldBelow_absorbed_lowWedgeFree selected) : Node153ResidualOutcome selected :=
  outcome.1

/-- The return of `Node153ResidualOutcome_realized_coldBelow_absorbed_lowWedgeFree`: one `get` per fact of its ledger. -/
theorem node153Return_realized_coldBelow_absorbed_lowWedgeFree
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
    [FactKeys.Has (K .coldRepeatedStateResidual) known]
    [FactKeys.Has (K .windowPackageRealized) known]
    [FactKeys.Has (K .coldRoute8Below) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .remainderEntropyLow) known]
    [FactKeys.Has (K .localTypeCoordinateRepetitive) known]
    [FactKeys.Has (K .dominantRootedType) known]
    [FactKeys.Has (K .dominantRootedTypeWedgeFree) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .netDeficiencyCap) known]
    [FactKeys.Has (K .exactCollisionFails) known]
    [FactKeys.Has (K .absorbedConfigurationResidual) known] :
    Node153ResidualOutcome_realized_coldBelow_absorbed_lowWedgeFree selected :=
  ⟨node153Return history,
    (history.get (K .windowPackageRealized)).down,
    (history.get (K .coldRoute8Below)).down,
    (history.get (K .route8Rate)).down,
    (history.get (K .remainderEntropyLow)).down,
    (history.get (K .localTypeCoordinateRepetitive)).down,
    (history.get (K .dominantRootedType)).down,
    (history.get (K .dominantRootedTypeWedgeFree)).down,
    (history.get (K .largeBudgetResidual)).down,
    (history.get (K .netDeficiencyCap)).down,
    (history.get (K .exactCollisionFails)).down,
    (history.get (K .absorbedConfigurationResidual)).down⟩

/-- **Node `[153]` residual, arms: `[158]` yes (window package realized); `[146]` yes (`θ < 1/78`, `[147]`); `[57]`/`[173]` exact collision fails (`[174]`); `[50]` low entropy, repetitive, dominant rooted wedge type.**  Path: `selectedLedgerBoundary → selectedNearCubicBranch → selectedNearCubicSurvivorBranch → nearCubicRealized → nearCubicLargeBudgetColdRate → selectedNetChargeContinuation → selectedAbsorbedGermPrerequisites`.
The generic residual and the 12 extra facts of this path's ledger
(54 facts). -/
abbrev Node153ResidualOutcome_realized_coldBelow_absorbed_lowWedge (selected : EGInput.{u}) : Prop :=
  Node153ResidualOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageRealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8Below selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8Rate selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderEntropyLow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .localTypeCoordinateRepetitive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .dominantRootedType selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .dominantRootedWedgeType selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .independentObstructionTranslates selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .largeBudgetResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .netDeficiencyCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .exactCollisionFails selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .absorbedConfigurationResidual selected.object

/-- `Node153ResidualOutcome_realized_coldBelow_absorbed_lowWedge` is a subtype of the generic `[153]` residual. -/
theorem Node153ResidualOutcome_realized_coldBelow_absorbed_lowWedge.toGeneric {selected : EGInput.{u}}
    (outcome : Node153ResidualOutcome_realized_coldBelow_absorbed_lowWedge selected) : Node153ResidualOutcome selected :=
  outcome.1

/-- The return of `Node153ResidualOutcome_realized_coldBelow_absorbed_lowWedge`: one `get` per fact of its ledger. -/
theorem node153Return_realized_coldBelow_absorbed_lowWedge
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
    [FactKeys.Has (K .coldRepeatedStateResidual) known]
    [FactKeys.Has (K .windowPackageRealized) known]
    [FactKeys.Has (K .coldRoute8Below) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .remainderEntropyLow) known]
    [FactKeys.Has (K .localTypeCoordinateRepetitive) known]
    [FactKeys.Has (K .dominantRootedType) known]
    [FactKeys.Has (K .dominantRootedWedgeType) known]
    [FactKeys.Has (K .independentObstructionTranslates) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .netDeficiencyCap) known]
    [FactKeys.Has (K .exactCollisionFails) known]
    [FactKeys.Has (K .absorbedConfigurationResidual) known] :
    Node153ResidualOutcome_realized_coldBelow_absorbed_lowWedge selected :=
  ⟨node153Return history,
    (history.get (K .windowPackageRealized)).down,
    (history.get (K .coldRoute8Below)).down,
    (history.get (K .route8Rate)).down,
    (history.get (K .remainderEntropyLow)).down,
    (history.get (K .localTypeCoordinateRepetitive)).down,
    (history.get (K .dominantRootedType)).down,
    (history.get (K .dominantRootedWedgeType)).down,
    (history.get (K .independentObstructionTranslates)).down,
    (history.get (K .largeBudgetResidual)).down,
    (history.get (K .netDeficiencyCap)).down,
    (history.get (K .exactCollisionFails)).down,
    (history.get (K .absorbedConfigurationResidual)).down⟩

/-- **Node `[153]` residual, arms: `[158]` yes (window package realized); `[146]` no, `[153]` bounded cold mass (`[24]`), route-8 entry rate holds; `[57]`/`[173]` exact collision fails (`[174]`); `[50]` high entropy, `[53]` entropy cap bound.**  Path: `selectedLedgerBoundary → selectedNearCubicBranch → selectedNearCubicSurvivorBranch → nearCubicRealized → nearCubicLargeBudgetDensityCap → nearCubicRouteEightEntry → selectedNetChargeContinuation → selectedAbsorbedGermPrerequisites`.
The generic residual and the 12 extra facts of this path's ledger
(54 facts). -/
abbrev Node153ResidualOutcome_realized_bounded_absorbed_high (selected : EGInput.{u}) : Prop :=
  Node153ResidualOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageRealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8AtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMassBounded selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .densityCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderEntropyHigh selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .entropyPackageDemand selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .entropyCapBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .largeBudgetResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .netDeficiencyCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8Rate selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .exactCollisionFails selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .absorbedConfigurationResidual selected.object

/-- `Node153ResidualOutcome_realized_bounded_absorbed_high` is a subtype of the generic `[153]` residual. -/
theorem Node153ResidualOutcome_realized_bounded_absorbed_high.toGeneric {selected : EGInput.{u}}
    (outcome : Node153ResidualOutcome_realized_bounded_absorbed_high selected) : Node153ResidualOutcome selected :=
  outcome.1

/-- The return of `Node153ResidualOutcome_realized_bounded_absorbed_high`: one `get` per fact of its ledger. -/
theorem node153Return_realized_bounded_absorbed_high
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
    [FactKeys.Has (K .coldRepeatedStateResidual) known]
    [FactKeys.Has (K .windowPackageRealized) known]
    [FactKeys.Has (K .coldRoute8AtOrAbove) known]
    [FactKeys.Has (K .coldMassBounded) known]
    [FactKeys.Has (K .densityCap) known]
    [FactKeys.Has (K .remainderEntropyHigh) known]
    [FactKeys.Has (K .entropyPackageDemand) known]
    [FactKeys.Has (K .entropyCapBound) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .netDeficiencyCap) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .exactCollisionFails) known]
    [FactKeys.Has (K .absorbedConfigurationResidual) known] :
    Node153ResidualOutcome_realized_bounded_absorbed_high selected :=
  ⟨node153Return history,
    (history.get (K .windowPackageRealized)).down,
    (history.get (K .coldRoute8AtOrAbove)).down,
    (history.get (K .coldMassBounded)).down,
    (history.get (K .densityCap)).down,
    (history.get (K .remainderEntropyHigh)).down,
    (history.get (K .entropyPackageDemand)).down,
    (history.get (K .entropyCapBound)).down,
    (history.get (K .largeBudgetResidual)).down,
    (history.get (K .netDeficiencyCap)).down,
    (history.get (K .route8Rate)).down,
    (history.get (K .exactCollisionFails)).down,
    (history.get (K .absorbedConfigurationResidual)).down⟩

/-- **Node `[153]` residual, arms: `[158]` yes (window package realized); `[146]` no, `[153]` bounded cold mass (`[24]`), route-8 entry rate holds; `[57]`/`[173]` exact collision fails (`[174]`); `[50]` low entropy, local-type coordinate non-repetitive.**  Path: `selectedLedgerBoundary → selectedNearCubicBranch → selectedNearCubicSurvivorBranch → nearCubicRealized → nearCubicLargeBudgetDensityCap → nearCubicRouteEightEntry → selectedNetChargeContinuation → selectedAbsorbedGermPrerequisites`.
The generic residual and the 11 extra facts of this path's ledger
(53 facts). -/
abbrev Node153ResidualOutcome_realized_bounded_absorbed_lowNonrep (selected : EGInput.{u}) : Prop :=
  Node153ResidualOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageRealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8AtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMassBounded selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .densityCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderEntropyLow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .localTypeCoordinateNonrepetitive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .largeBudgetResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .netDeficiencyCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8Rate selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .exactCollisionFails selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .absorbedConfigurationResidual selected.object

/-- `Node153ResidualOutcome_realized_bounded_absorbed_lowNonrep` is a subtype of the generic `[153]` residual. -/
theorem Node153ResidualOutcome_realized_bounded_absorbed_lowNonrep.toGeneric {selected : EGInput.{u}}
    (outcome : Node153ResidualOutcome_realized_bounded_absorbed_lowNonrep selected) : Node153ResidualOutcome selected :=
  outcome.1

/-- The return of `Node153ResidualOutcome_realized_bounded_absorbed_lowNonrep`: one `get` per fact of its ledger. -/
theorem node153Return_realized_bounded_absorbed_lowNonrep
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
    [FactKeys.Has (K .coldRepeatedStateResidual) known]
    [FactKeys.Has (K .windowPackageRealized) known]
    [FactKeys.Has (K .coldRoute8AtOrAbove) known]
    [FactKeys.Has (K .coldMassBounded) known]
    [FactKeys.Has (K .densityCap) known]
    [FactKeys.Has (K .remainderEntropyLow) known]
    [FactKeys.Has (K .localTypeCoordinateNonrepetitive) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .netDeficiencyCap) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .exactCollisionFails) known]
    [FactKeys.Has (K .absorbedConfigurationResidual) known] :
    Node153ResidualOutcome_realized_bounded_absorbed_lowNonrep selected :=
  ⟨node153Return history,
    (history.get (K .windowPackageRealized)).down,
    (history.get (K .coldRoute8AtOrAbove)).down,
    (history.get (K .coldMassBounded)).down,
    (history.get (K .densityCap)).down,
    (history.get (K .remainderEntropyLow)).down,
    (history.get (K .localTypeCoordinateNonrepetitive)).down,
    (history.get (K .largeBudgetResidual)).down,
    (history.get (K .netDeficiencyCap)).down,
    (history.get (K .route8Rate)).down,
    (history.get (K .exactCollisionFails)).down,
    (history.get (K .absorbedConfigurationResidual)).down⟩

/-- **Node `[153]` residual, arms: `[158]` yes (window package realized); `[146]` no, `[153]` bounded cold mass (`[24]`), route-8 entry rate holds; `[57]`/`[173]` exact collision fails (`[174]`); `[50]` low entropy, repetitive, dominant rooted type wedge-free.**  Path: `selectedLedgerBoundary → selectedNearCubicBranch → selectedNearCubicSurvivorBranch → nearCubicRealized → nearCubicLargeBudgetDensityCap → nearCubicRouteEightEntry → selectedNetChargeContinuation → selectedAbsorbedGermPrerequisites`.
The generic residual and the 13 extra facts of this path's ledger
(55 facts). -/
abbrev Node153ResidualOutcome_realized_bounded_absorbed_lowWedgeFree (selected : EGInput.{u}) : Prop :=
  Node153ResidualOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageRealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8AtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMassBounded selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .densityCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderEntropyLow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .localTypeCoordinateRepetitive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .dominantRootedType selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .dominantRootedTypeWedgeFree selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .largeBudgetResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .netDeficiencyCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8Rate selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .exactCollisionFails selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .absorbedConfigurationResidual selected.object

/-- `Node153ResidualOutcome_realized_bounded_absorbed_lowWedgeFree` is a subtype of the generic `[153]` residual. -/
theorem Node153ResidualOutcome_realized_bounded_absorbed_lowWedgeFree.toGeneric {selected : EGInput.{u}}
    (outcome : Node153ResidualOutcome_realized_bounded_absorbed_lowWedgeFree selected) : Node153ResidualOutcome selected :=
  outcome.1

/-- The return of `Node153ResidualOutcome_realized_bounded_absorbed_lowWedgeFree`: one `get` per fact of its ledger. -/
theorem node153Return_realized_bounded_absorbed_lowWedgeFree
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
    [FactKeys.Has (K .coldRepeatedStateResidual) known]
    [FactKeys.Has (K .windowPackageRealized) known]
    [FactKeys.Has (K .coldRoute8AtOrAbove) known]
    [FactKeys.Has (K .coldMassBounded) known]
    [FactKeys.Has (K .densityCap) known]
    [FactKeys.Has (K .remainderEntropyLow) known]
    [FactKeys.Has (K .localTypeCoordinateRepetitive) known]
    [FactKeys.Has (K .dominantRootedType) known]
    [FactKeys.Has (K .dominantRootedTypeWedgeFree) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .netDeficiencyCap) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .exactCollisionFails) known]
    [FactKeys.Has (K .absorbedConfigurationResidual) known] :
    Node153ResidualOutcome_realized_bounded_absorbed_lowWedgeFree selected :=
  ⟨node153Return history,
    (history.get (K .windowPackageRealized)).down,
    (history.get (K .coldRoute8AtOrAbove)).down,
    (history.get (K .coldMassBounded)).down,
    (history.get (K .densityCap)).down,
    (history.get (K .remainderEntropyLow)).down,
    (history.get (K .localTypeCoordinateRepetitive)).down,
    (history.get (K .dominantRootedType)).down,
    (history.get (K .dominantRootedTypeWedgeFree)).down,
    (history.get (K .largeBudgetResidual)).down,
    (history.get (K .netDeficiencyCap)).down,
    (history.get (K .route8Rate)).down,
    (history.get (K .exactCollisionFails)).down,
    (history.get (K .absorbedConfigurationResidual)).down⟩

/-- **Node `[153]` residual, arms: `[158]` yes (window package realized); `[146]` no, `[153]` bounded cold mass (`[24]`), route-8 entry rate holds; `[57]`/`[173]` exact collision fails (`[174]`); `[50]` low entropy, repetitive, dominant rooted wedge type.**  Path: `selectedLedgerBoundary → selectedNearCubicBranch → selectedNearCubicSurvivorBranch → nearCubicRealized → nearCubicLargeBudgetDensityCap → nearCubicRouteEightEntry → selectedNetChargeContinuation → selectedAbsorbedGermPrerequisites`.
The generic residual and the 14 extra facts of this path's ledger
(56 facts). -/
abbrev Node153ResidualOutcome_realized_bounded_absorbed_lowWedge (selected : EGInput.{u}) : Prop :=
  Node153ResidualOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageRealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8AtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMassBounded selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .densityCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderEntropyLow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .localTypeCoordinateRepetitive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .dominantRootedType selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .dominantRootedWedgeType selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .independentObstructionTranslates selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .largeBudgetResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .netDeficiencyCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8Rate selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .exactCollisionFails selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .absorbedConfigurationResidual selected.object

/-- `Node153ResidualOutcome_realized_bounded_absorbed_lowWedge` is a subtype of the generic `[153]` residual. -/
theorem Node153ResidualOutcome_realized_bounded_absorbed_lowWedge.toGeneric {selected : EGInput.{u}}
    (outcome : Node153ResidualOutcome_realized_bounded_absorbed_lowWedge selected) : Node153ResidualOutcome selected :=
  outcome.1

/-- The return of `Node153ResidualOutcome_realized_bounded_absorbed_lowWedge`: one `get` per fact of its ledger. -/
theorem node153Return_realized_bounded_absorbed_lowWedge
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
    [FactKeys.Has (K .coldRepeatedStateResidual) known]
    [FactKeys.Has (K .windowPackageRealized) known]
    [FactKeys.Has (K .coldRoute8AtOrAbove) known]
    [FactKeys.Has (K .coldMassBounded) known]
    [FactKeys.Has (K .densityCap) known]
    [FactKeys.Has (K .remainderEntropyLow) known]
    [FactKeys.Has (K .localTypeCoordinateRepetitive) known]
    [FactKeys.Has (K .dominantRootedType) known]
    [FactKeys.Has (K .dominantRootedWedgeType) known]
    [FactKeys.Has (K .independentObstructionTranslates) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .netDeficiencyCap) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .exactCollisionFails) known]
    [FactKeys.Has (K .absorbedConfigurationResidual) known] :
    Node153ResidualOutcome_realized_bounded_absorbed_lowWedge selected :=
  ⟨node153Return history,
    (history.get (K .windowPackageRealized)).down,
    (history.get (K .coldRoute8AtOrAbove)).down,
    (history.get (K .coldMassBounded)).down,
    (history.get (K .densityCap)).down,
    (history.get (K .remainderEntropyLow)).down,
    (history.get (K .localTypeCoordinateRepetitive)).down,
    (history.get (K .dominantRootedType)).down,
    (history.get (K .dominantRootedWedgeType)).down,
    (history.get (K .independentObstructionTranslates)).down,
    (history.get (K .largeBudgetResidual)).down,
    (history.get (K .netDeficiencyCap)).down,
    (history.get (K .route8Rate)).down,
    (history.get (K .exactCollisionFails)).down,
    (history.get (K .absorbedConfigurationResidual)).down⟩

/-- **Node `[153]` residual, arms: `[158]` yes (window package realized); `[146]` no, `[153]` linear cold mass.**  Path: `selectedLedgerBoundary → selectedNearCubicBranch → selectedNearCubicSurvivorBranch → nearCubicRealized`.
The generic residual and the 3 extra facts of this path's ledger
(45 facts). -/
abbrev Node153ResidualOutcome_realized_linear (selected : EGInput.{u}) : Prop :=
  Node153ResidualOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageRealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8AtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMassLinear selected.object

/-- `Node153ResidualOutcome_realized_linear` is a subtype of the generic `[153]` residual. -/
theorem Node153ResidualOutcome_realized_linear.toGeneric {selected : EGInput.{u}}
    (outcome : Node153ResidualOutcome_realized_linear selected) : Node153ResidualOutcome selected :=
  outcome.1

/-- The return of `Node153ResidualOutcome_realized_linear`: one `get` per fact of its ledger. -/
theorem node153Return_realized_linear
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
    [FactKeys.Has (K .coldRepeatedStateResidual) known]
    [FactKeys.Has (K .windowPackageRealized) known]
    [FactKeys.Has (K .coldRoute8AtOrAbove) known]
    [FactKeys.Has (K .coldMassLinear) known] :
    Node153ResidualOutcome_realized_linear selected :=
  ⟨node153Return history,
    (history.get (K .windowPackageRealized)).down,
    (history.get (K .coldRoute8AtOrAbove)).down,
    (history.get (K .coldMassLinear)).down⟩

/-- The 23 subtypes of node `[153]`'s residual, one per distinct fact set. -/
abbrev Node153ResidualSubtypes (selected : EGInput.{u}) : Prop :=
  Node153ResidualOutcome_denseAtOrAbove_coldBelow_absorbed_high selected ∨
  Node153ResidualOutcome_denseAtOrAbove_coldBelow_absorbed_lowNonrep selected ∨
  Node153ResidualOutcome_denseAtOrAbove_coldBelow_absorbed_lowWedgeFree selected ∨
  Node153ResidualOutcome_denseAtOrAbove_coldBelow_absorbed_lowWedge selected ∨
  Node153ResidualOutcome_denseAtOrAbove_linear selected ∨
  Node153ResidualOutcome_denseAtOrAbove_bounded_absorbed_high selected ∨
  Node153ResidualOutcome_denseAtOrAbove_bounded_absorbed_lowNonrep selected ∨
  Node153ResidualOutcome_denseAtOrAbove_bounded_absorbed_lowWedgeFree selected ∨
  Node153ResidualOutcome_denseAtOrAbove_bounded_absorbed_lowWedge selected ∨
  Node153ResidualOutcome_denseRateFails_linear selected ∨
  Node153ResidualOutcome_denseRate_absorbed_high selected ∨
  Node153ResidualOutcome_denseRate_absorbed_lowNonrep selected ∨
  Node153ResidualOutcome_denseRate_absorbed_lowWedgeFree selected ∨
  Node153ResidualOutcome_denseRate_absorbed_lowWedge selected ∨
  Node153ResidualOutcome_realized_coldBelow_absorbed_high selected ∨
  Node153ResidualOutcome_realized_coldBelow_absorbed_lowNonrep selected ∨
  Node153ResidualOutcome_realized_coldBelow_absorbed_lowWedgeFree selected ∨
  Node153ResidualOutcome_realized_coldBelow_absorbed_lowWedge selected ∨
  Node153ResidualOutcome_realized_bounded_absorbed_high selected ∨
  Node153ResidualOutcome_realized_bounded_absorbed_lowNonrep selected ∨
  Node153ResidualOutcome_realized_bounded_absorbed_lowWedgeFree selected ∨
  Node153ResidualOutcome_realized_bounded_absorbed_lowWedge selected ∨
  Node153ResidualOutcome_realized_linear selected

/-- Every subtype of node `[153]`'s residual projects to the generic one. -/
theorem Node153ResidualSubtypes.toGeneric {selected : EGInput.{u}}
    (outcome : Node153ResidualSubtypes selected) :
    Node153ResidualOutcome selected := by
  rcases outcome with o | o | o | o | o | o | o | o | o | o | o | o | o | o | o | o | o | o | o | o | o | o | o <;> exact o.1

end HypostructureErdos64EG
