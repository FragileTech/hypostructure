import HypostructureErdos64EG.Assembly.Residuals.ArmBlocks
import HypostructureErdos64EG.Assembly.Residuals.ColdBranchClosedOutcome

/-!
# Assembly: Residuals / Node153ResidualOutcome

Node `[153]`'s returned residual (`Node153ResidualOutcome`, G's first
equal-state pair on a retained cold corridor) is reached along 18 root paths,
and the single ExactLedger holds a different fact set on each of them.  Each
distinct fact set is its own open node, stated here as a subtype of the generic
residual: the generic conjunction (the 42 facts common to every path) together
with every extra fact of that path's ledger, one `Holds` conjunct per key, in
ledger order.  Each subtype has one return theorem reading every fact with one
`ExactLedger.get`, and projects to the generic residual.  The absorbed paths
through `[160]` `τ(θ) ≥ 1/4` and `[146]` `θ < 1/78` (four entropy arms) are
closed at `[146]` (`θ < 1/78` forces `τ(θ) < 1/4`), and the absorbed path
through `[161]` with high entropy is closed at `[53]` (the dense package
overflows the skeleton budget, so the entropy cap is active).

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

-- The linear-arm blocks: the arm evidence of the three paths that reach
-- `[153]` on its own linear arm (`nearCubicDenseLinear`, `nearCubicRealized`).
/-- Node `[153]` linear-arm block: `[158]` no, `[160]` `τ(θ) ≥ 1/4`, `[146]` no, `[153]` linear cold mass (the extra facts of `Node153ResidualOutcome_denseAtOrAbove_linear`) (4 facts). -/
abbrev Node153LinearBlock_denseAtOrAbove (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyAtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8AtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMassLinear selected.object

/-- `Node153LinearBlock_denseAtOrAbove` from the one ledger: one `get` per key,
the `[160]` fact from its dense-pass block. -/
theorem Node153LinearBlock_denseAtOrAbove.ret
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .windowPackageUnrealized) known]
    [FactKeys.Has (K .coldRoute8AtOrAbove) known]
    [FactKeys.Has (K .coldMassLinear) known]
    (tau : DenseTauBlock_atOrAbove selected) :
    Node153LinearBlock_denseAtOrAbove selected :=
  ⟨(history.get (K .windowPackageUnrealized)).down,
    tau,
    (history.get (K .coldRoute8AtOrAbove)).down,
    (history.get (K .coldMassLinear)).down⟩

/-- Node `[153]` linear-arm block: `[158]` no, `[160]` `τ(θ) < 1/4` with the private-carrier rate failed, `[146]` no, `[153]` linear cold mass (the extra facts of `Node153ResidualOutcome_denseRateFails_linear`) (5 facts). -/
abbrev Node153LinearBlock_denseRateFails (selected : EGInput.{u}) : Prop :=
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

/-- `Node153LinearBlock_denseRateFails` from the one ledger: one `get` per key,
the `[160]` facts from their dense-pass block. -/
theorem Node153LinearBlock_denseRateFails.ret
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .windowPackageUnrealized) known]
    [FactKeys.Has (K .coldRoute8AtOrAbove) known]
    [FactKeys.Has (K .coldMassLinear) known]
    (tau : DenseTauBlock_belowRateFails selected) :
    Node153LinearBlock_denseRateFails selected :=
  ⟨(history.get (K .windowPackageUnrealized)).down,
    tau.1,
    tau.2,
    (history.get (K .coldRoute8AtOrAbove)).down,
    (history.get (K .coldMassLinear)).down⟩

/-- Node `[153]` linear-arm block: `[158]` yes, `[146]` no, `[153]` linear cold mass (the extra facts of `Node153ResidualOutcome_realized_linear`) (3 facts). -/
abbrev Node153LinearBlock_realized (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageRealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8AtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMassLinear selected.object

/-- `Node153LinearBlock_realized` from the one ledger: one `get` per key. -/
theorem Node153LinearBlock_realized.ret
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .windowPackageRealized) known]
    [FactKeys.Has (K .coldRoute8AtOrAbove) known]
    [FactKeys.Has (K .coldMassLinear) known] :
    Node153LinearBlock_realized selected :=
  ⟨(history.get (K .windowPackageRealized)).down,
    (history.get (K .coldRoute8AtOrAbove)).down,
    (history.get (K .coldMassLinear)).down⟩

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

/-- The return of `Node153ResidualOutcome_denseAtOrAbove_linear`: one `get` per
fact of its ledger. The facts of the upstream arm are read from its block
(`Node153LinearBlock_denseAtOrAbove`), built by the block's `.ret` with one
`get` per key on the same ledger. -/
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
    (block : Node153LinearBlock_denseAtOrAbove selected) :
    Node153ResidualOutcome_denseAtOrAbove_linear selected :=
  ⟨node153Return history,
    block.1,
    block.2.1,
    block.2.2.1,
    block.2.2.2⟩

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

/-- The return of `Node153ResidualOutcome_denseAtOrAbove_bounded_absorbed_high`:
one `get` per fact of its ledger. The facts of the upstream arm are read from
its blocks (`ColdBranchClosedAbsorbedCommon`,
`Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdAtOrAbove`,
`EntropyArmBlock_high`), built by the block's `.ret` with one `get` per key on
the same ledger. -/
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
    (common : ColdBranchClosedAbsorbedCommon selected)
    (lanePrefix : Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdAtOrAbove selected)
    (entropy : EntropyArmBlock_high selected) :
    Node153ResidualOutcome_denseAtOrAbove_bounded_absorbed_high selected :=
  ⟨node153Return history,
    lanePrefix.2.2.2.2,
    lanePrefix.2.2.1,
    lanePrefix.2.1,
    lanePrefix.1,
    lanePrefix.2.2.2.1,
    entropy.2.2,
    entropy.2.1,
    entropy.1,
    common.2.2.1,
    common.2.2.2.1,
    common.2.2.2.2,
    common.2.1,
    common.1⟩

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

/-- The return of
`Node153ResidualOutcome_denseAtOrAbove_bounded_absorbed_lowNonrep`: one `get`
per fact of its ledger. The facts of the upstream arm are read from its blocks
(`ColdBranchClosedAbsorbedCommon`,
`Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdAtOrAbove`,
`EntropyArmBlock_lowNonrepetitive`), built by the block's `.ret` with one `get`
per key on the same ledger. -/
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
    (common : ColdBranchClosedAbsorbedCommon selected)
    (lanePrefix : Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdAtOrAbove selected)
    (entropy : EntropyArmBlock_lowNonrepetitive selected) :
    Node153ResidualOutcome_denseAtOrAbove_bounded_absorbed_lowNonrep selected :=
  ⟨node153Return history,
    lanePrefix.2.2.2.2,
    lanePrefix.2.2.1,
    lanePrefix.2.1,
    lanePrefix.1,
    lanePrefix.2.2.2.1,
    entropy.2,
    entropy.1,
    common.2.2.1,
    common.2.2.2.1,
    common.2.2.2.2,
    common.2.1,
    common.1⟩

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

/-- The return of
`Node153ResidualOutcome_denseAtOrAbove_bounded_absorbed_lowWedgeFree`: one `get`
per fact of its ledger. The facts of the upstream arm are read from its blocks
(`ColdBranchClosedAbsorbedCommon`,
`Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdAtOrAbove`,
`EntropyArmBlock_lowRepetitiveWedgeFree`), built by the block's `.ret` with one
`get` per key on the same ledger. -/
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
    (common : ColdBranchClosedAbsorbedCommon selected)
    (lanePrefix : Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdAtOrAbove selected)
    (entropy : EntropyArmBlock_lowRepetitiveWedgeFree selected) :
    Node153ResidualOutcome_denseAtOrAbove_bounded_absorbed_lowWedgeFree selected :=
  ⟨node153Return history,
    lanePrefix.2.2.2.2,
    lanePrefix.2.2.1,
    lanePrefix.2.1,
    lanePrefix.1,
    lanePrefix.2.2.2.1,
    entropy.2.2.2,
    entropy.2.2.1,
    entropy.1,
    entropy.2.1,
    common.2.2.1,
    common.2.2.2.1,
    common.2.2.2.2,
    common.2.1,
    common.1⟩

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

/-- The return of
`Node153ResidualOutcome_denseAtOrAbove_bounded_absorbed_lowWedge`: one `get` per
fact of its ledger. The facts of the upstream arm are read from its blocks
(`ColdBranchClosedAbsorbedCommon`,
`Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdAtOrAbove`,
`EntropyArmBlock_lowRepetitiveWedge`), built by the block's `.ret` with one
`get` per key on the same ledger. -/
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
    (common : ColdBranchClosedAbsorbedCommon selected)
    (lanePrefix : Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdAtOrAbove selected)
    (entropy : EntropyArmBlock_lowRepetitiveWedge selected) :
    Node153ResidualOutcome_denseAtOrAbove_bounded_absorbed_lowWedge selected :=
  ⟨node153Return history,
    lanePrefix.2.2.2.2,
    lanePrefix.2.2.1,
    lanePrefix.2.1,
    lanePrefix.1,
    lanePrefix.2.2.2.1,
    entropy.2.2.2.2,
    entropy.2.2.2.1,
    entropy.1,
    entropy.2.1,
    entropy.2.2.1,
    common.2.2.1,
    common.2.2.2.1,
    common.2.2.2.2,
    common.2.1,
    common.1⟩

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

/-- The return of `Node153ResidualOutcome_denseRateFails_linear`: one `get` per
fact of its ledger. The facts of the upstream arm are read from its block
(`Node153LinearBlock_denseRateFails`), built by the block's `.ret` with one
`get` per key on the same ledger. -/
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
    (block : Node153LinearBlock_denseRateFails selected) :
    Node153ResidualOutcome_denseRateFails_linear selected :=
  ⟨node153Return history,
    block.1,
    block.2.1,
    block.2.2.1,
    block.2.2.2.1,
    block.2.2.2.2⟩

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

/-- The return of `Node153ResidualOutcome_denseRate_absorbed_lowNonrep`: one
`get` per fact of its ledger. The facts of the upstream arm are read from its
blocks (`ColdBranchClosedAbsorbedCommon`,
`Route8LanePrefixBlock_unrealizedDenseBelow`,
`EntropyArmBlock_lowNonrepetitive`), built by the block's `.ret` with one `get`
per key on the same ledger. -/
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
    (common : ColdBranchClosedAbsorbedCommon selected)
    (lanePrefix : Route8LanePrefixBlock_unrealizedDenseBelow selected)
    (entropy : EntropyArmBlock_lowNonrepetitive selected) :
    Node153ResidualOutcome_denseRate_absorbed_lowNonrep selected :=
  ⟨node153Return history,
    lanePrefix.2,
    lanePrefix.1,
    common.2.2.2.2,
    entropy.2,
    entropy.1,
    common.2.2.1,
    common.2.2.2.1,
    common.2.1,
    common.1⟩

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

/-- The return of `Node153ResidualOutcome_denseRate_absorbed_lowWedgeFree`: one
`get` per fact of its ledger. The facts of the upstream arm are read from its
blocks (`ColdBranchClosedAbsorbedCommon`,
`Route8LanePrefixBlock_unrealizedDenseBelow`,
`EntropyArmBlock_lowRepetitiveWedgeFree`), built by the block's `.ret` with one
`get` per key on the same ledger. -/
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
    (common : ColdBranchClosedAbsorbedCommon selected)
    (lanePrefix : Route8LanePrefixBlock_unrealizedDenseBelow selected)
    (entropy : EntropyArmBlock_lowRepetitiveWedgeFree selected) :
    Node153ResidualOutcome_denseRate_absorbed_lowWedgeFree selected :=
  ⟨node153Return history,
    lanePrefix.2,
    lanePrefix.1,
    common.2.2.2.2,
    entropy.2.2.2,
    entropy.2.2.1,
    entropy.1,
    entropy.2.1,
    common.2.2.1,
    common.2.2.2.1,
    common.2.1,
    common.1⟩

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

/-- The return of `Node153ResidualOutcome_denseRate_absorbed_lowWedge`: one
`get` per fact of its ledger. The facts of the upstream arm are read from its
blocks (`ColdBranchClosedAbsorbedCommon`,
`Route8LanePrefixBlock_unrealizedDenseBelow`,
`EntropyArmBlock_lowRepetitiveWedge`), built by the block's `.ret` with one
`get` per key on the same ledger. -/
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
    (common : ColdBranchClosedAbsorbedCommon selected)
    (lanePrefix : Route8LanePrefixBlock_unrealizedDenseBelow selected)
    (entropy : EntropyArmBlock_lowRepetitiveWedge selected) :
    Node153ResidualOutcome_denseRate_absorbed_lowWedge selected :=
  ⟨node153Return history,
    lanePrefix.2,
    lanePrefix.1,
    common.2.2.2.2,
    entropy.2.2.2.2,
    entropy.2.2.2.1,
    entropy.1,
    entropy.2.1,
    entropy.2.2.1,
    common.2.2.1,
    common.2.2.2.1,
    common.2.1,
    common.1⟩

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

/-- The return of `Node153ResidualOutcome_realized_coldBelow_absorbed_high`: one
`get` per fact of its ledger. The facts of the upstream arm are read from its
blocks (`ColdBranchClosedAbsorbedCommon`,
`Route8LanePrefixBlock_realizedColdBelow`, `EntropyArmBlock_high`), built by the
block's `.ret` with one `get` per key on the same ledger. -/
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
    (common : ColdBranchClosedAbsorbedCommon selected)
    (lanePrefix : Route8LanePrefixBlock_realizedColdBelow selected)
    (entropy : EntropyArmBlock_high selected) :
    Node153ResidualOutcome_realized_coldBelow_absorbed_high selected :=
  ⟨node153Return history,
    lanePrefix.2,
    lanePrefix.1,
    common.2.2.2.2,
    entropy.2.2,
    entropy.2.1,
    entropy.1,
    common.2.2.1,
    common.2.2.2.1,
    common.2.1,
    common.1⟩

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

/-- The return of
`Node153ResidualOutcome_realized_coldBelow_absorbed_lowNonrep`: one `get` per
fact of its ledger. The facts of the upstream arm are read from its blocks
(`ColdBranchClosedAbsorbedCommon`, `Route8LanePrefixBlock_realizedColdBelow`,
`EntropyArmBlock_lowNonrepetitive`), built by the block's `.ret` with one `get`
per key on the same ledger. -/
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
    (common : ColdBranchClosedAbsorbedCommon selected)
    (lanePrefix : Route8LanePrefixBlock_realizedColdBelow selected)
    (entropy : EntropyArmBlock_lowNonrepetitive selected) :
    Node153ResidualOutcome_realized_coldBelow_absorbed_lowNonrep selected :=
  ⟨node153Return history,
    lanePrefix.2,
    lanePrefix.1,
    common.2.2.2.2,
    entropy.2,
    entropy.1,
    common.2.2.1,
    common.2.2.2.1,
    common.2.1,
    common.1⟩

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

/-- The return of
`Node153ResidualOutcome_realized_coldBelow_absorbed_lowWedgeFree`: one `get` per
fact of its ledger. The facts of the upstream arm are read from its blocks
(`ColdBranchClosedAbsorbedCommon`, `Route8LanePrefixBlock_realizedColdBelow`,
`EntropyArmBlock_lowRepetitiveWedgeFree`), built by the block's `.ret` with one
`get` per key on the same ledger. -/
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
    (common : ColdBranchClosedAbsorbedCommon selected)
    (lanePrefix : Route8LanePrefixBlock_realizedColdBelow selected)
    (entropy : EntropyArmBlock_lowRepetitiveWedgeFree selected) :
    Node153ResidualOutcome_realized_coldBelow_absorbed_lowWedgeFree selected :=
  ⟨node153Return history,
    lanePrefix.2,
    lanePrefix.1,
    common.2.2.2.2,
    entropy.2.2.2,
    entropy.2.2.1,
    entropy.1,
    entropy.2.1,
    common.2.2.1,
    common.2.2.2.1,
    common.2.1,
    common.1⟩

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

/-- The return of `Node153ResidualOutcome_realized_coldBelow_absorbed_lowWedge`:
one `get` per fact of its ledger. The facts of the upstream arm are read from
its blocks (`ColdBranchClosedAbsorbedCommon`,
`Route8LanePrefixBlock_realizedColdBelow`,
`EntropyArmBlock_lowRepetitiveWedge`), built by the block's `.ret` with one
`get` per key on the same ledger. -/
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
    (common : ColdBranchClosedAbsorbedCommon selected)
    (lanePrefix : Route8LanePrefixBlock_realizedColdBelow selected)
    (entropy : EntropyArmBlock_lowRepetitiveWedge selected) :
    Node153ResidualOutcome_realized_coldBelow_absorbed_lowWedge selected :=
  ⟨node153Return history,
    lanePrefix.2,
    lanePrefix.1,
    common.2.2.2.2,
    entropy.2.2.2.2,
    entropy.2.2.2.1,
    entropy.1,
    entropy.2.1,
    entropy.2.2.1,
    common.2.2.1,
    common.2.2.2.1,
    common.2.1,
    common.1⟩

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

/-- The return of `Node153ResidualOutcome_realized_bounded_absorbed_high`: one
`get` per fact of its ledger. The facts of the upstream arm are read from its
blocks (`ColdBranchClosedAbsorbedCommon`,
`Route8LanePrefixBlock_realizedColdAtOrAbove`, `EntropyArmBlock_high`), built by
the block's `.ret` with one `get` per key on the same ledger. -/
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
    (common : ColdBranchClosedAbsorbedCommon selected)
    (lanePrefix : Route8LanePrefixBlock_realizedColdAtOrAbove selected)
    (entropy : EntropyArmBlock_high selected) :
    Node153ResidualOutcome_realized_bounded_absorbed_high selected :=
  ⟨node153Return history,
    lanePrefix.2.2.2,
    lanePrefix.2.1,
    lanePrefix.1,
    lanePrefix.2.2.1,
    entropy.2.2,
    entropy.2.1,
    entropy.1,
    common.2.2.1,
    common.2.2.2.1,
    common.2.2.2.2,
    common.2.1,
    common.1⟩

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

/-- The return of `Node153ResidualOutcome_realized_bounded_absorbed_lowNonrep`:
one `get` per fact of its ledger. The facts of the upstream arm are read from
its blocks (`ColdBranchClosedAbsorbedCommon`,
`Route8LanePrefixBlock_realizedColdAtOrAbove`,
`EntropyArmBlock_lowNonrepetitive`), built by the block's `.ret` with one `get`
per key on the same ledger. -/
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
    (common : ColdBranchClosedAbsorbedCommon selected)
    (lanePrefix : Route8LanePrefixBlock_realizedColdAtOrAbove selected)
    (entropy : EntropyArmBlock_lowNonrepetitive selected) :
    Node153ResidualOutcome_realized_bounded_absorbed_lowNonrep selected :=
  ⟨node153Return history,
    lanePrefix.2.2.2,
    lanePrefix.2.1,
    lanePrefix.1,
    lanePrefix.2.2.1,
    entropy.2,
    entropy.1,
    common.2.2.1,
    common.2.2.2.1,
    common.2.2.2.2,
    common.2.1,
    common.1⟩

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

/-- The return of
`Node153ResidualOutcome_realized_bounded_absorbed_lowWedgeFree`: one `get` per
fact of its ledger. The facts of the upstream arm are read from its blocks
(`ColdBranchClosedAbsorbedCommon`,
`Route8LanePrefixBlock_realizedColdAtOrAbove`,
`EntropyArmBlock_lowRepetitiveWedgeFree`), built by the block's `.ret` with one
`get` per key on the same ledger. -/
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
    (common : ColdBranchClosedAbsorbedCommon selected)
    (lanePrefix : Route8LanePrefixBlock_realizedColdAtOrAbove selected)
    (entropy : EntropyArmBlock_lowRepetitiveWedgeFree selected) :
    Node153ResidualOutcome_realized_bounded_absorbed_lowWedgeFree selected :=
  ⟨node153Return history,
    lanePrefix.2.2.2,
    lanePrefix.2.1,
    lanePrefix.1,
    lanePrefix.2.2.1,
    entropy.2.2.2,
    entropy.2.2.1,
    entropy.1,
    entropy.2.1,
    common.2.2.1,
    common.2.2.2.1,
    common.2.2.2.2,
    common.2.1,
    common.1⟩

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

/-- The return of `Node153ResidualOutcome_realized_bounded_absorbed_lowWedge`:
one `get` per fact of its ledger. The facts of the upstream arm are read from
its blocks (`ColdBranchClosedAbsorbedCommon`,
`Route8LanePrefixBlock_realizedColdAtOrAbove`,
`EntropyArmBlock_lowRepetitiveWedge`), built by the block's `.ret` with one
`get` per key on the same ledger. -/
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
    (common : ColdBranchClosedAbsorbedCommon selected)
    (lanePrefix : Route8LanePrefixBlock_realizedColdAtOrAbove selected)
    (entropy : EntropyArmBlock_lowRepetitiveWedge selected) :
    Node153ResidualOutcome_realized_bounded_absorbed_lowWedge selected :=
  ⟨node153Return history,
    lanePrefix.2.2.2,
    lanePrefix.2.1,
    lanePrefix.1,
    lanePrefix.2.2.1,
    entropy.2.2.2.2,
    entropy.2.2.2.1,
    entropy.1,
    entropy.2.1,
    entropy.2.2.1,
    common.2.2.1,
    common.2.2.2.1,
    common.2.2.2.2,
    common.2.1,
    common.1⟩

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

/-- The return of `Node153ResidualOutcome_realized_linear`: one `get` per fact
of its ledger. The facts of the upstream arm are read from its block
(`Node153LinearBlock_realized`), built by the block's `.ret` with one `get` per
key on the same ledger. -/
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
    (block : Node153LinearBlock_realized selected) :
    Node153ResidualOutcome_realized_linear selected :=
  ⟨node153Return history,
    block.1,
    block.2.1,
    block.2.2⟩

/-- The 18 subtypes of node `[153]`'s residual, one per distinct fact set. -/
abbrev Node153ResidualSubtypes (selected : EGInput.{u}) : Prop :=
  Node153ResidualOutcome_denseAtOrAbove_linear selected ∨
  Node153ResidualOutcome_denseAtOrAbove_bounded_absorbed_high selected ∨
  Node153ResidualOutcome_denseAtOrAbove_bounded_absorbed_lowNonrep selected ∨
  Node153ResidualOutcome_denseAtOrAbove_bounded_absorbed_lowWedgeFree selected ∨
  Node153ResidualOutcome_denseAtOrAbove_bounded_absorbed_lowWedge selected ∨
  Node153ResidualOutcome_denseRateFails_linear selected ∨
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

/-- The arm evidence at node `[153]`'s return (`nearCubicColdOccurrence`): the
absorbed lane of the net-charge continuation (the facts common to its 15
paths and the lane entry: near-cubic prefix and entropy arm), or one of the three linear
arms of `[153]`. -/
abbrev Node153Arm (selected : EGInput.{u}) : Prop :=
  (ColdBranchClosedAbsorbedCommon selected ∧ Route8LaneEntry selected) ∨
    Node153LinearBlock_denseAtOrAbove selected ∨
    Node153LinearBlock_denseRateFails selected ∨
    Node153LinearBlock_realized selected

/-- The `[153]` arm evidence on the linear arm of the dense pass, from the
`[160]` arm named by `tau` and the one ledger. -/
theorem DenseTauArm.node153Arm
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .windowPackageUnrealized) known]
    [FactKeys.Has (K .coldRoute8AtOrAbove) known]
    [FactKeys.Has (K .coldMassLinear) known]
    (tau : DenseTauArm selected) : Node153Arm selected := by
  rcases tau with t | t
  · exact Or.inr (Or.inl (Node153LinearBlock_denseAtOrAbove.ret history t))
  · exact Or.inr (Or.inr (Or.inl (Node153LinearBlock_denseRateFails.ret history t)))

/-- The return of node `[153]`'s residual on the path named by `arm`: the
generic facts with one `get` each, and the subtype of that path, through its
own return theorem. -/
theorem node153SubtypesReturn
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
    (arm : Node153Arm selected) :
    Node153ResidualSubtypes selected := by
  rcases arm with ⟨common, ⟨lanePrefix, entropy⟩ | ⟨p, low⟩⟩ | b | b | b
  · rcases lanePrefix with p | p | p
    · rcases entropy with e | e | e | e
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (node153Return_realized_coldBelow_absorbed_high history common p e))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (node153Return_realized_coldBelow_absorbed_lowNonrep history common p e)))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (node153Return_realized_coldBelow_absorbed_lowWedgeFree history common p e))))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (node153Return_realized_coldBelow_absorbed_lowWedge history common p e)))))))))))))
    · rcases entropy with e | e | e | e
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (node153Return_realized_bounded_absorbed_high history common p e))))))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (node153Return_realized_bounded_absorbed_lowNonrep history common p e)))))))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (node153Return_realized_bounded_absorbed_lowWedgeFree history common p e))))))))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (node153Return_realized_bounded_absorbed_lowWedge history common p e)))))))))))))))))
    · rcases entropy with e | e | e | e
      · exact Or.inr (Or.inl (node153Return_denseAtOrAbove_bounded_absorbed_high history common p e))
      · exact Or.inr (Or.inr (Or.inl (node153Return_denseAtOrAbove_bounded_absorbed_lowNonrep history common p e)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (node153Return_denseAtOrAbove_bounded_absorbed_lowWedgeFree history common p e))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (node153Return_denseAtOrAbove_bounded_absorbed_lowWedge history common p e)))))
  · rcases low with e | e | e
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (node153Return_denseRate_absorbed_lowNonrep history common p e)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (node153Return_denseRate_absorbed_lowWedgeFree history common p e))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (node153Return_denseRate_absorbed_lowWedge history common p e)))))))))
  · exact Or.inl (node153Return_denseAtOrAbove_linear history b)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (node153Return_denseRateFails_linear history b))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (node153Return_realized_linear history b)))))))))))))))))

/-- Every subtype of node `[153]`'s residual projects to the generic one. -/
theorem Node153ResidualSubtypes.toGeneric {selected : EGInput.{u}}
    (outcome : Node153ResidualSubtypes selected) :
    Node153ResidualOutcome selected := by
  rcases outcome with o | o | o | o | o | o | o | o | o | o | o | o | o | o | o | o | o | o <;> exact o.1

end HypostructureErdos64EG
