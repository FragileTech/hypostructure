import HypostructureErdos64EG.Assembly.Residuals.ArmBlocks

/-!
# Assembly: Residuals / Node162ResidualOutcome

The `[162]` residual (`lem:dense-cold-pass`, tex 7692-7694) is reached along
two paths from the root, both through the dense linear arm of `[153]` inside
the pass on the no-arm of `[158]`.  Their ledgers differ only by the arm of
`[160]` (`lem:dense-deficiency-routing`) on which the pass runs, so there are
two residuals, each a subtype of the generic `Node162ResidualOutcome`:

- `Node162ResidualOutcome_tauAtOrAbove`: `[160]` first test fails,
  `τ(θ) ≥ 1/4` (61 facts);
- `Node162ResidualOutcome_tauBelowRateFails`: `[160]` first test holds,
  `τ(θ) < 1/4`, and the private-carrier rate `τ(θ) < 3/13` fails (62 facts).
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u

/-- **Node `[162]` on `[160]`'s first complement** (`τ(θ) ≥ 1/4`).
The generic `[162]` residual together with every fact its arm of `[160]`
adds to the ledger (61 facts in all). -/
abbrev Node162ResidualOutcome_tauAtOrAbove (selected : EGInput.{u}) : Prop :=
  Node162ResidualOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyAtOrAbove selected.object

theorem Node162ResidualOutcome_tauAtOrAbove.toGeneric {selected : EGInput.{u}}
    (h : Node162ResidualOutcome_tauAtOrAbove selected) : Node162ResidualOutcome selected :=
  h.1

/-- The return of `Node162ResidualOutcome_tauAtOrAbove`: one `get` per fact of
its ledger. The facts of the upstream arm are read from its block
(`DenseTauBlock_atOrAbove`), built by the block's `.ret` with one `get` per key
on the same ledger. -/
theorem node162Return_tauAtOrAbove
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
    [FactKeys.Has (K .coldDenseHeavyEntryResidual) known]
    (tau : DenseTauBlock_atOrAbove selected) :
    Node162ResidualOutcome_tauAtOrAbove selected :=
  ⟨node162Return history,
    tau⟩

/-- **Node `[162]` on `[160]`'s second complement** (`τ(θ) < 1/4`, the
private-carrier rate `τ(θ) < 3/13` failed).
The generic `[162]` residual together with every fact its arm of `[160]`
adds to the ledger (62 facts in all). -/
abbrev Node162ResidualOutcome_tauBelowRateFails (selected : EGInput.{u}) : Prop :=
  Node162ResidualOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyBelow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8RateFails selected.object

theorem Node162ResidualOutcome_tauBelowRateFails.toGeneric {selected : EGInput.{u}}
    (h : Node162ResidualOutcome_tauBelowRateFails selected) : Node162ResidualOutcome selected :=
  h.1

/-- The return of `Node162ResidualOutcome_tauBelowRateFails`: one `get` per fact
of its ledger. The facts of the upstream arm are read from its block
(`DenseTauBlock_belowRateFails`), built by the block's `.ret` with one `get` per
key on the same ledger. -/
theorem node162Return_tauBelowRateFails
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
    [FactKeys.Has (K .coldDenseHeavyEntryResidual) known]
    (tau : DenseTauBlock_belowRateFails selected) :
    Node162ResidualOutcome_tauBelowRateFails selected :=
  ⟨node162Return history,
    tau.1,
    tau.2⟩

/-- The two subtypes of node `[162]`'s residual, one per `[160]` arm of the dense pass. -/
abbrev Node162ResidualSubtypes (selected : EGInput.{u}) : Prop :=
  Node162ResidualOutcome_tauAtOrAbove selected ∨
  Node162ResidualOutcome_tauBelowRateFails selected

/-- The return of node `[162]`'s residual on the `[160]` arm named by `tau`, through that subtype's return theorem. -/
theorem node162SubtypesReturn
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
    [FactKeys.Has (K .coldDenseHeavyEntryResidual) known]
    (tau : DenseTauArm selected) :
    Node162ResidualSubtypes selected := by
  rcases tau with t | t
  · exact Or.inl (node162Return_tauAtOrAbove history t)
  · exact Or.inr (node162Return_tauBelowRateFails history t)

end HypostructureErdos64EG
