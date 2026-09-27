import HypostructureErdos64EG.Assembly.Residuals

/-!
# Assembly: Residuals / Node162ResidualOutcome

The `[162]` residual (`lem:dense-cold-pass`, tex 7692-7694) is reached along
two paths from the root, both through the dense linear arm of `[153]` inside
the pass on the no-arm of `[158]`.  Their ledgers differ only by the arm of
`[160]` (`lem:dense-deficiency-routing`) on which the pass runs, so there are
two residuals, each a subtype of the generic `Node162ResidualOutcome`:

- `Node162ResidualOutcome_tauAtOrAbove`: `[160]` first test fails,
  `τ(θ) ≥ 1/4` (47 facts);
- `Node162ResidualOutcome_tauBelowRateFails`: `[160]` first test holds,
  `τ(θ) < 1/4`, and the private-carrier rate `τ(θ) < 3/13` fails (48 facts).
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u

/-- **Node `[162]` on `[160]`'s first complement** (`τ(θ) ≥ 1/4`).
The generic `[162]` residual together with every fact its arm of `[160]`
adds to the ledger (47 facts in all). -/
abbrev Node162ResidualOutcome_tauAtOrAbove (selected : EGInput.{u}) : Prop :=
  Node162ResidualOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyAtOrAbove selected.object

theorem Node162ResidualOutcome_tauAtOrAbove.toGeneric {selected : EGInput.{u}}
    (h : Node162ResidualOutcome_tauAtOrAbove selected) : Node162ResidualOutcome selected :=
  h.1

/-- The return of `Node162ResidualOutcome_tauAtOrAbove`: one `get` per fact of its ledger. -/
theorem node162Return_tauAtOrAbove
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
    [FactKeys.Has (K .denseDeficiencyAtOrAbove) known] :
    Node162ResidualOutcome_tauAtOrAbove selected :=
  ⟨node162Return history,
    (history.get (K .denseDeficiencyAtOrAbove)).down⟩

/-- **Node `[162]` on `[160]`'s second complement** (`τ(θ) < 1/4`, the
private-carrier rate `τ(θ) < 3/13` failed).
The generic `[162]` residual together with every fact its arm of `[160]`
adds to the ledger (48 facts in all). -/
abbrev Node162ResidualOutcome_tauBelowRateFails (selected : EGInput.{u}) : Prop :=
  Node162ResidualOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyBelow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8RateFails selected.object

theorem Node162ResidualOutcome_tauBelowRateFails.toGeneric {selected : EGInput.{u}}
    (h : Node162ResidualOutcome_tauBelowRateFails selected) : Node162ResidualOutcome selected :=
  h.1

/-- The return of `Node162ResidualOutcome_tauBelowRateFails`: one `get` per fact of its ledger. -/
theorem node162Return_tauBelowRateFails
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
    [FactKeys.Has (K .denseDeficiencyBelow) known]
    [FactKeys.Has (K .route8RateFails) known] :
    Node162ResidualOutcome_tauBelowRateFails selected :=
  ⟨node162Return history,
    (history.get (K .denseDeficiencyBelow)).down,
    (history.get (K .route8RateFails)).down⟩

end HypostructureErdos64EG
