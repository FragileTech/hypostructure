import HypostructureErdos64EG.Assembly.Residuals.ArmBlocks

/-!
# Assembly: Residuals / Node54ResidualOutcome

The returned residual `[54]` (prop:entropy-high-theta, tex 9921), split by the
distinct fact set of the single ledger at its return.  The generic
`Node54ResidualOutcome` carries the 41 facts common to every path; it is
reached along five paths from the root whose ledgers hold five distinct fact
sets, one per combination of the arms of `[158]`, `[160]`, `[146]` and
`[153]` taken before the spine `[25]`--`[54]`.  Each distinct fact set is its
own open node, stated as a subtype of the generic residual: the generic
residual together with every extra fact of that set, one `Holds` conjunct per
key, and one return theorem reading each fact with one `ExactLedger.get`.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u

/-- **Node `[54]`, fact set `realizedColdBelow`**: [158] yes (window package
realized); [146] yes (`θ < 1/78`), the `[147]` arm, whose route-8
private-carrier rate is read from the cold route-8 inequality. The generic
`Node54ResidualOutcome` (41 facts) and the 3 facts of this path's ledger
outside it (44 facts in total). -/
abbrev Node54ResidualOutcome_realizedColdBelow (selected : EGInput.{u}) : Prop :=
  Node54ResidualOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageRealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8Below selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8Rate selected.object

/-- `Node54ResidualOutcome_realizedColdBelow` is a subtype of the generic `[54]`
residual. -/
theorem Node54ResidualOutcome_realizedColdBelow.toGeneric {selected : EGInput.{u}}
    (h : Node54ResidualOutcome_realizedColdBelow selected) :
    Node54ResidualOutcome selected :=
  h.1

/-- The return of `Node54ResidualOutcome_realizedColdBelow`: one `get` per fact
of its ledger. The facts of the upstream arm are read from its block
(`Route8LanePrefixBlock_realizedColdBelow`), built by the block's `.ret` with
one `get` per key on the same ledger. -/
theorem node54Return_realizedColdBelow
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
    [FactKeys.Has (K .allColdEntropyResidual) known]
    [FactKeys.Has (K .route8Rate) known]
    (lanePrefix : Route8LanePrefixBlock_realizedColdBelow selected) :
    Node54ResidualOutcome_realizedColdBelow selected :=
  ⟨node54Return history,
    lanePrefix.2,
    lanePrefix.1,
    (history.get (K .route8Rate)).down⟩

/-- **Node `[54]`, fact set `realizedBounded`**: [158] yes (window package
realized); [146] no (`θ ≥ 1/78`); [153] bounded cold mass, returned through
`[24]`'s density cap. The generic `Node54ResidualOutcome` (41 facts) and the
4 facts of this path's ledger outside it (45 facts in total). -/
abbrev Node54ResidualOutcome_realizedBounded (selected : EGInput.{u}) : Prop :=
  Node54ResidualOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageRealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8AtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMassBounded selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .densityCap selected.object

/-- `Node54ResidualOutcome_realizedBounded` is a subtype of the generic `[54]`
residual. -/
theorem Node54ResidualOutcome_realizedBounded.toGeneric {selected : EGInput.{u}}
    (h : Node54ResidualOutcome_realizedBounded selected) :
    Node54ResidualOutcome selected :=
  h.1

/-- The return of `Node54ResidualOutcome_realizedBounded`: one `get` per fact of
its ledger. The facts of the upstream arm are read from its block
(`Route8LanePrefixBlock_realizedColdAtOrAbove`), built by the block's `.ret`
with one `get` per key on the same ledger. -/
theorem node54Return_realizedBounded
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
    [FactKeys.Has (K .allColdEntropyResidual) known]
    (lanePrefix : Route8LanePrefixBlock_realizedColdAtOrAbove selected) :
    Node54ResidualOutcome_realizedBounded selected :=
  ⟨node54Return history,
    lanePrefix.2.2.2,
    lanePrefix.2.1,
    lanePrefix.1,
    lanePrefix.2.2.1⟩

/-- **Node `[54]`, fact set `unrealizedTauHighBounded`**: [158] no (window
package unrealized); [160] first test no (`τ(θ) ≥ 1/4`); [146] no (`θ ≥
1/78`); [153] bounded cold mass, returned through `[24]`. The generic
`Node54ResidualOutcome` (41 facts) and the 5 facts of this path's ledger
outside it (46 facts in total). -/
abbrev Node54ResidualOutcome_unrealizedTauHighBounded (selected : EGInput.{u}) : Prop :=
  Node54ResidualOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyAtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8AtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMassBounded selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .densityCap selected.object

/-- `Node54ResidualOutcome_unrealizedTauHighBounded` is a subtype of the generic
`[54]` residual. -/
theorem Node54ResidualOutcome_unrealizedTauHighBounded.toGeneric {selected : EGInput.{u}}
    (h : Node54ResidualOutcome_unrealizedTauHighBounded selected) :
    Node54ResidualOutcome selected :=
  h.1

/-- The return of `Node54ResidualOutcome_unrealizedTauHighBounded`: one `get`
per fact of its ledger. The facts of the upstream arm are read from its block
(`Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdAtOrAbove`), built by the
block's `.ret` with one `get` per key on the same ledger. -/
theorem node54Return_unrealizedTauHighBounded
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
    [FactKeys.Has (K .allColdEntropyResidual) known]
    (lanePrefix : Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdAtOrAbove selected) :
    Node54ResidualOutcome_unrealizedTauHighBounded selected :=
  ⟨node54Return history,
    lanePrefix.2.2.2.2,
    lanePrefix.2.2.1,
    lanePrefix.2.1,
    lanePrefix.1,
    lanePrefix.2.2.2.1⟩

/-- **Node `[54]`, fact set `unrealizedRateFailsBounded`**: [158] no (window
package unrealized); [160] first test yes (`τ(θ) < 1/4`), second test no
(private-carrier rate fails); [146] no (`θ ≥ 1/78`); [153] bounded cold
mass, returned through `[24]`. The generic `Node54ResidualOutcome` (41
facts) and the 6 facts of this path's ledger outside it (47 facts in total). -/
abbrev Node54ResidualOutcome_unrealizedRateFailsBounded (selected : EGInput.{u}) : Prop :=
  Node54ResidualOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyBelow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8RateFails selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8AtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMassBounded selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .densityCap selected.object

/-- `Node54ResidualOutcome_unrealizedRateFailsBounded` is a subtype of the
generic `[54]` residual. -/
theorem Node54ResidualOutcome_unrealizedRateFailsBounded.toGeneric {selected : EGInput.{u}}
    (h : Node54ResidualOutcome_unrealizedRateFailsBounded selected) :
    Node54ResidualOutcome selected :=
  h.1

/-- The return of `Node54ResidualOutcome_unrealizedRateFailsBounded`: one `get`
per fact of its ledger. -/
theorem node54Return_unrealizedRateFailsBounded
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
    [FactKeys.Has (K .allColdEntropyResidual) known]
    [FactKeys.Has (K .windowPackageUnrealized) known]
    [FactKeys.Has (K .denseDeficiencyBelow) known]
    [FactKeys.Has (K .route8RateFails) known]
    [FactKeys.Has (K .coldRoute8AtOrAbove) known]
    [FactKeys.Has (K .coldMassBounded) known]
    [FactKeys.Has (K .densityCap) known] :
    Node54ResidualOutcome_unrealizedRateFailsBounded selected :=
  ⟨node54Return history,
    (history.get (K .windowPackageUnrealized)).down,
    (history.get (K .denseDeficiencyBelow)).down,
    (history.get (K .route8RateFails)).down,
    (history.get (K .coldRoute8AtOrAbove)).down,
    (history.get (K .coldMassBounded)).down,
    (history.get (K .densityCap)).down⟩

/-- **Node `[54]`, fact set `unrealizedBothRates`**: [158] no (window package
unrealized); [160] both tests yes (`τ(θ) < 1/4` and the private-carrier
rate), the `[161]` arm. The generic `Node54ResidualOutcome` (41 facts) and
the 3 facts of this path's ledger outside it (44 facts in total). -/
abbrev Node54ResidualOutcome_unrealizedBothRates (selected : EGInput.{u}) : Prop :=
  Node54ResidualOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyBelow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8Rate selected.object

/-- `Node54ResidualOutcome_unrealizedBothRates` is a subtype of the generic
`[54]` residual. -/
theorem Node54ResidualOutcome_unrealizedBothRates.toGeneric {selected : EGInput.{u}}
    (h : Node54ResidualOutcome_unrealizedBothRates selected) :
    Node54ResidualOutcome selected :=
  h.1

/-- The return of `Node54ResidualOutcome_unrealizedBothRates`: one `get` per
fact of its ledger. -/
theorem node54Return_unrealizedBothRates
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
    [FactKeys.Has (K .allColdEntropyResidual) known]
    [FactKeys.Has (K .windowPackageUnrealized) known]
    [FactKeys.Has (K .denseDeficiencyBelow) known]
    [FactKeys.Has (K .route8Rate) known] :
    Node54ResidualOutcome_unrealizedBothRates selected :=
  ⟨node54Return history,
    (history.get (K .windowPackageUnrealized)).down,
    (history.get (K .denseDeficiencyBelow)).down,
    (history.get (K .route8Rate)).down⟩

/-- The five subtypes of node `[54]`'s residual, one per distinct fact set.
The fact set "[158] no, [160] `τ(θ) ≥ 1/4`, [146] `θ < 1/78`" is closed at
`[146]`: `θ < 1/78` forces `τ(θ) < 1/4`. -/
abbrev Node54ResidualSubtypes (selected : EGInput.{u}) : Prop :=
  Node54ResidualOutcome_realizedColdBelow selected ∨
  Node54ResidualOutcome_realizedBounded selected ∨
  Node54ResidualOutcome_unrealizedTauHighBounded selected ∨
  Node54ResidualOutcome_unrealizedRateFailsBounded selected ∨
  Node54ResidualOutcome_unrealizedBothRates selected

/-- The return of node `[54]`'s residual in `nearCubicLargeBudgetColdRate`, on the route named by `lanePrefix`, through that subtype's return theorem. -/
theorem node54SubtypesReturn_coldRate
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
    [FactKeys.Has (K .allColdEntropyResidual) known]
    [FactKeys.Has (K .route8Rate) known]
    (lanePrefix : ColdRateArm selected) :
    Node54ResidualSubtypes selected :=
  Or.inl (node54Return_realizedColdBelow history lanePrefix)

/-- The return of node `[54]`'s residual in `nearCubicLargeBudgetDensityCap`, on the route named by `lanePrefix`, through that subtype's return theorem. -/
theorem node54SubtypesReturn_densityCap
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
    [FactKeys.Has (K .allColdEntropyResidual) known]
    (lanePrefix : DensityCapArm selected) :
    Node54ResidualSubtypes selected := by
  rcases lanePrefix with p | p
  · exact Or.inr (Or.inl (node54Return_realizedBounded history p))
  · exact Or.inr (Or.inr (Or.inl (node54Return_unrealizedTauHighBounded history p)))

end HypostructureErdos64EG
