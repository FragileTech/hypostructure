import Hypostructure.Graph.Strategy.BlockedCompressionRows
import Hypostructure.Graph.Strategy.ColdCorridorRows.CanonicalReplacement
import Hypostructure.Graph.Strategy.ColdCorridorRows.GermTrichotomy
import HypostructureErdos64EG.Assembly.Residuals.BlockedBarrierOverlapOutcome

/-!
# Assembly: NearCubic / Replacement

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

set_option maxHeartbeats 8000000 in
/-- Nodes `[166]` and `[169]`: consume the exact canonical-replacement swap,
publish the forced equality `Q = E`, and enter the blocked-class continuation
on that literal residual.

**Nodes `[170]`--`[172]`, `lem:scale-additivity`.**  On the trivial neutral
germ residual of `[169]` (`K .blockedClassMember`, `def:blocked-class`), decide
whether the conditional savings of the barrier states add at every fixed scale.
Independently of that decision, the yes fact retains two local consequences of
the same incoming blocked-class ledger: imposing the current surviving-state
test can only shrink a graph fibre, and the conditional state fibre has size at
most `F_{a,b} + 1`, where the extra state is exactly the absent-completion
marker.  These strengthen the retained ledger but do not replace the paper's
relative `F_{a,b}/W_{a,b}` test.

*Additive* (`[171]`): `lem:blocked-graphs-compress` encodes every member of
`𝓑(𝒫)` as its outside edges together with all barrier states, paying
`log₂ W_{a,b} − γ_{a,b}` bits per coordinate, so
`card 𝓑(𝒫) · W^N ≤ |𝒢_{n,m}| · F^N`.  `blockedCompressionRow` proves this by
the manuscript's finite prefix exposure directly from `K .blockedClassMember`
and the additive decision arm, then publishes the registered package-bit form
as `K .blockedCompressionBound` and its budget consequence as
`K .blockedCompressionCap`.
The density hypothesis is the
dense-packing residual `[159]` itself: by `def:window-realization-test` the
no-branch of `[158]` is `2^{c₁₃p₁₃log₂n} > |𝒢_{n,m}|`, which
`K .windowPackageUnrealized`, the literal no-arm.  On that display
Core closes the two incompatible ledger facts, giving
`card 𝓑(𝒫) < 1` and contradicting
`G ∈ 𝓑(𝒫)`.  The complementary half of the same reading — the *joint* retained
code (window package with the remainder states and the exact curvature code)
overflowing the budget while the window package alone does not — remains node
`[53]`'s comparison in the hot/cold ledger and is not an arm of `[159]`.

*Not additive* (`[172]`): `lem:barrier-failure-overlap` supplies a minimal
same-scale barrier overlap obstruction with connected overlap support; the
uncrossing of `lem:window-system-realizability` (i)--(v) turns it into a
scale-spanning serial window system, `lem:serial-system-sumset` fills its
spectrum, and `lem:system-increment-arithmetic` closes it.  That uncrossing is
the next producer.

`tau` names the `[160]` arm of the dense pass; `[172a]` is returned as that
arm's subtype. -/
-- EG-NODE [166] refined lexicographic minimality: \(Q=E\)
-- EG-NODE [169] trivial neutral-configuration residual: dense packing, every corridor terminal and neutral, \(Q=E\); every window is blocked at every dyadic scale
-- EG-NODE [170] all conditional graph-count bounds hold?
-- EG-NODE [171] compression closure:\(|\mathcal B(\mathcal P)|<1\)
noncomputable def selectedCanonicalReplacementContinuation
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    (tau : DenseTauArm selected)
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .coldCanonicalReplacementSwap) known]
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .windowPackageUnrealized) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .minDegreeBaseline) known]
    (fresh : List.Disjoint
      [K .coldCanonicalReplacementTrivial, K .blockedClassMember,
        K .blockedScaleAdditive, K .blockedBarrierOverlap,
        K .blockedCompressionBound, K .blockedCompressionCap, closed] known := by
        key_fresh)
    [FactKeys.Has (K .absorbedGermFanData) known]
    [FactKeys.Has (K .absorbedGermSplit) known]
    [FactKeys.Has (K .barrierCap) known]
    [FactKeys.Has (K .barrierEnumeration) known]
    [FactKeys.Has (K .boundaryDemand) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .coldAmbientCubic) known]
    [FactKeys.Has (K .coldAmbientCubicStubExcess) known]
    [FactKeys.Has (K .coldBranchClosed) known]
    [FactKeys.Has (K .coldCanonicalNeutralConfiguration) known]
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
    [FactKeys.Has (K .coldGermFamilyPositive) known]
    [FactKeys.Has (K .coldGermNoneDistinguishing) known]
    [FactKeys.Has (K .coldGermNoneRealizing) known]
    [FactKeys.Has (K .coldGermRealized) known]
    [FactKeys.Has (K .coldGermRouted) known]
    [FactKeys.Has (K .coldGermSilent) known]
    [FactKeys.Has (K .coldHandoffTransfer) known]
    [FactKeys.Has (K .coldHeavyEntryTerminal) known]
    [FactKeys.Has (K .coldHotEntropyCap) known]
    [FactKeys.Has (K .coldMass) known]
    [FactKeys.Has (K .coldMassLinear) known]
    [FactKeys.Has (K .coldNeutralEqualLengthTerminal) known]
    [FactKeys.Has (K .coldReturnCorridors) known]
    [FactKeys.Has (K .coldRoute8AtOrAbove) known]
    [FactKeys.Has (K .coldSameInterfaceTable) known]
    [FactKeys.Has (K .coldSelectedBranchExcess) known]
    [FactKeys.Has (K .coldStubExcess) known]
    [FactKeys.Has (K .curvatureFullRank) known]
    [FactKeys.Has (K .curvatureTargetRank) known]
    [FactKeys.Has (K .cycleRankConstraint) known]
    [FactKeys.Has (K .degreeProfileFibres) known]
    [FactKeys.Has (K .denseColdCorridorsTerminal) known]
    [FactKeys.Has (K .exactResponseProfile) known]
    [FactKeys.Has (K .forcedCurvatureCost) known]
    [FactKeys.Has (K .localAlgebra) known]
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
    [FactKeys.Has (K .windowPresent) known] :
    BlockedBarrierOverlapSubtypes selected := by
  let trivial :=
    (canonicalReplacementTrivialRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by key_fresh)
  let blocked :=
    (blockedClassRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      trivial (by key_fresh)
  match scaleAdditivityDichotomy (data := spineData) blocked
      (by key_fresh) (by key_fresh) with
  | .left additiveHistory =>
      -- `[171]`: the compression bound against `[159]`'s strict overflow.
      exact ((blockedCompressionRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile)
        (data := spineData)).runAndCloseIncompatible additiveHistory
          (K .windowPackageUnrealized) (K .blockedCompressionCap)
          (by key_fresh) (by key_fresh)).elimClosed (by infer_instance) |>.elim
  | .right overlapHistory =>
      exact blockedBarrierOverlapSubtypesReturn overlapHistory tau

end HypostructureErdos64EG
