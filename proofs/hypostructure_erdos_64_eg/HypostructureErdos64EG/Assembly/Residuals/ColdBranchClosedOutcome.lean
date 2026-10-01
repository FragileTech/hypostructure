import HypostructureErdos64EG.Assembly.Residuals.ArmBlocks

/-!
# Assembly: the `ColdBranchClosedOutcome` residual, split by fact set

`ColdBranchClosedOutcome` ([187], local cold-terminal exclusion) is reached
at G along the [153] linear cold-mass arm of the realized package with a
silent germ family (the singleton `linearRealizedSilent`), and along `[153]`'s
repeat on the two dense linear arms (the subtypes `..._repeated`, G audit
`[153]`).
The 100 paths through the absorbed-germ residual `[174]`--`[177]` are not
entered: `[173]`'s
no-arm is closed at the node against the private-carrier rate `K .route8Rate`
(`instIncompatibleExactCollisionFailsRoute8Rate`).

The singleton lists every key of its arm as an explicit `Holds` conjunct, and
its return theorem reads each fact with one `ExactLedger.get`.

On the `[154]` G2 yes-arm `K .coldGermSomeDistinguishing` the second
representative `E` is a piece constructed from G at the support, so G2 is a live
test (every fold pair of the support distinguishes at the minimal G).  The yes-arm
returns the three subtypes `linearDenseAtOrAbove`, `linearDenseRateFailed` and
`linearRealizedDistinguished`, together with the two repeat-arm subtypes
`..._repeatedDistinguished` (the G2 yes-arm after `[153]`'s repeat on the dense
arms).

G audit (`[153]`): the equal-state pair of `[153]` is the (F5) repeat subcase and
continues into the germ path.  `K .coldCutStatesDistinct` is not a fact of the
generic residual; the two dense-arm subtypes `..._repeated` carry
`K .coldRepeatedStateResidual` (the dense ¬(★) arm of `[153]`).
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u

/-- **`[187]` (local cold-terminal exclusion), singleton `linearRealizedSilent`**
(`ColdBranchClosedOutcome`, 104 facts, and 18 extra facts: 122 facts): [153] linear cold mass in `nearCubicRealized`: [158] realized, [146] theta at or above, [154] none realizing / none distinguishing; [157]/[163] G's silent family has a neutral equal-length configuration (`coldAbsorbedNeutralConfiguration`) whose genuine second strand is closed at [167]--[168], so the canonical-replacement arm holds (`coldCanonicalNeutralConfiguration`), and [165]--[166] force `Q = E` (`coldCanonicalReplacementSwap`, `coldCanonicalReplacementTrivial`); [157] the marked germ is not handed off and its replacement is not strictly smaller (`coldMarkedGermUncompressed`); [157] F08: the excision of any path spanning the marked germ's support misses the baseline or leaves a non-accepted cycle length `L + q` in G (`coldMarkedGermStretchExcision`); the incidence structure of the stretch (`coldMarkedGermStretchIncidence`: every interior vertex of a spanning path has degree `t` and `t-2` extra neighbours); [169] `blockedClassMember` is a fact of G here too but is not carried (see `blockedCompressionCap_iff_windowPackageRealized`). -/
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
      erdosReceiverLoadProfile spineData .realizedOrderSmall selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldAbsorbedNeutralConfiguration selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldCanonicalNeutralConfiguration selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldCanonicalReplacementSwap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldCanonicalReplacementTrivial selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMarkedGermUncompressed selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMarkedGermStretchExcision selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMarkedGermStretchIncidence selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMarkedGermPairSuppression selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMarkedGermPairMersenne selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMarkedGermChordSpan selected.object

/-- On the realized arm `[158]` yes, the terminal consequence of `[171]`
(`K .blockedCompressionCap`) is the realization fact `K .windowPackageRealized`
itself, so the additive arm of `[170]` cannot contradict it: the dense arm's
closure pairs the cap with the strict reverse `K .windowPackageUnrealized`, which
is absent here. -/
theorem blockedCompressionCap_iff_windowPackageRealized (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    BlockedCompressionCapStatement data object ↔
      WindowPackageRealizedStatement data object :=
  Iff.rfl

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
    [FactKeys.Has (K .packingOrderBound) known]
    [FactKeys.Has (K .noSuppressionChordViolation) known]
    [FactKeys.Has (K .twoSwitchForcedPath) known]
    [FactKeys.Has (K .crossSwitchFamily) known]
    [FactKeys.Has (K .highCentreSplitForced) known]
    [FactKeys.Has (K .sameVertexSwitchForcedPath) known]
    [FactKeys.Has (K .declaredPairSupportStructure) known]
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
    [FactKeys.Has (K .coldAbsorbedNeutralConfiguration) known]
    [FactKeys.Has (K .coldCanonicalNeutralConfiguration) known]
    [FactKeys.Has (K .coldCanonicalReplacementSwap) known]
    [FactKeys.Has (K .coldCanonicalReplacementTrivial) known]
    [FactKeys.Has (K .coldMarkedGermUncompressed) known]
    [FactKeys.Has (K .coldMarkedGermStretchExcision) known]
    [FactKeys.Has (K .coldMarkedGermStretchIncidence) known]
    [FactKeys.Has (K .coldMarkedGermPairSuppression) known]
    [FactKeys.Has (K .coldMarkedGermPairMersenne) known]
    [FactKeys.Has (K .coldMarkedGermChordSpan) known]
    : ColdBranchClosedOutcome_linearRealizedSilent selected :=
  ⟨coldBranchClosedReturn history,
    (history.get (K .coldGermFamilyPositive)).down,
    (history.get (K .coldGermNoneDistinguishing)).down,
    (history.get (K .coldGermNoneRealizing)).down,
    (history.get (K .coldMassLinear)).down,
    (history.get (K .coldRoute8AtOrAbove)).down,
    (history.get (K .windowPackageRealized)).down,
    (history.get (K .realizedDensityOrder)).down,
    (history.get (K .realizedOrderSmall)).down,
    (history.get (K .coldAbsorbedNeutralConfiguration)).down,
    (history.get (K .coldCanonicalNeutralConfiguration)).down,
    (history.get (K .coldCanonicalReplacementSwap)).down,
    (history.get (K .coldCanonicalReplacementTrivial)).down,
    (history.get (K .coldMarkedGermUncompressed)).down,
    (history.get (K .coldMarkedGermStretchExcision)).down,
    (history.get (K .coldMarkedGermStretchIncidence)).down,
    (history.get (K .coldMarkedGermPairSuppression)).down,
    (history.get (K .coldMarkedGermPairMersenne)).down,
    (history.get (K .coldMarkedGermChordSpan)).down⟩


/-! ## The `[153]` repeat routed into the germ path (G audit)

`lem:cold-corridor-first-failure` continues an (F5) repeat into the germ routing
(`[154]`, G1/G2/G3).
At G a repeat is the first failure of a retained corridor with no earlier event,
so it is a germ of the extracted family, and the rows of `[154]`--`[157]` read
neither `K .coldCutStatesDistinct` nor its absence.  On the dense linear arms
of `[160]` the (★) decision is taken (`[162]` reads it); its ¬(★) arm
runs the germ path to `[157]` and returns `[187]` with the constructed
equal-state pair `K .coldRepeatedStateResidual` as one more fact of the same
ledger.  These are the two `[187]` subtypes of that route. -/

/-- **`[187]` after `[153]`'s repeat, dense arm `[160]` `τ(θ) ≥ 1/4`**: `ColdBranchClosedOutcome` and the constructed equal-state pair, the `[154]` silent facts and the arm facts. -/
abbrev ColdBranchClosedOutcome_linearDenseAtOrAbove_repeated (selected : EGInput.{u}) : Prop :=
  ColdBranchClosedOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRepeatedStateResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermFamilyPositive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermNoneRealizing selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermNoneDistinguishing selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMassLinear selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8AtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyAtOrAbove selected.object

theorem ColdBranchClosedOutcome_linearDenseAtOrAbove_repeated.toGeneric {selected : EGInput.{u}}
    (h : ColdBranchClosedOutcome_linearDenseAtOrAbove_repeated selected) : ColdBranchClosedOutcome selected :=
  h.1

/-- **`[187]` after `[153]`'s repeat, dense arm `[160]` `τ(θ) < 1/4` with the private-carrier rate failed**: `ColdBranchClosedOutcome` and the constructed equal-state pair, the `[154]` silent facts and the arm facts. -/
abbrev ColdBranchClosedOutcome_linearDenseRateFailed_repeated (selected : EGInput.{u}) : Prop :=
  ColdBranchClosedOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRepeatedStateResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermFamilyPositive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermNoneRealizing selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermNoneDistinguishing selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMassLinear selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8AtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyBelow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8RateFails selected.object

theorem ColdBranchClosedOutcome_linearDenseRateFailed_repeated.toGeneric {selected : EGInput.{u}}
    (h : ColdBranchClosedOutcome_linearDenseRateFailed_repeated selected) : ColdBranchClosedOutcome selected :=
  h.1

/-- The return of the two repeated `[187]` subtypes on the `[160]` arm named by `tau`:
one `get` per fact. -/
theorem coldBranchClosed_denseRepeatedReturn
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
    [FactKeys.Has (K .packingOrderBound) known]
    [FactKeys.Has (K .noSuppressionChordViolation) known]
    [FactKeys.Has (K .twoSwitchForcedPath) known]
    [FactKeys.Has (K .crossSwitchFamily) known]
    [FactKeys.Has (K .highCentreSplitForced) known]
    [FactKeys.Has (K .sameVertexSwitchForcedPath) known]
    [FactKeys.Has (K .declaredPairSupportStructure) known]
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
    [FactKeys.Has (K .coldRepeatedStateResidual) known]
    [FactKeys.Has (K .coldGermFamilyPositive) known]
    [FactKeys.Has (K .coldGermNoneDistinguishing) known]
    [FactKeys.Has (K .coldGermNoneRealizing) known]
    [FactKeys.Has (K .windowPackageUnrealized) known]
    [FactKeys.Has (K .coldRoute8AtOrAbove) known]
    [FactKeys.Has (K .coldMassLinear) known]
    (tau : DenseTauArm selected) :
    ColdBranchClosedOutcome_linearDenseAtOrAbove_repeated selected ∨
      ColdBranchClosedOutcome_linearDenseRateFailed_repeated selected := by
  rcases tau with t | t
  · exact Or.inl ⟨coldBranchClosedReturn history,
      (history.get (K .coldRepeatedStateResidual)).down,
      (history.get (K .coldGermFamilyPositive)).down,
      (history.get (K .coldGermNoneRealizing)).down,
      (history.get (K .coldGermNoneDistinguishing)).down,
      (history.get (K .coldMassLinear)).down,
      (history.get (K .coldRoute8AtOrAbove)).down,
      (history.get (K .windowPackageUnrealized)).down,
      t⟩
  · exact Or.inr ⟨coldBranchClosedReturn history,
      (history.get (K .coldRepeatedStateResidual)).down,
      (history.get (K .coldGermFamilyPositive)).down,
      (history.get (K .coldGermNoneRealizing)).down,
      (history.get (K .coldGermNoneDistinguishing)).down,
      (history.get (K .coldMassLinear)).down,
      (history.get (K .coldRoute8AtOrAbove)).down,
      (history.get (K .windowPackageUnrealized)).down,
      t.1, t.2⟩


/-! ## `[154]`'s G2 yes-arm

With the second representative `E` a piece constructed from G, G2 is a live test
(`Graph/ColdGermConstructed.lean`); its yes-arm returns `[187]` on the linear arm
as the subtypes below, one per root path. -/

/-- **`[187]` (local cold-terminal exclusion), subtype `linearDenseAtOrAbove`**: [153] (★) arm, [162] heavy entry, [160] `τ(θ) ≥ 1/4` on the unrealized package;
the `[154]` G2 yes-arm `K .coldGermSomeDistinguishing` in its G form: some
active germ's constructed second representative `E` (`GConstructedPiece`,
`BoundedGerm.HasCanonicalSecond`) has a target response in `G − Z`
(`BoundedGerm.DistinguishingAt` at `E`), with `K .coldGermDistinguished`
(the test is `E`'s response, and every fold pair of the support distinguishes,
`distinguishingAt_fold`) and `K .coldGermRouted` (every shortening germ is G2). -/
abbrev ColdBranchClosedOutcome_linearDenseAtOrAbove (selected : EGInput.{u}) : Prop :=
  ColdBranchClosedOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldCutStatesDistinct selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldHeavyEntryTerminal selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseColdCorridorsTerminal selected.object ∧
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
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyAtOrAbove selected.object

theorem ColdBranchClosedOutcome_linearDenseAtOrAbove.toGeneric {selected : EGInput.{u}}
    (h : ColdBranchClosedOutcome_linearDenseAtOrAbove selected) : ColdBranchClosedOutcome selected :=
  h.1

/-- **`[187]` (local cold-terminal exclusion), subtype `linearDenseRateFailed`**: [153] (★) arm, [162] heavy entry, [160] `τ(θ) < 1/4` with the private-carrier rate failed;
the `[154]` G2 yes-arm `K .coldGermSomeDistinguishing` in its G form: some
active germ's constructed second representative `E` (`GConstructedPiece`,
`BoundedGerm.HasCanonicalSecond`) has a target response in `G − Z`
(`BoundedGerm.DistinguishingAt` at `E`), with `K .coldGermDistinguished`
(the test is `E`'s response, and every fold pair of the support distinguishes,
`distinguishingAt_fold`) and `K .coldGermRouted` (every shortening germ is G2). -/
abbrev ColdBranchClosedOutcome_linearDenseRateFailed (selected : EGInput.{u}) : Prop :=
  ColdBranchClosedOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldCutStatesDistinct selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldHeavyEntryTerminal selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseColdCorridorsTerminal selected.object ∧
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
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyBelow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8RateFails selected.object

theorem ColdBranchClosedOutcome_linearDenseRateFailed.toGeneric {selected : EGInput.{u}}
    (h : ColdBranchClosedOutcome_linearDenseRateFailed selected) : ColdBranchClosedOutcome selected :=
  h.1

/-- **`[187]` (local cold-terminal exclusion), subtype `linearRealizedDistinguished`**: [153] linear arm of the realized package [158], [146] `θ` at or above, `n < N₀`;
the `[154]` G2 yes-arm `K .coldGermSomeDistinguishing` in its G form: some
active germ's constructed second representative `E` (`GConstructedPiece`,
`BoundedGerm.HasCanonicalSecond`) has a target response in `G − Z`
(`BoundedGerm.DistinguishingAt` at `E`), with `K .coldGermDistinguished`
(the test is `E`'s response, and every fold pair of the support distinguishes,
`distinguishingAt_fold`) and `K .coldGermRouted` (every shortening germ is G2). -/
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
    (h : ColdBranchClosedOutcome_linearRealizedDistinguished selected) : ColdBranchClosedOutcome selected :=
  h.1

/-- **`[187]` (local cold-terminal exclusion), subtype `linearDenseAtOrAbove_repeatedDistinguished`**: [153] repeat (¬(★)) arm, [160] `τ(θ) ≥ 1/4` on the unrealized package;
the `[154]` G2 yes-arm `K .coldGermSomeDistinguishing` in its G form: some
active germ's constructed second representative `E` (`GConstructedPiece`,
`BoundedGerm.HasCanonicalSecond`) has a target response in `G − Z`
(`BoundedGerm.DistinguishingAt` at `E`), with `K .coldGermDistinguished`
(the test is `E`'s response, and every fold pair of the support distinguishes,
`distinguishingAt_fold`) and `K .coldGermRouted` (every shortening germ is G2). -/
abbrev ColdBranchClosedOutcome_linearDenseAtOrAbove_repeatedDistinguished (selected : EGInput.{u}) : Prop :=
  ColdBranchClosedOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRepeatedStateResidual selected.object ∧
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
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyAtOrAbove selected.object

theorem ColdBranchClosedOutcome_linearDenseAtOrAbove_repeatedDistinguished.toGeneric {selected : EGInput.{u}}
    (h : ColdBranchClosedOutcome_linearDenseAtOrAbove_repeatedDistinguished selected) : ColdBranchClosedOutcome selected :=
  h.1

/-- **`[187]` (local cold-terminal exclusion), subtype `linearDenseRateFailed_repeatedDistinguished`**: [153] repeat (¬(★)) arm, [160] `τ(θ) < 1/4` with the private-carrier rate failed;
the `[154]` G2 yes-arm `K .coldGermSomeDistinguishing` in its G form: some
active germ's constructed second representative `E` (`GConstructedPiece`,
`BoundedGerm.HasCanonicalSecond`) has a target response in `G − Z`
(`BoundedGerm.DistinguishingAt` at `E`), with `K .coldGermDistinguished`
(the test is `E`'s response, and every fold pair of the support distinguishes,
`distinguishingAt_fold`) and `K .coldGermRouted` (every shortening germ is G2). -/
abbrev ColdBranchClosedOutcome_linearDenseRateFailed_repeatedDistinguished (selected : EGInput.{u}) : Prop :=
  ColdBranchClosedOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRepeatedStateResidual selected.object ∧
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
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyBelow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8RateFails selected.object

theorem ColdBranchClosedOutcome_linearDenseRateFailed_repeatedDistinguished.toGeneric {selected : EGInput.{u}}
    (h : ColdBranchClosedOutcome_linearDenseRateFailed_repeatedDistinguished selected) : ColdBranchClosedOutcome selected :=
  h.1

/-- The return of the two `denseDistinguished` `[187]` subtypes on the `[160]` arm named by
`tau`: one `get` per fact. -/
theorem coldBranchClosed_denseDistinguishedReturn
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
    [FactKeys.Has (K .packingOrderBound) known]
    [FactKeys.Has (K .noSuppressionChordViolation) known]
    [FactKeys.Has (K .twoSwitchForcedPath) known]
    [FactKeys.Has (K .crossSwitchFamily) known]
    [FactKeys.Has (K .highCentreSplitForced) known]
    [FactKeys.Has (K .sameVertexSwitchForcedPath) known]
    [FactKeys.Has (K .declaredPairSupportStructure) known]
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
    [FactKeys.Has (K .coldCutStatesDistinct) known]
    [FactKeys.Has (K .coldHeavyEntryTerminal) known]
    [FactKeys.Has (K .denseColdCorridorsTerminal) known]
    [FactKeys.Has (K .coldGermFamilyPositive) known]
    [FactKeys.Has (K .coldGermNoneRealizing) known]
    [FactKeys.Has (K .coldGermSomeDistinguishing) known]
    [FactKeys.Has (K .coldMassLinear) known]
    [FactKeys.Has (K .coldRoute8AtOrAbove) known]
    [FactKeys.Has (K .windowPackageUnrealized) known]
    (tau : DenseTauArm selected) :
    ColdBranchClosedOutcome_linearDenseAtOrAbove selected ∨
      ColdBranchClosedOutcome_linearDenseRateFailed selected := by
  rcases tau with t | t
  · exact Or.inl ⟨coldBranchClosedReturn history,
      (history.get (K .coldCutStatesDistinct)).down,
      (history.get (K .coldHeavyEntryTerminal)).down,
      (history.get (K .denseColdCorridorsTerminal)).down,
      (history.get (K .coldGermFamilyPositive)).down,
      (history.get (K .coldGermNoneRealizing)).down,
      (history.get (K .coldGermSomeDistinguishing)).down,
      (history.get (K .coldMassLinear)).down,
      (history.get (K .coldRoute8AtOrAbove)).down,
      (history.get (K .windowPackageUnrealized)).down,
      t⟩
  · exact Or.inr ⟨coldBranchClosedReturn history,
      (history.get (K .coldCutStatesDistinct)).down,
      (history.get (K .coldHeavyEntryTerminal)).down,
      (history.get (K .denseColdCorridorsTerminal)).down,
      (history.get (K .coldGermFamilyPositive)).down,
      (history.get (K .coldGermNoneRealizing)).down,
      (history.get (K .coldGermSomeDistinguishing)).down,
      (history.get (K .coldMassLinear)).down,
      (history.get (K .coldRoute8AtOrAbove)).down,
      (history.get (K .windowPackageUnrealized)).down,
      t.1, t.2⟩

/-- The return of the two `denseRepeatedDistinguished` `[187]` subtypes on the `[160]` arm named by
`tau`: one `get` per fact. -/
theorem coldBranchClosed_denseRepeatedDistinguishedReturn
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
    [FactKeys.Has (K .packingOrderBound) known]
    [FactKeys.Has (K .noSuppressionChordViolation) known]
    [FactKeys.Has (K .twoSwitchForcedPath) known]
    [FactKeys.Has (K .crossSwitchFamily) known]
    [FactKeys.Has (K .highCentreSplitForced) known]
    [FactKeys.Has (K .sameVertexSwitchForcedPath) known]
    [FactKeys.Has (K .declaredPairSupportStructure) known]
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
    [FactKeys.Has (K .coldRepeatedStateResidual) known]
    [FactKeys.Has (K .coldGermFamilyPositive) known]
    [FactKeys.Has (K .coldGermNoneRealizing) known]
    [FactKeys.Has (K .coldGermSomeDistinguishing) known]
    [FactKeys.Has (K .coldMassLinear) known]
    [FactKeys.Has (K .coldRoute8AtOrAbove) known]
    [FactKeys.Has (K .windowPackageUnrealized) known]
    (tau : DenseTauArm selected) :
    ColdBranchClosedOutcome_linearDenseAtOrAbove_repeatedDistinguished selected ∨
      ColdBranchClosedOutcome_linearDenseRateFailed_repeatedDistinguished selected := by
  rcases tau with t | t
  · exact Or.inl ⟨coldBranchClosedReturn history,
      (history.get (K .coldRepeatedStateResidual)).down,
      (history.get (K .coldGermFamilyPositive)).down,
      (history.get (K .coldGermNoneRealizing)).down,
      (history.get (K .coldGermSomeDistinguishing)).down,
      (history.get (K .coldMassLinear)).down,
      (history.get (K .coldRoute8AtOrAbove)).down,
      (history.get (K .windowPackageUnrealized)).down,
      t⟩
  · exact Or.inr ⟨coldBranchClosedReturn history,
      (history.get (K .coldRepeatedStateResidual)).down,
      (history.get (K .coldGermFamilyPositive)).down,
      (history.get (K .coldGermNoneRealizing)).down,
      (history.get (K .coldGermSomeDistinguishing)).down,
      (history.get (K .coldMassLinear)).down,
      (history.get (K .coldRoute8AtOrAbove)).down,
      (history.get (K .windowPackageUnrealized)).down,
      t.1, t.2⟩

/-- The return of `ColdBranchClosedOutcome_linearRealizedDistinguished`: one `get`
per fact. -/
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
    [FactKeys.Has (K .packingOrderBound) known]
    [FactKeys.Has (K .noSuppressionChordViolation) known]
    [FactKeys.Has (K .twoSwitchForcedPath) known]
    [FactKeys.Has (K .crossSwitchFamily) known]
    [FactKeys.Has (K .highCentreSplitForced) known]
    [FactKeys.Has (K .sameVertexSwitchForcedPath) known]
    [FactKeys.Has (K .declaredPairSupportStructure) known]
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
    [FactKeys.Has (K .coldGermNoneRealizing) known]
    [FactKeys.Has (K .coldGermSomeDistinguishing) known]
    [FactKeys.Has (K .coldMassLinear) known]
    [FactKeys.Has (K .coldRoute8AtOrAbove) known]
    [FactKeys.Has (K .windowPackageRealized) known]
    [FactKeys.Has (K .realizedDensityOrder) known]
    [FactKeys.Has (K .realizedOrderSmall) known] :
    ColdBranchClosedOutcome_linearRealizedDistinguished selected :=
  ⟨coldBranchClosedReturn history,
      (history.get (K .coldGermFamilyPositive)).down,
      (history.get (K .coldGermNoneRealizing)).down,
      (history.get (K .coldGermSomeDistinguishing)).down,
      (history.get (K .coldMassLinear)).down,
      (history.get (K .coldRoute8AtOrAbove)).down,
      (history.get (K .windowPackageRealized)).down,
      (history.get (K .realizedDensityOrder)).down,
      (history.get (K .realizedOrderSmall)).down⟩

/-- The linear-arm subtypes of the residual `[187]` (local cold-terminal
exclusion), returned on the `[153]` linear arm of the near-cubic survivor: the
silent singleton; the two reached through `[153]`'s repeat on the dense arms
(silent); and, on `[154]`'s G2 yes-arm (live with the constructed second
representative), the two dense (★) subtypes, the realized subtype and the two
dense repeat subtypes. -/
abbrev ColdBranchClosedLinearSubtypes (selected : EGInput.{u}) : Prop :=
  ColdBranchClosedOutcome_linearRealizedSilent selected ∨
  (ColdBranchClosedOutcome_linearDenseAtOrAbove_repeated selected ∨
    ColdBranchClosedOutcome_linearDenseRateFailed_repeated selected) ∨
  (ColdBranchClosedOutcome_linearDenseAtOrAbove selected ∨
    ColdBranchClosedOutcome_linearDenseRateFailed selected) ∨
  ColdBranchClosedOutcome_linearRealizedDistinguished selected ∨
  (ColdBranchClosedOutcome_linearDenseAtOrAbove_repeatedDistinguished selected ∨
    ColdBranchClosedOutcome_linearDenseRateFailed_repeatedDistinguished selected)

end HypostructureErdos64EG
