import HypostructureErdos64EG.Assembly.Residuals

/-!
# Assembly: Residuals / Node `[144a]`

The distinct fact sets of the residual `Node144aOutcome` (node `[144a]`,
thm:main (ii), tex 347-353).  Every path into `[144a]` passes through the
class decisions of `[139]`/`[141]` (window, remainder, or primitive class of
the overloading token, audited at `[140]`/`[142]`/`[143]`) and then through
the handoff decision of `[144]` (handoff, or handoff fails).  The six paths
carry six distinct fact sets, each stated here as a subtype of the generic
`Node144aOutcome` (its 87 common facts) with every extra fact as an explicit
`Holds` conjunct, plus one return theorem per subtype reading each fact with
one `ExactLedger.get`.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u

/-- **Node `[144a]`**, subtype `windowHandoff`: [139] token in 𝔗_W, yes arm; audited at [140]; handoff arm of [144].
The generic 87 common facts and 3 extra facts (90 facts in all). -/
abbrev Node144aOutcome_windowHandoff (selected : EGInput.{u}) : Prop :=
  Node144aOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowClassOverload selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBHandoff selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBFanEntry selected.object

/-- `Node144aOutcome_windowHandoff` is a case of the generic residual. -/
theorem Node144aOutcome_windowHandoff.toGeneric {selected : EGInput.{u}}
    (h : Node144aOutcome_windowHandoff selected) : Node144aOutcome selected :=
  h.1

/-- **Node `[144a]`**, subtype `windowFails`: [139] token in 𝔗_W, yes arm; audited at [140]; handoff-fails arm of [144] (the paper error).
The generic 87 common facts and 5 extra facts (92 facts in all). -/
abbrev Node144aOutcome_windowFails (selected : EGInput.{u}) : Prop :=
  Node144aOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowClassOverload selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBHandoffFails selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sameTokenPatternUnresolved selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sameTokenReadingsNotReplacement selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sameTokenPairPartition selected.object

/-- `Node144aOutcome_windowFails` is a case of the generic residual. -/
theorem Node144aOutcome_windowFails.toGeneric {selected : EGInput.{u}}
    (h : Node144aOutcome_windowFails selected) : Node144aOutcome selected :=
  h.1

/-- **Node `[144a]`**, subtype `remainderHandoff`: [139] no, [141] token in 𝔗_R, yes arm; audited at [142]; handoff arm of [144].
The generic 87 common facts and 4 extra facts (91 facts in all). -/
abbrev Node144aOutcome_remainderHandoff (selected : EGInput.{u}) : Prop :=
  Node144aOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowClassAbsent selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderClassOverload selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBHandoff selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBFanEntry selected.object

/-- `Node144aOutcome_remainderHandoff` is a case of the generic residual. -/
theorem Node144aOutcome_remainderHandoff.toGeneric {selected : EGInput.{u}}
    (h : Node144aOutcome_remainderHandoff selected) : Node144aOutcome selected :=
  h.1

/-- **Node `[144a]`**, subtype `remainderFails`: [139] no, [141] token in 𝔗_R, yes arm; audited at [142]; handoff-fails arm of [144] (the paper error).
The generic 87 common facts and 6 extra facts (93 facts in all). -/
abbrev Node144aOutcome_remainderFails (selected : EGInput.{u}) : Prop :=
  Node144aOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowClassAbsent selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderClassOverload selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBHandoffFails selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sameTokenPatternUnresolved selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sameTokenReadingsNotReplacement selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sameTokenPairPartition selected.object

/-- `Node144aOutcome_remainderFails` is a case of the generic residual. -/
theorem Node144aOutcome_remainderFails.toGeneric {selected : EGInput.{u}}
    (h : Node144aOutcome_remainderFails selected) : Node144aOutcome selected :=
  h.1

/-- **Node `[144a]`**, subtype `primitiveHandoff`: [139] no, [141] no: the primitive class; audited at [143]; handoff arm of [144].
The generic 87 common facts and 5 extra facts (92 facts in all). -/
abbrev Node144aOutcome_primitiveHandoff (selected : EGInput.{u}) : Prop :=
  Node144aOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowClassAbsent selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderClassAbsent selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .primitiveClassOverload selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBHandoff selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBFanEntry selected.object

/-- `Node144aOutcome_primitiveHandoff` is a case of the generic residual. -/
theorem Node144aOutcome_primitiveHandoff.toGeneric {selected : EGInput.{u}}
    (h : Node144aOutcome_primitiveHandoff selected) : Node144aOutcome selected :=
  h.1

/-- **Node `[144a]`**, subtype `primitiveFails`: [139] no, [141] no: the primitive class; audited at [143]; handoff-fails arm of [144] (the paper error).
The generic 87 common facts and 7 extra facts (94 facts in all). -/
abbrev Node144aOutcome_primitiveFails (selected : EGInput.{u}) : Prop :=
  Node144aOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowClassAbsent selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderClassAbsent selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .primitiveClassOverload selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBHandoffFails selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sameTokenPatternUnresolved selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sameTokenReadingsNotReplacement selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sameTokenPairPartition selected.object

/-- `Node144aOutcome_primitiveFails` is a case of the generic residual. -/
theorem Node144aOutcome_primitiveFails.toGeneric {selected : EGInput.{u}}
    (h : Node144aOutcome_primitiveFails selected) : Node144aOutcome selected :=
  h.1

section Returns

variable {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}

variable [FactKeys.Has (K .selection) known]
variable [FactKeys.Has (K .cubicBaseline) known]
variable [FactKeys.Has (K .minDegreeBaseline) known]
variable [FactKeys.Has (K .returnAvoidance) known]
variable [FactKeys.Has (K .noProperBaseline) known]
variable [FactKeys.Has (K .slackIndependent) known]
variable [FactKeys.Has (K .tightEndpoint) known]
variable [FactKeys.Has (K .cycleRankConstraint) known]
variable [FactKeys.Has (K .degreeProfileFibres) known]
variable [FactKeys.Has (K .targetCompleteContextUniversality) known]
variable [FactKeys.Has (K .replacementExclusion) known]
variable [FactKeys.Has (K .uncompressible) known]
variable [FactKeys.Has (K .windowPresent) known]
variable [FactKeys.Has (K .maximalPacking) known]
variable [FactKeys.Has (K .localAlgebra) known]
variable [FactKeys.Has (K .everyWitnessSpectrumSplit) known]
variable [FactKeys.Has (K .packingOrderBound) known]
variable [FactKeys.Has (K .noSuppressionChordViolation) known]
variable [FactKeys.Has (K .twoSwitchForcedPath) known]
variable [FactKeys.Has (K .crossSwitchFamily) known]
variable [FactKeys.Has (K .highCentreSplitForced) known]
variable [FactKeys.Has (K .sameVertexSwitchForcedPath) known]
variable [FactKeys.Has (K .specWitnessStructure) known]
variable [FactKeys.Has (K .remainderDeficiencyBelowCut) known]
variable [FactKeys.Has (K .windowCutCapacity) known]
variable [FactKeys.Has (K .primitiveCarrierCount) known]
variable [FactKeys.Has (K .singleBoundaryShape) known]
variable [FactKeys.Has (K .neighbourhoodPairCount) known]
variable [FactKeys.Has (K .starCycleConstraint) known]
variable [FactKeys.Has (K .meetingCycleConstraint) known]
variable [FactKeys.Has (K .highDegreePairSum) known]
variable [FactKeys.Has (K .vertexDeletionComponents) known]
variable [FactKeys.Has (K .cyclesThroughVertex) known]
variable [FactKeys.Has (K .cutVertexBlockPaths) known]
variable [FactKeys.Has (K .cycleDoubleCount) known]
variable [FactKeys.Has (K .surplusDartIdentity) known]
variable [FactKeys.Has (K .highDegreeCountBound) known]
variable [FactKeys.Has (K .admissibleQuotientsLabelInjective) known]
variable [FactKeys.Has (K .surplusAbove) known]
variable [FactKeys.Has (K .highSurplusConfiguration) known]
variable [FactKeys.Has (K .highEndpointSwitch) known]
variable [FactKeys.Has (K .edgeSurplusIdentity) known]
variable [FactKeys.Has (K .ceilSqrtAboveScale) known]
variable [FactKeys.Has (K .orderAboveScaleSquare) known]
variable [FactKeys.Has (K .sixVertexExtremalEnvelope) known]
variable [FactKeys.Has (K .highDegreePositive) known]
variable [FactKeys.Has (K .highDegreeSurplusCapacity) known]
variable [FactKeys.Has (K .canonicalCapacityExplicit) known]
variable [FactKeys.Has (K .canonicalTokenCount) known]
variable [FactKeys.Has (K .canonicalBlockedFreePartition) known]
variable [FactKeys.Has (K .canonicalLedgerDeficit) known]
variable [FactKeys.Has (K .pairCountDeficit) known]
variable [FactKeys.Has (K .canonicalCertificationCriterion) known]
variable [FactKeys.Has (K .canonicalOverloadOfFits) known]
variable [FactKeys.Has (K .canonicalFreeExcessOfCapped) known]
variable [FactKeys.Has (K .paperBudgetBound) known]
variable [FactKeys.Has (K .paperBudgetCertifies) known]
variable [FactKeys.Has (K .pairCodeConfiguration) known]
variable [FactKeys.Has (K .sparseSurplusSurvivor) known]
variable [FactKeys.Has (K .openPortSuppression) known]
variable [FactKeys.Has (K .openPortSuppressionSafe) known]
variable [FactKeys.Has (K .singleOpenPortSuppressionWitness) known]
variable [FactKeys.Has (K .suppressedFamilyCriticalCycle) known]
variable [FactKeys.Has (K .sparseSlackSurplus) known]
variable [FactKeys.Has (K .activeSurplusFamily) known]
variable [FactKeys.Has (K .sparsePortActivation) known]
variable [FactKeys.Has (K .activeSurplusDemands) known]
variable [FactKeys.Has (K .baselineSpineDemand) known]
variable [FactKeys.Has (K .freePairCountFails) known]
variable [FactKeys.Has (K .dependentPairFamily) known]
variable [FactKeys.Has (K .pairDegreeProfileFibres) known]
variable [FactKeys.Has (K .pairNoProfileObstruction) known]
variable [FactKeys.Has (K .pairNoResponseObstruction) known]
variable [FactKeys.Has (K .blockedPairNoExit) known]
variable [FactKeys.Has (K .canonicalBlockerRoute) known]
variable [FactKeys.Has (K .canonicalPairLedger) known]
variable [FactKeys.Has (K .sparseUpperEnvelope) known]
variable [FactKeys.Has (K .capacityTokenLedger) known]
variable [FactKeys.Has (K .blockedPairEntropySetup) known]
variable [FactKeys.Has (K .blockedPairEntropySandwich) known]
variable [FactKeys.Has (K .roleFibrePartition) known]
variable [FactKeys.Has (K .fibrePressure) known]
variable [FactKeys.Has (K .sparsePressureOverload) known]
variable [FactKeys.Has (K .bridgeless) known]
variable [FactKeys.Has (K .highCentreNormalForm) known]
variable [FactKeys.Has (K .homogeneousBottleneckPattern) known]
variable [FactKeys.Has (K .homogeneousCapsFail) known]
variable [FactKeys.Has (K .bottleneckRouting) known]
variable [FactKeys.Has (K .sameTokenPatternSupports) known]
variable [FactKeys.Has (K .sameTokenPatternSwap) known]

/-- The return of `Node144aOutcome_windowHandoff`: one `get` per fact of its ledger. -/
theorem node144aWindowHandoffReturn
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .windowClassOverload) known]
    [FactKeys.Has (K .typeBHandoff) known]
    [FactKeys.Has (K .typeBFanEntry) known] :
    Node144aOutcome_windowHandoff selected :=
  ⟨node144aReturn history,
    (history.get (K .windowClassOverload)).down,
    (history.get (K .typeBHandoff)).down,
    (history.get (K .typeBFanEntry)).down⟩

/-- The return of `Node144aOutcome_windowFails`: one `get` per fact of its ledger. -/
theorem node144aWindowFailsReturn
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .windowClassOverload) known]
    [FactKeys.Has (K .typeBHandoffFails) known]
    [FactKeys.Has (K .sameTokenPatternUnresolved) known]
    [FactKeys.Has (K .sameTokenReadingsNotReplacement) known]
    [FactKeys.Has (K .sameTokenPairPartition) known] :
    Node144aOutcome_windowFails selected :=
  ⟨node144aReturn history,
    (history.get (K .windowClassOverload)).down,
    (history.get (K .typeBHandoffFails)).down,
    (history.get (K .sameTokenPatternUnresolved)).down,
    (history.get (K .sameTokenReadingsNotReplacement)).down,
    (history.get (K .sameTokenPairPartition)).down⟩

/-- The return of `Node144aOutcome_remainderHandoff`: one `get` per fact of its ledger. -/
theorem node144aRemainderHandoffReturn
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .windowClassAbsent) known]
    [FactKeys.Has (K .remainderClassOverload) known]
    [FactKeys.Has (K .typeBHandoff) known]
    [FactKeys.Has (K .typeBFanEntry) known] :
    Node144aOutcome_remainderHandoff selected :=
  ⟨node144aReturn history,
    (history.get (K .windowClassAbsent)).down,
    (history.get (K .remainderClassOverload)).down,
    (history.get (K .typeBHandoff)).down,
    (history.get (K .typeBFanEntry)).down⟩

/-- The return of `Node144aOutcome_remainderFails`: one `get` per fact of its ledger. -/
theorem node144aRemainderFailsReturn
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .windowClassAbsent) known]
    [FactKeys.Has (K .remainderClassOverload) known]
    [FactKeys.Has (K .typeBHandoffFails) known]
    [FactKeys.Has (K .sameTokenPatternUnresolved) known]
    [FactKeys.Has (K .sameTokenReadingsNotReplacement) known]
    [FactKeys.Has (K .sameTokenPairPartition) known] :
    Node144aOutcome_remainderFails selected :=
  ⟨node144aReturn history,
    (history.get (K .windowClassAbsent)).down,
    (history.get (K .remainderClassOverload)).down,
    (history.get (K .typeBHandoffFails)).down,
    (history.get (K .sameTokenPatternUnresolved)).down,
    (history.get (K .sameTokenReadingsNotReplacement)).down,
    (history.get (K .sameTokenPairPartition)).down⟩

/-- The return of `Node144aOutcome_primitiveHandoff`: one `get` per fact of its ledger. -/
theorem node144aPrimitiveHandoffReturn
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .windowClassAbsent) known]
    [FactKeys.Has (K .remainderClassAbsent) known]
    [FactKeys.Has (K .primitiveClassOverload) known]
    [FactKeys.Has (K .typeBHandoff) known]
    [FactKeys.Has (K .typeBFanEntry) known] :
    Node144aOutcome_primitiveHandoff selected :=
  ⟨node144aReturn history,
    (history.get (K .windowClassAbsent)).down,
    (history.get (K .remainderClassAbsent)).down,
    (history.get (K .primitiveClassOverload)).down,
    (history.get (K .typeBHandoff)).down,
    (history.get (K .typeBFanEntry)).down⟩

/-- The return of `Node144aOutcome_primitiveFails`: one `get` per fact of its ledger. -/
theorem node144aPrimitiveFailsReturn
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .windowClassAbsent) known]
    [FactKeys.Has (K .remainderClassAbsent) known]
    [FactKeys.Has (K .primitiveClassOverload) known]
    [FactKeys.Has (K .typeBHandoffFails) known]
    [FactKeys.Has (K .sameTokenPatternUnresolved) known]
    [FactKeys.Has (K .sameTokenReadingsNotReplacement) known]
    [FactKeys.Has (K .sameTokenPairPartition) known] :
    Node144aOutcome_primitiveFails selected :=
  ⟨node144aReturn history,
    (history.get (K .windowClassAbsent)).down,
    (history.get (K .remainderClassAbsent)).down,
    (history.get (K .primitiveClassOverload)).down,
    (history.get (K .typeBHandoffFails)).down,
    (history.get (K .sameTokenPatternUnresolved)).down,
    (history.get (K .sameTokenReadingsNotReplacement)).down,
    (history.get (K .sameTokenPairPartition)).down⟩

end Returns

end HypostructureErdos64EG
