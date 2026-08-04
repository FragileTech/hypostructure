import Hypostructure.Core.Strategy.Data

/-!
# Closed identifiers for framework-owned strategy execution

This module contains no executable strategy supplied by an application.  It
is the declarative half of the replacement registry boundary: a proof author
may select an official identifier and a problem-data slot, while the Core
compiler resolves the identifier by closed pattern matching.

The constructors intentionally carry no functions, propositions, proofs,
stages, contracts, routes, outcomes, or terminal values.
-/

namespace Hypostructure.Core.Strategy.OfficialRegistry

/-- Framework layers which may own an implementation.  These are framework
domains, not application namespaces. -/
inductive Owner where
  | core
  | graph
  | pde
  deriving DecidableEq, Repr, Inhabited

/-- The exhaustive **residual-continuation** shape promised by an official
strategy family.

Framework-owned target closure is deliberately not counted here: a strategy
which either closes the target or returns one avoidance residual is `linear`,
not `binary`.  Applications cannot provide either this metadata or a terminal
classifier. -/
inductive TerminalShape where
  | linear
  | binary
  | finite
  deriving DecidableEq, Repr, Inhabited

/-- Closed, problem-agnostic strategy identifiers.

Adding execution machinery requires adding a constructor in the framework
and a corresponding compiler equation.  Merely defining an application
constant can therefore never add or replace an executor. -/
inductive Id where
  | orderedExhaustion
  | responseClassification
  | capacityAccounting
  | supportLocalization
  | rankBudget
  | closedCodeExhaustion
  | exhaustiveDichotomy
  | targetDecision
  | rootedReturn
  | targetDefectivePeel
  | decoratedFan
  | representedSupportLocalization
  | representedFluxAccounting
  | representedDefectExhaustion
  | derivedResourceAccounting
  | sequentialExtensionFiltration
  | supportComplement
  | functionalRankSplit
  | minimalDeterminationSupport
  | admissibleQuotientRouting
  | minimalCompressionClosure
  | independentStateBudget
  | deletionCriticality
  | highCenterFanIncidence
  | receiverExhaustion
  | canonicalEssentialCarrier
  | privateCarrierSqueeze
  | measuredDefectDescent
  | deletionDefectNoGo
  | pairResponseAccounting
  | canonicalObstructionAssignment
  | tokenCapacityAccounting
  | homogeneousFibrePressure
  | finiteBottleneckExhaustion
  | boundedFirstFailure
  | finiteContextCoverage
  | sameInterfaceResponse
  | canonicalReplacementSearch
  | minimalReplacementClosure
  | minimalCounterexampleSelection
  | inducedPathPacking
  | counterexampleDecision
  | targetReturnAlgebra
  | properCoreExclusion
  | boundaryAtomDecomposition
  | contextUniversalReplacement
  | hereditaryTargetUncompressibility
  | inducedObstructionDecision
  | exactObstructionLabelling
  | packedSupportAccounting
  | scaleThresholdDecision
  | surplusActivationRefinement
  | packedWindowDensity
  | hotColdDensityRefinement
  | remainderCoreExclusion
  | externalIncidenceSupply
  | wedgeSupply
  | rankDropClosure
  | netDeficiencyBudget
  | localFanDeficitClosure
  | receiverSaturation
  | routeEightBurden
  | smallCarrierRouting
  /-- Canonical CT composition strategies.  These replace the detached
  feature executors under `Core/Strategy/Official/Features` and
  `Graph/Strategy/Official/Features`.  Each is a sealed composition of
  CT1--CT17 whose inputs are queries on the literal predecessor and whose
  outputs are successive `Ledger.Extension`s. -/
  | strictReplacement
  | measuredFinitePeel
  | defectiveLoadPeeling
  | finiteResponseCapacity
  | finiteEligibleTokenLedger
  | finiteStateBudget
  | finiteTraceSeparator
  | finiteContextQuotient
  | finiteObstructionAccounting
  | finiteErrorCoefficientSchedule
  | multiplicativeRateTable
  | orderedReceiverPressure
  | finiteEntropyAccounting
  | finiteReplacementClassification
  | finiteObservationRank
  | finiteOverloadGeometry
  | finiteRankCarrierCompression
  | finiteRankEntropySupportComposition
  /-- Graph-owned canonical CT composition strategies.  These replace the
  detached Graph feature executors.  Each is a sealed composition of
  CT1--CT17 whose inputs are graph-derived data stored in the predecessor. -/
  | sparseSurplus
  | supportIncidenceLedger
  | packedWindowTokenLedger
  | contextualQuotientSearch
  | functionalRankQuotient
  | labelledStateBudget
  | universalTargetResponseObstructions
  | highCenterFanClosure
  deriving DecidableEq, Repr, Inhabited

/-- A reference authored in a DAG.  `slot` selects problem presentation data;
it never selects an executor and has no operational interpretation by itself. -/
structure Ref where
  id : Id
  slot : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- Public, non-executable description of a registry entry. -/
structure Descriptor where
  owner : Owner
  terminals : TerminalShape
  recursive : Bool
  /-- Whether the framework implementation may close the registered target
  directly.  Closure is proof-carrying and bypasses residual ports. -/
  closesTarget : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- Total closed registry metadata.  The future private compiler dispatcher
must use the same case split; there is deliberately no extensible map and no
caller-provided resolver. -/
def describe : Id -> Descriptor
  | .orderedExhaustion =>
      { owner := .core, terminals := .finite, recursive := false }
  | .responseClassification =>
      { owner := .core, terminals := .finite, recursive := false }
  | .capacityAccounting =>
      { owner := .core, terminals := .finite, recursive := false }
  | .supportLocalization =>
      { owner := .core, terminals := .finite, recursive := false }
  | .rankBudget =>
      { owner := .core, terminals := .binary, recursive := false }
  | .closedCodeExhaustion =>
      { owner := .core, terminals := .finite, recursive := false }
  | .exhaustiveDichotomy =>
      { owner := .core, terminals := .binary, recursive := false }
  | .targetDecision =>
      { owner := .core, terminals := .linear, recursive := false,
        closesTarget := true }
  | .rootedReturn =>
      { owner := .graph, terminals := .linear, recursive := false,
        closesTarget := true }
  | .targetDefectivePeel =>
      { owner := .graph, terminals := .finite, recursive := true }
  | .decoratedFan =>
      { owner := .graph, terminals := .finite, recursive := false }
  | .representedSupportLocalization =>
      { owner := .pde, terminals := .finite, recursive := false }
  | .representedFluxAccounting =>
      { owner := .pde, terminals := .finite, recursive := false }
  | .representedDefectExhaustion =>
      { owner := .pde, terminals := .finite, recursive := true }
  | .derivedResourceAccounting =>
      { owner := .core, terminals := .linear, recursive := false }
  | .sequentialExtensionFiltration =>
      { owner := .core, terminals := .finite, recursive := false }
  | .supportComplement =>
      { owner := .core, terminals := .linear, recursive := false }
  | .functionalRankSplit =>
      { owner := .core, terminals := .binary, recursive := false }
  | .minimalDeterminationSupport =>
      { owner := .core, terminals := .linear, recursive := false }
  | .admissibleQuotientRouting =>
      { owner := .core, terminals := .finite, recursive := false }
  | .minimalCompressionClosure =>
      { owner := .core, terminals := .linear, recursive := true }
  | .independentStateBudget =>
      { owner := .core, terminals := .linear, recursive := false,
        closesTarget := true }
  | .deletionCriticality =>
      { owner := .graph, terminals := .linear, recursive := false }
  | .highCenterFanIncidence =>
      { owner := .graph, terminals := .linear, recursive := false }
  | .receiverExhaustion =>
      { owner := .graph, terminals := .binary, recursive := true,
        closesTarget := true }
  | .canonicalEssentialCarrier =>
      { owner := .core, terminals := .linear, recursive := false }
  | .privateCarrierSqueeze =>
      { owner := .core, terminals := .binary, recursive := false }
  | .measuredDefectDescent =>
      { owner := .core, terminals := .linear, recursive := true }
  | .deletionDefectNoGo =>
      { owner := .core, terminals := .linear, recursive := false }
  | .pairResponseAccounting =>
      { owner := .core, terminals := .finite, recursive := false }
  | .canonicalObstructionAssignment =>
      { owner := .core, terminals := .linear, recursive := false }
  | .tokenCapacityAccounting =>
      { owner := .core, terminals := .linear, recursive := false }
  | .homogeneousFibrePressure =>
      { owner := .core, terminals := .binary, recursive := false }
  | .finiteBottleneckExhaustion =>
      { owner := .core, terminals := .binary, recursive := false,
        closesTarget := true }
  | .boundedFirstFailure =>
      { owner := .core, terminals := .finite, recursive := false }
  | .finiteContextCoverage =>
      { owner := .core, terminals := .linear, recursive := false }
  | .sameInterfaceResponse =>
      { owner := .core, terminals := .finite, recursive := false }
  | .canonicalReplacementSearch =>
      { owner := .core, terminals := .finite, recursive := false }
  | .minimalReplacementClosure =>
      { owner := .core, terminals := .linear, recursive := true }
  | .minimalCounterexampleSelection =>
      { owner := .core, terminals := .linear, recursive := false }
  | .inducedPathPacking =>
      { owner := .graph, terminals := .finite, recursive := false }
  | .counterexampleDecision =>
      { owner := .core, terminals := .linear, recursive := false,
        closesTarget := true }
  | .targetReturnAlgebra =>
      { owner := .graph, terminals := .linear, recursive := false }
  | .properCoreExclusion =>
      { owner := .core, terminals := .linear, recursive := false }
  | .boundaryAtomDecomposition =>
      { owner := .graph, terminals := .linear, recursive := false }
  | .contextUniversalReplacement =>
      { owner := .core, terminals := .finite, recursive := false }
  | .hereditaryTargetUncompressibility =>
      { owner := .core, terminals := .linear, recursive := false }
  | .inducedObstructionDecision =>
      { owner := .graph, terminals := .linear, recursive := false,
        closesTarget := true }
  | .exactObstructionLabelling =>
      { owner := .graph, terminals := .linear, recursive := false }
  | .packedSupportAccounting =>
      { owner := .graph, terminals := .linear, recursive := false }
  | .scaleThresholdDecision =>
      { owner := .core, terminals := .binary, recursive := false }
  | .surplusActivationRefinement =>
      { owner := .graph, terminals := .linear, recursive := false }
  | .packedWindowDensity =>
      { owner := .core, terminals := .linear, recursive := false,
        closesTarget := true }
  | .hotColdDensityRefinement =>
      { owner := .core, terminals := .finite, recursive := false,
        closesTarget := true }
  | .remainderCoreExclusion =>
      { owner := .core, terminals := .linear, recursive := false }
  | .externalIncidenceSupply =>
      { owner := .core, terminals := .linear, recursive := false }
  | .wedgeSupply =>
      { owner := .graph, terminals := .linear, recursive := false }
  | .rankDropClosure =>
      { owner := .core, terminals := .linear, recursive := false }
  | .netDeficiencyBudget =>
      { owner := .core, terminals := .linear, recursive := false,
        closesTarget := true }
  | .localFanDeficitClosure =>
      { owner := .graph, terminals := .linear, recursive := false,
        closesTarget := true }
  | .receiverSaturation =>
      { owner := .core, terminals := .linear, recursive := false,
        closesTarget := true }
  | .routeEightBurden =>
      { owner := .core, terminals := .linear, recursive := false }
  | .smallCarrierRouting =>
      { owner := .core, terminals := .linear, recursive := false,
        closesTarget := true }
  | .strictReplacement =>
      { owner := .core, terminals := .finite, recursive := false }
  | .measuredFinitePeel =>
      { owner := .core, terminals := .linear, recursive := false }
  | .defectiveLoadPeeling =>
      { owner := .core, terminals := .linear, recursive := false }
  | .finiteResponseCapacity =>
      { owner := .core, terminals := .finite, recursive := false }
  | .finiteEligibleTokenLedger =>
      { owner := .core, terminals := .linear, recursive := false }
  | .finiteStateBudget =>
      { owner := .core, terminals := .linear, recursive := false,
        closesTarget := true }
  | .finiteTraceSeparator =>
      { owner := .core, terminals := .binary, recursive := false }
  | .finiteContextQuotient =>
      { owner := .core, terminals := .linear, recursive := false }
  | .finiteObstructionAccounting =>
      { owner := .core, terminals := .linear, recursive := false }
  | .finiteErrorCoefficientSchedule =>
      { owner := .core, terminals := .linear, recursive := false }
  | .multiplicativeRateTable =>
      { owner := .core, terminals := .linear, recursive := false }
  | .orderedReceiverPressure =>
      { owner := .core, terminals := .linear, recursive := false }
  | .finiteEntropyAccounting =>
      { owner := .core, terminals := .linear, recursive := false,
        closesTarget := true }
  | .finiteReplacementClassification =>
      { owner := .core, terminals := .linear, recursive := false }
  | .finiteObservationRank =>
      { owner := .core, terminals := .linear, recursive := false }
  | .finiteOverloadGeometry =>
      { owner := .core, terminals := .linear, recursive := false }
  | .finiteRankCarrierCompression =>
      { owner := .core, terminals := .linear, recursive := false }
  | .finiteRankEntropySupportComposition =>
      { owner := .core, terminals := .linear, recursive := false,
        closesTarget := true }
  | .sparseSurplus =>
      { owner := .graph, terminals := .linear, recursive := false }
  | .supportIncidenceLedger =>
      { owner := .graph, terminals := .linear, recursive := false }
  | .packedWindowTokenLedger =>
      { owner := .graph, terminals := .linear, recursive := false }
  | .contextualQuotientSearch =>
      { owner := .graph, terminals := .linear, recursive := false }
  | .functionalRankQuotient =>
      { owner := .graph, terminals := .linear, recursive := false }
  | .labelledStateBudget =>
      { owner := .graph, terminals := .linear, recursive := false,
        closesTarget := true }
  | .universalTargetResponseObstructions =>
      { owner := .graph, terminals := .linear, recursive := false }
  | .highCenterFanClosure =>
      { owner := .graph, terminals := .linear, recursive := false,
        closesTarget := true }

@[simp] theorem describe_owner (id : Id) :
    (describe id).owner =
      match id with
      | .orderedExhaustion | .responseClassification
      | .capacityAccounting | .supportLocalization | .rankBudget
      | .closedCodeExhaustion
      | .exhaustiveDichotomy | .targetDecision
      | .derivedResourceAccounting | .sequentialExtensionFiltration
      | .supportComplement | .functionalRankSplit
      | .minimalDeterminationSupport | .admissibleQuotientRouting
      | .minimalCompressionClosure | .independentStateBudget
      | .canonicalEssentialCarrier | .privateCarrierSqueeze
      | .measuredDefectDescent | .deletionDefectNoGo
      | .pairResponseAccounting | .canonicalObstructionAssignment
      | .tokenCapacityAccounting | .homogeneousFibrePressure
      | .finiteBottleneckExhaustion | .boundedFirstFailure
      | .finiteContextCoverage | .sameInterfaceResponse
      | .canonicalReplacementSearch | .minimalReplacementClosure
      | .minimalCounterexampleSelection | .counterexampleDecision
      | .properCoreExclusion | .contextUniversalReplacement
      | .hereditaryTargetUncompressibility | .packedWindowDensity
      | .scaleThresholdDecision
      | .hotColdDensityRefinement | .remainderCoreExclusion
      | .externalIncidenceSupply | .rankDropClosure
      | .netDeficiencyBudget | .receiverSaturation
      | .routeEightBurden | .smallCarrierRouting
      | .strictReplacement | .measuredFinitePeel
      | .defectiveLoadPeeling | .finiteResponseCapacity
      | .finiteEligibleTokenLedger | .finiteStateBudget
      | .finiteTraceSeparator | .finiteContextQuotient
      | .finiteObstructionAccounting | .finiteErrorCoefficientSchedule
      | .multiplicativeRateTable | .orderedReceiverPressure
      | .finiteEntropyAccounting | .finiteReplacementClassification
      | .finiteObservationRank | .finiteOverloadGeometry
      | .finiteRankCarrierCompression
      | .finiteRankEntropySupportComposition => .core
      | .rootedReturn | .targetDefectivePeel | .decoratedFan
      | .deletionCriticality | .highCenterFanIncidence
      | .receiverExhaustion | .inducedPathPacking
      | .targetReturnAlgebra | .boundaryAtomDecomposition
      | .inducedObstructionDecision | .exactObstructionLabelling
      | .packedSupportAccounting
      | .surplusActivationRefinement
      | .wedgeSupply | .localFanDeficitClosure
      | .sparseSurplus | .supportIncidenceLedger
      | .packedWindowTokenLedger | .contextualQuotientSearch
      | .functionalRankQuotient | .labelledStateBudget
      | .universalTargetResponseObstructions
      | .highCenterFanClosure => .graph
      | .representedSupportLocalization | .representedFluxAccounting
      | .representedDefectExhaustion => .pde := by
  cases id <;> rfl

/-- Registry selections are inert data.  This theorem is useful to frontend
fixtures asserting that changing a slot cannot change implementation
ownership. -/
@[simp] theorem Ref.owner_independent_of_slot (ref : Ref) (slot : Nat) :
    (describe { ref with slot := slot }.id).owner = (describe ref.id).owner :=
  rfl

end Hypostructure.Core.Strategy.OfficialRegistry
