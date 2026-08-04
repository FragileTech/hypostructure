import Hypostructure.Core.Strategy.Official.ProblemDefinition

/-!
# Structural availability of official strategies

Availability is derived solely from a closed strategy identifier and a
bounded slot in the callback-free presentation.  It contains no executor and
does not evaluate application code.
-/

namespace Hypostructure.Core.Strategy.Official

open Core.Strategy.OfficialRegistry

/-- The number of presentation slots canonically available to an official
identifier.  This is a closed framework-owned case split. -/
def slotCount (schema : ProblemSchema) : Id -> Nat
  | .orderedExhaustion => schema.core.schedules.length
  | .responseClassification => schema.core.responseTables.length
  | .capacityAccounting => schema.core.capacityTables.length
  | .supportLocalization => schema.core.supportRelations.length
  | .rankBudget => schema.core.rankTables.length
  | .closedCodeExhaustion => schema.core.closedCodeTables.length
  /- These executors are not application-slot driven.  They become available
  only through a framework-owned predecessor terminal, never through raw
  transition, dichotomy, or target tables in a problem presentation. -/
  | .exhaustiveDichotomy => 0
  | .targetDecision => 0
  | .rootedReturn => schema.graph.rootedReturnTables.length
  | .targetDefectivePeel => schema.graph.targetDefectTables.length
  | .decoratedFan => schema.graph.decoratedFanTables.length
  | .representedSupportLocalization => schema.pde.representedSupports.length
  | .representedFluxAccounting => schema.pde.representedFluxTables.length
  | .representedDefectExhaustion => schema.pde.representedDefectTables.length
  /- Feature strategies are predecessor-capability driven.  A static problem
  slot can never make them available; the semantic compiler enables them only
  after their required typed producers occur in the same ledger branch. -/
  | .derivedResourceAccounting
  | .sequentialExtensionFiltration
  | .supportComplement
  | .functionalRankSplit
  | .minimalDeterminationSupport
  | .admissibleQuotientRouting
  | .minimalCompressionClosure
  | .independentStateBudget
  | .deletionCriticality
  | .highCenterFanIncidence
  | .receiverExhaustion
  | .canonicalEssentialCarrier
  | .privateCarrierSqueeze
  | .measuredDefectDescent
  | .deletionDefectNoGo
  | .pairResponseAccounting
  | .canonicalObstructionAssignment
  | .tokenCapacityAccounting
  | .homogeneousFibrePressure
  | .finiteBottleneckExhaustion
  | .boundedFirstFailure
  | .finiteContextCoverage
  | .sameInterfaceResponse
  | .canonicalReplacementSearch
  | .minimalReplacementClosure => 0
  | .minimalCounterexampleSelection
  | .inducedPathPacking
  | .counterexampleDecision
  | .targetReturnAlgebra
  | .properCoreExclusion
  | .boundaryAtomDecomposition
  | .contextUniversalReplacement
  | .hereditaryTargetUncompressibility
  | .inducedObstructionDecision
  | .exactObstructionLabelling
  | .packedSupportAccounting
  | .scaleThresholdDecision
  | .surplusActivationRefinement
  | .packedWindowDensity
  | .hotColdDensityRefinement
  | .remainderCoreExclusion
  | .externalIncidenceSupply
  | .wedgeSupply
  | .rankDropClosure
  | .netDeficiencyBudget
  | .localFanDeficitClosure
  | .receiverSaturation
  | .routeEightBurden
  | .smallCarrierRouting
  | .strictReplacement
  | .measuredFinitePeel
  | .defectiveLoadPeeling
  | .finiteResponseCapacity
  | .finiteEligibleTokenLedger
  | .finiteStateBudget
  | .finiteTraceSeparator
  | .finiteContextQuotient
  | .finiteObstructionAccounting
  | .finiteErrorCoefficientSchedule
  | .multiplicativeRateTable
  | .orderedReceiverPressure
  | .finiteEntropyAccounting
  | .finiteReplacementClassification
  | .finiteObservationRank
  | .finiteOverloadGeometry
  | .finiteRankCarrierCompression
  | .finiteRankEntropySupportComposition
  | .sparseSurplus
  | .supportIncidenceLedger
  | .packedWindowTokenLedger
  | .contextualQuotientSearch
  | .functionalRankQuotient
  | .labelledStateBudget
  | .universalTargetResponseObstructions
  | .highCenterFanClosure => 0

/-- A reference is available exactly when its inert presentation slot exists.
There is intentionally no constructor accepting a resolver or proof of the
problem target. -/
inductive Available (definition : ProblemDefinition) (ref : StrategyRef) : Prop where
  | intro (slot_lt : ref.slot < slotCount definition.schema ref.id)

instance (definition : ProblemDefinition) (ref : StrategyRef) :
    Decidable (Available definition ref) :=
  if h : ref.slot < slotCount definition.schema ref.id then
    isTrue (.intro h)
  else
    isFalse (fun | .intro hlt => h hlt)

theorem available_iff (definition : ProblemDefinition) (ref : StrategyRef) :
    Available definition ref ↔
      ref.slot < slotCount definition.schema ref.id := by
  constructor
  · intro h
    cases h with
    | intro hlt => exact hlt
  · exact Available.intro

/-- Slot changes can affect availability but can never change executor
ownership. -/
theorem available_owner_fixed
    (definition : ProblemDefinition) (ref : StrategyRef)
    (_ : Available definition ref) :
    (describe ref.id).owner = (describe { ref with slot := 0 }.id).owner :=
  rfl

end Hypostructure.Core.Strategy.Official
