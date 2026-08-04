import Hypostructure.Core.Strategy.Official.Syntax

/-!
# Closed predecessor-capability validation

This is a static companion to the exact ledger query in `Executor`.  The
requirements are fixed by official identifiers.  A program can select an
official strategy but cannot declare, waive, or manufacture its inputs.
-/

namespace Hypostructure.Core.Strategy.Official.CapabilityFlow

open OfficialRegistry

/-- Closed producer requirements for the implemented strategy families. -/
def requirements : Id → List Id
  | .targetReturnAlgebra => [.minimalCounterexampleSelection]
  | .properCoreExclusion => [.targetReturnAlgebra]
  | .deletionCriticality => [.properCoreExclusion]
  | .boundaryAtomDecomposition => [.deletionCriticality]
  | .contextUniversalReplacement => [.boundaryAtomDecomposition]
  | .hereditaryTargetUncompressibility => [.contextUniversalReplacement]
  | .inducedObstructionDecision => [.hereditaryTargetUncompressibility]
  | .inducedPathPacking => [.inducedObstructionDecision]
  | .exactObstructionLabelling => [.inducedPathPacking]
  | .packedSupportAccounting => [.exactObstructionLabelling]
  | .scaleThresholdDecision => [.packedSupportAccounting]
  | .surplusActivationRefinement => [.scaleThresholdDecision]
  | .supportComplement => [.derivedResourceAccounting]
  | .sequentialExtensionFiltration => [.inducedPathPacking, .supportComplement]
  | .functionalRankSplit => [.supportComplement]
  | .minimalDeterminationSupport => [.functionalRankSplit]
  | .admissibleQuotientRouting => [.minimalDeterminationSupport]
  | .minimalCompressionClosure =>
      [.minimalCounterexampleSelection, .admissibleQuotientRouting]
  | .independentStateBudget =>
      [.inducedPathPacking, .functionalRankSplit]
  | .highCenterFanIncidence => [.deletionCriticality]
  | .decoratedFan => [.receiverExhaustion]
  | .localFanDeficitClosure => [.highCenterFanIncidence]
  | .canonicalEssentialCarrier => [.receiverExhaustion]
  | .privateCarrierSqueeze => [.canonicalEssentialCarrier]
  | .measuredDefectDescent => [.privateCarrierSqueeze]
  | .deletionDefectNoGo => [.measuredDefectDescent]
  | .pairResponseAccounting => [.surplusActivationRefinement]
  | .canonicalObstructionAssignment => [.pairResponseAccounting]
  | .tokenCapacityAccounting => [.canonicalObstructionAssignment]
  | .homogeneousFibrePressure => [.tokenCapacityAccounting]
  | .finiteBottleneckExhaustion => [.homogeneousFibrePressure]
  | .boundedFirstFailure => [.sequentialExtensionFiltration]
  | .finiteContextCoverage => [.boundedFirstFailure]
  | .sameInterfaceResponse => [.finiteContextCoverage]
  | .canonicalReplacementSearch =>
      [.minimalCounterexampleSelection, .sameInterfaceResponse]
  | .minimalReplacementClosure => [.canonicalReplacementSearch]
  | .packedWindowDensity =>
      [.exactObstructionLabelling, .finiteBottleneckExhaustion]
  | .hotColdDensityRefinement => [.packedWindowDensity]
  | .remainderCoreExclusion => [.supportComplement]
  | .externalIncidenceSupply => [.remainderCoreExclusion]
  | .wedgeSupply => [.externalIncidenceSupply]
  | .rankDropClosure => [.admissibleQuotientRouting]
  | .netDeficiencyBudget => [.independentStateBudget]
  | .receiverSaturation =>
      [.supportLocalization, .responseClassification]
  | .receiverExhaustion => [.receiverSaturation]
  | .routeEightBurden => [.receiverExhaustion]
  | .smallCarrierRouting =>
      [.routeEightBurden, .canonicalEssentialCarrier]
  | _ => []

/-- Some registered consumers have more than one typed producer family.  The
alternative is selected by the framework terminal that actually reached the
consumer; a problem DAG may satisfy any complete producer family, but never a
proper subset of one. -/
def requirementAlternatives : Id → List (List Id)
  | .routeEightBurden =>
      [[.receiverExhaustion], [.localFanDeficitClosure]]
  | .packedWindowDensity =>
      [[.exactObstructionLabelling, .finiteBottleneckExhaustion],
        [.exactObstructionLabelling, .scaleThresholdDecision]]
  | id => [requirements id]

def containsAll (available required : List Id) : Bool :=
  required.all available.contains

def containsAnyComplete (available : List Id) (alternatives : List (List Id)) : Bool :=
  alternatives.any (containsAll available)

def insert (id : Id) (available : List Id) : List Id :=
  if id ∈ available then available else id :: available

def intersect (left right : List Id) : List Id :=
  left.filter right.contains

def intersectAll : List (List Id) → List Id
  | [] => []
  | head :: tail => tail.foldl intersect head

mutual

/-- Validate one reusable program from a known set of predecessor
capabilities.  The returned list contains exactly the capabilities guaranteed
on every surviving path. -/
def checkFrom : List Id → Program → Option (List Id)
  | available, .done => some available
  | available, .invoke _ ref =>
      if containsAnyComplete available (requirementAlternatives ref.id) then
        some (insert ref.id available)
      else none
  | available, .chain _ head tail => do
      let afterHead ← checkFrom available head
      checkFrom afterHead tail
  | available, .branch _ ref continuations => do
      if !containsAnyComplete available (requirementAlternatives ref.id) then none
      else
        let afterVertex := insert ref.id available
        let outputs ← checkMany afterVertex continuations
        some (intersectAll outputs)
  | available, .join _ branches continuation =>
      match branches with
      | [] => none
      | _ :: _ => do
          let outputs ← checkMany available branches
          checkFrom (intersectAll outputs) continuation

def checkMany : List Id → List Program → Option (List (List Id))
  | _, [] => some []
  | available, head :: tail => do
      let headOutput ← checkFrom available head
      let tailOutputs ← checkMany available tail
      some (headOutput :: tailOutputs)

end

def validFrom (available : List Id) (program : Program) : Bool :=
  (checkFrom available program).isSome

def valid (program : Program) : Bool := validFrom [] program

end Hypostructure.Core.Strategy.Official.CapabilityFlow
