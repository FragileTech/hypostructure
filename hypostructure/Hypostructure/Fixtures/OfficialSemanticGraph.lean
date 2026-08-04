import Hypostructure.Graph.Strategy.Official.Semantics.Terminal

namespace Hypostructure.Fixtures.OfficialSemanticGraph

open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Official
open Hypostructure.Graph.Strategy.Official.Semantics

abbrev completeGraph : FiniteObject where
  Vertex := Fin 3
  graph := ⊤
  vertices := inferInstance
  decideAdj := inferInstance

def data : Presentation where
  object := completeGraph
  target := {
    CycleLengthOK := fun length => length = 3
    cycleLengthDecidable := fun _ => inferInstance
  }

/-- Supported equations return proof-carrying graph terminals. -/
example : Nonempty (Result data .rootedReturn) :=
  ⟨interpret data .rootedReturn⟩

example :
    interpret data .targetDefectivePeel =
      .missing .targetDefectiveQuotientPresentation := rfl

/-- Every currently unsupported graph-owned program operation identifies its
indispensable missing datum exactly. -/
example :
    interpret data .decoratedFan =
      .missing .decoratedFanPresentation := rfl

example :
    interpret data .deletionCriticality =
      .missing .deletionCriticalityPresentation := rfl

example :
    interpret data .highCenterFanIncidence =
      .missing .deletionCriticalityPredecessor := rfl

example :
    interpret data .receiverExhaustion =
      .missing .receiverPresentation := rfl

example :
    interpret data .inducedPathPacking =
      .missing .inducedPathOrder := rfl

/-- The semantic operation mapping is exactly the registered graph-owned ID
mapping used by the official structural program. -/
example :
    [ Operation.rootedReturn, .targetDefectivePeel, .decoratedFan,
      .deletionCriticality, .highCenterFanIncidence, .receiverExhaustion,
      .inducedPathPacking ].map Operation.id =
    [ .rootedReturn, .targetDefectivePeel, .decoratedFan,
      .deletionCriticality, .highCenterFanIncidence, .receiverExhaustion,
      .inducedPathPacking ] := rfl

#print axioms interpret
#print axioms decideReturn

end Hypostructure.Fixtures.OfficialSemanticGraph
