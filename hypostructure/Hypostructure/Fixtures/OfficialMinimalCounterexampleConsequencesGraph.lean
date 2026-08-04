import Hypostructure.Graph.Strategy.Official.Features.MinimalCounterexampleConsequences

namespace Hypostructure.Fixtures.OfficialMinimalCounterexampleConsequencesGraph

open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Official.Features

def triangleGraph : SimpleGraph (Fin 3) :=
  SimpleGraph.fromRel fun left right => left ≠ right

def triangle : FiniteObject where
  Vertex := Fin 3
  graph := triangleGraph
  vertices := by infer_instance
  decideAdj := by
    intro left right
    simp [triangleGraph]
    infer_instance

def baseline : DeletionCriticalityProfile (MinimumDegreeAtLeast 2) :=
  minimumDegreeDeletionCriticalityProfile 2

noncomputable def sparseResult :=
  SparseDeletionEnvelope.execute baseline triangle

noncomputable def bridgeResult :
    CanonicalBridgeQuotient.Result
      (HasCycleWithLength fun length => length = 3) triangle :=
  CanonicalBridgeQuotient.execute
    (HasCycleWithLength fun length => length = 3)
    (some {
      invariant := cycleTargetInterface _
      hereditary := cycleProperSubgraphTargetMonotone _
    }) triangle

noncomputable def missingLawResult :
    CanonicalBridgeQuotient.Result (fun _ => False) triangle :=
  CanonicalBridgeQuotient.execute (fun _ => False) none triangle

noncomputable def pathResult :=
  LexicographicPathSelection.supportPath? triangle (0 : Fin 3) (1 : Fin 3)

example : SparseDeletionEnvelope.work baseline triangle =
    triangle.vertexCount + 2 ^ (triangle.vertexCount - 1) + 1 := rfl

example : CanonicalBridgeQuotient.work triangle =
    triangle.orderedDarts.length * triangle.vertexCount := rfl

#print axioms sparseResult
#print axioms bridgeResult
#print axioms missingLawResult
#print axioms pathResult
#print axioms ExcessPortExtraction.ports_length_eq_total_surplus

end Hypostructure.Fixtures.OfficialMinimalCounterexampleConsequencesGraph
