import Hypostructure.Graph.TightVertexSuppression

namespace Hypostructure.Fixtures.OfficialTightVertexSuppressionGraph

open Hypostructure.Graph
open Hypostructure.Graph.TightVertexSuppression

universe u v

variable {object : FiniteObject.{u}}

example (configuration : Configuration object)
    (left right : configuration.suppressed.Vertex) :
    configuration.suppressed.graph.Adj left right ↔
      object.graph.Adj left.1 right.1 ∨
        (left.1 = configuration.left ∧
          right.1 = configuration.right) ∨
        (left.1 = configuration.right ∧
          right.1 = configuration.left) :=
  configuration.suppressed_adj left right

example (configuration : Configuration object) :
    configuration.suppressed.vertexCount + 1 = object.vertexCount :=
  configuration.vertexCount_suppressed

example (configuration : Configuration object)
    (threshold : Nat)
    (baseline : threshold ≤ object.minDegree)
    (centerSlack : threshold < object.degree configuration.center) :
    threshold ≤ configuration.suppressed.minDegree :=
  configuration.minimumDegree_preserved threshold baseline centerSlack

example
    {BranchState : FiniteObject.{u} → Type v}
    {LengthOK : Nat → Prop}
    {threshold : Nat}
    (context : Core.MinimalCounterexampleContext
      (problem (fun current => threshold ≤ current.minDegree) BranchState)
      (HasCycleWithLength LengthOK)
      (lexicographicProgress
        (fun current => threshold ≤ current.minDegree) BranchState))
    (configuration : Configuration context.G)
    (centerSlack : threshold < context.G.degree configuration.center) :
    ∃ certificate :
        CycleCertificate configuration.suppressed LengthOK,
      Nonempty
        (Configuration.ReconstructedPath configuration certificate) :=
  configuration.singleSuppressionWitness_of_minimality
    context centerSlack

#print axioms FiniteObject.addEdge_adj
#print axioms Configuration.suppressed_adj
#print axioms Configuration.vertexCount_suppressed
#print axioms Configuration.minimumDegree_preserved
#print axioms Configuration.target_on_suppressed_of_minimality
#print axioms Configuration.cycle_uses_shoulder
#print axioms Configuration.reconstructPath
#print axioms Configuration.singleSuppressionWitness_of_minimality

end Hypostructure.Fixtures.OfficialTightVertexSuppressionGraph
