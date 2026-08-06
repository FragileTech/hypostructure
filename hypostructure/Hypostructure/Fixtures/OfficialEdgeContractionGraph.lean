import Hypostructure.Graph.Contraction

namespace Hypostructure.Fixtures.OfficialEdgeContractionGraph

open Hypostructure.Graph

universe u v

variable {object : FiniteObject.{u}}

example (contraction : EdgeContraction object)
    (left right : contraction.contracted.Vertex) :
    contraction.contracted.graph.Adj left right ↔
      left ≠ right ∧
        (object.graph.Adj left.1 right.1 ∨
          (left.1 = contraction.tail ∧
            object.graph.Adj contraction.head right.1) ∨
          (right.1 = contraction.tail ∧
            object.graph.Adj contraction.head left.1)) :=
  contraction.contracted_adj left right

example (contraction : EdgeContraction object) :
    contraction.contracted.vertexCount < object.vertexCount :=
  contraction.vertexCount_contracted_lt

example (contraction : EdgeContraction object)
    (noReturn : ¬ contraction.HasReturn) :
    contraction.contracted.degree contraction.tailVertex + 2 =
      object.degree contraction.tail + object.degree contraction.head :=
  contraction.degree_contracted_tail noReturn

example (contraction : EdgeContraction object)
    (noReturn : ¬ contraction.HasReturn) (threshold : Nat)
    (degreeSum : threshold + 2 ≤
      object.degree contraction.tail + object.degree contraction.head)
    (baseline : threshold ≤ object.minDegree) :
    threshold ≤ contraction.contracted.minDegree :=
  contraction.minDegree_contracted noReturn threshold degreeSum baseline

example
    {BranchState : FiniteObject.{u} → Type v}
    {LengthOK : Nat → Prop}
    {threshold : Nat}
    (context : Core.MinimalCounterexampleContext
      (problem (fun current => threshold ≤ current.minDegree) BranchState)
      (HasCycleWithLength LengthOK)
      (lexicographicProgress
        (fun current => threshold ≤ current.minDegree) BranchState))
    (contraction : EdgeContraction context.G)
    (degreeSum : threshold + 2 ≤
      context.G.degree contraction.tail + context.G.degree contraction.head) :
    Nonempty (contraction.severed.Path contraction.tail contraction.head) :=
  EdgeContraction.hasReturn_of_minimality context contraction degreeSum

#print axioms FiniteObject.contractEdge_adj
#print axioms EdgeContraction.contracted_adj_tail
#print axioms EdgeContraction.vertexCount_contracted_lt
#print axioms EdgeContraction.degree_contracted_of_ne_tail
#print axioms EdgeContraction.degree_contracted_tail
#print axioms EdgeContraction.minDegree_contracted
#print axioms EdgeContraction.false_of_mixed_incidences
#print axioms EdgeContraction.hasReturn_of_minimal
#print axioms EdgeContraction.hasReturn_of_minimality

end Hypostructure.Fixtures.OfficialEdgeContractionGraph
