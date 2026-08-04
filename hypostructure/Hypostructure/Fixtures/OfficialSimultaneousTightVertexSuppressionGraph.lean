import Hypostructure.Graph.SimultaneousTightVertexSuppression

namespace Hypostructure.Fixtures.OfficialSimultaneousTightVertexSuppressionGraph

open Hypostructure.Graph
open Hypostructure.Graph.TightVertexSuppression

universe u v

variable {object : FiniteObject.{u}}

example (family : CompatibleFamily object)
    (x y : {x // x ∈ family.remainingVertices}) :
    family.suppressedGraph.Adj x y ↔
      object.graph.Adj x.1 y.1 ∨
      ∃ i,
        (x.1 = (family.configuration i).left ∧
          y.1 = (family.configuration i).right) ∨
        (x.1 = (family.configuration i).right ∧
          y.1 = (family.configuration i).left) :=
  family.suppressed_adj x y

example (family : CompatibleFamily object) :
    family.suppressed.vertexCount + Fintype.card family.Index =
      object.vertexCount :=
  family.vertexCount_suppressed

example (family : CompatibleFamily object) [Nonempty family.Index] :
    family.suppressed.LexicographicallySmaller object :=
  family.lexicographicallySmaller

example
    {BranchState : FiniteObject.{u} → Type v}
    {LengthOK : Nat → Prop}
    {threshold : Nat}
    (context : Core.MinimalCounterexampleContext
      (problem (fun current => threshold ≤ current.minDegree) BranchState)
      (HasCycleWithLength LengthOK)
      (lexicographicProgress
        (fun current => threshold ≤ current.minDegree) BranchState))
    (family : CompatibleFamily context.G)
    [Nonempty family.Index]
    (preserved : threshold ≤ family.suppressed.minDegree) :
    HasCycleWithLength LengthOK family.suppressed :=
  family.target_on_suppressed_of_minimality context preserved

example (family : CompatibleFamily object)
    (vertex : family.suppressed.Vertex) :
    family.suppressed.degree vertex =
      (family.resultingNeighbors
        (family.toRemaining vertex).1).card :=
  family.degree_suppressed_eq_resultingNeighbors vertex

example (family : CompatibleFamily object)
    (vertex : family.suppressed.Vertex) :
    family.suppressed.degree vertex + family.centerLoad vertex.1 =
      object.degree vertex.1 :=
  family.degree_add_centerLoad vertex

example (family : CompatibleFamily object)
    (vertex : object.Vertex) :
    (family.resultingNeighbors vertex).card +
        family.centerLoad vertex =
      object.degree vertex :=
  family.resultingNeighbors_card_add_centerLoad vertex

example (family : CompatibleFamily object)
    (threshold : Nat)
    (baseline : threshold ≤ object.minDegree)
    (capacity : family.CenterCapacity threshold)
    [Nonempty family.suppressed.Vertex] :
    threshold ≤ family.suppressed.minDegree :=
  family.minimumDegree_preserved threshold baseline capacity

example (family : CompatibleFamily object)
    {LengthOK : Nat → Prop}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (certificate : CycleCertificate family.suppressed LengthOK) :
    (family.usedChords certificate.walk).Nonempty :=
  family.usedChords_nonempty_of_avoids avoids certificate

example (family : CompatibleFamily object)
    {LengthOK : Nat → Prop}
    (certificate : CycleCertificate family.suppressed LengthOK) :
    (family.expandCycle certificate).walk.IsCycle ∧
      (family.expandCycle certificate).walk.length =
        certificate.walk.length +
          (family.usedChords certificate.walk).card :=
  ⟨(family.expandCycle certificate).isCycle,
    (family.expandCycle certificate).length_eq⟩

example (family : CompatibleFamily object)
    {LengthOK : Nat → Prop}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (certificate : CycleCertificate family.suppressed LengthOK) :
    (family.usedChords certificate.walk).Nonempty ∧
      ∃ expanded : family.ExpandedCycle certificate,
        expanded.walk.length =
          certificate.walk.length +
            (family.usedChords certificate.walk).card :=
  family.suppressedFamilyExpansion avoids certificate

#print axioms CompatibleFamily.suppressed_adj
#print axioms CompatibleFamily.vertexCount_suppressed
#print axioms CompatibleFamily.lexicographicallySmaller
#print axioms CompatibleFamily.target_on_suppressed_of_minimality
#print axioms CompatibleFamily.degree_suppressed_eq_resultingNeighbors
#print axioms CompatibleFamily.resultingNeighbors_card_add_centerLoad
#print axioms CompatibleFamily.degree_add_centerLoad
#print axioms CompatibleFamily.minimumDegree_preserved
#print axioms CompatibleFamily.usedChords_nonempty_of_avoids
#print axioms CompatibleFamily.expandWalk_isCycle
#print axioms CompatibleFamily.expandCycle
#print axioms CompatibleFamily.suppressedFamilyExpansion

end Hypostructure.Fixtures.OfficialSimultaneousTightVertexSuppressionGraph
