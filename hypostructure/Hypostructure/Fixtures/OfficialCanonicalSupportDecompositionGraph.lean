import Hypostructure.Graph.Strategy.Official.Features.CanonicalSupportDecomposition

namespace Hypostructure.Fixtures.OfficialCanonicalSupportDecompositionGraph

open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Official.Features

def path : FiniteObject where
  Vertex := Fin 3
  graph := SimpleGraph.fromRel fun left right =>
    left.val + 1 = right.val ∨ right.val + 1 = left.val
  vertices := inferInstance
  decideAdj := by
    intro left right
    simp only [SimpleGraph.fromRel_adj]
    infer_instance

def initial : Finset (Fin 3) := {(0 : Fin 3), (1 : Fin 3)}

noncomputable example : OwnedDecomposition path :=
  CanonicalSupportDecomposition.decomposition path initial

example
    (inside : CanonicalSupportDecomposition.PieceInternal path initial)
    (outside : CanonicalSupportDecomposition.OutsideInternal path initial) :
    ¬ path.graph.Adj inside.1 outside.1 :=
  CanonicalSupportDecomposition.not_adj_pieceInternal_outside
    path initial inside outside

end Hypostructure.Fixtures.OfficialCanonicalSupportDecompositionGraph
