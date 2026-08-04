import Hypostructure.Graph.Strategy.Official.Features.CanonicalConnectedSupportHull

namespace Hypostructure.Fixtures.OfficialCanonicalConnectedSupportHullGraph

open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Official.Features.CanonicalConnectedSupportHull

def path : FiniteObject where
  Vertex := Fin 3
  graph := SimpleGraph.fromRel fun left right =>
    left.val + 1 = right.val ∨ right.val + 1 = left.val
  vertices := inferInstance
  decideAdj := by
    intro left right
    simp only [SimpleGraph.fromRel_adj]
    infer_instance

example :
    Presentation.outsideDegree path
      ({(0 : Fin 3), (1 : Fin 3)} : Finset (Fin 3)) (1 : Fin 3) = 1 := by
  native_decide

example :
    Presentation.insideDegree path
      ({(0 : Fin 3), (1 : Fin 3)} : Finset (Fin 3)) (1 : Fin 3) = 1 := by
  native_decide

end Hypostructure.Fixtures.OfficialCanonicalConnectedSupportHullGraph
