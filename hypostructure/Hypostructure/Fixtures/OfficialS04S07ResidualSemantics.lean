import Hypostructure.Core.Strategy.Official.Semantics.SparseSurplusRefinement
import Hypostructure.Core.Strategy.Official.Semantics.FiniteEntropyPipeline

namespace Hypostructure.Fixtures.OfficialS04S07ResidualSemantics

namespace S04

open Core.Strategy.Official.Semantics.SparseSurplusRefinement

def input : Input where
  rows :=
    [ { baseline := 4, observed := 2, attempts := 3, successes := 0,
        requiredSuccesses := 1 }
    , { baseline := 3, observed := 7, attempts := 5, successes := 2,
        requiredSuccesses := 2 }
    , { baseline := 1, observed := 1, attempts := 1, successes := 1,
        requiredSuccesses := 1 } ]
  successes_le_attempts := by decide
  required_le_attempts := by decide

example : (execute input).sparseTotal = -2 := by native_decide
example : (execute input).denseTotal = 4 := by native_decide
example : (execute input).hot.length = 2 := by native_decide
example : (execute input).cold.length = 1 := by native_decide
example : (execute input).checks = 6 := by native_decide

end S04

namespace S07

open Core.Strategy.Official.Semantics.FiniteEntropyPipeline

def input : Input where
  windows :=
    [ { support := {0, 1}, stateCodes := [4, 5], curvatureCosts := [3, 2] }
    , { support := {2}, stateCodes := [8, 9, 10], curvatureCosts := [7] } ]
  realizedCodes := [20, 21, 22, 23, 24, 25]
  ambientCodes := [20, 21, 22, 23, 24, 25]

example : packed input := by native_decide
example : stateDemand input = 6 := by native_decide
example : curvatureCost input = 12 := by native_decide
example : ambientCapacity input = 6 := by native_decide
example : Realizes input := by native_decide
example : stateDemand input ≤ ambientCapacity input :=
  demand_le_capacity input (by native_decide)

def overlapping : Input where
  windows :=
    [ { support := {0, 1}, stateCodes := [0], curvatureCosts := [] }
    , { support := {1, 2}, stateCodes := [1], curvatureCosts := [] } ]
  realizedCodes := []
  ambientCodes := []

example : ¬ packed overlapping := by native_decide

def overflow : Input where
  windows :=
    [ { support := {0}, stateCodes := [0, 1], curvatureCosts := [4] }
    , { support := {1}, stateCodes := [2, 3], curvatureCosts := [6] } ]
  realizedCodes := [10, 11]
  ambientCodes := [10, 11]

example : ambientCapacity overflow < stateDemand overflow := by native_decide
example : ¬ Realizes overflow := by native_decide

#print axioms S04.input
#print axioms execute
#print axioms demand_le_capacity
#print axioms entropyCapContradiction

end S07

end Hypostructure.Fixtures.OfficialS04S07ResidualSemantics
