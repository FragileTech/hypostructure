import Hypostructure.Graph.Strategy.Official.Universal.Declaration

namespace Hypostructure.Fixtures.OfficialUniversalGraph

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Core.Strategy.Official
open Hypostructure.Core.Strategy.OfficialRegistry
open Hypostructure.Graph.Strategy.Official
open Hypostructure.Graph.Strategy.Official.Universal

abbrev SmallVertex := Fin 2
abbrev LargeVertex := Fin 3

def small : FiniteObject :=
  FiniteObject.of (⊥ : SimpleGraph SmallVertex) inferInstance (by
    change DecidableRel fun _ _ : SmallVertex => False
    infer_instance)

def large : FiniteObject :=
  FiniteObject.of (SimpleGraph.completeGraph LargeVertex) inferInstance (by
    change DecidableRel fun left right : LargeVertex => left ≠ right
    infer_instance)

def reusableProgram : Program :=
  .chain ⟨"universal"⟩
    (.invoke ⟨"return"⟩ ⟨.rootedReturn, 0⟩)
    (.invoke ⟨"packing"⟩ ⟨.inducedPathPacking, 0⟩)

def declaration : Declaration where
  baseline := .minimumDegreeAtLeast 0
  targetSpec := .finiteLengths [3, 4]
  program := reusableProgram

example : (prepare declaration small).view.vertices.length = 2 := by decide
example : (prepare declaration large).view.vertices.length = 3 := by decide

example : (prepare declaration small).view.darts.length = 0 := by decide
example : (prepare declaration large).view.darts.length = 6 := by decide

example : (prepare declaration small).view.edges.length = 0 := by decide
example : (prepare declaration large).view.edges.length = 3 := by decide

example :
    (prepare declaration small).view.degrees =
      (declaration.presentation small).degreeCapacities := rfl

example :
    (prepare declaration large).view.adjacency =
      (declaration.presentation large).adjacencyResponses := rfl

example :
    programAvailability reusableProgram =
      [(⟨.rootedReturn, 0⟩, .executableRootedReturn),
       (⟨.inducedPathPacking, 0⟩,
        .unavailable .semanticInputNotYetDerived)] := by
  native_decide

example :
    (prepare declaration small).view.paths = pathCandidates small := rfl

example :
    (prepare declaration large).view.paths = pathCandidates large := rfl

#print axioms Universal.prepare
#print axioms Universal.executeRootedReturn

end Hypostructure.Fixtures.OfficialUniversalGraph
