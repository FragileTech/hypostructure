import Hypostructure.Core.Strategy.Official.Schema
import Hypostructure.Core.Strategy.Official.Availability
import Hypostructure.Graph.Strategy.Official.Kernel

/-!
# Closed Graph-owned official registry

`Semantics` and `resolve` are closed dependent case splits.  Applications may
select an official identifier in a DAG, but cannot replace any equation.
-/

namespace Hypostructure.Graph.Strategy.Official

open Hypostructure.Core.Strategy
open Hypostructure.Graph

universe u

/-- Closed result vocabulary of the Graph dispatcher.  Constructors describe
framework-derived semantic data; none is an execution callback or closure. -/
inductive Result (data : Presentation.{u}) where
  | graphSchedule (vertices : List data.object.Vertex)
  | adjacencyResponses
      (rows : List ((data.object.Vertex × data.object.Vertex) × Bool))
  | vertexNumbers (rows : List (data.object.Vertex × Nat))
  | adjacencySupport
      (rows : List (data.object.Vertex × data.object.Vertex))

/-- Closed graph dispatcher. `none` is rejection: unsupported Core/PDE IDs are
never reinterpreted as dummy Graph strategies.  The slot number is deliberately
absent because it cannot select or perturb Graph execution. -/
noncomputable def resolve (data : Presentation.{u})
    (id : OfficialRegistry.Id) : Option (Result data) := by
  cases id with
  | orderedExhaustion => exact some (.graphSchedule data.vertexSchedule)
  | responseClassification =>
      exact some (.adjacencyResponses data.adjacencyResponses)
  | capacityAccounting =>
      exact some (.vertexNumbers data.degreeCapacities)
  | supportLocalization =>
      exact some (.adjacencySupport data.adjacencySupport)
  | rankBudget =>
      exact some (.vertexNumbers data.degreeRanks)
  | closedCodeExhaustion
  | exhaustiveDichotomy
  | targetDecision
  | rootedReturn
  | targetDefectivePeel
  | decoratedFan
  | representedSupportLocalization
  | representedFluxAccounting
  | representedDefectExhaustion => exact none
  | _ => exact none

theorem rejects_pde (data : Presentation.{u}) :
    resolve data .representedSupportLocalization = none ∧
    resolve data .representedFluxAccounting = none ∧
    resolve data .representedDefectExhaustion = none := by
  simp [resolve]

theorem rejects_unsupported_core (data : Presentation.{u}) :
    resolve data .closedCodeExhaustion = none ∧
    resolve data .exhaustiveDichotomy = none ∧
    resolve data .targetDecision = none := by
  simp [resolve]

theorem graph_id_owner (id : OfficialRegistry.Id)
    (h : id = .rootedReturn ∨ id = .targetDefectivePeel ∨ id = .decoratedFan) :
    (OfficialRegistry.describe id).owner = .graph := by
  rcases h with rfl | rfl | rfl <;> rfl

end Hypostructure.Graph.Strategy.Official
