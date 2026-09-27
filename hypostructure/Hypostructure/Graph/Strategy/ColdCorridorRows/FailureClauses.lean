import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.ColdIncrementArithmetic
import Hypostructure.Graph.ColdGermFamily
import Hypostructure.Graph.Strategy.ColdCorridorRows.Basic
import Hypostructure.Graph.Contracts.Spine.ColdFirstFailure

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[153]`, (F2), `lem:cold-corridor-first-failure` (ii) at G's retained
occurrence, on the distinct-states arm of `coldCutStatesDichotomy`: an (F2)
first failure of G's retained corridor is a named sparse surplus exit of G --
vacuously, since (★) (`K .coldCutStatesDistinct`) excludes an (F2) first
failure (`Contracts.Spine.coldFailureDefectRoutes_of_distinct`). -/
@[reducible] noncomputable def coldFailureDefectRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldFailureDefect
    { Requires := [K .coldCutStatesDistinct]
      Produces := [K .coldFailureDefectRoute]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .coldFailureDefectRoute)
        ⟨Contracts.Spine.coldFailureDefectRoutes_of_distinct data.toParameters
          inputs.current.object
          (inputs.get (K .coldCutStatesDistinct)).down⟩ .nil)

/-- Node `[153]`, (F1): the selected residual contains no target cycle. -/
@[reducible] noncomputable def coldFailureCycleRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldFailureCycle
    { Requires := [K .selection]
      Produces := [K .coldFailureCycle]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .coldFailureCycle)
        ⟨Contracts.Spine.coldFailureCycle_of_avoids data.toParameters
          inputs.current.object (inputs.get (K .selection)).down.1⟩
        .nil)

/-- Node `[153]`, (F3): uncompressibility excludes a smaller proper
representative on the current residual. -/
@[reducible] noncomputable def coldFailureCompressionRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldFailureCompression
    { Requires := [K .uncompressible]
      Produces := [K .coldFailureCompression]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .coldFailureCompression)
        ⟨Contracts.Spine.coldFailureCompression_of_uncompressible
          data.toParameters inputs.current.object
          (inputs.get (K .uncompressible)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
