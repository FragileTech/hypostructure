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

/-! Node `[153]`: `lem:cold-corridor-first-failure` on the literal
surviving-cold residual -- (F1) and (F3) are excluded by their ledger facts and
(F2) is excluded by the node-`[125]` survivor, and every other first failure
is routed to (F5) or (F4)
(`Contracts.Spine.coldFailureRouting_of_failures`). -/

@[reducible] noncomputable def coldFirstFailureRoutingRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldFirstFailureRouting
    { Requires := [K .coldFirstFailureOccurrence, K .coldFailureCycle,
        K .coldFailureCompression, K .sparseSurplusSurvivor]
      Produces := [K .coldFailureRouting]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .coldFailureRouting)
        ⟨Contracts.Spine.coldFailureRouting_of_failures data.toParameters
          inputs.current.object
          (inputs.get (K .coldFirstFailureOccurrence)).down
          (inputs.get (K .coldFailureCycle)).down
          (inputs.get (K .coldFailureCompression)).down
          (inputs.get (K .sparseSurplusSurvivor)).down⟩
        .nil)


end Hypostructure.Graph.Strategy.Spine
