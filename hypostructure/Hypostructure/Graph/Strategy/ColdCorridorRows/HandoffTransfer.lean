import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.ColdIncrementArithmetic
import Hypostructure.Graph.ColdGermFamily
import Hypostructure.Graph.Strategy.ColdCorridorRows.Basic
import Hypostructure.Graph.Contracts.Spine.ColdHandoff

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[153]`: publish the bounded-prefix/first-high handoff conclusion
from the retained corridor state
(`Contracts.Spine.coldHandoffTransfer_of_state`). -/
@[reducible] noncomputable def coldHandoffTransferRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldHandoffTransfer
    { Requires := [K .coldCorridorState]
      Produces := [K .coldHandoffTransfer]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .coldHandoffTransfer)
        ⟨Contracts.Spine.coldHandoffTransfer_of_state data.toParameters
          inputs.current.object (inputs.get (K .coldCorridorState)).down⟩ .nil)

end Hypostructure.Graph.Strategy.Spine
