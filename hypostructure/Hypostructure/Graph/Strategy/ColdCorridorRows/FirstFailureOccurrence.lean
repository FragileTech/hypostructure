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

/-- Node `[153]`: select the first event in the manuscript's ordered
(F1)--(F5) list for every retained cold corridor
(`Contracts.Spine.coldFirstFailureOccurrence_of_state`). -/
@[reducible] noncomputable def coldFirstFailureOccurrenceRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldFirstFailureOccurrence
    { Requires := [K .coldCorridorState, K .coldDeclaredHandoffLedger]
      Produces := [K .coldFirstFailureOccurrence]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .coldFirstFailureOccurrence)
        ⟨Contracts.Spine.coldFirstFailureOccurrence_of_state data.toParameters
          inputs.current.object (inputs.get (K .coldCorridorState)).down
          (inputs.get (K .coldDeclaredHandoffLedger)).down⟩
        .nil)


end Hypostructure.Graph.Strategy.Spine
