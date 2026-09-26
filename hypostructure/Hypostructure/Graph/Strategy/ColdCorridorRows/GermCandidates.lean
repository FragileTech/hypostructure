import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.ColdIncrementArithmetic
import Hypostructure.Graph.ColdGermFamily
import Hypostructure.Graph.Strategy.ColdCorridorRows.Basic
import Hypostructure.Graph.Contracts.Spine.ColdCorridorState

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! ## Node `[153]`, `lem:cold-germ-extraction`: the (F5) candidate family

The candidates are exactly the manuscript's complete repaired occurrence
family: outside-corridor F5 prefixes and immediate two-vertex terminal germs
for selected cross-window incidences.  A noncandidate occurrence is charged
at its first high-to-subcubic edge; there is no separate conditional or
unbounded cross-window loss (`Contracts.Spine.coldGermCandidates_of_routing`). -/
@[reducible] noncomputable def coldGermCandidatesRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldGermCandidates
    { Requires := [K .coldFailureRouting, K .coldExchangeBound,
        K .coldHandoffTransfer]
      Produces := [K .coldGermCandidates]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .coldGermCandidates)
        ⟨Contracts.Spine.coldGermCandidates_of_routing data.toParameters
          inputs.current.object inputs.current.baseline data.threshold_eq_three
          data.three_le_windowOrder (inputs.get (K .coldFailureRouting)).down
          (inputs.get (K .coldHandoffTransfer)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
