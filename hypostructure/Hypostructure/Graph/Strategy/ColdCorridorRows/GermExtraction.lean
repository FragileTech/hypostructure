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

/-! ## Node `[153]`, the `M_cold` exchange bound

On the routed first-failure residual (`K .coldFailureRouting`), a terminal cold
corridor reads at most `M_cold` cut states beyond the interface budget
(`exchange_card_le`, `Contracts.Spine.coldExchangeBound_holds`).  The greedy
extraction of `lem:cold-germ-extraction` is applied directly by node `[153]`'s
candidate owner (`Contracts.Spine.coldGermCandidates_of_routing`). -/
@[reducible] noncomputable def coldGermExtractionRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldGermExtraction
    { Requires := [K .coldFailureRouting]
      Produces := [K .coldExchangeBound]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .coldExchangeBound)
        ⟨Contracts.Spine.coldExchangeBound_holds data.toParameters
          inputs.current.object⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
