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

/-! ## Node `[153]`, `lem:cold-germ-extraction`: exchange bound and extraction

The first-failure cold exchange is bounded by `M_cold` (`exchange_card_le`),
and an occurrence-indexed candidate family with the paper's overlap bound has
a disjoint subfamily of size at least `|𝒢_cand|/D_cold` (greedy independent
set, `coldGermOccurrenceExtractionLocal`).  Positivity belongs to the later
linear arm, not to this finite extraction theorem
(`Contracts.Spine.coldExchangeBound_of_routing`,
`Contracts.Spine.coldGermExtraction_of_exchangeBound`). -/
@[reducible] noncomputable def coldGermExtractionRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldGermExtraction
    { Requires := [K .coldFailureRouting]
      Produces := [K .coldExchangeBound, K .coldGermExtraction]
      requiresUnique := by simp
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      let exchange := Contracts.Spine.coldExchangeBound_of_routing
        data.toParameters inputs.current.object
        (inputs.get (K .coldFailureRouting)).down
      .cons (key := K .coldExchangeBound)
        ⟨exchange⟩
        (.cons (key := K .coldGermExtraction)
          ⟨Contracts.Spine.coldGermExtraction_of_exchangeBound data.toParameters
            inputs.current.object exchange⟩
          .nil))


end Hypostructure.Graph.Strategy.Spine
