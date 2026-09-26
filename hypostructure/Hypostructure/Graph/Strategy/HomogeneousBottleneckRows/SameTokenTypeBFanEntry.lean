import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeB.Entry

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[144]` → `[65]`: the same-token handoff envelope enters the common Type B
entry. -/
@[reducible] noncomputable def sameTokenTypeBFanEntryRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sameTokenTypeBFanEntry
    { Requires := [K .typeBHandoff]
      Produces := [K .typeBFanEntry]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBFanEntry)
        ⟨Contracts.TypeB.typeBFanEntry_of_sameTokenHandoff (inputs.get (K .typeBHandoff)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
