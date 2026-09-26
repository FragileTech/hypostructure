import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeB.OpenPort

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- `def:open-port-suppression`. -/
@[reducible] noncomputable def openPortSuppressionRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.openPortSuppression
    { Requires := []
      Produces := [K .openPortSuppression]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .openPortSuppression)
        ⟨Contracts.TypeB.openPortSuppression (data := data.toParameters)⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
