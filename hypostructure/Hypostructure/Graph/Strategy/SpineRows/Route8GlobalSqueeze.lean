import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.Collection

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- **Node `[111]`**: the route-`8` collection `𝒳_A` and its cleared deficit. -/
@[reducible] noncomputable def route8GlobalSqueezeRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8GlobalSqueeze
    { Requires := []
      Produces := [K .route8GlobalSqueeze]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8GlobalSqueeze)
        ⟨Graph.Contracts.RouteEight.route8GlobalSqueeze data.toParameters inputs.current.object⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
