import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.Collection

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- **Node `[114]`**: every indexed entry of `𝒳_A` passes to its canonical
essential carrier core. -/
@[reducible] noncomputable def route8CarrierCoreRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8CarrierCore
    { Requires := []
      Produces := [K .route8CarrierCore]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8CarrierCore)
        ⟨Graph.Contracts.RouteEight.route8CarrierCore data.toParameters inputs.current.object⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
