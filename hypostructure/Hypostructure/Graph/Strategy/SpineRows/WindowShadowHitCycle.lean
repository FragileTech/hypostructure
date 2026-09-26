import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.WindowShadow

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- The recorded-hit certificate (O1), with its actual simple cycle. -/
@[reducible] noncomputable def windowShadowHitCycleRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.windowShadowHitCycle
    { Requires := []
      Produces := [K .windowShadowHitCycle]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .windowShadowHitCycle)
        ⟨Graph.Contracts.RouteEight.windowShadowHitCycle data.toParameters inputs.current.object⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
