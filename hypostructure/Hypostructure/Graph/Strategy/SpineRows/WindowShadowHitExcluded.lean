import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.WindowShadow

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- The selected object has no recorded shadow hit
(`lem:typeA-window-shadow-hit-routes`). -/
@[reducible] noncomputable def windowShadowHitExcludedRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.windowShadowHitExcluded
    { Requires := [K .selection, K .windowShadowHitCycle]
      Produces := [K .windowShadowHitExcluded]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .windowShadowHitExcluded)
        ⟨Graph.Contracts.RouteEight.windowShadowHitExcluded data.toParameters inputs.current.object
          (inputs.get (K .selection)).down.1
          (inputs.get (K .windowShadowHitCycle)).down⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
