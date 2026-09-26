import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.WindowShadow

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- The tail of `lem:typeA-singleton-shadow-table`. -/
@[reducible] noncomputable def windowShadowSingletonTailRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.windowShadowSingletonTail
    { Requires := []
      Produces := [K .windowShadowSingletonTail]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .windowShadowSingletonTail)
        ⟨Graph.Contracts.RouteEight.windowShadowSingletonTail data.toParameters inputs.current.object
          data.lengthOK_iff_powerOfTwo⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
