import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.Collection

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- **`def:typeA-unified-negative`** (node `[123]`) on the active remainder. -/
@[reducible] noncomputable def route8UnifiedNegativeRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8UnifiedNegative
    { Requires := []
      Produces := [K .route8UnifiedNegative]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8UnifiedNegative)
        ⟨Graph.Contracts.RouteEight.route8UnifiedNegative data.toParameters inputs.current.object⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
