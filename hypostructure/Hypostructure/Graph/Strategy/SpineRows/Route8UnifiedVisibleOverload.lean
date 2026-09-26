import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.VisibleOverload

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- **Node `[185]`, `lem:typeA-unified-visible-overload`**: every entry owns
its canonical actual visible-four package. -/
@[reducible] noncomputable def route8UnifiedVisibleOverloadRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8UnifiedVisibleOverload
    { Requires := [K .route8UnifiedVisibleResidual]
      Produces := [K .route8UnifiedVisibleOverload]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8UnifiedVisibleOverload)
        ⟨Graph.Contracts.RouteEight.route8UnifiedVisibleOverload data.toParameters inputs.current.object
          (inputs.get (K .route8UnifiedVisibleResidual)).down
          inputs.current.baseline⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
