import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.Absorption

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- The (O2) step of `lem:typeA-routed-overload-not-open` and the demand-unit
count on the committed maximal absorption. -/
@[reducible] noncomputable def route8OpenBoundarySaturatedRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8OpenBoundarySaturated
    { Requires := [K .route8DemandAbsorption]
      Produces := [K .route8OpenBoundarySaturated, K .route8DemandUnitCount]
      requiresUnique := by simp
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8OpenBoundarySaturated)
        ⟨Graph.Contracts.RouteEight.route8OpenBoundarySaturated data.toParameters inputs.current.object
          (inputs.get (K .route8DemandAbsorption)).down⟩
        (.cons (key := K .route8DemandUnitCount)
        ⟨Graph.Contracts.RouteEight.route8DemandUnitCount data.toParameters inputs.current.object⟩
        .nil))
    0 0

end Hypostructure.Graph.Strategy.Spine
