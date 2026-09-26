import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.Collection

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- **Node `[114]`, `def:typeA-true-route8-residual`** on `𝒳_A`. -/
@[reducible] noncomputable def route8TrueResidualRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8TrueResidual
    { Requires := [K .route8ResidualProfile]
      Produces := [K .route8TrueResidual]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8TrueResidual)
        ⟨Graph.Contracts.RouteEight.route8TrueResidual data.toParameters
          inputs.current.object⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
