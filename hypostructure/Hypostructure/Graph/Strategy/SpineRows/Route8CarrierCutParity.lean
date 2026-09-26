import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.Collection

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- **Node `[114]`, `lem:typeA-carrier-cut-parity`** on the essential cores of
`𝒳_A`. -/
@[reducible] noncomputable def route8CarrierCutParityRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8CarrierCutParity
    { Requires := [K .route8TrueResidual]
      Produces := [K .route8CarrierCutParity]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8CarrierCutParity)
        ⟨Graph.Contracts.RouteEight.route8CarrierCutParity data.toParameters inputs.current.object
          (inputs.get (K .route8TrueResidual)).down⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
