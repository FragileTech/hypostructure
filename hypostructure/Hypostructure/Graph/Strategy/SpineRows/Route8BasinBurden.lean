import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.Collection

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- **Node `[112]`, `lem:typeA-route8-burden`**: `s·D_A(𝒳_A) ≤ N_basin(𝒳_A)`,
from the receiver routing of node `[88]`. -/
@[reducible] noncomputable def route8BasinBurdenRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8BasinBurden
    { Requires := [K .typeAReceiverRouting]
      Produces := [K .route8BasinBurden]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8BasinBurden)
        ⟨Graph.Contracts.RouteEight.route8BasinBurden data.toParameters inputs.current.object
          inputs.current.baseline
          data.dischargeScale_pos
          (inputs.get (K .typeAReceiverRouting)).down⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
