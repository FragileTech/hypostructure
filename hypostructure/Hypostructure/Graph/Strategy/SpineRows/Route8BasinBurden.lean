import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.Collection

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- **Node `[112]`, `lem:typeA-route8-burden`**: `s·D_A(𝒳_A) ≤ N_basin(𝒳_A)`,
on the collection `𝒳_A` extracted at node `[111]`, with the receiver routing of
its supports from node `[13]` (`lem:typeA-receiver-loads`). -/
@[reducible] noncomputable def route8BasinBurdenRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8BasinBurden
    { Requires := [K .route8GlobalSqueeze, K .remainderNormalized, K .cubicBaseline]
      Produces := [K .route8BasinBurden]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8BasinBurden)
        ⟨Graph.Contracts.RouteEight.route8BasinBurden data.toParameters inputs.current.object
          inputs.current.baseline
          (by have := (inputs.get (K .cubicBaseline)).down.1.2.1; omega)
          (inputs.get (K .route8GlobalSqueeze)).down
          (inputs.get (K .remainderNormalized)).down⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
