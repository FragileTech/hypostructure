import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.Collection

/-! # Node `[111]`: the global squeeze extracts `𝒳_A` carrying `D_A(𝒳_A)`

Read after the node-`[110]` residual profile (`K .route8ResidualProfile`):
the route-`8` collection `𝒳_A = route8SurvivorComponents` of `G`'s fixed
packing, each member a Type A support with a strictly positive share of the
cleared deficit `s·D_A(𝒳_A)`.  Thin adapter of
`Contracts.RouteEight.route8GlobalSqueeze`. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- **Node `[111]`**. -/
@[reducible] noncomputable def route8GlobalSqueezeRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8GlobalSqueeze
    { Requires := [K .route8ResidualProfile]
      Produces := [K .route8GlobalSqueeze]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8GlobalSqueeze)
        ⟨Graph.Contracts.RouteEight.route8GlobalSqueeze data.toParameters
          inputs.current.object (inputs.get (K .route8ResidualProfile)).down⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
