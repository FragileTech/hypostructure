import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.Collection

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- **Node `[110]`**: the exit-`(8)` route-`8` residual profile, read from the
node-`[109]` exit-`(7)`-free fact. -/
@[reducible] noncomputable def route8ResidualProfileRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8ResidualProfile
    { Requires := [K .typeAExitSevenFree]
      Produces := [K .route8ResidualProfile]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8ResidualProfile)
        ⟨Graph.Contracts.RouteEight.route8ResidualProfile data.toParameters inputs.current.object
          (inputs.get (K .typeAExitSevenFree)).down⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
