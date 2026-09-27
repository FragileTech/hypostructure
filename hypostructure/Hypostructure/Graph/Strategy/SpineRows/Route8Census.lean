import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.Collection

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- The object-level census of `𝒳_A`: the deficit and private-carrier rate
readings. -/
@[reducible] noncomputable def route8CensusRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8Census
    { Requires := [K .route8BasinBurden, K .route8LargeBudgetDeficit, K .route8Rate,
        K .cubicBaseline]
      Produces := [K .route8Census]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8Census)
        ⟨Graph.Contracts.RouteEight.route8Census data.toParameters inputs.current.object
          inputs.current.baseline
          (by have := (inputs.get (K .cubicBaseline)).down.1.2.1; omega)
          (inputs.get (K .route8BasinBurden)).down
          (inputs.get (K .route8LargeBudgetDeficit)).down
          (inputs.get (K .route8Rate)).down⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
