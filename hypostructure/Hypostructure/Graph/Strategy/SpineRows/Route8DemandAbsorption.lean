import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.Absorption

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- `def:typeA-pressure-absorbers` with `lem:typeA-pressure-absorber-no-overcount`
on every committed maximal `2/3`-demand ledger. -/
@[reducible] noncomputable def route8DemandAbsorptionRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8DemandAbsorption
    { Requires := []
      Produces := [K .route8DemandAbsorption]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8DemandAbsorption)
        ⟨Graph.Contracts.RouteEight.route8DemandAbsorption data.toParameters inputs.current.object⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
