import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.Absorption

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- **Node `[351]`**: `def:typeA-pressure-absorbers` with
`lem:typeA-pressure-absorber-no-overcount` at the committed ledger `P₀` of
node `[349]`: the canonical maximal absorption `A₀`. -/
@[reducible] noncomputable def route8DemandAbsorptionRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8DemandAbsorption
    { Requires := [K .route8DemandLedger]
      Produces := [K .route8DemandAbsorption]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8DemandAbsorption)
        ⟨Graph.Contracts.RouteEight.route8DemandAbsorption data.toParameters
          inputs.current.object
          (route8DemandLedger_of_pinned data.toParameters inputs.current.object
            (inputs.get (K .route8DemandLedger)).down)⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
