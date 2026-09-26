import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.TwoCarrier

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- **Node `[118]`, (T5)**: the declared deletion witnesses of the selected
two-support entry. -/
@[reducible] noncomputable def route8CarrierDeletionWitnessesRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8CarrierDeletionWitnesses
    { Requires := [K .route8TwoCarrierEntry]
      Produces := [K .route8CarrierDeletionWitnesses]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8CarrierDeletionWitnesses)
        ⟨Graph.Contracts.RouteEight.route8CarrierDeletionWitnesses data.toParameters inputs.current.object
          (inputs.get (K .route8TwoCarrierEntry)).down⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
