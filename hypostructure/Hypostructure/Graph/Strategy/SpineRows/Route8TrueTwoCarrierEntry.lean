import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.TwoCarrier

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- **Node `[118]`**: the selected two-support entry is a true route-`8`
entry. -/
@[reducible] noncomputable def route8TrueTwoCarrierEntryRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8TrueTwoCarrierEntry
    { Requires := [K .route8TwoCarrierEntry, K .route8TrueResidual, K .cubicBaseline]
      Produces := [K .route8TrueTwoCarrierEntry]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8TrueTwoCarrierEntry)
        ⟨Graph.Contracts.RouteEight.route8TrueTwoCarrierEntry data.toParameters inputs.current.object
          (inputs.get (K .route8TwoCarrierEntry)).down
          (inputs.get (K .route8TrueResidual)).down
          inputs.current.baseline
          (by have := (inputs.get (K .cubicBaseline)).down.1.2.1; omega)⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
