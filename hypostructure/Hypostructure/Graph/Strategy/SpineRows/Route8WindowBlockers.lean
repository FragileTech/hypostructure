import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.Absorption

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- `def:typeA-open-window-blocker` with `lem:typeA-open-window-blocker-count`
on the unified census. -/
@[reducible] noncomputable def route8WindowBlockersRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8WindowBlockers
    { Requires := [K .route8UnifiedEntryCensus]
      Produces := [K .route8WindowBlockers]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8WindowBlockers)
        ⟨Graph.Contracts.RouteEight.route8WindowBlockers data.toParameters inputs.current.object
          (inputs.get (K .route8UnifiedEntryCensus)).down⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
