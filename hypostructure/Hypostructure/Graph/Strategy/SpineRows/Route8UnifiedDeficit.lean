import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.UnifiedDeficit

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- **`lem:typeA-unified-deficit`** (node `[123]`): the unified collection
carries the whole large-budget deficit. -/
@[reducible] noncomputable def route8UnifiedDeficitRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8UnifiedDeficit
    { Requires := [K .typeBSublinearLedger, K .surplusAtOrBelow, K .cubicBaseline]
      Produces := [K .route8UnifiedDeficit]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8UnifiedDeficit)
        ⟨Graph.Contracts.RouteEight.route8UnifiedDeficit data.toParameters inputs.current.object
          inputs.current.baseline
          (inputs.get (K .cubicBaseline)).down.2.1.2.2.2.2
          (inputs.get (K .typeBSublinearLedger)).down
          (inputs.get (K .surplusAtOrBelow)).down⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
