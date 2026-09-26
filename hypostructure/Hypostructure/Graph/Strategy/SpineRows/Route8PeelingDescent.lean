import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.Descent

/-!
# Node `[123]`: the exact large-budget descent

`thm:large-budget-route8-only`'s deterministic exit-`(4)` peeling procedure on
the unified census, from the unified deficit and the receiver routing of
node `[88]`.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- **Node `[123]`**: the terminal stage of the descent, with its recorded peel
chain and exact stage accounting. -/
@[reducible] noncomputable def route8PeelingDescentRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8PeelingDescent
    { Requires := [K .route8UnifiedDeficit, K .typeAReceiverRouting]
      Produces := [K .route8PeelingDescent]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8PeelingDescent)
        ⟨Graph.Contracts.RouteEight.route8PeelingDescent data.toParameters
          inputs.current.object inputs.current.baseline
          (le_trans (by norm_num) data.three_le_threshold)
          data.dischargeScale_pos
          (inputs.get (K .typeAReceiverRouting)).down
          (inputs.get (K .route8UnifiedDeficit)).down⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
