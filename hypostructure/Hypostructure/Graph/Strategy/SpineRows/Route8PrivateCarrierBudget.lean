import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.Terminal

/-!
# Nodes `[119]`--`[122]`: the private-support budget and its contradiction

Node `[117]`'s no-arm gives every entry of `Ξ(𝒳_A)` at least `δ` private
essential incidences; nodes `[119]`--`[120]` publish the resulting budget
`δ·|Ξ(𝒳_A)| ≤ |∂R|`.  Nodes `[121]`--`[122]` are the framework's closure: the
budget is `Incompatible` with the census deficit and rate readings.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- **Nodes `[119]`--`[120]`**: the private-support budget on the no-two-support
arm of node `[117]`. -/
@[reducible] noncomputable def route8PrivateCarrierBudgetRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8PrivateCarrierBudget
    { Requires := [K .route8NoTwoCarrierEntry, K .cubicBaseline]
      Produces := [K .route8PrivateCarrierBudget]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .route8PrivateCarrierBudget)
        ⟨Graph.Contracts.RouteEight.route8PrivateCarrierBudget_of_noTwoCarrier
          data.toParameters inputs.current.object
          (by have := (inputs.get (K .cubicBaseline)).down.1; omega)
          (inputs.get (K .route8NoTwoCarrierEntry)).down⟩ .nil)
    0 0

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- **Nodes `[121]`--`[122]`** (`rem:route8-carrier-margin`): the private
budget contradicts the census burden/deficit and rate readings. -/
noncomputable instance instIncompatibleRoute8CensusPrivateCarrierBudget :
    Incompatible (Input BranchState Presentation presentation data)
      (K .route8Census) (K .route8PrivateCarrierBudget) where
  contradiction := fun input census budget =>
    Graph.Contracts.RouteEight.route8Census_privateCarrierBudget_false
      data.toParameters input.object
      (le_trans (by norm_num) data.three_le_threshold) census.down budget.down

end Hypostructure.Graph.Strategy.Spine
