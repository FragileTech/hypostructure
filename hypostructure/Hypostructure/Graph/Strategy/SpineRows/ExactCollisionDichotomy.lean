import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.NetCharge
import Hypostructure.Graph.Contracts.Spine.SpineRemainder
import Hypostructure.Graph.Contracts.RouteEight.CollisionRate

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- **Node `[173]`'s no-arm is closed by the private-carrier rate.**  Every
path into `[57]`/`[173]` carries `K .route8Rate` (decided before the net-charge
continuation: `[160]`'s double-yes arm, `[147]`'s `θ < 1/78`, or the exact test
at the route-`8` entry of the `[24]` arm), the rate `[120]`--`[122]` consume.
At the same remainder `R₀` the failed collision `N₀(R₀) ≥ 0` reads `τ ≥ 1/4`
and the rate reads `τ < 3/13`, through node `[29]`'s boundary demand
`def⁺(R₀) ≤ e(R₀,W)`, which is the residual's own baseline reading
(`boundaryDemandRow` publishes exactly this term)
(`Contracts.RouteEight.exactCollisionFails_route8Rate_false`). -/
noncomputable instance instIncompatibleExactCollisionFailsRoute8Rate :
    Incompatible (Input BranchState Presentation presentation data)
      (K .exactCollisionFails) (K .route8Rate) where
  contradiction := fun residual fails rate =>
    Contracts.RouteEight.exactCollisionFails_route8Rate_false data.toParameters
      residual.object
      (Contracts.Spine.boundaryDemand_of_baseline data.toParameters
        residual.object residual.baseline)
      rate.down fails.down

variable [FactSystem (Input BranchState Presentation presentation data)]

/-! ## Node `[57]` = `[173]`: the exact collision test

`lem:exact-collision-test`.  Node `[56]`'s collision is an inequality of the
current object — with the actual surpluses, the actual hot and cold window
counts, and the exact skeleton budget — and node `[173]` decides it on the
object: `def⁺(R₀) − σ(R₀) < |R₀|/s` at the remainder `R₀` of the fixed maximum
packing `P₀` (`NegativeNetCharge`),
which is exactly `K .netChargeCap`.  Its yes arm continues at `[58]`; its no arm
is the absorbed-germ residual `[174]` (`K .exactCollisionFails`), closed
against the private-carrier rate (`instIncompatibleExactCollisionFailsRoute8Rate`).  No condition
on `n` is used (`rem:no-sufficient-order`): the sufficient-order reading of
node `[57]` and the cap row that consumed it are gone. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def exactCollisionDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@Core.Residual.FactKeys.Has
      (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .netDeficiencyCap) known]
    (capFresh : K .netChargeCap ∉ known)
    (failsFresh : K .exactCollisionFails ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .netChargeCap) (K .exactCollisionFails) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .netChargeCap) (K .exactCollisionFails)
    `Hypostructure.Graph.Strategy.Spine.exactCollisionDichotomy
    (by
      classical
      -- `[56]` → `[57]`/`[173]`: the net-deficiency cap is the predecessor.
      let _cap := (@ExactLedger.get
        (Input BranchState Presentation presentation data) _
        (factSystem BranchState Presentation presentation data)
        current known previous (K .netDeficiencyCap)).down
      exact if holds : NetChargeCapStatement data.toParameters current.object then
        .inl ⟨holds⟩
      else
        .inr ⟨Contracts.Spine.exactCollisionFails_of_not_netChargeCap
          data.toParameters current.object holds⟩)
    capFresh failsFresh

end Hypostructure.Graph.Strategy.Spine
