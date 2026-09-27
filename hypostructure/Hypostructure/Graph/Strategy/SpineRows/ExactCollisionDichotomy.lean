import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.NetCharge

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

variable [FactSystem (Input BranchState Presentation presentation data)]

/-! ## Node `[57]` = `[173]`: the exact collision test

`lem:exact-collision-test`.  Node `[56]`'s collision is an inequality of the
current object — with the actual surpluses, the actual hot and cold window
counts, and the exact skeleton budget — and node `[173]` decides it on the
object: `def⁺(R₀) − σ(R₀) < |R₀|/s` at the remainder `R₀` of the fixed maximum
packing `P₀` (`NegativeNetCharge`),
which is exactly `K .netChargeCap`.  Its yes arm continues at `[58]`; its no arm
is the absorbed-germ residual `[174]` (`K .exactCollisionFails`).  No condition
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
