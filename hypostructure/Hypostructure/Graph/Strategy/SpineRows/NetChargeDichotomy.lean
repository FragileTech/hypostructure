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

/-- **The terminal `[60]`, the net-cap contradiction.**  On the yes-arm of
`[59]` the fixed maximum packing `P₀` has `N₀(R₀) ≥ 0`; the collision
`K .netChargeCap` of `[57]`/`[173]` gives `N₀(R₀) < 0` at the same `R₀`. -/
noncomputable instance instIncompatibleNetChargeNonNegativeCap :
    Incompatible (Input BranchState Presentation presentation data)
      (K .netChargeNonNegative) (K .netChargeCap) where
  contradiction := fun residual nonNegative cap => by
    have nonnegative := nonNegative.down
    exact ((residual.object.not_negativeNetCharge_iff
      (residual.object.remainderSupport
        (canonicalWindowPacking data.toParameters residual.object))
      data.threshold data.dischargeScale).mpr nonnegative) cap.down

variable [FactSystem (Input BranchState Presentation presentation data)]

/-! ## Node `[59]`: the net-charge sign test

`N₀(R) ≥ 0?`  Here `R` is the complement of the one maximum packing selected
at node `[27]` (`canonicalWindowPacking`), not a quantifier over every maximal
packing.  The decision tests its exact integer charge, and each arm is a
contract lemma (`Contracts.Spine.netChargeNonNegative_of_nonNegative`,
`Contracts.Spine.netChargeNegative_of_not_nonNegative`) carrying that same
packing and its maximality.  The yes arm is the manuscript's
node `[60]`; the no arm is node `[61]`, where a connected negative support is
selected.  The decision itself does not close `[60]`: that terminal additionally
uses the strict net-cap estimate of `prop:negative-net-charge`. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def netChargeDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    (nonNegativeFresh : K .netChargeNonNegative ∉ known)
    (negativeFresh : K .netChargeNegative ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .netChargeNonNegative) (K .netChargeNegative) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .netChargeNonNegative) (K .netChargeNegative)
    `Hypostructure.Graph.Strategy.Spine.netChargeDichotomy
    (by
      classical
      let packing := canonicalWindowPacking data.toParameters current.object
      by_cases nonNegative : current.object.NonNegativeNetCharge
          (current.object.remainderSupport packing) data.threshold
          data.dischargeScale
      · exact .inl ⟨Contracts.Spine.netChargeNonNegative_of_nonNegative
          data.toParameters current.object nonNegative⟩
      · exact .inr ⟨Contracts.Spine.netChargeNegative_of_not_nonNegative
          data.toParameters current.object nonNegative⟩)
    nonNegativeFresh negativeFresh

end Hypostructure.Graph.Strategy.Spine
