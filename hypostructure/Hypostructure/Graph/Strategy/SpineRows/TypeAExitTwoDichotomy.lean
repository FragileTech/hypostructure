import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Exits

/-! # Node `[97]`: exit `(2)`, a power-of-two common-port theta

The yes arm (`K .typeAExitTwoTheta`) closes at node `[98]` against the
selection (`lem:typeA-common-port-return-cycle`); the no arm
(`K .typeAExitTwoFree`) is its exact negation and enters node `[99]`. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

noncomputable def typeAExitTwoDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data) current
        known)
    (yesFresh : K .typeAExitTwoTheta ∉ known)
    (noFresh : K .typeAExitTwoFree ∉ known) :
    Decision (K .typeAExitTwoTheta) (K .typeAExitTwoFree) previous :=
  Decision.run previous (K .typeAExitTwoTheta) (K .typeAExitTwoFree)
    `Hypostructure.Graph.Strategy.Spine.typeAExitTwoDichotomy
    (by
      classical
      by_cases yes : TypeAExitTwoThetaStatement data.toParameters current.object
      · exact .inl ⟨yes⟩
      · exact .inr ⟨Graph.Contracts.TypeA.typeAExitTwoFree_of_not_theta data.toParameters current.object
          yes⟩)
    yesFresh noFresh

end Hypostructure.Graph.Strategy.Spine
