import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Exits

/-! # Node `[95]`: exit `(1)`, a Mersenne anchored return

The yes arm (`K .typeAExitOneReturn`) closes at node `[96]` against the
return-avoidance invariant (`lem:return-equivalence`); the no arm
(`K .typeAExitOneFree`) is its exact negation and enters node `[97]`. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

noncomputable def typeAExitOneDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data) current
        known)
    (yesFresh : K .typeAExitOneReturn ∉ known)
    (noFresh : K .typeAExitOneFree ∉ known) :
    Decision (K .typeAExitOneReturn) (K .typeAExitOneFree) previous :=
  Decision.run previous (K .typeAExitOneReturn) (K .typeAExitOneFree)
    `Hypostructure.Graph.Strategy.Spine.typeAExitOneDichotomy
    (by
      classical
      by_cases yes : TypeAExitOneReturnStatement data.toParameters current.object
      · exact .inl ⟨yes⟩
      · exact .inr ⟨Graph.Contracts.TypeA.typeAExitOneFree_of_not_return data.toParameters current.object
          yes⟩)
    yesFresh noFresh

end Hypostructure.Graph.Strategy.Spine
