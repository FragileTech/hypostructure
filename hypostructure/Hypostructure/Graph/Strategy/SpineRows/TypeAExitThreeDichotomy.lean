import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Exits

/-! # Node `[99]`: exit `(3)`, a `P₁₃` label collision

The yes arm (`K .typeAExitThreeCollision`) closes at node `[100]` against the
selection (`lem:labels`); the no arm (`K .typeAExitThreeFree`) is its exact
negation and enters node `[101]`. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

noncomputable def typeAExitThreeDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data) current
        known)
    (yesFresh : K .typeAExitThreeCollision ∉ known)
    (noFresh : K .typeAExitThreeFree ∉ known) :
    Decision (K .typeAExitThreeCollision) (K .typeAExitThreeFree) previous :=
  Decision.run previous (K .typeAExitThreeCollision) (K .typeAExitThreeFree)
    `Hypostructure.Graph.Strategy.Spine.typeAExitThreeDichotomy
    (by
      classical
      by_cases yes : TypeAExitThreeCollisionStatement data.toParameters current.object
      · exact .inl ⟨yes⟩
      · exact .inr ⟨Graph.Contracts.TypeA.typeAExitThreeFree_of_not_collision data.toParameters current.object
          yes⟩)
    yesFresh noFresh

end Hypostructure.Graph.Strategy.Spine
