import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Exits

/-! # Node `[103]`: exit `(5)`, a target-complete response compression

Asked at the saturated exit-`(4)`-free states.  The yes arm
(`K .typeAExitFive`) closes at node `[104]` against `cor:uncompressible`; the
no arm (`K .typeAExitFiveFree`) is its exact negation and enters node `[105]`. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

noncomputable def typeAExitFiveDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data) current
        known)
    (yesFresh : K .typeAExitFive ∉ known)
    (noFresh : K .typeAExitFiveFree ∉ known) :
    Decision (K .typeAExitFive) (K .typeAExitFiveFree) previous :=
  Decision.run previous (K .typeAExitFive) (K .typeAExitFiveFree)
    `Hypostructure.Graph.Strategy.Spine.typeAExitFiveDichotomy
    (by
      classical
      by_cases yes : TypeAExitFiveStatement data.toParameters current.object
      · exact .inl ⟨yes⟩
      · exact .inr ⟨Graph.Contracts.TypeA.typeAExitFiveFree_of_not_exitFive data.toParameters current.object
          yes⟩)
    yesFresh noFresh

end Hypostructure.Graph.Strategy.Spine
