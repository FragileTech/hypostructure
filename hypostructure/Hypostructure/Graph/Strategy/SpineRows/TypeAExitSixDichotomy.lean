import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Exits

/-! # Node `[105]`: exit `(6)`, support dependence

Asked at the saturated states where exits `(4)` and `(5)` fail.  The yes arm
(`K .typeAExitSix`) closes at node `[106]`; the no arm (`K .typeAExitSixFree`)
is its exact negation and enters node `[107]`. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

noncomputable def typeAExitSixDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data) current
        known)
    (yesFresh : K .typeAExitSix ∉ known)
    (noFresh : K .typeAExitSixFree ∉ known) :
    Decision (K .typeAExitSix) (K .typeAExitSixFree) previous :=
  Decision.run previous (K .typeAExitSix) (K .typeAExitSixFree)
    `Hypostructure.Graph.Strategy.Spine.typeAExitSixDichotomy
    (by
      classical
      by_cases yes : TypeAExitSixStatement data.toParameters current.object
      · exact .inl ⟨yes⟩
      · exact .inr ⟨Graph.Contracts.TypeA.typeAExitSixFree_of_not_exitSix data.toParameters current.object
          yes⟩)
    yesFresh noFresh

end Hypostructure.Graph.Strategy.Spine
