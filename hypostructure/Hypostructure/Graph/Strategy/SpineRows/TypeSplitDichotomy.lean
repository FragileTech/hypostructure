import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Support

/-! # Node `[62]`: the Type A / Type B split

`[62]` asks whether a negative support carries assigned high-degree surplus.
The yes arm is node `[64]`, Type B (`K .typeBHighSurplus`); the no arm is node
`[63]`, Type A (`K .typeALowSurplus`), the exact negation of the yes arm in
positive form.  The decision is a case analysis on the yes-arm proposition. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

noncomputable def typeSplitDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data) current
        known)
    (typeAFresh : K .typeALowSurplus ∉ known)
    (typeBFresh : K .typeBHighSurplus ∉ known) :
    Decision (K .typeALowSurplus) (K .typeBHighSurplus) previous :=
  Decision.run previous (K .typeALowSurplus) (K .typeBHighSurplus)
    `Hypostructure.Graph.Strategy.Spine.typeSplitDichotomy
    (by
      classical
      by_cases high : TypeBHighSurplusStatement data.toParameters current.object
      · exact .inr ⟨high⟩
      · exact .inl ⟨Graph.Contracts.TypeA.typeALowSurplus_of_not_typeBHighSurplus
          data.toParameters current.object high⟩)
    typeAFresh typeBFresh

end Hypostructure.Graph.Strategy.Spine
