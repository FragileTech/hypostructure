import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Support

/-! # Node `[93]`: does a saturated receiver see `s` visible returns at one port?

The yes arm (`K .typeAVisibleEntry`) enters the saturated exit chain at node
`[95]`; the no arm (`K .typeANoVisibleEntry`) is its exact negation and the
hypothesis of `lem:typeA-silent-excess-count` at node `[94]`.  The decision is
a case analysis on the yes-arm proposition. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

noncomputable def typeAVisibleEntryDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data) current
        known)
    (visibleFresh : K .typeAVisibleEntry ∉ known)
    (noVisibleFresh : K .typeANoVisibleEntry ∉ known) :
    Decision (K .typeAVisibleEntry) (K .typeANoVisibleEntry) previous :=
  Decision.run previous (K .typeAVisibleEntry) (K .typeANoVisibleEntry)
    `Hypostructure.Graph.Strategy.Spine.typeAVisibleEntryDichotomy
    (by
      classical
      by_cases visible :
          TypeAVisibleEntryStatement data.toParameters current.object
      · exact .inl ⟨visible⟩
      · exact .inr ⟨Graph.Contracts.TypeA.typeANoVisibleEntry_of_not_visibleEntry
          data.toParameters current.object visible⟩)
    visibleFresh noVisibleFresh

end Hypostructure.Graph.Strategy.Spine
