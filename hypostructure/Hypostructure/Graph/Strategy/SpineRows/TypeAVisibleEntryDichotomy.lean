import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Support

/-! # Node `[93]`: does a saturated receiver of `X₀` see `s` visible returns at one port?

Asked of `X₀`, read from `K .typeASaturatedReceiver`.  The yes arm
(`K .typeAVisibleEntry`) enters the saturated exit chain at node `[95]` at the
visible receiver of `X₀`; the no arm (`K .typeANoVisibleEntry`) is its exact
negation at `X₀` and the hypothesis of `lem:typeA-silent-excess-count` at node
`[94]`. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[93]`, decided at `X₀`. -/
noncomputable def typeAVisibleEntryDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data) current
        known)
    [FactKeys.Has (K .typeASaturatedReceiver) known]
    (visibleFresh : K .typeAVisibleEntry ∉ known)
    (noVisibleFresh : K .typeANoVisibleEntry ∉ known) :
    Decision (K .typeAVisibleEntry) (K .typeANoVisibleEntry) previous :=
  Decision.run previous (K .typeAVisibleEntry) (K .typeANoVisibleEntry)
    `Hypostructure.Graph.Strategy.Spine.typeAVisibleEntryDichotomy
    (Classical.choice (show Nonempty
        ((K .typeAVisibleEntry).At current ⊕ (K .typeANoVisibleEntry).At current) from by
      classical
      obtain ⟨piece, pinned, _⟩ := (previous.get (K .typeASaturatedReceiver)).down
      by_cases visible :
          ∃ receiver, VisibleReceiverSpec data.toParameters current.object piece receiver
      · exact ⟨.inl ⟨⟨piece, pinned, canonicalVisibleReceiverAt_spec visible⟩⟩⟩
      · exact ⟨.inr ⟨⟨piece, pinned,
          Graph.Contracts.TypeA.noVisible_of_not_visibleReceiver data.toParameters current.object
            visible⟩⟩⟩))
    visibleFresh noVisibleFresh

end Hypostructure.Graph.Strategy.Spine
