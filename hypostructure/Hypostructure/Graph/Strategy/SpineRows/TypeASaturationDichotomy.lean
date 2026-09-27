import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Support

/-! # Node `[89]`: is some receiver of `X₀` saturated?

`L(w) ≥ s·q(w)?`, asked of the Type A support `X₀` whose routing and threshold
algebra node `[88]` published (`K .typeAReceiverRouting`).  The yes arm (`K .typeASaturatedReceiver`) is node
`[93]`'s entry; the no arm (`K .typeAUnsaturatedReceivers`) is node `[90]`,
`L(w) ≤ s·q(w) − 1` at every receiver of `X₀`, written subtraction-free. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[89]`, decided at `X₀`. -/
noncomputable def typeASaturationDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data) current
        known)
    [FactKeys.Has (K .typeAReceiverRouting) known]
    (saturatedFresh : K .typeASaturatedReceiver ∉ known)
    (unsaturatedFresh : K .typeAUnsaturatedReceivers ∉ known) :
    Decision (K .typeASaturatedReceiver) (K .typeAUnsaturatedReceivers) previous :=
  Decision.run previous (K .typeASaturatedReceiver) (K .typeAUnsaturatedReceivers)
    `Hypostructure.Graph.Strategy.Spine.typeASaturationDichotomy
    (Classical.choice (show Nonempty
        ((K .typeASaturatedReceiver).At current ⊕ (K .typeAUnsaturatedReceivers).At current) from by
      classical
      obtain ⟨piece, pinned, _routing⟩ :=
        (previous.get (K .typeAReceiverRouting)).down
      by_cases saturated :
          ∃ receiver, SaturatedReceiverSpec data.toParameters current.object piece receiver
      · exact ⟨.inl ⟨⟨piece, pinned, saturated⟩⟩⟩
      · exact ⟨.inr ⟨⟨piece, pinned,
          Graph.Contracts.TypeA.unsaturated_of_not_saturated data.toParameters current.object
            saturated⟩⟩⟩))
    saturatedFresh unsaturatedFresh

end Hypostructure.Graph.Strategy.Spine
