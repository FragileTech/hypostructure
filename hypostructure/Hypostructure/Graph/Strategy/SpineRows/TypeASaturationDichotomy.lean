import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Support

/-! # Node `[89]`: is some receiver of a Type A support saturated?

`L(w) ≥ s·q(w)?`  The yes arm (`K .typeASaturatedReceiver`) is node `[93]`'s
entry; the no arm (`K .typeAUnsaturatedReceivers`) is node `[90]`,
`L(w) ≤ s·q(w) − 1`, the exact negation written subtraction-free.  The
decision is a case analysis on the yes-arm proposition. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

noncomputable def typeASaturationDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data) current
        known)
    (saturatedFresh : K .typeASaturatedReceiver ∉ known)
    (unsaturatedFresh : K .typeAUnsaturatedReceivers ∉ known) :
    Decision (K .typeASaturatedReceiver) (K .typeAUnsaturatedReceivers)
      previous :=
  Decision.run previous (K .typeASaturatedReceiver)
    (K .typeAUnsaturatedReceivers)
    `Hypostructure.Graph.Strategy.Spine.typeASaturationDichotomy
    (by
      classical
      by_cases saturated :
          TypeASaturatedReceiverStatement data.toParameters current.object
      · exact .inl ⟨saturated⟩
      · exact .inr ⟨Graph.Contracts.TypeA.typeAUnsaturatedReceivers_of_not_saturated
          data.toParameters current.object saturated⟩)
    saturatedFresh unsaturatedFresh

end Hypostructure.Graph.Strategy.Spine
