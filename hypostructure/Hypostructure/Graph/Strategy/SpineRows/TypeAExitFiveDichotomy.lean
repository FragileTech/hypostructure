import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Exits

/-! # Node `[103]`: exit `(5)`, a target-complete response compression

Asked at the terminal state `(X₀, w, P₄(w))`, read from
`K .typeASaturatedHandoffExitFourFree`.  The yes arm (`K .typeAExitFive`)
closes at node `[104]` against `cor:uncompressible`; the no arm
(`K .typeAExitFiveFree`) is its exact negation at the same state. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[103]`, decided at the terminal state. -/
noncomputable def typeAExitFiveDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data) current
        known)
    [FactKeys.Has (K .typeASaturatedHandoffExitFourFree) known]
    (exitFresh : K .typeAExitFive ∉ known)
    (freeFresh : K .typeAExitFiveFree ∉ known) :
    Decision (K .typeAExitFive) (K .typeAExitFiveFree) previous :=
  Decision.run previous (K .typeAExitFive) (K .typeAExitFiveFree)
    `Hypostructure.Graph.Strategy.Spine.typeAExitFiveDichotomy
    (Classical.choice (show Nonempty
        ((K .typeAExitFive).At current ⊕ (K .typeAExitFiveFree).At current) from by
      classical
      obtain ⟨piece, pinned, receiver, chosen, state⟩ :=
        (previous.get (K .typeASaturatedHandoffExitFourFree)).down
      by_cases five : ExitFiveAt data.toParameters current.object piece receiver
          (canonicalTerminalPeeled data.toParameters current.object piece receiver)
      · exact ⟨.inl ⟨⟨piece, pinned, receiver, chosen, state, five⟩⟩⟩
      · exact ⟨.inr ⟨⟨piece, pinned, receiver, chosen, state, five⟩⟩⟩))
    exitFresh freeFresh

end Hypostructure.Graph.Strategy.Spine
