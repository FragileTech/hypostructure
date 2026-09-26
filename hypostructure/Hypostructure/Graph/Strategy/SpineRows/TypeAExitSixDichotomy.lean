import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Exits

/-! # Node `[105]`: exit `(6)`, support dependence

Asked at the terminal state, read from `K .typeAExitFiveFree`.  The yes arm
(`K .typeAExitSix`) is scoped and closed at node `[106]`; the no arm
(`K .typeAExitSixFree`) is its exact negation at the same state. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[105]`, decided at the terminal state. -/
noncomputable def typeAExitSixDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data) current
        known)
    [FactKeys.Has (K .typeAExitFiveFree) known]
    (exitFresh : K .typeAExitSix ∉ known)
    (freeFresh : K .typeAExitSixFree ∉ known) :
    Decision (K .typeAExitSix) (K .typeAExitSixFree) previous :=
  Decision.run previous (K .typeAExitSix) (K .typeAExitSixFree)
    `Hypostructure.Graph.Strategy.Spine.typeAExitSixDichotomy
    (Classical.choice (show Nonempty
        ((K .typeAExitSix).At current ⊕ (K .typeAExitSixFree).At current) from by
      classical
      obtain ⟨piece, pinned, receiver, chosen, state⟩ :=
        (previous.get (K .typeAExitFiveFree)).down
      by_cases six : ExitSixDelocalizes data.toParameters current.object piece receiver
          (canonicalTerminalPeeled data.toParameters current.object piece receiver)
      · exact ⟨.inl ⟨⟨piece, pinned, receiver, chosen, state, six⟩⟩⟩
      · exact ⟨.inr ⟨⟨piece, pinned, receiver, chosen, state, six⟩⟩⟩))
    exitFresh freeFresh

end Hypostructure.Graph.Strategy.Spine
