import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Exits

/-! # Nodes `[107]`--`[109]`: exit `(7)` and the route-`8` residual

Exit `(7)` is asked at the terminal state where exits `(4)`--`(6)` fail, read
from `K .typeAExitSixFree` (with the zero surplus of `X₀` from
`K .typeALowSurplus`).  The yes arm (`K .typeAExitSevenHandoff`) is node
`[108]`: `X₀` produces a decorated handoff at a surviving first separator,
which returns to Type B at `[65]`.  The no arm (`K .typeAExitSevenFree`) is its
exact negation at the same state: node `[109]`, the route-`8` residual
continued in Part IX.  These are d2ded0e's two arm keys. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Nodes `[107]`/`[108]`/`[109]`, decided at the terminal state. -/
noncomputable def typeAExitSevenDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data) current
        known)
    [FactKeys.Has (K .typeALowSurplus) known]
    [FactKeys.Has (K .typeAExitSixFree) known]
    (handoffFresh : K .typeAExitSevenHandoff ∉ known)
    (freeFresh : K .typeAExitSevenFree ∉ known) :
    Decision (K .typeAExitSevenHandoff) (K .typeAExitSevenFree) previous :=
  Decision.run previous (K .typeAExitSevenHandoff) (K .typeAExitSevenFree)
    `Hypostructure.Graph.Strategy.Spine.typeAExitSevenDichotomy
    (Classical.choice (show Nonempty
        ((K .typeAExitSevenHandoff).At current ⊕ (K .typeAExitSevenFree).At current) from by
      classical
      obtain ⟨piece, pinned, zero, receiver, chosen, state⟩ :=
        canonicalPin_merge (previous.get (K .typeALowSurplus)).down
          (previous.get (K .typeAExitSixFree)).down
      by_cases handoff : SeparatorHandoffAt data.toParameters current.object piece
      · exact ⟨.inl ⟨⟨piece, pinned, receiver, chosen, zero, state, handoff⟩⟩⟩
      · exact ⟨.inr ⟨⟨piece, pinned, receiver, chosen, zero, state, handoff⟩⟩⟩))
    handoffFresh freeFresh

end Hypostructure.Graph.Strategy.Spine
