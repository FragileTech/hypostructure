import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Exits

/-! # Node `[95]`: exit `(1)`, a Mersenne anchored return

Asked at the overloaded port of the visible receiver of `X₀`, read from
`K .typeAVisibleEntry` (d2ded0e: the port of the node-`[93]` package).  The yes
arm (`K .typeAExitOneReturn`) closes at node `[96]` against the
return-avoidance invariant (`lem:return-equivalence`); the no arm
(`K .typeAExitOneFree`) is its exact negation at the same port. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[95]`, decided at the overloaded port of the visible receiver of `X₀`. -/
noncomputable def typeAExitOneDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data) current
        known)
    [FactKeys.Has (K .typeAVisibleEntry) known]
    (returnFresh : K .typeAExitOneReturn ∉ known)
    (freeFresh : K .typeAExitOneFree ∉ known) :
    Decision (K .typeAExitOneReturn) (K .typeAExitOneFree) previous :=
  Decision.run previous (K .typeAExitOneReturn) (K .typeAExitOneFree)
    `Hypostructure.Graph.Strategy.Spine.typeAExitOneDichotomy
    (Classical.choice (show Nonempty
        ((K .typeAExitOneReturn).At current ⊕ (K .typeAExitOneFree).At current) from by
      classical
      obtain ⟨piece, pinned, receiver, chosen, port, portPinned⟩ :=
        Graph.Contracts.TypeA.visibleEntry_pins data.toParameters current.object
          (previous.get (K .typeAVisibleEntry)).down
      by_cases realized : ∃ return' : Graph.VisibleEntry.AnchoredReturn current.object receiver
            port, Graph.ShiftedCycleLength data.LengthOK return'.path.length
      · exact ⟨.inl ⟨⟨piece, pinned, receiver, chosen, port, portPinned,
          realized⟩⟩⟩
      · exact ⟨.inr ⟨⟨piece, pinned, receiver, chosen, port, portPinned,
          fun return' accepted => realized ⟨return', accepted⟩⟩⟩⟩))
    returnFresh freeFresh

end Hypostructure.Graph.Strategy.Spine
