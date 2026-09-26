import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Exits

/-! # Node `[97]`: exit `(2)`, a power-of-two common-port theta

Asked at the overloaded port of the visible receiver of `X₀`, read from
`K .typeAVisibleEntry`.  The yes arm (`K .typeAExitTwoTheta`) closes at node
`[98]` (`lem:typeA-common-port-return-cycle`); the no arm
(`K .typeAExitTwoFree`) is its exact negation at the same port. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[97]`, decided at the overloaded port of the visible receiver of `X₀`. -/
noncomputable def typeAExitTwoDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data) current
        known)
    [FactKeys.Has (K .typeAVisibleEntry) known]
    (thetaFresh : K .typeAExitTwoTheta ∉ known)
    (freeFresh : K .typeAExitTwoFree ∉ known) :
    Decision (K .typeAExitTwoTheta) (K .typeAExitTwoFree) previous :=
  Decision.run previous (K .typeAExitTwoTheta) (K .typeAExitTwoFree)
    `Hypostructure.Graph.Strategy.Spine.typeAExitTwoDichotomy
    (Classical.choice (show Nonempty
        ((K .typeAExitTwoTheta).At current ⊕ (K .typeAExitTwoFree).At current) from by
      classical
      obtain ⟨piece, pinned, receiver, chosen, port, portPinned⟩ :=
        Graph.Contracts.TypeA.visibleEntry_pins data.toParameters current.object
          (previous.get (K .typeAVisibleEntry)).down
      by_cases realized : Graph.VisibleEntry.ExitTwoThrough current.object piece data.LengthOK
            receiver port
      · exact ⟨.inl ⟨⟨piece, pinned, receiver, chosen, port, portPinned,
          realized⟩⟩⟩
      · exact ⟨.inr ⟨⟨piece, pinned, receiver, chosen, port, portPinned,
          realized⟩⟩⟩))
    thetaFresh freeFresh

end Hypostructure.Graph.Strategy.Spine
