import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Exits

/-! # Node `[99]`: exit `(3)`, a `P₁₃` label collision

Asked at the overloaded port of the visible receiver of `X₀`, read from its
predecessor, node `[97]`'s no arm `K .typeAExitTwoFree`: do two receiver-entry
returns through the port fail `C_s` at a common packed window of `P₀`
(`ExitThreeThrough`)?  The yes arm (`K .typeAExitThreeCollision`) reaches node
`[100]`, where the collision closes an accepted cycle (`lem:labels`); the no
arm (`K .typeAExitThreeFree`) is its exact negation at the same port. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[99]`, decided at the visible state of `X₀`. -/
noncomputable def typeAExitThreeDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data) current
        known)
    [FactKeys.Has (K .typeAExitTwoFree) known]
    (collisionFresh : K .typeAExitThreeCollision ∉ known)
    (freeFresh : K .typeAExitThreeFree ∉ known) :
    Decision (K .typeAExitThreeCollision) (K .typeAExitThreeFree) previous :=
  Decision.run previous (K .typeAExitThreeCollision) (K .typeAExitThreeFree)
    `Hypostructure.Graph.Strategy.Spine.typeAExitThreeDichotomy
    (Classical.choice (show Nonempty
        ((K .typeAExitThreeCollision).At current ⊕ (K .typeAExitThreeFree).At current) from by
      classical
      obtain ⟨piece, pinned, receiver, chosen, port, portPinned, _twoFree⟩ :=
        (previous.get (K .typeAExitTwoFree)).down
      by_cases realized : ExitThreeThrough data.toParameters current.object piece
          receiver port
      · exact ⟨.inl ⟨⟨piece, pinned, receiver, chosen, port, portPinned,
          realized⟩⟩⟩
      · exact ⟨.inr ⟨⟨piece, pinned, receiver, chosen, port, portPinned,
          realized⟩⟩⟩))
    collisionFresh freeFresh

/-- **Node `[100]`**: the label collision of exit `(3)` closes an accepted cycle
of `G`; the registered target rejects the degenerate closure
(`K .cubicBaseline`). -/
@[reducible] noncomputable def typeAExitThreeCycleRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeAExitThreeCycle
    { Requires := [K .typeAExitThreeCollision, K .cubicBaseline]
      Produces := [K .typeAExitThreeCycle]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeAExitThreeCycle)
        ⟨Graph.Contracts.TypeA.typeAExitThreeCycle data.toParameters
          inputs.current.object (inputs.get (K .cubicBaseline)).down.2.2.1
          (inputs.get (K .typeAExitThreeCollision)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
