import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Exits

/-! # Node `[99]`: exit `(3)`, a `P₁₃` label collision

Asked at the visible state of `X₀`, read from `K .typeAVisibleEntry`; the
collision is the one of the canonical packing `P₀`, as at d2ded0e.  The yes arm
(`K .typeAExitThreeCollision`) closes at node `[100]` (`lem:labels`); the no
arm (`K .typeAExitThreeFree`) is its exact negation. -/

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
    [FactKeys.Has (K .typeAVisibleEntry) known]
    (collisionFresh : K .typeAExitThreeCollision ∉ known)
    (freeFresh : K .typeAExitThreeFree ∉ known) :
    Decision (K .typeAExitThreeCollision) (K .typeAExitThreeFree) previous :=
  Decision.run previous (K .typeAExitThreeCollision) (K .typeAExitThreeFree)
    `Hypostructure.Graph.Strategy.Spine.typeAExitThreeDichotomy
    (Classical.choice (show Nonempty
        ((K .typeAExitThreeCollision).At current ⊕ (K .typeAExitThreeFree).At current) from by
      classical
      obtain ⟨piece, pinned, receiver, chosen, port, portPinned⟩ :=
        Graph.Contracts.TypeA.visibleEntry_pins data.toParameters current.object
          (previous.get (K .typeAVisibleEntry)).down
      by_cases realized : Graph.WindowLabelCollision.LabelCollision current.object
            data.windowOrder data.LengthOK (canonicalWindowPacking data.toParameters current.object)
      · exact ⟨.inl ⟨⟨piece, pinned, receiver, chosen, port, portPinned,
          realized⟩⟩⟩
      · exact ⟨.inr ⟨⟨piece, pinned, receiver, chosen, port, portPinned,
          realized⟩⟩⟩))
    collisionFresh freeFresh

end Hypostructure.Graph.Strategy.Spine
