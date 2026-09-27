import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Exits

/-! # Nodes `[107]`--`[109]`: exit `(7)` and the route-`8` residual

Exit `(7)` is asked at the terminal state `(X₀, w, P₄(w))` where exits
`(4)`--`(6)` fail, read from `K .typeAExitSixFree` (with the zero surplus of
`X₀` from `K .typeALowSurplus`): does an eligible load of `w` at `P₄(w)` have a
surviving first separator (`ExitSevenAt`)?  The yes arm
(`K .typeAExitSevenHandoff`) continues to node `[108]`
(`typeAExitSevenEnvelopeRow`), which builds the decorated handoff fan envelope
and returns to Type B.  The no arm (`K .typeAExitSevenFree`) is its exact
negation at the same state: node `[109]`, the route-`8` residual continued in
Part IX. -/

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
      by_cases handoff : ExitSevenAt data.toParameters current.object piece receiver
          (canonicalTerminalPeeled data.toParameters current.object piece receiver)
      · exact ⟨.inl ⟨⟨piece, pinned, receiver, chosen, zero, state, handoff⟩⟩⟩
      · exact ⟨.inr ⟨⟨piece, pinned, receiver, chosen, zero, state, handoff⟩⟩⟩))
    handoffFresh freeFresh

/-- **Node `[108]`**: the exit-`(7)` separation of the terminal state is the
canonical separation of `X₀`, and `lem:typeA-high-degree-handoff` builds its
decorated handoff fan envelope (the separator has degree at least `4`, above the
registered baseline `3`; the exit-`(3)` absorbing clause is refuted by target
avoidance with the degenerate closure rejected). -/
@[reducible] noncomputable def typeAExitSevenEnvelopeRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeAExitSevenEnvelope
    { Requires := [K .typeAExitSevenHandoff, K .selection, K .cubicBaseline]
      Produces := [K .typeAExitSevenEnvelope]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeAExitSevenEnvelope)
        ⟨Graph.Contracts.TypeA.typeAExitSevenEnvelope data.toParameters
          inputs.current.object (inputs.get (K .selection)).down.1
          (inputs.get (K .cubicBaseline)).down.1.1
          (inputs.get (K .cubicBaseline)).down.1.2.2.1
          (inputs.get (K .typeAExitSevenHandoff)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
