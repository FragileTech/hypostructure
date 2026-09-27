import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Exits

/-! # Node `[102]` → `[89]`: recompute `L₄`

After the exit-`(4)` peel of node `[102]` (`K .typeAExitFourPeeled`) node `[89]`
is asked again with the residual loads (tex 1095, "recompute `L₄`";
`lem:typeA-saturated-handoff`): is some receiver of `X₀` still saturated,
`L₄(w) ≥ s·q(w)`, after its canonical witnessed peeling sequence has stopped?
The yes arm (`K .typeAPeeledSaturatedReceiver`) is the terminal receiver `w`
at its terminal set `P₄(w)`, which re-enters node `[93]`.  The no arm
(`K .typeAExitFourReceiverDischarged`) is node `[90]` with `L₄`: every receiver
of `X₀` is unsaturated after peeling; node `[91]`
(`K .typeAPeeledUnsaturatedDischarge`) is the charge bound on the unpeeled
loads (`lem:typeA-exit4-peeling-charge`). -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[102]` → `[89]`, decided over the receivers of `X₀` at their terminal
sets. -/
noncomputable def typeAExitFourRetestDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data) current
        known)
    [FactKeys.Has (K .typeAExitFourPeeled) known]
    (saturatedFresh : K .typeAPeeledSaturatedReceiver ∉ known)
    (dischargedFresh : K .typeAExitFourReceiverDischarged ∉ known) :
    Decision (K .typeAPeeledSaturatedReceiver)
      (K .typeAExitFourReceiverDischarged) previous :=
  Decision.run previous (K .typeAPeeledSaturatedReceiver)
    (K .typeAExitFourReceiverDischarged)
    `Hypostructure.Graph.Strategy.Spine.typeAExitFourRetestDichotomy
    (Classical.choice (show Nonempty
        ((K .typeAPeeledSaturatedReceiver).At current ⊕
          (K .typeAExitFourReceiverDischarged).At current) from by
      classical
      obtain ⟨piece, pinned, _peeled⟩ :=
        (previous.get (K .typeAExitFourPeeled)).down
      by_cases saturated :
          ∃ receiver, TerminalSaturatedSpec data.toParameters current.object piece
            receiver
      · obtain ⟨receiver, chosen, spec⟩ := canonicalTerminalReceiverAt_spec saturated
        exact ⟨.inl ⟨⟨piece, pinned, receiver, chosen, spec.2⟩⟩⟩
      · exact ⟨.inr ⟨⟨piece, pinned,
          Graph.Contracts.TypeA.receiverDischarged_of_not_terminalSaturated
            data.toParameters current.object saturated⟩⟩⟩))
    saturatedFresh dischargedFresh

/-- Node `[91]` after peeling: `|V(X₀)| ≤ s·def⁺(X₀) + Σ_w |P₄(w)|`. -/
@[reducible] noncomputable def typeAPeeledUnsaturatedDischargeRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeAPeeledUnsaturatedDischarge
    { Requires := [K .typeAReceiverRouting, K .typeALowSurplus,
        K .typeAExitFourReceiverDischarged]
      Produces := [K .typeAPeeledUnsaturatedDischarge]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeAPeeledUnsaturatedDischarge)
        ⟨Graph.Contracts.TypeA.typeAPeeledUnsaturatedDischarge data.toParameters
          inputs.current.object
          (inputs.get (K .typeAReceiverRouting)).down
          (inputs.get (K .typeALowSurplus)).down
          (inputs.get (K .typeAExitFourReceiverDischarged)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
