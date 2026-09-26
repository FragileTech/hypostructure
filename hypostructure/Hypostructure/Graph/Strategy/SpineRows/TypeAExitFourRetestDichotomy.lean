import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Exits

/-! # Node `[102]` → `[89]`: recompute `L₄`

After the exit-`(4)` peel of node `[102]` (`K .typeAExitFourPeeled`) the
canonical witnessed peeling sequence of the exit-chain receiver runs to its
terminal set `P₄(w)` (`lem:typeA-saturated-handoff`), and the saturation test
is asked there.  The yes arm (`K .typeASaturatedHandoffExitFourFree`): the
receiver is still saturated at `P₄(w)`, which is then exit-`(4)`-free, and
exits `(5)`--`(8)` are asked there.  The no arm
(`K .typeAExitFourReceiverDischarged`): it is unsaturated at `P₄(w)`, with
nonnegative remaining charge (`lem:typeA-exit4-peeling-charge`).  These are
d2ded0e's two arms of the same retest. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[102]` → `[89]`, decided at the terminal state of the canonical sequence. -/
noncomputable def typeAExitFourRetestDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data) current
        known)
    [FactKeys.Has (K .typeALowSurplus) known]
    [FactKeys.Has (K .typeAExitFourPeeled) known]
    (freeFresh : K .typeASaturatedHandoffExitFourFree ∉ known)
    (dischargedFresh : K .typeAExitFourReceiverDischarged ∉ known) :
    Decision (K .typeASaturatedHandoffExitFourFree) (K .typeAExitFourReceiverDischarged) previous :=
  Decision.run previous (K .typeASaturatedHandoffExitFourFree) (K .typeAExitFourReceiverDischarged)
    `Hypostructure.Graph.Strategy.Spine.typeAExitFourRetestDichotomy
    (Classical.choice (show Nonempty
        ((K .typeASaturatedHandoffExitFourFree).At current ⊕ (K .typeAExitFourReceiverDischarged).At current) from by
      classical
      obtain ⟨piece, pinned, zero, receiver, chosen, _⟩ :=
        canonicalPin_merge (previous.get (K .typeALowSurplus)).down
          (previous.get (K .typeAExitFourPeeled)).down
      by_cases saturated : Graph.ExitFour.SaturatedAfter piece data.threshold
          data.dischargeScale receiver
          (canonicalTerminalPeeled data.toParameters current.object piece receiver)
      · exact ⟨.inl ⟨⟨piece, pinned, receiver, chosen, saturated,
          Graph.Contracts.TypeA.exitFourFreeAt_terminal data.toParameters current.object
            current.baseline zero chosen saturated⟩⟩⟩
      · exact ⟨.inr ⟨⟨piece, pinned, receiver, chosen, saturated,
          Graph.Contracts.TypeA.receiverDischarged_of_not_saturated
            data.toParameters current.object saturated⟩⟩⟩))
    freeFresh dischargedFresh

end Hypostructure.Graph.Strategy.Spine
