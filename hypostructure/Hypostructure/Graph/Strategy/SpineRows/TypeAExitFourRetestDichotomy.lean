import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Exits

/-! # Node `[102]` → `[89]`: recompute `L₄`

After the exit-`(4)` peel the saturated test is asked again.  The yes arm
(`K .typeASaturatedHandoffExitFourFree`): some saturated peeling state is
exit-`(4)`-free, and exits `(5)`--`(8)` are asked there.  The no arm
(`K .typeAExitFourExhausted`) is its exact negation: every saturated peeling
state still realizes exit `(4)`, so the finite descent
(`lem:typeA-saturated-handoff`) peels the node-`[102]` receiver down to an
unsaturated state whose remaining charge is nonnegative
(`lem:typeA-exit4-peeling-charge`). -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

noncomputable def typeAExitFourRetestDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data) current
        known)
    (freeFresh : K .typeASaturatedHandoffExitFourFree ∉ known)
    (exhaustedFresh : K .typeAExitFourExhausted ∉ known) :
    Decision (K .typeASaturatedHandoffExitFourFree) (K .typeAExitFourExhausted)
      previous :=
  Decision.run previous (K .typeASaturatedHandoffExitFourFree)
    (K .typeAExitFourExhausted)
    `Hypostructure.Graph.Strategy.Spine.typeAExitFourRetestDichotomy
    (by
      classical
      by_cases free :
          TypeASaturatedHandoffExitFourFreeStatement data.toParameters
            current.object
      · exact .inl ⟨free⟩
      · exact .inr ⟨Graph.Contracts.TypeA.typeAExitFourExhausted_of_not_free
          data.toParameters current.object free⟩)
    freeFresh exhaustedFresh

/-- The retest's no arm: the peeled receiver is discharged. -/
@[reducible] noncomputable def typeAExitFourDischargedRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeAExitFourDischarged
    { Requires := [K .typeAExitFourPeeled, K .typeAExitFourExhausted]
      Produces := [K .typeAExitFourReceiverDischarged]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeAExitFourReceiverDischarged)
        ⟨Graph.Contracts.TypeA.typeAExitFourReceiverDischarged data.toParameters
          inputs.current.object inputs.current.baseline
          (inputs.get (K .typeAExitFourPeeled)).down
          (inputs.get (K .typeAExitFourExhausted)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
