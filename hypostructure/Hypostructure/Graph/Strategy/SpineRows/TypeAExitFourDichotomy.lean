import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Exits

/-! # Node `[101]`: exit `(4)`, a target-defective canonical quotient

`lem:typeA-exit4-residual-routing` at the entry state of the exit segment: the
exit-chain receiver of `X₀` at the empty peeling set, read from
`K .typeASaturatedExitEntry`.  The yes arm (`K .typeASaturatedHandoffExitFour`)
is peeled at node `[102]`; the no arm (`K .typeAExitFourAbsent`) is its exact
negation at the same state, on which the terminal state of the canonical
peeling sequence is the entry state itself. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[101]`, decided at the entry state. -/
noncomputable def typeAExitFourDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data) current
        known)
    [FactKeys.Has (K .typeASaturatedExitEntry) known]
    (exitFresh : K .typeASaturatedHandoffExitFour ∉ known)
    (absentFresh : K .typeAExitFourAbsent ∉ known) :
    Decision (K .typeASaturatedHandoffExitFour) (K .typeAExitFourAbsent) previous :=
  Decision.run previous (K .typeASaturatedHandoffExitFour) (K .typeAExitFourAbsent)
    `Hypostructure.Graph.Strategy.Spine.typeAExitFourDichotomy
    (Classical.choice (show Nonempty
        ((K .typeASaturatedHandoffExitFour).At current ⊕ (K .typeAExitFourAbsent).At current) from by
      classical
      obtain ⟨piece, pinned, receiver, chosen, _⟩ :=
        (previous.get (K .typeASaturatedExitEntry)).down
      by_cases exit : ExitFourAt data.toParameters current.object piece receiver ∅
      · exact ⟨.inl ⟨⟨piece, pinned, receiver, chosen, exit⟩⟩⟩
      · exact ⟨.inr ⟨⟨piece, pinned, receiver, chosen, exit⟩⟩⟩))
    exitFresh absentFresh

/-- Node `[101]`, no arm → `[103]`: the terminal state is the entry state,
saturated and exit-`(4)`-free. -/
@[reducible] noncomputable def typeAExitFourFreeEntryRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeAExitFourFreeEntry
    { Requires := [K .typeALowSurplus, K .typeASaturatedExitEntry,
        K .typeAExitFourAbsent]
      Produces := [K .typeASaturatedHandoffExitFourFree]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeASaturatedHandoffExitFourFree)
        ⟨Graph.Contracts.TypeA.typeASaturatedHandoffExitFourFree_of_absent
          data.toParameters inputs.current.object inputs.current.baseline
          (inputs.get (K .typeALowSurplus)).down
          (inputs.get (K .typeASaturatedExitEntry)).down
          (inputs.get (K .typeAExitFourAbsent)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
