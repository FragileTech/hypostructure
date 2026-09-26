import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Exits

/-! # Node `[101]`: exit `(4)`, a target-defective canonical quotient

`lem:typeA-exit4-residual-routing` at the witnessed saturated peeling states:
the yes arm (`K .typeASaturatedHandoffExitFour`) is peeled at node `[102]`;
the no arm (`K .typeAExitFourAbsent`) is its exact negation.  On the no arm the
entry state of the segment is the saturated exit-`(4)`-free state on which exits
`(5)`--`(8)` are asked. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

noncomputable def typeAExitFourDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data) current
        known)
    (exitFresh : K .typeASaturatedHandoffExitFour ∉ known)
    (absentFresh : K .typeAExitFourAbsent ∉ known) :
    Decision (K .typeASaturatedHandoffExitFour) (K .typeAExitFourAbsent)
      previous :=
  Decision.run previous (K .typeASaturatedHandoffExitFour)
    (K .typeAExitFourAbsent)
    `Hypostructure.Graph.Strategy.Spine.typeAExitFourDichotomy
    (by
      classical
      by_cases exit :
          TypeASaturatedHandoffExitFourStatement data.toParameters current.object
      · exact .inl ⟨exit⟩
      · exact .inr ⟨Graph.Contracts.TypeA.typeAExitFourAbsent_of_not_exitFour
          data.toParameters current.object exit⟩)
    exitFresh absentFresh

/-- Node `[101]`, no arm → `[103]`: the entry state, with exit `(4)` absent. -/
@[reducible] noncomputable def typeAExitFourFreeEntryRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeAExitFourFreeEntry
    { Requires := [K .typeASaturatedExitEntry, K .typeAExitFourAbsent]
      Produces := [K .typeASaturatedHandoffExitFourFree]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeASaturatedHandoffExitFourFree)
        ⟨Graph.Contracts.TypeA.typeASaturatedHandoffExitFourFree_of_absent
          data.toParameters inputs.current.object inputs.current.baseline
          (inputs.get (K .typeASaturatedExitEntry)).down
          (inputs.get (K .typeAExitFourAbsent)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
