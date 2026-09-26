import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Exits

/-! # Nodes `[107]`--`[109]`: exit `(7)` and the route-`8` residual

Exit `(7)` is asked at the saturated states where exits `(4)`--`(6)` fail.
The yes arm (`K .typeAExitSevenHandoff`) is node `[108]`: the produced
decorated handoff fan envelope, which returns to Type B at `[65]`.  The no arm
(`K .typeAExitSevenAbsent`) is its exact negation, and on it the
exit-`(4)`-free state of the segment is node `[109]`, the route-`8` residual
continued in Part IX. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

noncomputable def typeAExitSevenDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data) current
        known)
    (handoffFresh : K .typeAExitSevenHandoff ∉ known)
    (absentFresh : K .typeAExitSevenAbsent ∉ known) :
    Decision (K .typeAExitSevenHandoff) (K .typeAExitSevenAbsent) previous :=
  Decision.run previous (K .typeAExitSevenHandoff) (K .typeAExitSevenAbsent)
    `Hypostructure.Graph.Strategy.Spine.typeAExitSevenDichotomy
    (by
      classical
      by_cases handoff :
          TypeAExitSevenHandoffStatement data.toParameters current.object
      · exact .inl ⟨handoff⟩
      · exact .inr ⟨Graph.Contracts.TypeA.typeAExitSevenAbsent_of_not_handoff
          data.toParameters current.object handoff⟩)
    handoffFresh absentFresh

/-- Node `[109]`: the route-`8` residual state. -/
@[reducible] noncomputable def typeAExitSevenFreeRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeAExitSevenFree
    { Requires := [K .typeASaturatedHandoffExitFourFree, K .typeAExitFiveFree,
        K .typeAExitSixFree, K .typeAExitSevenAbsent]
      Produces := [K .typeAExitSevenFree]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeAExitSevenFree)
        ⟨Graph.Contracts.TypeA.typeAExitSevenFree data.toParameters
          inputs.current.object
          (inputs.get (K .typeASaturatedHandoffExitFourFree)).down
          (inputs.get (K .typeAExitFiveFree)).down
          (inputs.get (K .typeAExitSixFree)).down
          (inputs.get (K .typeAExitSevenAbsent)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
