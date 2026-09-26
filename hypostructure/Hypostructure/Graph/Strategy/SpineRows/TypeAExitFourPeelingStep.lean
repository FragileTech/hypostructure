import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Exits

/-! # Node `[102]`: the exit-`(4)` peel

`lem:typeA-exit4-discharge`: the witness's routed load is adjoined to the
peeling set, which stays inside the routed loads, and the residual load drops
by exactly one.  Thin adapter of `Contracts.TypeA.typeAExitFourPeeled`. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

@[reducible] noncomputable def typeAExitFourPeelingStepRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeAExitFourPeelingStep
    { Requires := [K .typeASaturatedExitEntry, K .typeASaturatedHandoffExitFour]
      Produces := [K .typeAExitFourPeeled]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeAExitFourPeeled)
        ⟨Graph.Contracts.TypeA.typeAExitFourPeeled data.toParameters
          inputs.current.object
          (inputs.get (K .typeASaturatedExitEntry)).down
          (inputs.get (K .typeASaturatedHandoffExitFour)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
