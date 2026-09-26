import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Exits

/-! # `lem:typeA-exit4-finite-descent` at the entry of the exit segment

The finite exit-`(4)` descent from the entry state: every peeling step lowers
the residual load, so repeated peeling ends at a terminal or an unsaturated
state.  Thin adapter of `Contracts.TypeA.typeAExitFourFiniteDescent`. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

@[reducible] noncomputable def typeAExitFourFiniteDescentRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeAExitFourFiniteDescent
    { Requires := [K .typeASaturatedExitEntry]
      Produces := [K .typeAExitFourFiniteDescent]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeAExitFourFiniteDescent)
        ⟨Graph.Contracts.TypeA.typeAExitFourFiniteDescent data.toParameters
          inputs.current.object (inputs.get (K .typeASaturatedExitEntry)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
