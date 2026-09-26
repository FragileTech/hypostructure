import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Support

/-! # Node `[99]` → `[101]`: the visible entry of the exit segment

On the visible lane, after exits `(1)`--`(3)` have failed, the saturated
receiver of the node-`[93]` package enters the shared exit segment at the
empty peeling set (`lem:typeA-unpeeled-visible-routing`).  Thin adapter of
`Contracts.TypeA.typeASaturatedExitEntry_of_exitThreeFree`. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

@[reducible] noncomputable def typeAVisibleExitEntryRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeAVisibleExitEntry
    { Requires := [K .typeAExitThreeFree]
      Produces := [K .typeASaturatedExitEntry]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeASaturatedExitEntry)
        ⟨Graph.Contracts.TypeA.typeASaturatedExitEntry_of_exitThreeFree
          data.toParameters inputs.current.object
          (inputs.get (K .typeAExitThreeFree)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
