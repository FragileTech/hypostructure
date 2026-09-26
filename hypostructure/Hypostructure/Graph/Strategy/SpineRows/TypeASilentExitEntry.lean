import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Support

/-! # Node `[94]` → `[101]`: the silent entry of the exit segment

On the silent lane the node-`[94]` saturated receiver enters the same exit
segment at the empty peeling set (`lem:typeA-unpeeled-silent-routing`).  Thin
adapter of `Contracts.TypeA.typeASaturatedExitEntry_of_visibleFirstExcess`. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

@[reducible] noncomputable def typeASilentExitEntryRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeASilentExitEntry
    { Requires := [K .typeAVisibleFirstExcess, K .typeANoVisibleEntry]
      Produces := [K .typeASaturatedExitEntry]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeASaturatedExitEntry)
        ⟨Graph.Contracts.TypeA.typeASaturatedExitEntry_of_visibleFirstExcess
          data.toParameters inputs.current.object
          (inputs.get (K .typeAVisibleFirstExcess)).down
          (inputs.get (K .typeANoVisibleEntry)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
