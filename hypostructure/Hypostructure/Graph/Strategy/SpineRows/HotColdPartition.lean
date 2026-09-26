import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.SpineWindows

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

variable [FactSystem (Input BranchState Presentation presentation data)]

/-! ## Node `[22]`: the canonical hot/cold partition

`def:cold-window-ledger`.  The manuscript fixes the maximal packing once (the
lexicographically first object with the extremal property, `lem:skeleton-dominates`)
and splits it into hot and cold windows.  `canonicalWindowPacking` is that fixed
packing, so its defining specification is the whole input of the split: the row
reads no predecessor fact and re-proves nothing.  `hot` and `cold` are the
canonical filters inside the ledger proposition; they are not callback arguments
or mutable routing state. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def hotColdPartitionRow :
    @AtomicStrategy (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  @factOnly (Input BranchState Presentation presentation data) _
    (instFactSystem (BranchState := BranchState)
      (Presentation := Presentation) (presentation := presentation)
      (data := data))
    `Hypostructure.Graph.Strategy.Spine.hotColdPartition
    { Requires := []
      Produces := [K .hotColdPartition]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .hotColdPartition)
        ⟨Contracts.Spine.hotColdPartition_canonical data.toParameters
          inputs.current.object⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
