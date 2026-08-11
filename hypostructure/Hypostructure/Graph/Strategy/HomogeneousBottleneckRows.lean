import Hypostructure.Graph.Strategy.SpineRows
import Hypostructure.Graph.NamedSurplusExits

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}
@[reducible] noncomputable def sparseSurplusSurvivorRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sparseSurplusSurvivor
    { Requires := [K .selection, K .uncompressible]
      Produces := [K .sparseSurplusSurvivor]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let selection := (inputs.get (K .selection)).down
      let uncompressible := (inputs.get (K .uncompressible)).down
      .cons (key := K .sparseSurplusSurvivor)
        (show Value BranchState Presentation presentation data
            .sparseSurplusSurvivor inputs.current from
          ⟨⟨Graph.survives_of_selection selection.1 selection.2 uncompressible,
            fun _support replacement =>
              not_globalBarrierReading (BranchState := BranchState)
                (Presentation := Presentation) (presentation := presentation)
                (data := data) inputs.current selection.1 selection.2
                (Or.inl replacement)⟩⟩)
        .nil)

end Hypostructure.Graph.Strategy.Spine
