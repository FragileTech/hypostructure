import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.DominantType

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

/-! ## Node `[51]`, `lem:dominant-type`

The repetitive coordinate is a finite relabelling-orbit statement.  Its
multinomial threshold supplies a fibre covering all but `T(n)` vertices of the
subcubic remainder.  At most another `T(n)` vertices lie outside that support,
by the incoming near-cubic surplus bound. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def dominantRootedTypeRow :
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
    `Hypostructure.Graph.Strategy.Spine.dominantRootedType
    { Requires := [K .localTypeCoordinateRepetitive, K .surplusAtOrBelow]
      Produces := [K .dominantRootedType]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .dominantRootedType)
        ⟨Contracts.Spine.dominantRootedType_of_repetitive data.toParameters
          inputs.current.object inputs.current.baseline
          (inputs.get (K .localTypeCoordinateRepetitive)).down
          (inputs.get (K .surplusAtOrBelow)).down⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
