import Hypostructure.Graph.Strategy.DominantRootedType

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
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let repetitiveInput :=
        (inputs.get (K .localTypeCoordinateRepetitive)).down
      let nearCubic := (inputs.get (K .surplusAtOrBelow)).down
      .cons (key := K .dominantRootedType)
        (show Value BranchState Presentation presentation data
            .dominantRootedType inputs.current from
          ⟨dominantRootedType_of_repetitive data inputs.current.object
            inputs.current.baseline repetitiveInput nearCubic⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
