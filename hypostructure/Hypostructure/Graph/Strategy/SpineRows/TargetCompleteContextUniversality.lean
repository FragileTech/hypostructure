import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.SpineSelection

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

/-! ## Node `[12]`: context-universality for target-complete identifications

`lem:context-universality` (tex 6106), at G's own boundaried pieces.  The row
reads node `[11]` (`K .degreeProfileFibres`, the diagram's edge `[11] → [12]`):
an identification made by an admissible quotient of G's declared coordinates
stays in one boundary-degree fibre and has the same target response against
every boundaried context, so it is target-complete; and an identification valid
only at G's own outside context is target-defective.  Branch D's terminal
`[37]` closes against this fact. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def targetCompleteContextUniversalityRow :
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
    `Hypostructure.Graph.Strategy.Spine.targetCompleteContextUniversality
    { Requires := [K .degreeProfileFibres]
      Produces := [K .targetCompleteContextUniversality]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .targetCompleteContextUniversality)
        ⟨Contracts.Spine.targetCompleteContextUniversality_of_degreeProfileFibres
          data.toParameters inputs.current.object
          (inputs.get (K .degreeProfileFibres)).down⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
