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

`lem:context-universality` (tex 6106), stated about G.  The row reads node
`[11]` (`K .degreeProfileFibres`, the diagram's edge `[11] → [12]`) and the
selection (`K .selection`): two readings an admissible quotient of G's declared
coordinates identifies stay in one boundary-degree fibre and agree in G's own
rest `G − Z`; and no reading of G closes a power-of-two cycle in `G − Z` (a
subgraph of G), so no context of G separates two readings.  This decided fact
routes G at `[36]`: Branch D's terminal `[37]` closes against it (Lean
improvement: `[36]`'s defect arm is empty at G). -/
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
    { Requires := [K .degreeProfileFibres, K .selection]
      Produces := [K .targetCompleteContextUniversality]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .targetCompleteContextUniversality)
        ⟨Contracts.Spine.targetCompleteContextUniversality_of_degreeProfileFibres
          data.toParameters inputs.current.object
          (inputs.get (K .degreeProfileFibres)).down
          (inputs.get (K .selection)).down⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
