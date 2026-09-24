import Hypostructure.Graph.Strategy.SpineVocabulary

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

omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def sameCenterOpenPortCompatibilityRow :
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
    `Hypostructure.Graph.Strategy.Spine.sameCenterOpenPortCompatibility
    { Requires := [K .highCentreNormalForm]
      Produces := [K .sameCenterOpenPortCompatibility]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let normal := (inputs.get (K .highCentreNormalForm)).down
      .cons (key := K .sameCenterOpenPortCompatibility)
        (show Value BranchState Presentation presentation data
            .sameCenterOpenPortCompatibility inputs.current from
          ⟨by
            intro centre high left right centreLeft centreRight distinct nonadjacent
              leftOpen rightOpen
            exact Graph.fanCompatible_of_endpoints_nonadjacent
              (normal centre high) centreLeft centreRight distinct nonadjacent
                leftOpen rightOpen⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
