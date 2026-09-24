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

@[reducible] noncomputable def highCentreNormalFormRow
    : @AtomicStrategy (Input BranchState Presentation presentation data) _
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
    `Hypostructure.Graph.Strategy.Spine.highCentreNormalForm
    { Requires := [K .selection, K .tightEndpoint]
      Produces := [K .highCentreNormalForm]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let tight := (inputs.get (K .tightEndpoint)).down
      let avoids := (inputs.get (K .selection)).down.1
      .cons (key := K .highCentreNormalForm)
        ⟨fun centre high =>
          { neighbourTight := by
              intro x adjacent
              rcases tight ⟨(centre, x), adjacent⟩ with centreTight | endpointTight
              · exact absurd centreTight (Nat.ne_of_gt high)
              · exact endpointTight
            inducedMatching := by
              intro x y z centreX centreY centreZ distinct xy yz
              exact Graph.not_quadrilateral avoids data.quadrilateralAccepted
                centreX xy yz centreZ.symm centreY.ne distinct
            noCommonNeighbourOutside := by
              intro x y z centreX centreY distinct _nonadjacent outside xz yz
              exact Graph.not_quadrilateral avoids data.quadrilateralAccepted
                centreX xz yz.symm centreY.symm (Ne.symm outside) distinct }⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
