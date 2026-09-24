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
@[reducible] noncomputable def typeBBridgeSublinearRow :
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
    `Hypostructure.Graph.Strategy.Spine.typeBBridgeSublinear
    { Requires := [K .typeBBridgeMass, K .surplusAtOrBelow]
      Produces := [K .typeBBridgeSublinear]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let bridge := inputs.get (K .typeBBridgeMass)
      let nearCubic := inputs.get (K .surplusAtOrBelow)
      .cons (key := K .typeBBridgeSublinear)
        ⟨by
          intro packing valid ordinary grouped ordinaryInside groupedInside
            ordinaryComponents groupedComponents
          have atMostTwice := bridge.down.2.2 packing valid ordinary grouped
            ordinaryInside groupedInside ∅ ∅ (by simp) (by simp)
            (by
              intro piece pieceMem _pieceNotEmpty
              exact ordinaryComponents piece pieceMem)
            (by
              intro piece pieceMem _pieceNotEmpty
              exact groupedComponents piece pieceMem)
          simpa [Graph.TypeBEnvelopeCharge.route8Deficit] using atMostTwice,
          nearCubic.down⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
