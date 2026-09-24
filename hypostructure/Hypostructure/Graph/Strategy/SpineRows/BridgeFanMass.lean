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

/-! ## Nodes `[73]`/`[75]` and `[83]`/`[84]`: Type B bridge fan mass

The three incoming residual forms have already published their branch-specific
mass facts.  The bridge estimate itself is the manuscript's object-level
summation theorem proved from `inputs.current.object` and appended to that
literal residual ledger. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def bridgeFanMassRow :
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
    `Hypostructure.Graph.Strategy.Spine.typeBBridgeMass
    { Requires := []
      Produces := [K .typeBBridgeMass]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBBridgeMass) ⟨by
        have baseline : ∀ vertex : inputs.current.object.Vertex,
            data.threshold ≤ inputs.current.object.degree vertex := fun vertex =>
          le_trans inputs.current.baseline
            (inputs.current.object.minDegree_le_degree vertex)
        refine ⟨?_, ?_, ?_⟩
        · intro _packing _valid piece _inside _connected _charge _positive
          refine ⟨fun centre _member high envelope => ?_, fun component => ?_⟩
          · exact Graph.TypeBEnvelopeCharge.envelopeNegativePart_le _ high
              data.bridgeMassSlack
          · exact Graph.TypeBEnvelopeCharge.bridgeDeficitBound
              inputs.current.object piece data.bridgeMassSlack baseline
              component.1 component.2
        · intro packing _valid route8 route8Surplus components
          exact Graph.TypeBEnvelopeCharge.bridgeResidualMass_le_route8
            inputs.current.object _ route8 data.bridgeMassSlack baseline
            route8Surplus components
        · intro _packing _valid ordinary grouped _ordinaryInside _groupedInside
            ordinaryRoute8 groupedRoute8
            ordinarySurplus groupedSurplus ordinaryComponents groupedComponents
          exact Graph.TypeBEnvelopeCharge.bridgeResidualMass_le_twice
            inputs.current.object ordinary grouped ordinaryRoute8 groupedRoute8
            data.bridgeMassSlack baseline ordinarySurplus groupedSurplus
            ordinaryComponents groupedComponents⟩
      .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
