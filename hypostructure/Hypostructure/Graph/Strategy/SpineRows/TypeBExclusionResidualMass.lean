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
@[reducible] noncomputable def typeBExclusionResidualMassRow :
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
    `Hypostructure.Graph.Strategy.Spine.typeBExclusionResidualMass
    { Requires := [K .typeBExclusionResidual]
      Produces := [K .typeBExclusionResidualMass]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let residual := inputs.get (K .typeBExclusionResidual)
      .cons (key := K .typeBExclusionResidualMass) (by
        classical
        refine ⟨?_⟩
        obtain ⟨packing, packingValid, packingMaximal, canonicalPiece,
          centres, assigned, ledger, exact, _postLedger, negative⟩ := residual.down
        exact ⟨packing, packingValid, packingMaximal, canonicalPiece,
          centres, assigned, ledger, exact, negative,
          fun centre member envelope =>
            Graph.TypeBEnvelopeCharge.envelopeNegativePart_le envelope
              (TypeBAssignedCentres.high data inputs.current.object assigned
                centre member)
              data.bridgeMassSlack⟩)
      .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
