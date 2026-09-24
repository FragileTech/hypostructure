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
@[reducible] noncomputable def typeBOverlapObstructionMassRow :
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
    `Hypostructure.Graph.Strategy.Spine.typeBOverlapObstructionMass
    { Requires := [K .typeBGlobalLocalBridge]
      Produces := [K .typeBOverlapObstructionMass]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let residual := inputs.get (K .typeBGlobalLocalBridge)
      .cons (key := K .typeBOverlapObstructionMass) (by
        refine ⟨?_⟩
        rcases residual.down with support | absorbed | sameToken
        · obtain ⟨packing, valid, maximal, canonicalPiece, centres, assigned,
            obstruction⟩ := support
          obtain ⟨obstruction, _reflection⟩ := obstruction
          exact Or.inl ⟨packing, valid, maximal, canonicalPiece, centres, assigned,
            ⟨obstruction⟩, fun centre member envelope =>
              Graph.TypeBEnvelopeCharge.envelopeNegativePart_le envelope
                (TypeBAssignedCentres.high data inputs.current.object assigned
                  centre member)
                data.bridgeMassSlack⟩
        · obtain ⟨directFree, germ, centre, witness, obstruction⟩ := absorbed
          have high : Graph.IsHighCentre inputs.current.object
              data.threshold centre := by
            rcases witness with ⟨routing, epsilon, germEq, firstIndex,
              centreEq, indexLe, high, tail⟩
            exact high
          exact .inr (.inl ⟨directFree, germ, centre, witness, obstruction,
            fun envelope =>
              Graph.TypeBEnvelopeCharge.envelopeNegativePart_le envelope
                high data.bridgeMassSlack⟩)
        · obtain ⟨packing, valid, maximal, core, envelope, coreEq, nonempty,
              marked, directFree, obstruction⟩ := sameToken
          exact .inr (.inr ⟨packing, valid, maximal, core, envelope, coreEq,
            nonempty, marked, directFree, obstruction,
            fun centre member localEnvelope =>
              Graph.TypeBEnvelopeCharge.envelopeNegativePart_le localEnvelope
                (envelope.decorations_high centre member)
                data.bridgeMassSlack⟩))
      .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
