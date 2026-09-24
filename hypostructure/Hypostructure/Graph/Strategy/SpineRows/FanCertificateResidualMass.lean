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
@[reducible] noncomputable def fanCertificateResidualMassRow :
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
    `Hypostructure.Graph.Strategy.Spine.fanCertificateResidualMass
    { Requires := [K .fanCertificateResidual]
      Produces := [K .fanCertificateResidualMass]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let residual := inputs.get (K .fanCertificateResidual)
      .cons (key := K .fanCertificateResidualMass) (by
        refine ⟨?_⟩
        rcases residual.down with support | absorbed | sameToken
        · obtain ⟨packing, valid, maximal, component, componentMem, centres, assigned,
            centre, centreMem, high, empty⟩ := support
          exact .inl ⟨packing, valid, maximal, component, componentMem, centres,
            assigned, centre, centreMem, high, empty, fun envelope =>
              Graph.TypeBEnvelopeCharge.envelopeNegativePart_le envelope high
                data.bridgeMassSlack⟩
        · obtain ⟨envelopes, germ, centre, witness, empty⟩ := absorbed
          have high : Graph.IsHighCentre inputs.current.object
              data.threshold centre := by
            rcases witness with ⟨routing, epsilon, germEq, firstIndex,
              centreEq, indexLe, high, tail⟩
            exact high
          exact .inr (.inl ⟨envelopes, germ, centre, witness, empty,
            fun envelope =>
              Graph.TypeBEnvelopeCharge.envelopeNegativePart_le envelope
                high data.bridgeMassSlack⟩)
        · obtain ⟨packing, valid, maximal, core, handoff, coreEq, nonempty,
              centre, member, high, empty⟩ := sameToken
          exact .inr (.inr ⟨packing, valid, maximal, core, handoff, coreEq,
            nonempty, centre, member, high, empty, fun envelope =>
              Graph.TypeBEnvelopeCharge.envelopeNegativePart_le envelope high
                data.bridgeMassSlack⟩))
      .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
