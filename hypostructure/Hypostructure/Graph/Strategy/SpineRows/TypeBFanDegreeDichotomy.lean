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
noncomputable def typeBFanDegreeDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data))}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data) _
        (instFactSystem (BranchState := BranchState)
          (Presentation := Presentation) (presentation := presentation)
          (data := data)) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) (K .typeBFanEntry) known]
    (heavyFresh : K .typeBFanHeavyCentre ∉ known)
    (degreeFourFresh : K .typeBFanDegreeFourCentres ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) current known
      (K .typeBFanHeavyCentre) (K .typeBFanDegreeFourCentres) previous :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  Decision.run previous (K .typeBFanHeavyCentre) (K .typeBFanDegreeFourCentres)
    `Hypostructure.Graph.Strategy.Spine.typeBFanDegreeDichotomy
    (by
      classical
      apply Classical.choice
      have entry := (ExactLedger.get previous (K .typeBFanEntry)).down
      change TypeBFanEntryStatement data current.object at entry
      rcases entry with canonical | absorbed | sameToken
      · obtain ⟨packing, valid, maximal, component, present, centres, assigned,
          _nonempty, high⟩ := canonical
        by_cases heavy :
            ∃ centre ∈ centres, data.threshold + 1 < current.object.degree centre
        · exact ⟨.inl ⟨Or.inl ⟨packing, valid, maximal, component, present,
              centres, assigned, heavy⟩⟩⟩
        · refine ⟨.inr ⟨Or.inl ⟨packing, valid, maximal, component, present,
              centres, assigned, ?_⟩⟩⟩
          intro centre member
          have lower := high centre member
          have upper : ¬ data.threshold + 1 < current.object.degree centre :=
            fun above => heavy ⟨centre, member, above⟩
          simp only [Graph.IsHighCentre] at lower
          omega
      · by_cases heavy :
            ∃ (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
                  (Graph.MinimumDegreeAtLeast data.threshold)
                  (Graph.HasCycleWithLength data.LengthOK) current.object)
                (centre : current.object.Vertex),
              AbsorbedGermFanEnvelopeWitness data current.object germ centre ∧
                data.threshold + 1 < current.object.degree centre
        · exact ⟨.inl ⟨Or.inr (Or.inl ⟨absorbed, heavy⟩)⟩⟩
        · refine ⟨.inr ⟨Or.inr (Or.inl ⟨absorbed, ?_⟩)⟩⟩
          intro germ centre witness
          have lower : data.threshold < current.object.degree centre :=
            by
              rcases witness with ⟨routing, epsilon, germEq, firstIndex,
                centreEq, indexLe, high, tail⟩
              exact high
          have upper : ¬ data.threshold + 1 < current.object.degree centre := by
            intro above
            exact heavy ⟨germ, centre, witness, above⟩
          omega
      · obtain ⟨packing, valid, maximal, core, envelope, coreEq, nonempty⟩ :=
          sameToken
        by_cases heavy :
            ∃ centre ∈ envelope.decorations,
              data.threshold + 1 < current.object.degree centre
        · exact ⟨.inl ⟨Or.inr (Or.inr ⟨packing, valid, maximal, core,
              envelope, coreEq, nonempty, heavy⟩)⟩⟩
        · refine ⟨.inr ⟨Or.inr (Or.inr ⟨packing, valid, maximal, core,
              envelope, coreEq, nonempty, ?_⟩)⟩⟩
          intro centre member
          have lower : data.threshold < current.object.degree centre := by
            exact envelope.decorations_high centre member
          have upper : ¬ data.threshold + 1 < current.object.degree centre := by
            intro above
            exact heavy ⟨centre, member, above⟩
          omega)
    heavyFresh degreeFourFresh

end Hypostructure.Graph.Strategy.Spine
