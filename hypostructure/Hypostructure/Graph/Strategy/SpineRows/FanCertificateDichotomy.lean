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

/-! ## Node `[71]`/`[80]`: is a certificate labelling present?

`def:marked-typeB-fan`.  A Type B fan is *certificate-marked* when the
fan-certificate labelling is part of the assigned support data; a high-degree
centre assigned to a Type B support but not certificate-marked is a
*fan-certificate residual center*, which is charged to the Type B
bridge-residual mass of `def:typeB-residual-mass` and takes no part in the
certificate-closed local discharging step.

The question is therefore scoped to the centres of the literal Type B carrier,
not to the object's high centres at large: either the assigned centres of the
canonical support or the actual centres indexed by the absorbed corridor
witness.  A high centre in neither carrier is not a residual centre and carries
no bridge mass.

The split is taken on the carrier's certificate proposition.  The marked arm
retains an actual labelling and `[70]`'s cap at each applicable centre; the
other arm extracts an actual applicable centre with no labelling.  This is a
`Decision`, so the arm not taken is absent from the taken branch's key index. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def fanCertificateDichotomy
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
        (data := data)) (K .fanCertificateCap) known]
    (markedFresh : K .fanCertificateMarked ∉ known)
    (residualFresh : K .fanCertificateResidual ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) current known
      (K .fanCertificateMarked) (K .fanCertificateResidual) previous :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  Decision.run previous (K .fanCertificateMarked) (K .fanCertificateResidual)
    `Hypostructure.Graph.Strategy.Spine.fanCertificateDichotomy
    (by
      classical
      apply Classical.choice
      rcases (ExactLedger.get previous (K .fanCertificateCap)).down with
        support | absorbed | sameToken
      · obtain ⟨packing, valid, maximal, component, present, centres, assigned,
          cap⟩ := support
        by_cases marked :
            ∀ centre ∈ centres,
              Nonempty (Graph.FanCertificateLabelling current.object
                data.windowOrder centre)
        · exact ⟨.inl ⟨.inl ⟨packing, valid, maximal, component, present, centres,
            assigned, fun centre member => by
              obtain ⟨marking⟩ := marked centre member
              exact ⟨marking, cap centre member marking⟩⟩⟩⟩
        · -- Not every assigned centre is marked, so one of them is a
          -- fan-certificate residual centre.
          push Not at marked
          obtain ⟨centre, member, unmarked⟩ := marked
          exact ⟨.inr ⟨.inl ⟨packing, valid, maximal, component, present, centres,
            assigned, centre, member,
            TypeBAssignedCentres.high data current.object assigned centre member,
            unmarked⟩⟩⟩
      · obtain ⟨envelopes, cap⟩ := absorbed
        by_cases marked :
            ∀ (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
                  (Graph.MinimumDegreeAtLeast data.threshold)
                  (Graph.HasCycleWithLength data.LengthOK) current.object)
                (centre : current.object.Vertex),
              AbsorbedGermFanEnvelopeWitness data current.object germ centre →
                Nonempty (Graph.FanCertificateLabelling current.object
                  data.windowOrder centre)
        · exact ⟨.inl ⟨Or.inr (Or.inl ⟨envelopes,
            fun germ centre witness => by
              obtain ⟨marking⟩ := marked germ centre witness
              exact ⟨marking,
                cap germ centre witness marking⟩⟩)⟩⟩
        · push Not at marked
          obtain ⟨germ, centre, witness, unmarked⟩ := marked
          exact ⟨.inr ⟨Or.inr (Or.inl ⟨envelopes, germ, centre, witness,
            unmarked⟩)⟩⟩
      · obtain ⟨packing, valid, maximal, core, envelope, coreEq, nonempty,
          cap⟩ := sameToken
        by_cases marked :
            ∀ centre ∈ envelope.decorations,
              Nonempty (Graph.FanCertificateLabelling current.object
                data.windowOrder centre)
        · exact ⟨.inl ⟨Or.inr (Or.inr ⟨packing, valid, maximal, core,
            envelope, coreEq, nonempty, fun centre member => by
              obtain ⟨marking⟩ := marked centre member
              exact ⟨marking, cap centre member marking⟩⟩)⟩⟩
        · push Not at marked
          obtain ⟨centre, member, unmarked⟩ := marked
          exact ⟨.inr ⟨Or.inr (Or.inr ⟨packing, valid, maximal, core,
            envelope, coreEq, nonempty, centre, member,
            envelope.decorations_high centre member, unmarked⟩)⟩⟩)
    markedFresh residualFresh

end Hypostructure.Graph.Strategy.Spine
