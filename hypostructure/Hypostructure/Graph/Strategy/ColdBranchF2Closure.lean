import Hypostructure.Graph.Strategy.ColdBranchFailureRouting


namespace Hypostructure.Graph.Strategy.ColdBranchF2Closure

open Hypostructure
open Hypostructure.Core.Finite
open Hypostructure.Graph.InducedPathCold

universe u uPrevious

set_option maxHeartbeats 1000000

variable {object : FiniteObject.{u}} {order : Nat}

/-! ## The stored (F2) hit -/

/-- Consumes `Graph.InducedPathCold.f2CandidateOfHit_valid`, applied to the
stored event exactly as `f2BookkeepingOfStoredEvent` does.  The returned
validity is the one recorded by the stored hit; no candidate schedule is
scanned again. -/
theorem storedF2EventValid
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex)
    (event : Core.Finite.ColdCorridor.Contract.EventWitness
      (canonicalFirstFailurePresentation occurrence member CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport).coreContract
      .f2) :
    F2Valid occurrence member Target decideTarget event.item
      (f2CandidateOfHit occurrence member Target decideTarget event.item
        ((canonicalFirstFailurePresentation_f2Hit occurrence member
          CycleLengthOK cycleLengthDecidable Target decideTarget
          handoffItems handoffSupport event.item).mp event.sound)) := by
  let hit := (canonicalFirstFailurePresentation_f2Hit occurrence member
    CycleLengthOK cycleLengthDecidable Target decideTarget handoffItems handoffSupport
    event.item).mp event.sound
  exact f2CandidateOfHit_valid occurrence member Target decideTarget event.item
    hit

theorem storedF2Defect
    {Previous : Type uPrevious}
    {profile : InducedPathMaximalPacking.Profile object order}
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (decideTarget : ∀ candidate,
      Decidable (Graph.HasCycleWithLength CycleLengthOK candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex)
    (stage : (canonicalFamilyProducer profile CycleLengthOK cycleLengthDecidable
      (Graph.HasCycleWithLength CycleLengthOK) decideTarget
      handoffItems handoffSupport).ClassifiedStateStage Previous)
    (owner :
      let family := canonicalFamilyProducer profile CycleLengthOK
        cycleLengthDecidable (Graph.HasCycleWithLength CycleLengthOK)
        decideTarget handoffItems handoffSupport
      family.FailureOwner (family.storedClassificationQuery.read stage) .f2) :
    let event := ColdBranchFailureRouting.storedF2Event profile CycleLengthOK
      cycleLengthDecidable (Graph.HasCycleWithLength CycleLengthOK) decideTarget
      handoffItems handoffSupport stage owner
    let hit := (canonicalFirstFailurePresentation_f2Hit owner.1.1.1.1
      owner.1.1.1.2 CycleLengthOK cycleLengthDecidable
      (Graph.HasCycleWithLength CycleLengthOK) decideTarget handoffItems handoffSupport
      event.item).mp event.sound
    let candidate := f2CandidateOfHit owner.1.1.1.1 owner.1.1.1.2
      (Graph.HasCycleWithLength CycleLengthOK) decideTarget event.item hit
    F2TargetDefect owner.1.1.1.1 owner.1.1.1.2
      (Graph.HasCycleWithLength CycleLengthOK) candidate event.item := by
  dsimp only
  exact (storedF2EventValid owner.1.1.1.1 owner.1.1.1.2 CycleLengthOK
    cycleLengthDecidable (Graph.HasCycleWithLength CycleLengthOK) decideTarget
    handoffItems handoffSupport _).2.2

/-! ## (G2) CT7's distinguishing terminal -/

theorem canonicalF5G2Target
    {Previous : Type uPrevious}
    {profile : InducedPathMaximalPacking.Profile object order}
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (decideTarget : ∀ candidate,
      Decidable (Graph.HasCycleWithLength CycleLengthOK candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex)
    (view : Core.Residual.Focus.ActiveView
      (canonicalF5Focus (Previous := Previous) profile CycleLengthOK
        cycleLengthDecidable (Graph.HasCycleWithLength CycleLengthOK)
        decideTarget handoffItems handoffSupport))
    (residual : _root_.Hypostructure.CT7.DistinguishingResidual
      (canonicalF5CT7Capability (Previous := Previous) profile CycleLengthOK
        cycleLengthDecidable (Graph.HasCycleWithLength CycleLengthOK)
        decideTarget handoffItems handoffSupport) view) :
    Graph.HasCycleWithLength CycleLengthOK object := by
  let representatives : Core.Response.Representatives
      (CanonicalColdRepresentative profile) :=
    (canonicalF5CT7Capability (Previous := Previous) profile CycleLengthOK
      cycleLengthDecidable (Graph.HasCycleWithLength CycleLengthOK)
      decideTarget handoffItems handoffSupport).representativesAt view
  let owner := residual.context.1
  -- The germ of this owner: `def:cold-bounded-germ`'s bounded support, whose
  -- carried target-response profile is what CT7 observed.  Every step below is
  -- a framework call on that one germ.
  have transport : ∀ stage : ReturnStage owner.1.1.1 owner.1.1.2,
      germTargetResponse owner.1.1.1 owner.1.1.2
          (Graph.HasCycleWithLength CycleLengthOK) decideTarget stage = true →
        Graph.HasCycleWithLength CycleLengthOK object := by
    intro stage realized
    have cycled : Graph.HasCycleWithLength CycleLengthOK
        (germCompletion owner.1.1.1 owner.1.1.2 stage) := by
      have decided := realized
      unfold germTargetResponse at decided
      exact of_decide_eq_true decided
    rcases cycled with ⟨certificate⟩
    let support : Finset object.Vertex :=
      (returnPrefixSupport owner.1.1.1 owner.1.1.2 stage).toFinset
    exact ⟨certificate.mapHom (object.induceEmbedding support).toHom
      (object.induceEmbedding support).injective⟩
  have different :
      germTargetResponse owner.1.1.1 owner.1.1.2
          (Graph.HasCycleWithLength CycleLengthOK) decideTarget
          (representatives.source owner) ≠
        germTargetResponse owner.1.1.1 owner.1.1.2
          (Graph.HasCycleWithLength CycleLengthOK) decideTarget
          (representatives.replacement owner) := by
    simpa [representatives, owner, canonicalF5CT7Spec,
      canonicalF5ResponseSystem, Core.Response.System.ofDecodedContexts] using
        residual.contextDiffers
  rcases Bool.eq_false_or_eq_true
      (germTargetResponse owner.1.1.1 owner.1.1.2
        (Graph.HasCycleWithLength CycleLengthOK) decideTarget
        (representatives.source owner)) with sourceTrue | sourceFalse
  · exact transport _ sourceTrue
  · rcases Bool.eq_false_or_eq_true
        (germTargetResponse owner.1.1.1 owner.1.1.2
          (Graph.HasCycleWithLength CycleLengthOK) decideTarget
          (representatives.replacement owner)) with
      replacementTrue | replacementFalse
    · exact transport _ replacementTrue
    · exact absurd (sourceFalse.trans replacementFalse.symm) different

end Hypostructure.Graph.Strategy.ColdBranchF2Closure
