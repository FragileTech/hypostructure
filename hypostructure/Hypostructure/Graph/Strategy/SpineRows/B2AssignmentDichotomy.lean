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

/-! ## Node `[72]`/`[81]`, second half: does the B2 disjoint ledger exist?

(B2) of `def:typeB-bridge-statements`.  With the local fan-window ledger complete
-- the direct configurations removed by the row above -- the question is whether
the assigned high-degree centres of the selected canonical Type B support admit
a *simultaneous* choice of candidate ledger entries with pairwise disjoint
carriers.  It is a global question: an entry
that pays at one centre may need a carrier another centre has already spent, so
no local count decides it.

Both arms are the manuscript's own mathematics rather than a proposition and its
negation.  The no arm is `lem:typeB-bridge-to-overlap`: a disjoint-carrier
failure is *represented* by a minimal Type B overlap obstruction, the smallest
failing subfamily of demands, which is the object node `[73]`/`[83]` hands to the
fan-mass accounting.  The yes arm records only the disjoint choice.  Its exact
B2(a)--(c) refinement is committed by the fact-only row below; B2(d) is not
claimed by either row.

This is a `Decision`, so the arm not taken is absent from the taken branch's key
index; the fan-mass row can no more read the ledger than the bridge-reduction row
can read the obstruction. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def b2AssignmentDichotomy
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
        (data := data)) (K .typeBDirectCycleFree) known]
    (choiceFresh : K .typeBB2Choice ∉ known)
    (obstructionFresh : K .typeBOverlapObstruction ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) current known
      (K .typeBB2Choice) (K .typeBOverlapObstruction) previous :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  Decision.run previous (K .typeBB2Choice) (K .typeBOverlapObstruction)
    `Hypostructure.Graph.Strategy.Spine.b2AssignmentDichotomy
    (by
      classical
      apply Classical.choice
      -- Read the surviving support from the direct-cycle-free fact itself.
      -- This both consumes the first half of `[81]` and prevents the B2 choice
      -- from silently selecting a different existential Type B support.
      rcases (ExactLedger.get previous (K .typeBDirectCycleFree)).down with
        canonical | absorbed | sameToken
      · obtain ⟨packing, valid, maximal, component, componentMem, centres,
          assigned, _directFree⟩ := canonical
        let canonicalPiece :
            Graph.TypeBRefinedSupport.CanonicalPiece current.object packing :=
          ⟨component, componentMem⟩
        have assigned' : TypeBAssignedCentres data current.object packing
            canonicalPiece.vertices centres := assigned
        rcases Graph.TypeBRefinedSupport.b2_or_overlap current.object
            data.threshold data.dischargeScale packing canonicalPiece.vertices
            centres (TypeBAssignedCentres.high data current.object assigned') with
          choice | obstruction
        · exact ⟨.inl ⟨.inl ⟨packing, valid, maximal, canonicalPiece, centres,
              assigned', choice⟩⟩⟩
        · exact ⟨.inr ⟨.inl ⟨packing, valid, maximal, canonicalPiece, centres,
              assigned', obstruction⟩⟩⟩
      · let packing := canonicalWindowPacking data current.object
        by_cases choices :
            ∀ (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
                  (Graph.MinimumDegreeAtLeast data.threshold)
                  (Graph.HasCycleWithLength data.LengthOK) current.object)
                (centre : current.object.Vertex),
              AbsorbedGermFanEnvelopeWitness data current.object germ centre →
                Graph.TypeBRefinedSupport.HasDisjointChoice current.object
                  data.threshold data.dischargeScale packing
                  germ.support {centre} {centre}
        · exact ⟨.inl ⟨Or.inr (Or.inl ⟨absorbed, choices⟩)⟩⟩
        · push Not at choices
          obtain ⟨germ, centre, witness, failure⟩ := choices
          have noChoice : ¬ Graph.TypeBRefinedSupport.HasDisjointChoice
              current.object data.threshold data.dischargeScale packing
              germ.support {centre} {centre} := failure
          rcases Graph.TypeBRefinedSupport.b2_or_overlap current.object
              data.threshold data.dischargeScale packing
              germ.support
              {centre} (by
                intro hub member
                rw [Finset.mem_singleton] at member
                subst hub
                rcases witness with ⟨routing, epsilon, germEq, firstIndex,
                  centreEq, indexLe, high, tail⟩
                exact high) with
            choice | obstruction
          · exact absurd choice noChoice
          · exact ⟨.inr ⟨Or.inr (Or.inl ⟨absorbed, germ, centre, witness,
                obstruction⟩)⟩⟩
      · obtain ⟨packing, valid, maximal, core, envelope, coreEq, nonempty,
            marked, directFree⟩ := sameToken
        rcases Graph.TypeBRefinedSupport.b2_or_overlap current.object
            data.threshold data.dischargeScale packing core
            envelope.decorations (fun centre member =>
              envelope.decorations_high centre member) with
          choice | obstruction
        · exact ⟨.inl ⟨Or.inr (Or.inr ⟨packing, valid, maximal, core,
              envelope, coreEq, nonempty, marked, directFree, choice⟩)⟩⟩
        · exact ⟨.inr ⟨Or.inr (Or.inr ⟨packing, valid, maximal, core,
              envelope, coreEq, nonempty, marked, directFree,
              obstruction⟩)⟩⟩)
    choiceFresh obstructionFresh

end Hypostructure.Graph.Strategy.Spine
