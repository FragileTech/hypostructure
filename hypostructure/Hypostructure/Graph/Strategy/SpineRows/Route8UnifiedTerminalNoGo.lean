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

/-! ## Node `[124]`: terminal unified two-support route-8 exclusion

The selected unified entry is already target-complete-minimal, has at least two
essential incidences, has at most two private incidences, and has no canonical
exit-(4) witness.  The executor constructs the deletion witnesses of every
essential incidence and the exact Q5 census datum locally, then obtains the
forbidden exit-(4) witness.  No proof object is transported beside the ledger. -/
set_option maxHeartbeats 1000000 in
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def route8UnifiedTerminalNoGoRow
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
    `Hypostructure.Graph.Strategy.Spine.route8UnifiedTerminalNoGo
    { Requires := [K .route8UnifiedTrueTwoCarrierEntry]
      Produces := [K .route8TerminalNoGo]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let trueEntry := inputs.get (K .route8UnifiedTrueTwoCarrierEntry)
      .cons (key := K .route8TerminalNoGo)
        ⟨by
          classical
          letI : DecidableEq inputs.current.object.Vertex :=
            Graph.Route8.vertexDecEq inputs.current.object
          obtain ⟨index, indexMem, twoCarrier, entryFacts, _minimal,
            noExitFour⟩ := Classical.choice trueEntry.down
          have selected := entryFacts.1
          have alphaAtLeast := entryFacts.2.1
          rcases index with ⟨piece, receiver, load⟩
          let packing := canonicalWindowPacking data inputs.current.object
          let support := inputs.current.object.remainderSupport packing
          let components := route8UnifiedComponents data inputs.current.object
          let entries := route8UnifiedEntries data inputs.current.object
          let index : Graph.Route8Census.Index inputs.current.object :=
            (piece, receiver, load)
          let basin := Graph.Route8Census.basin inputs.current.object
            data.threshold index
          let presented := Graph.Route8Census.presented inputs.current.object
            data.threshold data.LengthOK index
          let entry := presented.toEntry
            (Graph.HasCycleWithLength data.LengthOK)
          have broadIndexMem : (piece, receiver, load) ∈
              Graph.Route8Census.entries inputs.current.object packing
                data.threshold data.dischargeScale := by
            simp only [route8UnifiedEntries,
              Graph.Route8Census.entriesOfComponents, Finset.mem_biUnion,
              Finset.mem_image, Prod.mk.injEq] at indexMem
            obtain ⟨component, componentMem, receiver', receiverMem, load', loadMem,
              pieceEq, receiverEq, loadEq⟩ := indexMem
            subst piece
            subst receiver
            subst load
            apply (Graph.Route8Census.mem_entries inputs.current.object).2
            refine ⟨?_, (Finset.mem_filter.1 receiverMem).1, loadMem⟩
            simp only [Graph.Route8Census.typeAPieces, Finset.mem_filter,
              Finset.mem_image]
            have selected := (Finset.mem_filter.1 componentMem).2
            exact ⟨⟨component, (Finset.mem_filter.1 componentMem).1, rfl⟩,
              selected.2.1, selected.1⟩
          have entrySpec := (Graph.Route8Census.mem_entries
            inputs.current.object).mp broadIndexMem
          have loadMem := entrySpec.2.2
          change 2 ≤ entry.alpha at alphaAtLeast
          have coreNonempty : entry.essentialCore.Nonempty := by
            rw [Finset.nonempty_iff_ne_empty]
            intro empty
            have zero : entry.essentialCore.card = 0 := by rw [empty]; simp
            change 2 ≤ entry.essentialCore.card at alphaAtLeast
            omega
          obtain ⟨carrier, carrierMem⟩ := coreNonempty
          have deletionWitnesses := Graph.Route8.twoCarrierDeletionWitnesses
            (Target := Graph.HasCycleWithLength data.LengthOK) entry.carriers
            entry.coordinates entry.car entry.car_subset entry.state entries
            (Graph.Route8Census.core inputs.current.object data.threshold
              data.LengthOK) twoCarrier rfl
          obtain ⟨targetDefect, coordinate, coordinateMem, coordinateCore,
            carrierCoordinate⟩ := deletionWitnesses.2 carrier carrierMem
          have loadRouted : load ∈ inputs.current.object.routedLoads piece
              data.threshold receiver := (Finset.mem_sdiff.mp loadMem).1
          have unpeeled : load ∈ Graph.ExitFour.unpeeledLoads piece
              data.threshold receiver ∅ := by
            rw [Graph.ExitFour.mem_unpeeledLoads]
            exact ⟨loadRouted, by simp⟩
          have sameBoundaryProfile :
              (entry.restriction (entry.essentialCore.erase carrier)).boundaryDegreeProfile =
                (entry.restriction entry.essentialCore).boundaryDegreeProfile := by
            change (presented.state
                (entry.retained (entry.essentialCore.erase carrier))).boundaryDegreeProfile =
              (presented.state
                (entry.retained entry.essentialCore)).boundaryDegreeProfile
            exact Graph.Route8.PresentedEntry.ofTraceBasin_boundaryDegreeProfile
              inputs.current.object piece basin data.threshold data.LengthOK
                receiver load _ _
          have q5 : Graph.ExitFour.Q5TargetDefect
              (Graph.HasCycleWithLength data.LengthOK) piece data.threshold
                data.dischargeScale receiver load := by
            have canonicalCollection : Graph.ExitFour.Q5CanonicalCollection
                inputs.current.object packing data.threshold data.dischargeScale
                  entries := by
              refine Or.inr ⟨components, ?_, ?_, rfl⟩
              · intro component componentMem
                exact (Finset.mem_filter.mp componentMem).1
              · intro component componentMem
                have selectedComponent :=
                  (Finset.mem_filter.mp componentMem).2
                exact ⟨selectedComponent.2.1, selectedComponent.1⟩
            refine ⟨packing, entries, canonicalCollection,
              (piece, receiver, load), indexMem,
              rfl, rfl, rfl, data.LengthOK, rfl, selected, twoCarrier,
              carrier, carrierMem, ?_, ?_, ?_⟩
            · change Graph.Response.TargetDefect
                (Graph.HasCycleWithLength data.LengthOK)
                (entry.restriction (entry.essentialCore.erase carrier))
                (entry.restriction entry.essentialCore)
              exact targetDefect
            · change
                (entry.restriction
                    (entry.essentialCore.erase carrier)).boundaryDegreeProfile =
                  (entry.restriction
                    entry.essentialCore).boundaryDegreeProfile
              exact sameBoundaryProfile
            · refine ⟨coordinate, ?_, ?_, carrierCoordinate⟩
              · change coordinate ∈ entry.coordinates
                exact coordinateMem
              · change entry.car coordinate ⊆ entry.essentialCore
                exact coordinateCore
          let exitFour := Graph.ExitFour.Witness.ofCarrierDeletion unpeeled q5
          exact noExitFour ⟨exitFour, rfl⟩⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
