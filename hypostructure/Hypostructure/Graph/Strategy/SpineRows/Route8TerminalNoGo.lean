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
@[reducible] noncomputable def route8TerminalNoGoRow
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
    `Hypostructure.Graph.Strategy.Spine.route8TerminalNoGo
    { Requires := [K .route8TrueResidual, K .route8NoSmallCoreEntry,
        K .route8CarrierDeletionWitnesses]
      Produces := [K .route8TerminalNoGo]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let trueResidual := inputs.get (K .route8TrueResidual)
      let noSmall := inputs.get (K .route8NoSmallCoreEntry)
      let witnessPackage := inputs.get (K .route8CarrierDeletionWitnesses)
      .cons (key := K .route8TerminalNoGo)
        ⟨by
          classical
          letI : DecidableEq inputs.current.object.Vertex :=
            inputs.current.object.vertices.decEq
          obtain ⟨index, indexMem, twoCarrier, deletionWitnesses⟩ :=
            witnessPackage.down
          rcases index with ⟨piece, receiver, load⟩
          let packing := canonicalWindowPacking data inputs.current.object
          let support := inputs.current.object.remainderSupport packing
          let routeEight :=
            (inputs.current.object.canonicalPieces support).filter
              (Route8Survives data inputs.current.object packing)
          have indexSpec :
              (piece, receiver, load) ∈
                  Graph.Route8Census.entriesOfComponents inputs.current.object
                    packing routeEight data.threshold data.dischargeScale ↔
                ∃ component ∈ routeEight,
                  piece = inputs.current.object.pieceSupport support component ∧
                    receiver ∈ Graph.VisibleEntry.saturatedReceivers
                      inputs.current.object piece data.threshold data.dischargeScale ∧
                    load ∈ Graph.VisibleEntry.excessBasin inputs.current.object piece
                      data.threshold data.dischargeScale receiver := by
            simp only [Graph.Route8Census.entriesOfComponents,
              Finset.mem_biUnion, Finset.mem_image, Prod.mk.injEq]
            constructor
            · rintro ⟨component, componentMem, receiver', receiverMem, load',
                loadMem, rfl, rfl, rfl⟩
              exact ⟨component, componentMem, rfl, receiverMem, loadMem⟩
            · rintro ⟨component, componentMem, pieceEq, receiverMem, loadMem⟩
              subst piece
              exact ⟨component, componentMem, receiver, receiverMem, load,
                loadMem, rfl, rfl, rfl⟩
          obtain ⟨component, componentMem, pieceEq, receiverMem, loadMem⟩ :=
            indexSpec.mp indexMem
          change piece = inputs.current.object.pieceSupport
            (inputs.current.object.remainderSupport
              (canonicalWindowPacking data inputs.current.object)) component at pieceEq
          subst piece
          let piece := inputs.current.object.pieceSupport support component
          let index : Graph.Route8Census.Index inputs.current.object :=
            (piece, receiver, load)
          let basin := Graph.Route8Census.basin inputs.current.object
            data.threshold index
          let presented := Graph.Route8Census.presented inputs.current.object
            data.threshold data.LengthOK index
          let entry := presented.toEntry
            (Graph.HasCycleWithLength data.LengthOK)
          have survives := (Finset.mem_filter.mp componentMem).2
          have trueFactsEarly := trueResidual.down.2 component componentMem
          have receiverFactsEarly := trueFactsEarly.2 receiver receiverMem
          have exactDegree : ∀ vertex ∈ inputs.current.object.pieceSupport
              support component,
              inputs.current.object.degree vertex = data.threshold := by
            intro vertex vertexMem
            have nonneg := le_trans inputs.current.baseline
              (inputs.current.object.minDegree_le_degree vertex)
            have summand : inputs.current.object.degree vertex -
                data.threshold = 0 :=
              Nat.eq_zero_of_le_zero
                (survives.2.1 ▸ Finset.single_le_sum
                  (f := fun other =>
                    inputs.current.object.degree other - data.threshold)
                  (fun _ _ => Nat.zero_le _) vertexMem)
            omega
          have silentLoadMem : load ∈ Graph.VisibleEntry.silentExcess
              inputs.current.object piece data.threshold data.dischargeScale
              receiver := by
            rw [Graph.VisibleEntry.silentExcess_eq_excessBasin
              inputs.current.object _ data.threshold data.dischargeScale
              (exactDegree receiver receiverFactsEarly.1.1)
              receiverFactsEarly.1 data.dischargeScale_pos
              (fun saturated =>
                trueFactsEarly.1 receiver receiverFactsEarly.1 saturated)]
            exact loadMem
          have notSmall := noSmall.down.2 component componentMem receiver
            receiverMem load silentLoadMem
          change ¬ entry.alpha ≤ 1 at notSmall
          have alphaAtLeast : 2 ≤ entry.alpha := by omega
          have coreNonempty : entry.essentialCore.Nonempty := by
            rw [Finset.nonempty_iff_ne_empty]
            intro empty
            have : entry.essentialCore.card = 0 := by rw [empty]; simp
            change 2 ≤ entry.essentialCore.card at alphaAtLeast
            omega
          obtain ⟨carrier, carrierMem⟩ := coreNonempty
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
          have trueFacts := trueResidual.down.2 component componentMem
          have receiverFacts := trueFacts.2 receiver receiverMem
          have entryFacts := receiverFacts.2.2 load silentLoadMem
          have selected := entryFacts.1
          have noExitFour := entryFacts.2.2
          have canonicalCollection : Graph.ExitFour.Q5CanonicalCollection
              inputs.current.object packing data.threshold data.dischargeScale
                (Graph.Route8Census.entriesOfComponents inputs.current.object
                  packing routeEight data.threshold data.dischargeScale) := by
            refine Or.inr ⟨routeEight, Finset.filter_subset _ _, ?_, rfl⟩
            intro candidate candidateMem
            have survives := (Finset.mem_filter.mp candidateMem).2
            exact ⟨survives.1, survives.2.1⟩
          have q5 : Graph.ExitFour.Q5TargetDefect
              (Graph.HasCycleWithLength data.LengthOK) piece data.threshold
                data.dischargeScale receiver load := by
            refine ⟨packing,
              Graph.Route8Census.entriesOfComponents inputs.current.object
                packing routeEight data.threshold data.dischargeScale,
              canonicalCollection, (piece, receiver, load), indexMem,
              rfl, rfl, rfl,
              data.LengthOK, rfl, selected, twoCarrier,
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
          change False
          exact noExitFour ⟨exitFour, rfl⟩⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
