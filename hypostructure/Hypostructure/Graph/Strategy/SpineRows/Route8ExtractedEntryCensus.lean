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

/-! ## `def:typeA-unified-entries` with `lem:typeA-unified-carriers` at the
extracted route-8 cores (node `[123]`)

The same per-entry census, at the entries of the route-8 non-window cores
extracted from the Type B bridge pieces (`lem:typeB-bridge-with-route8-core`'s
`𝒜_X`; the appendix rows for `[74]`/`[76]`/`[85]`: "after any route-8
non-window core is extracted into `D_A`").  A core is a canonical connected
component of the deleted region `X ∖ centres(X)` of a negative
positive-surplus canonical piece, so its basins and coordinates live at a
connected support; the collection's own filter carries
`def:typeA-unified-negative`'s clauses — alternative (d) is refuted through the
envelope bridge against the filter's no-handoff clause exactly as at the
unified collection, and alternative (b), cased at `[104]` for the unified
entries, is definitionally absent from an extracted core (a profile-record
component is not a route-8 core) — while (c) is refuted through
`not_traceDelocalization` against `K .replacementExclusion` and the selection's
minimality, and `lem:typeA-unified-carriers`' bound `α(ξ) ≥ 2` holds on both
arms through `lem:typeA-carrier-cut-parity` and
`lem:typeA-one-terminal-collapse`'s collapse engine. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
set_option maxHeartbeats 1600000 in
@[reducible] noncomputable def route8ExtractedEntryCensusRow :
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
    `Hypostructure.Graph.Strategy.Spine.route8ExtractedEntryCensus
    { Requires := [K .selection, K .replacementExclusion, K .cubicBaseline]
      Produces := [K .route8ExtractedEntryCensus]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let selection := (inputs.get (K .selection)).down
      let exclusion := (inputs.get (K .replacementExclusion)).down
      let cubic := (inputs.get (K .cubicBaseline)).down.1
      .cons (key := K .route8ExtractedEntryCensus)
        (⟨by
          classical
          letI : DecidableEq inputs.current.object.Vertex :=
            inputs.current.object.vertices.decEq
          intro index indexMem
          rcases index with ⟨piece, receiver, load⟩
          have indexSpec :
              (piece, receiver, load) ∈
                  route8ExtractedEntries data inputs.current.object ↔
                ∃ core ∈ route8ExtractedCores data inputs.current.object,
                  piece = core ∧
                    receiver ∈ inputs.current.object.receivers core
                      data.threshold ∧
                    load ∈ Graph.VisibleEntry.excessBasinReduced
                      inputs.current.object core data.threshold
                      data.dischargeScale receiver ∅ := by
            simp only [route8ExtractedEntries, Finset.mem_biUnion,
              Finset.mem_image, Prod.mk.injEq]
            constructor
            · rintro ⟨core, coreMem, receiver', receiverMem, load', loadMem,
                rfl, rfl, rfl⟩
              exact ⟨core, coreMem, rfl, receiverMem, loadMem⟩
            · rintro ⟨core, coreMem, pieceEq, receiverMem, loadMem⟩
              subst pieceEq
              exact ⟨piece, coreMem, receiver, receiverMem, load, loadMem, rfl,
                rfl, rfl⟩
          obtain ⟨core, coreMem, pieceEq, receiverMem, loadMem⟩ :=
            indexSpec.mp indexMem
          subst pieceEq
          obtain ⟨_bridge, _bridgeMem, coreSpec⟩ :=
            Finset.mem_biUnion.mp coreMem
          have coreFilter := Finset.mem_filter.mp coreSpec
          have noHandoff := coreFilter.2.2.2.1
          have quotientFreeCore := coreFilter.2.2.2.2
          obtain ⟨component, componentMem, componentEq⟩ :=
            Finset.mem_image.mp coreFilter.1
          have connected : Graph.SupportComponents.Connected.ConnectedOn
              inputs.current.object piece := by
            rw [← componentEq]
            exact Graph.SupportComponents.Connected.connectedOn_of_mem_order
              inputs.current.object _
              ((Graph.FiniteObject.mem_canonicalPieces _ _).1 componentMem)
          have loadRouted : load ∈ inputs.current.object.routedLoads piece
              data.threshold receiver :=
            (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp loadMem).1).1
          obtain ⟨basin₀, selectedEq⟩ :=
            Graph.Route8.TraceBasin.exists_select?_eq_some_of_mem_routedLoads
              inputs.current.object piece data.threshold connected loadRouted
          have basinEq : Graph.Route8Census.basin inputs.current.object
              data.threshold (piece, receiver, load) = basin₀ := by
            rw [Graph.Route8Census.basin, selectedEq]
            rfl
          have selectedCensus : Graph.Route8.TraceBasin.select?
              inputs.current.object piece data.threshold receiver load =
                some (Graph.Route8Census.basin inputs.current.object
                  data.threshold (piece, receiver, load)) := by
            rw [basinEq]
            exact selectedEq
          have complete := Graph.Route8.TraceBasin.select?_traceComplete
            selectedCensus
          have avoids : ¬ Graph.HasCycleWithLength data.LengthOK
              inputs.current.object := selection.1
          have minimality : ∀ representative : Graph.FiniteObject.{u},
              representative.LexicographicallySmaller inputs.current.object →
              Graph.MinimumDegreeAtLeast data.threshold representative →
              Graph.HasCycleWithLength data.LengthOK representative :=
            fun representative lex base => selection.2 representative lex base
          have noQuotient : ¬ ∃ retained,
              Graph.Route8.TraceBasin.TraceResponseQuotient inputs.current.object
                piece data.threshold data.LengthOK receiver load
                (Graph.Route8Census.basin inputs.current.object data.threshold
                  (piece, receiver, load)) retained :=
            quotientFreeCore receiver receiverMem load loadMem _ selectedCensus
          have noDeloc : ¬ Graph.Route8.TraceBasin.TraceDelocalization
              inputs.current.object piece data.threshold data.LengthOK receiver
              load (Graph.Route8Census.basin inputs.current.object data.threshold
                (piece, receiver, load)) :=
            Graph.Route8.TraceBasin.not_traceDelocalization exclusion avoids
              minimality
          have noSep : ¬ Graph.Route8.TraceBasin.TraceSurvivingSeparator
              inputs.current.object piece data.threshold data.LengthOK receiver
              load (Graph.Route8Census.basin inputs.current.object data.threshold
                (piece, receiver, load)) :=
            Graph.Route8.TraceBasin.not_traceSurvivingSeparator_of_noEnvelope
              avoids
              (fun vertex high => by
                show data.threshold < inputs.current.object.degree vertex
                rw [cubic]
                exact high)
              (fun centre first second collision =>
                avoids
                  (Graph.WindowLabelCollision.hasCycleWithLength_of_labelCollision
                    data.degenerateClosureRejected collision))
              noHandoff
          have basinSubset : Graph.Route8Census.basin inputs.current.object
              data.threshold (piece, receiver, load) ⊆ piece := complete.1
          have loadDegree : inputs.current.object.internalDegree piece load =
              data.threshold :=
            (inputs.current.object.mem_routedLoads.mp loadRouted).2.1
          have receiverDegree : inputs.current.object.internalDegree piece
              receiver < data.threshold :=
            (inputs.current.object.mem_receivers.mp receiverMem).2
          have loadNeReceiver : load ≠ receiver := by
            intro same
            subst load
            omega
          obtain ⟨trace, traceSelected, traceInside⟩ := complete.2.1
          have tracePositive : 0 < trace.1.length := by
            apply Nat.pos_of_ne_zero
            intro zero
            exact loadNeReceiver (trace.1.eq_of_length_eq_zero zero)
          set basin := Graph.Route8Census.basin inputs.current.object
            data.threshold (piece, receiver, load) with basinDef
          set presented := Graph.Route8Census.presented inputs.current.object
            data.threshold data.LengthOK (piece, receiver, load) with presentedDef
          set entry := presented.toEntry
            (Graph.HasCycleWithLength data.LengthOK) with entryDef
          let crossing := (entry.retained entry.essentialCore).filter
            (fun coordinate =>
              ∃ event : Graph.Route8.CoordinateEvent inputs.current.object,
                presented.event? coordinate = some event ∧
                  (∃ left right : inputs.current.object.Vertex,
                    s(left, right) ∈ event.walk.edges ∧
                      left ∈ basin ∧ right ∈ basin) ∧
                    ∃ left right : inputs.current.object.Vertex,
                      s(left, right) ∈ event.walk.edges ∧
                        (left ∉ piece ∨ right ∉ piece))
          have parity : ∀ coordinate ∈ crossing,
              2 ≤ (entry.car coordinate).card := by
            intro coordinate member
            obtain ⟨_retained, event, eventEq, ⟨insideL, insideR, insideEdge,
              insideLBasin, _insideRBasin⟩, outsideL, outsideR, outsideEdge,
              outsideSplit⟩ := Finset.mem_filter.mp member
            refine Graph.Route8.PresentedEntry.two_le_card_car presented
              ⟨event, eventEq, ⟨insideL, ?_, ?_⟩, ?_⟩
            · exact SimpleGraph.Walk.fst_mem_support_of_mem_edges _ insideEdge
            · exact basinSubset insideLBasin
            · rcases outsideSplit with outsideLNot | outsideRNot
              · exact ⟨outsideL,
                  SimpleGraph.Walk.fst_mem_support_of_mem_edges _ outsideEdge,
                  outsideLNot⟩
              · exact ⟨outsideR,
                  SimpleGraph.Walk.snd_mem_support_of_mem_edges _ outsideEdge,
                  outsideRNot⟩
          have alphaBound : 2 ≤ entry.alpha := by
            by_contra small
            have alphaSmall : entry.alpha ≤ 1 := by omega
            refine noQuotient (entry.smallCoreCollapseFacts
              (crossing := crossing) parity ?_ alphaSmall)
            intro crossingEq
            let traceCoordinate : presented.Coordinate :=
              Graph.Route8.PresentedEntry.TraceCoordinate.traceIncidence
            let retained :=
              (entry.retained entry.essentialCore \ crossing).erase traceCoordinate
            refine ⟨retained, ?_, ?_, ?_⟩
            · intro coordinate member
              have retainedMember := (Finset.mem_erase.mp member).2
              have crossingMember := (Finset.mem_sdiff.mp retainedMember).1
              exact (entry.mem_retained.mp crossingMember).1
            · refine ⟨traceCoordinate, ?_, ?_, ?_⟩
              · change Graph.Route8.PresentedEntry.TraceCoordinate.traceIncidence ∈
                  Graph.Route8.PresentedEntry.traceCoordinates
                    inputs.current.object piece data.threshold receiver load
                exact Finset.mem_insert_self _ _
              · exact Finset.notMem_erase _ _
              · left
                exact ⟨rfl, trace, traceSelected, tracePositive, traceInside⟩
            · have retainedBaseEq :
                  Graph.Route8.PresentedEntry.retainedBaseCoordinates
                      inputs.current.object piece retained =
                    Graph.Route8.PresentedEntry.retainedBaseCoordinates
                      inputs.current.object piece
                        (entry.retained entry.essentialCore \ crossing) := by
                apply Finset.ext
                intro coordinate
                simp only [Graph.Route8.PresentedEntry.retainedBaseCoordinates,
                  Finset.mem_filter]
                constructor
                · intro member
                  exact ⟨member.1, (Finset.mem_erase.mp member.2).2⟩
                · intro member
                  refine ⟨member.1, Finset.mem_erase.mpr ⟨?_, member.2⟩⟩
                  simp [traceCoordinate]
              have traceErase :
                  presented.state retained =
                    presented.state (entry.retained entry.essentialCore \ crossing) := by
                change Graph.Route8.PresentedEntry.retainedReading
                    inputs.current.object piece basin data.threshold data.LengthOK
                      (Graph.Route8.PresentedEntry.retainedBaseCoordinates
                        inputs.current.object piece retained) =
                  Graph.Route8.PresentedEntry.retainedReading
                    inputs.current.object piece basin data.threshold data.LengthOK
                      (Graph.Route8.PresentedEntry.retainedBaseCoordinates
                        inputs.current.object piece
                          (entry.retained entry.essentialCore \ crossing))
                exact congrArg
                  (Graph.Route8.PresentedEntry.retainedReading
                    inputs.current.object piece basin data.threshold data.LengthOK)
                  retainedBaseEq
              have retainedEq :
                  presented.state retained = entry.restriction entry.essentialCore :=
                traceErase.trans crossingEq
              -- `lem:typeA-one-terminal-collapse` step 3:
              -- the quotient is target-complete against the declared
              -- `u`-supported target algebra (`def:typeA-trace-basin`) because `alpha <= 1`
              -- refutes the failure side -- a surviving mixed return would carry
              -- two distinct boundary incidences of the core
              -- (`lem:typeA-carrier-cut-parity`).  This replaces the
              -- `essentialCore_complete` shortcut.
              exact fun realization _realizes =>
                Graph.Route8.TraceBasin.allQuotientRealizations_declaredEquivalent_of_alpha_le_one
                  alphaSmall realization _
          -- the classification of the entry
          refine ⟨selectedCensus, alphaBound, ?_⟩
          by_cases defect : Graph.Route8.TraceBasin.TraceLocalTargetDefect
              inputs.current.object piece data.threshold data.LengthOK receiver
              load basin
          · refine Or.inr ⟨defect, noQuotient, noDeloc, noSep, ?_⟩
            exact Graph.Route8.TraceBasin.exists_witness_of_traceLocalTargetDefect
              selectedCensus loadRouted defect
          · exact Or.inl
              (Graph.Route8.TraceBasin.targetCompleteMinimal_of_refutations
                complete defect noQuotient exclusion avoids minimality noSep)⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
