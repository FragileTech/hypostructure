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

/-! ## Fact 2 of node `[123]`: `lem:typeA-unpeeled-visible-routing`

*"Suppose that a completion port of `w` carries four visible receiver-entry
returns whose routed loads lie in `L(w) \\ P₄(w)`.  Then the unpeeled data
realize one of exits (1)--(7) ... If the realized exit is (4), the
target-defective quotient has declared routed-load support containing at least
one of those four unpeeled loads."*  At the unified collection, exits
`(1)`--`(3)` and `(6)` close against the standing invariants inside the
per-load routing, exit `(7)` contradicts the collection's own no-handoff
filter (`rem:unified-covers-exit4`), and what remains per overloaded port is
the exit-`(4)` witness or, per selected visible unpeeled load, the trace-basin
outcome of `lem:typeA-reduced-silent-residual`. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def route8VisibleRoutingRow :
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
    `Hypostructure.Graph.Strategy.Spine.route8VisibleExitFourRouting
    { Requires := [K .selection, K .replacementExclusion, K .cubicBaseline]
      Produces := [K .route8VisibleExitFourRouting]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let selection := (inputs.get (K .selection)).down
      let exclusion := (inputs.get (K .replacementExclusion)).down
      let cubic := (inputs.get (K .cubicBaseline)).down.1
      .cons (key := K .route8VisibleExitFourRouting)
        (show Value BranchState Presentation presentation data
            .route8VisibleExitFourRouting inputs.current from
          ⟨by
            classical
            dsimp only [Holds]
            letI : DecidableEq inputs.current.object.Vertex :=
              inputs.current.object.vertices.decEq
            intro component componentMem receiver _receiverMem peeled
              _peeledSubset outside _portMem _overCard
            set piece := inputs.current.object.pieceSupport
              (inputs.current.object.remainderSupport
                (canonicalWindowPacking data inputs.current.object)) component
              with pieceDef
            have avoids :
                ¬ Graph.HasCycleWithLength data.LengthOK
                  inputs.current.object := selection.1
            have minimality : ∀ representative : Graph.FiniteObject.{u},
                representative.LexicographicallySmaller inputs.current.object →
                Graph.MinimumDegreeAtLeast data.threshold representative →
                Graph.HasCycleWithLength data.LengthOK representative :=
              fun representative lex base =>
                selection.2 representative lex base
            have componentPiece : component ∈
                inputs.current.object.canonicalPieces
                  (inputs.current.object.remainderSupport
                    (canonicalWindowPacking data inputs.current.object)) :=
              (Finset.mem_filter.1 componentMem).1
            have connected :
                Graph.SupportComponents.Connected.ConnectedOn
                  inputs.current.object piece :=
              Graph.SupportComponents.Connected.connectedOn_of_mem_order
                inputs.current.object _
                ((Graph.FiniteObject.mem_canonicalPieces _ _).1 componentPiece)
            have noHandoff : ¬ HandoffProduced data inputs.current.object
                (canonicalWindowPacking data inputs.current.object) piece :=
              ((Finset.mem_filter.1 componentMem).2).2.2
            by_cases witnessed : ∃ witness : Graph.ExitFour.Witness
                (Graph.HasCycleWithLength data.LengthOK) piece data.threshold
                data.dischargeScale receiver peeled,
              witness.load ∈
                (Graph.VisibleEntry.visibleLoadsAt inputs.current.object piece
                  data.threshold receiver outside) \ peeled
            · exact Or.inl witnessed
            refine Or.inr ?_
            intro load loadMem
            have inOrder := List.mem_of_mem_take loadMem
            have member : load ∈ Graph.ExitFour.unpeeledVisibleLoadsAt piece
                data.threshold receiver outside peeled := by
              simpa [inputs.current.object.mem_orderedVertices load] using
                inOrder
            have unpeeled : load ∈ Graph.ExitFour.unpeeledLoads piece
                data.threshold receiver peeled :=
              (Finset.mem_inter.1 member).2
            have visMem : load ∈ Graph.VisibleEntry.visibleLoadsAt
                inputs.current.object piece data.threshold receiver outside :=
              (Finset.mem_inter.1 member).1
            have unpeeledSplit := unpeeled
            rw [Graph.ExitFour.mem_unpeeledLoads] at unpeeledSplit
            by_cases quotient : ∃ basin : Finset inputs.current.object.Vertex,
                Graph.Route8.TraceBasin.select? inputs.current.object piece
                    data.threshold receiver load = some basin ∧
                  ∃ retained,
                    Graph.Route8.TraceBasin.TraceResponseQuotient
                      inputs.current.object piece data.threshold
                      data.LengthOK receiver load basin retained
            · exact Or.inr quotient
            refine Or.inl ?_
            by_cases separated : ∃ basin : Finset inputs.current.object.Vertex,
                Graph.Route8.TraceBasin.TraceSurvivingSeparator
                  inputs.current.object piece data.threshold data.LengthOK
                  receiver load basin
            · obtain ⟨basin, separator⟩ := separated
              refine absurd ?_ noHandoff
              obtain ⟨envelope, coreEq, decorated⟩ :=
                Graph.Route8.TraceBasin.exists_envelope_of_traceSurvivingSeparator
                  (HighDegree := handoffHighDegree data inputs.current.object)
                  (Absorbing :=
                    handoffAbsorbing data inputs.current.object
                      (canonicalWindowPacking data inputs.current.object))
                  separator avoids
                  (fun vertex high => by
                    show data.threshold < inputs.current.object.degree vertex
                    rw [cubic]
                    exact high)
                  (fun centre first second collision =>
                    avoids
                      (Graph.WindowLabelCollision.hasCycleWithLength_of_labelCollision
                        data.degenerateClosureRejected collision))
              exact ⟨envelope, coreEq, decorated⟩
            · rcases Graph.Route8.TraceBasin.exists_witness_or_route8Entry
                  (scale := data.dischargeScale) connected unpeeledSplit.1
                  (fun basin selectedEq quotientAt =>
                    quotient ⟨basin, selectedEq, quotientAt⟩)
                  exclusion avoids minimality
                  (not_exists.1 separated) with ⟨witness₀, witnessLoad⟩ | entry
              · refine absurd ?_ witnessed
                exact ⟨⟨load, unpeeled, witnessLoad ▸ witness₀.member⟩,
                  Finset.mem_sdiff.2 ⟨visMem, unpeeledSplit.2⟩⟩
              · exact entry⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
