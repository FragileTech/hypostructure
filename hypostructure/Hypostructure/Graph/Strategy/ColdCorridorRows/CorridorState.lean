import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.ColdIncrementArithmetic
import Hypostructure.Graph.ColdGermFamily
import Hypostructure.Graph.Strategy.ColdCorridorRows.Basic

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! ## Node `[153]`, `lem:cold-corridor-first-failure`: routing

This is the joint owner of `K .coldCorridorState` and
`K .coldFailureRouting`.  It reads the selected-stub partition from
`K .coldReturnCorridors`, constructs the current finite prefix-code
presentation from the literal corridor and its bounded active interface, and
performs the terminal-or-first-repeat construction locally in this atomic
executor.  Its support, offset, relational label, embedded-incidence, and
labelled-degree data are all read from the current graph.  In particular, the
former `(support.card, head ∈ support)` surrogate is absent: equal retained
values mean equal labelled embedded data for the declared coordinate.

The second representative is selected only from the retained finite-state
class: it preserves the inherited boundary-degree profile and baseline, while
the target response is left to the manuscript's (F2)/G2 test.  In particular
the executor does not call `CanonicalPiece.cutStateRepresentative`, whose
all-context `ContextEquivalent` field would circularly erase that alternative.

The separately named (F1)--(F4) consequences are committed in the same atomic
row.  Candidate overlap and mass accounting belong to
`lem:cold-germ-extraction` and are not published under this key. -/

set_option maxHeartbeats 1600000 in
@[reducible] noncomputable def coldCorridorStateRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldCorridorState
    { Requires := [K .coldReturnCorridors, K .hotColdPartition]
      Produces := [K .coldCorridorState]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let corridors := (inputs.get (K .coldReturnCorridors)).down
      let split := (inputs.get (K .hotColdPartition)).down
      let state : ColdCorridorStateStatement data.toParameters inputs.current.object := by
          classical
          let object := inputs.current.object
          letI : FinEnum object.Vertex := object.vertices
          let cubic := (canonicalColdWindows data.toParameters object).filter
            (AmbientCubicWindow data.toParameters object)
          let packing := canonicalWindowPacking data.toParameters object
          let windows := coldCorridorWindows data.toParameters object
          let Selected := {stub : object.Vertex × object.Vertex //
            stub ∈ Graph.ColdCorridor.allSelectedStubs object cubic}
          change HotColdWindowStatement data.toParameters object at split
          obtain ⟨validPacking, _attains, _maximal, _hot,
            coldIff, _disjoint, _cover⟩ := split
          have cubicWindow : ∀ window ∈ cubic,
              object.InducesWindow data.windowOrder window := by
            intro window member
            have coldMember : window ∈ canonicalColdWindows data.toParameters object :=
              (Finset.mem_filter.mp member).1
            have packingMember : window ∈ canonicalWindowPacking data.toParameters object :=
              (coldIff window).mp coldMember |>.1
            exact validPacking.1 window packingMember
          have packingWindow : ∀ window ∈ packing,
              object.InducesWindow data.windowOrder window := by
            intro window member
            exact validPacking.1 window member
          change ColdReturnCorridorsStatement data.toParameters object at corridors
          simp only [ColdReturnCorridorsStatement] at corridors
          obtain ⟨_componentwise, partition, _cardinality⟩ := corridors
          have corridorExists : ∀ epsilon : ColdEligibleHalfEdge data.toParameters object,
              ∃ (component : Finset object.Vertex)
                (corridor : Graph.ColdCorridor.Corridor object windows component),
                Graph.ColdCorridor.IsOutsideComponent object windows component ∧
                  corridor.entryStub = (epsilon.1.2, epsilon.1.1) := by
            intro epsilon
            let selectedEpsilon : Selected := ⟨epsilon.1, epsilon.property.1⟩
            rcases partition selectedEpsilon with outside | crossWindow
            · obtain ⟨_outsideFoot, component, corridor, outsideComponent,
                  entry⟩ := outside
              exact ⟨component, corridor, outsideComponent, entry⟩
            · exact (epsilon.property.2 crossWindow).elim
          let componentAt : ColdEligibleHalfEdge data.toParameters object → Finset object.Vertex :=
            fun epsilon => Classical.choose (corridorExists epsilon)
          let corridorAt : (epsilon : ColdEligibleHalfEdge data.toParameters object) →
              Graph.ColdCorridor.Corridor object windows (componentAt epsilon) :=
            fun epsilon => Classical.choose (Classical.choose_spec
              (corridorExists epsilon))
          have corridorFacts : ∀ epsilon : ColdEligibleHalfEdge data.toParameters object,
              Graph.ColdCorridor.IsOutsideComponent object windows
                  (componentAt epsilon) ∧
                (corridorAt epsilon).entryStub =
                  (epsilon.1.2, epsilon.1.1) := by
            intro epsilon
            exact Classical.choose_spec (Classical.choose_spec
              (corridorExists epsilon))
          let entryWindowAt : ColdEligibleHalfEdge data.toParameters object →
              Finset object.Vertex := fun epsilon =>
            Classical.choose
              ((Graph.ColdCorridor.mem_windowsOf object cubic epsilon.1.1).1
                (Graph.ColdCorridor.selected_facts object cubic
                  (⟨epsilon.1, epsilon.2.1⟩ :
                    ColdSelectedHalfEdge data.toParameters object)).1)
          let successorWindowAt : (epsilon : ColdEligibleHalfEdge data.toParameters object) →
              Finset object.Vertex := fun epsilon => by
            have boundaryMember : (corridorAt epsilon).successorStub ∈
                Graph.ColdCorridor.boundaryStubs object windows
                  (componentAt epsilon) := List.get_mem _ _
            have inWindows : (corridorAt epsilon).successorStub.2 ∈ windows :=
              ((Graph.ColdCorridor.mem_boundaryStubs_iff object windows
                (componentAt epsilon) _).1 boundaryMember).2.1
            exact Classical.choose
              ((Graph.ColdCorridor.mem_windowsOf object packing
                (corridorAt epsilon).successorStub.2).1 inWindows)
          let activeAt := fun (epsilon : ColdEligibleHalfEdge data.toParameters object)
              (segment : (corridorAt epsilon).Segment) =>
            entryWindowAt epsilon ∪ successorWindowAt epsilon ∪
              ({(corridorAt epsilon).entryStub.1,
                (corridorAt epsilon).head segment} : Finset object.Vertex)
          let offsetAt : object.Vertex → Fin data.coldSignature.windowOrder :=
            fun vertex => by
              by_cases contained : ∃ window ∈ packing, vertex ∈ window
              · let window := Classical.choose contained
                have windowFacts := Classical.choose_spec contained
                have windowMember : window ∈ packing := windowFacts.1
                have vertexMember : vertex ∈ window := windowFacts.2
                have induced := packingWindow window windowMember
                letI : FinEnum (object.induce window).Vertex :=
                  (object.induce window).vertices
                let embedding := Classical.choice induced.1
                have cardInduced :
                    Fintype.card (object.induce window).Vertex = window.card := by
                  simpa [FiniteObject.vertexCount,
                    FinEnum.card_eq_fintypeCard] using
                    object.vertexCount_induce window
                have embeddingSurjective : Function.Surjective embedding := by
                  exact ((Fintype.bijective_iff_injective_and_card embedding).2
                    ⟨embedding.injective, by
                      rw [Fintype.card_fin, cardInduced, induced.2]⟩).2
                exact Classical.choose (embeddingSurjective ⟨vertex, vertexMember⟩)
              · exact
                  ⟨(FinEnum.equiv vertex).1 % data.coldSignature.windowOrder,
                    Nat.mod_lt _ data.coldSignature.windowOrder_pos⟩
          let supportOn := fun (activeSet : Finset object.Vertex)
              (_clause : data.coldSignature.Clause)
              (generator : Graph.ColdCorridor.Coordinate
                (Graph.ColdCorridor.interfaceWidth data.windowOrder)) => by
            let active := activeSet.toList
            let valid := generator.support.filter fun position =>
              position.1 < active.length
            exact valid.attach.image fun position => by
              have member := position.property
              change position.1 ∈ generator.support.filter
                (fun slot => slot.1 < active.length) at member
              exact active.get ⟨position.1.1,
                (Finset.mem_filter.1 member).2⟩
          let valueOn : (activeSet : Finset object.Vertex) →
              (clause : data.coldSignature.Clause) →
              (generator : data.coldSignature.Generator clause) →
              data.coldSignature.Value clause generator :=
            fun activeSet clause generator => by
            let width := Graph.ColdCorridor.interfaceWidth data.windowOrder
            let active := activeSet.toList
            let activePositions : Finset (Fin width) :=
              Finset.univ.filter fun position => position.1 < active.length
            let supportPositions : Finset (Fin width) :=
              generator.support.filter fun position => position.1 < active.length
            let incidences : Finset (Fin width × Fin width) :=
              (generator.support.product activePositions).filter fun incidence =>
                if leftBound : incidence.1.1 < active.length then
                  if rightBound : incidence.2.1 < active.length then
                    object.graph.Adj
                      (active.get ⟨incidence.1.1, leftBound⟩)
                      (active.get ⟨incidence.2.1, rightBound⟩)
                  else False
                else False
            let labelNeighbors : Finset (Fin width) :=
              activePositions.filter fun position =>
                if labelBound : generator.anchor.1 < active.length then
                  if positionBound : position.1 < active.length then
                    object.graph.Adj
                      (active.get ⟨generator.anchor.1, labelBound⟩)
                      (active.get ⟨position.1, positionBound⟩)
                  else False
                else False
            have labelDegreeBound : labelNeighbors.card ≤ width := by
              calc
                labelNeighbors.card ≤ activePositions.card :=
                  Finset.card_le_card (Finset.filter_subset _ _)
                _ ≤ (Finset.univ : Finset (Fin width)).card :=
                  Finset.card_le_card (Finset.subset_univ _)
                _ = width := Fintype.card_fin width
            change Graph.ColdCorridor.EmbeddedCoordinateValue width clause generator
            exact (supportPositions, incidences,
              ⟨labelNeighbors.card, Nat.lt_succ_of_le labelDegreeBound⟩)
          let supportAt := fun (epsilon : ColdEligibleHalfEdge data.toParameters object)
              (segment : (corridorAt epsilon).Segment) =>
            supportOn (activeAt epsilon segment)
          let valueAt : (epsilon : ColdEligibleHalfEdge data.toParameters object) →
              (corridorAt epsilon).Segment →
              (clause : data.coldSignature.Clause) →
              (generator : data.coldSignature.Generator clause) →
              data.coldSignature.Value clause generator :=
            fun epsilon segment => valueOn (activeAt epsilon segment)
          let presentationAt : ColdEligibleHalfEdge data.toParameters object →
              Graph.ColdCorridor.Presentation data.coldSignature object :=
            fun epsilon => (corridorAt epsilon).presentation data.coldSignature
              (activeAt epsilon) offsetAt (supportAt epsilon) (valueAt epsilon)
          let indexAt : (epsilon : ColdEligibleHalfEdge data.toParameters object) →
              (corridorAt epsilon).Segment → (presentationAt epsilon).Segment :=
            fun _epsilon segment => ULift.up segment
          let makeGerm : (support : Finset object.Vertex) →
              support.card ≤ Graph.ColdCorridor.exchangeBound data.coldSignature →
              Graph.SupportComponents.Connected.ConnectedOn object support →
              (∃ vertex, vertex ∉ support) →
              Graph.ColdCorridor.Record data.coldSignature →
              Graph.ColdCorridor.BoundedGerm data.coldSignature
                (Graph.MinimumDegreeAtLeast data.threshold)
                (Graph.HasCycleWithLength data.LengthOK) object :=
            fun support bounded connected proper record => by
              let atom := Graph.ColdCorridor.rowAtom object support connected proper
              let reading : Graph.CanonicalPiece atom.interface → Prop :=
                fun candidate =>
                  candidate.toPiece.boundaryDegreeProfile =
                      atom.piece.boundaryDegreeProfile ∧
                    ∀ outside : Graph.OutsideContext atom.interface,
                      Graph.MinimumDegreeAtLeast data.threshold
                          (Graph.glue atom.piece outside) →
                        Graph.MinimumDegreeAtLeast data.threshold
                          (Graph.glue candidate.toPiece outside)
              have sourceReading : reading atom.piece.toCanonical := by
                refine ⟨?_, ?_⟩
                · rw [Graph.BoundaryPiece.toCanonical_toPiece]
                  exact atom.piece.transport_boundaryDegreeProfile _
                · intro outside sourceBaseline
                  exact
                    ((Graph.minimumDegreeAtLeast_isomorphismInvariant
                      data.threshold).iff_of_iso
                        (atom.piece.toCanonical_glue_isomorphic outside)).2
                      sourceBaseline
              have realizable : ∃ candidate, reading candidate :=
                ⟨atom.piece.toCanonical, sourceReading⟩
              let selected :=
                Graph.CanonicalPiece.canonicalRepresentative reading realizable
              have selectedReading : reading selected :=
                Graph.CanonicalPiece.canonicalRepresentative_reading reading
                  realizable
              have pieceSizeLe : atom.piece.internalVertexCount ≤ support.card := by
                let embedding : atom.piece.Internal →
                    {vertex // vertex ∈ support} :=
                  fun vertex => ⟨vertex.1, vertex.2.1⟩
                have injective : Function.Injective embedding := by
                  intro left right same
                  apply Subtype.ext
                  exact congrArg
                    (fun vertex : {vertex // vertex ∈ support} => vertex.1) same
                letI : FinEnum atom.piece.Internal := atom.piece.internalVertices
                letI : Fintype atom.piece.Internal :=
                  @FinEnum.instFintype atom.piece.Internal
                    atom.piece.internalVertices
                have cardBound := Fintype.card_le_of_injective embedding injective
                change @FinEnum.card atom.piece.Internal
                    atom.piece.internalVertices ≤ support.card
                rw [FinEnum.card_eq_fintypeCard]
                simpa using cardBound
              have selectedBound : selected.toPiece.internalVertexCount ≤
                  Graph.ColdCorridor.exchangeBound data.coldSignature := by
                calc
                  selected.toPiece.internalVertexCount = selected.size := by simp
                  _ ≤ atom.piece.toCanonical.size :=
                    Graph.CanonicalPiece.canonicalRepresentative_size_le
                      reading realizable sourceReading
                  _ = atom.piece.internalVertexCount := rfl
                  _ ≤ support.card := pieceSizeLe
                  _ ≤ Graph.ColdCorridor.exchangeBound data.coldSignature := bounded
              have sourceBaseline :
                  Graph.MinimumDegreeAtLeast data.threshold
                    (Graph.glue atom.piece atom.outside) :=
                ((Graph.minimumDegreeAtLeast_isomorphismInvariant
                  data.threshold).iff_of_iso ⟨atom.reconstructionIso⟩).mpr
                    inputs.current.baseline
              exact
                { support := support
                  bounded := bounded
                  connected := connected
                  proper := proper
                  canonical := selected.toPiece
                  canonicalBounded := selectedBound
                  sameProfile := selectedReading.1
                  baseline := selectedReading.2 atom.outside sourceBaseline
                  record := record }
          have germExists : ∀ epsilon : ColdEligibleHalfEdge data.toParameters object,
              ∃ germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
                  (Graph.MinimumDegreeAtLeast data.threshold)
                  (Graph.HasCycleWithLength data.LengthOK) object,
                (corridorAt epsilon).FirstFailureGermWitness
                  (Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold)
                  (Graph.cycleTargetInterface data.LengthOK).isomorphismInvariant
                  (presentationAt epsilon) (indexAt epsilon) germ := by
            intro epsilon
            let corridor := corridorAt epsilon
            let presentation := presentationAt epsilon
            let index := indexAt epsilon
            rcases corridor.exists_firstFailure presentation index
                ULift.up_injective with terminal | repeated
            · let support := corridor.prefixSupport corridor.statesRead
              let terminalSegment : corridor.Segment :=
                ⟨corridor.inside.1.length, Nat.lt_succ_self _⟩
              let record := corridor.recordAt presentation index terminalSegment
              have supportBound : support.card ≤
                  Graph.ColdCorridor.exchangeBound data.coldSignature := by
                have supportCard :=
                  corridor.prefixSupport_card_le corridor.statesRead
                have terminalBound : corridor.statesRead ≤
                    Graph.ColdCorridor.stateBound data.coldSignature := terminal
                have budgetPositive : 1 ≤
                    Graph.ColdCorridor.interfaceBudget data.coldSignature := by
                  unfold Graph.ColdCorridor.interfaceBudget
                  omega
                change support.card ≤
                  Graph.ColdCorridor.exchangeBound data.coldSignature
                dsimp [support]
                unfold Graph.ColdCorridor.exchangeBound
                omega
              let germ := makeGerm support supportBound
                (corridor.prefixSupport_connectedOn corridor.statesRead)
                (corridor.prefixSupport_proper (corridorFacts epsilon).1
                  corridor.statesRead) record
              refine ⟨germ, supportBound, ?_, Or.inl ⟨terminal, rfl, ?_⟩⟩
              · intro vertex member
                exact corridor.prefixSupport_subset_inside
                  corridor.statesRead vertex member
              · rfl
            · obtain ⟨left, right, rightBound, before, same, first⟩ := repeated
              let support := corridor.intervalSupport left right
              let record := corridor.recordAt presentation index left
              have supportBound : support.card ≤
                  Graph.ColdCorridor.exchangeBound data.coldSignature := by
                have supportCard := corridor.intervalSupport_card_le left right
                have budgetPositive : 1 ≤
                    Graph.ColdCorridor.interfaceBudget data.coldSignature := by
                  unfold Graph.ColdCorridor.interfaceBudget
                  omega
                change support.card ≤
                  Graph.ColdCorridor.exchangeBound data.coldSignature
                dsimp [support]
                unfold Graph.ColdCorridor.exchangeBound
                omega
              let germ := makeGerm support supportBound
                (corridor.intervalSupport_connectedOn left right)
                (corridor.intervalSupport_proper (corridorFacts epsilon).1
                  left right) record
              have recordSame : corridor.recordAt presentation index left =
                  corridor.recordAt presentation index right := by
                unfold Graph.ColdCorridor.Corridor.recordAt
                have boundaryDegrees :
                    presentation.boundaryDegrees (index left) =
                      presentation.boundaryDegrees (index right) := by
                  simpa only [Graph.ColdCorridor.Presentation.state] using
                    congrArg Graph.ColdCorridor.CutState.boundaryDegrees same
                have halfEdges : presentation.halfEdges (index left) =
                    presentation.halfEdges (index right) := by
                  simpa only [Graph.ColdCorridor.Presentation.state] using
                    congrArg Graph.ColdCorridor.CutState.halfEdges same
                have offsets : presentation.offsets (index left) =
                    presentation.offsets (index right) := by
                  simpa only [Graph.ColdCorridor.Presentation.state] using
                    congrArg Graph.ColdCorridor.CutState.offsets same
                rw [boundaryDegrees, halfEdges, offsets, same]
              refine ⟨germ, supportBound, ?_, Or.inr
                ⟨left, right, rightBound, before, same,
                  presentation.reading_eq_of_state_eq same, first, rfl, rfl,
                    recordSame⟩⟩
              · intro vertex member
                exact corridor.intervalSupport_subset_inside left right vertex member
          let outsideIncidence := fun epsilon =>
            Classical.choose (germExists epsilon)
          have crossGermExists : ∀ epsilon : ColdCrossWindowHalfEdge data.toParameters object,
              ∃ germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
                  (Graph.MinimumDegreeAtLeast data.threshold)
                  (Graph.HasCycleWithLength data.LengthOK) object,
                germ.support = {epsilon.1.1, epsilon.1.2} := by
            intro epsilon
            let selectedEpsilon : Selected := ⟨epsilon.1, epsilon.property.1⟩
            have selectedFacts :=
              Graph.ColdCorridor.selected_facts object cubic selectedEpsilon
            obtain ⟨sourceWindow, sourceWindowMem, sourceMem⟩ :=
              (Graph.ColdCorridor.mem_windowsOf object cubic epsilon.1.1).1
                selectedFacts.1
            obtain ⟨targetWindow, targetWindowMem, targetMem⟩ :=
              (Graph.ColdCorridor.mem_windowsOf object packing epsilon.1.2).1
                epsilon.property.2
            let support : Finset object.Vertex := {epsilon.1.1, epsilon.1.2}
            have adjacent : object.graph.Adj epsilon.1.1 epsilon.1.2 := by
              simpa only [selectedEpsilon] using selectedFacts.2
            have connected :
                Graph.SupportComponents.Connected.ConnectedOn object support := by
              refine ⟨⟨epsilon.1.1, by simp [support]⟩, ?_⟩
              intro left right leftMem rightMem
              simp only [support, Finset.mem_insert, Finset.mem_singleton] at leftMem rightMem
              rcases leftMem with rfl | rfl <;> rcases rightMem with rfl | rfl
              · exact ⟨SimpleGraph.Walk.nil, by simp, by simp [support]⟩
              · have isPath : (SimpleGraph.Walk.cons adjacent
                    SimpleGraph.Walk.nil).IsPath :=
                  (SimpleGraph.Walk.cons_isPath_iff adjacent
                    SimpleGraph.Walk.nil).2 ⟨by simp, by simpa using adjacent.ne⟩
                refine ⟨SimpleGraph.Walk.cons adjacent
                    SimpleGraph.Walk.nil, isPath, ?_⟩
                simp [support]
              · have isPath : (SimpleGraph.Walk.cons adjacent.symm
                    SimpleGraph.Walk.nil).IsPath :=
                  (SimpleGraph.Walk.cons_isPath_iff adjacent.symm
                    SimpleGraph.Walk.nil).2 ⟨by simp, by simpa using adjacent.symm.ne⟩
                refine ⟨SimpleGraph.Walk.cons adjacent.symm
                    SimpleGraph.Walk.nil, isPath, ?_⟩
                simp [support]
              · exact ⟨SimpleGraph.Walk.nil, by simp, by simp [support]⟩
            have proper : ∃ vertex, vertex ∉ support := by
              have sourceCard : sourceWindow.card = data.windowOrder :=
                (cubicWindow sourceWindow sourceWindowMem).2
              have supportCard : support.card ≤ 2 := by
                exact (Finset.card_insert_le _ _).trans
                  (Nat.succ_le_succ (Finset.card_singleton _).le)
              have notContained : ¬ sourceWindow ⊆ support := by
                intro contained
                have cardBound := Finset.card_le_card contained
                have orderBound := data.five_le_windowOrder
                omega
              obtain ⟨vertex, _sourceMem, notSupport⟩ :=
                Finset.not_subset.mp notContained
              exact ⟨vertex, notSupport⟩
            have bounded : support.card ≤
                Graph.ColdCorridor.exchangeBound data.coldSignature := by
              have supportCard : support.card ≤ 2 := by
                exact (Finset.card_insert_le _ _).trans
                  (Nat.succ_le_succ (Finset.card_singleton _).le)
              unfold Graph.ColdCorridor.exchangeBound
                Graph.ColdCorridor.interfaceBudget
              omega
            let endpointAt : Fin 2 → object.Vertex := fun position =>
              if position = 0 then epsilon.1.1 else epsilon.1.2
            let reverseEndpointAt : Fin 2 → object.Vertex := fun position =>
              if position = 0 then epsilon.1.2 else epsilon.1.1
            let boundedDegree : Fin 2 →
                Fin (data.coldSignature.degreeBound + 1) := fun position =>
              ⟨min (object.degree (endpointAt position))
                  data.coldSignature.degreeBound,
                Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
            let halfEdgeCode : Fin 2 →
                Fin (data.coldSignature.degreeBound + 1) := fun position =>
              ⟨min ((FinEnum.equiv
                    (endpointAt position, reverseEndpointAt position)).1)
                  data.coldSignature.degreeBound,
                Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
            let directState : Graph.ColdCorridor.CutState data.coldSignature :=
              { boundaryDegrees := boundedDegree
                halfEdges := halfEdgeCode
                offsets := fun position => offsetAt (endpointAt position)
                declared := fun clause generator =>
                  some (valueOn support clause generator) }
            let record : Graph.ColdCorridor.Record data.coldSignature :=
              { boundaryDegrees := boundedDegree
                stubs := halfEdgeCode
                offsets := fun position => offsetAt (endpointAt position)
                state := directState
                truth := false }
            let germ := makeGerm support bounded connected proper record
            exact ⟨germ, rfl⟩
          let crossIncidence := fun epsilon =>
            Classical.choose (crossGermExists epsilon)
          have componentInR : ∀ epsilon : ColdEligibleHalfEdge data.toParameters object,
              componentAt epsilon ⊆ object.remainderSupport packing := by
            intro epsilon vertex vertexMember
            apply Finset.mem_sdiff.2
            refine ⟨Finset.mem_univ vertex, ?_⟩
            have outsideWindows : vertex ∉ windows :=
              Finset.disjoint_left.1 (corridorFacts epsilon).1.1
                vertexMember
            intro inPackedSupport
            apply outsideWindows
            exact inPackedSupport
          refine ⟨outsideIncidence, componentAt, corridorAt, presentationAt, indexAt,
            ?_, ?_, ?_, componentInR, ?_, crossIncidence, ?_⟩
          · intro epsilon
            refine ⟨(corridorFacts epsilon).1, (corridorFacts epsilon).2,
              ULift.up_injective, Classical.choose_spec (germExists epsilon)⟩
          · intro epsilon segment
            change (activeAt epsilon segment).card ≤
              Graph.ColdCorridor.interfaceWidth data.windowOrder
            have entryFacts := Classical.choose_spec
              ((Graph.ColdCorridor.mem_windowsOf object cubic epsilon.1.1).1
                (Graph.ColdCorridor.selected_facts object cubic
                  (⟨epsilon.1, epsilon.2.1⟩ :
                    ColdSelectedHalfEdge data.toParameters object)).1)
            have entryCard : (entryWindowAt epsilon).card = data.windowOrder :=
              (cubicWindow (entryWindowAt epsilon) entryFacts.1).2
            have boundaryMember : (corridorAt epsilon).successorStub ∈
                Graph.ColdCorridor.boundaryStubs object windows
                  (componentAt epsilon) := List.get_mem _ _
            have successorInside : (corridorAt epsilon).successorStub.2 ∈ windows :=
              ((Graph.ColdCorridor.mem_boundaryStubs_iff object windows
                (componentAt epsilon) _).1 boundaryMember).2.1
            have successorFacts := Classical.choose_spec
              ((Graph.ColdCorridor.mem_windowsOf object packing
                (corridorAt epsilon).successorStub.2).1 successorInside)
            have successorCard : (successorWindowAt epsilon).card =
                data.windowOrder :=
              (packingWindow (successorWindowAt epsilon) successorFacts.1).2
            have pairCard :
                ({(corridorAt epsilon).entryStub.1,
                  (corridorAt epsilon).head segment} :
                    Finset object.Vertex).card ≤ 2 := by
              exact (Finset.card_insert_le _ _).trans
                (Nat.succ_le_succ (Finset.card_singleton _).le)
            calc
              (activeAt epsilon segment).card ≤
                  (entryWindowAt epsilon ∪ successorWindowAt epsilon).card +
                    ({(corridorAt epsilon).entryStub.1,
                      (corridorAt epsilon).head segment} :
                        Finset object.Vertex).card := by
                simpa [activeAt] using
                  (Finset.card_union_le
                    (entryWindowAt epsilon ∪ successorWindowAt epsilon)
                    ({(corridorAt epsilon).entryStub.1,
                      (corridorAt epsilon).head segment} :
                        Finset object.Vertex))
              _ ≤ ((entryWindowAt epsilon).card +
                    (successorWindowAt epsilon).card) + 2 :=
                Nat.add_le_add
                  (Finset.card_union_le (entryWindowAt epsilon)
                    (successorWindowAt epsilon)) pairCard
              _ ≤ Graph.ColdCorridor.interfaceWidth data.windowOrder := by
                rw [entryCard, successorCard]
                unfold Graph.ColdCorridor.interfaceWidth
                omega
          · intro epsilon crossWindow
            obtain ⟨sourceWindow, sourceMember, sourceInside⟩ :=
              (Graph.ColdCorridor.mem_windowsOf object cubic epsilon.1.1).1
                (Graph.ColdCorridor.selected_facts object cubic epsilon).1
            obtain ⟨targetWindow, targetMember, targetInside⟩ :=
              (Graph.ColdCorridor.mem_windowsOf object packing epsilon.1.2).1
                crossWindow
            exact ⟨sourceWindow, sourceMember, targetWindow, targetMember,
              sourceInside, targetInside,
              (Graph.ColdCorridor.selected_facts object cubic epsilon).2⟩
          · intro epsilon vertex vertexMember
            apply componentInR epsilon
            obtain ⟨inner, _innerMember, rfl⟩ := List.mem_map.1 vertexMember
            exact inner.2
          · intro epsilon
            exact Classical.choose_spec (crossGermExists epsilon)
      .cons (key := K .coldCorridorState) ⟨state⟩ .nil)

end Hypostructure.Graph.Strategy.Spine
