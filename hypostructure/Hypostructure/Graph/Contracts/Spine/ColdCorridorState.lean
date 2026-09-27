import Hypostructure.Graph.Statements.Spine
import Hypostructure.Graph.Contracts.Spine.ColdSubcubicCharge
import Hypostructure.Graph.ColdIncrementArithmetic
import Hypostructure.Graph.ColdGermFamily
import Hypostructure.Graph.ColdGermOverlap

/-!
# Contracts: the cold corridor state and the germ candidates `[153]`

Proof-agnostic contract lemmas for `lem:cold-corridor-first-failure` (the
retained corridor state: presentations, readings, first repeat, table record,
and terminal/repeated exchange germ) and `lem:cold-germ-extraction` (the
repaired (F5) candidate family with its loss accounting).  Each lemma is stated
over a `Graph.FiniteObject` with the registered `Parameters` as a parameter and
every paper hypothesis explicit; its conclusion is exactly the statement of the
fact it proves.  This module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Contracts.Spine

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

set_option maxHeartbeats 1600000 in
/-- **Node `[153]`, `lem:cold-corridor-first-failure`: the retained corridor
state.**  Every eligible selected half-edge has its return corridor (from the
selected-stub partition of the return corridors); the corridor carries the
finite prefix-code presentation read from the current graph with its bounded
active interface, and the terminal-or-first-repeat construction gives its
exchange germ.  The second representative is selected from the retained
finite-state class only, preserving the boundary-degree profile and baseline. -/
theorem coldCorridorState_of_corridors (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (fiveLeOrder : 5 ≤ data.windowOrder)
    (corridors : ColdReturnCorridorsStatement data object)
    (split : HotColdWindowStatement data object) :
    ColdCorridorStateStatement data object := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  let cubic := (canonicalColdWindows data object).filter
    (AmbientCubicWindow data object)
  let packing := canonicalWindowPacking data object
  let windows := coldCorridorWindows data object
  let Selected := {stub : object.Vertex × object.Vertex //
    stub ∈ Graph.ColdCorridor.allSelectedStubs object cubic}
  change HotColdWindowStatement data object at split
  obtain ⟨validPacking, _attains, _maximal, _hot,
    coldIff, _disjoint, _cover⟩ := split
  have cubicWindow : ∀ window ∈ cubic,
      object.InducesWindow data.windowOrder window := by
    intro window member
    have coldMember : window ∈ canonicalColdWindows data object :=
      (Finset.mem_filter.mp member).1
    have packingMember : window ∈ canonicalWindowPacking data object :=
      (coldIff window).mp coldMember |>.1
    exact validPacking.1 window packingMember
  have packingWindow : ∀ window ∈ packing,
      object.InducesWindow data.windowOrder window := by
    intro window member
    exact validPacking.1 window member
  change ColdReturnCorridorsStatement data object at corridors
  simp only [ColdReturnCorridorsStatement] at corridors
  obtain ⟨_componentwise, partition, _cardinality⟩ := corridors
  have corridorExists : ∀ epsilon : ColdEligibleHalfEdge data object,
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
  let componentAt : ColdEligibleHalfEdge data object → Finset object.Vertex :=
    fun epsilon => Classical.choose (corridorExists epsilon)
  let corridorAt : (epsilon : ColdEligibleHalfEdge data object) →
      Graph.ColdCorridor.Corridor object windows (componentAt epsilon) :=
    fun epsilon => Classical.choose (Classical.choose_spec
      (corridorExists epsilon))
  have corridorFacts : ∀ epsilon : ColdEligibleHalfEdge data object,
      Graph.ColdCorridor.IsOutsideComponent object windows
          (componentAt epsilon) ∧
        (corridorAt epsilon).entryStub =
          (epsilon.1.2, epsilon.1.1) := by
    intro epsilon
    exact Classical.choose_spec (Classical.choose_spec
      (corridorExists epsilon))
  let presentationAt : ColdEligibleHalfEdge data object →
      Graph.ColdCorridor.Presentation data.coldSignature object :=
    fun epsilon => coldCutStatePresentation data object (corridorAt epsilon)
  let indexAt : (epsilon : ColdEligibleHalfEdge data object) →
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
            baseline
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
  have germExists : ∀ epsilon : ColdEligibleHalfEdge data object,
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
  have crossGermExists : ∀ epsilon : ColdCrossWindowHalfEdge data object,
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
        have orderBound := fiveLeOrder
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
        offsets := fun position => coldWindowOffset data object (endpointAt position)
        declared := fun clause generator =>
          some (coldDeclaredValue data object support clause generator) }
    let record : Graph.ColdCorridor.Record data.coldSignature :=
      { boundaryDegrees := boundedDegree
        stubs := halfEdgeCode
        offsets := fun position => coldWindowOffset data object (endpointAt position)
        state := directState
        truth := false }
    let germ := makeGerm support bounded connected proper record
    exact ⟨germ, rfl⟩
  let crossIncidence := fun epsilon =>
    Classical.choose (crossGermExists epsilon)
  have componentInR : ∀ epsilon : ColdEligibleHalfEdge data object,
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
      ⟨ULift.up_injective, rfl⟩, Classical.choose_spec (germExists epsilon)⟩
  · intro epsilon segment
    exact coldActiveInterface_card_le data object packingWindow
      (corridorAt epsilon) segment
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


set_option maxHeartbeats 4000000 in
/-- **Node `[153]`, `lem:cold-germ-extraction`: the (F5) candidate family.**
The candidates are exactly the complete repaired occurrence family: the
outside-corridor F5 prefixes and the immediate two-vertex terminal germs of the
selected cross-window incidences.  A noncandidate occurrence is charged at its
first high-to-subcubic edge, so the corridor loss is bounded by
`(threshold+1)·B_cold·σ(G)`, and the extraction bound applies to the family. -/
theorem coldGermCandidates_of_routing (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (thresholdEq : data.threshold = 3)
    (threeLeOrder : 3 ≤ data.windowOrder)
    (routing : ColdFailureRoutingStatement data object)
    (handoff : ColdFirstHighHandoffStatement data object) :
    ColdGermCandidatesStatement data object := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  let cold := canonicalColdWindows data object
  let cubic := cold.filter (AmbientCubicWindow data object)
  let windows := coldCorridorWindows data object
  let Eligible := ColdEligibleHalfEdge data object
  let Cross := ColdCrossWindowHalfEdge data object
  let Occurrence := ColdGermOccurrence data object
  let Selected := ColdSelectedHalfEdge data object
  change ColdFailureRoutingStatement data object at routing
  let classified := coldRoutedClassified data object routing
  let state := classified.state
  change ColdCorridorStateStatement data object at state
  let outsideIncidence : Eligible →
      Graph.ColdCorridor.BoundedGerm data.coldSignature
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object :=
    coldOccurrenceIncidence data object classified
  let corridorAt := coldOccurrenceCorridorAt data object classified
  let presentationAt :=
    coldOccurrencePresentationAt data object classified
  let indexAt := coldOccurrenceIndexAt data object classified
  let stateFacts := coldOccurrenceStateFacts data object classified
  let traceEnd := coldRoutedTraceEnd data object routing
  let traceFacts := fun epsilon : Eligible => Classical.choose_spec
    (Graph.ColdCorridor.Corridor.FirstFailureGermWitness.exists_traceEnd
      (Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold)
      (Graph.cycleTargetInterface data.LengthOK).isomorphismInvariant
      (corridorAt epsilon) (presentationAt epsilon) (indexAt epsilon)
      (outsideIncidence epsilon) (stateFacts epsilon).2.2.2)
  let firstFailureGerm :=
    ColdFirstFailureGermOccurrence data object classified
  let firstFailureHandoff :=
    ColdFirstFailureHandoffOccurrence data object classified
  let stateOne := Classical.choose_spec state
  let stateTwo := Classical.choose_spec (Classical.choose_spec stateOne)
  let stateBundle := Classical.choose_spec (Classical.choose_spec stateTwo)
  let crossIncidence := coldRoutedCrossIncidence data object routing
  let crossFacts := Classical.choose_spec stateBundle.2.2.2.2.2
  let incidence := coldRoutedOccurrenceIncidence data object routing
  let candidates := coldRoutedCandidates data object routing
  have occurrenceStubInjective : Function.Injective
      (@ColdGermOccurrence.stub data object) := by
    intro left right same
    cases left with
    | inl left =>
        cases right with
        | inl right =>
            exact congrArg Sum.inl (Subtype.ext same)
        | inr right =>
            exfalso
            have targetSame := congrArg Prod.snd same
            exact left.property.2 (targetSame ▸ right.property.2)
    | inr left =>
        cases right with
        | inl right =>
            exfalso
            have targetSame := congrArg Prod.snd same
            exact right.property.2 (targetSame.symm ▸ left.property.2)
        | inr right =>
            exact congrArg Sum.inr (Subtype.ext same)
  have candidateFamily :
      Graph.ColdCorridor.CandidateGermOccurrenceFamily data.coldSignature
        data.threshold (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object incidence candidates := by
    apply Graph.ColdCorridor.overlap_card_le_of_vertex_multiplicity
      (support := fun epsilon => (incidence epsilon).support)
      (supportBound := Graph.ColdCorridor.exchangeBound data.coldSignature)
      (multiplicityBound :=
        Graph.ColdCorridor.overlapBound data.threshold data.coldSignature)
    · intro epsilon _epsilonMem
      exact (incidence epsilon).bounded
    · intro vertex
      let through := candidates.filter fun epsilon =>
        vertex ∈ (incidence epsilon).support
      let subcubic := object.vertexFinset.filter fun current =>
        object.degree current ≤ data.threshold
      let reach := @Graph.SubcubicReach.reach object.Vertex
        (@FinEnum.instFintype _ object.vertices) object.graph
        subcubic vertex
        (Graph.ColdCorridor.exchangeBound data.coldSignature + 2) vertex
      let sourceRegion := reach ∩ Graph.ColdCorridor.windowsOf object cubic
      have throughToIncidences : through.card ≤
          (object.incidences.filter fun pair : object.Vertex × object.Vertex =>
            pair.1 ∈ sourceRegion).card := by
        exact Finset.card_le_card_of_injOn
          (@ColdGermOccurrence.stub data object)
          (by
            intro occurrence occurrenceMem
            have occurrenceCandidate :=
              (Finset.mem_filter.1 occurrenceMem).1
            have vertexMem := (Finset.mem_filter.1 occurrenceMem).2
            have selectedMem : ColdGermOccurrence.stub occurrence ∈
                Graph.ColdCorridor.allSelectedStubs object cubic := by
              cases occurrence with
              | inl epsilon => exact epsilon.property.1
              | inr epsilon => exact epsilon.property.1
            let selected : Selected :=
              ⟨ColdGermOccurrence.stub occurrence, selectedMem⟩
            have selectedFacts :=
              Graph.ColdCorridor.selected_facts object cubic selected
            have sourceReach :
                (ColdGermOccurrence.stub occurrence).1 ∈ reach := by
              cases occurrence with
              | inl epsilon =>
                  have prefixSubcubic :
                      ∀ current ∈ (corridorAt epsilon).prefixSupport
                          (traceEnd epsilon),
                        object.degree current ≤ data.threshold :=
                    (Finset.mem_filter.1 occurrenceCandidate).2.2
                  have facts := stateFacts epsilon
                  have sourceSubcubic :
                      object.degree (corridorAt epsilon).entryStub.2 ≤
                        data.threshold := by
                    obtain ⟨window, windowMem, stubMem⟩ :=
                      (Graph.ColdCorridor.mem_windowsOf object cubic
                        epsilon.1.1).1 selectedFacts.1
                    have ambient := (Finset.mem_filter.1 windowMem).2
                    have entryEq : (corridorAt epsilon).entryStub.2 =
                        epsilon.1.1 := by
                      simpa only [corridorAt, coldOccurrenceCorridorAt] using
                        congrArg Prod.snd facts.2.1
                    rw [entryEq]
                    exact le_of_eq (ambient epsilon.1.1 stubMem)
                  have vertexMemOutside :
                      vertex ∈ (outsideIncidence epsilon).support := by
                    simpa [incidence] using vertexMem
                  have reached :=
                    Graph.ColdCorridor.Corridor.FirstFailureGermWitness.source_mem_subcubicReach_of_trace
                      (corridorAt epsilon) (outsideIncidence epsilon)
                      (traceEnd epsilon) (traceFacts epsilon).1
                      (traceFacts epsilon).2 data.threshold
                      prefixSubcubic sourceSubcubic vertexMemOutside
                  have entryEq : (corridorAt epsilon).entryStub.2 =
                      epsilon.1.1 := by
                    simpa only [corridorAt, coldOccurrenceCorridorAt] using
                      congrArg Prod.snd facts.2.1
                  rw [entryEq] at reached
                  exact reached
              | inr epsilon =>
                  have supportBound : ∀ current ∈
                      (crossIncidence epsilon).support,
                        object.degree current ≤ data.threshold :=
                    (Finset.mem_filter.1 occurrenceCandidate).2
                  have sourceBound :
                      object.degree epsilon.1.1 ≤ data.threshold := by
                    apply supportBound epsilon.1.1
                    rw [crossFacts epsilon]
                    simp
                  have targetBound :
                      object.degree epsilon.1.2 ≤ data.threshold := by
                    apply supportBound epsilon.1.2
                    rw [crossFacts epsilon]
                    simp
                  have vertexPair : vertex = epsilon.1.1 ∨
                      vertex = epsilon.1.2 := by
                    rw [crossFacts epsilon] at vertexMem
                    simpa using vertexMem
                  rcases vertexPair with rfl | rfl
                  · exact Graph.SubcubicReach.self_mem_reach object.graph
                      subcubic epsilon.1.1
                      (Graph.ColdCorridor.exchangeBound
                        data.coldSignature + 2) epsilon.1.1
                  · exact Graph.SubcubicReach.adjacent_mem_reach object.graph
                      subcubic selectedFacts.2.symm
                      (Finset.mem_filter.2
                        ⟨Finset.mem_univ _, targetBound⟩)
                      selectedFacts.2.ne (by omega)
            refine Finset.mem_filter.2
              ⟨(object.mem_incidences_iff
                  (ColdGermOccurrence.stub occurrence)).2 selectedFacts.2, ?_⟩
            exact Finset.mem_inter.2
              ⟨sourceReach, selectedFacts.1⟩)
          (by
            intro left _leftMem right _rightMem same
            exact occurrenceStubInjective same)
      calc
        through.card ≤
            (object.incidences.filter
              fun pair : object.Vertex × object.Vertex =>
                pair.1 ∈ sourceRegion).card := throughToIncidences
        _ ≤ Graph.ColdCorridor.overlapBound data.threshold
            data.coldSignature :=
          Graph.ColdCorridor.card_incidences_reach_windows_le_overlapBound
            object cubic data.coldSignature data.threshold
            thresholdEq threeLeOrder
            (fun _window windowMem => (Finset.mem_filter.1 windowMem).2)
            vertex
  obtain ⟨disjointFamily, extracted⟩ :=
    (Graph.ColdCorridor.coldGermOccurrenceExtractionLocal
      (S := data.coldSignature) (threshold := data.threshold)
      (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
      (Target := Graph.HasCycleWithLength data.LengthOK) (object := object))
      Occurrence (Classical.decEq Occurrence) incidence candidates
      candidateFamily
  have failureClassified : ∀ epsilon : Eligible,
      (∀ vertex ∈ (corridorAt epsilon).prefixSupport (traceEnd epsilon),
        object.degree vertex ≤ data.threshold) →
      firstFailureGerm epsilon :=
    fun epsilon subcubic =>
      coldSubcubicFirstFailureGerm data object routing epsilon subcubic
  have noncandidateClassified : ∀ occurrence : Occurrence,
      occurrence ∉ candidates →
        ∃ charged root : object.Vertex,
          data.threshold < object.degree charged ∧
            object.graph.Adj charged root ∧
            object.degree root ≤ data.threshold ∧
            (ColdGermOccurrence.stub occurrence).1 ∈
              @Graph.SubcubicReach.reach object.Vertex
                (@FinEnum.instFintype _ object.vertices) object.graph
                (object.vertexFinset.filter fun current =>
                  object.degree current ≤ data.threshold)
                root
                (Graph.ColdCorridor.exchangeBound data.coldSignature + 2)
                root := by
    intro occurrence notCandidate
    cases occurrence with
    | inl epsilon =>
        rcases handoff state epsilon with subcubic | high
        · exfalso
          apply notCandidate
          exact Finset.mem_filter.2
            ⟨Finset.mem_univ _, failureClassified epsilon subcubic, subcubic⟩
        · obtain ⟨first, _bound, firstHigh, _earlier,
              root, adjacent, rootSubcubic, sourceReach⟩ := high
          exact ⟨(corridorAt epsilon).head first, root, firstHigh,
            adjacent, rootSubcubic, sourceReach⟩
    | inr epsilon =>
        have notSubcubic : ¬ ∀ vertex ∈
            (crossIncidence epsilon).support,
              object.degree vertex ≤ data.threshold := by
          intro subcubic
          exact notCandidate (Finset.mem_filter.2
            ⟨Finset.mem_univ _, subcubic⟩)
        push_neg at notSubcubic
        obtain ⟨charged, chargedMem, chargedHigh⟩ := notSubcubic
        have chargedPair : charged = epsilon.1.1 ∨
            charged = epsilon.1.2 := by
          rw [crossFacts epsilon] at chargedMem
          simpa using chargedMem
        have selectedFacts := Graph.ColdCorridor.selected_facts object cubic
          (⟨epsilon.1, epsilon.property.1⟩ : Selected)
        obtain ⟨sourceWindow, sourceWindowMem, sourceMem⟩ :=
          (Graph.ColdCorridor.mem_windowsOf object cubic epsilon.1.1).1
            selectedFacts.1
        have sourceDegree : object.degree epsilon.1.1 = data.threshold :=
          (Finset.mem_filter.1 sourceWindowMem).2 epsilon.1.1 sourceMem
        have chargedEq : charged = epsilon.1.2 := by
          rcases chargedPair with sourceEq | targetEq
          · subst charged
            omega
          · exact targetEq
        subst charged
        refine ⟨epsilon.1.2, epsilon.1.1, chargedHigh,
          selectedFacts.2.symm, le_of_eq sourceDegree, ?_⟩
        exact Graph.SubcubicReach.self_mem_reach object.graph
          (object.vertexFinset.filter fun current =>
            object.degree current ≤ data.threshold)
          epsilon.1.1
          (Graph.ColdCorridor.exchangeBound data.coldSignature + 2)
          epsilon.1.1
  have eligibleUniverseCount : (Finset.univ : Finset Eligible).card =
      ((Graph.ColdCorridor.allSelectedStubs object cubic).filter
        fun stub => stub.2 ∉ windows).card :=
    Graph.card_univ_subtype_mem_and _ _
  have crossUniverseCount : (Finset.univ : Finset Cross).card =
      ((Graph.ColdCorridor.allSelectedStubs object cubic).filter
        fun stub => stub.2 ∈ windows).card :=
    Graph.card_univ_subtype_mem_and _ _
  have selectedPartition :
      (Graph.ColdCorridor.allSelectedStubs object cubic).card =
        ((Graph.ColdCorridor.allSelectedStubs object cubic).filter
            fun stub => stub.2 ∉ windows).card +
          ((Graph.ColdCorridor.allSelectedStubs object cubic).filter
            fun stub => stub.2 ∈ windows).card := by
    have partition := Finset.card_filter_add_card_filter_not
      (s := Graph.ColdCorridor.allSelectedStubs object cubic)
      (fun stub => stub.2 ∉ windows)
    simpa only [not_not] using partition.symm
  have occurrenceUniverseCount :
      (Finset.univ : Finset Occurrence).card =
        (Graph.ColdCorridor.allSelectedStubs object cubic).card := by
    calc
      (Finset.univ : Finset Occurrence).card = Fintype.card Occurrence :=
        Finset.card_univ
      _ = Fintype.card Eligible + Fintype.card Cross :=
        Fintype.card_sum
      _ = (Finset.univ : Finset Eligible).card +
            (Finset.univ : Finset Cross).card := by simp
      _ = (Graph.ColdCorridor.allSelectedStubs object cubic).card := by
        rw [eligibleUniverseCount, crossUniverseCount, selectedPartition]
  have candidateCount : candidates.card ≤
      (Finset.univ : Finset Occurrence).card :=
    Finset.card_le_card (Finset.subset_univ _)
  let corridorLoss :=
    (Finset.univ : Finset Occurrence).card - candidates.card
  have corridorCount : (Finset.univ : Finset Occurrence).card =
      candidates.card + corridorLoss := by
    simpa only [corridorLoss] using
      (Nat.add_sub_of_le candidateCount).symm
  have totalCount :
      (Graph.ColdCorridor.allSelectedStubs object cubic).card =
        candidates.card + corridorLoss := by
    rw [← occurrenceUniverseCount, corridorCount]
  let losses := (Finset.univ : Finset Occurrence).filter fun occurrence =>
    occurrence ∉ candidates
  have lossCard : losses.card = corridorLoss := by
    have partition := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset Occurrence))
      (fun occurrence => occurrence ∈ candidates)
    have candidateFilter :
        ((Finset.univ : Finset Occurrence).filter fun occurrence =>
          occurrence ∈ candidates) = candidates := by
      ext occurrence
      simp
    rw [candidateFilter] at partition
    have lossFilter :
        ((Finset.univ : Finset Occurrence).filter fun occurrence =>
          occurrence ∉ candidates) = losses := rfl
    rw [lossFilter] at partition
    omega
  let chargePair : Occurrence → object.Vertex × object.Vertex :=
    fun occurrence =>
      if missing : occurrence ∉ candidates then
        let witness := noncandidateClassified occurrence missing
        (Classical.choose witness,
          Classical.choose (Classical.choose_spec witness))
      else
        ((ColdGermOccurrence.stub occurrence).1,
          (ColdGermOccurrence.stub occurrence).1)
  have chargeFacts : ∀ occurrence : Occurrence,
      occurrence ∉ candidates →
        data.threshold < object.degree (chargePair occurrence).1 ∧
          object.graph.Adj (chargePair occurrence).1
            (chargePair occurrence).2 ∧
          object.degree (chargePair occurrence).2 ≤ data.threshold ∧
          (ColdGermOccurrence.stub occurrence).1 ∈
            @Graph.SubcubicReach.reach object.Vertex
              (@FinEnum.instFintype _ object.vertices) object.graph
              (object.vertexFinset.filter fun current =>
                object.degree current ≤ data.threshold)
              (chargePair occurrence).2
              (Graph.ColdCorridor.exchangeBound data.coldSignature + 2)
              (chargePair occurrence).2 := by
    intro occurrence missing
    dsimp only [chargePair]
    rw [dif_pos missing]
    exact Classical.choose_spec
      (Classical.choose_spec (noncandidateClassified occurrence missing))
  let highIncidences := object.incidences.filter
    fun pair : object.Vertex × object.Vertex =>
      data.threshold < object.degree pair.1 ∧
        object.degree pair.2 ≤ data.threshold
  let sourceFibre := fun pair : object.Vertex × object.Vertex =>
    (Finset.univ : Finset Occurrence).filter fun occurrence =>
      (ColdGermOccurrence.stub occurrence).1 ∈
        @Graph.SubcubicReach.reach object.Vertex
          (@FinEnum.instFintype _ object.vertices) object.graph
          (object.vertexFinset.filter fun current =>
            object.degree current ≤ data.threshold)
          pair.2
          (Graph.ColdCorridor.exchangeBound data.coldSignature + 2)
          pair.2
  have lossesCovered : losses ⊆ highIncidences.biUnion sourceFibre := by
    intro occurrence occurrenceMem
    have missing := (Finset.mem_filter.1 occurrenceMem).2
    have facts := chargeFacts occurrence missing
    have chargeMember : chargePair occurrence ∈ highIncidences := by
      refine Finset.mem_filter.2
        ⟨(object.mem_incidences_iff (chargePair occurrence)).2 facts.2.1,
          facts.1, facts.2.2.1⟩
    exact Finset.mem_biUnion.2
      ⟨chargePair occurrence, chargeMember,
        Finset.mem_filter.2 ⟨Finset.mem_univ _, facts.2.2.2⟩⟩
  have sourceFibreBound : ∀ pair ∈ highIncidences,
      (sourceFibre pair).card ≤
        Graph.ColdCorridor.overlapBound data.threshold
          data.coldSignature := by
    intro pair pairMem
    let subcubic := object.vertexFinset.filter fun current =>
      object.degree current ≤ data.threshold
    let reach := @Graph.SubcubicReach.reach object.Vertex
      (@FinEnum.instFintype _ object.vertices) object.graph
      subcubic pair.2
      (Graph.ColdCorridor.exchangeBound data.coldSignature + 2) pair.2
    let sourceRegion := reach ∩ Graph.ColdCorridor.windowsOf object cubic
    have fibreToIncidences : (sourceFibre pair).card ≤
        (object.incidences.filter fun incidencePair :
            object.Vertex × object.Vertex =>
          incidencePair.1 ∈ sourceRegion).card := by
      exact Finset.card_le_card_of_injOn
        (@ColdGermOccurrence.stub data object)
        (by
          intro occurrence occurrenceMem
          have sourceReach := (Finset.mem_filter.1 occurrenceMem).2
          have selectedMem : ColdGermOccurrence.stub occurrence ∈
              Graph.ColdCorridor.allSelectedStubs object cubic := by
            cases occurrence with
            | inl epsilon => exact epsilon.property.1
            | inr epsilon => exact epsilon.property.1
          have selectedFacts := Graph.ColdCorridor.selected_facts object cubic
            (⟨ColdGermOccurrence.stub occurrence, selectedMem⟩ : Selected)
          refine Finset.mem_filter.2
            ⟨(object.mem_incidences_iff
                (ColdGermOccurrence.stub occurrence)).2 selectedFacts.2, ?_⟩
          exact Finset.mem_inter.2 ⟨sourceReach, selectedFacts.1⟩)
        (by
          intro left _leftMem right _rightMem same
          exact occurrenceStubInjective same)
    calc
      (sourceFibre pair).card ≤
          (object.incidences.filter fun incidencePair :
              object.Vertex × object.Vertex =>
            incidencePair.1 ∈ sourceRegion).card := fibreToIncidences
      _ ≤ Graph.ColdCorridor.overlapBound data.threshold
          data.coldSignature :=
        Graph.ColdCorridor.card_incidences_reach_windows_le_overlapBound
          object cubic data.coldSignature data.threshold
          thresholdEq threeLeOrder
          (fun _window windowMem => (Finset.mem_filter.1 windowMem).2)
          pair.2
  have lossesPerHighIncidence : losses.card ≤
      highIncidences.card *
        Graph.ColdCorridor.overlapBound data.threshold
          data.coldSignature := by
    calc
      losses.card ≤ (highIncidences.biUnion sourceFibre).card :=
        Finset.card_le_card lossesCovered
      _ ≤ ∑ pair ∈ highIncidences, (sourceFibre pair).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _pair ∈ highIncidences,
            Graph.ColdCorridor.overlapBound data.threshold
              data.coldSignature :=
        Finset.sum_le_sum sourceFibreBound
      _ = highIncidences.card *
            Graph.ColdCorridor.overlapBound data.threshold
              data.coldSignature := by simp
  let highVertices := (Finset.univ : Finset object.Vertex).filter
    fun vertex => data.threshold < object.degree vertex
  let incidencesFromHigh := object.incidences.filter
    fun pair : object.Vertex × object.Vertex => pair.1 ∈ highVertices
  have highIncidencesSubset : highIncidences ⊆ incidencesFromHigh := by
    intro pair pairMem
    have facts := (Finset.mem_filter.1 pairMem).2
    exact Finset.mem_filter.2
      ⟨(Finset.mem_filter.1 pairMem).1,
        Finset.mem_filter.2 ⟨Finset.mem_univ _, facts.1⟩⟩
  have incidencesFromHighBound : incidencesFromHigh.card ≤
      ∑ vertex ∈ highVertices, object.degree vertex := by
    dsimp only [incidencesFromHigh]
    exact Graph.ColdCorridor.card_incidences_filter_fst_le_sum_degree
      object highVertices
  have highDegreeSumBound :
      (∑ vertex ∈ highVertices, object.degree vertex) ≤
        (data.threshold + 1) *
          object.ambientSurplus highVertices data.threshold := by
    unfold Graph.FiniteObject.ambientSurplus
    calc
      (∑ vertex ∈ highVertices, object.degree vertex) ≤
          ∑ vertex ∈ highVertices,
            (data.threshold + 1) *
              (object.degree vertex - data.threshold) := by
        exact Finset.sum_le_sum fun vertex vertexMem => by
          have high := (Finset.mem_filter.1 vertexMem).2
          have oneLe : 1 ≤ object.degree vertex - data.threshold := by
            omega
          have multiplied := Nat.mul_le_mul_left data.threshold oneLe
          have multiplied' : data.threshold ≤ data.threshold *
              (object.degree vertex - data.threshold) := by
            calc
              data.threshold = data.threshold * 1 := by simp
              _ ≤ data.threshold *
                  (object.degree vertex - data.threshold) := multiplied
          calc
            object.degree vertex = data.threshold +
                (object.degree vertex - data.threshold) := by omega
            _ ≤ data.threshold *
                  (object.degree vertex - data.threshold) +
                (object.degree vertex - data.threshold) :=
              Nat.add_le_add_right multiplied'
                (object.degree vertex - data.threshold)
            _ = (data.threshold + 1) *
                (object.degree vertex - data.threshold) := by ring
      _ = (data.threshold + 1) *
            ∑ vertex ∈ highVertices,
              (object.degree vertex - data.threshold) := by
        exact (Finset.mul_sum highVertices
          (fun vertex => object.degree vertex - data.threshold)
          (data.threshold + 1)).symm
  have baselineDegree : ∀ vertex : object.Vertex,
      data.threshold ≤ object.degree vertex := fun vertex =>
    le_trans baseline (object.minDegree_le_degree vertex)
  have highIncidencesBound : highIncidences.card ≤
      (data.threshold + 1) * object.degreeSurplus data.threshold := by
    calc
      highIncidences.card ≤ incidencesFromHigh.card :=
        Finset.card_le_card highIncidencesSubset
      _ ≤ ∑ vertex ∈ highVertices, object.degree vertex :=
        incidencesFromHighBound
      _ ≤ (data.threshold + 1) *
            object.ambientSurplus highVertices data.threshold :=
        highDegreeSumBound
      _ ≤ (data.threshold + 1) *
            object.degreeSurplus data.threshold :=
        Nat.mul_le_mul_left _
          (object.ambientSurplus_le_degreeSurplus highVertices
            data.threshold baselineDegree)
  have routedLossBound : corridorLoss ≤
      (data.threshold + 1) *
        Graph.ColdCorridor.overlapBound data.threshold
          data.coldSignature * object.degreeSurplus data.threshold := by
    calc
      corridorLoss = losses.card := lossCard.symm
      _ ≤ highIncidences.card *
            Graph.ColdCorridor.overlapBound data.threshold
              data.coldSignature := lossesPerHighIncidence
      _ ≤ ((data.threshold + 1) *
            object.degreeSurplus data.threshold) *
            Graph.ColdCorridor.overlapBound data.threshold
              data.coldSignature :=
        Nat.mul_le_mul_right _ highIncidencesBound
      _ = (data.threshold + 1) *
            Graph.ColdCorridor.overlapBound data.threshold
              data.coldSignature * object.degreeSurplus data.threshold := by
        ring
  have quantitative :
      (Graph.ColdCorridor.allSelectedStubs object cubic).card ≤
        disjointFamily.card *
            Graph.ColdCorridor.extractionDenominator data.threshold
              data.coldSignature +
          corridorLoss := by
    have cover := extracted.2.2
    omega
  change ColdGermCandidatesStatement data object
  simp only [ColdGermCandidatesStatement]
  refine ⟨routing, incidence, candidates, disjointFamily, corridorLoss,
    ?_⟩
  simp only [ColdGermFamilyWitness]
  exact ⟨rfl, rfl, candidateFamily, extracted,
    noncandidateClassified, corridorCount, totalCount,
    routedLossBound, quantitative⟩


end Hypostructure.Graph.Contracts.Spine
