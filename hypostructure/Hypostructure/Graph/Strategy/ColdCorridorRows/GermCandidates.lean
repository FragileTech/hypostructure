import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.ColdIncrementArithmetic
import Hypostructure.Graph.ColdGermFamily
import Hypostructure.Graph.Strategy.ColdCorridorRows.Basic
import Hypostructure.Graph.ColdGermOverlap

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! ## Node `[153]`, `lem:cold-germ-extraction`: the (F5) candidate family

The candidates are exactly the manuscript's complete repaired occurrence
family: outside-corridor F5 prefixes and immediate two-vertex terminal germs
for selected cross-window incidences.  A noncandidate occurrence is charged
at its first high-to-subcubic edge; there is no separate conditional or
unbounded cross-window loss. -/
set_option maxHeartbeats 4000000 in
@[reducible] noncomputable def coldGermCandidatesRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldGermCandidates
    { Requires := [K .coldFailureRouting, K .coldGermExtraction,
        K .coldHandoffTransfer]
      Produces := [K .coldGermCandidates]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let routing := (inputs.get (K .coldFailureRouting)).down
      let extraction := (inputs.get (K .coldGermExtraction)).down
      let handoff := (inputs.get (K .coldHandoffTransfer)).down
      .cons (key := K .coldGermCandidates)
        ⟨by
          classical
          let object := inputs.current.object
          letI : FinEnum object.Vertex := object.vertices
          letI : DecidableEq object.Vertex := object.vertices.decEq
          letI : DecidableRel object.graph.Adj := object.decideAdj
          let cold := canonicalColdWindows data.toParameters object
          let cubic := cold.filter (AmbientCubicWindow data.toParameters object)
          let windows := coldCorridorWindows data.toParameters object
          let Eligible := ColdEligibleHalfEdge data.toParameters object
          let Cross := ColdCrossWindowHalfEdge data.toParameters object
          let Occurrence := ColdGermOccurrence data.toParameters object
          let Selected := ColdSelectedHalfEdge data.toParameters object
          change ColdFailureRoutingStatement data.toParameters object at routing
          let classified := coldRoutedClassified data.toParameters object routing
          let classification := Classical.choose_spec routing.surviving.holds
          let state := classified.state
          change ColdCorridorStateStatement data.toParameters object at state
          let outsideIncidence : Eligible →
              Graph.ColdCorridor.BoundedGerm data.coldSignature
                (Graph.MinimumDegreeAtLeast data.threshold)
                (Graph.HasCycleWithLength data.LengthOK) object :=
            coldOccurrenceIncidence data.toParameters object classified
          let corridorAt := coldOccurrenceCorridorAt data.toParameters object classified
          let presentationAt :=
            coldOccurrencePresentationAt data.toParameters object classified
          let indexAt := coldOccurrenceIndexAt data.toParameters object classified
          let stateFacts := coldOccurrenceStateFacts data.toParameters object classified
          let traceEnd := coldRoutedTraceEnd data.toParameters object routing
          let traceFacts := fun epsilon : Eligible => Classical.choose_spec
            (Graph.ColdCorridor.Corridor.FirstFailureGermWitness.exists_traceEnd
              (Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold)
              (Graph.cycleTargetInterface data.LengthOK).isomorphismInvariant
              (corridorAt epsilon) (presentationAt epsilon) (indexAt epsilon)
              (outsideIncidence epsilon) (stateFacts epsilon).2.2.2)
          let firstFailureGerm :=
            ColdFirstFailureGermOccurrence data.toParameters object classified
          let firstFailureHandoff :=
            ColdFirstFailureHandoffOccurrence data.toParameters object classified
          let stateOne := Classical.choose_spec state
          let stateTwo := Classical.choose_spec (Classical.choose_spec stateOne)
          let stateBundle := Classical.choose_spec (Classical.choose_spec stateTwo)
          let crossIncidence := coldRoutedCrossIncidence data.toParameters object routing
          let crossFacts := Classical.choose_spec stateBundle.2.2.2.2.2
          let incidence := coldRoutedOccurrenceIncidence data.toParameters object routing
          let candidates := coldRoutedCandidates data.toParameters object routing
          have occurrenceStubInjective : Function.Injective
              (@ColdGermOccurrence.stub data.toParameters object) := by
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
          change ColdExchangeBoundStatement data.toParameters object ∧
            Graph.ColdCorridor.ColdGermOccurrenceExtractionLocal data.coldSignature
              data.threshold (Graph.MinimumDegreeAtLeast data.threshold)
              (Graph.HasCycleWithLength data.LengthOK) object at extraction
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
                  (@ColdGermOccurrence.stub data.toParameters object)
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
                    data.threshold_eq_three data.three_le_windowOrder
                    (fun _window windowMem => (Finset.mem_filter.1 windowMem).2)
                    vertex
          obtain ⟨disjointFamily, extracted⟩ :=
            extraction.2 Occurrence (Classical.decEq Occurrence) incidence candidates
              candidateFamily
          have failureClassified : ∀ epsilon : Eligible,
              firstFailureGerm epsilon := by
            intro epsilon
            simpa only [firstFailureHandoff, firstFailureGerm] using
              classification epsilon
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
                    ⟨Finset.mem_univ _, failureClassified epsilon, subcubic⟩
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
                (@ColdGermOccurrence.stub data.toParameters object)
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
                  data.threshold_eq_three data.three_le_windowOrder
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
            le_trans inputs.current.baseline (object.minDegree_le_degree vertex)
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
          change ColdGermCandidatesStatement data.toParameters object
          simp only [ColdGermCandidatesStatement]
          refine ⟨routing, incidence, candidates, disjointFamily, corridorLoss,
            ?_⟩
          simp only [ColdGermFamilyWitness]
          exact ⟨rfl, rfl, candidateFamily, extracted,
            noncandidateClassified, corridorCount, totalCount,
            routedLossBound, quantitative⟩
        ⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
