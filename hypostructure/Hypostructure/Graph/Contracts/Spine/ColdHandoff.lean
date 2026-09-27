import Hypostructure.Graph.Statements.Spine
import Hypostructure.Graph.ColdIncrementArithmetic
import Hypostructure.Graph.ColdGermFamily
import Hypostructure.Graph.Contracts.Spine.ColdSubcubicCharge

/-!
# Contracts: the first-high handoff of `lem:cold-germ-extraction` `[153]`

Proof-agnostic contract lemmas for the bounded-prefix/first-high dichotomy of
the retained cold corridors.  Each lemma is stated over a `Graph.FiniteObject`
with the registered `Parameters` as a parameter and every paper hypothesis
explicit; its conclusion is exactly the statement of the fact it proves.  This
module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Contracts.Spine

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

/-- The least high-degree segment of a non-subcubic retained prefix. -/
theorem coldFirstHighOfNotBounded
    {object : Graph.FiniteObject.{u}}
    {windows component : Finset object.Vertex}
    (corridor : Graph.ColdCorridor.Corridor object windows component)
    (n threshold : Nat)
    (notBounded : ¬ ∀ vertex ∈ corridor.prefixSupport n,
      object.degree vertex ≤ threshold) :
    ∃ first : corridor.Segment,
      first.1 ≤ n ∧ threshold < object.degree (corridor.head first) ∧
        ∀ earlier : corridor.Segment, earlier.1 < first.1 →
          object.degree (corridor.head earlier) ≤ threshold := by
  classical
  push Not at notBounded
  obtain ⟨vertex, vertexMember, vertexHigh⟩ := notBounded
  obtain ⟨inner, innerMember, innerEq⟩ :=
    (corridor.mem_prefixSupport n vertex).1 vertexMember
  obtain ⟨segmentIndex, indexEq, _indexBound⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp innerMember
  have segmentBound : segmentIndex ≤ n := by
    have takeLength := SimpleGraph.Walk.take_length corridor.inside.1 n
    omega
  have segmentIndexLt : segmentIndex < corridor.inside.1.length + 1 := by
    have takeLength := SimpleGraph.Walk.take_length corridor.inside.1 n
    have lengthBound : (corridor.inside.1.take n).length ≤
        corridor.inside.1.length := by omega
    omega
  let segment : corridor.Segment := ⟨segmentIndex, segmentIndexLt⟩
  have headEq : corridor.head segment = vertex := by
    have takeEq : (corridor.inside.1.take n).getVert segmentIndex =
        corridor.inside.1.getVert segmentIndex := by
      rw [SimpleGraph.Walk.take_getVert]
      simp [Nat.min_eq_right segmentBound]
    exact congrArg Subtype.val (takeEq.symm.trans indexEq) |>.trans innerEq
  let highSegments : Finset corridor.Segment :=
    Finset.univ.filter fun current =>
      current.1 ≤ n ∧ threshold < object.degree (corridor.head current)
  have highNonempty : highSegments.Nonempty := by
    refine ⟨segment, Finset.mem_filter.2
      ⟨Finset.mem_univ _, segmentBound, ?_⟩⟩
    simpa [headEq] using vertexHigh
  let first := highSegments.min' highNonempty
  have firstMember : first ∈ highSegments :=
    Finset.min'_mem highSegments highNonempty
  have firstFacts := (Finset.mem_filter.1 firstMember).2
  refine ⟨first, firstFacts.1, firstFacts.2, ?_⟩
  intro earlier earlierBefore
  apply le_of_not_gt
  intro earlierHigh
  have earlierMember : earlier ∈ highSegments :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _,
      le_trans (Nat.le_of_lt earlierBefore) firstFacts.1, earlierHigh⟩
  have firstLeEarlier := Finset.min'_le highSegments earlier earlierMember
  exact (Nat.not_lt_of_ge firstLeEarlier) earlierBefore

set_option maxHeartbeats 800000 in
/-- The first-high handoff conclusion obtained from the retained corridor
state.  This is the manuscript's bounded-prefix/high-degree dichotomy. -/
theorem coldHandoffTransfer_of_state
    (data : Parameters) (object : Graph.FiniteObject.{u})
    (state : ColdCorridorStateStatement data object) :
    ColdFirstHighHandoffStatement data object := by
  classical
  change ColdFirstHighHandoffStatement data object
  simp only [ColdFirstHighHandoffStatement]
  letI : FinEnum object.Vertex := object.vertices
  letI : Fintype object.Vertex := @FinEnum.instFintype _ object.vertices
  let cold := canonicalColdWindows data object
  let cubic := cold.filter (AmbientCubicWindow data object)
  let windows := coldCorridorWindows data object
  intro retained
  have retainedEq : retained = state := Subsingleton.elim _ _
  subst retained
  intro epsilon
  let incidence := Classical.choose state
  let stateOne := Classical.choose_spec state
  let componentAt := Classical.choose stateOne
  let stateTwo := Classical.choose_spec stateOne
  let corridorAt := Classical.choose stateTwo
  let stateTail := Classical.choose_spec stateTwo
  let presentationAt := Classical.choose stateTail
  let indexAt := Classical.choose (Classical.choose_spec stateTail)
  let stateFacts := (Classical.choose_spec
    (Classical.choose_spec stateTail)).1
  let traceEnd := fun routed : ColdEligibleHalfEdge data object =>
    Classical.choose
      (Graph.ColdCorridor.Corridor.FirstFailureGermWitness.exists_traceEnd
        (Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold)
        (Graph.cycleTargetInterface data.LengthOK).isomorphismInvariant
        (corridorAt routed) (presentationAt routed) (indexAt routed)
        (incidence routed) (stateFacts routed).2.2.2)
  by_cases subcubic : ∀ vertex ∈
      (corridorAt epsilon).prefixSupport (traceEnd epsilon),
        object.degree vertex ≤ data.threshold
  · exact Or.inl subcubic
  · obtain ⟨first, firstBound, firstHigh, earlierBound⟩ :=
      coldFirstHighOfNotBounded (corridorAt epsilon)
        (traceEnd epsilon) data.threshold subcubic
    refine Or.inr ⟨first, firstBound, firstHigh, earlierBound, ?_⟩
    let corridor := corridorAt epsilon
    have entryWindowFacts := Classical.choose_spec
      ((Graph.ColdCorridor.mem_windowsOf object cubic epsilon.1.1).1
        (Graph.ColdCorridor.selected_facts object cubic
          (⟨epsilon.1, epsilon.2.1⟩ : ColdSelectedHalfEdge data object)).1)
    have sourceSubcubic : object.degree epsilon.1.1 ≤ data.threshold := by
      exact le_of_eq ((Finset.mem_filter.1 entryWindowFacts.1).2
        epsilon.1.1 entryWindowFacts.2)
    by_cases firstZero : first.1 = 0
    · let root := epsilon.1.1
      have headEq : corridor.head first = epsilon.1.2 := by
        simpa [corridor, corridorAt, Graph.ColdCorridor.Corridor.head,
          Graph.ColdCorridor.Corridor.entryStub,
          Graph.ColdCorridor.stubFoot, firstZero] using
            congrArg Prod.fst (stateFacts epsilon).2.1
      have adjacent : object.graph.Adj (corridor.head first) root := by
        rw [headEq]
        exact (Graph.ColdCorridor.selected_facts object cubic
          (⟨epsilon.1, epsilon.2.1⟩ :
            ColdSelectedHalfEdge data object)).2.symm
      refine ⟨root, adjacent, sourceSubcubic, ?_⟩
      refine (Graph.SubcubicReach.mem_reach object.graph).2
        ⟨SimpleGraph.Walk.nil, by simp, by simp, ?_, ?_⟩
      · simp
      · simp
    · have firstPositive : 0 < first.1 := Nat.pos_of_ne_zero firstZero
      let previous : corridor.Segment := ⟨first.1 - 1, by
        dsimp [corridor]
        omega⟩
      let root := corridor.head previous
      have previousBefore : previous.1 < first.1 := by
        dsimp [previous]
        omega
      have rootSubcubic : object.degree root ≤ data.threshold :=
        earlierBound previous previousBefore
      have adjacent : object.graph.Adj (corridor.head first) root := by
        have step := corridor.inside.1.adj_getVert_succ
          (i := previous.1) (by
            change previous.1 < (corridorAt epsilon).inside.1.length
            have firstLt := first.2
            dsimp [previous]
            omega)
        change object.graph.Adj
          (corridor.inside.1.getVert first.1).1
          (corridor.inside.1.getVert previous.1).1
        have succEq : previous.1 + 1 = first.1 := by
          dsimp [previous]
          omega
        rw [← succEq]
        exact step.symm
      have prefixSubcubic : ∀ vertex ∈
          corridor.prefixSupport previous.1,
            object.degree vertex ≤ data.threshold := by
        intro vertex member
        obtain ⟨inner, innerMember, innerEq⟩ :=
          (corridor.mem_prefixSupport previous.1 vertex).1 member
        obtain ⟨segmentIndex, indexEq, indexBound⟩ :=
          SimpleGraph.Walk.mem_support_iff_exists_getVert.mp innerMember
        have segmentLe : segmentIndex ≤ previous.1 := by
          have takeLength := SimpleGraph.Walk.take_length
            corridor.inside.1 previous.1
          omega
        let segment : corridor.Segment :=
          ⟨segmentIndex, by
            have previousLt : previous.1 < corridor.inside.1.length := by
              change previous.1 < (corridorAt epsilon).inside.1.length
              have firstLt := first.2
              dsimp [previous]
              omega
            omega⟩
        have segmentBefore : segment.1 < first.1 :=
          lt_of_le_of_lt segmentLe previousBefore
        have headEq : corridor.head segment = vertex := by
          have takeEq :
              (corridor.inside.1.take previous.1).getVert segmentIndex =
                corridor.inside.1.getVert segmentIndex := by
            rw [SimpleGraph.Walk.take_getVert]
            simp [Nat.min_eq_right segmentLe]
          exact congrArg Subtype.val
            (takeEq.symm.trans indexEq) |>.trans innerEq
        simpa [corridor, headEq] using earlierBound segment segmentBefore
      let short := corridor.inside.1.take previous.1
      let embedding := object.induceEmbedding (componentAt epsilon)
      let backwards := short.reverse.map embedding.toHom
      have shortEnd :
          embedding (corridor.inside.1.getVert previous.1) = root := rfl
      have shortStart : embedding
          (Graph.ColdCorridor.stubFoot object windows
            (componentAt epsilon) corridor.entry) =
            corridor.entryStub.1 := rfl
      let toFoot : object.graph.Walk root corridor.entryStub.1 :=
        backwards.copy shortEnd shortStart
      have entryMember : corridor.entryStub ∈
          Graph.ColdCorridor.boundaryStubs object windows
            (componentAt epsilon) := List.get_mem _ _
      have entryAdjacent : object.graph.Adj corridor.entryStub.1
          corridor.entryStub.2 :=
        ((Graph.ColdCorridor.mem_boundaryStubs_iff object windows
          (componentAt epsilon) corridor.entryStub).1 entryMember).2.2
      let joined : object.graph.Walk root corridor.entryStub.2 :=
        toFoot.concat entryAdjacent
      have sourceEq : corridor.entryStub.2 = epsilon.1.1 :=
        congrArg Prod.snd (stateFacts epsilon).2.1
      let sourceWalk : object.graph.Walk root epsilon.1.1 :=
        joined.copy rfl sourceEq
      let path := sourceWalk.toPath
      refine ⟨root, adjacent, rootSubcubic, ?_⟩
      refine (Graph.SubcubicReach.mem_reach object.graph).2
        ⟨path.1, path.2, ?_, ?_, ?_⟩
      · calc
          path.1.length ≤ sourceWalk.length :=
            sourceWalk.length_bypass_le_length
          _ = short.length + 1 := by
            simp [sourceWalk, joined, toFoot, backwards]
          _ ≤ previous.1 + 1 := by
            simp [short, SimpleGraph.Walk.take_length]
          _ ≤ Graph.ColdCorridor.exchangeBound data.coldSignature + 2 := by
            have stateBound : traceEnd epsilon ≤
                Graph.ColdCorridor.stateBound data.coldSignature := by
              dsimp [traceEnd]
              exact (Classical.choose_spec
                (Graph.ColdCorridor.Corridor.FirstFailureGermWitness.exists_traceEnd
                  (Graph.minimumDegreeAtLeast_isomorphismInvariant
                    data.threshold)
                  (Graph.cycleTargetInterface data.LengthOK).isomorphismInvariant
                  corridor (presentationAt epsilon) (indexAt epsilon)
                  (incidence epsilon) (stateFacts epsilon).2.2.2)).1
            unfold Graph.ColdCorridor.exchangeBound
            dsimp [previous]
            omega
      · intro current currentMember
        have currentSourceWalk : current ∈ sourceWalk.support :=
          SimpleGraph.Walk.support_toPath_subset_support sourceWalk
            (List.mem_of_mem_dropLast currentMember)
        simp only [sourceWalk, SimpleGraph.Walk.support_copy,
          joined, SimpleGraph.Walk.support_concat,
          List.mem_append, List.mem_singleton] at currentSourceWalk
        rcases currentSourceWalk with currentBackwards | currentSource
        · simp only [toFoot, SimpleGraph.Walk.support_copy,
            backwards, SimpleGraph.Walk.support_map,
            SimpleGraph.Walk.support_reverse, List.mem_map]
            at currentBackwards
          obtain ⟨inner, innerMember, innerEq⟩ := currentBackwards
          refine Finset.mem_filter.2 ⟨object.mem_vertexFinset _, ?_⟩
          apply prefixSubcubic current
          exact (corridor.mem_prefixSupport previous.1 current).2
            ⟨inner, by simpa [short] using innerMember, innerEq⟩
        · refine Finset.mem_filter.2 ⟨object.mem_vertexFinset _, ?_⟩
          simpa [currentSource, sourceEq] using sourceSubcubic
      · intro nonnil same
        have firstAdjacent := path.1.adj_getVert_succ
          (i := 0) (by
            simpa [SimpleGraph.Walk.not_nil_iff_lt_length] using nonnil)
        exact firstAdjacent.ne
          (by simpa [SimpleGraph.Walk.getVert_zero, same])

/-- **An (F4)-routed half-edge is not a germ candidate.** -/
theorem coldHandoffOccurrence_not_candidate (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (routing : ColdFailureRoutingStatement data object)
    (epsilon : ColdEligibleHalfEdge data object)
    (handoff : ColdFirstFailureHandoffOccurrence data object
      (coldRoutedClassified data object routing) epsilon) :
    (Sum.inl epsilon : ColdGermOccurrence data object) ∉
      coldRoutedCandidates data object routing := by
  classical
  intro member
  have facts := (Finset.mem_filter.1 member).2
  exact coldHandoffOccurrence_not_subcubic data object routing epsilon
    handoff facts.2

open Classical in
/-- **The (F4) count is inside the corridor loss** (`lem:cold-germ-extraction`,
tex 7318-7329, with G's heavy-centre (F4) registry).  On the node-`[153]`
witness published by `K .coldGermCandidates`, the (F4)-routed half-edges
together with every other non-candidate eligible half-edge (the (F5) ones whose
trace is not subcubic) are counted by the existing first-high loss:

`#{ε eligible : ε ∉ candidates} ≤ corridorLoss ≤ (δ+1)·B_cold·σ(G)`,

and `#{ε : first failure (F4)} ≤ #{ε eligible : ε ∉ candidates}`.  No new
term, no `o(n)`. -/
theorem coldF4_card_le_corridorLoss (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (routing : ColdFailureRoutingStatement data object)
    (incidence : ColdGermOccurrence data object →
      Graph.ColdCorridor.BoundedGerm data.coldSignature
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object)
    (candidates disjointFamily : Finset (ColdGermOccurrence data object))
    (corridorLoss : Nat)
    (witness : ColdGermFamilyWitness data object routing incidence candidates
      disjointFamily corridorLoss) :
    (Finset.univ.filter (ColdFirstFailureHandoffOccurrence data object
        (coldRoutedClassified data object routing))).card ≤
      (Finset.univ.filter (fun epsilon : ColdEligibleHalfEdge data object =>
        (Sum.inl epsilon : ColdGermOccurrence data object) ∉ candidates)).card ∧
    (Finset.univ.filter (fun epsilon : ColdEligibleHalfEdge data object =>
        (Sum.inl epsilon : ColdGermOccurrence data object) ∉ candidates)).card ≤
      corridorLoss ∧
    corridorLoss ≤ (data.threshold + 1) *
      Graph.ColdCorridor.overlapBound data.threshold data.coldSignature *
        object.degreeSurplus data.threshold := by
  obtain ⟨_incidenceEq, candidatesEq, _family, _extracted, _charged, total,
    _selected, lossBound, _extraction⟩ := witness
  refine ⟨?_, ?_, lossBound⟩
  · apply Finset.card_le_card
    intro epsilon member
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    rw [candidatesEq]
    exact coldHandoffOccurrence_not_candidate data object routing epsilon
      (Finset.mem_filter.1 member).2
  · -- the eligible non-candidates inject into the non-candidate occurrences
    have outsideCard : ((Finset.univ : Finset (ColdGermOccurrence data object)) \
        candidates).card = corridorLoss := by
      have := Finset.card_sdiff_add_card_inter
        (Finset.univ : Finset (ColdGermOccurrence data object)) candidates
      rw [Finset.univ_inter] at this
      omega
    rw [← outsideCard]
    refine Finset.card_le_card_of_injOn (fun epsilon => Sum.inl epsilon) ?_ ?_
    · intro epsilon member
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at member
      exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, member⟩
    · intro left _ right _ equal
      exact Sum.inl_injective equal

end Hypostructure.Graph.Contracts.Spine
