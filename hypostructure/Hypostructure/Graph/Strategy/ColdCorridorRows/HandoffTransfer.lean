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

/-- The first-high handoff conclusion obtained from the retained corridor
state.  This is the manuscript's bounded-prefix/high-degree dichotomy. -/
theorem coldHandoffTransferFact
    {data : Data.{u}} {object : Graph.FiniteObject.{u}}
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

/-- Node `[153]`: publish the bounded-prefix/first-high handoff conclusion
from the retained corridor state. -/
@[reducible] noncomputable def coldHandoffTransferRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldHandoffTransfer
    { Requires := [K .coldCorridorState]
      Produces := [K .coldHandoffTransfer]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let state := (inputs.get (K .coldCorridorState)).down
      .cons (key := K .coldHandoffTransfer)
        ⟨coldHandoffTransferFact state⟩ .nil)

end Hypostructure.Graph.Strategy.Spine
