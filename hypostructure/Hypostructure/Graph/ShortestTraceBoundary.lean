import Hypostructure.Graph.ReceiverRouting
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# The canonical trace is a shortest, chordless path

`FiniteObject.tracePath?` scans the object's complete finite path schedule
length-first, so the selected trace is no longer than any other trace-shaped
path between the same endpoints (`tracePath?_length_le`).  In particular it is
a shortest path inside the subgraph induced on its own vertex set, hence an
induced (chordless) path: every trace vertex has at most two neighbours on the
trace.  When every vertex of the support has ambient degree at least `3`, each
trace vertex therefore has a neighbour off the trace
(`tracePath?_support_exits`): the whole trace support is its own cut boundary.

This is pure graph geometry; it mentions no strategy, row, or ledger.
-/

namespace Hypostructure.Graph.FiniteObject

open Hypostructure
open Hypostructure.Graph

universe u

/-- **The canonical trace is length-minimal.**  `tracePath?` is the first
trace-shaped path of the length-major path schedule, so it is no longer than
any other trace-shaped path between the same endpoints. -/
theorem tracePath?_length_le (object : FiniteObject.{u})
    {support : Finset object.Vertex} {threshold : Nat}
    {source target : object.Vertex} {trace : object.graph.Path source target}
    (selected : object.tracePath? support threshold source target = some trace)
    (other : object.graph.Path source target)
    (otherShape : object.IsTracePath support threshold other.1) :
    trace.1.length ≤ other.1.length := by
  letI : FinEnum object.Vertex := object.vertices
  letI : Fintype object.Vertex := FinEnum.instFintype
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  let schedule :=
    FinitePathSelection.pathSchedule object.graph source target
  let predicate := fun path : object.graph.Path source target =>
    @decide (object.IsTracePath support threshold path.1)
      (Classical.propDecidable _)
  change List.find? predicate schedule = some trace at selected
  obtain ⟨_selectedTrue, i, hi, selectedAt, earlierFalse⟩ :=
    List.find?_eq_some_iff_getElem.mp selected
  have otherMem : other ∈ schedule :=
    FinitePathSelection.mem_pathSchedule object.graph other
  obtain ⟨j, hj, otherAt⟩ := List.mem_iff_getElem.mp otherMem
  have notBefore : ¬ j < i := by
    intro before
    have failed := earlierFalse j before
    rw [otherAt] at failed
    simp [predicate, otherShape] at failed
  rcases Nat.eq_or_lt_of_le (Nat.le_of_not_gt notBefore) with
    equal | before
  · subst j
    have same : trace = other := selectedAt.symm.trans otherAt
    simp [same]
  · have ordered :=
      FinitePathSelection.pathSchedule_pairwise_length
        object.graph source target
    have relation := ordered.rel_get_of_lt
      (a := ⟨i, hi⟩) (b := ⟨j, hj⟩) (by simpa using before)
    change schedule[i].1.length ≤ schedule[j].1.length at relation
    rw [selectedAt, otherAt] at relation
    exact relation

/-- Every vertex of the canonical trace, viewed through any finset `T` with the
trace's vertex set, has a neighbour outside `T`. -/
private theorem tracePath?_exits_of_support_iff (object : FiniteObject.{u})
    {support : Finset object.Vertex} {threshold : Nat}
    {source target : object.Vertex} {trace : object.graph.Path source target}
    (selected : object.tracePath? support threshold source target = some trace)
    (T : Finset object.Vertex)
    (traceSupportIff : ∀ vertex, vertex ∈ T ↔ vertex ∈ trace.1.support)
    (sourceFull : threshold ≤ object.internalDegree support source)
    (degreeThree : ∀ vertex ∈ support, 3 ≤ object.degree vertex) :
    ∀ vertex ∈ T, ∃ neighbor, object.graph.Adj vertex neighbor ∧ neighbor ∉ T := by
  letI : FinEnum object.Vertex := object.vertices
  letI : Fintype object.Vertex := FinEnum.instFintype
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  have shape := object.isTracePath_of_tracePath?_eq_some selected
  have traceInside : ∀ vertex ∈ trace.1.support, vertex ∈ T := by
    intro vertex member
    exact (traceSupportIff vertex).2 member
  let sourceT : (object.induce T).Vertex :=
    ⟨source, traceInside source trace.1.start_mem_support⟩
  let targetT : (object.induce T).Vertex :=
    ⟨target, traceInside target trace.1.end_mem_support⟩
  let lifted : (object.induce T).graph.Walk sourceT targetT :=
    trace.1.induce (↑T : Set object.Vertex) traceInside
  have liftedSupport : lifted.support =
      trace.1.support.attachWith
        (Membership.mem (↑T : Set object.Vertex)) traceInside := by
    simpa only [lifted, Graph.FiniteObject.induce] using
      (SimpleGraph.Walk.support_induce trace.1 traceInside)
  have liftedPath : lifted.IsPath := by
    have mappedPath :
        (lifted.map (object.induceEmbedding T).toHom).IsPath := by
      rw [show lifted.map
          (object.induceEmbedding T).toHom = trace.1 by
        simpa only [lifted, Graph.FiniteObject.induce,
          Graph.FiniteObject.induceEmbedding] using
          (SimpleGraph.Walk.map_induce trace.1 traceInside)]
      exact trace.2
    exact (SimpleGraph.Walk.map_isPath_iff_of_injective
      (f := (object.induceEmbedding T).toHom)
      (p := lifted)
      (object.induceEmbedding T).injective).mp mappedPath
  have liftedLength : lifted.length = trace.1.length := by
    have supportLength :
        lifted.support.length = trace.1.support.length := by
      calc
        lifted.support.length =
            (trace.1.support.attachWith
              (Membership.mem (↑T : Set object.Vertex))
              traceInside).length :=
          congrArg List.length liftedSupport
        _ = trace.1.support.length := List.length_attachWith
    have leftLength := lifted.length_support
    have rightLength := trace.1.length_support
    omega
  have reachable : (object.induce T).graph.Reachable
      sourceT targetT := ⟨lifted⟩
  obtain ⟨shortest, shortestPath, shortestLength⟩ :=
    reachable.exists_path_of_dist
  let ambientShortestWalk : object.graph.Walk source target := by
    let raw := shortest.map (object.induceEmbedding T).toHom
    exact raw.copy (by rfl) (by rfl)
  have ambientShortestPath : ambientShortestWalk.IsPath := by
    have mapped :
        (shortest.map (object.induceEmbedding T).toHom).IsPath :=
      (SimpleGraph.Walk.map_isPath_iff_of_injective
        (object.induceEmbedding T).injective).mpr shortestPath
    simpa [ambientShortestWalk, sourceT, targetT] using mapped
  let ambientShortest : object.graph.Path source target :=
    ⟨ambientShortestWalk, ambientShortestPath⟩
  have ambientShortestSupport :
      ∀ vertex ∈ ambientShortest.1.support, vertex ∈ T := by
    intro vertex member
    change vertex ∈ ambientShortestWalk.support at member
    simp only [ambientShortestWalk,
      SimpleGraph.Walk.support_copy] at member
    rw [SimpleGraph.Walk.support_map] at member
    rcases List.mem_map.mp member with ⟨inside, insideMem, rfl⟩
    exact inside.2
  have ambientShortestShape :
      object.IsTracePath support threshold ambientShortest.1 := by
    refine ⟨?_, ?_, shape.2.2⟩
    · intro vertex member
      have inT := ambientShortestSupport vertex member
      have onTrace : vertex ∈ trace.1.support := by
        exact (traceSupportIff vertex).1 inT
      exact shape.1 vertex onTrace
    · intro vertex member different
      have inT := ambientShortestSupport vertex member
      have onTrace : vertex ∈ trace.1.support := by
        exact (traceSupportIff vertex).1 inT
      exact shape.2.1 vertex onTrace different
  have selectedLe :=
    object.tracePath?_length_le selected ambientShortest ambientShortestShape
  have ambientShortestLength :
      ambientShortest.1.length = shortest.length := by
    change ambientShortestWalk.length = shortest.length
    simpa [ambientShortestWalk] using
      (SimpleGraph.Walk.length_map
        (object.induceEmbedding T).toHom shortest)
  have traceLeDist : trace.1.length ≤
      (object.induce T).graph.dist sourceT targetT := by
    rw [ambientShortestLength, shortestLength] at selectedLe
    exact selectedLe
  have distLeTrace : (object.induce T).graph.dist
      sourceT targetT ≤ trace.1.length := by
    rw [← liftedLength]
    exact SimpleGraph.dist_le lifted
  have liftedShortest : lifted.length =
      (object.induce T).graph.dist sourceT targetT := by
    omega
  have inducedSubgraph : lifted.toSubgraph.IsInduced := by
    intro x xMem y yMem adjacent
    have xSupport : x ∈ lifted.support :=
      lifted.mem_verts_toSubgraph.mp xMem
    have ySupport : y ∈ lifted.support :=
      lifted.mem_verts_toSubgraph.mp yMem
    obtain ⟨i, xEq, iLe⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp xSupport
    obtain ⟨j, yEq, jLe⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp ySupport
    have ijNe : i ≠ j := by
      intro equal
      exact adjacent.ne (calc
        x = lifted.getVert i := xEq.symm
        _ = lifted.getVert j := congrArg lifted.getVert equal
        _ = y := yEq)
    rcases lt_or_gt_of_ne ijNe with iLt | jLt
    · let segment := (lifted.drop i).take (j - i)
      have segmentSub : segment.IsSubwalk lifted :=
        (SimpleGraph.Walk.isSubwalk_take (lifted.drop i)
          (j - i)).trans
          (SimpleGraph.Walk.isSubwalk_drop lifted i)
      have segmentShortest :=
        SimpleGraph.length_eq_dist_of_subwalk liftedShortest
          segmentSub
      have segmentLength : segment.length = j - i := by
        simp only [segment, SimpleGraph.Walk.take_length,
          SimpleGraph.Walk.drop_length]
        rw [Nat.min_eq_left
          (by omega : j - i ≤ lifted.length - i)]
      have segmentTarget :
          (lifted.drop i).getVert (j - i) = lifted.getVert j := by
        rw [SimpleGraph.Walk.drop_getVert]
        congr 1
        omega
      have distanceOne : (object.induce T).graph.dist
          (lifted.getVert i) (lifted.getVert j) = 1 := by
        have distanceXY :=
          SimpleGraph.dist_eq_one_iff_adj.mpr adjacent
        simpa only [xEq, yEq] using distanceXY
      have consecutive : j = i + 1 := by
        have distanceTarget := congrArg
          (fun target => (object.induce T).graph.dist
            (lifted.getVert i) target)
          segmentTarget
        omega
      subst j
      simpa [xEq, yEq] using
        lifted.toSubgraph_adj_getVert
          (by omega : i < lifted.length)
    · have adjacent' := adjacent.symm
      let segment := (lifted.drop j).take (i - j)
      have segmentSub : segment.IsSubwalk lifted :=
        (SimpleGraph.Walk.isSubwalk_take (lifted.drop j)
          (i - j)).trans
          (SimpleGraph.Walk.isSubwalk_drop lifted j)
      have segmentShortest :=
        SimpleGraph.length_eq_dist_of_subwalk liftedShortest
          segmentSub
      have segmentLength : segment.length = i - j := by
        simp only [segment, SimpleGraph.Walk.take_length,
          SimpleGraph.Walk.drop_length]
        rw [Nat.min_eq_left
          (by omega : i - j ≤ lifted.length - j)]
      have segmentTarget :
          (lifted.drop j).getVert (i - j) = lifted.getVert i := by
        rw [SimpleGraph.Walk.drop_getVert]
        congr 1
        omega
      have distanceOne : (object.induce T).graph.dist
          (lifted.getVert j) (lifted.getVert i) = 1 := by
        have distanceYX :=
          SimpleGraph.dist_eq_one_iff_adj.mpr adjacent'
        simpa only [xEq, yEq] using distanceYX
      have consecutive : i = j + 1 := by
        have distanceTarget := congrArg
          (fun target => (object.induce T).graph.dist
            (lifted.getVert j) target)
          segmentTarget
        omega
      subst i
      simpa [xEq, yEq] using
        (lifted.toSubgraph_adj_getVert
          (by omega : j < lifted.length)).symm
  have spanning : lifted.toSubgraph.IsSpanning := by
    intro vertex
    rw [lifted.mem_verts_toSubgraph]
    have onTrace : vertex.1 ∈ trace.1.support :=
      (traceSupportIff vertex.1).1 vertex.2
    rw [liftedSupport]
    exact (List.mem_attachWith traceInside vertex).2 onTrace
  have sourceNeTarget : source ≠ target := by
    intro equal
    subst target
    have receiver := shape.2.2
    omega
  have liftedNonNil : ¬ lifted.Nil := by
    apply SimpleGraph.Walk.not_nil_of_ne
    intro equal
    exact sourceNeTarget (congrArg Subtype.val equal)
  intro vertex vertexMem
  have vertexInSupport : vertex ∈ support := by
    have onTrace : vertex ∈ trace.1.support := by
      exact (traceSupportIff vertex).1 vertexMem
    exact shape.1 vertex onTrace
  let vertexInduced : (object.induce T).Vertex :=
    ⟨vertex, vertexMem⟩
  have vertexSpanning :
      vertexInduced ∈ lifted.toSubgraph.verts :=
    spanning vertexInduced
  have neighborEq :
      (object.induce T).graph.neighborSet vertexInduced =
        lifted.toSubgraph.neighborSet vertexInduced := by
    ext neighbor
    constructor
    · intro adjacent
      exact inducedSubgraph vertexSpanning (spanning neighbor)
        adjacent
    · intro adjacent
      exact lifted.toSubgraph.adj_sub adjacent
  have vertexOnLifted : vertexInduced ∈ lifted.support :=
    lifted.mem_verts_toSubgraph.mp vertexSpanning
  obtain ⟨i, vertexEq, iLe⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp
      vertexOnLifted
  have pathNeighborNcard :
      (lifted.toSubgraph.neighborSet vertexInduced).ncard ≤ 2 := by
    rw [← vertexEq]
    rcases lt_or_eq_of_le iLe with beforeEnd | atEnd
    · by_cases atStart : i = 0
      · subst i
        rw [SimpleGraph.Walk.getVert_zero,
          liftedPath.neighborSet_toSubgraph_startpoint
            liftedNonNil]
        simp
      · rw [liftedPath.neighborSet_toSubgraph_internal atStart
          beforeEnd]
        calc
          ({lifted.getVert (i - 1), lifted.getVert (i + 1)} :
              Set (object.induce T).Vertex).ncard ≤
              ({lifted.getVert (i + 1)} :
                Set (object.induce T).Vertex).ncard + 1 :=
            Set.ncard_insert_le _ _
          _ = 2 := by simp
    · subst i
      rw [SimpleGraph.Walk.getVert_length,
        liftedPath.neighborSet_toSubgraph_endpoint liftedNonNil]
      simp
  have inducedNeighborNcard :
      ((object.induce T).graph.neighborSet
        vertexInduced).ncard ≤ 2 := by
    rw [neighborEq]
    exact pathNeighborNcard
  have inducedDegree :
      (object.induce T).degree vertexInduced ≤ 2 := by
    rw [(object.induce T).degree_eq_ncard_neighborSet]
    exact inducedNeighborNcard
  have internalDegree : object.internalDegree T vertex ≤ 2 := by
    rw [← object.degree_induce_eq_internalDegree T vertexInduced]
    exact inducedDegree
  have ambientDegree : 3 ≤ object.degree vertex :=
    degreeThree vertex vertexInSupport
  have split :=
    object.internalDegree_add_internalDegree_compl T vertex
  have outsidePositive :
      0 < object.internalDegree (Finset.univ \ T) vertex := by
    omega
  unfold Graph.FiniteObject.internalDegree at outsidePositive
  rw [Finset.card_pos] at outsidePositive
  obtain ⟨neighbor, neighborMem⟩ := outsidePositive
  rcases Finset.mem_inter.mp neighborMem with
    ⟨adjacent, outsideT⟩
  refine ⟨neighbor, ?_, ?_⟩
  · exact (SimpleGraph.mem_neighborFinset object.graph vertex
      neighbor).mp adjacent
  · exact (Finset.mem_sdiff.mp outsideT).2

/-- **The canonical trace support is boundary-only.**  If the trace source is
full (`threshold ≤` its internal degree) and every support vertex has ambient
degree at least `3`, then every vertex of the selected trace has a neighbour
off the trace: the trace is a shortest, hence chordless, path in its own
induced subgraph, so it gives each vertex at most two trace neighbours. -/
theorem tracePath?_support_exits (object : FiniteObject.{u})
    [DecidableEq object.Vertex]
    {support : Finset object.Vertex} {threshold : Nat}
    {source target : object.Vertex} {trace : object.graph.Path source target}
    (selected : object.tracePath? support threshold source target = some trace)
    (sourceFull : threshold ≤ object.internalDegree support source)
    (degreeThree : ∀ vertex ∈ support, 3 ≤ object.degree vertex) :
    ∀ vertex ∈ trace.1.support.toFinset,
      ∃ neighbor, object.graph.Adj vertex neighbor ∧
        neighbor ∉ trace.1.support.toFinset :=
  tracePath?_exits_of_support_iff object selected _
    (fun _ => List.mem_toFinset) sourceFull degreeThree

end Hypostructure.Graph.FiniteObject
