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

/-! ## Node `[184]`: silent-ownership exhaustion on the retained entries

The active family is still the broad unified family supplied at `[123]` and
retained through `[181]` and `[183]`.  This row does not rebuild that family.
It reads its census and proves, on the selected object, that a silent member
would have a boundary-only shortest trace basin and hence essential-core
cardinality zero, contradicting the census lower bound `alpha >= 2`. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
set_option maxHeartbeats 6000000 in
@[reducible] noncomputable def route8UnifiedVisibleResidualRow :
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
    `Hypostructure.Graph.Strategy.Spine.route8UnifiedVisibleResidual
    { Requires := [K .route8UnifiedEntryCensus]
      Produces := [K .route8UnifiedVisibleResidual]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let census := (inputs.get (K .route8UnifiedEntryCensus)).down
      .cons (key := K .route8UnifiedVisibleResidual)
        (⟨by
          classical
          letI : DecidableEq inputs.current.object.Vertex :=
            inputs.current.object.vertices.decEq

          -- `lem:typeA-unified-visible-ownership`: in a
          -- boundary-only basin no coordinate can alter an edge, so every
          -- retained reading is the basin's own piece.
          have boundaryOnly :=
            @Graph.Route8.PresentedEntry.retainedBasinPiece_eq_piece_of_cutBoundary

          -- `tracePath?` scans the complete path schedule length-first, so its
          -- chosen trace is no longer than any other trace-shaped path.
          have tracePathLengthLe
              (object : Graph.FiniteObject.{u})
              (support : Finset object.Vertex) (threshold : Nat)
              (source target : object.Vertex)
              (trace other : object.graph.Path source target)
              (selected : object.tracePath? support threshold source target =
                some trace)
              (otherShape : object.IsTracePath support threshold other.1) :
              trace.1.length ≤ other.1.length := by
            letI : FinEnum object.Vertex := object.vertices
            letI : Fintype object.Vertex := FinEnum.instFintype
            letI : DecidableEq object.Vertex := object.vertices.decEq
            letI : DecidableRel object.graph.Adj := object.decideAdj
            classical
            let schedule :=
              Graph.FinitePathSelection.pathSchedule object.graph source target
            let predicate := fun path : object.graph.Path source target =>
              @decide (object.IsTracePath support threshold path.1)
                (Classical.propDecidable _)
            change List.find? predicate schedule = some trace at selected
            obtain ⟨_selectedTrue, i, hi, selectedAt, earlierFalse⟩ :=
              List.find?_eq_some_iff_getElem.mp selected
            have otherMem : other ∈ schedule :=
              Graph.FinitePathSelection.mem_pathSchedule object.graph other
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
              simpa [same]
            · have ordered :=
                Graph.FinitePathSelection.pathSchedule_pairwise_length
                  object.graph source target
              have relation := ordered.rel_get_of_lt
                (a := ⟨i, hi⟩) (b := ⟨j, hj⟩) (by simpa using before)
              change schedule[i].1.length ≤ schedule[j].1.length at relation
              rw [selectedAt, otherAt] at relation
              exact relation

          -- The selected trace is shortest inside its own vertex support.
          -- Hence it has no chord there; every trace vertex has at most two
          -- neighbours in the trace.  Exact ambient cubicity then supplies an
          -- edge leaving the trace at every trace vertex.
          have traceSupportBoundary
              (object : Graph.FiniteObject.{u})
              (support : Finset object.Vertex) (threshold : Nat)
              (source target : object.Vertex)
              (trace : object.graph.Path source target)
              (selected : object.tracePath? support threshold source target =
                some trace)
              (T : Finset object.Vertex)
              (traceSupportIff : ∀ vertex,
                vertex ∈ T ↔ vertex ∈ trace.1.support)
              (thresholdThree : 3 ≤ threshold)
              (sourceFull : object.internalDegree support source = threshold)
              (exactDegree : ∀ vertex ∈ support,
                object.degree vertex = threshold) :
              T ⊆
                Graph.Strategy.InterfaceReplacement.SupportAtom.cutBoundary
                  object T := by
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
            have selectedLe := tracePathLengthLe object support threshold
              source target trace ambientShortest selected ambientShortestShape
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
            have ambientDegree : object.degree vertex = threshold :=
              exactDegree vertex vertexInSupport
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
            apply (Graph.Strategy.InterfaceReplacement.SupportAtom.mem_cutBoundary_iff
              object T vertex).2
            refine ⟨vertexMem, neighbor, ?_, ?_⟩
            · exact (SimpleGraph.mem_neighborFinset object.graph vertex
                neighbor).mp adjacent
            · exact (Finset.mem_sdiff.mp outsideT).2

          have allVisible :
              ∀ index ∈ route8UnifiedEntries data inputs.current.object,
                index.2.2 ∈ Graph.VisibleEntry.visibleLoads
                  inputs.current.object index.1 data.threshold index.2.1 := by
            intro index indexMem
            by_contra notVisible
            have censusAt := census index indexMem
            rcases index with ⟨indexedPiece, receiver, load⟩
            simp only [route8UnifiedEntries,
              Graph.Route8Census.entriesOfComponents, Finset.mem_biUnion,
              Finset.mem_image, Prod.mk.injEq] at indexMem
            obtain ⟨component, componentMem, receiver', receiverMem, load',
              excessMem, pieceEq, receiverEq, loadEq⟩ := indexMem
            subst indexedPiece
            subst receiver
            subst load
            have surplusZero : inputs.current.object.ambientSurplus
                (inputs.current.object.pieceSupport
                  (inputs.current.object.remainderSupport
                    (canonicalWindowPacking data inputs.current.object))
                  component)
                data.threshold = 0 :=
              ((Finset.mem_filter.1 componentMem).2).1
            let piece := inputs.current.object.pieceSupport
              (inputs.current.object.remainderSupport
                (canonicalWindowPacking data inputs.current.object)) component
            have routed : load' ∈ inputs.current.object.routedLoads piece
                data.threshold receiver' :=
              (Finset.mem_sdiff.mp excessMem).1
            have routedSpec :=
              (inputs.current.object.mem_routedLoads).mp routed
            have baseline : ∀ vertex : inputs.current.object.Vertex,
                data.threshold ≤ inputs.current.object.degree vertex :=
              fun vertex => le_trans inputs.current.baseline
                (inputs.current.object.minDegree_le_degree vertex)
            have exactDegree : ∀ vertex ∈ piece,
                inputs.current.object.degree vertex = data.threshold := by
              intro vertex vertexMem
              have lower := baseline vertex
              have zeroSum := surplusZero
              unfold Graph.FiniteObject.ambientSurplus at zeroSum
              have zeroTerm :=
                (Finset.sum_eq_zero_iff.mp zeroSum) vertex vertexMem
              omega
            have traceTo :=
              inputs.current.object.traceTo_of_traceReceiver?_eq_some
                routedSpec.2.2
            obtain ⟨trace, traceSelected⟩ := Option.isSome_iff_exists.mp
              (inputs.current.object.isSome_tracePath?_of_traceTo traceTo)
            let traceSupport : Finset inputs.current.object.Vertex :=
              trace.1.support.toFinset
            have traceBoundary : traceSupport ⊆
                Graph.Strategy.InterfaceReplacement.SupportAtom.cutBoundary
                  inputs.current.object traceSupport := by
              apply traceSupportBoundary inputs.current.object piece
                data.threshold load' receiver' trace traceSelected traceSupport
              · intro vertex
                simp [traceSupport]
              · exact data.three_le_threshold
              · exact routedSpec.2.1
              · exact exactDegree
            have traceShape :=
              inputs.current.object.isTracePath_of_tracePath?_eq_some
                traceSelected
            have traceSupportSubset : traceSupport ⊆ piece := by
              intro vertex vertexMem
              exact traceShape.1 vertex (List.mem_toFinset.mp vertexMem)
            have traceConnected :
                Graph.SupportComponents.Connected.ConnectedOn
                  inputs.current.object traceSupport := by
              exact Graph.SameTokenRoutingGerms.connectedOn_walkSupport
                trace.1
            have noDeclaredOwner :
                ∀ declared : Finset inputs.current.object.Vertex,
                  ¬ Graph.VisibleEntry.ownsDeclaredSupport
                    inputs.current.object piece data.threshold receiver' load'
                    declared := by
              intro declared
              rintro ⟨outside, port, return', _scheduled, owns⟩
              apply notVisible
              apply (Graph.VisibleEntry.mem_visibleLoads
                inputs.current.object).2
              refine ⟨routed, outside, port, ?_⟩
              unfold Graph.VisibleEntry.visibleLoadsAt
              rw [Finset.mem_filter]
              exact ⟨routed, return', owns.2⟩
            have traceComplete :
                Graph.Route8.TraceBasin.TraceComplete inputs.current.object
                  piece data.threshold receiver' load' traceSupport := by
              refine ⟨traceSupportSubset,
                ⟨trace, traceSelected, Finset.Subset.rfl⟩,
                traceConnected, ?_⟩
              intro coordinate _scheduled supported
              cases coordinate with
              | d1 coordinate =>
                  rcases supported with meets | owned
                  · obtain ⟨other, otherSelected, coordinateTrace⟩ := meets
                    have otherEq : other = trace :=
                      Option.some.inj
                        (otherSelected.symm.trans traceSelected)
                    subst other
                    refine Or.inr ⟨coordinate.1,
                      traceBoundary
                        (List.mem_toFinset.mpr coordinateTrace), ?_⟩
                    show coordinate.1 ∈
                      Graph.TraceCoordinateSystem.D1.declaredSupport
                        inputs.current.object piece coordinate
                    exact Finset.mem_singleton_self _
                  · exact (noDeclaredOwner {coordinate.1} owned).elim
              | d2ReturnLength coordinate =>
                  rcases supported with meets | owned
                  · obtain ⟨other, otherSelected, vertex, vertexDeclared,
                      vertexTrace⟩ := meets
                    have otherEq : other = trace :=
                      Option.some.inj
                        (otherSelected.symm.trans traceSelected)
                    subst other
                    refine Or.inr ⟨vertex,
                      traceBoundary (List.mem_toFinset.mpr vertexTrace), ?_⟩
                    exact vertexDeclared
                  · obtain ⟨outside, port, _rootAtReceiver, _rootAtOutside,
                      return', scheduled, owns⟩ := owned
                    exact (noDeclaredOwner
                      (Graph.TraceCoordinateSystem.D2.declaredSupport
                        inputs.current.object coordinate)
                      ⟨outside, port, return', scheduled, owns⟩).elim
              | d3WindowLabel coordinate =>
                  rcases supported with meets | owned
                  · obtain ⟨other, otherSelected, vertex, vertexDeclared,
                      vertexTrace⟩ := meets
                    have otherEq : other = trace :=
                      Option.some.inj
                        (otherSelected.symm.trans traceSelected)
                    subst other
                    refine Or.inr ⟨vertex,
                      traceBoundary (List.mem_toFinset.mpr vertexTrace), ?_⟩
                    exact vertexDeclared
                  · exact (noDeclaredOwner
                      (Graph.TraceCoordinateSystem.D3.declaredSupport
                        inputs.current.object piece coordinate) owned).elim
              | d4RawCurvature coordinate =>
                  rcases supported with meets | owned
                  · obtain ⟨other, otherSelected, vertex, vertexDeclared,
                      vertexTrace⟩ := meets
                    have otherEq : other = trace :=
                      Option.some.inj
                        (otherSelected.symm.trans traceSelected)
                    subst other
                    refine Or.inr ⟨vertex,
                      traceBoundary (List.mem_toFinset.mpr vertexTrace), ?_⟩
                    exact vertexDeclared
                  · exact (noDeclaredOwner
                      (Graph.TraceCoordinateSystem.D4.declaredSupport
                        inputs.current.object piece coordinate) owned).elim
            let entryIndex : Graph.Route8Census.Index inputs.current.object :=
              (piece, receiver', load')
            let basin := Graph.Route8Census.basin inputs.current.object
              data.threshold entryIndex
            let presented := Graph.Route8Census.presented inputs.current.object
              data.threshold data.LengthOK entryIndex
            let entry := presented.toEntry
              (Graph.HasCycleWithLength data.LengthOK)
            change Route8UnifiedEntryFacts data inputs.current.object
              entryIndex at censusAt
            change
              Graph.Route8.TraceBasin.select? inputs.current.object piece
                    data.threshold receiver' load' = some basin ∧
                2 ≤ entry.alpha ∧ _ at censusAt
            obtain ⟨basinSelected, alphaTwo, _classification⟩ := censusAt
            have basinComplete :=
              Graph.Route8.TraceBasin.select?_traceComplete basinSelected
            obtain ⟨_basinInside,
              ⟨basinTrace, basinTraceSelected, basinTraceSubset⟩,
              _basinConnected, _basinCoordinates⟩ := basinComplete
            have basinTraceEq : basinTrace = trace :=
              Option.some.inj
                (basinTraceSelected.symm.trans traceSelected)
            have traceSubsetBasin : traceSupport ⊆ basin := by
              rw [basinTraceEq] at basinTraceSubset
              exact basinTraceSubset
            have traceCandidate : traceSupport ∈
                Graph.Route8.TraceBasin.candidates inputs.current.object piece
                  data.threshold receiver' load' :=
              Graph.Route8.TraceBasin.mem_candidates_iff.mpr traceComplete
            have basinCardLeTrace :=
              Graph.Route8.TraceBasin.select?_card_le basinSelected
                traceCandidate
            have traceSupportEqBasin : traceSupport = basin :=
              Finset.eq_of_subset_of_card_le traceSubsetBasin
                basinCardLeTrace
            have basinBoundary : basin ⊆
                Graph.Strategy.InterfaceReplacement.SupportAtom.cutBoundary
                  inputs.current.object basin := by
              rw [← traceSupportEqBasin]
              exact traceBoundary
            have stateIndependent :
                ∀ left right : Finset entry.Coordinate,
                  entry.state left = entry.state right := by
              intro left right
              change Graph.Route8.PresentedEntry.retainedReading
                    inputs.current.object piece basin data.threshold
                    data.LengthOK
                    (Graph.Route8.PresentedEntry.retainedBaseCoordinates
                      inputs.current.object piece left) =
                  Graph.Route8.PresentedEntry.retainedReading
                    inputs.current.object piece basin data.threshold
                    data.LengthOK
                    (Graph.Route8.PresentedEntry.retainedBaseCoordinates
                      inputs.current.object piece right)
              unfold Graph.Route8.PresentedEntry.retainedReading
              rw [boundaryOnly inputs.current.object basin _ basinBoundary,
                boundaryOnly inputs.current.object basin _ basinBoundary]
            have emptyComplete : entry.Complete ∅ := by
              unfold Graph.Route8.Entry.Complete Graph.Route8.Entry.restriction
                Graph.Route8.Entry.full
              intro outside
              rw [stateIndependent]
            have minimumLe :=
              entry.carrierProfile.minimumCard_le ∅ emptyComplete
            have coreCard := entry.carrierProfile.core_card
            change 2 ≤ entry.essentialCore.card at alphaTwo
            change entry.essentialCore.card =
              entry.carrierProfile.minimumCard at coreCard
            have minimumZero : entry.carrierProfile.minimumCard = 0 := by
              apply Nat.eq_zero_of_le_zero
              simpa using minimumLe
            have essentialZero : entry.essentialCore.card = 0 := by
              rw [coreCard, minimumZero]
            omega

          show Route8UnifiedVisibleResidualStatement data
            inputs.current.object
          unfold Route8UnifiedVisibleResidualStatement
          refine ⟨allVisible, ?_⟩
          rw [Finset.card_eq_zero]
          apply Finset.filter_eq_empty_iff.mpr
          intro index indexMem
          simpa using allVisible index indexMem⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
