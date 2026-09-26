import Hypostructure.Graph.Contracts.RouteEight.Basic
import Hypostructure.Graph.ShortestTraceBoundary

/-!
# Contracts: node `[184]`, silent-ownership exhaustion

`lem:typeA-unified-visible-ownership` on the unified entry family
(`route8UnifiedVisibleResidual`).  The graph-theoretic core — the canonical
trace is a shortest, chordless path whose support is its own cut boundary — is
the generic `Graph.FiniteObject.tracePath?_support_exits`.
-/

namespace Hypostructure.Graph.Contracts.RouteEight

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine

universe u

/-- **`lem:typeA-unified-visible-ownership`** (node `[184]`).

The active family is still the broad unified family supplied at `[123]` and
retained through `[181]` and `[183]`.  Reading its census, a silent member
would have a boundary-only shortest trace basin (in a boundary-only basin no
coordinate can alter an edge, so every retained reading is the basin's own
piece) and hence essential-core cardinality zero, contradicting the census
lower bound `alpha >= 2`. -/
theorem route8UnifiedVisibleResidual (data : Parameters)
    (object : FiniteObject.{u})
    (census : Route8UnifiedEntryCensusFact data object)
    (baseline : data.threshold ≤ object.minDegree)
    (threeLe : 3 ≤ data.threshold) :
    Route8UnifiedVisibleResidualStatement data object := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  have allVisible :
      ∀ index ∈ route8UnifiedEntries data object,
        index.2.2 ∈ Graph.VisibleEntry.visibleLoads
          object index.1 data.threshold index.2.1 := by
    intro index indexMem
    by_contra notVisible
    have censusAt := census index indexMem
    obtain ⟨component, componentMem, pieceEq, _receiverMem, excessMem⟩ :=
      mem_entriesOfComponents.mp indexMem
    obtain ⟨indexedPiece, receiver', load'⟩ := index
    simp only at pieceEq excessMem notVisible
    subst pieceEq
    let piece := object.pieceSupport
      (object.remainderSupport
        (canonicalWindowPacking data object)) component
    have routed : load' ∈ object.routedLoads piece
        data.threshold receiver' :=
      (Finset.mem_sdiff.mp excessMem).1
    have routedSpec :=
      (object.mem_routedLoads).mp routed
    have degreeThree : ∀ vertex ∈ piece, 3 ≤ object.degree vertex :=
      fun vertex _ =>
        le_trans threeLe (degree_ge_of_minDegree data object baseline vertex)
    have traceTo :=
      object.traceTo_of_traceReceiver?_eq_some
        routedSpec.2.2
    obtain ⟨trace, traceSelected⟩ := Option.isSome_iff_exists.mp
      (object.isSome_tracePath?_of_traceTo traceTo)
    let traceSupport : Finset object.Vertex :=
      trace.1.support.toFinset
    -- The selected trace is shortest, hence chordless, in its own support;
    -- ambient degree at least three gives every trace vertex an exit edge.
    have traceBoundary : traceSupport ⊆
        Graph.Strategy.InterfaceReplacement.SupportAtom.cutBoundary
          object traceSupport := by
      intro vertex vertexMem
      obtain ⟨neighbor, adjacent, outside⟩ :=
        object.tracePath?_support_exits traceSelected routedSpec.2.1.ge
          degreeThree vertex vertexMem
      exact (Graph.Strategy.InterfaceReplacement.SupportAtom.mem_cutBoundary_iff
        object traceSupport vertex).2 ⟨vertexMem, neighbor, adjacent, outside⟩
    have traceShape :=
      object.isTracePath_of_tracePath?_eq_some
        traceSelected
    have traceSupportSubset : traceSupport ⊆ piece := by
      intro vertex vertexMem
      exact traceShape.1 vertex (List.mem_toFinset.mp vertexMem)
    have traceConnected :
        Graph.SupportComponents.Connected.ConnectedOn
          object traceSupport := by
      exact Graph.SameTokenRoutingGerms.connectedOn_walkSupport
        trace.1
    have noDeclaredOwner :
        ∀ declared : Finset object.Vertex,
          ¬ Graph.VisibleEntry.ownsDeclaredSupport
            object piece data.threshold receiver' load'
            declared := by
      intro declared
      rintro ⟨outside, port, return', _scheduled, owns⟩
      apply notVisible
      apply (Graph.VisibleEntry.mem_visibleLoads
        object).2
      refine ⟨routed, outside, port, ?_⟩
      unfold Graph.VisibleEntry.visibleLoadsAt
      rw [Finset.mem_filter]
      exact ⟨routed, return', owns.2⟩
    have traceComplete :
        Graph.Route8.TraceBasin.TraceComplete object
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
                object piece coordinate
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
                object coordinate)
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
                object piece coordinate) owned).elim
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
                object piece coordinate) owned).elim
    let entryIndex : Graph.Route8Census.Index object :=
      (piece, receiver', load')
    let basin := Graph.Route8Census.basin object
      data.threshold entryIndex
    let presented := Graph.Route8Census.presented object
      data.threshold data.LengthOK entryIndex
    let entry := presented.toEntry
      (Graph.HasCycleWithLength data.LengthOK)
    change Route8UnifiedEntryFacts data object
      entryIndex at censusAt
    change
      Graph.Route8.TraceBasin.select? object piece
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
        Graph.Route8.TraceBasin.candidates object piece
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
          object basin := by
      rw [← traceSupportEqBasin]
      exact traceBoundary
    have stateIndependent :
        ∀ left right : Finset entry.Coordinate,
          entry.state left = entry.state right := by
      intro left right
      change Graph.Route8.PresentedEntry.retainedReading
            object piece basin data.threshold
            data.LengthOK
            (Graph.Route8.PresentedEntry.retainedBaseCoordinates
              object piece left) =
          Graph.Route8.PresentedEntry.retainedReading
            object piece basin data.threshold
            data.LengthOK
            (Graph.Route8.PresentedEntry.retainedBaseCoordinates
              object piece right)
      unfold Graph.Route8.PresentedEntry.retainedReading
      rw [Graph.Route8.PresentedEntry.retainedBasinPiece_eq_piece_of_cutBoundary
          object basin _ basinBoundary,
        Graph.Route8.PresentedEntry.retainedBasinPiece_eq_piece_of_cutBoundary
          object basin _ basinBoundary]
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
  unfold Route8UnifiedVisibleResidualStatement
  refine ⟨allVisible, ?_⟩
  rw [Finset.card_eq_zero]
  apply Finset.filter_eq_empty_iff.mpr
  intro index indexMem
  simpa using allVisible index indexMem

end Hypostructure.Graph.Contracts.RouteEight
