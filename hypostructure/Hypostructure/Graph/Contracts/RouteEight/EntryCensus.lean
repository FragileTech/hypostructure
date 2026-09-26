import Hypostructure.Graph.Contracts.RouteEight.Basic
import Hypostructure.Graph.Statements.TypeB

/-!
# Contracts: the route-8 per-entry census and the all-pieces classification

* `lem:typeA-one-terminal-collapse`, the per-entry quotient construction: an
  entry with `α ≤ 1` whose crossing coordinates obey the carrier cut parity
  carries a nontrivial trace-response quotient (`route8Entry_smallCoreQuotient`),
  shared by the census below and by node `[116]`'s `route8SmallCoreCollapse`;
* `def:typeA-unified-entries` with `lem:typeA-unified-carriers` (node `[123]`):
  the exact per-entry census at one connected entry (`route8EntryFacts`),
  instantiated at the unified collection (`route8UnifiedEntryCensus`) and at the
  extracted route-8 cores (`route8ExtractedEntryCensus`);
* `thm:branch-kill`'s all-pieces classification at the canonical packing
  (`route8PiecesClassified`).

This module imports no vocabulary, row, or strategy module.
-/

namespace Hypostructure.Graph.Contracts.RouteEight

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine

universe u

attribute [local instance] Graph.Route8.vertexDecEq

/-- **`lem:typeA-one-terminal-collapse`, the quotient construction** (nodes
`[115]`--`[116]`, and `lem:typeA-unified-carriers` at node `[123]`): at an
indexed entry whose selected basin is trace-complete, if every coordinate of a
crossing family has at least two carriers (`lem:typeA-carrier-cut-parity`) and
`α ≤ 1`, then erasing the trace incidence from the retained core minus the
crossing family is a nontrivial trace-response quotient of the basin. -/
theorem route8Entry_smallCoreQuotient (data : Parameters)
    (object : FiniteObject.{u}) (piece : Finset object.Vertex)
    (receiver load : object.Vertex)
    (receiverMem : receiver ∈ object.receivers piece data.threshold)
    (loadRouted : load ∈ object.routedLoads piece data.threshold receiver)
    (complete : Graph.Route8.TraceBasin.TraceComplete object piece
      data.threshold receiver load
      (Graph.Route8Census.basin object data.threshold (piece, receiver, load)))
    {crossing : Finset ((Graph.Route8Census.presented object data.threshold
      data.LengthOK (piece, receiver, load)).toEntry
        (Graph.HasCycleWithLength data.LengthOK)).Coordinate}
    (parity : ∀ coordinate ∈ crossing,
      2 ≤ (((Graph.Route8Census.presented object data.threshold data.LengthOK
        (piece, receiver, load)).toEntry
          (Graph.HasCycleWithLength data.LengthOK)).car coordinate).card)
    (small : ((Graph.Route8Census.presented object data.threshold data.LengthOK
        (piece, receiver, load)).toEntry
          (Graph.HasCycleWithLength data.LengthOK)).alpha ≤ 1) :
    ∃ retained, Graph.Route8.TraceBasin.TraceResponseQuotient object piece
      data.threshold data.LengthOK receiver load
      (Graph.Route8Census.basin object data.threshold (piece, receiver, load))
      retained := by
  classical
  let basin := Graph.Route8Census.basin object data.threshold
    (piece, receiver, load)
  let presented := Graph.Route8Census.presented object data.threshold
    data.LengthOK (piece, receiver, load)
  let entry := presented.toEntry (Graph.HasCycleWithLength data.LengthOK)
   
  have loadDegree : object.internalDegree piece load = data.threshold :=
    (object.mem_routedLoads.mp loadRouted).2.1
  have receiverDegree : object.internalDegree piece receiver < data.threshold :=
    (object.mem_receivers.mp receiverMem).2
  have loadNeReceiver : load ≠ receiver := by
    intro same
    subst load
    omega
  obtain ⟨trace, traceSelected, traceInside⟩ := complete.2.1
  have tracePositive : 0 < trace.1.length := by
    apply Nat.pos_of_ne_zero
    intro zero
    exact loadNeReceiver (trace.1.eq_of_length_eq_zero zero)
  refine Graph.Route8.Entry.smallCoreCollapseFacts entry (crossing := crossing)
    parity ?_ small
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
          object piece data.threshold receiver load
      exact Finset.mem_insert_self _ _
    · exact Finset.notMem_erase _ _
    · left
      exact ⟨rfl, trace, traceSelected, tracePositive, traceInside⟩
  · have retainedBaseEq :
        Graph.Route8.PresentedEntry.retainedBaseCoordinates object piece
            retained =
          Graph.Route8.PresentedEntry.retainedBaseCoordinates object piece
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
          object piece basin data.threshold data.LengthOK
            (Graph.Route8.PresentedEntry.retainedBaseCoordinates
              object piece retained) =
        Graph.Route8.PresentedEntry.retainedReading
          object piece basin data.threshold data.LengthOK
            (Graph.Route8.PresentedEntry.retainedBaseCoordinates
              object piece (entry.retained entry.essentialCore \ crossing))
      exact congrArg
        (Graph.Route8.PresentedEntry.retainedReading
          object piece basin data.threshold data.LengthOK)
        retainedBaseEq
    have _retainedEq :
        presented.state retained = entry.restriction entry.essentialCore :=
      traceErase.trans crossingEq
    -- `lem:typeA-one-terminal-collapse` step 3: the quotient is
    -- target-complete against the declared `u`-supported target algebra
    -- (`def:typeA-trace-basin`) because `alpha <= 1` refutes the failure side
    -- -- a surviving mixed return would carry two distinct boundary
    -- incidences of the core (`lem:typeA-carrier-cut-parity`).
    exact fun realization _realizes =>
      Graph.Route8.TraceBasin.allQuotientRealizations_declaredEquivalent_of_alpha_le_one
        small realization _

/-- **`def:typeA-unified-entries` with `lem:typeA-unified-carriers`, one
entry** (node `[123]`): at a connected support whose receiver has a routed
load, with the plain trace-response quotient absent at the selected basin and
no decorated Type B handoff at the support, the selected trace basin is
target-complete-minimal or fails through alternative (a) alone with its
canonical exit-(4) witness — (b) by the quotient-freeness, (c) through
`not_traceDelocalization` against the replacement exclusion and the
selection's minimality, (d) through the envelope bridge against the
no-handoff clause — and `α(ξ) ≥ 2` holds through
`lem:typeA-carrier-cut-parity` and `lem:typeA-one-terminal-collapse`. -/
theorem route8EntryFacts (data : Parameters) (object : FiniteObject.{u})
    (piece : Finset object.Vertex) (receiver load : object.Vertex)
    (connected : Graph.SupportComponents.Connected.ConnectedOn object piece)
    (receiverMem : receiver ∈ object.receivers piece data.threshold)
    (loadRouted : load ∈ object.routedLoads piece data.threshold receiver)
    (quotientFree : ∀ basin : Finset object.Vertex,
      Graph.Route8.TraceBasin.select? object piece data.threshold receiver
          load = some basin →
        ¬ ∃ retained, Graph.Route8.TraceBasin.TraceResponseQuotient object
          piece data.threshold data.LengthOK receiver load basin retained)
    (noHandoff : ¬ HandoffProduced data object
      (canonicalWindowPacking data object) piece)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimality : ∀ representative : FiniteObject.{u},
      representative.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast data.threshold representative →
      Graph.HasCycleWithLength data.LengthOK representative)
    (exclusion : ReplacementExclusionStatement data object)
    (cubic : data.threshold = 3)
    (degenerate : ¬ data.LengthOK 2) :
    Route8UnifiedEntryFacts data object (piece, receiver, load) := by
  classical
  obtain ⟨basin₀, selectedEq⟩ :=
    Graph.Route8.TraceBasin.exists_select?_eq_some_of_mem_routedLoads
      object piece data.threshold connected loadRouted
  have selectedCensus : Graph.Route8.TraceBasin.select? object piece
      data.threshold receiver load =
        some (Graph.Route8Census.basin object data.threshold
          (piece, receiver, load)) := by
    rw [Graph.Route8Census.basin, selectedEq]
    rfl
  have complete := Graph.Route8.TraceBasin.select?_traceComplete selectedCensus
  have noQuotient := quotientFree _ selectedCensus
  have noDeloc : ¬ Graph.Route8.TraceBasin.TraceDelocalization object piece
      data.threshold data.LengthOK receiver load
      (Graph.Route8Census.basin object data.threshold (piece, receiver, load)) :=
    Graph.Route8.TraceBasin.not_traceDelocalization exclusion avoids minimality
  have noSep : ¬ Graph.Route8.TraceBasin.TraceSurvivingSeparator object piece
      data.threshold data.LengthOK receiver load
      (Graph.Route8Census.basin object data.threshold (piece, receiver, load)) :=
    Graph.Route8.TraceBasin.not_traceSurvivingSeparator_of_noEnvelope avoids
      (fun vertex high => by
        show data.threshold < object.degree vertex
        rw [cubic]
        exact high)
      (fun _centre _first _second collision =>
        avoids (Graph.WindowLabelCollision.hasCycleWithLength_of_labelCollision
          degenerate collision))
      noHandoff
  -- `lem:typeA-unified-carriers`: `α(ξ) ≥ 2` through the collapse engine
  let basin := Graph.Route8Census.basin object data.threshold
    (piece, receiver, load)
  let presented := Graph.Route8Census.presented object data.threshold
    data.LengthOK (piece, receiver, load)
  let entry := presented.toEntry (Graph.HasCycleWithLength data.LengthOK)
   
  let crossing := (entry.retained entry.essentialCore).filter
    (fun coordinate =>
      ∃ event : Graph.Route8.CoordinateEvent object,
        presented.event? coordinate = some event ∧
          (∃ left right : object.Vertex,
            s(left, right) ∈ event.walk.edges ∧
              left ∈ basin ∧ right ∈ basin) ∧
            ∃ left right : object.Vertex,
              s(left, right) ∈ event.walk.edges ∧
                (left ∉ piece ∨ right ∉ piece))
  have parity : ∀ coordinate ∈ crossing, 2 ≤ (entry.car coordinate).card := by
    intro coordinate member
    obtain ⟨_retained, event, eventEq, ⟨insideL, _insideR, insideEdge,
      insideLBasin, _insideRBasin⟩, outsideL, outsideR, outsideEdge,
      outsideSplit⟩ := Finset.mem_filter.mp member
    refine Graph.Route8.PresentedEntry.two_le_card_car presented
      ⟨event, eventEq, ⟨insideL, ?_, ?_⟩, ?_⟩
    · exact SimpleGraph.Walk.fst_mem_support_of_mem_edges _ insideEdge
    · exact complete.1 insideLBasin
    · rcases outsideSplit with outsideLNot | outsideRNot
      · exact ⟨outsideL,
          SimpleGraph.Walk.fst_mem_support_of_mem_edges _ outsideEdge,
          outsideLNot⟩
      · exact ⟨outsideR,
          SimpleGraph.Walk.snd_mem_support_of_mem_edges _ outsideEdge,
          outsideRNot⟩
  have alphaBound : 2 ≤ entry.alpha := by
    by_contra large
    exact noQuotient (route8Entry_smallCoreQuotient data object piece receiver
      load receiverMem loadRouted complete parity
      (Nat.le_of_lt_succ (Nat.lt_of_not_le large)))
  -- the classification of the entry
  refine ⟨selectedCensus, alphaBound, ?_⟩
  by_cases defect : Graph.Route8.TraceBasin.TraceLocalTargetDefect object piece
      data.threshold data.LengthOK receiver load basin
  · exact Or.inr ⟨defect, noQuotient, noDeloc, noSep,
      Graph.Route8.TraceBasin.exists_witness_of_traceLocalTargetDefect
        selectedCensus loadRouted defect⟩
  · exact Or.inl
      (Graph.Route8.TraceBasin.targetCompleteMinimal_of_refutations
        complete defect noQuotient exclusion avoids minimality noSep)

/-- **`def:typeA-unified-entries` with `lem:typeA-unified-carriers`** (node
`[123]`): the exact per-entry census of the unified collection, alternative
(b) refuted by the `[113]`-tested quotient-freeness and (d) against the
collection's own no-handoff filter. -/
theorem route8UnifiedEntryCensus (data : Parameters)
    (object : FiniteObject.{u})
    (quotientFree : ∀ index ∈ route8UnifiedEntries data object,
      ∀ basin : Finset object.Vertex,
        Graph.Route8.TraceBasin.select? object index.1 data.threshold
            index.2.1 index.2.2 = some basin →
          ¬ ∃ retained,
            Graph.Route8.TraceBasin.TraceResponseQuotient object index.1
              data.threshold data.LengthOK index.2.1 index.2.2 basin retained)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimality : ∀ representative : FiniteObject.{u},
      representative.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast data.threshold representative →
      Graph.HasCycleWithLength data.LengthOK representative)
    (exclusion : ReplacementExclusionStatement data object)
    (cubic : data.threshold = 3)
    (degenerate : ¬ data.LengthOK 2) :
    Route8UnifiedEntryCensusFact data object := by
  classical
  intro index indexMem
  obtain ⟨component, componentMem, pieceEq, receiverMem, loadMem⟩ :=
    mem_entriesOfComponents.mp indexMem
  obtain ⟨_zeroSurplus, _negative, noHandoff⟩ :=
    (Finset.mem_filter.mp componentMem).2
  have connected : Graph.SupportComponents.Connected.ConnectedOn object
      index.1 := by
    rw [pieceEq]
    exact Graph.SupportComponents.Connected.connectedOn_of_mem_order object _
      ((Graph.FiniteObject.mem_canonicalPieces _ _).1
        (Finset.mem_filter.mp componentMem).1)
  have noHandoff' : ¬ HandoffProduced data object
      (canonicalWindowPacking data object) index.1 := by
    rw [pieceEq]
    exact noHandoff
  exact route8EntryFacts data object index.1 index.2.1 index.2.2 connected
    (Finset.mem_filter.mp receiverMem).1
    (Finset.mem_sdiff.mp loadMem).1
    (quotientFree index indexMem) noHandoff' avoids minimality exclusion cubic
    degenerate

/-- **`def:typeA-unified-entries` with `lem:typeA-unified-carriers` at the
extracted route-8 cores** (node `[123]`; `lem:typeB-bridge-with-route8-core`'s
`𝒜_X`): the same per-entry census at the entries of the route-8 non-window
cores extracted from the Type B bridge pieces.  A core is a canonical
connected component of a deleted region; alternative (b) is refuted by the
core's own quotient-free filter clause and (d) by its no-handoff clause. -/
theorem route8ExtractedEntryCensus (data : Parameters)
    (object : FiniteObject.{u})
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimality : ∀ representative : FiniteObject.{u},
      representative.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast data.threshold representative →
      Graph.HasCycleWithLength data.LengthOK representative)
    (exclusion : ReplacementExclusionStatement data object)
    (cubic : data.threshold = 3)
    (degenerate : ¬ data.LengthOK 2) :
    Route8ExtractedEntryCensusFact data object := by
  classical
  intro index indexMem
  obtain ⟨piece, receiver, load⟩ := index
  simp only [route8ExtractedEntries, Finset.mem_biUnion, Finset.mem_image,
    Prod.mk.injEq] at indexMem
  obtain ⟨core, coreMem, receiver', receiverMem, load', loadMem, rfl, rfl,
    rfl⟩ := indexMem
  obtain ⟨_bridge, _bridgeMem, coreSpec⟩ := Finset.mem_biUnion.mp coreMem
  have coreFilter := Finset.mem_filter.mp coreSpec
  obtain ⟨component, componentMem, componentEq⟩ :=
    Finset.mem_image.mp coreFilter.1
  have connected : Graph.SupportComponents.Connected.ConnectedOn object core := by
    rw [← componentEq]
    exact Graph.SupportComponents.Connected.connectedOn_of_mem_order object _
      ((Graph.FiniteObject.mem_canonicalPieces _ _).1 componentMem)
  exact route8EntryFacts data object core receiver' load' connected receiverMem
    (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp loadMem).1).1
    (coreFilter.2.2.2.2 receiver' receiverMem load' loadMem)
    coreFilter.2.2.2.1 avoids minimality exclusion cubic degenerate

/-- **`thm:branch-kill`: the all-pieces classification at the canonical
packing.**  The contrapositive of clauses (a) and (b) at every negative piece
of the canonical decomposition: the zero-surplus arm is `lem:typeA-exclusion`'s
"Consequently" trichotomy, and the positive-surplus arm is
`prop:typeB-bridge-reduction`'s contrapositive — the B2 disjoint ledger with
strictly negative remaining core, or a minimal overlap obstruction; the
post-ledger hygiene and grouped coverage are not republished.  Maximality of
the canonical packing is derived, not assumed. -/
theorem route8PiecesClassified (data : Parameters) (object : FiniteObject.{u})
    (exclusion : TypeAExclusionStatement data object)
    (bridge : TypeBBridgeReductionStatement data object) :
    Route8PiecesClassifiedStatement data object := by
  classical
  obtain ⟨valid, maximal⟩ := canonicalWindowPacking_valid_maximal data object
  intro piece pieceMem negative
  refine ⟨fun zeroSurplus => ?_, fun positiveSurplus => ?_⟩
  · -- `thm:branch-kill`(a): the `[86]` trichotomy at this exact piece.
    exact (exclusion (canonicalWindowPacking data object) valid maximal
      (object.pieceSupport
        (object.remainderSupport (canonicalWindowPacking data object)) piece)
      (object.pieceSupport_subset _ piece)
      (Graph.SupportComponents.Connected.connectedOn_of_mem_order object _
        ((Graph.FiniteObject.mem_canonicalPieces _ _).1 pieceMem))
      negative zeroSurplus).1
  · -- `thm:branch-kill`(b): the bridge-residual dichotomy at this piece.
    rcases bridge (canonicalWindowPacking data object) valid maximal
        ⟨piece, pieceMem⟩ negative positiveSurplus with
      ⟨ledger, exactRefinement, notClean, _postLedger, _grouped⟩ | obstruction
    · exact Or.inl ⟨ledger, exactRefinement, notClean⟩
    · exact Or.inr obstruction

end Hypostructure.Graph.Contracts.RouteEight
