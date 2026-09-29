import Hypostructure.Graph.Contracts.RouteEight.EntryCensus
import Hypostructure.Graph.Statements.Route8QuotientSize
import Hypostructure.Graph.FoldCycleLift
import Hypostructure.Graph.Contracts.RouteEight.Collection
import Hypostructure.Graph.Statements.JointHubs

/-!
# Contracts: the route-8 quotient test decided at G

Node `[348]` / `[113]` stated about G.

* `route8BasinRepresentative`: the canonical representative of the
  cut-state of G's piece at any basin is a valid replacement of exactly the
  size of the piece, and its gluing is not smaller than G (the selection's
  minimality): a valid replacement of a piece of the minimal counterexample
  cannot be smaller.
* `route8QuotientReadingsNotSmaller`: the same for every trace-response
  quotient reading of the basin.
* `not_traceTargetCompleteCompression`: the exit-`(5)` datum is absent at every
  basin (`cor:uncompressible`, `CompressibleSupport`).
* `route8QuotientEntriesAtG`: the quotient test is decided at G; the failure
  of quotient freeness is exactly the non-emptiness of the unified entry family,
  and every unified entry has `α(ξ) = 0`, its quotient, a size-preserving
  representative, and no exit-`(5)` datum.

This module imports no vocabulary, row, or strategy module.
-/

namespace Hypostructure.Graph.Contracts.RouteEight

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine

universe u

attribute [local instance] Graph.Route8.vertexDecEq

/-- **The canonical representative of the (b)-quotient class of G's piece is a
valid replacement of the size of the piece, not smaller** (the valid-replacement
principle).  It has the profile, the degree baseline (inherited from G through
`G − basin`) and no target cycle; a smaller lexicographic size would make its
gluing a smaller baseline object, to which the minimality of G gives a target
cycle. -/
theorem route8BasinRepresentative (data : Parameters)
    (object : FiniteObject.{u})
    (baseline : data.threshold ≤ object.minDegree)
    (avoids : ¬ HasCycleWithLength data.LengthOK object)
    (minimality : ∀ representative : FiniteObject.{u},
      representative.LexicographicallySmaller object →
      MinimumDegreeAtLeast data.threshold representative →
      HasCycleWithLength data.LengthOK representative)
    (basin : Finset object.Vertex) :
    Route8BasinRepresentative data object basin := by
  classical
  unfold Route8BasinRepresentative
  intro piece outside representative
  have reading := CanonicalPiece.cutStateRepresentativeAt_reading
    (minimumDegreeAtLeast_isomorphismInvariant data.threshold)
    (cycleTargetInterface data.LengthOK).isomorphismInvariant piece outside
  have le : representative.size ≤ piece.internalVertexCount :=
    CanonicalPiece.cutStateRepresentativeAt_size_le
    (minimumDegreeAtLeast_isomorphismInvariant data.threshold)
    (cycleTargetInterface data.LengthOK).isomorphismInvariant piece outside
  have iso := (Strategy.InterfaceReplacement.SupportAtom.decomposition object
    basin).reconstructionIso
  have glueBaseline : MinimumDegreeAtLeast data.threshold (glue piece outside) :=
    ((minimumDegreeAtLeast_isomorphismInvariant data.threshold).iff_of_iso
      ⟨iso⟩).mpr baseline
  have representativeBaseline :
      MinimumDegreeAtLeast data.threshold (glue representative.toPiece outside) :=
    reading.2.2 glueBaseline
  have noTarget : ¬ HasCycleWithLength data.LengthOK
      (glue representative.toPiece outside) := fun hit =>
    Strategy.InterfaceReplacement.not_target_glue_piece_outside avoids basin
      (reading.2.1.mp hit)
  have notSmaller : ¬ (glue representative.toPiece outside).LexicographicallySmaller
      object := fun smaller => noTarget
    (minimality _ smaller representativeBaseline)
  refine ⟨reading.1, representativeBaseline, noTarget, ?_, notSmaller⟩
  by_contra ne
  have lt := lt_of_le_of_ne le ne
  have countEq : (glue piece outside).vertexCount = object.vertexCount :=
    FiniteObject.vertexCount_eq_of_iso iso
  refine notSmaller (FiniteObject.lexicographicallySmaller_of_vertexCount_lt ?_)
  simp only [glue_vertexCount, CanonicalPiece.toPiece_internalVertexCount] at countEq ⊢
  omega

/-- **No quotient reading of a basin of G is a smaller valid replacement**: a
reading glued into `G − basin` carries no target cycle
(`not_target_glue_retainedReading_outside`), so a lexicographically smaller size
together with the degree baseline would contradict the minimality of G. -/
theorem route8QuotientReadingsNotSmaller (data : Parameters)
    (object : FiniteObject.{u})
    (avoids : ¬ HasCycleWithLength data.LengthOK object)
    (minimality : ∀ representative : FiniteObject.{u},
      representative.LexicographicallySmaller object →
      MinimumDegreeAtLeast data.threshold representative →
      HasCycleWithLength data.LengthOK representative)
    (support basin : Finset object.Vertex) :
    Route8QuotientReadingsNotSmaller data object support basin :=
  fun retained baselineAt smaller =>
    Graph.Route8.PresentedEntry.not_target_glue_retainedReading_outside
      (basin := basin) (threshold := data.threshold) avoids retained
      (minimality _ smaller baselineAt)

/-- **The folds of the basin's piece are smaller valid realizations with an
accepted cycle** (`foldRealization_baseline_and_smaller` and the minimality of
G). -/
theorem route8BasinFoldsCarryCycles (data : Parameters)
    (object : FiniteObject.{u}) (two : 2 ≤ data.threshold)
    (baseline : data.threshold ≤ object.minDegree)
    (minimality : ∀ representative : FiniteObject.{u},
      representative.LexicographicallySmaller object →
      MinimumDegreeAtLeast data.threshold representative →
      HasCycleWithLength data.LengthOK representative)
    (basin : Finset object.Vertex) :
    Route8BasinFoldsCarryCycles data object basin := by
  intro connected proper keep remove different noCommon
  obtain ⟨foldBaseline, foldSmaller⟩ :=
    Graph.Route8.PresentedEntry.foldRealization_baseline_and_smaller object
      basin data.threshold two connected proper keep remove different baseline
      noCommon
  exact ⟨foldBaseline, foldSmaller, minimality _ foldSmaller foldBaseline⟩

/-- **The path a fold forces** (`FoldCycleLift.foldGlue_path_of_cycle` with the
crossing lemma): the fold's cycle (minimality) lifts to an accepted path of G
between the two folded vertices, which stays in the support or crosses its cut
twice. -/
theorem route8BasinFoldPaths (data : Parameters)
    (object : FiniteObject.{u}) (two : 2 ≤ data.threshold)
    (baseline : data.threshold ≤ object.minDegree)
    (avoids : ¬ HasCycleWithLength data.LengthOK object)
    (minimality : ∀ representative : FiniteObject.{u},
      representative.LexicographicallySmaller object →
      MinimumDegreeAtLeast data.threshold representative →
      HasCycleWithLength data.LengthOK representative)
    (support basin : Finset object.Vertex) :
    Route8BasinFoldPaths data object support basin := by
  classical
  intro subset connected proper keep remove different noCommon
  have cycles := route8BasinFoldsCarryCycles data object two baseline minimality
    basin connected proper keep remove different noCommon
  have pieceAvoids : ¬ HasCycleWithLength data.LengthOK
      (glue (Strategy.InterfaceReplacement.SupportAtom.piece object basin)
        (Strategy.InterfaceReplacement.SupportAtom.outside object basin)) :=
    Strategy.InterfaceReplacement.not_target_glue_piece_outside avoids basin
  obtain ⟨path, hpath, hlen⟩ := FoldCycleLift.foldGlue_path_of_cycle
    (Strategy.InterfaceReplacement.SupportAtom.piece object basin) keep remove
    different (Strategy.InterfaceReplacement.SupportAtom.outside object basin)
    data.LengthOK pieceAvoids cycles.2.2
  let iso := (Strategy.InterfaceReplacement.SupportAtom.decomposition object
    basin).reconstructionIso
  let P := path.map iso.toHom
  have hP : P.IsPath := SimpleGraph.Walk.map_isPath_of_injective iso.injective hpath
  have hPlen : P.length = path.length := SimpleGraph.Walk.length_map _ _
  have keepIn : Strategy.InterfaceReplacement.SupportAtom.pieceDecode object
      basin (.inr keep) ∈ support := subset keep.2.1
  have removeIn : Strategy.InterfaceReplacement.SupportAtom.pieceDecode object
      basin (.inr remove) ∈ support := subset remove.2.1
  refine ⟨P, hP, hPlen ▸ hlen, ?_⟩
  by_cases stays : ∀ x ∈ P.support, x ∈ support
  · exact Or.inl stays
  · right
    push_neg at stays
    obtain ⟨w, hw, hwS⟩ := stays
    obtain ⟨e1, he1, e2, he2, hne, ⟨x1, hx1, y1, hy1, hxS1, hyS1⟩,
      ⟨x2, hx2, y2, hy2, hxS2, hyS2⟩⟩ :=
      FoldCycleLift.two_crossing object.graph (↑support : Set object.Vertex) P hP
        keepIn removeIn hw hwS
    refine ⟨e1, he1, e2, he2, hne, ?_, ?_⟩
    · rw [Graph.Route8.mem_cutEdges]
      exact ⟨by simpa using P.edges_subset_edgeSet he1,
        x1, hx1, y1, hy1, hxS1, hyS1⟩
    · rw [Graph.Route8.mem_cutEdges]
      exact ⟨by simpa using P.edges_subset_edgeSet he2,
        x2, hx2, y2, hy2, hxS2, hyS2⟩

/-- **The baseline-essential carriers of an entry**: the cut edges of the
piece that meet the basin, with their map into `∂R`. -/
theorem route8EntryCarriers (data : Parameters) (object : FiniteObject.{u})
    (baseline : data.threshold ≤ object.minDegree)
    (support basin : Finset object.Vertex) (receiver : object.Vertex)
    (zero : object.ambientSurplus support data.threshold = 0)
    (cutSubset : Graph.Route8.cutEdges object support ⊆
      Graph.Route8Census.supply object (canonicalWindowPacking data object))
    (basinSubset : basin ⊆ support)
    (receiverMem : receiver ∈ object.receivers support data.threshold)
    (inBasin : receiver ∈ basin) :
    Route8EntryCarriers data object support basin := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  have degreeEq := degree_eq_threshold_of_ambientSurplus_eq_zero data object
    baseline zero
  have isReceiver := Graph.FiniteObject.mem_receivers.mp receiverMem
  have inSupport : receiver ∈ support := isReceiver.1
  have port : ∃ y, object.graph.Adj receiver y ∧ y ∉ support := by
    by_contra none
    push_neg at none
    have subset : object.graph.neighborFinset receiver ⊆ support := by
      intro y hy
      exact none y ((SimpleGraph.mem_neighborFinset _ _ _).mp hy)
    have same : object.internalDegree support receiver = object.degree receiver := by
      simp only [FiniteObject.internalDegree, FiniteObject.degree]
      rw [Finset.inter_eq_left.mpr subset]
      exact SimpleGraph.card_neighborFinset_eq_degree _ _
    have := isReceiver.2
    have := degreeEq receiver inSupport
    omega
  refine ⟨?_, ?_⟩
  · obtain ⟨y, adjacent, outside⟩ := port
    refine ⟨s(receiver, y), ?_, receiver, Sym2.mem_mk_left _ _, inBasin⟩
    rw [Graph.Route8.mem_cutEdges]
    refine ⟨?_, receiver, Sym2.mem_mk_left _ _, y, Sym2.mem_mk_right _ _,
      inSupport, outside⟩
    simpa using adjacent
  · intro e he ⟨v, hv, hvB⟩
    exact ⟨cutSubset he, v, hv, hvB, degreeEq v (basinSubset hvB)⟩

/-- **Paths inside a hub-free part of the remainder are short**
(`K .remainderPathBounds`). -/
theorem route8InsidePathBound (data : Parameters) (object : FiniteObject.{u})
    (three : data.threshold = 3) (baseline : data.threshold ≤ object.minDegree)
    (bounds : RemainderPathBoundsStatement data object)
    (support : Finset object.Vertex)
    (subR : support ⊆ object.remainderSupport (canonicalWindowPacking data object))
    (zero : object.ambientSurplus support data.threshold = 0) :
    Route8InsidePathBound object support := by
  classical
  intro a b P hP hin
  have degreeEq := degree_eq_threshold_of_ambientSurplus_eq_zero data object
    baseline zero
  have seq : Graph.RemainderPaths.PathSeq object.graph
      (Graph.JointObject.Rset object (canonicalWindowPacking data object))
      P.length (fun t => P.getVert t) := by
    refine ⟨?_, fun t ht => P.adj_getVert_succ ht, fun t _ => ?_⟩
    · intro i hi j hj h
      exact hP.getVert_injOn hi hj h
    · exact subR (hin _ (P.getVert_mem_support t))
  have h3 := bounds.2.2.1 P.length (fun t => P.getVert t) seq
  have noHub : ((Finset.range (P.length + 1)).filter
      (fun t => P.getVert t ∈ Graph.JointObject.hubSet object)).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro t ht hub
    have mem := hin _ (P.getVert_mem_support t)
    have := degreeEq _ mem
    have hubDeg := (Graph.JointObject.mem_hubs (object := object)).mp hub
    exact hubDeg (by rw [← three]; exact this)
  have := h3.1
  rw [noHub] at this
  omega

/-- **The declared `u`-supported algebra is empty at `α(ξ) = 0`**, at every
realization and every outside context. -/
theorem not_declaredAlgebra_of_alpha_zero (data : Parameters)
    (object : FiniteObject.{u}) (support basin : Finset object.Vertex)
    (receiver load : object.Vertex)
    (small : ((Graph.Route8.PresentedEntry.ofTraceBasin object support basin
      data.threshold data.LengthOK receiver load).toEntry
        (HasCycleWithLength data.LengthOK)).alpha = 0)
    (Q : BoundaryPiece
      (Strategy.InterfaceReplacement.SupportAtom.boundary object basin))
    (outside : OutsideContext
      (Strategy.InterfaceReplacement.SupportAtom.boundary object basin)) :
    ¬ Graph.Route8.TraceBasin.declaredAlgebra object support basin
      data.threshold data.LengthOK receiver load Q outside := by
  intro holds
  obtain ⟨coordinate, coreRetained, crossing⟩ :=
    Graph.Route8.TraceBasin.distinguishingEventCrosses holds
  have alphaTwo :=
    Graph.Route8.Entry.two_le_alpha_of_two_le_card_car _ coreRetained
      ((Graph.Route8.PresentedEntry.ofTraceBasin object support basin
        data.threshold data.LengthOK receiver load).two_le_card_car crossing)
  omega

/-- **The realizations constructed from G do not hold the declared algebra**
(the declared algebra is empty at `α(ξ) = 0`). -/
theorem route8ConstructedRealizationsUndeclared (data : Parameters)
    (object : FiniteObject.{u}) (support basin : Finset object.Vertex)
    (receiver load : object.Vertex)
    (small : ((Graph.Route8.PresentedEntry.ofTraceBasin object support basin
      data.threshold data.LengthOK receiver load).toEntry
        (HasCycleWithLength data.LengthOK)).alpha = 0) :
    Route8ConstructedRealizationsUndeclared data object support basin receiver
      load :=
  ⟨not_declaredAlgebra_of_alpha_zero data object support basin receiver load
      small _ _,
    fun _ => not_declaredAlgebra_of_alpha_zero data object support basin
      receiver load small _ _,
    fun _ _ _ => not_declaredAlgebra_of_alpha_zero data object support basin
      receiver load small _ _⟩

/-- **The exit-`(5)` datum is absent at every basin of G**: its clauses are the
hypotheses of `lem:replacement` at `B_u`, which `cor:uncompressible` excludes. -/
theorem not_traceTargetCompleteCompression (data : Parameters)
    (object : FiniteObject.{u})
    (uncompressible : UncompressibleStatement data object)
    (piece : Finset object.Vertex) (receiver load : object.Vertex)
    (basin : Finset object.Vertex) :
    ¬ Graph.Route8.TraceBasin.TraceTargetCompleteCompression object piece
      data.threshold data.LengthOK receiver load basin := by
  rintro ⟨retained, _retainedSubset, _changed, profile, targetFree, connected,
    proper, baselineAt, smaller⟩
  exact uncompressible basin ⟨connected, proper,
    Graph.Route8.PresentedEntry.retainedReading object piece basin
      data.threshold data.LengthOK
      (Graph.Route8.PresentedEntry.retainedBaseCoordinates object piece
        retained), profile, baselineAt, smaller, targetFree⟩

/-- **The unified entry family carries the rate**: the stage accounting of the
descent bounds the cleared unified deficit by the number of entries, so the
unified deficit bound against the private-carrier rate leaves
`|∂R| < δ·|\tilde\Xi|`. -/
theorem route8SupplyLtEntries (data : Parameters) (object : FiniteObject.{u})
    (descent : Route8PeelingDescentStatement data object)
    (deficit : Route8UnifiedDeficitFact data object)
    (rate : Route8RateStatement data object) :
    (Route8Census.supply object (canonicalWindowPacking data object)).card <
      data.threshold * (route8UnifiedEntries data object).card := by
  classical
  obtain ⟨_chain, accounting, _outcome⟩ := descent
  obtain ⟨_peeledSubset, entriesEq, disjoint, _peeledLe, _deficitEq,
    deficitLe, _reducedLe, _stageDeficit⟩ := accounting
  have entriesCard : (route8UnifiedEntries data object).card =
      (Route8Pressure.peeledEntries object (route8UnifiedEntries data object)
        (route8DescentChain data object).toFinset).card +
        (route8DescentChain data object).toFinset.card :=
    (congrArg Finset.card entriesEq).trans (Finset.card_union_of_disjoint disjoint)
  have deficitLeEntries : TypeBEnvelopeCharge.route8Deficit object
      (object.remainderSupport (canonicalWindowPacking data object))
      data.threshold data.dischargeScale (route8UnifiedComponents data object) ≤
      (route8UnifiedEntries data object).card := by
    rw [entriesCard]
    exact deficitLe
  have bound : (object.remainderSupport (canonicalWindowPacking data object)).card ≤
      (route8UnifiedEntries data object).card +
        data.dischargeScale *
          (Route8Census.supply object (canonicalWindowPacking data object)).card +
        data.bridgeMassFactor * data.dischargeScale *
          data.surplusThreshold object.vertexCount := by
    have := deficit
    omega
  unfold Route8RateStatement Route8Census.Rate at rate
  have scaled := Nat.mul_le_mul_left data.threshold bound
  nlinarith

/-- **Node `[348]`, stated about G**: the quotient test is decided at G. -/
theorem route8QuotientEntriesAtG (data : Parameters)
    (object : FiniteObject.{u})
    (baseline : data.threshold ≤ object.minDegree)
    (avoids : ¬ HasCycleWithLength data.LengthOK object)
    (minimality : ∀ representative : FiniteObject.{u},
      representative.LexicographicallySmaller object →
      MinimumDegreeAtLeast data.threshold representative →
      HasCycleWithLength data.LengthOK representative)
    (uncompressible : UncompressibleStatement data object)
    (two : 2 ≤ data.threshold)
    (descent : Route8PeelingDescentStatement data object)
    (deficit : Route8UnifiedDeficitFact data object)
    (rate : Route8RateStatement data object)
    (three : data.threshold = 3)
    (pathBounds : RemainderPathBoundsStatement data object) :
    Route8QuotientEntriesAtGStatement data object := by
  classical
  -- every unified entry: its basin is selected and carries the quotient
  have perEntry : ∀ index ∈ route8UnifiedEntries data object,
      ∃ basin : Finset object.Vertex,
        Graph.Route8.TraceBasin.select? object index.1 data.threshold
            index.2.1 index.2.2 = some basin ∧
          (∃ retained, Graph.Route8.TraceBasin.TraceResponseQuotient object
            index.1 data.threshold data.LengthOK index.2.1 index.2.2 basin
            retained) ∧ Route8EntryCarriers data object index.1 basin ∧
            Route8InsidePathBound object index.1 := by
    intro index indexMem
    obtain ⟨component, componentMem, pieceEq, receiverMem, loadMem⟩ :=
      mem_entriesOfComponents.mp indexMem
    have connected : Graph.SupportComponents.Connected.ConnectedOn object
        index.1 := by
      rw [pieceEq]
      exact Graph.SupportComponents.Connected.connectedOn_of_mem_order object _
        ((Graph.FiniteObject.mem_canonicalPieces _ _).1
          (Finset.mem_filter.mp componentMem).1)
    have receiverIn := (Finset.mem_filter.mp receiverMem).1
    have loadRouted := (Finset.mem_sdiff.mp loadMem).1
    obtain ⟨basin, selectedEq⟩ :=
      Graph.Route8.TraceBasin.exists_select?_eq_some_of_mem_routedLoads
        object index.1 data.threshold connected loadRouted
    have complete := Graph.Route8.TraceBasin.select?_traceComplete selectedEq
    obtain ⟨trace, _traceSel, traceInside⟩ := complete.2.1
    have receiverInBasin : index.2.1 ∈ basin :=
      traceInside (List.mem_toFinset.mpr trace.1.end_mem_support)
    have zero : object.ambientSurplus index.1 data.threshold = 0 := by
      rw [pieceEq]; exact (Finset.mem_filter.mp componentMem).2.1
    have cutSubset : Graph.Route8.cutEdges object index.1 ⊆
        Graph.Route8Census.supply object (canonicalWindowPacking data object) := by
      rw [pieceEq]
      exact Graph.Route8Census.cutEdges_piece_subset object
        (canonicalWindowPacking data object) component
    exact ⟨basin, selectedEq,
      Graph.Route8.TraceBasin.exists_traceResponseQuotient_of_avoids avoids
        (Graph.FiniteObject.mem_receivers.mpr
          (Graph.FiniteObject.mem_receivers.mp receiverIn))
        loadRouted complete,
      route8EntryCarriers data object baseline index.1 basin index.2.1 zero
        cutSubset complete.1 receiverIn receiverInBasin,
      route8InsidePathBound data object three baseline pathBounds index.1
        (by rw [pieceEq]; exact object.pieceSupport_subset _ component) zero⟩
  refine ⟨?_, route8SupplyLtEntries data object descent deficit rate, ?_⟩
  · constructor
    · intro free
      apply Finset.eq_empty_of_forall_notMem
      intro index indexMem
      obtain ⟨basin, selectedEq, quotient, _, _⟩ := perEntry index indexMem
      exact free index indexMem basin selectedEq quotient
    · intro empty index indexMem basin _selectedEq _quotient
      rw [empty] at indexMem
      exact absurd indexMem (Finset.notMem_empty _)
  · intro index indexMem
    obtain ⟨basin, selectedEq, quotient, carriers, inside⟩ := perEntry index indexMem
    have alphaZero := Graph.Route8.PresentedEntry.ofTraceBasin_alpha_eq_zero
      (support := index.1) (basin := Graph.Route8Census.basin object
        data.threshold index) (threshold := data.threshold)
      (receiver := index.2.1) (load := index.2.2) avoids
    exact ⟨alphaZero, basin,
      selectedEq, quotient,
      route8BasinRepresentative data object baseline avoids minimality basin,
      route8QuotientReadingsNotSmaller data object avoids minimality index.1 basin,
      route8BasinFoldsCarryCycles data object two baseline minimality basin,
      route8BasinFoldPaths data object two baseline avoids minimality index.1
        basin,
      carriers, inside,
      route8ConstructedRealizationsUndeclared data object index.1 basin
        index.2.1 index.2.2 (by
          have selectedBasin : Graph.Route8Census.basin object data.threshold
              index = basin := by
            rw [Graph.Route8Census.basin, selectedEq]; rfl
          rw [selectedBasin] at alphaZero
          exact alphaZero),
      not_traceTargetCompleteCompression data object uncompressible _ _ _ _⟩

end Hypostructure.Graph.Contracts.RouteEight
