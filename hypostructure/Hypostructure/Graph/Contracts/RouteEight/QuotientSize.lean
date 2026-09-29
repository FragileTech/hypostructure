import Hypostructure.Graph.Contracts.RouteEight.EntryCensus
import Hypostructure.Graph.Statements.Route8QuotientSize

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

/-- **Every smaller degree-valid realization of a basin of G carries an
undeclared target cycle** (minimality of G; the declared algebra is empty at
`α(ξ) = 0`). -/
theorem route8SmallerRealizationsUndeclared (data : Parameters)
    (object : FiniteObject.{u})
    (minimality : ∀ representative : FiniteObject.{u},
      representative.LexicographicallySmaller object →
      MinimumDegreeAtLeast data.threshold representative →
      HasCycleWithLength data.LengthOK representative)
    (support basin : Finset object.Vertex) (receiver load : object.Vertex)
    (small : ((Graph.Route8.PresentedEntry.ofTraceBasin object support basin
      data.threshold data.LengthOK receiver load).toEntry
        (HasCycleWithLength data.LengthOK)).alpha = 0) :
    Route8SmallerRealizationsUndeclared data object support basin receiver
      load :=
  fun Q baselineAt smaller =>
    ⟨minimality _ smaller baselineAt,
      not_declaredAlgebra_of_alpha_zero data object support basin receiver load
        small Q _⟩

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
    (rate : Route8RateStatement data object) :
    Route8QuotientEntriesAtGStatement data object := by
  classical
  -- every unified entry: its basin is selected and carries the quotient
  have perEntry : ∀ index ∈ route8UnifiedEntries data object,
      ∃ basin : Finset object.Vertex,
        Graph.Route8.TraceBasin.select? object index.1 data.threshold
            index.2.1 index.2.2 = some basin ∧
          ∃ retained, Graph.Route8.TraceBasin.TraceResponseQuotient object
            index.1 data.threshold data.LengthOK index.2.1 index.2.2 basin
            retained := by
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
    exact ⟨basin, selectedEq,
      Graph.Route8.TraceBasin.exists_traceResponseQuotient_of_avoids avoids
        (Graph.FiniteObject.mem_receivers.mpr
          (Graph.FiniteObject.mem_receivers.mp receiverIn))
        loadRouted
        (Graph.Route8.TraceBasin.select?_traceComplete selectedEq)⟩
  refine ⟨?_, route8SupplyLtEntries data object descent deficit rate, ?_⟩
  · constructor
    · intro free
      apply Finset.eq_empty_of_forall_notMem
      intro index indexMem
      obtain ⟨basin, selectedEq, quotient⟩ := perEntry index indexMem
      exact free index indexMem basin selectedEq quotient
    · intro empty index indexMem basin _selectedEq _quotient
      rw [empty] at indexMem
      exact absurd indexMem (Finset.notMem_empty _)
  · intro index indexMem
    obtain ⟨basin, selectedEq, quotient⟩ := perEntry index indexMem
    have alphaZero := Graph.Route8.PresentedEntry.ofTraceBasin_alpha_eq_zero
      (support := index.1) (basin := Graph.Route8Census.basin object
        data.threshold index) (threshold := data.threshold)
      (receiver := index.2.1) (load := index.2.2) avoids
    exact ⟨alphaZero, basin,
      selectedEq, quotient,
      route8BasinRepresentative data object baseline avoids minimality basin,
      route8QuotientReadingsNotSmaller data object avoids minimality index.1 basin,
      route8BasinFoldsCarryCycles data object two baseline minimality basin,
      route8SmallerRealizationsUndeclared data object minimality index.1 basin
        index.2.1 index.2.2 (by
          have selectedBasin : Graph.Route8Census.basin object data.threshold
              index = basin := by
            rw [Graph.Route8Census.basin, selectedEq]; rfl
          rw [selectedBasin] at alphaZero
          exact alphaZero),
      not_traceTargetCompleteCompression data object uncompressible _ _ _ _⟩

end Hypostructure.Graph.Contracts.RouteEight
