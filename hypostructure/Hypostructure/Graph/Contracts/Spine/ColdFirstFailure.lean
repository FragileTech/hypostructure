import Hypostructure.Graph.Statements.Spine
import Hypostructure.Graph.ColdIncrementArithmetic
import Hypostructure.Graph.ColdGermFamily

/-!
# Contracts: the cold-corridor first failure `[153]`

Proof-agnostic contract lemmas for `lem:cold-corridor-first-failure` and the
exchange/extraction step of `lem:cold-germ-extraction`.  Each lemma is stated
over a `Graph.FiniteObject` with the registered `Parameters` as a parameter and
every paper hypothesis explicit; its conclusion is exactly the statement of the
fact it proves.  This module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Contracts.Spine

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

/-- **(F2) is a sparse exit (b).**  The two prefixes of an (F2) pair and their
distinguishing context form a rank-reducing attempted quotient with a target
defect, i.e. the sparse surplus exit (b). -/
theorem coldFailureDefectRoutes
    (data : Parameters) (object : Graph.FiniteObject.{u}) :
    ColdFailureDefectRoutesStatement data object := by
      intro windows component corridor presentation index left right
      intro failure
      classical
      let support := corridor.prefixSupport right.1
      let reduced :=
        Graph.Strategy.InterfaceReplacement.SupportAtom.retainedPiece
          object support (corridor.prefixSupport left.1)
      let full :=
        Graph.Strategy.InterfaceReplacement.SupportAtom.piece object support
      let family : Finset (ULift.{u} (Fin 2)) := Finset.univ
      let coordinateSupport : ULift.{u} (Fin 2) →
          Finset object.Vertex := fun _ => ∅
      let attempt : Graph.AttemptedQuotient
          (Coordinate := ULift.{u} (Fin 2))
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK)
          object family coordinateSupport :=
        { support := support
          connected := corridor.prefixSupport_connectedOn right.1
          carries := by
            intro coordinate member vertex vertexMember
            simp [coordinateSupport] at vertexMember
          Label := ULift.{u + 1} Unit
          Value := ULift.{u + 1} Unit
          label := fun _ => ULift.up ()
          value := fun _ _ => ULift.up ()
          properRepresentative := by
            intro _proper _reducing complete
            exfalso
            obtain ⟨outside, separates⟩ := failure.2
            apply separates
            exact (complete reduced full
              (by intro coordinate member; rfl)).2 outside
          closedRepresentative := by
            intro _closed _reducing complete
            exfalso
            obtain ⟨outside, separates⟩ := failure.2
            apply separates
            exact (complete reduced full
              (by intro coordinate member; rfl)).2 outside }
      have reducing : ¬ Set.InjOn attempt.label ↑family := by
        intro injective
        have equal : ULift.up (0 : Fin 2) = ULift.up 1 :=
          injective (by simp [family]) (by simp [family]) rfl
        have downEqual : (0 : Fin 2) = 1 := congrArg ULift.down equal
        omega
      have identified : attempt.Identifies reduced full := by
        intro coordinate member
        rfl
      exact .targetDefect family coordinateSupport attempt reducing
        reduced full identified failure.2

/-- **F2-free context equivalence.**  When (F2) is excluded on two prefixes
with the same state, the two prefixes agree against every outside context. -/
theorem coldFailureDefectEquivalent
    (data : Parameters) (object : Graph.FiniteObject.{u}) :
    ColdFailureDefectEquivalentStatement data object := by
      intro windows component corridor presentation index left right
        excluded same
      classical
      intro outside
      by_contra distinguishes
      exact excluded ⟨same, ⟨outside, distinguishes⟩⟩

/-- **(F2), complete local content**: the sparse-exit route and the F2-free
context equivalence. -/
theorem coldFailureDefectFact
    (data : Parameters) (object : Graph.FiniteObject.{u}) :
    ColdFailureDefectStatement data object :=
  { routes := coldFailureDefectRoutes data object
    equivalent := coldFailureDefectEquivalent data object }

/-- **(F1) never occurs.**  An (F1) completion is a target cycle of the object;
an object avoiding the target has none. -/
theorem coldFailureCycle_of_avoids
    (data : Parameters) (object : Graph.FiniteObject.{u})
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object) :
    ColdFailureCycleStatement data object := by
  intro windows component corridor order window segment failure
  exact avoids
    (Graph.ColdCorridor.Corridor.hasCycleWithLength_of_firstFailureCycle
      failure)

/-- **(F3) never occurs.**  An (F3) pair is a target-complete compression of a
proper support, which `cor:uncompressible` forbids. -/
theorem coldFailureCompression_of_uncompressible
    (data : Parameters) (object : Graph.FiniteObject.{u})
    (uncompressible : UncompressibleStatement data object) :
    ColdFailureCompressionStatement data object := by
  intro windows component corridor presentation index support
  exact Graph.ColdCorridor.Corridor.FirstFailureCompression.not_occurs
    (fun support compressible => uncompressible support
      (Graph.Strategy.InterfaceReplacement.replacementSupportOfCompressibleSupport
        _ _ _ _ compressible))

/-- **(F4) transfers to the handoff support.**  A corridor that first enters a
declared handoff support has its head in that support. -/
theorem coldFailureHandoff_holds (object : Graph.FiniteObject.{u}) :
    ColdFailureHandoffStatement object := by
  intro windows component corridor Handoff segment failure
  exact Graph.ColdCorridor.Corridor.handoff_mem failure

/-- **The ordered first failure.**  On the retained cold corridor state, with
the declared (empty) handoff ledger, every eligible half-edge has a first event
in the ordered (F1)--(F5) list: the germ event of the state witnesses that the
set of failing segments is nonempty, and its minimum is the first failure. -/
theorem coldFirstFailureOccurrence_of_state
    (data : Parameters) (object : Graph.FiniteObject.{u})
    (state : ColdCorridorStateStatement data object)
    (handoffLedger : ColdDeclaredHandoffLedgerStatement data object) :
    ColdFirstFailureOccurrenceStatement data object := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  obtain ⟨Handoff, handoffAbsent⟩ := handoffLedger
  refine ⟨⟨Handoff, handoffAbsent, state, ?_⟩⟩
  intro Eligible incidence stateOne componentAt stateTwo corridorAt stateTail
    presentationAt indexAt epsilon
  let indexTail := Classical.choose_spec stateTail
  let stateFacts := (Classical.choose_spec indexTail).1
  let germ := incidence epsilon
  let corridor := corridorAt epsilon
  let presentation := presentationAt epsilon
  let index := indexAt epsilon
  let packing := canonicalWindowPacking data object
  let cycleAt : corridor.Segment → Prop := fun segment =>
    ∃ windowSupport ∈ packing,
      ∃ window : Graph.ColdCorridor.Window object data.windowOrder,
        (∀ vertex, vertex ∈ windowSupport ↔
          ∃ position, window.place position = vertex) ∧
        corridor.FirstFailureCycle window data.LengthOK segment
  let defectAt : corridor.Segment → Prop := fun segment =>
    ∃ left : corridor.Segment,
      left.1 < segment.1 ∧
        Graph.ColdCorridor.Corridor.FirstFailureDefect corridor presentation
          index (Graph.HasCycleWithLength data.LengthOK)
          (fun stage => corridor.prefixSupport stage.1) left segment
  let compressionAt : corridor.Segment → Prop := fun segment =>
    ∃ failure : Graph.ColdCorridor.Corridor.FirstFailureCompression corridor
        presentation index (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK)
        (fun stage => corridor.prefixSupport stage.1),
      failure.stage = segment
  let handoffAt : corridor.Segment → Prop := fun segment =>
    Graph.ColdCorridor.Corridor.FirstFailureHandoff corridor Handoff segment
  let germAt : corridor.Segment → Prop := fun segment =>
    (corridor.TerminalCorridor data.coldSignature ∧
      germ.support = corridor.prefixSupport corridor.statesRead ∧
      (let terminal : corridor.Segment :=
        ⟨corridor.inside.1.length, Nat.lt_succ_self _⟩
       germ.record = corridor.recordAt presentation index terminal) ∧
      segment.1 = corridor.inside.1.length) ∨
    ∃ left right : corridor.Segment,
      right.1 ≤ Graph.ColdCorridor.stateBound data.coldSignature ∧
      left.1 < right.1 ∧
      presentation.state (index left) = presentation.state (index right) ∧
      (∀ coordinate : Graph.ColdCorridor.Generated data.coldSignature,
        presentation.support (index left) coordinate ⊆
            ↑(presentation.activeInterface (index left)) →
          presentation.reading (index left) coordinate =
            presentation.reading (index right) coordinate) ∧
      (∀ earlierLeft earlierRight : corridor.Segment,
        earlierLeft.1 < earlierRight.1 → earlierRight.1 < right.1 →
          presentation.state (index earlierLeft) ≠
            presentation.state (index earlierRight)) ∧
      germ.support = corridor.intervalSupport left right ∧
      germ.record = corridor.recordAt presentation index left ∧
      germ.record = corridor.recordAt presentation index right ∧
      segment = right
  let failureAt : corridor.Segment → Prop := fun segment =>
    ColdFirstFailureEvent data object corridor presentation index germ
      Handoff segment
  change ∃ first : corridor.Segment,
    failureAt first ∧
      ∀ earlier : corridor.Segment, earlier.1 < first.1 →
        ¬ failureAt earlier
  have germWitness : corridor.FirstFailureGermWitness
      (Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold)
      (Graph.cycleTargetInterface data.LengthOK).isomorphismInvariant
      presentation index germ :=
    (stateFacts epsilon).2.2.2
  have germEvent : ∃ segment : corridor.Segment, germAt segment := by
    rcases germWitness.2.2 with terminal | repeated
    · let segment : corridor.Segment :=
        ⟨corridor.inside.1.length, Nat.lt_succ_self _⟩
      exact ⟨segment, Or.inl
        ⟨terminal.1, terminal.2.1, terminal.2.2, rfl⟩⟩
    · obtain ⟨left, right, rightBound, before, same, readings, first,
        supportEq, leftRecord, rightRecord⟩ := repeated
      exact ⟨right, Or.inr
        ⟨left, right, rightBound, before, same, readings, first,
          supportEq, leftRecord, rightRecord, rfl⟩⟩
  let failures : Finset corridor.Segment :=
    Finset.univ.filter failureAt
  have failuresNonempty : failures.Nonempty := by
    obtain ⟨segment, event⟩ := germEvent
    exact ⟨segment, Finset.mem_filter.2 ⟨Finset.mem_univ _,
      .germ event⟩⟩
  let first := failures.min' failuresNonempty
  have firstMember : first ∈ failures :=
    Finset.min'_mem failures failuresNonempty
  refine ⟨first, (Finset.mem_filter.1 firstMember).2, ?_⟩
  intro earlier earlierBefore earlierFailure
  have earlierMember : earlier ∈ failures :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, earlierFailure⟩
  have firstLeEarlier := Finset.min'_le failures earlier earlierMember
  exact (Nat.not_lt_of_ge firstLeEarlier) earlierBefore

/-- **(F5) is the only surviving first failure.**  On the sparse-exit survivor,
(F1) and (F3) never occur, an (F2) pair would be a sparse exit, and every (F4)
support is absent from the declared handoff ledger; so every first failure is
the terminal/least-repeat germ. -/
theorem coldFailureRouting_of_failures
    (data : Parameters) (object : Graph.FiniteObject.{u})
    (occurrence : ColdFirstFailureOccurrenceStatement data object)
    (failureCycle : ColdFailureCycleStatement data object)
    (failureDefectRoute : ColdFailureDefectRoutesStatement data object)
    (failureCompression : ColdFailureCompressionStatement data object)
    (failureHandoff : ColdFailureHandoffStatement object)
    (sparseSurvivor : Graph.SurvivesSparseExits
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object) :
    ColdFailureRoutingStatement data object := by
  refine ⟨sparseSurvivor, ?_⟩
  let occurrenceData := Classical.choice occurrence
  refine ⟨⟨occurrenceData, ?_⟩⟩
  intro epsilon
  obtain ⟨first, event, minimal⟩ := occurrenceData.occurs epsilon
  cases event with
  | cycle cycle =>
      exact (failureCycle _ _ _ _ _ _
        (Classical.choose_spec
          (Classical.choose_spec cycle).2).2).elim
  | defect defect =>
      exact (sparseSurvivor
        (failureDefectRoute _ _ _ _ _ (Classical.choose defect) first
          (Classical.choose_spec defect).2)).elim
  | compression compression =>
      exact (failureCompression _ _ _ _ _ _
        ⟨Classical.choose compression⟩).elim
  | handoff handoff =>
      obtain ⟨support, supportHandoff, _⟩ :=
        failureHandoff _ _ _ _ _ handoff
      exact (occurrenceData.handoffAbsent support supportHandoff).elim
  | germ germ => exact ⟨⟨first, germ, minimal⟩⟩

/-- **The first-failure exchange is bounded by `M_cold`.** -/
theorem coldExchangeBound_of_routing
    (data : Parameters) (object : Graph.FiniteObject.{u})
    (routing : ColdFailureRoutingStatement data object) :
    ColdExchangeBoundStatement data object :=
  ⟨routing, fun _windows _component corridor terminal =>
    corridor.exchange_card_le terminal⟩

/-- **`lem:cold-germ-extraction`, the finite extraction.**  With the exchange
bound, an occurrence-indexed candidate family with the paper's overlap bound
has a disjoint subfamily of size at least `|𝒢_cand|/D_cold`. -/
theorem coldGermExtraction_of_exchangeBound
    (data : Parameters) (object : Graph.FiniteObject.{u})
    (exchange : ColdExchangeBoundStatement data object) :
    ColdGermExtractionStatement data object :=
  ⟨exchange, Graph.ColdCorridor.coldGermOccurrenceExtractionLocal⟩

end Hypostructure.Graph.Contracts.Spine
