import Hypostructure.Graph.Statements.Spine
import Hypostructure.Graph.Statements.CanonicalSurplus
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

/-- **(F2) is a target-defective quotient** (`lem:cold-corridor-first-failure`
(ii), through `lem:context-universality`): the separating context of an (F2)
pair shows that its identification on G's own prefix piece is target-complete
in no immutable profile fibre. -/
theorem coldFailureDefectRoutes
    (data : Parameters) (object : Graph.FiniteObject.{u}) :
    ColdFailureDefectRoutesStatement data object := by
  unfold ColdFailureDefectRoutesStatement
  intro _windows _component corridor _presentation _index _left _right failure
    _Profile profile
  exact Graph.ColdCorridor.Corridor.not_targetComplete_of_firstFailureDefect
    (support := fun stage => corridor.prefixSupport stage.1)
    (profile := profile) failure

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
    (fun support compressible => uncompressible support compressible)

/-- **The ordered first failure.**  On the retained cold corridor state, with
the declared handoff registry `ColdDeclaredHandoffSupport`, every eligible half-edge has a first event
in the ordered (F1)--(F5) list: the germ event of the state witnesses that the
set of failing segments is nonempty, and its minimum is the first failure. -/
theorem coldFirstFailureOccurrence_of_state
    (data : Parameters) (object : Graph.FiniteObject.{u})
    (state : ColdCorridorStateStatement data object) :
    ColdFirstFailureOccurrenceStatement data object := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  refine ⟨⟨state, ?_⟩⟩
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
    Graph.ColdCorridor.Corridor.FirstFailureHandoff corridor
      (ColdDeclaredHandoffSupport data object) segment
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
      (ColdDeclaredHandoffSupport data object) segment
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

/-- **`lem:cold-corridor-first-failure` (ii), the paper's claim** (tex
7265-7270), at G's retained occurrence: on the surviving cold branch, the first
failure of a selected half-edge `ε` of G -- read on the corridor, presentation
and segment index that G's classified data retains for `ε`
(`coldOccurrenceCorridorAt` / `coldOccurrencePresentationAt` /
`coldOccurrenceIndexAt`) -- is not (F2), because the (F2) pair is a
target-defective quotient, i.e. a sparse surplus exit, excluded by
`K .sparseSurplusSurvivor`.

Recorded as a paper error (`lean-vs-paper-discrepancies.md#paper-errors`): the
(F2) pair compares two corridor prefixes through their cut-state interface,
not two declared coordinates of G's sparse family, so it is not a sparse exit
of `def:named-surplus-exits` and the survivor fact does not refute it
(`Quarantine/PaperRepairs/ColdF2Refutation.lean`,
`coldF2_not_clauseB`).

The statement is quantified only over G's retained objects: the earlier
all-presentations/all-indices form is false
(`ColdF2Refutation.coldFailureDefect_excluded_is_false`, with a constant
index), while the retained index is injective and its states are G's
chosen ones. -/
theorem coldFailureDefect_excluded (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (_survivor : DeclaredSparseSurvivor data object)
    (occurrence : ColdFirstFailureOccurrenceData data object)
    (epsilon : ColdEligibleHalfEdge data object)
    (first : (coldOccurrenceCorridorAt data object occurrence epsilon).Segment)
    (_minimal : ∀ earlier :
        (coldOccurrenceCorridorAt data object occurrence epsilon).Segment,
      earlier.1 < first.1 →
        ¬ ColdFirstFailureEvent data object
          (coldOccurrenceCorridorAt data object occurrence epsilon)
          (coldOccurrencePresentationAt data object occurrence epsilon)
          (coldOccurrenceIndexAt data object occurrence epsilon)
          (coldOccurrenceIncidence data object occurrence epsilon)
          (ColdDeclaredHandoffSupport data object) earlier) :
    ¬ ColdFirstFailureDefectAt data object
      (coldOccurrenceCorridorAt data object occurrence epsilon)
      (coldOccurrencePresentationAt data object occurrence epsilon)
      (coldOccurrenceIndexAt data object occurrence epsilon) first := by
  -- PAPER-ERROR [153] tex:7268 — see lean-vs-paper-discrepancies.md#paper-errors
  sorry

/-- **`lem:cold-corridor-first-failure`, the routing** (tex 7234-7295): (F1)
is a target cycle and (F3) a target-complete compression, both excluded by the
ledger; (F2) is a sparse exit excluded by the node-`[125]` survivor
(`coldFailureDefect_excluded`, applied at G's retained occurrence and first
failure; PAPER-ERROR [153] tex:7268); every other first failure is routed as
the lemma states -- (F5) a cold bounded configuration or (F4) an already named
handoff of the declared registry `ColdDeclaredHandoffSupport` (G's heavy
handoff centres). -/
theorem coldFailureRouting_of_failures
    (data : Parameters) (object : Graph.FiniteObject.{u})
    (occurrence : ColdFirstFailureOccurrenceStatement data object)
    (failureCycle : ColdFailureCycleStatement data object)
    (failureCompression : ColdFailureCompressionStatement data object)
    (survivor : DeclaredSparseSurvivor data object) :
    ColdFailureRoutingStatement data object := by
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
      exact (coldFailureDefect_excluded data object survivor occurrenceData epsilon
        first minimal defect).elim
  | compression compression =>
      exact (failureCompression _ _ _ _ _ _
        ⟨Classical.choose compression⟩).elim
  | handoff handoff => exact Or.inr ⟨first, handoff, minimal⟩
  | germ germ => exact Or.inl ⟨⟨first, germ, minimal⟩⟩

/-- **The first-failure exchange is bounded by `M_cold`.** -/
theorem coldExchangeBound_holds
    (data : Parameters) (object : Graph.FiniteObject.{u}) :
    ColdExchangeBoundStatement data object :=
  fun _windows _component corridor terminal =>
    corridor.exchange_card_le terminal

end Hypostructure.Graph.Contracts.Spine
